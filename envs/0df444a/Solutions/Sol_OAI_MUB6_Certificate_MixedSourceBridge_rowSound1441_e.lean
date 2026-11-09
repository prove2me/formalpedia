-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:03:13.926871+00:00
-- url     : https://prove2.me/submissions/7f46d3a4-0aa4-44d5-9f52-76c0a4b888dc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound1299_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5292_e

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

theorem canonical76 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw76 raw76Labels = mixedMoment B node1300 node1300Labels := by
  calc
    mixedMoment B raw76 raw76Labels = mixedMoment B raw76step0 raw76step0Labels := by
      have ha : raw76step0 = (fun i j => raw76 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw76step0 raw76; decide +kernel
      have hl : raw76step0Labels = raw76Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw76 raw76Labels permutation8 permutation5
    mixedMoment B raw76step0 raw76step0Labels = mixedMoment B raw76step1 raw76step1Labels := by
      have ha : raw76step1 = raw76step0 := by apply Matrix.ext; unfold raw76step1 raw76step0; decide +kernel
      have hl : raw76step0Labels = labelEmbedding1 ∘ raw76step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw76step0 raw76step0Labels raw76step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1300 node1300Labels := by rfl

theorem canonical77 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw77 raw77Labels = mixedMoment B node156 node156Labels := by
  calc
    mixedMoment B raw77 raw77Labels = mixedMoment B raw77step0 raw77step0Labels := by
      have ha : raw77step0 = (fun i j => raw77 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw77step0 raw77; decide +kernel
      have hl : raw77step0Labels = raw77Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw77 raw77Labels permutation8 permutation5
    _ = mixedMoment B node156 node156Labels := by rfl

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

theorem canonical1311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1311 raw1311Labels = mixedMoment B node4513 node4513Labels := by
  calc
    mixedMoment B raw1311 raw1311Labels = mixedMoment B raw1311step0 raw1311step0Labels := by
      have ha : raw1311step0 = (fun i j => raw1311 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1311step0 raw1311; decide +kernel
      have hl : raw1311step0Labels = raw1311Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1311 raw1311Labels permutation152 permutation4
    mixedMoment B raw1311step0 raw1311step0Labels = mixedMoment B raw1311step1 raw1311step1Labels := by
      have ha : raw1311step1 = raw1311step0 := by apply Matrix.ext; unfold raw1311step1 raw1311step0; decide +kernel
      have hl : raw1311step0Labels = labelEmbedding7 ∘ raw1311step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1311step0 raw1311step0Labels raw1311step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4513 node4513Labels := by rfl

theorem canonical1312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1312 raw1312Labels = mixedMoment B node1097 node1097Labels := by
  calc
    mixedMoment B raw1312 raw1312Labels = mixedMoment B raw1312step0 raw1312step0Labels := by
      have ha : raw1312step0 = (fun i j => raw1312 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1312step0 raw1312; decide +kernel
      have hl : raw1312step0Labels = raw1312Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1312 raw1312Labels permutation152 permutation4
    _ = mixedMoment B node1097 node1097Labels := by rfl

theorem canonical1313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1313 raw1313Labels = mixedMoment B node3232 node3232Labels := by
  calc
    mixedMoment B raw1313 raw1313Labels = mixedMoment B raw1313step0 raw1313step0Labels := by
      have ha : raw1313step0 = (fun i j => raw1313 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1313step0 raw1313; decide +kernel
      have hl : raw1313step0Labels = raw1313Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1313 raw1313Labels permutation152 permutation6
    mixedMoment B raw1313step0 raw1313step0Labels = mixedMoment B raw1313step1 raw1313step1Labels := by
      have ha : raw1313step1 = -raw1313step0 := by apply Matrix.ext; change ∀ i j, raw1313step1 i j = -(raw1313step0 i j); unfold raw1313step1 raw1313step0; decide +kernel
      have hl : raw1313step1Labels = raw1313step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1313step1 raw1313step1Labels = mixedMoment B raw1313step2 raw1313step2Labels := by
      have ha : raw1313step2 = raw1313step1 := by apply Matrix.ext; unfold raw1313step2 raw1313step1; decide +kernel
      have hl : raw1313step1Labels = labelEmbedding1 ∘ raw1313step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1313step1 raw1313step1Labels raw1313step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3232 node3232Labels := by rfl

theorem canonical1314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1314 raw1314Labels = mixedMoment B node4514 node4514Labels := by
  calc
    mixedMoment B raw1314 raw1314Labels = mixedMoment B raw1314step0 raw1314step0Labels := by
      have ha : raw1314step0 = (fun i j => raw1314 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1314step0 raw1314; decide +kernel
      have hl : raw1314step0Labels = raw1314Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1314 raw1314Labels permutation32 permutation4
    mixedMoment B raw1314step0 raw1314step0Labels = mixedMoment B raw1314step1 raw1314step1Labels := by
      have ha : raw1314step1 = raw1314step0 := by apply Matrix.ext; unfold raw1314step1 raw1314step0; decide +kernel
      have hl : raw1314step0Labels = labelEmbedding7 ∘ raw1314step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1314step0 raw1314step0Labels raw1314step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4514 node4514Labels := by rfl

theorem canonical1315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1315 raw1315Labels = mixedMoment B node1098 node1098Labels := by
  calc
    mixedMoment B raw1315 raw1315Labels = mixedMoment B raw1315step0 raw1315step0Labels := by
      have ha : raw1315step0 = (fun i j => raw1315 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1315step0 raw1315; decide +kernel
      have hl : raw1315step0Labels = raw1315Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1315 raw1315Labels permutation32 permutation4
    _ = mixedMoment B node1098 node1098Labels := by rfl

theorem canonical1316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1316 raw1316Labels = mixedMoment B node1894 node1894Labels := by
  calc
    mixedMoment B raw1316 raw1316Labels = mixedMoment B raw1316step0 raw1316step0Labels := by
      have ha : raw1316step0 = (fun i j => raw1316 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1316step0 raw1316; decide +kernel
      have hl : raw1316step0Labels = raw1316Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1316 raw1316Labels permutation151 permutation6
    mixedMoment B raw1316step0 raw1316step0Labels = mixedMoment B raw1316step1 raw1316step1Labels := by
      have ha : raw1316step1 = raw1316step0 := by apply Matrix.ext; unfold raw1316step1 raw1316step0; decide +kernel
      have hl : raw1316step0Labels = labelEmbedding1 ∘ raw1316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1316step0 raw1316step0Labels raw1316step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1894 node1894Labels := by rfl

theorem canonical1317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1317 raw1317Labels = mixedMoment B node4515 node4515Labels := by
  calc
    mixedMoment B raw1317 raw1317Labels = mixedMoment B raw1317step0 raw1317step0Labels := by
      have ha : raw1317step0 = (fun i j => raw1317 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1317step0 raw1317; decide +kernel
      have hl : raw1317step0Labels = raw1317Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1317 raw1317Labels permutation32 permutation4
    mixedMoment B raw1317step0 raw1317step0Labels = mixedMoment B raw1317step1 raw1317step1Labels := by
      have ha : raw1317step1 = raw1317step0 := by apply Matrix.ext; unfold raw1317step1 raw1317step0; decide +kernel
      have hl : raw1317step0Labels = labelEmbedding7 ∘ raw1317step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1317step0 raw1317step0Labels raw1317step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4515 node4515Labels := by rfl

theorem canonical1318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1318 raw1318Labels = mixedMoment B node1099 node1099Labels := by
  calc
    mixedMoment B raw1318 raw1318Labels = mixedMoment B raw1318step0 raw1318step0Labels := by
      have ha : raw1318step0 = (fun i j => raw1318 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1318step0 raw1318; decide +kernel
      have hl : raw1318step0Labels = raw1318Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1318 raw1318Labels permutation32 permutation4
    _ = mixedMoment B node1099 node1099Labels := by rfl

theorem canonical1319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1319 raw1319Labels = mixedMoment B node3233 node3233Labels := by
  calc
    mixedMoment B raw1319 raw1319Labels = mixedMoment B raw1319step0 raw1319step0Labels := by
      have ha : raw1319step0 = (fun i j => raw1319 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1319step0 raw1319; decide +kernel
      have hl : raw1319step0Labels = raw1319Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1319 raw1319Labels permutation32 permutation6
    mixedMoment B raw1319step0 raw1319step0Labels = mixedMoment B raw1319step1 raw1319step1Labels := by
      have ha : raw1319step1 = -raw1319step0 := by apply Matrix.ext; change ∀ i j, raw1319step1 i j = -(raw1319step0 i j); unfold raw1319step1 raw1319step0; decide +kernel
      have hl : raw1319step1Labels = raw1319step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1319step1 raw1319step1Labels = mixedMoment B raw1319step2 raw1319step2Labels := by
      have ha : raw1319step2 = raw1319step1 := by apply Matrix.ext; unfold raw1319step2 raw1319step1; decide +kernel
      have hl : raw1319step1Labels = labelEmbedding1 ∘ raw1319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1319step1 raw1319step1Labels raw1319step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3233 node3233Labels := by rfl

theorem canonical1326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1326 raw1326Labels = mixedMoment B node4518 node4518Labels := by
  calc
    mixedMoment B raw1326 raw1326Labels = mixedMoment B raw1326step0 raw1326step0Labels := by
      have ha : raw1326step0 = (fun i j => raw1326 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1326step0 raw1326; decide +kernel
      have hl : raw1326step0Labels = raw1326Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1326 raw1326Labels permutation32 permutation4
    mixedMoment B raw1326step0 raw1326step0Labels = mixedMoment B raw1326step1 raw1326step1Labels := by
      have ha : raw1326step1 = raw1326step0 := by apply Matrix.ext; unfold raw1326step1 raw1326step0; decide +kernel
      have hl : raw1326step0Labels = labelEmbedding7 ∘ raw1326step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1326step0 raw1326step0Labels raw1326step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4518 node4518Labels := by rfl

theorem canonical1327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1327 raw1327Labels = mixedMoment B node1102 node1102Labels := by
  calc
    mixedMoment B raw1327 raw1327Labels = mixedMoment B raw1327step0 raw1327step0Labels := by
      have ha : raw1327step0 = (fun i j => raw1327 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1327step0 raw1327; decide +kernel
      have hl : raw1327step0Labels = raw1327Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1327 raw1327Labels permutation32 permutation4
    _ = mixedMoment B node1102 node1102Labels := by rfl

theorem canonical1328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1328 raw1328Labels = mixedMoment B node3236 node3236Labels := by
  calc
    mixedMoment B raw1328 raw1328Labels = mixedMoment B raw1328step0 raw1328step0Labels := by
      have ha : raw1328step0 = (fun i j => raw1328 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1328step0 raw1328; decide +kernel
      have hl : raw1328step0Labels = raw1328Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1328 raw1328Labels permutation32 permutation6
    mixedMoment B raw1328step0 raw1328step0Labels = mixedMoment B raw1328step1 raw1328step1Labels := by
      have ha : raw1328step1 = -raw1328step0 := by apply Matrix.ext; change ∀ i j, raw1328step1 i j = -(raw1328step0 i j); unfold raw1328step1 raw1328step0; decide +kernel
      have hl : raw1328step1Labels = raw1328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1328step1 raw1328step1Labels = mixedMoment B raw1328step2 raw1328step2Labels := by
      have ha : raw1328step2 = raw1328step1 := by apply Matrix.ext; unfold raw1328step2 raw1328step1; decide +kernel
      have hl : raw1328step1Labels = labelEmbedding1 ∘ raw1328step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1328step1 raw1328step1Labels raw1328step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3236 node3236Labels := by rfl

theorem canonical1335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1335 raw1335Labels = mixedMoment B node4521 node4521Labels := by
  calc
    mixedMoment B raw1335 raw1335Labels = mixedMoment B raw1335step0 raw1335step0Labels := by
      have ha : raw1335step0 = (fun i j => raw1335 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1335step0 raw1335; decide +kernel
      have hl : raw1335step0Labels = raw1335Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1335 raw1335Labels permutation152 permutation4
    mixedMoment B raw1335step0 raw1335step0Labels = mixedMoment B raw1335step1 raw1335step1Labels := by
      have ha : raw1335step1 = raw1335step0 := by apply Matrix.ext; unfold raw1335step1 raw1335step0; decide +kernel
      have hl : raw1335step0Labels = labelEmbedding7 ∘ raw1335step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1335step0 raw1335step0Labels raw1335step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4521 node4521Labels := by rfl

theorem canonical1336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1336 raw1336Labels = mixedMoment B node1105 node1105Labels := by
  calc
    mixedMoment B raw1336 raw1336Labels = mixedMoment B raw1336step0 raw1336step0Labels := by
      have ha : raw1336step0 = (fun i j => raw1336 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1336step0 raw1336; decide +kernel
      have hl : raw1336step0Labels = raw1336Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1336 raw1336Labels permutation152 permutation4
    _ = mixedMoment B node1105 node1105Labels := by rfl

theorem canonical1337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1337 raw1337Labels = mixedMoment B node1887 node1887Labels := by
  calc
    mixedMoment B raw1337 raw1337Labels = mixedMoment B raw1337step0 raw1337step0Labels := by
      have ha : raw1337step0 = (fun i j => raw1337 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1337step0 raw1337; decide +kernel
      have hl : raw1337step0Labels = raw1337Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1337 raw1337Labels permutation688 permutation6
    mixedMoment B raw1337step0 raw1337step0Labels = mixedMoment B raw1337step1 raw1337step1Labels := by
      have ha : raw1337step1 = raw1337step0 := by apply Matrix.ext; unfold raw1337step1 raw1337step0; decide +kernel
      have hl : raw1337step0Labels = labelEmbedding1 ∘ raw1337step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1337step0 raw1337step0Labels raw1337step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1887 node1887Labels := by rfl

theorem canonical1338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1338 raw1338Labels = mixedMoment B node4522 node4522Labels := by
  calc
    mixedMoment B raw1338 raw1338Labels = mixedMoment B raw1338step0 raw1338step0Labels := by
      have ha : raw1338step0 = (fun i j => raw1338 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1338step0 raw1338; decide +kernel
      have hl : raw1338step0Labels = raw1338Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1338 raw1338Labels permutation152 permutation4
    mixedMoment B raw1338step0 raw1338step0Labels = mixedMoment B raw1338step1 raw1338step1Labels := by
      have ha : raw1338step1 = raw1338step0 := by apply Matrix.ext; unfold raw1338step1 raw1338step0; decide +kernel
      have hl : raw1338step0Labels = labelEmbedding7 ∘ raw1338step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1338step0 raw1338step0Labels raw1338step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4522 node4522Labels := by rfl

theorem canonical1339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1339 raw1339Labels = mixedMoment B node1106 node1106Labels := by
  calc
    mixedMoment B raw1339 raw1339Labels = mixedMoment B raw1339step0 raw1339step0Labels := by
      have ha : raw1339step0 = (fun i j => raw1339 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1339step0 raw1339; decide +kernel
      have hl : raw1339step0Labels = raw1339Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1339 raw1339Labels permutation152 permutation4
    _ = mixedMoment B node1106 node1106Labels := by rfl

theorem canonical1340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1340 raw1340Labels = mixedMoment B node3249 node3249Labels := by
  calc
    mixedMoment B raw1340 raw1340Labels = mixedMoment B raw1340step0 raw1340step0Labels := by
      have ha : raw1340step0 = (fun i j => raw1340 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1340step0 raw1340; decide +kernel
      have hl : raw1340step0Labels = raw1340Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1340 raw1340Labels permutation152 permutation6
    mixedMoment B raw1340step0 raw1340step0Labels = mixedMoment B raw1340step1 raw1340step1Labels := by
      have ha : raw1340step1 = -raw1340step0 := by apply Matrix.ext; change ∀ i j, raw1340step1 i j = -(raw1340step0 i j); unfold raw1340step1 raw1340step0; decide +kernel
      have hl : raw1340step1Labels = raw1340step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1340step1 raw1340step1Labels = mixedMoment B raw1340step2 raw1340step2Labels := by
      have ha : raw1340step2 = raw1340step1 := by apply Matrix.ext; unfold raw1340step2 raw1340step1; decide +kernel
      have hl : raw1340step1Labels = labelEmbedding1 ∘ raw1340step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1340step1 raw1340step1Labels raw1340step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3249 node3249Labels := by rfl

theorem canonical1344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1344 raw1344Labels = mixedMoment B node4524 node4524Labels := by
  calc
    mixedMoment B raw1344 raw1344Labels = mixedMoment B raw1344step0 raw1344step0Labels := by
      have ha : raw1344step0 = (fun i j => raw1344 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1344step0 raw1344; decide +kernel
      have hl : raw1344step0Labels = raw1344Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1344 raw1344Labels permutation152 permutation4
    mixedMoment B raw1344step0 raw1344step0Labels = mixedMoment B raw1344step1 raw1344step1Labels := by
      have ha : raw1344step1 = raw1344step0 := by apply Matrix.ext; unfold raw1344step1 raw1344step0; decide +kernel
      have hl : raw1344step0Labels = labelEmbedding7 ∘ raw1344step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1344step0 raw1344step0Labels raw1344step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4524 node4524Labels := by rfl

theorem canonical1345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1345 raw1345Labels = mixedMoment B node1108 node1108Labels := by
  calc
    mixedMoment B raw1345 raw1345Labels = mixedMoment B raw1345step0 raw1345step0Labels := by
      have ha : raw1345step0 = (fun i j => raw1345 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1345step0 raw1345; decide +kernel
      have hl : raw1345step0Labels = raw1345Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1345 raw1345Labels permutation152 permutation4
    _ = mixedMoment B node1108 node1108Labels := by rfl

theorem canonical1346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1346 raw1346Labels = mixedMoment B node3251 node3251Labels := by
  calc
    mixedMoment B raw1346 raw1346Labels = mixedMoment B raw1346step0 raw1346step0Labels := by
      have ha : raw1346step0 = (fun i j => raw1346 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1346step0 raw1346; decide +kernel
      have hl : raw1346step0Labels = raw1346Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1346 raw1346Labels permutation152 permutation6
    mixedMoment B raw1346step0 raw1346step0Labels = mixedMoment B raw1346step1 raw1346step1Labels := by
      have ha : raw1346step1 = -raw1346step0 := by apply Matrix.ext; change ∀ i j, raw1346step1 i j = -(raw1346step0 i j); unfold raw1346step1 raw1346step0; decide +kernel
      have hl : raw1346step1Labels = raw1346step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1346step1 raw1346step1Labels = mixedMoment B raw1346step2 raw1346step2Labels := by
      have ha : raw1346step2 = raw1346step1 := by apply Matrix.ext; unfold raw1346step2 raw1346step1; decide +kernel
      have hl : raw1346step1Labels = labelEmbedding1 ∘ raw1346step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1346step1 raw1346step1Labels raw1346step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3251 node3251Labels := by rfl

theorem canonical1362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1362 raw1362Labels = mixedMoment B node4541 node4541Labels := by
  calc
    mixedMoment B raw1362 raw1362Labels = mixedMoment B raw1362step0 raw1362step0Labels := by
      have ha : raw1362step0 = (fun i j => raw1362 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1362step0 raw1362; decide +kernel
      have hl : raw1362step0Labels = raw1362Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1362 raw1362Labels permutation152 permutation4
    mixedMoment B raw1362step0 raw1362step0Labels = mixedMoment B raw1362step1 raw1362step1Labels := by
      have ha : raw1362step1 = raw1362step0 := by apply Matrix.ext; unfold raw1362step1 raw1362step0; decide +kernel
      have hl : raw1362step0Labels = labelEmbedding7 ∘ raw1362step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1362step0 raw1362step0Labels raw1362step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4541 node4541Labels := by rfl

theorem canonical1363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1363 raw1363Labels = mixedMoment B node1126 node1126Labels := by
  calc
    mixedMoment B raw1363 raw1363Labels = mixedMoment B raw1363step0 raw1363step0Labels := by
      have ha : raw1363step0 = (fun i j => raw1363 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1363step0 raw1363; decide +kernel
      have hl : raw1363step0Labels = raw1363Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1363 raw1363Labels permutation152 permutation4
    _ = mixedMoment B node1126 node1126Labels := by rfl

theorem canonical1364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1364 raw1364Labels = mixedMoment B node3256 node3256Labels := by
  calc
    mixedMoment B raw1364 raw1364Labels = mixedMoment B raw1364step0 raw1364step0Labels := by
      have ha : raw1364step0 = (fun i j => raw1364 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1364step0 raw1364; decide +kernel
      have hl : raw1364step0Labels = raw1364Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1364 raw1364Labels permutation152 permutation6
    mixedMoment B raw1364step0 raw1364step0Labels = mixedMoment B raw1364step1 raw1364step1Labels := by
      have ha : raw1364step1 = -raw1364step0 := by apply Matrix.ext; change ∀ i j, raw1364step1 i j = -(raw1364step0 i j); unfold raw1364step1 raw1364step0; decide +kernel
      have hl : raw1364step1Labels = raw1364step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1364step1 raw1364step1Labels = mixedMoment B raw1364step2 raw1364step2Labels := by
      have ha : raw1364step2 = raw1364step1 := by apply Matrix.ext; unfold raw1364step2 raw1364step1; decide +kernel
      have hl : raw1364step1Labels = labelEmbedding1 ∘ raw1364step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1364step1 raw1364step1Labels raw1364step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3256 node3256Labels := by rfl

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

theorem canonical1413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1413 raw1413Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw1413 raw1413Labels = mixedMoment B raw1413step0 raw1413step0Labels := by
      have ha : raw1413step0 = (fun i j => raw1413 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1413step0 raw1413; decide +kernel
      have hl : raw1413step0Labels = raw1413Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1413 raw1413Labels permutation152 permutation4
    mixedMoment B raw1413step0 raw1413step0Labels = mixedMoment B raw1413step1 raw1413step1Labels := by
      have ha : raw1413step1 = raw1413step0 := by apply Matrix.ext; unfold raw1413step1 raw1413step0; decide +kernel
      have hl : raw1413step0Labels = labelEmbedding7 ∘ raw1413step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1413step0 raw1413step0Labels raw1413step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

theorem canonical1414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1414 raw1414Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw1414 raw1414Labels = mixedMoment B raw1414step0 raw1414step0Labels := by
      have ha : raw1414step0 = (fun i j => raw1414 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1414step0 raw1414; decide +kernel
      have hl : raw1414step0Labels = raw1414Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1414 raw1414Labels permutation152 permutation4
    _ = mixedMoment B node1200 node1200Labels := by rfl

theorem canonical1415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1415 raw1415Labels = mixedMoment B node3281 node3281Labels := by
  calc
    mixedMoment B raw1415 raw1415Labels = mixedMoment B raw1415step0 raw1415step0Labels := by
      have ha : raw1415step0 = (fun i j => raw1415 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1415step0 raw1415; decide +kernel
      have hl : raw1415step0Labels = raw1415Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1415 raw1415Labels permutation152 permutation6
    mixedMoment B raw1415step0 raw1415step0Labels = mixedMoment B raw1415step1 raw1415step1Labels := by
      have ha : raw1415step1 = -raw1415step0 := by apply Matrix.ext; change ∀ i j, raw1415step1 i j = -(raw1415step0 i j); unfold raw1415step1 raw1415step0; decide +kernel
      have hl : raw1415step1Labels = raw1415step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1415step1 raw1415step1Labels = mixedMoment B raw1415step2 raw1415step2Labels := by
      have ha : raw1415step2 = raw1415step1 := by apply Matrix.ext; unfold raw1415step2 raw1415step1; decide +kernel
      have hl : raw1415step1Labels = labelEmbedding1 ∘ raw1415step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1415step1 raw1415step1Labels raw1415step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3281 node3281Labels := by rfl

theorem canonical1416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1416 raw1416Labels = mixedMoment B node4583 node4583Labels := by
  calc
    mixedMoment B raw1416 raw1416Labels = mixedMoment B raw1416step0 raw1416step0Labels := by
      have ha : raw1416step0 = (fun i j => raw1416 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1416step0 raw1416; decide +kernel
      have hl : raw1416step0Labels = raw1416Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1416 raw1416Labels permutation32 permutation4
    mixedMoment B raw1416step0 raw1416step0Labels = mixedMoment B raw1416step1 raw1416step1Labels := by
      have ha : raw1416step1 = raw1416step0 := by apply Matrix.ext; unfold raw1416step1 raw1416step0; decide +kernel
      have hl : raw1416step0Labels = labelEmbedding7 ∘ raw1416step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1416step0 raw1416step0Labels raw1416step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4583 node4583Labels := by rfl

theorem canonical1417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1417 raw1417Labels = mixedMoment B node1202 node1202Labels := by
  calc
    mixedMoment B raw1417 raw1417Labels = mixedMoment B raw1417step0 raw1417step0Labels := by
      have ha : raw1417step0 = (fun i j => raw1417 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1417step0 raw1417; decide +kernel
      have hl : raw1417step0Labels = raw1417Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1417 raw1417Labels permutation32 permutation4
    _ = mixedMoment B node1202 node1202Labels := by rfl

theorem canonical1418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1418 raw1418Labels = mixedMoment B node1942 node1942Labels := by
  calc
    mixedMoment B raw1418 raw1418Labels = mixedMoment B raw1418step0 raw1418step0Labels := by
      have ha : raw1418step0 = (fun i j => raw1418 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1418step0 raw1418; decide +kernel
      have hl : raw1418step0Labels = raw1418Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1418 raw1418Labels permutation149 permutation6
    mixedMoment B raw1418step0 raw1418step0Labels = mixedMoment B raw1418step1 raw1418step1Labels := by
      have ha : raw1418step1 = raw1418step0 := by apply Matrix.ext; unfold raw1418step1 raw1418step0; decide +kernel
      have hl : raw1418step0Labels = labelEmbedding1 ∘ raw1418step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1418step0 raw1418step0Labels raw1418step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1942 node1942Labels := by rfl

theorem canonical1419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1419 raw1419Labels = mixedMoment B node4586 node4586Labels := by
  calc
    mixedMoment B raw1419 raw1419Labels = mixedMoment B raw1419step0 raw1419step0Labels := by
      have ha : raw1419step0 = (fun i j => raw1419 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1419step0 raw1419; decide +kernel
      have hl : raw1419step0Labels = raw1419Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1419 raw1419Labels permutation32 permutation4
    mixedMoment B raw1419step0 raw1419step0Labels = mixedMoment B raw1419step1 raw1419step1Labels := by
      have ha : raw1419step1 = raw1419step0 := by apply Matrix.ext; unfold raw1419step1 raw1419step0; decide +kernel
      have hl : raw1419step0Labels = labelEmbedding7 ∘ raw1419step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1419step0 raw1419step0Labels raw1419step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4586 node4586Labels := by rfl

theorem canonical1420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1420 raw1420Labels = mixedMoment B node1205 node1205Labels := by
  calc
    mixedMoment B raw1420 raw1420Labels = mixedMoment B raw1420step0 raw1420step0Labels := by
      have ha : raw1420step0 = (fun i j => raw1420 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1420step0 raw1420; decide +kernel
      have hl : raw1420step0Labels = raw1420Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1420 raw1420Labels permutation32 permutation4
    _ = mixedMoment B node1205 node1205Labels := by rfl

theorem canonical1421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1421 raw1421Labels = mixedMoment B node3284 node3284Labels := by
  calc
    mixedMoment B raw1421 raw1421Labels = mixedMoment B raw1421step0 raw1421step0Labels := by
      have ha : raw1421step0 = (fun i j => raw1421 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1421step0 raw1421; decide +kernel
      have hl : raw1421step0Labels = raw1421Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1421 raw1421Labels permutation32 permutation6
    mixedMoment B raw1421step0 raw1421step0Labels = mixedMoment B raw1421step1 raw1421step1Labels := by
      have ha : raw1421step1 = -raw1421step0 := by apply Matrix.ext; change ∀ i j, raw1421step1 i j = -(raw1421step0 i j); unfold raw1421step1 raw1421step0; decide +kernel
      have hl : raw1421step1Labels = raw1421step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1421step1 raw1421step1Labels = mixedMoment B raw1421step2 raw1421step2Labels := by
      have ha : raw1421step2 = raw1421step1 := by apply Matrix.ext; unfold raw1421step2 raw1421step1; decide +kernel
      have hl : raw1421step1Labels = labelEmbedding1 ∘ raw1421step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1421step1 raw1421step1Labels raw1421step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3284 node3284Labels := by rfl

theorem canonical1422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1422 raw1422Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw1422 raw1422Labels = mixedMoment B raw1422step0 raw1422step0Labels := by
      have ha : raw1422step0 = (fun i j => raw1422 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1422step0 raw1422; decide +kernel
      have hl : raw1422step0Labels = raw1422Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1422 raw1422Labels permutation152 permutation4
    mixedMoment B raw1422step0 raw1422step0Labels = mixedMoment B raw1422step1 raw1422step1Labels := by
      have ha : raw1422step1 = raw1422step0 := by apply Matrix.ext; unfold raw1422step1 raw1422step0; decide +kernel
      have hl : raw1422step0Labels = labelEmbedding7 ∘ raw1422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1422step0 raw1422step0Labels raw1422step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical1423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1423 raw1423Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw1423 raw1423Labels = mixedMoment B raw1423step0 raw1423step0Labels := by
      have ha : raw1423step0 = (fun i j => raw1423 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1423step0 raw1423; decide +kernel
      have hl : raw1423step0Labels = raw1423Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1423 raw1423Labels permutation152 permutation4
    _ = mixedMoment B node1235 node1235Labels := by rfl

theorem canonical1424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1424 raw1424Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw1424 raw1424Labels = mixedMoment B raw1424step0 raw1424step0Labels := by
      have ha : raw1424step0 = (fun i j => raw1424 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1424step0 raw1424; decide +kernel
      have hl : raw1424step0Labels = raw1424Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1424 raw1424Labels permutation152 permutation6
    mixedMoment B raw1424step0 raw1424step0Labels = mixedMoment B raw1424step1 raw1424step1Labels := by
      have ha : raw1424step1 = -raw1424step0 := by apply Matrix.ext; change ∀ i j, raw1424step1 i j = -(raw1424step0 i j); unfold raw1424step1 raw1424step0; decide +kernel
      have hl : raw1424step1Labels = raw1424step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1424step1 raw1424step1Labels = mixedMoment B raw1424step2 raw1424step2Labels := by
      have ha : raw1424step2 = raw1424step1 := by apply Matrix.ext; unfold raw1424step2 raw1424step1; decide +kernel
      have hl : raw1424step1Labels = labelEmbedding1 ∘ raw1424step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1424step1 raw1424step1Labels raw1424step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3292 node3292Labels := by rfl

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

theorem canonical1428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1428 raw1428Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw1428 raw1428Labels = mixedMoment B raw1428step0 raw1428step0Labels := by
      have ha : raw1428step0 = (fun i j => raw1428 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1428step0 raw1428; decide +kernel
      have hl : raw1428step0Labels = raw1428Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1428 raw1428Labels permutation8 permutation4
    mixedMoment B raw1428step0 raw1428step0Labels = mixedMoment B raw1428step1 raw1428step1Labels := by
      have ha : raw1428step1 = raw1428step0 := by apply Matrix.ext; unfold raw1428step1 raw1428step0; decide +kernel
      have hl : raw1428step0Labels = labelEmbedding7 ∘ raw1428step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1428step0 raw1428step0Labels raw1428step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical1429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1429 raw1429Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw1429 raw1429Labels = mixedMoment B raw1429step0 raw1429step0Labels := by
      have ha : raw1429step0 = (fun i j => raw1429 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1429step0 raw1429; decide +kernel
      have hl : raw1429step0Labels = raw1429Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1429 raw1429Labels permutation8 permutation4
    _ = mixedMoment B node1239 node1239Labels := by rfl

theorem canonical1430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1430 raw1430Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw1430 raw1430Labels = mixedMoment B raw1430step0 raw1430step0Labels := by
      have ha : raw1430step0 = (fun i j => raw1430 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1430step0 raw1430; decide +kernel
      have hl : raw1430step0Labels = raw1430Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1430 raw1430Labels permutation31 permutation6
    mixedMoment B raw1430step0 raw1430step0Labels = mixedMoment B raw1430step1 raw1430step1Labels := by
      have ha : raw1430step1 = raw1430step0 := by apply Matrix.ext; unfold raw1430step1 raw1430step0; decide +kernel
      have hl : raw1430step0Labels = labelEmbedding1 ∘ raw1430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1430step0 raw1430step0Labels raw1430step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical1431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1431 raw1431Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw1431 raw1431Labels = mixedMoment B raw1431step0 raw1431step0Labels := by
      have ha : raw1431step0 = (fun i j => raw1431 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1431step0 raw1431; decide +kernel
      have hl : raw1431step0Labels = raw1431Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1431 raw1431Labels permutation32 permutation4
    mixedMoment B raw1431step0 raw1431step0Labels = mixedMoment B raw1431step1 raw1431step1Labels := by
      have ha : raw1431step1 = raw1431step0 := by apply Matrix.ext; unfold raw1431step1 raw1431step0; decide +kernel
      have hl : raw1431step0Labels = labelEmbedding7 ∘ raw1431step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1431step0 raw1431step0Labels raw1431step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical1432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1432 raw1432Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw1432 raw1432Labels = mixedMoment B raw1432step0 raw1432step0Labels := by
      have ha : raw1432step0 = (fun i j => raw1432 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1432step0 raw1432; decide +kernel
      have hl : raw1432step0Labels = raw1432Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1432 raw1432Labels permutation32 permutation4
    _ = mixedMoment B node1240 node1240Labels := by rfl

theorem canonical1433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1433 raw1433Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw1433 raw1433Labels = mixedMoment B raw1433step0 raw1433step0Labels := by
      have ha : raw1433step0 = (fun i j => raw1433 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1433step0 raw1433; decide +kernel
      have hl : raw1433step0Labels = raw1433Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1433 raw1433Labels permutation32 permutation6
    mixedMoment B raw1433step0 raw1433step0Labels = mixedMoment B raw1433step1 raw1433step1Labels := by
      have ha : raw1433step1 = -raw1433step0 := by apply Matrix.ext; change ∀ i j, raw1433step1 i j = -(raw1433step0 i j); unfold raw1433step1 raw1433step0; decide +kernel
      have hl : raw1433step1Labels = raw1433step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1433step1 raw1433step1Labels = mixedMoment B raw1433step2 raw1433step2Labels := by
      have ha : raw1433step2 = raw1433step1 := by apply Matrix.ext; unfold raw1433step2 raw1433step1; decide +kernel
      have hl : raw1433step1Labels = labelEmbedding1 ∘ raw1433step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1433step1 raw1433step1Labels raw1433step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

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

theorem canonical1449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1449 raw1449Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw1449 raw1449Labels = mixedMoment B raw1449step0 raw1449step0Labels := by
      have ha : raw1449step0 = (fun i j => raw1449 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1449step0 raw1449; decide +kernel
      have hl : raw1449step0Labels = raw1449Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1449 raw1449Labels permutation32 permutation4
    mixedMoment B raw1449step0 raw1449step0Labels = mixedMoment B raw1449step1 raw1449step1Labels := by
      have ha : raw1449step1 = raw1449step0 := by apply Matrix.ext; unfold raw1449step1 raw1449step0; decide +kernel
      have hl : raw1449step0Labels = labelEmbedding7 ∘ raw1449step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1449step0 raw1449step0Labels raw1449step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4622 node4622Labels := by rfl

theorem canonical1450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1450 raw1450Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw1450 raw1450Labels = mixedMoment B raw1450step0 raw1450step0Labels := by
      have ha : raw1450step0 = (fun i j => raw1450 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1450step0 raw1450; decide +kernel
      have hl : raw1450step0Labels = raw1450Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1450 raw1450Labels permutation32 permutation4
    _ = mixedMoment B node1299 node1299Labels := by rfl

theorem canonical1451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1451 raw1451Labels = mixedMoment B node3307 node3307Labels := by
  calc
    mixedMoment B raw1451 raw1451Labels = mixedMoment B raw1451step0 raw1451step0Labels := by
      have ha : raw1451step0 = (fun i j => raw1451 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1451step0 raw1451; decide +kernel
      have hl : raw1451step0Labels = raw1451Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1451 raw1451Labels permutation48 permutation3
    mixedMoment B raw1451step0 raw1451step0Labels = mixedMoment B raw1451step1 raw1451step1Labels := by
      have ha : raw1451step1 = -raw1451step0 := by apply Matrix.ext; change ∀ i j, raw1451step1 i j = -(raw1451step0 i j); unfold raw1451step1 raw1451step0; decide +kernel
      have hl : raw1451step1Labels = raw1451step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1451step1 raw1451step1Labels = mixedMoment B raw1451step2 raw1451step2Labels := by
      have ha : raw1451step2 = raw1451step1 := by apply Matrix.ext; unfold raw1451step2 raw1451step1; decide +kernel
      have hl : raw1451step1Labels = labelEmbedding1 ∘ raw1451step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1451step1 raw1451step1Labels raw1451step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3307 node3307Labels := by rfl

theorem canonical1452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1452 raw1452Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw1452 raw1452Labels = mixedMoment B raw1452step0 raw1452step0Labels := by
      have ha : raw1452step0 = (fun i j => raw1452 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1452step0 raw1452; decide +kernel
      have hl : raw1452step0Labels = raw1452Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1452 raw1452Labels permutation8 permutation4
    mixedMoment B raw1452step0 raw1452step0Labels = mixedMoment B raw1452step1 raw1452step1Labels := by
      have ha : raw1452step1 = raw1452step0 := by apply Matrix.ext; unfold raw1452step1 raw1452step0; decide +kernel
      have hl : raw1452step0Labels = labelEmbedding7 ∘ raw1452step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1452step0 raw1452step0Labels raw1452step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4623 node4623Labels := by rfl

theorem canonical1453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1453 raw1453Labels = mixedMoment B node1300 node1300Labels := by
  calc
    mixedMoment B raw1453 raw1453Labels = mixedMoment B raw1453step0 raw1453step0Labels := by
      have ha : raw1453step0 = (fun i j => raw1453 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1453step0 raw1453; decide +kernel
      have hl : raw1453step0Labels = raw1453Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1453 raw1453Labels permutation8 permutation4
    _ = mixedMoment B node1300 node1300Labels := by rfl

theorem canonical1454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1454 raw1454Labels = mixedMoment B node3308 node3308Labels := by
  calc
    mixedMoment B raw1454 raw1454Labels = mixedMoment B raw1454step0 raw1454step0Labels := by
      have ha : raw1454step0 = (fun i j => raw1454 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1454step0 raw1454; decide +kernel
      have hl : raw1454step0Labels = raw1454Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1454 raw1454Labels permutation8 permutation6
    mixedMoment B raw1454step0 raw1454step0Labels = mixedMoment B raw1454step1 raw1454step1Labels := by
      have ha : raw1454step1 = -raw1454step0 := by apply Matrix.ext; change ∀ i j, raw1454step1 i j = -(raw1454step0 i j); unfold raw1454step1 raw1454step0; decide +kernel
      have hl : raw1454step1Labels = raw1454step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1454step1 raw1454step1Labels = mixedMoment B raw1454step2 raw1454step2Labels := by
      have ha : raw1454step2 = raw1454step1 := by apply Matrix.ext; unfold raw1454step2 raw1454step1; decide +kernel
      have hl : raw1454step1Labels = labelEmbedding1 ∘ raw1454step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1454step1 raw1454step1Labels raw1454step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3308 node3308Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2175 raw2175Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw2175 raw2175Labels = mixedMoment B raw2175step0 raw2175step0Labels := by
      have ha : raw2175step0 = (fun i j => raw2175 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2175step0 raw2175; decide +kernel
      have hl : raw2175step0Labels = raw2175Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2175 raw2175Labels permutation152 permutation5
    mixedMoment B raw2175step0 raw2175step0Labels = mixedMoment B raw2175step1 raw2175step1Labels := by
      have ha : raw2175step1 = raw2175step0 := by apply Matrix.ext; unfold raw2175step1 raw2175step0; decide +kernel
      have hl : raw2175step0Labels = labelEmbedding8 ∘ raw2175step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2175step0 raw2175step0Labels raw2175step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

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

theorem canonical2176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2176 raw2176Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw2176 raw2176Labels = mixedMoment B raw2176step0 raw2176step0Labels := by
      have ha : raw2176step0 = (fun i j => raw2176 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2176step0 raw2176; decide +kernel
      have hl : raw2176step0Labels = raw2176Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2176 raw2176Labels permutation154 permutation4
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical2177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2177 raw2177Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw2177 raw2177Labels = mixedMoment B raw2177step0 raw2177step0Labels := by
      have ha : raw2177step0 = (fun i j => raw2177 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2177step0 raw2177; decide +kernel
      have hl : raw2177step0Labels = raw2177Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2177 raw2177Labels permutation162 permutation3
    mixedMoment B raw2177step0 raw2177step0Labels = mixedMoment B raw2177step1 raw2177step1Labels := by
      have ha : raw2177step1 = -raw2177step0 := by apply Matrix.ext; change ∀ i j, raw2177step1 i j = -(raw2177step0 i j); unfold raw2177step1 raw2177step0; decide +kernel
      have hl : raw2177step1Labels = raw2177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2177step1 raw2177step1Labels = mixedMoment B raw2177step2 raw2177step2Labels := by
      have ha : raw2177step2 = raw2177step1 := by apply Matrix.ext; unfold raw2177step2 raw2177step1; decide +kernel
      have hl : raw2177step1Labels = labelEmbedding1 ∘ raw2177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2177step1 raw2177step1Labels raw2177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

theorem canonical2232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2232 raw2232Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw2232 raw2232Labels = mixedMoment B raw2232step0 raw2232step0Labels := by
      have ha : raw2232step0 = (fun i j => raw2232 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2232step0 raw2232; decide +kernel
      have hl : raw2232step0Labels = raw2232Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2232 raw2232Labels permutation32 permutation5
    mixedMoment B raw2232step0 raw2232step0Labels = mixedMoment B raw2232step1 raw2232step1Labels := by
      have ha : raw2232step1 = raw2232step0 := by apply Matrix.ext; unfold raw2232step1 raw2232step0; decide +kernel
      have hl : raw2232step0Labels = labelEmbedding8 ∘ raw2232step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2232step0 raw2232step0Labels raw2232step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

theorem canonical2233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2233 raw2233Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw2233 raw2233Labels = mixedMoment B raw2233step0 raw2233step0Labels := by
      have ha : raw2233step0 = (fun i j => raw2233 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2233step0 raw2233; decide +kernel
      have hl : raw2233step0Labels = raw2233Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2233 raw2233Labels permutation34 permutation4
    _ = mixedMoment B node2881 node2881Labels := by rfl

theorem canonical2234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2234 raw2234Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw2234 raw2234Labels = mixedMoment B raw2234step0 raw2234step0Labels := by
      have ha : raw2234step0 = (fun i j => raw2234 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2234step0 raw2234; decide +kernel
      have hl : raw2234step0Labels = raw2234Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2234 raw2234Labels permutation42 permutation3
    mixedMoment B raw2234step0 raw2234step0Labels = mixedMoment B raw2234step1 raw2234step1Labels := by
      have ha : raw2234step1 = -raw2234step0 := by apply Matrix.ext; change ∀ i j, raw2234step1 i j = -(raw2234step0 i j); unfold raw2234step1 raw2234step0; decide +kernel
      have hl : raw2234step1Labels = raw2234step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2234step1 raw2234step1Labels = mixedMoment B raw2234step2 raw2234step2Labels := by
      have ha : raw2234step2 = raw2234step1 := by apply Matrix.ext; unfold raw2234step2 raw2234step1; decide +kernel
      have hl : raw2234step1Labels = labelEmbedding1 ∘ raw2234step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2234step1 raw2234step1Labels raw2234step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

theorem canonical2289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2289 raw2289Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw2289 raw2289Labels = mixedMoment B raw2289step0 raw2289step0Labels := by
      have ha : raw2289step0 = (fun i j => raw2289 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2289step0 raw2289; decide +kernel
      have hl : raw2289step0Labels = raw2289Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2289 raw2289Labels permutation32 permutation5
    mixedMoment B raw2289step0 raw2289step0Labels = mixedMoment B raw2289step1 raw2289step1Labels := by
      have ha : raw2289step1 = raw2289step0 := by apply Matrix.ext; unfold raw2289step1 raw2289step0; decide +kernel
      have hl : raw2289step0Labels = labelEmbedding8 ∘ raw2289step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2289step0 raw2289step0Labels raw2289step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2290 raw2290Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw2290 raw2290Labels = mixedMoment B raw2290step0 raw2290step0Labels := by
      have ha : raw2290step0 = (fun i j => raw2290 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2290step0 raw2290; decide +kernel
      have hl : raw2290step0Labels = raw2290Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2290 raw2290Labels permutation32 permutation4
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2291 raw2291Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw2291 raw2291Labels = mixedMoment B raw2291step0 raw2291step0Labels := by
      have ha : raw2291step0 = (fun i j => raw2291 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2291step0 raw2291; decide +kernel
      have hl : raw2291step0Labels = raw2291Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2291 raw2291Labels permutation48 permutation3
    mixedMoment B raw2291step0 raw2291step0Labels = mixedMoment B raw2291step1 raw2291step1Labels := by
      have ha : raw2291step1 = -raw2291step0 := by apply Matrix.ext; change ∀ i j, raw2291step1 i j = -(raw2291step0 i j); unfold raw2291step1 raw2291step0; decide +kernel
      have hl : raw2291step1Labels = raw2291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2291step1 raw2291step1Labels = mixedMoment B raw2291step2 raw2291step2Labels := by
      have ha : raw2291step2 = raw2291step1 := by apply Matrix.ext; unfold raw2291step2 raw2291step1; decide +kernel
      have hl : raw2291step1Labels = labelEmbedding1 ∘ raw2291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2291step1 raw2291step1Labels raw2291step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

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

theorem canonical2304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2304 raw2304Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw2304 raw2304Labels = mixedMoment B raw2304step0 raw2304step0Labels := by
      have ha : raw2304step0 = (fun i j => raw2304 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2304step0 raw2304; decide +kernel
      have hl : raw2304step0Labels = raw2304Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2304 raw2304Labels permutation8 permutation4
    mixedMoment B raw2304step0 raw2304step0Labels = mixedMoment B raw2304step1 raw2304step1Labels := by
      have ha : raw2304step1 = raw2304step0 := by apply Matrix.ext; unfold raw2304step1 raw2304step0; decide +kernel
      have hl : raw2304step0Labels = labelEmbedding7 ∘ raw2304step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2304step0 raw2304step0Labels raw2304step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

theorem canonical2305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2305 raw2305Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw2305 raw2305Labels = mixedMoment B raw2305step0 raw2305step0Labels := by
      have ha : raw2305step0 = (fun i j => raw2305 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2305step0 raw2305; decide +kernel
      have hl : raw2305step0Labels = raw2305Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2305 raw2305Labels permutation8 permutation4
    _ = mixedMoment B node2768 node2768Labels := by rfl

theorem canonical2306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2306 raw2306Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw2306 raw2306Labels = mixedMoment B raw2306step0 raw2306step0Labels := by
      have ha : raw2306step0 = (fun i j => raw2306 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2306step0 raw2306; decide +kernel
      have hl : raw2306step0Labels = raw2306Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2306 raw2306Labels permutation12 permutation6
    mixedMoment B raw2306step0 raw2306step0Labels = mixedMoment B raw2306step1 raw2306step1Labels := by
      have ha : raw2306step1 = -raw2306step0 := by apply Matrix.ext; change ∀ i j, raw2306step1 i j = -(raw2306step0 i j); unfold raw2306step1 raw2306step0; decide +kernel
      have hl : raw2306step1Labels = raw2306step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2306step1 raw2306step1Labels = mixedMoment B raw2306step2 raw2306step2Labels := by
      have ha : raw2306step2 = raw2306step1 := by apply Matrix.ext; unfold raw2306step2 raw2306step1; decide +kernel
      have hl : raw2306step1Labels = labelEmbedding1 ∘ raw2306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2306step1 raw2306step1Labels raw2306step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3632 node3632Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical193
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24752 raw24752Labels = mixedMoment B node5149 node5149Labels := by
  calc
    _ = mixedMoment B node5149 node5149Labels := by rfl

theorem canonical24753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24753 raw24753Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw24753 raw24753Labels = mixedMoment B raw24753step0 raw24753step0Labels := by
      have hz : ∀ j, raw24753 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24753step0 = (fun i j => raw24753 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24753step0 raw24753; decide +kernel
      have hl : raw24753step0Labels = raw24753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24753 raw24753Labels permutation265 hz
    _ = mixedMoment B node5204 node5204Labels := by rfl

theorem canonical24754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24754 raw24754Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw24754 raw24754Labels = mixedMoment B raw24754step0 raw24754step0Labels := by
      have hz : ∀ j, raw24754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24754step0 = (fun i j => raw24754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24754step0 raw24754; decide +kernel
      have hl : raw24754step0Labels = raw24754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24754 raw24754Labels permutation434 hz
    mixedMoment B raw24754step0 raw24754step0Labels = mixedMoment B raw24754step1 raw24754step1Labels := by
      have hz : ∀ j, raw24754step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24754step1 = (fun i j => raw24754step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24754step1 raw24754step0; decide +kernel
      have hl : raw24754step1Labels = raw24754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24754step0 raw24754step0Labels permutation56 hz
    _ = mixedMoment B node5294 node5294Labels := by rfl

theorem canonical24755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24755 raw24755Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw24755 raw24755Labels = mixedMoment B raw24755step0 raw24755step0Labels := by
      have hz : ∀ j, raw24755 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24755step0 = (fun i j => raw24755 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24755step0 raw24755; decide +kernel
      have hl : raw24755step0Labels = raw24755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24755 raw24755Labels permutation265 hz
    mixedMoment B raw24755step0 raw24755step0Labels = mixedMoment B raw24755step1 raw24755step1Labels := by
      have ha : raw24755step1 = (fun i j => raw24755step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24755step1 raw24755step0; decide +kernel
      have hl : raw24755step1Labels = raw24755step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24755step0 raw24755step0Labels permutation34 permutation2
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical24756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24756 raw24756Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw24756 raw24756Labels = mixedMoment B raw24756step0 raw24756step0Labels := by
      have hz : ∀ j, raw24756 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24756step0 = (fun i j => raw24756 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24756step0 raw24756; decide +kernel
      have hl : raw24756step0Labels = raw24756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24756 raw24756Labels permutation265 hz
    mixedMoment B raw24756step0 raw24756step0Labels = mixedMoment B raw24756step1 raw24756step1Labels := by
      have ha : raw24756step1 = (fun i j => raw24756step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24756step1 raw24756step0; decide +kernel
      have hl : raw24756step1Labels = raw24756step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24756step0 raw24756step0Labels permutation33 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical24757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24757 raw24757Labels = mixedMoment B node4139 node4139Labels := by
  calc
    mixedMoment B raw24757 raw24757Labels = mixedMoment B raw24757step0 raw24757step0Labels := by
      have ha : raw24757step0 = (fun i j => raw24757 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24757step0 raw24757; decide +kernel
      have hl : raw24757step0Labels = raw24757Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24757 raw24757Labels permutation188 permutation3
    mixedMoment B raw24757step0 raw24757step0Labels = mixedMoment B raw24757step1 raw24757step1Labels := by
      have ha : raw24757step1 = raw24757step0 := by apply Matrix.ext; unfold raw24757step1 raw24757step0; decide +kernel
      have hl : raw24757step0Labels = labelEmbedding6 ∘ raw24757step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24757step0 raw24757step0Labels raw24757step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4139 node4139Labels := by rfl

theorem canonical24758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24758 raw24758Labels = mixedMoment B node4513 node4513Labels := by
  calc
    mixedMoment B raw24758 raw24758Labels = mixedMoment B raw24758step0 raw24758step0Labels := by
      have ha : raw24758step0 = (fun i j => raw24758 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24758step0 raw24758; decide +kernel
      have hl : raw24758step0Labels = raw24758Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24758 raw24758Labels permutation188 permutation3
    mixedMoment B raw24758step0 raw24758step0Labels = mixedMoment B raw24758step1 raw24758step1Labels := by
      have ha : raw24758step1 = raw24758step0 := by apply Matrix.ext; unfold raw24758step1 raw24758step0; decide +kernel
      have hl : raw24758step0Labels = labelEmbedding6 ∘ raw24758step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24758step0 raw24758step0Labels raw24758step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4513 node4513Labels := by rfl

theorem canonical24759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24759 raw24759Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24759 raw24759Labels = mixedMoment B raw24759step0 raw24759step0Labels := by
      have hz : ∀ j, raw24759 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24759step0 = (fun i j => raw24759 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24759step0 raw24759; decide +kernel
      have hl : raw24759step0Labels = raw24759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24759 raw24759Labels permutation434 hz
    mixedMoment B raw24759step0 raw24759step0Labels = mixedMoment B raw24759step1 raw24759step1Labels := by
      have ha : raw24759step1 = (fun i j => raw24759step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24759step1 raw24759step0; decide +kernel
      have hl : raw24759step1Labels = raw24759step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24759step0 raw24759step0Labels permutation40 permutation3
    mixedMoment B raw24759step1 raw24759step1Labels = mixedMoment B raw24759step2 raw24759step2Labels := by
      have ha : raw24759step2 = raw24759step1 := by apply Matrix.ext; unfold raw24759step2 raw24759step1; decide +kernel
      have hl : raw24759step1Labels = labelEmbedding6 ∘ raw24759step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24759step1 raw24759step1Labels raw24759step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical24760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24760 raw24760Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw24760 raw24760Labels = mixedMoment B raw24760step0 raw24760step0Labels := by
      have ha : raw24760step0 = (fun i j => raw24760 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24760step0 raw24760; decide +kernel
      have hl : raw24760step0Labels = raw24760Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24760 raw24760Labels permutation188 permutation3
    mixedMoment B raw24760step0 raw24760step0Labels = mixedMoment B raw24760step1 raw24760step1Labels := by
      have ha : raw24760step1 = raw24760step0 := by apply Matrix.ext; unfold raw24760step1 raw24760step0; decide +kernel
      have hl : raw24760step0Labels = labelEmbedding6 ∘ raw24760step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24760step0 raw24760step0Labels raw24760step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

theorem canonical24761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24761 raw24761Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw24761 raw24761Labels = mixedMoment B raw24761step0 raw24761step0Labels := by
      have ha : raw24761step0 = (fun i j => raw24761 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24761step0 raw24761; decide +kernel
      have hl : raw24761step0Labels = raw24761Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24761 raw24761Labels permutation188 permutation3
    mixedMoment B raw24761step0 raw24761step0Labels = mixedMoment B raw24761step1 raw24761step1Labels := by
      have ha : raw24761step1 = raw24761step0 := by apply Matrix.ext; unfold raw24761step1 raw24761step0; decide +kernel
      have hl : raw24761step0Labels = labelEmbedding6 ∘ raw24761step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24761step0 raw24761step0Labels raw24761step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical24762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24762 raw24762Labels = mixedMoment B node4172 node4172Labels := by
  calc
    mixedMoment B raw24762 raw24762Labels = mixedMoment B raw24762step0 raw24762step0Labels := by
      have hz : ∀ j, raw24762 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24762step0 = (fun i j => raw24762 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24762step0 raw24762; decide +kernel
      have hl : raw24762step0Labels = raw24762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24762 raw24762Labels permutation265 hz
    mixedMoment B raw24762step0 raw24762step0Labels = mixedMoment B raw24762step1 raw24762step1Labels := by
      have ha : raw24762step1 = (fun i j => raw24762step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24762step1 raw24762step0; decide +kernel
      have hl : raw24762step1Labels = raw24762step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24762step0 raw24762step0Labels permutation34 permutation3
    mixedMoment B raw24762step1 raw24762step1Labels = mixedMoment B raw24762step2 raw24762step2Labels := by
      have ha : raw24762step2 = raw24762step1 := by apply Matrix.ext; unfold raw24762step2 raw24762step1; decide +kernel
      have hl : raw24762step1Labels = labelEmbedding6 ∘ raw24762step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24762step1 raw24762step1Labels raw24762step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4172 node4172Labels := by rfl

theorem canonical24763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24763 raw24763Labels = mixedMoment B node4541 node4541Labels := by
  calc
    mixedMoment B raw24763 raw24763Labels = mixedMoment B raw24763step0 raw24763step0Labels := by
      have ha : raw24763step0 = (fun i j => raw24763 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24763step0 raw24763; decide +kernel
      have hl : raw24763step0Labels = raw24763Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24763 raw24763Labels permutation154 permutation3
    mixedMoment B raw24763step0 raw24763step0Labels = mixedMoment B raw24763step1 raw24763step1Labels := by
      have ha : raw24763step1 = raw24763step0 := by apply Matrix.ext; unfold raw24763step1 raw24763step0; decide +kernel
      have hl : raw24763step0Labels = labelEmbedding6 ∘ raw24763step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24763step0 raw24763step0Labels raw24763step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4541 node4541Labels := by rfl

theorem canonical24764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24764 raw24764Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw24764 raw24764Labels = mixedMoment B raw24764step0 raw24764step0Labels := by
      have hz : ∀ j, raw24764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24764step0 = (fun i j => raw24764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24764step0 raw24764; decide +kernel
      have hl : raw24764step0Labels = raw24764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24764 raw24764Labels permutation434 hz
    mixedMoment B raw24764step0 raw24764step0Labels = mixedMoment B raw24764step1 raw24764step1Labels := by
      have hz : ∀ j, raw24764step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24764step1 = (fun i j => raw24764step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24764step1 raw24764step0; decide +kernel
      have hl : raw24764step1Labels = raw24764step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24764step0 raw24764step0Labels permutation56 hz
    mixedMoment B raw24764step1 raw24764step1Labels = mixedMoment B raw24764step2 raw24764step2Labels := by
      have ha : raw24764step2 = (fun i j => raw24764step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24764step2 raw24764step1; decide +kernel
      have hl : raw24764step2Labels = raw24764step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24764step1 raw24764step1Labels permutation8 permutation3
    mixedMoment B raw24764step2 raw24764step2Labels = mixedMoment B raw24764step3 raw24764step3Labels := by
      have ha : raw24764step3 = raw24764step2 := by apply Matrix.ext; unfold raw24764step3 raw24764step2; decide +kernel
      have hl : raw24764step2Labels = labelEmbedding6 ∘ raw24764step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24764step2 raw24764step2Labels raw24764step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4623 node4623Labels := by rfl

theorem canonical24765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24765 raw24765Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24765 raw24765Labels = mixedMoment B raw24765step0 raw24765step0Labels := by
      have hz : ∀ j, raw24765 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24765step0 = (fun i j => raw24765 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24765step0 raw24765; decide +kernel
      have hl : raw24765step0Labels = raw24765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24765 raw24765Labels permutation265 hz
    mixedMoment B raw24765step0 raw24765step0Labels = mixedMoment B raw24765step1 raw24765step1Labels := by
      have ha : raw24765step1 = (fun i j => raw24765step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24765step1 raw24765step0; decide +kernel
      have hl : raw24765step1Labels = raw24765step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24765step0 raw24765step0Labels permutation44 permutation3
    mixedMoment B raw24765step1 raw24765step1Labels = mixedMoment B raw24765step2 raw24765step2Labels := by
      have ha : raw24765step2 = raw24765step1 := by apply Matrix.ext; unfold raw24765step2 raw24765step1; decide +kernel
      have hl : raw24765step1Labels = labelEmbedding6 ∘ raw24765step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24765step1 raw24765step1Labels raw24765step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical24766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24766 raw24766Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw24766 raw24766Labels = mixedMoment B raw24766step0 raw24766step0Labels := by
      have hz : ∀ j, raw24766 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24766step0 = (fun i j => raw24766 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24766step0 raw24766; decide +kernel
      have hl : raw24766step0Labels = raw24766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24766 raw24766Labels permutation265 hz
    mixedMoment B raw24766step0 raw24766step0Labels = mixedMoment B raw24766step1 raw24766step1Labels := by
      have ha : raw24766step1 = (fun i j => raw24766step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24766step1 raw24766step0; decide +kernel
      have hl : raw24766step1Labels = raw24766step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24766step0 raw24766step0Labels permutation42 permutation2
    _ = mixedMoment B node4622 node4622Labels := by rfl

theorem canonical24767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24767 raw24767Labels = mixedMoment B node4141 node4141Labels := by
  calc
    mixedMoment B raw24767 raw24767Labels = mixedMoment B raw24767step0 raw24767step0Labels := by
      have hz : ∀ j, raw24767 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24767step0 = (fun i j => raw24767 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24767step0 raw24767; decide +kernel
      have hl : raw24767step0Labels = raw24767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24767 raw24767Labels permutation265 hz
    mixedMoment B raw24767step0 raw24767step0Labels = mixedMoment B raw24767step1 raw24767step1Labels := by
      have ha : raw24767step1 = (fun i j => raw24767step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24767step1 raw24767step0; decide +kernel
      have hl : raw24767step1Labels = raw24767step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24767step0 raw24767step0Labels permutation34 permutation3
    mixedMoment B raw24767step1 raw24767step1Labels = mixedMoment B raw24767step2 raw24767step2Labels := by
      have ha : raw24767step2 = raw24767step1 := by apply Matrix.ext; unfold raw24767step2 raw24767step1; decide +kernel
      have hl : raw24767step1Labels = labelEmbedding6 ∘ raw24767step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24767step1 raw24767step1Labels raw24767step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4141 node4141Labels := by rfl

theorem canonical24768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24768 raw24768Labels = mixedMoment B node4522 node4522Labels := by
  calc
    mixedMoment B raw24768 raw24768Labels = mixedMoment B raw24768step0 raw24768step0Labels := by
      have ha : raw24768step0 = (fun i j => raw24768 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24768step0 raw24768; decide +kernel
      have hl : raw24768step0Labels = raw24768Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24768 raw24768Labels permutation154 permutation3
    mixedMoment B raw24768step0 raw24768step0Labels = mixedMoment B raw24768step1 raw24768step1Labels := by
      have ha : raw24768step1 = raw24768step0 := by apply Matrix.ext; unfold raw24768step1 raw24768step0; decide +kernel
      have hl : raw24768step0Labels = labelEmbedding6 ∘ raw24768step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24768step0 raw24768step0Labels raw24768step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4522 node4522Labels := by rfl

theorem canonical24769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24769 raw24769Labels = mixedMoment B node4515 node4515Labels := by
  calc
    mixedMoment B raw24769 raw24769Labels = mixedMoment B raw24769step0 raw24769step0Labels := by
      have hz : ∀ j, raw24769 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24769step0 = (fun i j => raw24769 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24769step0 raw24769; decide +kernel
      have hl : raw24769step0Labels = raw24769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24769 raw24769Labels permutation265 hz
    mixedMoment B raw24769step0 raw24769step0Labels = mixedMoment B raw24769step1 raw24769step1Labels := by
      have ha : raw24769step1 = (fun i j => raw24769step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24769step1 raw24769step0; decide +kernel
      have hl : raw24769step1Labels = raw24769step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24769step0 raw24769step0Labels permutation34 permutation3
    mixedMoment B raw24769step1 raw24769step1Labels = mixedMoment B raw24769step2 raw24769step2Labels := by
      have ha : raw24769step2 = raw24769step1 := by apply Matrix.ext; unfold raw24769step2 raw24769step1; decide +kernel
      have hl : raw24769step1Labels = labelEmbedding6 ∘ raw24769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24769step1 raw24769step1Labels raw24769step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4515 node4515Labels := by rfl

theorem canonical24770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24770 raw24770Labels = mixedMoment B node4586 node4586Labels := by
  calc
    mixedMoment B raw24770 raw24770Labels = mixedMoment B raw24770step0 raw24770step0Labels := by
      have hz : ∀ j, raw24770 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24770step0 = (fun i j => raw24770 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24770step0 raw24770; decide +kernel
      have hl : raw24770step0Labels = raw24770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24770 raw24770Labels permutation265 hz
    mixedMoment B raw24770step0 raw24770step0Labels = mixedMoment B raw24770step1 raw24770step1Labels := by
      have ha : raw24770step1 = (fun i j => raw24770step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24770step1 raw24770step0; decide +kernel
      have hl : raw24770step1Labels = raw24770step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24770step0 raw24770step0Labels permutation34 permutation3
    mixedMoment B raw24770step1 raw24770step1Labels = mixedMoment B raw24770step2 raw24770step2Labels := by
      have ha : raw24770step2 = raw24770step1 := by apply Matrix.ext; unfold raw24770step2 raw24770step1; decide +kernel
      have hl : raw24770step1Labels = labelEmbedding6 ∘ raw24770step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24770step1 raw24770step1Labels raw24770step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4586 node4586Labels := by rfl

theorem canonical24771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24771 raw24771Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24771 raw24771Labels = mixedMoment B raw24771step0 raw24771step0Labels := by
      have hz : ∀ j, raw24771 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24771step0 = (fun i j => raw24771 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24771step0 raw24771; decide +kernel
      have hl : raw24771step0Labels = raw24771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24771 raw24771Labels permutation265 hz
    mixedMoment B raw24771step0 raw24771step0Labels = mixedMoment B raw24771step1 raw24771step1Labels := by
      have ha : raw24771step1 = (fun i j => raw24771step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24771step1 raw24771step0; decide +kernel
      have hl : raw24771step1Labels = raw24771step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24771step0 raw24771step0Labels permutation35 permutation3
    mixedMoment B raw24771step1 raw24771step1Labels = mixedMoment B raw24771step2 raw24771step2Labels := by
      have ha : raw24771step2 = raw24771step1 := by apply Matrix.ext; unfold raw24771step2 raw24771step1; decide +kernel
      have hl : raw24771step1Labels = labelEmbedding6 ∘ raw24771step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24771step1 raw24771step1Labels raw24771step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical24772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24772 raw24772Labels = mixedMoment B node4145 node4145Labels := by
  calc
    mixedMoment B raw24772 raw24772Labels = mixedMoment B raw24772step0 raw24772step0Labels := by
      have hz : ∀ j, raw24772 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24772step0 = (fun i j => raw24772 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24772step0 raw24772; decide +kernel
      have hl : raw24772step0Labels = raw24772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24772 raw24772Labels permutation265 hz
    mixedMoment B raw24772step0 raw24772step0Labels = mixedMoment B raw24772step1 raw24772step1Labels := by
      have ha : raw24772step1 = (fun i j => raw24772step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24772step1 raw24772step0; decide +kernel
      have hl : raw24772step1Labels = raw24772step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24772step0 raw24772step0Labels permutation32 permutation3
    mixedMoment B raw24772step1 raw24772step1Labels = mixedMoment B raw24772step2 raw24772step2Labels := by
      have ha : raw24772step2 = raw24772step1 := by apply Matrix.ext; unfold raw24772step2 raw24772step1; decide +kernel
      have hl : raw24772step1Labels = labelEmbedding6 ∘ raw24772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24772step1 raw24772step1Labels raw24772step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4145 node4145Labels := by rfl

theorem canonical24773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24773 raw24773Labels = mixedMoment B node4524 node4524Labels := by
  calc
    mixedMoment B raw24773 raw24773Labels = mixedMoment B raw24773step0 raw24773step0Labels := by
      have ha : raw24773step0 = (fun i j => raw24773 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24773step0 raw24773; decide +kernel
      have hl : raw24773step0Labels = raw24773Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24773 raw24773Labels permutation152 permutation3
    mixedMoment B raw24773step0 raw24773step0Labels = mixedMoment B raw24773step1 raw24773step1Labels := by
      have ha : raw24773step1 = raw24773step0 := by apply Matrix.ext; unfold raw24773step1 raw24773step0; decide +kernel
      have hl : raw24773step0Labels = labelEmbedding6 ∘ raw24773step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24773step0 raw24773step0Labels raw24773step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4524 node4524Labels := by rfl

theorem canonical24774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24774 raw24774Labels = mixedMoment B node4518 node4518Labels := by
  calc
    mixedMoment B raw24774 raw24774Labels = mixedMoment B raw24774step0 raw24774step0Labels := by
      have hz : ∀ j, raw24774 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24774step0 = (fun i j => raw24774 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24774step0 raw24774; decide +kernel
      have hl : raw24774step0Labels = raw24774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24774 raw24774Labels permutation265 hz
    mixedMoment B raw24774step0 raw24774step0Labels = mixedMoment B raw24774step1 raw24774step1Labels := by
      have ha : raw24774step1 = (fun i j => raw24774step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24774step1 raw24774step0; decide +kernel
      have hl : raw24774step1Labels = raw24774step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24774step0 raw24774step0Labels permutation32 permutation3
    mixedMoment B raw24774step1 raw24774step1Labels = mixedMoment B raw24774step2 raw24774step2Labels := by
      have ha : raw24774step2 = raw24774step1 := by apply Matrix.ext; unfold raw24774step2 raw24774step1; decide +kernel
      have hl : raw24774step1Labels = labelEmbedding6 ∘ raw24774step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24774step1 raw24774step1Labels raw24774step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4518 node4518Labels := by rfl

theorem canonical24775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24775 raw24775Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw24775 raw24775Labels = mixedMoment B raw24775step0 raw24775step0Labels := by
      have hz : ∀ j, raw24775 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24775step0 = (fun i j => raw24775 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24775step0 raw24775; decide +kernel
      have hl : raw24775step0Labels = raw24775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24775 raw24775Labels permutation434 hz
    mixedMoment B raw24775step0 raw24775step0Labels = mixedMoment B raw24775step1 raw24775step1Labels := by
      have hz : ∀ j, raw24775step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24775step1 = (fun i j => raw24775step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24775step1 raw24775step0; decide +kernel
      have hl : raw24775step1Labels = raw24775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24775step0 raw24775step0Labels permutation56 hz
    mixedMoment B raw24775step1 raw24775step1Labels = mixedMoment B raw24775step2 raw24775step2Labels := by
      have ha : raw24775step2 = (fun i j => raw24775step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24775step2 raw24775step1; decide +kernel
      have hl : raw24775step2Labels = raw24775step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24775step1 raw24775step1Labels permutation8 permutation3
    mixedMoment B raw24775step2 raw24775step2Labels = mixedMoment B raw24775step3 raw24775step3Labels := by
      have ha : raw24775step3 = raw24775step2 := by apply Matrix.ext; unfold raw24775step3 raw24775step2; decide +kernel
      have hl : raw24775step2Labels = labelEmbedding6 ∘ raw24775step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24775step2 raw24775step2Labels raw24775step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical24776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24776 raw24776Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw24776 raw24776Labels = mixedMoment B raw24776step0 raw24776step0Labels := by
      have hz : ∀ j, raw24776 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24776step0 = (fun i j => raw24776 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24776step0 raw24776; decide +kernel
      have hl : raw24776step0Labels = raw24776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24776 raw24776Labels permutation265 hz
    mixedMoment B raw24776step0 raw24776step0Labels = mixedMoment B raw24776step1 raw24776step1Labels := by
      have ha : raw24776step1 = (fun i j => raw24776step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24776step1 raw24776step0; decide +kernel
      have hl : raw24776step1Labels = raw24776step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24776step0 raw24776step0Labels permutation33 permutation3
    mixedMoment B raw24776step1 raw24776step1Labels = mixedMoment B raw24776step2 raw24776step2Labels := by
      have ha : raw24776step2 = raw24776step1 := by apply Matrix.ext; unfold raw24776step2 raw24776step1; decide +kernel
      have hl : raw24776step1Labels = labelEmbedding6 ∘ raw24776step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24776step1 raw24776step1Labels raw24776step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical24777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24777 raw24777Labels = mixedMoment B node4140 node4140Labels := by
  calc
    mixedMoment B raw24777 raw24777Labels = mixedMoment B raw24777step0 raw24777step0Labels := by
      have hz : ∀ j, raw24777 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24777step0 = (fun i j => raw24777 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24777step0 raw24777; decide +kernel
      have hl : raw24777step0Labels = raw24777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24777 raw24777Labels permutation265 hz
    mixedMoment B raw24777step0 raw24777step0Labels = mixedMoment B raw24777step1 raw24777step1Labels := by
      have ha : raw24777step1 = (fun i j => raw24777step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24777step1 raw24777step0; decide +kernel
      have hl : raw24777step1Labels = raw24777step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24777step0 raw24777step0Labels permutation34 permutation3
    mixedMoment B raw24777step1 raw24777step1Labels = mixedMoment B raw24777step2 raw24777step2Labels := by
      have ha : raw24777step2 = raw24777step1 := by apply Matrix.ext; unfold raw24777step2 raw24777step1; decide +kernel
      have hl : raw24777step1Labels = labelEmbedding6 ∘ raw24777step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24777step1 raw24777step1Labels raw24777step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4140 node4140Labels := by rfl

theorem canonical24778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24778 raw24778Labels = mixedMoment B node4521 node4521Labels := by
  calc
    mixedMoment B raw24778 raw24778Labels = mixedMoment B raw24778step0 raw24778step0Labels := by
      have ha : raw24778step0 = (fun i j => raw24778 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24778step0 raw24778; decide +kernel
      have hl : raw24778step0Labels = raw24778Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24778 raw24778Labels permutation154 permutation3
    mixedMoment B raw24778step0 raw24778step0Labels = mixedMoment B raw24778step1 raw24778step1Labels := by
      have ha : raw24778step1 = raw24778step0 := by apply Matrix.ext; unfold raw24778step1 raw24778step0; decide +kernel
      have hl : raw24778step0Labels = labelEmbedding6 ∘ raw24778step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24778step0 raw24778step0Labels raw24778step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4521 node4521Labels := by rfl

theorem canonical24779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24779 raw24779Labels = mixedMoment B node4514 node4514Labels := by
  calc
    mixedMoment B raw24779 raw24779Labels = mixedMoment B raw24779step0 raw24779step0Labels := by
      have hz : ∀ j, raw24779 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24779step0 = (fun i j => raw24779 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24779step0 raw24779; decide +kernel
      have hl : raw24779step0Labels = raw24779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24779 raw24779Labels permutation265 hz
    mixedMoment B raw24779step0 raw24779step0Labels = mixedMoment B raw24779step1 raw24779step1Labels := by
      have ha : raw24779step1 = (fun i j => raw24779step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24779step1 raw24779step0; decide +kernel
      have hl : raw24779step1Labels = raw24779step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24779step0 raw24779step0Labels permutation34 permutation3
    mixedMoment B raw24779step1 raw24779step1Labels = mixedMoment B raw24779step2 raw24779step2Labels := by
      have ha : raw24779step2 = raw24779step1 := by apply Matrix.ext; unfold raw24779step2 raw24779step1; decide +kernel
      have hl : raw24779step1Labels = labelEmbedding6 ∘ raw24779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24779step1 raw24779step1Labels raw24779step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4514 node4514Labels := by rfl

theorem canonical24780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24780 raw24780Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw24780 raw24780Labels = mixedMoment B raw24780step0 raw24780step0Labels := by
      have hz : ∀ j, raw24780 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24780step0 = (fun i j => raw24780 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24780step0 raw24780; decide +kernel
      have hl : raw24780step0Labels = raw24780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24780 raw24780Labels permutation434 hz
    mixedMoment B raw24780step0 raw24780step0Labels = mixedMoment B raw24780step1 raw24780step1Labels := by
      have hz : ∀ j, raw24780step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24780step1 = (fun i j => raw24780step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24780step1 raw24780step0; decide +kernel
      have hl : raw24780step1Labels = raw24780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24780step0 raw24780step0Labels permutation56 hz
    mixedMoment B raw24780step1 raw24780step1Labels = mixedMoment B raw24780step2 raw24780step2Labels := by
      have ha : raw24780step2 = (fun i j => raw24780step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24780step2 raw24780step1; decide +kernel
      have hl : raw24780step2Labels = raw24780step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24780step1 raw24780step1Labels permutation8 permutation3
    mixedMoment B raw24780step2 raw24780step2Labels = mixedMoment B raw24780step3 raw24780step3Labels := by
      have ha : raw24780step3 = raw24780step2 := by apply Matrix.ext; unfold raw24780step3 raw24780step2; decide +kernel
      have hl : raw24780step2Labels = labelEmbedding6 ∘ raw24780step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24780step2 raw24780step2Labels raw24780step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical24781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24781 raw24781Labels = mixedMoment B node4583 node4583Labels := by
  calc
    mixedMoment B raw24781 raw24781Labels = mixedMoment B raw24781step0 raw24781step0Labels := by
      have hz : ∀ j, raw24781 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24781step0 = (fun i j => raw24781 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24781step0 raw24781; decide +kernel
      have hl : raw24781step0Labels = raw24781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24781 raw24781Labels permutation265 hz
    mixedMoment B raw24781step0 raw24781step0Labels = mixedMoment B raw24781step1 raw24781step1Labels := by
      have ha : raw24781step1 = (fun i j => raw24781step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24781step1 raw24781step0; decide +kernel
      have hl : raw24781step1Labels = raw24781step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24781step0 raw24781step0Labels permutation34 permutation3
    mixedMoment B raw24781step1 raw24781step1Labels = mixedMoment B raw24781step2 raw24781step2Labels := by
      have ha : raw24781step2 = raw24781step1 := by apply Matrix.ext; unfold raw24781step2 raw24781step1; decide +kernel
      have hl : raw24781step1Labels = labelEmbedding6 ∘ raw24781step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24781step1 raw24781step1Labels raw24781step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4583 node4583Labels := by rfl

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

theorem canonical272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw272 raw272Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw272 raw272Labels = mixedMoment B raw272step0 raw272step0Labels := by
      have ha : raw272step0 = (fun i j => raw272 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw272step0 raw272; decide +kernel
      have hl : raw272step0Labels = raw272Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw272 raw272Labels permutation8 permutation5
    mixedMoment B raw272step0 raw272step0Labels = mixedMoment B raw272step1 raw272step1Labels := by
      have ha : raw272step1 = raw272step0 := by apply Matrix.ext; unfold raw272step1 raw272step0; decide +kernel
      have hl : raw272step0Labels = labelEmbedding1 ∘ raw272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw272step0 raw272step0Labels raw272step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2768 node2768Labels := by rfl

theorem canonical273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw273 raw273Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw273 raw273Labels = mixedMoment B raw273step0 raw273step0Labels := by
      have ha : raw273step0 = (fun i j => raw273 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw273step0 raw273; decide +kernel
      have hl : raw273step0Labels = raw273Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw273 raw273Labels permutation8 permutation5
    _ = mixedMoment B node405 node405Labels := by rfl

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

theorem canonical756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw756 raw756Labels = mixedMoment B node4139 node4139Labels := by
  calc
    mixedMoment B raw756 raw756Labels = mixedMoment B raw756step0 raw756step0Labels := by
      have ha : raw756step0 = (fun i j => raw756 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw756step0 raw756; decide +kernel
      have hl : raw756step0Labels = raw756Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw756 raw756Labels permutation152 permutation4
    mixedMoment B raw756step0 raw756step0Labels = mixedMoment B raw756step1 raw756step1Labels := by
      have ha : raw756step1 = raw756step0 := by apply Matrix.ext; unfold raw756step1 raw756step0; decide +kernel
      have hl : raw756step0Labels = labelEmbedding7 ∘ raw756step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw756step0 raw756step0Labels raw756step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4139 node4139Labels := by rfl

theorem canonical757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw757 raw757Labels = mixedMoment B node567 node567Labels := by
  calc
    mixedMoment B raw757 raw757Labels = mixedMoment B raw757step0 raw757step0Labels := by
      have ha : raw757step0 = (fun i j => raw757 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw757step0 raw757; decide +kernel
      have hl : raw757step0Labels = raw757Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw757 raw757Labels permutation152 permutation4
    _ = mixedMoment B node567 node567Labels := by rfl

theorem canonical758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw758 raw758Labels = mixedMoment B node1488 node1488Labels := by
  calc
    mixedMoment B raw758 raw758Labels = mixedMoment B raw758step0 raw758step0Labels := by
      have ha : raw758step0 = (fun i j => raw758 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw758step0 raw758; decide +kernel
      have hl : raw758step0Labels = raw758Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw758 raw758Labels permutation152 permutation6
    mixedMoment B raw758step0 raw758step0Labels = mixedMoment B raw758step1 raw758step1Labels := by
      have ha : raw758step1 = -raw758step0 := by apply Matrix.ext; change ∀ i j, raw758step1 i j = -(raw758step0 i j); unfold raw758step1 raw758step0; decide +kernel
      have hl : raw758step1Labels = raw758step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw758step1 raw758step1Labels = mixedMoment B raw758step2 raw758step2Labels := by
      have ha : raw758step2 = raw758step1 := by apply Matrix.ext; unfold raw758step2 raw758step1; decide +kernel
      have hl : raw758step1Labels = labelEmbedding1 ∘ raw758step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw758step1 raw758step1Labels raw758step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1488 node1488Labels := by rfl

theorem canonical759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw759 raw759Labels = mixedMoment B node4140 node4140Labels := by
  calc
    mixedMoment B raw759 raw759Labels = mixedMoment B raw759step0 raw759step0Labels := by
      have ha : raw759step0 = (fun i j => raw759 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw759step0 raw759; decide +kernel
      have hl : raw759step0Labels = raw759Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw759 raw759Labels permutation32 permutation4
    mixedMoment B raw759step0 raw759step0Labels = mixedMoment B raw759step1 raw759step1Labels := by
      have ha : raw759step1 = raw759step0 := by apply Matrix.ext; unfold raw759step1 raw759step0; decide +kernel
      have hl : raw759step0Labels = labelEmbedding7 ∘ raw759step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw759step0 raw759step0Labels raw759step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4140 node4140Labels := by rfl

theorem canonical760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw760 raw760Labels = mixedMoment B node568 node568Labels := by
  calc
    mixedMoment B raw760 raw760Labels = mixedMoment B raw760step0 raw760step0Labels := by
      have ha : raw760step0 = (fun i j => raw760 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw760step0 raw760; decide +kernel
      have hl : raw760step0Labels = raw760Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw760 raw760Labels permutation32 permutation4
    _ = mixedMoment B node568 node568Labels := by rfl

theorem canonical761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw761 raw761Labels = mixedMoment B node1489 node1489Labels := by
  calc
    mixedMoment B raw761 raw761Labels = mixedMoment B raw761step0 raw761step0Labels := by
      have ha : raw761step0 = (fun i j => raw761 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw761step0 raw761; decide +kernel
      have hl : raw761step0Labels = raw761Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw761 raw761Labels permutation32 permutation6
    mixedMoment B raw761step0 raw761step0Labels = mixedMoment B raw761step1 raw761step1Labels := by
      have ha : raw761step1 = -raw761step0 := by apply Matrix.ext; change ∀ i j, raw761step1 i j = -(raw761step0 i j); unfold raw761step1 raw761step0; decide +kernel
      have hl : raw761step1Labels = raw761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw761step1 raw761step1Labels = mixedMoment B raw761step2 raw761step2Labels := by
      have ha : raw761step2 = raw761step1 := by apply Matrix.ext; unfold raw761step2 raw761step1; decide +kernel
      have hl : raw761step1Labels = labelEmbedding1 ∘ raw761step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw761step1 raw761step1Labels raw761step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1489 node1489Labels := by rfl

theorem canonical762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw762 raw762Labels = mixedMoment B node4141 node4141Labels := by
  calc
    mixedMoment B raw762 raw762Labels = mixedMoment B raw762step0 raw762step0Labels := by
      have ha : raw762step0 = (fun i j => raw762 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw762step0 raw762; decide +kernel
      have hl : raw762step0Labels = raw762Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw762 raw762Labels permutation32 permutation4
    mixedMoment B raw762step0 raw762step0Labels = mixedMoment B raw762step1 raw762step1Labels := by
      have ha : raw762step1 = raw762step0 := by apply Matrix.ext; unfold raw762step1 raw762step0; decide +kernel
      have hl : raw762step0Labels = labelEmbedding7 ∘ raw762step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw762step0 raw762step0Labels raw762step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4141 node4141Labels := by rfl

theorem canonical763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw763 raw763Labels = mixedMoment B node569 node569Labels := by
  calc
    mixedMoment B raw763 raw763Labels = mixedMoment B raw763step0 raw763step0Labels := by
      have ha : raw763step0 = (fun i j => raw763 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw763step0 raw763; decide +kernel
      have hl : raw763step0Labels = raw763Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw763 raw763Labels permutation32 permutation4
    _ = mixedMoment B node569 node569Labels := by rfl

theorem canonical764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw764 raw764Labels = mixedMoment B node1490 node1490Labels := by
  calc
    mixedMoment B raw764 raw764Labels = mixedMoment B raw764step0 raw764step0Labels := by
      have ha : raw764step0 = (fun i j => raw764 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw764step0 raw764; decide +kernel
      have hl : raw764step0Labels = raw764Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw764 raw764Labels permutation32 permutation6
    mixedMoment B raw764step0 raw764step0Labels = mixedMoment B raw764step1 raw764step1Labels := by
      have ha : raw764step1 = -raw764step0 := by apply Matrix.ext; change ∀ i j, raw764step1 i j = -(raw764step0 i j); unfold raw764step1 raw764step0; decide +kernel
      have hl : raw764step1Labels = raw764step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw764step1 raw764step1Labels = mixedMoment B raw764step2 raw764step2Labels := by
      have ha : raw764step2 = raw764step1 := by apply Matrix.ext; unfold raw764step2 raw764step1; decide +kernel
      have hl : raw764step1Labels = labelEmbedding1 ∘ raw764step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw764step1 raw764step1Labels raw764step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1490 node1490Labels := by rfl

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

theorem canonical774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw774 raw774Labels = mixedMoment B node4145 node4145Labels := by
  calc
    mixedMoment B raw774 raw774Labels = mixedMoment B raw774step0 raw774step0Labels := by
      have ha : raw774step0 = (fun i j => raw774 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw774step0 raw774; decide +kernel
      have hl : raw774step0Labels = raw774Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw774 raw774Labels permutation32 permutation4
    mixedMoment B raw774step0 raw774step0Labels = mixedMoment B raw774step1 raw774step1Labels := by
      have ha : raw774step1 = raw774step0 := by apply Matrix.ext; unfold raw774step1 raw774step0; decide +kernel
      have hl : raw774step0Labels = labelEmbedding7 ∘ raw774step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw774step0 raw774step0Labels raw774step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4145 node4145Labels := by rfl

theorem canonical775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw775 raw775Labels = mixedMoment B node573 node573Labels := by
  calc
    mixedMoment B raw775 raw775Labels = mixedMoment B raw775step0 raw775step0Labels := by
      have ha : raw775step0 = (fun i j => raw775 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw775step0 raw775; decide +kernel
      have hl : raw775step0Labels = raw775Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw775 raw775Labels permutation32 permutation4
    _ = mixedMoment B node573 node573Labels := by rfl

theorem canonical776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw776 raw776Labels = mixedMoment B node1493 node1493Labels := by
  calc
    mixedMoment B raw776 raw776Labels = mixedMoment B raw776step0 raw776step0Labels := by
      have ha : raw776step0 = (fun i j => raw776 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw776step0 raw776; decide +kernel
      have hl : raw776step0Labels = raw776Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw776 raw776Labels permutation32 permutation6
    mixedMoment B raw776step0 raw776step0Labels = mixedMoment B raw776step1 raw776step1Labels := by
      have ha : raw776step1 = -raw776step0 := by apply Matrix.ext; change ∀ i j, raw776step1 i j = -(raw776step0 i j); unfold raw776step1 raw776step0; decide +kernel
      have hl : raw776step1Labels = raw776step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw776step1 raw776step1Labels = mixedMoment B raw776step2 raw776step2Labels := by
      have ha : raw776step2 = raw776step1 := by apply Matrix.ext; unfold raw776step2 raw776step1; decide +kernel
      have hl : raw776step1Labels = labelEmbedding1 ∘ raw776step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw776step1 raw776step1Labels raw776step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1493 node1493Labels := by rfl

theorem canonical804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw804 raw804Labels = mixedMoment B node4172 node4172Labels := by
  calc
    mixedMoment B raw804 raw804Labels = mixedMoment B raw804step0 raw804step0Labels := by
      have ha : raw804step0 = (fun i j => raw804 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw804step0 raw804; decide +kernel
      have hl : raw804step0Labels = raw804Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw804 raw804Labels permutation32 permutation4
    mixedMoment B raw804step0 raw804step0Labels = mixedMoment B raw804step1 raw804step1Labels := by
      have ha : raw804step1 = raw804step0 := by apply Matrix.ext; unfold raw804step1 raw804step0; decide +kernel
      have hl : raw804step0Labels = labelEmbedding7 ∘ raw804step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw804step0 raw804step0Labels raw804step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4172 node4172Labels := by rfl

theorem canonical805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw805 raw805Labels = mixedMoment B node600 node600Labels := by
  calc
    mixedMoment B raw805 raw805Labels = mixedMoment B raw805step0 raw805step0Labels := by
      have ha : raw805step0 = (fun i j => raw805 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw805step0 raw805; decide +kernel
      have hl : raw805step0Labels = raw805Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw805 raw805Labels permutation32 permutation4
    _ = mixedMoment B node600 node600Labels := by rfl

theorem canonical806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw806 raw806Labels = mixedMoment B node1507 node1507Labels := by
  calc
    mixedMoment B raw806 raw806Labels = mixedMoment B raw806step0 raw806step0Labels := by
      have ha : raw806step0 = (fun i j => raw806 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw806step0 raw806; decide +kernel
      have hl : raw806step0Labels = raw806Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw806 raw806Labels permutation32 permutation6
    mixedMoment B raw806step0 raw806step0Labels = mixedMoment B raw806step1 raw806step1Labels := by
      have ha : raw806step1 = -raw806step0 := by apply Matrix.ext; change ∀ i j, raw806step1 i j = -(raw806step0 i j); unfold raw806step1 raw806step0; decide +kernel
      have hl : raw806step1Labels = raw806step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw806step1 raw806step1Labels = mixedMoment B raw806step2 raw806step2Labels := by
      have ha : raw806step2 = raw806step1 := by apply Matrix.ext; unfold raw806step2 raw806step1; decide +kernel
      have hl : raw806step1Labels = labelEmbedding1 ∘ raw806step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw806step1 raw806step1Labels raw806step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1507 node1507Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7671 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7671 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7671 = injectiveMoment H raw7671step0 := by
      have hz : ∀ j, raw7671 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7671step0 = (fun i j => raw7671 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7671 permutation21 hz
    injectiveMoment H raw7671step0 = injectiveMoment H raw7671step1 := by
      have heq : raw7671step1 = (fun i j => raw7671step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7671step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

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

theorem canonical782 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw782 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw782 = injectiveMoment H raw782step0 := by
      have heq : raw782step0 = -raw782 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw782).symm
    injectiveMoment H raw782step0 = injectiveMoment H raw782step1 := by
      have heq : raw782step1 = (fun i j => raw782step0 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw782step0 permutation13 permutation8
    _ = injectiveMoment H node185 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw895 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw895 = injectiveMoment H raw895step0 := by
      have hz : ∀ j, raw895 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw895step0 = (fun i j => raw895 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw895 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

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

theorem canonical174 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw174 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw174 = injectiveMoment H raw174step0 := by
      have heq : raw174step0 = -raw174 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw174).symm
    injectiveMoment H raw174step0 = injectiveMoment H raw174step1 := by
      have heq : raw174step1 = (fun i j => raw174step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw174step0 permutation9 permutation8
    _ = injectiveMoment H node145 := by rfl

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

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

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

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1420 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1420 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1420 = injectiveMoment H raw1420step0 := by
      have heq : raw1420step0 = raw1420.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1420).symm
    injectiveMoment H raw1420step0 = injectiveMoment H raw1420step1 := by
      have heq : raw1420step1 = (fun i j => raw1420step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1420step0 permutation7 permutation6
    _ = injectiveMoment H node52 := by rfl

theorem canonical1435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1435 = injectiveMoment H node31 := by
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

theorem canonical2863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2863 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2863 = injectiveMoment H raw2863step0 := by
      have heq : raw2863step0 = (fun i j => raw2863 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2863 permutation4 permutation5
    _ = injectiveMoment H node56 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5979 = injectiveMoment H node57 := by
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

theorem sound145 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node145 = Sparse.eval value145 (momentVector H) := by
  have heq : pivotMatrix145 = (fun u v => node145 (pivotPermutation145 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node145 = injectiveMoment H pivotMatrix145 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix145 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix145 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix145 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (0 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix145 (1 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (1 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix145 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (2 : Fin 3) = raw1420 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1420 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node145 + (injectiveMoment H (mergeFirst pivotMatrix145 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix145 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix145 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value145, value31, value52, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound185 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node185 = Sparse.eval value185 (momentVector H) := by
  have heq : pivotMatrix185 = (fun u v => node185 (pivotPermutation185 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node185 = injectiveMoment H pivotMatrix185 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix185 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix185 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (0 : Fin 3) = raw5979 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (1 : Fin 3) = raw2863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2863 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node185 + (injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value185, value36, value56, value57, Sparse.eval] at hc ⊢
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

theorem singlePair405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node405 node405Labels = Sparse.eval singlePairValue405 (familyPairVector B) := by
  have hp := single_label_three B hB node405
  have hl : node405Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node405 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 1) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node405 PairSemantics.raw5204; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 2) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node405 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node405 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value185 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 4) = PairSemantics.raw782 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node405 PairSemantics.raw782; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical782 hH).trans (PairSemantics.sound185 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue405, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value185, Sparse.eval] at hp ⊢
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

theorem singlePair156 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node156 node156Labels = Sparse.eval singlePairValue156 (familyPairVector B) := by
  have hp := single_label_three B hB node156
  have hl : node156Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node156 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node156 PairSemantics.raw5169
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 2) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node156 PairSemantics.raw5204
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 3) = PairSemantics.raw208 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node156 PairSemantics.raw208
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical208 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value145 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 4) = PairSemantics.raw174 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node156 PairSemantics.raw174
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical174 hH).trans (PairSemantics.sound145 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue156, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value16, PairSemantics.value145, Sparse.eval] at hp ⊢
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

theorem singleton1300 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1300 node1300Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node156 node156Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw76 singletonSmall1300
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1300) = raw76Labels := by decide +kernel
  rw [hl, canonical76 B hB] at h
  have hc0 : mixedMoment B raw76 (Fin.cases (0 : Fin 1) singletonSmall1300) =
      mixedMoment B node156 node156Labels := by
    have ha : raw76 = raw77 := by apply Matrix.ext; unfold raw76 raw77; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1300 = raw77Labels := by decide +kernel
    rw [ha, hj, canonical77 B hB]
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

theorem singleton2768 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2768 node2768Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node405 node405Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw272 singletonSmall2768
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2768) = raw272Labels := by decide +kernel
  rw [hl, canonical272 B hB] at h
  have hc0 : mixedMoment B raw272 (Fin.cases (0 : Fin 1) singletonSmall2768) =
      mixedMoment B node405 node405Labels := by
    have ha : raw272 = raw273 := by apply Matrix.ext; unfold raw272 raw273; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2768 = raw273Labels := by decide +kernel
    rw [ha, hj, canonical273 B hB]
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

theorem singleton4139 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4139 node4139Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node567 node567Labels + mixedMoment B node1488 node1488Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw756 singletonSmall4139
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4139) = raw756Labels := by decide +kernel
  rw [hl, canonical756 B hB] at h
  have hc0 : mixedMoment B raw756 (Fin.cases (0 : Fin 2) singletonSmall4139) =
      mixedMoment B node567 node567Labels := by
    have ha : raw756 = raw757 := by apply Matrix.ext; unfold raw756 raw757; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4139 = raw757Labels := by decide +kernel
    rw [ha, hj, canonical757 B hB]
  have hc1 : mixedMoment B raw756 (Fin.cases (1 : Fin 2) singletonSmall4139) =
      mixedMoment B node1488 node1488Labels := by
    have ha : raw756 = raw758 := by apply Matrix.ext; unfold raw756 raw758; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4139 = raw758Labels := by decide +kernel
    rw [ha, hj, canonical758 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4140 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4140 node4140Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node568 node568Labels + mixedMoment B node1489 node1489Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw759 singletonSmall4140
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4140) = raw759Labels := by decide +kernel
  rw [hl, canonical759 B hB] at h
  have hc0 : mixedMoment B raw759 (Fin.cases (0 : Fin 2) singletonSmall4140) =
      mixedMoment B node568 node568Labels := by
    have ha : raw759 = raw760 := by apply Matrix.ext; unfold raw759 raw760; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4140 = raw760Labels := by decide +kernel
    rw [ha, hj, canonical760 B hB]
  have hc1 : mixedMoment B raw759 (Fin.cases (1 : Fin 2) singletonSmall4140) =
      mixedMoment B node1489 node1489Labels := by
    have ha : raw759 = raw761 := by apply Matrix.ext; unfold raw759 raw761; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4140 = raw761Labels := by decide +kernel
    rw [ha, hj, canonical761 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4141 node4141Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node569 node569Labels + mixedMoment B node1490 node1490Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw762 singletonSmall4141
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4141) = raw762Labels := by decide +kernel
  rw [hl, canonical762 B hB] at h
  have hc0 : mixedMoment B raw762 (Fin.cases (0 : Fin 2) singletonSmall4141) =
      mixedMoment B node569 node569Labels := by
    have ha : raw762 = raw763 := by apply Matrix.ext; unfold raw762 raw763; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4141 = raw763Labels := by decide +kernel
    rw [ha, hj, canonical763 B hB]
  have hc1 : mixedMoment B raw762 (Fin.cases (1 : Fin 2) singletonSmall4141) =
      mixedMoment B node1490 node1490Labels := by
    have ha : raw762 = raw764 := by apply Matrix.ext; unfold raw762 raw764; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4141 = raw764Labels := by decide +kernel
    rw [ha, hj, canonical764 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4145 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4145 node4145Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node573 node573Labels + mixedMoment B node1493 node1493Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw774 singletonSmall4145
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4145) = raw774Labels := by decide +kernel
  rw [hl, canonical774 B hB] at h
  have hc0 : mixedMoment B raw774 (Fin.cases (0 : Fin 2) singletonSmall4145) =
      mixedMoment B node573 node573Labels := by
    have ha : raw774 = raw775 := by apply Matrix.ext; unfold raw774 raw775; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4145 = raw775Labels := by decide +kernel
    rw [ha, hj, canonical775 B hB]
  have hc1 : mixedMoment B raw774 (Fin.cases (1 : Fin 2) singletonSmall4145) =
      mixedMoment B node1493 node1493Labels := by
    have ha : raw774 = raw776 := by apply Matrix.ext; unfold raw774 raw776; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4145 = raw776Labels := by decide +kernel
    rw [ha, hj, canonical776 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
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

theorem singleton4172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4172 node4172Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node600 node600Labels + mixedMoment B node1507 node1507Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw804 singletonSmall4172
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4172) = raw804Labels := by decide +kernel
  rw [hl, canonical804 B hB] at h
  have hc0 : mixedMoment B raw804 (Fin.cases (0 : Fin 2) singletonSmall4172) =
      mixedMoment B node600 node600Labels := by
    have ha : raw804 = raw805 := by apply Matrix.ext; unfold raw804 raw805; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4172 = raw805Labels := by decide +kernel
    rw [ha, hj, canonical805 B hB]
  have hc1 : mixedMoment B raw804 (Fin.cases (1 : Fin 2) singletonSmall4172) =
      mixedMoment B node1507 node1507Labels := by
    have ha : raw804 = raw806 := by apply Matrix.ext; unfold raw804 raw806; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4172 = raw806Labels := by decide +kernel
    rw [ha, hj, canonical806 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4513 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4513 node4513Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1097 node1097Labels + mixedMoment B node3232 node3232Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1311 singletonSmall4513
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4513) = raw1311Labels := by decide +kernel
  rw [hl, canonical1311 B hB] at h
  have hc0 : mixedMoment B raw1311 (Fin.cases (0 : Fin 2) singletonSmall4513) =
      mixedMoment B node1097 node1097Labels := by
    have ha : raw1311 = raw1312 := by apply Matrix.ext; unfold raw1311 raw1312; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4513 = raw1312Labels := by decide +kernel
    rw [ha, hj, canonical1312 B hB]
  have hc1 : mixedMoment B raw1311 (Fin.cases (1 : Fin 2) singletonSmall4513) =
      mixedMoment B node3232 node3232Labels := by
    have ha : raw1311 = raw1313 := by apply Matrix.ext; unfold raw1311 raw1313; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4513 = raw1313Labels := by decide +kernel
    rw [ha, hj, canonical1313 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4514 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4514 node4514Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1098 node1098Labels + mixedMoment B node1894 node1894Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1314 singletonSmall4514
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4514) = raw1314Labels := by decide +kernel
  rw [hl, canonical1314 B hB] at h
  have hc0 : mixedMoment B raw1314 (Fin.cases (0 : Fin 2) singletonSmall4514) =
      mixedMoment B node1098 node1098Labels := by
    have ha : raw1314 = raw1315 := by apply Matrix.ext; unfold raw1314 raw1315; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4514 = raw1315Labels := by decide +kernel
    rw [ha, hj, canonical1315 B hB]
  have hc1 : mixedMoment B raw1314 (Fin.cases (1 : Fin 2) singletonSmall4514) =
      mixedMoment B node1894 node1894Labels := by
    have ha : raw1314 = raw1316 := by apply Matrix.ext; unfold raw1314 raw1316; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4514 = raw1316Labels := by decide +kernel
    rw [ha, hj, canonical1316 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4515 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4515 node4515Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1099 node1099Labels + mixedMoment B node3233 node3233Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1317 singletonSmall4515
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4515) = raw1317Labels := by decide +kernel
  rw [hl, canonical1317 B hB] at h
  have hc0 : mixedMoment B raw1317 (Fin.cases (0 : Fin 2) singletonSmall4515) =
      mixedMoment B node1099 node1099Labels := by
    have ha : raw1317 = raw1318 := by apply Matrix.ext; unfold raw1317 raw1318; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4515 = raw1318Labels := by decide +kernel
    rw [ha, hj, canonical1318 B hB]
  have hc1 : mixedMoment B raw1317 (Fin.cases (1 : Fin 2) singletonSmall4515) =
      mixedMoment B node3233 node3233Labels := by
    have ha : raw1317 = raw1319 := by apply Matrix.ext; unfold raw1317 raw1319; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4515 = raw1319Labels := by decide +kernel
    rw [ha, hj, canonical1319 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4518 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4518 node4518Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1102 node1102Labels + mixedMoment B node3236 node3236Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1326 singletonSmall4518
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4518) = raw1326Labels := by decide +kernel
  rw [hl, canonical1326 B hB] at h
  have hc0 : mixedMoment B raw1326 (Fin.cases (0 : Fin 2) singletonSmall4518) =
      mixedMoment B node1102 node1102Labels := by
    have ha : raw1326 = raw1327 := by apply Matrix.ext; unfold raw1326 raw1327; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4518 = raw1327Labels := by decide +kernel
    rw [ha, hj, canonical1327 B hB]
  have hc1 : mixedMoment B raw1326 (Fin.cases (1 : Fin 2) singletonSmall4518) =
      mixedMoment B node3236 node3236Labels := by
    have ha : raw1326 = raw1328 := by apply Matrix.ext; unfold raw1326 raw1328; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4518 = raw1328Labels := by decide +kernel
    rw [ha, hj, canonical1328 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4521 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4521 node4521Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1105 node1105Labels + mixedMoment B node1887 node1887Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1335 singletonSmall4521
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4521) = raw1335Labels := by decide +kernel
  rw [hl, canonical1335 B hB] at h
  have hc0 : mixedMoment B raw1335 (Fin.cases (0 : Fin 2) singletonSmall4521) =
      mixedMoment B node1105 node1105Labels := by
    have ha : raw1335 = raw1336 := by apply Matrix.ext; unfold raw1335 raw1336; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4521 = raw1336Labels := by decide +kernel
    rw [ha, hj, canonical1336 B hB]
  have hc1 : mixedMoment B raw1335 (Fin.cases (1 : Fin 2) singletonSmall4521) =
      mixedMoment B node1887 node1887Labels := by
    have ha : raw1335 = raw1337 := by apply Matrix.ext; unfold raw1335 raw1337; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4521 = raw1337Labels := by decide +kernel
    rw [ha, hj, canonical1337 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4522 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4522 node4522Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1106 node1106Labels + mixedMoment B node3249 node3249Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1338 singletonSmall4522
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4522) = raw1338Labels := by decide +kernel
  rw [hl, canonical1338 B hB] at h
  have hc0 : mixedMoment B raw1338 (Fin.cases (0 : Fin 2) singletonSmall4522) =
      mixedMoment B node1106 node1106Labels := by
    have ha : raw1338 = raw1339 := by apply Matrix.ext; unfold raw1338 raw1339; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4522 = raw1339Labels := by decide +kernel
    rw [ha, hj, canonical1339 B hB]
  have hc1 : mixedMoment B raw1338 (Fin.cases (1 : Fin 2) singletonSmall4522) =
      mixedMoment B node3249 node3249Labels := by
    have ha : raw1338 = raw1340 := by apply Matrix.ext; unfold raw1338 raw1340; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4522 = raw1340Labels := by decide +kernel
    rw [ha, hj, canonical1340 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4524 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4524 node4524Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1108 node1108Labels + mixedMoment B node3251 node3251Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1344 singletonSmall4524
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4524) = raw1344Labels := by decide +kernel
  rw [hl, canonical1344 B hB] at h
  have hc0 : mixedMoment B raw1344 (Fin.cases (0 : Fin 2) singletonSmall4524) =
      mixedMoment B node1108 node1108Labels := by
    have ha : raw1344 = raw1345 := by apply Matrix.ext; unfold raw1344 raw1345; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4524 = raw1345Labels := by decide +kernel
    rw [ha, hj, canonical1345 B hB]
  have hc1 : mixedMoment B raw1344 (Fin.cases (1 : Fin 2) singletonSmall4524) =
      mixedMoment B node3251 node3251Labels := by
    have ha : raw1344 = raw1346 := by apply Matrix.ext; unfold raw1344 raw1346; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4524 = raw1346Labels := by decide +kernel
    rw [ha, hj, canonical1346 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4541 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4541 node4541Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1126 node1126Labels + mixedMoment B node3256 node3256Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1362 singletonSmall4541
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4541) = raw1362Labels := by decide +kernel
  rw [hl, canonical1362 B hB] at h
  have hc0 : mixedMoment B raw1362 (Fin.cases (0 : Fin 2) singletonSmall4541) =
      mixedMoment B node1126 node1126Labels := by
    have ha : raw1362 = raw1363 := by apply Matrix.ext; unfold raw1362 raw1363; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4541 = raw1363Labels := by decide +kernel
    rw [ha, hj, canonical1363 B hB]
  have hc1 : mixedMoment B raw1362 (Fin.cases (1 : Fin 2) singletonSmall4541) =
      mixedMoment B node3256 node3256Labels := by
    have ha : raw1362 = raw1364 := by apply Matrix.ext; unfold raw1362 raw1364; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4541 = raw1364Labels := by decide +kernel
    rw [ha, hj, canonical1364 B hB]
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

theorem singleton4581 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4581 node4581Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1200 node1200Labels + mixedMoment B node3281 node3281Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1413 singletonSmall4581
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4581) = raw1413Labels := by decide +kernel
  rw [hl, canonical1413 B hB] at h
  have hc0 : mixedMoment B raw1413 (Fin.cases (0 : Fin 2) singletonSmall4581) =
      mixedMoment B node1200 node1200Labels := by
    have ha : raw1413 = raw1414 := by apply Matrix.ext; unfold raw1413 raw1414; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4581 = raw1414Labels := by decide +kernel
    rw [ha, hj, canonical1414 B hB]
  have hc1 : mixedMoment B raw1413 (Fin.cases (1 : Fin 2) singletonSmall4581) =
      mixedMoment B node3281 node3281Labels := by
    have ha : raw1413 = raw1415 := by apply Matrix.ext; unfold raw1413 raw1415; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4581 = raw1415Labels := by decide +kernel
    rw [ha, hj, canonical1415 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4583 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4583 node4583Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1202 node1202Labels + mixedMoment B node1942 node1942Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1416 singletonSmall4583
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4583) = raw1416Labels := by decide +kernel
  rw [hl, canonical1416 B hB] at h
  have hc0 : mixedMoment B raw1416 (Fin.cases (0 : Fin 2) singletonSmall4583) =
      mixedMoment B node1202 node1202Labels := by
    have ha : raw1416 = raw1417 := by apply Matrix.ext; unfold raw1416 raw1417; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4583 = raw1417Labels := by decide +kernel
    rw [ha, hj, canonical1417 B hB]
  have hc1 : mixedMoment B raw1416 (Fin.cases (1 : Fin 2) singletonSmall4583) =
      mixedMoment B node1942 node1942Labels := by
    have ha : raw1416 = raw1418 := by apply Matrix.ext; unfold raw1416 raw1418; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4583 = raw1418Labels := by decide +kernel
    rw [ha, hj, canonical1418 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4586 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4586 node4586Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1205 node1205Labels + mixedMoment B node3284 node3284Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1419 singletonSmall4586
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4586) = raw1419Labels := by decide +kernel
  rw [hl, canonical1419 B hB] at h
  have hc0 : mixedMoment B raw1419 (Fin.cases (0 : Fin 2) singletonSmall4586) =
      mixedMoment B node1205 node1205Labels := by
    have ha : raw1419 = raw1420 := by apply Matrix.ext; unfold raw1419 raw1420; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4586 = raw1420Labels := by decide +kernel
    rw [ha, hj, canonical1420 B hB]
  have hc1 : mixedMoment B raw1419 (Fin.cases (1 : Fin 2) singletonSmall4586) =
      mixedMoment B node3284 node3284Labels := by
    have ha : raw1419 = raw1421 := by apply Matrix.ext; unfold raw1419 raw1421; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4586 = raw1421Labels := by decide +kernel
    rw [ha, hj, canonical1421 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4601 node4601Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1235 node1235Labels + mixedMoment B node3292 node3292Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1422 singletonSmall4601
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4601) = raw1422Labels := by decide +kernel
  rw [hl, canonical1422 B hB] at h
  have hc0 : mixedMoment B raw1422 (Fin.cases (0 : Fin 2) singletonSmall4601) =
      mixedMoment B node1235 node1235Labels := by
    have ha : raw1422 = raw1423 := by apply Matrix.ext; unfold raw1422 raw1423; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4601 = raw1423Labels := by decide +kernel
    rw [ha, hj, canonical1423 B hB]
  have hc1 : mixedMoment B raw1422 (Fin.cases (1 : Fin 2) singletonSmall4601) =
      mixedMoment B node3292 node3292Labels := by
    have ha : raw1422 = raw1424 := by apply Matrix.ext; unfold raw1422 raw1424; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4601 = raw1424Labels := by decide +kernel
    rw [ha, hj, canonical1424 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4605 node4605Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1239 node1239Labels + mixedMoment B node2226 node2226Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1428 singletonSmall4605
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4605) = raw1428Labels := by decide +kernel
  rw [hl, canonical1428 B hB] at h
  have hc0 : mixedMoment B raw1428 (Fin.cases (0 : Fin 2) singletonSmall4605) =
      mixedMoment B node1239 node1239Labels := by
    have ha : raw1428 = raw1429 := by apply Matrix.ext; unfold raw1428 raw1429; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4605 = raw1429Labels := by decide +kernel
    rw [ha, hj, canonical1429 B hB]
  have hc1 : mixedMoment B raw1428 (Fin.cases (1 : Fin 2) singletonSmall4605) =
      mixedMoment B node2226 node2226Labels := by
    have ha : raw1428 = raw1430 := by apply Matrix.ext; unfold raw1428 raw1430; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4605 = raw1430Labels := by decide +kernel
    rw [ha, hj, canonical1430 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4606 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4606 node4606Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1240 node1240Labels + mixedMoment B node3299 node3299Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1431 singletonSmall4606
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4606) = raw1431Labels := by decide +kernel
  rw [hl, canonical1431 B hB] at h
  have hc0 : mixedMoment B raw1431 (Fin.cases (0 : Fin 2) singletonSmall4606) =
      mixedMoment B node1240 node1240Labels := by
    have ha : raw1431 = raw1432 := by apply Matrix.ext; unfold raw1431 raw1432; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4606 = raw1432Labels := by decide +kernel
    rw [ha, hj, canonical1432 B hB]
  have hc1 : mixedMoment B raw1431 (Fin.cases (1 : Fin 2) singletonSmall4606) =
      mixedMoment B node3299 node3299Labels := by
    have ha : raw1431 = raw1433 := by apply Matrix.ext; unfold raw1431 raw1433; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4606 = raw1433Labels := by decide +kernel
    rw [ha, hj, canonical1433 B hB]
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

theorem singleton4622 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4622 node4622Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1299 node1299Labels + mixedMoment B node3307 node3307Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1449 singletonSmall4622
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4622) = raw1449Labels := by decide +kernel
  rw [hl, canonical1449 B hB] at h
  have hc0 : mixedMoment B raw1449 (Fin.cases (0 : Fin 2) singletonSmall4622) =
      mixedMoment B node1299 node1299Labels := by
    have ha : raw1449 = raw1450 := by apply Matrix.ext; unfold raw1449 raw1450; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4622 = raw1450Labels := by decide +kernel
    rw [ha, hj, canonical1450 B hB]
  have hc1 : mixedMoment B raw1449 (Fin.cases (1 : Fin 2) singletonSmall4622) =
      mixedMoment B node3307 node3307Labels := by
    have ha : raw1449 = raw1451 := by apply Matrix.ext; unfold raw1449 raw1451; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4622 = raw1451Labels := by decide +kernel
    rw [ha, hj, canonical1451 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4623 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4623 node4623Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1300 node1300Labels + mixedMoment B node3308 node3308Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1452 singletonSmall4623
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4623) = raw1452Labels := by decide +kernel
  rw [hl, canonical1452 B hB] at h
  have hc0 : mixedMoment B raw1452 (Fin.cases (0 : Fin 2) singletonSmall4623) =
      mixedMoment B node1300 node1300Labels := by
    have ha : raw1452 = raw1453 := by apply Matrix.ext; unfold raw1452 raw1453; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4623 = raw1453Labels := by decide +kernel
    rw [ha, hj, canonical1453 B hB]
  have hc1 : mixedMoment B raw1452 (Fin.cases (1 : Fin 2) singletonSmall4623) =
      mixedMoment B node3308 node3308Labels := by
    have ha : raw1452 = raw1454 := by apply Matrix.ext; unfold raw1452 raw1454; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4623 = raw1454Labels := by decide +kernel
    rw [ha, hj, canonical1454 B hB]
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

theorem singleton5149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5149 node5149Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2924 node2924Labels + mixedMoment B node3605 node3605Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2175 singletonSmall5149
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5149) = raw2175Labels := by decide +kernel
  rw [hl, canonical2175 B hB] at h
  have hc0 : mixedMoment B raw2175 (Fin.cases (0 : Fin 2) singletonSmall5149) =
      mixedMoment B node2924 node2924Labels := by
    have ha : raw2175 = raw2176 := by apply Matrix.ext; unfold raw2175 raw2176; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5149 = raw2176Labels := by decide +kernel
    rw [ha, hj, canonical2176 B hB]
  have hc1 : mixedMoment B raw2175 (Fin.cases (1 : Fin 2) singletonSmall5149) =
      mixedMoment B node3605 node3605Labels := by
    have ha : raw2175 = raw2177 := by apply Matrix.ext; unfold raw2175 raw2177; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5149 = raw2177Labels := by decide +kernel
    rw [ha, hj, canonical2177 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5204 node5204Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2881 node2881Labels + mixedMoment B node3624 node3624Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2232 singletonSmall5204
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5204) = raw2232Labels := by decide +kernel
  rw [hl, canonical2232 B hB] at h
  have hc0 : mixedMoment B raw2232 (Fin.cases (0 : Fin 2) singletonSmall5204) =
      mixedMoment B node2881 node2881Labels := by
    have ha : raw2232 = raw2233 := by apply Matrix.ext; unfold raw2232 raw2233; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5204 = raw2233Labels := by decide +kernel
    rw [ha, hj, canonical2233 B hB]
  have hc1 : mixedMoment B raw2232 (Fin.cases (1 : Fin 2) singletonSmall5204) =
      mixedMoment B node3624 node3624Labels := by
    have ha : raw2232 = raw2234 := by apply Matrix.ext; unfold raw2232 raw2234; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5204 = raw2234Labels := by decide +kernel
    rw [ha, hj, canonical2234 B hB]
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

theorem singleton5284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5284 node5284Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3077 node3077Labels + mixedMoment B node3625 node3625Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2289 singletonSmall5284
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5284) = raw2289Labels := by decide +kernel
  rw [hl, canonical2289 B hB] at h
  have hc0 : mixedMoment B raw2289 (Fin.cases (0 : Fin 2) singletonSmall5284) =
      mixedMoment B node3077 node3077Labels := by
    have ha : raw2289 = raw2290 := by apply Matrix.ext; unfold raw2289 raw2290; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5284 = raw2290Labels := by decide +kernel
    rw [ha, hj, canonical2290 B hB]
  have hc1 : mixedMoment B raw2289 (Fin.cases (1 : Fin 2) singletonSmall5284) =
      mixedMoment B node3625 node3625Labels := by
    have ha : raw2289 = raw2291 := by apply Matrix.ext; unfold raw2289 raw2291; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5284 = raw2291Labels := by decide +kernel
    rw [ha, hj, canonical2291 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5294 node5294Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2768 node2768Labels + mixedMoment B node3632 node3632Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2304 singletonSmall5294
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5294) = raw2304Labels := by decide +kernel
  rw [hl, canonical2304 B hB] at h
  have hc0 : mixedMoment B raw2304 (Fin.cases (0 : Fin 2) singletonSmall5294) =
      mixedMoment B node2768 node2768Labels := by
    have ha : raw2304 = raw2305 := by apply Matrix.ext; unfold raw2304 raw2305; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5294 = raw2305Labels := by decide +kernel
    rw [ha, hj, canonical2305 B hB]
  have hc1 : mixedMoment B raw2304 (Fin.cases (1 : Fin 2) singletonSmall5294) =
      mixedMoment B node3632 node3632Labels := by
    have ha : raw2304 = raw2306 := by apply Matrix.ext; unfold raw2304 raw2306; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5294 = raw2306Labels := by decide +kernel
    rw [ha, hj, canonical2306 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound1097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1097 node1097Labels = Sparse.eval nodeValue1097 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1097) = mixedMoment B node1097 node1097Labels := rfl
  simpa [nodeValue1097, Sparse.eval] using hc.symm

theorem sound1098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1098 node1098Labels = Sparse.eval nodeValue1098 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1098) = mixedMoment B node1098 node1098Labels := rfl
  simpa [nodeValue1098, Sparse.eval] using hc.symm

theorem sound1099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1099 node1099Labels = Sparse.eval nodeValue1099 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1099) = mixedMoment B node1099 node1099Labels := rfl
  simpa [nodeValue1099, Sparse.eval] using hc.symm

theorem sound1102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1102 node1102Labels = Sparse.eval nodeValue1102 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1102) = mixedMoment B node1102 node1102Labels := rfl
  simpa [nodeValue1102, Sparse.eval] using hc.symm

theorem sound1105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1105 node1105Labels = Sparse.eval nodeValue1105 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1105) = mixedMoment B node1105 node1105Labels := rfl
  simpa [nodeValue1105, Sparse.eval] using hc.symm

theorem sound1106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1106 node1106Labels = Sparse.eval nodeValue1106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1106) = mixedMoment B node1106 node1106Labels := rfl
  simpa [nodeValue1106, Sparse.eval] using hc.symm

theorem sound1108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1108 node1108Labels = Sparse.eval nodeValue1108 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1108) = mixedMoment B node1108 node1108Labels := rfl
  simpa [nodeValue1108, Sparse.eval] using hc.symm

theorem sound1126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1126 node1126Labels = Sparse.eval nodeValue1126 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1126) = mixedMoment B node1126 node1126Labels := rfl
  simpa [nodeValue1126, Sparse.eval] using hc.symm

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

theorem sound156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node156 node156Labels = Sparse.eval nodeValue156 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue156 (familyPairVector B) := singlePair156 B _hB
    _ = _ := by
      norm_num [singlePairValue156, nodeValue156, Sparse.eval, mixedVector]
      ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1200 node1200Labels = Sparse.eval nodeValue1200 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1200) = mixedMoment B node1200 node1200Labels := rfl
  simpa [nodeValue1200, Sparse.eval] using hc.symm

theorem sound1202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1202 node1202Labels = Sparse.eval nodeValue1202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1202) = mixedMoment B node1202 node1202Labels := rfl
  simpa [nodeValue1202, Sparse.eval] using hc.symm

theorem sound1205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1205 node1205Labels = Sparse.eval nodeValue1205 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1205) = mixedMoment B node1205 node1205Labels := rfl
  simpa [nodeValue1205, Sparse.eval] using hc.symm

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

theorem sound1235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1235 node1235Labels = Sparse.eval nodeValue1235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1235) = mixedMoment B node1235 node1235Labels := rfl
  simpa [nodeValue1235, Sparse.eval] using hc.symm

theorem sound1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1236 node1236Labels = Sparse.eval nodeValue1236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1236) = mixedMoment B node1236 node1236Labels := rfl
  simpa [nodeValue1236, Sparse.eval] using hc.symm

theorem sound1239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1239 node1239Labels = Sparse.eval nodeValue1239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1239) = mixedMoment B node1239 node1239Labels := rfl
  simpa [nodeValue1239, Sparse.eval] using hc.symm

theorem sound1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1240 node1240Labels = Sparse.eval nodeValue1240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1240) = mixedMoment B node1240 node1240Labels := rfl
  simpa [nodeValue1240, Sparse.eval] using hc.symm

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

theorem sound1300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1300 node1300Labels = Sparse.eval nodeValue1300 (mixedVector B) := by
  have h := singleton1300 B _hB
  rw [sound156 B _hB _hF] at h
  norm_num [nodeValue1300, nodeValue156, Sparse.eval] at h ⊢
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

theorem sound1488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1488 node1488Labels = Sparse.eval nodeValue1488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1488) = mixedMoment B node1488 node1488Labels := rfl
  simpa [nodeValue1488, Sparse.eval] using hc.symm

theorem sound1489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1489 node1489Labels = Sparse.eval nodeValue1489 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1489) = mixedMoment B node1489 node1489Labels := rfl
  simpa [nodeValue1489, Sparse.eval] using hc.symm

theorem sound1490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1490 node1490Labels = Sparse.eval nodeValue1490 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1490) = mixedMoment B node1490 node1490Labels := rfl
  simpa [nodeValue1490, Sparse.eval] using hc.symm

theorem sound1493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1493 node1493Labels = Sparse.eval nodeValue1493 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1493) = mixedMoment B node1493 node1493Labels := rfl
  simpa [nodeValue1493, Sparse.eval] using hc.symm

theorem sound1507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1507 node1507Labels = Sparse.eval nodeValue1507 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1507) = mixedMoment B node1507 node1507Labels := rfl
  simpa [nodeValue1507, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1887 node1887Labels = Sparse.eval nodeValue1887 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1887) = mixedMoment B node1887 node1887Labels := rfl
  simpa [nodeValue1887, Sparse.eval] using hc.symm

theorem sound1894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1894 node1894Labels = Sparse.eval nodeValue1894 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1894) = mixedMoment B node1894 node1894Labels := rfl
  simpa [nodeValue1894, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1942 node1942Labels = Sparse.eval nodeValue1942 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1942) = mixedMoment B node1942 node1942Labels := rfl
  simpa [nodeValue1942, Sparse.eval] using hc.symm

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

theorem sound2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2226 node2226Labels = Sparse.eval nodeValue2226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2226) = mixedMoment B node2226 node2226Labels := rfl
  simpa [nodeValue2226, Sparse.eval] using hc.symm

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

theorem sound405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node405 node405Labels = Sparse.eval nodeValue405 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue405 (familyPairVector B) := singlePair405 B _hB
    _ = _ := by
      norm_num [singlePairValue405, nodeValue405, Sparse.eval, mixedVector]
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

theorem sound2768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2768 node2768Labels = Sparse.eval nodeValue2768 (mixedVector B) := by
  have h := singleton2768 B _hB
  rw [sound405 B _hB _hF] at h
  norm_num [nodeValue2768, nodeValue405, Sparse.eval] at h ⊢
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

theorem sound2881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2881 node2881Labels = Sparse.eval nodeValue2881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2881) = mixedMoment B node2881 node2881Labels := rfl
  simpa [nodeValue2881, Sparse.eval] using hc.symm

theorem sound2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2924 node2924Labels = Sparse.eval nodeValue2924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2924) = mixedMoment B node2924 node2924Labels := rfl
  simpa [nodeValue2924, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3232 node3232Labels = Sparse.eval nodeValue3232 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3232) = mixedMoment B node3232 node3232Labels := rfl
  simpa [nodeValue3232, Sparse.eval] using hc.symm

theorem sound3233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3233 node3233Labels = Sparse.eval nodeValue3233 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3233) = mixedMoment B node3233 node3233Labels := rfl
  simpa [nodeValue3233, Sparse.eval] using hc.symm

theorem sound3236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3236 node3236Labels = Sparse.eval nodeValue3236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3236) = mixedMoment B node3236 node3236Labels := rfl
  simpa [nodeValue3236, Sparse.eval] using hc.symm

theorem sound3249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3249 node3249Labels = Sparse.eval nodeValue3249 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3249) = mixedMoment B node3249 node3249Labels := rfl
  simpa [nodeValue3249, Sparse.eval] using hc.symm

theorem sound3251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3251 node3251Labels = Sparse.eval nodeValue3251 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3251) = mixedMoment B node3251 node3251Labels := rfl
  simpa [nodeValue3251, Sparse.eval] using hc.symm

theorem sound3256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3256 node3256Labels = Sparse.eval nodeValue3256 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3256) = mixedMoment B node3256 node3256Labels := rfl
  simpa [nodeValue3256, Sparse.eval] using hc.symm

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

theorem sound3281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3281 node3281Labels = Sparse.eval nodeValue3281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3281) = mixedMoment B node3281 node3281Labels := rfl
  simpa [nodeValue3281, Sparse.eval] using hc.symm

theorem sound3284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3284 node3284Labels = Sparse.eval nodeValue3284 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3284) = mixedMoment B node3284 node3284Labels := rfl
  simpa [nodeValue3284, Sparse.eval] using hc.symm

theorem sound3292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3292 node3292Labels = Sparse.eval nodeValue3292 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3292) = mixedMoment B node3292 node3292Labels := rfl
  simpa [nodeValue3292, Sparse.eval] using hc.symm

theorem sound3293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3293 node3293Labels = Sparse.eval nodeValue3293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3293) = mixedMoment B node3293 node3293Labels := rfl
  simpa [nodeValue3293, Sparse.eval] using hc.symm

theorem sound3299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3299 node3299Labels = Sparse.eval nodeValue3299 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3299) = mixedMoment B node3299 node3299Labels := rfl
  simpa [nodeValue3299, Sparse.eval] using hc.symm

theorem sound3301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3301 node3301Labels = Sparse.eval nodeValue3301 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3301) = mixedMoment B node3301 node3301Labels := rfl
  simpa [nodeValue3301, Sparse.eval] using hc.symm

theorem sound3307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3307 node3307Labels = Sparse.eval nodeValue3307 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3307) = mixedMoment B node3307 node3307Labels := rfl
  simpa [nodeValue3307, Sparse.eval] using hc.symm

theorem sound3308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3308 node3308Labels = Sparse.eval nodeValue3308 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3308) = mixedMoment B node3308 node3308Labels := rfl
  simpa [nodeValue3308, Sparse.eval] using hc.symm

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

theorem sound3605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3605 node3605Labels = Sparse.eval nodeValue3605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3605) = mixedMoment B node3605 node3605Labels := rfl
  simpa [nodeValue3605, Sparse.eval] using hc.symm

theorem sound3624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3624 node3624Labels = Sparse.eval nodeValue3624 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3624) = mixedMoment B node3624 node3624Labels := rfl
  simpa [nodeValue3624, Sparse.eval] using hc.symm

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

theorem sound3632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3632 node3632Labels = Sparse.eval nodeValue3632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3632) = mixedMoment B node3632 node3632Labels := rfl
  simpa [nodeValue3632, Sparse.eval] using hc.symm

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

theorem sound567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node567 node567Labels = Sparse.eval nodeValue567 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 567) = mixedMoment B node567 node567Labels := rfl
  simpa [nodeValue567, Sparse.eval] using hc.symm

theorem sound568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node568 node568Labels = Sparse.eval nodeValue568 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 568) = mixedMoment B node568 node568Labels := rfl
  simpa [nodeValue568, Sparse.eval] using hc.symm

theorem sound569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node569 node569Labels = Sparse.eval nodeValue569 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 569) = mixedMoment B node569 node569Labels := rfl
  simpa [nodeValue569, Sparse.eval] using hc.symm

theorem sound573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node573 node573Labels = Sparse.eval nodeValue573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 573) = mixedMoment B node573 node573Labels := rfl
  simpa [nodeValue573, Sparse.eval] using hc.symm

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

theorem sound600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node600 node600Labels = Sparse.eval nodeValue600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 600) = mixedMoment B node600 node600Labels := rfl
  simpa [nodeValue600, Sparse.eval] using hc.symm

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

theorem sound4139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4139 node4139Labels = Sparse.eval nodeValue4139 (mixedVector B) := by
  have h := singleton4139 B _hB
  rw [sound567 B _hB _hF, sound1488 B _hB _hF] at h
  norm_num [nodeValue4139, nodeValue567, nodeValue1488, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4140 node4140Labels = Sparse.eval nodeValue4140 (mixedVector B) := by
  have h := singleton4140 B _hB
  rw [sound568 B _hB _hF, sound1489 B _hB _hF] at h
  norm_num [nodeValue4140, nodeValue568, nodeValue1489, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4141 node4141Labels = Sparse.eval nodeValue4141 (mixedVector B) := by
  have h := singleton4141 B _hB
  rw [sound569 B _hB _hF, sound1490 B _hB _hF] at h
  norm_num [nodeValue4141, nodeValue569, nodeValue1490, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4145 node4145Labels = Sparse.eval nodeValue4145 (mixedVector B) := by
  have h := singleton4145 B _hB
  rw [sound573 B _hB _hF, sound1493 B _hB _hF] at h
  norm_num [nodeValue4145, nodeValue573, nodeValue1493, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4172 node4172Labels = Sparse.eval nodeValue4172 (mixedVector B) := by
  have h := singleton4172 B _hB
  rw [sound600 B _hB _hF, sound1507 B _hB _hF] at h
  norm_num [nodeValue4172, nodeValue600, nodeValue1507, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4513 node4513Labels = Sparse.eval nodeValue4513 (mixedVector B) := by
  have h := singleton4513 B _hB
  rw [sound1097 B _hB _hF, sound3232 B _hB _hF] at h
  norm_num [nodeValue4513, nodeValue1097, nodeValue3232, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4514 node4514Labels = Sparse.eval nodeValue4514 (mixedVector B) := by
  have h := singleton4514 B _hB
  rw [sound1098 B _hB _hF, sound1894 B _hB _hF] at h
  norm_num [nodeValue4514, nodeValue1098, nodeValue1894, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4515 node4515Labels = Sparse.eval nodeValue4515 (mixedVector B) := by
  have h := singleton4515 B _hB
  rw [sound1099 B _hB _hF, sound3233 B _hB _hF] at h
  norm_num [nodeValue4515, nodeValue1099, nodeValue3233, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4518 node4518Labels = Sparse.eval nodeValue4518 (mixedVector B) := by
  have h := singleton4518 B _hB
  rw [sound1102 B _hB _hF, sound3236 B _hB _hF] at h
  norm_num [nodeValue4518, nodeValue1102, nodeValue3236, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4521 node4521Labels = Sparse.eval nodeValue4521 (mixedVector B) := by
  have h := singleton4521 B _hB
  rw [sound1105 B _hB _hF, sound1887 B _hB _hF] at h
  norm_num [nodeValue4521, nodeValue1105, nodeValue1887, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4522 node4522Labels = Sparse.eval nodeValue4522 (mixedVector B) := by
  have h := singleton4522 B _hB
  rw [sound1106 B _hB _hF, sound3249 B _hB _hF] at h
  norm_num [nodeValue4522, nodeValue1106, nodeValue3249, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4524 node4524Labels = Sparse.eval nodeValue4524 (mixedVector B) := by
  have h := singleton4524 B _hB
  rw [sound1108 B _hB _hF, sound3251 B _hB _hF] at h
  norm_num [nodeValue4524, nodeValue1108, nodeValue3251, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4541 node4541Labels = Sparse.eval nodeValue4541 (mixedVector B) := by
  have h := singleton4541 B _hB
  rw [sound1126 B _hB _hF, sound3256 B _hB _hF] at h
  norm_num [nodeValue4541, nodeValue1126, nodeValue3256, Sparse.eval] at h ⊢
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

theorem sound4581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4581 node4581Labels = Sparse.eval nodeValue4581 (mixedVector B) := by
  have h := singleton4581 B _hB
  rw [sound1200 B _hB _hF, sound3281 B _hB _hF] at h
  norm_num [nodeValue4581, nodeValue1200, nodeValue3281, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4583 node4583Labels = Sparse.eval nodeValue4583 (mixedVector B) := by
  have h := singleton4583 B _hB
  rw [sound1202 B _hB _hF, sound1942 B _hB _hF] at h
  norm_num [nodeValue4583, nodeValue1202, nodeValue1942, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4586 node4586Labels = Sparse.eval nodeValue4586 (mixedVector B) := by
  have h := singleton4586 B _hB
  rw [sound1205 B _hB _hF, sound3284 B _hB _hF] at h
  norm_num [nodeValue4586, nodeValue1205, nodeValue3284, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4601 node4601Labels = Sparse.eval nodeValue4601 (mixedVector B) := by
  have h := singleton4601 B _hB
  rw [sound1235 B _hB _hF, sound3292 B _hB _hF] at h
  norm_num [nodeValue4601, nodeValue1235, nodeValue3292, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4602 node4602Labels = Sparse.eval nodeValue4602 (mixedVector B) := by
  have h := singleton4602 B _hB
  rw [sound1236 B _hB _hF, sound3293 B _hB _hF] at h
  norm_num [nodeValue4602, nodeValue1236, nodeValue3293, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4605 node4605Labels = Sparse.eval nodeValue4605 (mixedVector B) := by
  have h := singleton4605 B _hB
  rw [sound1239 B _hB _hF, sound2226 B _hB _hF] at h
  norm_num [nodeValue4605, nodeValue1239, nodeValue2226, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4606 node4606Labels = Sparse.eval nodeValue4606 (mixedVector B) := by
  have h := singleton4606 B _hB
  rw [sound1240 B _hB _hF, sound3299 B _hB _hF] at h
  norm_num [nodeValue4606, nodeValue1240, nodeValue3299, Sparse.eval] at h ⊢
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

theorem sound4612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4612 node4612Labels = Sparse.eval nodeValue4612 (mixedVector B) := by
  have h := singleton4612 B _hB
  rw [sound1246 B _hB _hF, sound3301 B _hB _hF] at h
  norm_num [nodeValue4612, nodeValue1246, nodeValue3301, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4622 node4622Labels = Sparse.eval nodeValue4622 (mixedVector B) := by
  have h := singleton4622 B _hB
  rw [sound1299_e B _hB _hF, sound3307 B _hB _hF] at h
  norm_num [nodeValue4622, nodeValue1299, nodeValue3307, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4623 node4623Labels = Sparse.eval nodeValue4623 (mixedVector B) := by
  have h := singleton4623 B _hB
  rw [sound1300 B _hB _hF, sound3308 B _hB _hF] at h
  norm_num [nodeValue4623, nodeValue1300, nodeValue3308, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5149 node5149Labels = Sparse.eval nodeValue5149 (mixedVector B) := by
  have h := singleton5149 B _hB
  rw [sound2924 B _hB _hF, sound3605 B _hB _hF] at h
  norm_num [nodeValue5149, nodeValue2924, nodeValue3605, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5204 node5204Labels = Sparse.eval nodeValue5204 (mixedVector B) := by
  have h := singleton5204 B _hB
  rw [sound2881 B _hB _hF, sound3624 B _hB _hF] at h
  norm_num [nodeValue5204, nodeValue2881, nodeValue3624, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5284 node5284Labels = Sparse.eval nodeValue5284 (mixedVector B) := by
  have h := singleton5284 B _hB
  rw [sound3077 B _hB _hF, sound3625 B _hB _hF] at h
  norm_num [nodeValue5284, nodeValue3077, nodeValue3625, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5294 node5294Labels = Sparse.eval nodeValue5294 (mixedVector B) := by
  have h := singleton5294 B _hB
  rw [sound2768 B _hB _hF, sound3632 B _hB _hF] at h
  norm_num [nodeValue5294, nodeValue2768, nodeValue3632, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources52
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1683 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1683 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1683 + difference 0 1) (sourceB1683 + difference 1 0) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA1683 + difference 0 1) (sourceB1683 + difference 1 0) sourceC1683) = raw24752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24752; decide +kernel
    rw [ha]
    exact (canonical24752 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1683 + difference 0 2) (sourceB1683 + difference 2 0) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA1683 + difference 0 2) (sourceB1683 + difference 2 0) sourceC1683) = raw24753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24753; decide +kernel
    rw [ha]
    exact (canonical24753 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1683 + difference 0 3) (sourceB1683 + difference 3 0) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1683 + difference 0 3) (sourceB1683 + difference 3 0) sourceC1683) = raw24754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24754; decide +kernel
    rw [ha]
    exact (canonical24754 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1683 + difference 0 4) (sourceB1683 + difference 4 0) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA1683 + difference 0 4) (sourceB1683 + difference 4 0) sourceC1683) = raw24755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24755; decide +kernel
    rw [ha]
    exact (canonical24755 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1683 + difference 0 5) (sourceB1683 + difference 5 0) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1683 + difference 0 5) (sourceB1683 + difference 5 0) sourceC1683) = raw24756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24756; decide +kernel
    rw [ha]
    exact (canonical24756 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1683 + difference 1 0) (sourceB1683 + difference 0 1) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4139) := by
    have ha : (tripleCharges (sourceA1683 + difference 1 0) (sourceB1683 + difference 0 1) sourceC1683) = raw24757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24757; decide +kernel
    rw [ha]
    exact (canonical24757 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1683 + difference 1 2) (sourceB1683 + difference 2 1) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4513) := by
    have ha : (tripleCharges (sourceA1683 + difference 1 2) (sourceB1683 + difference 2 1) sourceC1683) = raw24758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24758; decide +kernel
    rw [ha]
    exact (canonical24758 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1683 + difference 1 3) (sourceB1683 + difference 3 1) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1683 + difference 1 3) (sourceB1683 + difference 3 1) sourceC1683) = raw24759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24759; decide +kernel
    rw [ha]
    exact (canonical24759 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1683 + difference 1 4) (sourceB1683 + difference 4 1) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA1683 + difference 1 4) (sourceB1683 + difference 4 1) sourceC1683) = raw24760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24760; decide +kernel
    rw [ha]
    exact (canonical24760 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1683 + difference 1 5) (sourceB1683 + difference 5 1) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1683 + difference 1 5) (sourceB1683 + difference 5 1) sourceC1683) = raw24761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24761; decide +kernel
    rw [ha]
    exact (canonical24761 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1683 + difference 2 0) (sourceB1683 + difference 0 2) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4172) := by
    have ha : (tripleCharges (sourceA1683 + difference 2 0) (sourceB1683 + difference 0 2) sourceC1683) = raw24762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24762; decide +kernel
    rw [ha]
    exact (canonical24762 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1683 + difference 2 1) (sourceB1683 + difference 1 2) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4541) := by
    have ha : (tripleCharges (sourceA1683 + difference 2 1) (sourceB1683 + difference 1 2) sourceC1683) = raw24763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24763; decide +kernel
    rw [ha]
    exact (canonical24763 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1683 + difference 2 3) (sourceB1683 + difference 3 2) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1683 + difference 2 3) (sourceB1683 + difference 3 2) sourceC1683) = raw24764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24764; decide +kernel
    rw [ha]
    exact (canonical24764 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1683 + difference 2 4) (sourceB1683 + difference 4 2) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1683 + difference 2 4) (sourceB1683 + difference 4 2) sourceC1683) = raw24765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24765; decide +kernel
    rw [ha]
    exact (canonical24765 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1683 + difference 2 5) (sourceB1683 + difference 5 2) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1683 + difference 2 5) (sourceB1683 + difference 5 2) sourceC1683) = raw24766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24766; decide +kernel
    rw [ha]
    exact (canonical24766 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1683 + difference 3 0) (sourceB1683 + difference 0 3) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4141) := by
    have ha : (tripleCharges (sourceA1683 + difference 3 0) (sourceB1683 + difference 0 3) sourceC1683) = raw24767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24767; decide +kernel
    rw [ha]
    exact (canonical24767 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1683 + difference 3 1) (sourceB1683 + difference 1 3) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4522) := by
    have ha : (tripleCharges (sourceA1683 + difference 3 1) (sourceB1683 + difference 1 3) sourceC1683) = raw24768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24768; decide +kernel
    rw [ha]
    exact (canonical24768 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1683 + difference 3 2) (sourceB1683 + difference 2 3) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4515) := by
    have ha : (tripleCharges (sourceA1683 + difference 3 2) (sourceB1683 + difference 2 3) sourceC1683) = raw24769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24769; decide +kernel
    rw [ha]
    exact (canonical24769 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1683 + difference 3 4) (sourceB1683 + difference 4 3) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4586) := by
    have ha : (tripleCharges (sourceA1683 + difference 3 4) (sourceB1683 + difference 4 3) sourceC1683) = raw24770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24770; decide +kernel
    rw [ha]
    exact (canonical24770 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1683 + difference 3 5) (sourceB1683 + difference 5 3) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1683 + difference 3 5) (sourceB1683 + difference 5 3) sourceC1683) = raw24771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24771; decide +kernel
    rw [ha]
    exact (canonical24771 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1683 + difference 4 0) (sourceB1683 + difference 0 4) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4145) := by
    have ha : (tripleCharges (sourceA1683 + difference 4 0) (sourceB1683 + difference 0 4) sourceC1683) = raw24772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24772; decide +kernel
    rw [ha]
    exact (canonical24772 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1683 + difference 4 1) (sourceB1683 + difference 1 4) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4524) := by
    have ha : (tripleCharges (sourceA1683 + difference 4 1) (sourceB1683 + difference 1 4) sourceC1683) = raw24773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24773; decide +kernel
    rw [ha]
    exact (canonical24773 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1683 + difference 4 2) (sourceB1683 + difference 2 4) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4518) := by
    have ha : (tripleCharges (sourceA1683 + difference 4 2) (sourceB1683 + difference 2 4) sourceC1683) = raw24774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24774; decide +kernel
    rw [ha]
    exact (canonical24774 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1683 + difference 4 3) (sourceB1683 + difference 3 4) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1683 + difference 4 3) (sourceB1683 + difference 3 4) sourceC1683) = raw24775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24775; decide +kernel
    rw [ha]
    exact (canonical24775 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1683 + difference 4 5) (sourceB1683 + difference 5 4) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1683 + difference 4 5) (sourceB1683 + difference 5 4) sourceC1683) = raw24776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24776; decide +kernel
    rw [ha]
    exact (canonical24776 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1683 + difference 5 0) (sourceB1683 + difference 0 5) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4140) := by
    have ha : (tripleCharges (sourceA1683 + difference 5 0) (sourceB1683 + difference 0 5) sourceC1683) = raw24777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24777; decide +kernel
    rw [ha]
    exact (canonical24777 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1683 + difference 5 1) (sourceB1683 + difference 1 5) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4521) := by
    have ha : (tripleCharges (sourceA1683 + difference 5 1) (sourceB1683 + difference 1 5) sourceC1683) = raw24778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24778; decide +kernel
    rw [ha]
    exact (canonical24778 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1683 + difference 5 2) (sourceB1683 + difference 2 5) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4514) := by
    have ha : (tripleCharges (sourceA1683 + difference 5 2) (sourceB1683 + difference 2 5) sourceC1683) = raw24779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24779; decide +kernel
    rw [ha]
    exact (canonical24779 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1683 + difference 5 3) (sourceB1683 + difference 3 5) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1683 + difference 5 3) (sourceB1683 + difference 3 5) sourceC1683) = raw24780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24780; decide +kernel
    rw [ha]
    exact (canonical24780 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1683 + difference 5 4) (sourceB1683 + difference 4 5) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4583) := by
    have ha : (tripleCharges (sourceA1683 + difference 5 4) (sourceB1683 + difference 4 5) sourceC1683) = raw24781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24781; decide +kernel
    rw [ha]
    exact (canonical24781 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1683 sourceB1683 sourceC1683
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1683, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1441 : Integer.Sparse.reindex keyMap MixedData.row1441 = numericRow1441 := by decide +kernel

theorem numericCheck1441 (x : Master → ℝ) : Integer.Sparse.eval numericRow1441 x =
    (17280 : ℝ) * reducedSource1441 x := by
  norm_num [numericRow1441, reducedSource1441, Integer.Sparse.eval, Sparse.eval, nodeValue4139, nodeValue4140, nodeValue4141, nodeValue4145, nodeValue4172, nodeValue4513, nodeValue4514, nodeValue4515, nodeValue4518, nodeValue4521, nodeValue4522, nodeValue4524, nodeValue4541, nodeValue4581, nodeValue4583, nodeValue4586, nodeValue4601, nodeValue4602, nodeValue4605, nodeValue4606, nodeValue4612, nodeValue4622, nodeValue4623, nodeValue5149, nodeValue5204, nodeValue5284, nodeValue5292, nodeValue5294]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1441 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1441 (mixedVector B) = 0 := by
  have h4139 : mixedVector B (Sum.inr 4139) = Sparse.eval nodeValue4139 (mixedVector B) := by
    change mixedMoment B node4139 node4139Labels = _
    exact sound4139 B hB hF
  have h4140 : mixedVector B (Sum.inr 4140) = Sparse.eval nodeValue4140 (mixedVector B) := by
    change mixedMoment B node4140 node4140Labels = _
    exact sound4140 B hB hF
  have h4141 : mixedVector B (Sum.inr 4141) = Sparse.eval nodeValue4141 (mixedVector B) := by
    change mixedMoment B node4141 node4141Labels = _
    exact sound4141 B hB hF
  have h4145 : mixedVector B (Sum.inr 4145) = Sparse.eval nodeValue4145 (mixedVector B) := by
    change mixedMoment B node4145 node4145Labels = _
    exact sound4145 B hB hF
  have h4172 : mixedVector B (Sum.inr 4172) = Sparse.eval nodeValue4172 (mixedVector B) := by
    change mixedMoment B node4172 node4172Labels = _
    exact sound4172 B hB hF
  have h4513 : mixedVector B (Sum.inr 4513) = Sparse.eval nodeValue4513 (mixedVector B) := by
    change mixedMoment B node4513 node4513Labels = _
    exact sound4513 B hB hF
  have h4514 : mixedVector B (Sum.inr 4514) = Sparse.eval nodeValue4514 (mixedVector B) := by
    change mixedMoment B node4514 node4514Labels = _
    exact sound4514 B hB hF
  have h4515 : mixedVector B (Sum.inr 4515) = Sparse.eval nodeValue4515 (mixedVector B) := by
    change mixedMoment B node4515 node4515Labels = _
    exact sound4515 B hB hF
  have h4518 : mixedVector B (Sum.inr 4518) = Sparse.eval nodeValue4518 (mixedVector B) := by
    change mixedMoment B node4518 node4518Labels = _
    exact sound4518 B hB hF
  have h4521 : mixedVector B (Sum.inr 4521) = Sparse.eval nodeValue4521 (mixedVector B) := by
    change mixedMoment B node4521 node4521Labels = _
    exact sound4521 B hB hF
  have h4522 : mixedVector B (Sum.inr 4522) = Sparse.eval nodeValue4522 (mixedVector B) := by
    change mixedMoment B node4522 node4522Labels = _
    exact sound4522 B hB hF
  have h4524 : mixedVector B (Sum.inr 4524) = Sparse.eval nodeValue4524 (mixedVector B) := by
    change mixedMoment B node4524 node4524Labels = _
    exact sound4524 B hB hF
  have h4541 : mixedVector B (Sum.inr 4541) = Sparse.eval nodeValue4541 (mixedVector B) := by
    change mixedMoment B node4541 node4541Labels = _
    exact sound4541 B hB hF
  have h4581 : mixedVector B (Sum.inr 4581) = Sparse.eval nodeValue4581 (mixedVector B) := by
    change mixedMoment B node4581 node4581Labels = _
    exact sound4581 B hB hF
  have h4583 : mixedVector B (Sum.inr 4583) = Sparse.eval nodeValue4583 (mixedVector B) := by
    change mixedMoment B node4583 node4583Labels = _
    exact sound4583 B hB hF
  have h4586 : mixedVector B (Sum.inr 4586) = Sparse.eval nodeValue4586 (mixedVector B) := by
    change mixedMoment B node4586 node4586Labels = _
    exact sound4586 B hB hF
  have h4601 : mixedVector B (Sum.inr 4601) = Sparse.eval nodeValue4601 (mixedVector B) := by
    change mixedMoment B node4601 node4601Labels = _
    exact sound4601 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4622 : mixedVector B (Sum.inr 4622) = Sparse.eval nodeValue4622 (mixedVector B) := by
    change mixedMoment B node4622 node4622Labels = _
    exact sound4622 B hB hF
  have h4623 : mixedVector B (Sum.inr 4623) = Sparse.eval nodeValue4623 (mixedVector B) := by
    change mixedMoment B node4623 node4623Labels = _
    exact sound4623 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5204 : mixedVector B (Sum.inr 5204) = Sparse.eval nodeValue5204 (mixedVector B) := by
    change mixedMoment B node5204 node5204Labels = _
    exact sound5204 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  simpa only [sourceForm1683, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4139, h4140, h4141, h4145, h4172, h4513, h4514, h4515, h4518, h4521, h4522, h4524, h4541, h4581, h4583, h4586, h4601, h4602, h4605, h4606, h4612, h4622, h4623, h5149, h5204, h5284, h5292, h5294, reducedSource1441] using sourceEq1683 B hB

theorem rowSound1441_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1441 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1441, numericCheck1441, reducedZero1441 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e_oai
