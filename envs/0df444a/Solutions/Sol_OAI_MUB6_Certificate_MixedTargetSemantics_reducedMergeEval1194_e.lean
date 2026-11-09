-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:10:57.029631+00:00
-- url     : https://prove2.me/submissions/03046e32-23ff-4b89-b493-1bdcef206dd7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E130
import Definitions.Def_OAIQ106E137
import Definitions.Def_OAIQ106E138
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3087_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3088_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3089_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3109_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_CompareMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse collection needs only a computable comparison, not order axioms.
The comparison changes the representation but never its real evaluation. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*} [DecidableEq ι]

theorem eval_mergeByFuel (less : ι → ι → Bool) (fuel : ℕ)
    (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeByFuel less fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeByFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeByFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeByFuel]
      | cons b bs =>
        simp only [mergeByFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_mergeBy (less : ι → ι → Bool) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeBy less a b) x = eval a x + eval b x := eval_mergeByFuel _ _ _ _ _

end MUB6.Certificate.Integer.Sparse

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

theorem canonical376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw376 raw376Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw376 raw376Labels = mixedMoment B raw376step0 raw376step0Labels := by
      have ha : raw376step0 = (fun i j => raw376 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw376step0 raw376; decide +kernel
      have hl : raw376step0Labels = raw376Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw376 raw376Labels permutation32 permutation5
    mixedMoment B raw376step0 raw376step0Labels = mixedMoment B raw376step1 raw376step1Labels := by
      have ha : raw376step1 = raw376step0 := by apply Matrix.ext; unfold raw376step1 raw376step0; decide +kernel
      have hl : raw376step0Labels = labelEmbedding1 ∘ raw376step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw376step0 raw376step0Labels raw376step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3099 node3099Labels := by rfl

theorem canonical377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw377 raw377Labels = mixedMoment B node401 node401Labels := by
  calc
    mixedMoment B raw377 raw377Labels = mixedMoment B raw377step0 raw377step0Labels := by
      have ha : raw377step0 = (fun i j => raw377 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw377step0 raw377; decide +kernel
      have hl : raw377step0Labels = raw377Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw377 raw377Labels permutation36 permutation4
    _ = mixedMoment B node401 node401Labels := by rfl

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

theorem canonical384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw384 raw384Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw384 raw384Labels = mixedMoment B raw384step0 raw384step0Labels := by
      have ha : raw384step0 = (fun i j => raw384 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw384step0 raw384; decide +kernel
      have hl : raw384step0Labels = raw384Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw384 raw384Labels permutation8 permutation5
    mixedMoment B raw384step0 raw384step0Labels = mixedMoment B raw384step1 raw384step1Labels := by
      have ha : raw384step1 = raw384step0 := by apply Matrix.ext; unfold raw384step1 raw384step0; decide +kernel
      have hl : raw384step0Labels = labelEmbedding1 ∘ raw384step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw384step0 raw384step0Labels raw384step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3103 node3103Labels := by rfl

theorem canonical385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw385 raw385Labels = mixedMoment B node402 node402Labels := by
  calc
    mixedMoment B raw385 raw385Labels = mixedMoment B raw385step0 raw385step0Labels := by
      have ha : raw385step0 = (fun i j => raw385 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw385step0 raw385; decide +kernel
      have hl : raw385step0Labels = raw385Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw385 raw385Labels permutation8 permutation4
    _ = mixedMoment B node402 node402Labels := by rfl

theorem canonical392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw392 raw392Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw392 raw392Labels = mixedMoment B raw392step0 raw392step0Labels := by
      have ha : raw392step0 = (fun i j => raw392 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw392step0 raw392; decide +kernel
      have hl : raw392step0Labels = raw392Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw392 raw392Labels permutation8 permutation5
    mixedMoment B raw392step0 raw392step0Labels = mixedMoment B raw392step1 raw392step1Labels := by
      have ha : raw392step1 = raw392step0 := by apply Matrix.ext; unfold raw392step1 raw392step0; decide +kernel
      have hl : raw392step0Labels = labelEmbedding1 ∘ raw392step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw392step0 raw392step0Labels raw392step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3110 node3110Labels := by rfl

theorem canonical393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw393 raw393Labels = mixedMoment B node390 node390Labels := by
  calc
    mixedMoment B raw393 raw393Labels = mixedMoment B raw393step0 raw393step0Labels := by
      have ha : raw393step0 = (fun i j => raw393 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw393step0 raw393; decide +kernel
      have hl : raw393step0Labels = raw393Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw393 raw393Labels permutation8 permutation4
    _ = mixedMoment B node390 node390Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5149 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5149 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5149 = injectiveMoment H raw5149step0 := by
      have heq : raw5149step0 = (fun i j => raw5149 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5149 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical750 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw750 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw750 = injectiveMoment H raw750step0 := by
      have heq : raw750step0 = -raw750 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw750).symm
    injectiveMoment H raw750step0 = injectiveMoment H raw750step1 := by
      have heq : raw750step1 = (fun i j => raw750step0 (permutation11 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw750step0 permutation11 permutation6
    _ = injectiveMoment H node261 := by rfl

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

theorem canonical7981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7981 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7981 = injectiveMoment H raw7981step0 := by
      have hz : ∀ j, raw7981 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7981step0 = (fun i j => raw7981 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981 permutation128 hz
    injectiveMoment H raw7981step0 = injectiveMoment H raw7981step1 := by
      have hz : ∀ j, raw7981step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7981step1 = (fun i j => raw7981step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step0 permutation27 hz
    injectiveMoment H raw7981step1 = injectiveMoment H raw7981step2 := by
      have hz : ∀ j, raw7981step1 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7981step2 = (fun i j => raw7981step1 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step1 permutation7 hz
    injectiveMoment H raw7981step2 = injectiveMoment H raw7981step3 := by
      have hz : ∀ j, raw7981step2 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7981step3 = (fun i j => raw7981step2 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step2 permutation2 hz
    injectiveMoment H raw7981step3 = injectiveMoment H raw7981step4 := by
      have hz : ∀ j, raw7981step3 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7981step4 = (fun i j => raw7981step3 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step3 permutation0 hz
    injectiveMoment H raw7981step4 = injectiveMoment H raw7981step5 := by
      have hz : ∀ i, raw7981step4 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7981step5 = (fun i j => raw7981step4 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7981step4 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

theorem canonical7995 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7995 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw7995 = injectiveMoment H raw7995step0 := by
      have heq : raw7995step0 = (fun i j => raw7995 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7995 permutation5 permutation4
    _ = injectiveMoment H node63 := by rfl

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

theorem canonical893 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw893 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw893 = injectiveMoment H raw893step0 := by
      have hz : ∀ j, raw893 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw893step0 = (fun i j => raw893 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw893 permutation57 hz
    _ = injectiveMoment H node26 := by rfl

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

theorem canonical5190 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5190 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw5190 = injectiveMoment H raw5190step0 := by
      have heq : raw5190step0 = (fun i j => raw5190 (permutation39 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5190 permutation39 permutation1
    _ = injectiveMoment H node232 := by rfl

theorem canonical5192 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5192 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5192 = injectiveMoment H raw5192step0 := by
      have heq : raw5192step0 = (fun i j => raw5192 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5192 permutation11 permutation1
    _ = injectiveMoment H node46 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical233
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7462 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7462 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7462 = injectiveMoment H raw7462step0 := by
      have hz : ∀ i, raw7462 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw7462step0 = (fun i j => raw7462 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7462 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

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

theorem sound43 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node43 = Sparse.eval value43 (momentVector H) := by
  have hc : momentVector H 26 = injectiveMoment H node43 := rfl
  simp [value43, Sparse.eval, hc]

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

theorem sound61 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node61 = Sparse.eval value61 (momentVector H) := by
  have heq : pivotMatrix61 = (fun u v => node61 (pivotPermutation61 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node61 = injectiveMoment H pivotMatrix61 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix61 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix61 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix61 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix61 (0 : Fin 2) = raw7462 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7462 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix61 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix61 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node61 + (injectiveMoment H (mergeFirst pivotMatrix61 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix61 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value61, value11, value5, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical777 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw777 = injectiveMoment H node708 := by
  calc
    injectiveMoment H raw777 = injectiveMoment H raw777step0 := by
      have heq : raw777step0 = (fun i j => raw777 (permutation97 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw777 permutation97 permutation6
    _ = injectiveMoment H node708 := by rfl

theorem canonical778 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw778 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw778 = injectiveMoment H raw778step0 := by
      have heq : raw778step0 = (fun i j => raw778 (permutation26 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw778 permutation26 permutation6
    _ = injectiveMoment H node226 := by rfl

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

theorem canonical7685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7685 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7685 = injectiveMoment H raw7685step0 := by
      have hz : ∀ j, raw7685 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7685step0 = (fun i j => raw7685 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7685 permutation27 hz
    injectiveMoment H raw7685step0 = injectiveMoment H raw7685step1 := by
      have heq : raw7685step1 = (fun i j => raw7685step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7685step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

theorem canonical7686 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7686 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7686 = injectiveMoment H raw7686step0 := by
      have hz : ∀ j, raw7686 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7686step0 = (fun i j => raw7686 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7686 permutation128 hz
    injectiveMoment H raw7686step0 = injectiveMoment H raw7686step1 := by
      have hz : ∀ j, raw7686step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7686step1 = (fun i j => raw7686step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7686step0 permutation27 hz
    injectiveMoment H raw7686step1 = injectiveMoment H raw7686step2 := by
      have heq : raw7686step2 = (fun i j => raw7686step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7686step1 permutation7 permutation2
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4088 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4088 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw4088 = injectiveMoment H raw4088step0 := by
      have heq : raw4088step0 = -raw4088 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4088).symm
    injectiveMoment H raw4088step0 = injectiveMoment H raw4088step1 := by
      have heq : raw4088step1 = (fun i j => raw4088step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4088step0 permutation28 permutation5
    _ = injectiveMoment H node185 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4922 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4922 = injectiveMoment H node226 := by
  rfl

theorem canonical4925 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4925 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4925 = injectiveMoment H raw4925step0 := by
      have heq : raw4925step0 = -raw4925 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4925).symm
    injectiveMoment H raw4925step0 = injectiveMoment H raw4925step1 := by
      have heq : raw4925step1 = (fun i j => raw4925step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4925step0 permutation8 permutation3
    _ = injectiveMoment H node36 := by rfl

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

theorem canonical4945 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4945 = injectiveMoment H node229 := by
  rfl

theorem canonical4946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4946 = injectiveMoment H node230 := by
  rfl

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

theorem canonical4965 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4965 = injectiveMoment H node43 := by
  rfl

theorem canonical4966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4966 = injectiveMoment H node44 := by
  rfl

theorem canonical4967 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4967 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw4967 = injectiveMoment H raw4967step0 := by
      have heq : raw4967step0 = -raw4967 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4967).symm
    injectiveMoment H raw4967step0 = injectiveMoment H raw4967step1 := by
      have heq : raw4967step1 = (fun i j => raw4967step0 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4967step0 permutation4 permutation6
    _ = injectiveMoment H node61 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical184
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5891 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5891 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw5891 = injectiveMoment H raw5891step0 := by
      have heq : raw5891step0 = (fun i j => raw5891 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5891 permutation4 permutation5
    _ = injectiveMoment H node36 := by rfl

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

theorem canonical5972 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5972 = injectiveMoment H node56 := by
  rfl

theorem canonical5979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5979 = injectiveMoment H node57 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical231
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7419 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7419 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw7419 = injectiveMoment H raw7419step0 := by
      have heq : raw7419step0 = -raw7419 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7419).symm
    injectiveMoment H raw7419step0 = injectiveMoment H raw7419step1 := by
      have heq : raw7419step1 = (fun i j => raw7419step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7419step0 permutation8 permutation3
    _ = injectiveMoment H node57 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound226 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node226 = Sparse.eval value226 (momentVector H) := by
  have heq : pivotMatrix226 = (fun u v => node226 (pivotPermutation226 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node226 = injectiveMoment H pivotMatrix226 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix226 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix226 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix226 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix226 (0 : Fin 3) = raw7419 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7419 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix226 (1 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix226 (1 : Fin 3) = raw4965 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4965 hH).trans (sound43 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix226 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix226 (2 : Fin 3) = raw4925 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4925 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node226 + (injectiveMoment H (mergeFirst pivotMatrix226 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix226 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix226 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value226, value36, value43, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound229 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node229 = Sparse.eval value229 (momentVector H) := by
  have heq : pivotMatrix229 = (fun u v => node229 (pivotPermutation229 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node229 = injectiveMoment H pivotMatrix229 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix229 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix229 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix229 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix229 (0 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix229 (1 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix229 (1 : Fin 3) = raw4965 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4965 hH).trans (sound43 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix229 (2 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix229 (2 : Fin 3) = raw4966 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4966 hH).trans (sound44 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node229 + (injectiveMoment H (mergeFirst pivotMatrix229 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix229 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix229 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value229, value36, value43, value44, Sparse.eval] at hc ⊢
  linarith

theorem sound230 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node230 = Sparse.eval value230 (momentVector H) := by
  have heq : pivotMatrix230 = (fun u v => node230 (pivotPermutation230 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node230 = injectiveMoment H pivotMatrix230 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix230 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix230 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix230 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix230 (0 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix230 (1 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix230 (1 : Fin 3) = raw4966 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4966 hH).trans (sound44 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix230 (2 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix230 (2 : Fin 3) = raw4967 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4967 hH).trans (sound61 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node230 + (injectiveMoment H (mergeFirst pivotMatrix230 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix230 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix230 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value230, value44, value61, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound232 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node232 = Sparse.eval value232 (momentVector H) := by
  have heq : pivotMatrix232 = (fun u v => node232 (pivotPermutation232 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node232 = injectiveMoment H pivotMatrix232 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix232 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix232 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix232 (0 : Fin 4)) =
      Sparse.eval value26 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (0 : Fin 4) = raw914 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical914 hH).trans (sound26 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix232 (1 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (1 : Fin 4) = raw5177 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5177 hH).trans (sound11 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix232 (2 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (2 : Fin 4) = raw5197 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5197 hH).trans (sound11 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix232 (3 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (3 : Fin 4) = raw5204 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5204 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node232 + (injectiveMoment H (mergeFirst pivotMatrix232 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value232, value11, value26, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound4
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound261 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node261 = Sparse.eval value261 (momentVector H) := by
  have heq : pivotMatrix261 = (fun u v => node261 (pivotPermutation261 u) v) := by apply Matrix.ext; unfold pivotMatrix261 node261 pivotPermutation261; decide +kernel
  have hmoment : injectiveMoment H node261 = injectiveMoment H pivotMatrix261 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix261 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix261 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix261 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix261 (0 : Fin 3) = raw7995 := by apply Matrix.ext; unfold mergeFirst pivotMatrix261 raw7995; decide +kernel
    rw [heq]
    exact (canonical7995 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix261 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix261 (1 : Fin 3) = raw5972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix261 raw5972; decide +kernel
    rw [heq]
    exact (canonical5972 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix261 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix261 (2 : Fin 3) = raw5891 := by apply Matrix.ext; unfold mergeFirst pivotMatrix261 raw5891; decide +kernel
    rw [heq]
    exact (canonical5891 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node261 + (injectiveMoment H (mergeFirst pivotMatrix261 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix261 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix261 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value261, value36, value56, value63, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound11
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound708 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node708 = Sparse.eval value708 (momentVector H) := by
  have heq : pivotMatrix708 = (fun u v => node708 (pivotPermutation708 u) v) := by apply Matrix.ext; unfold pivotMatrix708 node708 pivotPermutation708; decide +kernel
  have hmoment : injectiveMoment H node708 = injectiveMoment H pivotMatrix708 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix708 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix708 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix708 (0 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix708 (0 : Fin 4) = raw4088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix708 raw4088; decide +kernel
    rw [heq]
    exact (canonical4088 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix708 (1 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix708 (1 : Fin 4) = raw4922 := by apply Matrix.ext; unfold mergeFirst pivotMatrix708 raw4922; decide +kernel
    rw [heq]
    exact (canonical4922 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix708 (2 : Fin 4)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix708 (2 : Fin 4) = raw4945 := by apply Matrix.ext; unfold mergeFirst pivotMatrix708 raw4945; decide +kernel
    rw [heq]
    exact (canonical4945 hH).trans (sound229 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix708 (3 : Fin 4)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix708 (3 : Fin 4) = raw4946 := by apply Matrix.ext; unfold mergeFirst pivotMatrix708 raw4946; decide +kernel
    rw [heq]
    exact (canonical4946 hH).trans (sound230 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node708 + (injectiveMoment H (mergeFirst pivotMatrix708 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix708 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix708 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix708 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value708, value185, value226, value229, value230, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair390 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node390 node390Labels = Sparse.eval singlePairValue390 (familyPairVector B) := by
  have hp := single_label_three B hB node390
  have hl : node390Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node390 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node390 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node390 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node390 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node390 (EqualityPatterns.family3.label 1) = PairSemantics.raw5149 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node390 PairSemantics.raw5149; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5149 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node390 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node390 (EqualityPatterns.family3.label 2) = PairSemantics.raw7731 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node390 PairSemantics.raw7731; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7731 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node390 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node390 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node390 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node390 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value261 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node390 (EqualityPatterns.family3.label 4) = PairSemantics.raw750 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node390 PairSemantics.raw750; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical750 hH).trans (PairSemantics.sound261 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue390, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value65, PairSemantics.value261, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

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

theorem singlePair401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node401 node401Labels = Sparse.eval singlePairValue401 (familyPairVector B) := by
  have hp := single_label_three B hB node401
  have hl : node401Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node401 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node401 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node401 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node401 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node401 (EqualityPatterns.family3.label 1) = PairSemantics.raw5190 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node401 PairSemantics.raw5190; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5190 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node401 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node401 (EqualityPatterns.family3.label 2) = PairSemantics.raw7686 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node401 PairSemantics.raw7686; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7686 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node401 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node401 (EqualityPatterns.family3.label 3) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node401 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node401 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value708 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node401 (EqualityPatterns.family3.label 4) = PairSemantics.raw777 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node401 PairSemantics.raw777; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical777 hH).trans (PairSemantics.sound708 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue401, PairSemantics.value0, PairSemantics.value11, PairSemantics.value26, PairSemantics.value232, PairSemantics.value708, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair402 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node402 node402Labels = Sparse.eval singlePairValue402 (familyPairVector B) := by
  have hp := single_label_three B hB node402
  have hl : node402Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node402 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node402 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node402 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node402 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node402 (EqualityPatterns.family3.label 1) = PairSemantics.raw5192 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node402 PairSemantics.raw5192; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5192 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node402 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node402 (EqualityPatterns.family3.label 2) = PairSemantics.raw7685 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node402 PairSemantics.raw7685; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7685 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node402 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node402 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node402 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node402 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value226 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node402 (EqualityPatterns.family3.label 4) = PairSemantics.raw778 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node402 PairSemantics.raw778; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical778 hH).trans (PairSemantics.sound226 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue402, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value46, PairSemantics.value226, Sparse.eval] at hp ⊢
  linarith only [hp]

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

theorem singleton3099 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3099 node3099Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node401 node401Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw376 singletonSmall3099
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3099) = raw376Labels := by decide +kernel
  rw [hl, canonical376 B hB] at h
  have hc0 : mixedMoment B raw376 (Fin.cases (0 : Fin 1) singletonSmall3099) =
      mixedMoment B node401 node401Labels := by
    have ha : raw376 = raw377 := by apply Matrix.ext; unfold raw376 raw377; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3099 = raw377Labels := by decide +kernel
    rw [ha, hj, canonical377 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton3103 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3103 node3103Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node402 node402Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw384 singletonSmall3103
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3103) = raw384Labels := by decide +kernel
  rw [hl, canonical384 B hB] at h
  have hc0 : mixedMoment B raw384 (Fin.cases (0 : Fin 1) singletonSmall3103) =
      mixedMoment B node402 node402Labels := by
    have ha : raw384 = raw385 := by apply Matrix.ext; unfold raw384 raw385; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3103 = raw385Labels := by decide +kernel
    rw [ha, hj, canonical385 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton3110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3110 node3110Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node390 node390Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw392 singletonSmall3110
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3110) = raw392Labels := by decide +kernel
  rw [hl, canonical392 B hB] at h
  have hc0 : mixedMoment B raw392 (Fin.cases (0 : Fin 1) singletonSmall3110) =
      mixedMoment B node390 node390Labels := by
    have ha : raw392 = raw393 := by apply Matrix.ext; unfold raw392 raw393; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3110 = raw393Labels := by decide +kernel
    rw [ha, hj, canonical393 B hB]
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

theorem sound3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3054 node3054Labels = Sparse.eval nodeValue3054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3054) = mixedMoment B node3054 node3054Labels := rfl
  simpa [nodeValue3054, Sparse.eval] using hc.symm

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

theorem sound2964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2964 node2964Labels = Sparse.eval nodeValue2964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2964) = mixedMoment B node2964 node2964Labels := rfl
  simpa [nodeValue2964, Sparse.eval] using hc.symm

theorem sound2967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2967 node2967Labels = Sparse.eval nodeValue2967 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2967) = mixedMoment B node2967 node2967Labels := rfl
  simpa [nodeValue2967, Sparse.eval] using hc.symm

theorem sound2979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2979 node2979Labels = Sparse.eval nodeValue2979 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2979) = mixedMoment B node2979 node2979Labels := rfl
  simpa [nodeValue2979, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3065 node3065Labels = 0 := by
  exact mixedMoment_alpha B hF node3065 node3065Labels 2 permutation152
    (by decide +kernel)

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

theorem sound3016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3016 node3016Labels = Sparse.eval nodeValue3016 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3016) = mixedMoment B node3016 node3016Labels := rfl
  simpa [nodeValue3016, Sparse.eval] using hc.symm

theorem sound3023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3023 node3023Labels = Sparse.eval nodeValue3023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3023) = mixedMoment B node3023 node3023Labels := rfl
  simpa [nodeValue3023, Sparse.eval] using hc.symm

theorem sound3024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3024 node3024Labels = Sparse.eval nodeValue3024 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3024) = mixedMoment B node3024 node3024Labels := rfl
  simpa [nodeValue3024, Sparse.eval] using hc.symm

theorem sound3025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3025 node3025Labels = Sparse.eval nodeValue3025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3025) = mixedMoment B node3025 node3025Labels := rfl
  simpa [nodeValue3025, Sparse.eval] using hc.symm

theorem sound3029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3029 node3029Labels = Sparse.eval nodeValue3029 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3029) = mixedMoment B node3029 node3029Labels := rfl
  simpa [nodeValue3029, Sparse.eval] using hc.symm

theorem sound3030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3030 node3030Labels = Sparse.eval nodeValue3030 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3030) = mixedMoment B node3030 node3030Labels := rfl
  simpa [nodeValue3030, Sparse.eval] using hc.symm

theorem sound3031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3031 node3031Labels = Sparse.eval nodeValue3031 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3031) = mixedMoment B node3031 node3031Labels := rfl
  simpa [nodeValue3031, Sparse.eval] using hc.symm

theorem sound3032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3032 node3032Labels = Sparse.eval nodeValue3032 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3032) = mixedMoment B node3032 node3032Labels := rfl
  simpa [nodeValue3032, Sparse.eval] using hc.symm

theorem sound3033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3033 node3033Labels = Sparse.eval nodeValue3033 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3033) = mixedMoment B node3033 node3033Labels := rfl
  simpa [nodeValue3033, Sparse.eval] using hc.symm

theorem sound3036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3036 node3036Labels = Sparse.eval nodeValue3036 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3036) = mixedMoment B node3036 node3036Labels := rfl
  simpa [nodeValue3036, Sparse.eval] using hc.symm

theorem sound3037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3037 node3037Labels = Sparse.eval nodeValue3037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3037) = mixedMoment B node3037 node3037Labels := rfl
  simpa [nodeValue3037, Sparse.eval] using hc.symm

theorem sound3038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3038 node3038Labels = Sparse.eval nodeValue3038 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3038) = mixedMoment B node3038 node3038Labels := rfl
  simpa [nodeValue3038, Sparse.eval] using hc.symm

theorem sound3039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3039 node3039Labels = Sparse.eval nodeValue3039 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3039) = mixedMoment B node3039 node3039Labels := rfl
  simpa [nodeValue3039, Sparse.eval] using hc.symm

theorem sound3040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3040 node3040Labels = Sparse.eval nodeValue3040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3040) = mixedMoment B node3040 node3040Labels := rfl
  simpa [nodeValue3040, Sparse.eval] using hc.symm

theorem sound3043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3043 node3043Labels = Sparse.eval nodeValue3043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3043) = mixedMoment B node3043 node3043Labels := rfl
  simpa [nodeValue3043, Sparse.eval] using hc.symm

theorem sound3044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3044 node3044Labels = Sparse.eval nodeValue3044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3044) = mixedMoment B node3044 node3044Labels := rfl
  simpa [nodeValue3044, Sparse.eval] using hc.symm

theorem sound3045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3045 node3045Labels = Sparse.eval nodeValue3045 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3045) = mixedMoment B node3045 node3045Labels := rfl
  simpa [nodeValue3045, Sparse.eval] using hc.symm

theorem sound3046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3046 node3046Labels = Sparse.eval nodeValue3046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3046) = mixedMoment B node3046 node3046Labels := rfl
  simpa [nodeValue3046, Sparse.eval] using hc.symm

theorem sound3050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3050 node3050Labels = Sparse.eval nodeValue3050 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3050) = mixedMoment B node3050 node3050Labels := rfl
  simpa [nodeValue3050, Sparse.eval] using hc.symm

theorem sound3051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3051 node3051Labels = Sparse.eval nodeValue3051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3051) = mixedMoment B node3051 node3051Labels := rfl
  simpa [nodeValue3051, Sparse.eval] using hc.symm

theorem sound3052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3052 node3052Labels = Sparse.eval nodeValue3052 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3052) = mixedMoment B node3052 node3052Labels := rfl
  simpa [nodeValue3052, Sparse.eval] using hc.symm

theorem sound3053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3053 node3053Labels = Sparse.eval nodeValue3053 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3053) = mixedMoment B node3053 node3053Labels := rfl
  simpa [nodeValue3053, Sparse.eval] using hc.symm

theorem sound3055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3055 node3055Labels = Sparse.eval nodeValue3055 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3055) = mixedMoment B node3055 node3055Labels := rfl
  simpa [nodeValue3055, Sparse.eval] using hc.symm

theorem sound3056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3056 node3056Labels = Sparse.eval nodeValue3056 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3056) = mixedMoment B node3056 node3056Labels := rfl
  simpa [nodeValue3056, Sparse.eval] using hc.symm

theorem sound3058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3058 node3058Labels = Sparse.eval nodeValue3058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3058) = mixedMoment B node3058 node3058Labels := rfl
  simpa [nodeValue3058, Sparse.eval] using hc.symm

theorem sound3059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3059 node3059Labels = Sparse.eval nodeValue3059 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3059) = mixedMoment B node3059 node3059Labels := rfl
  simpa [nodeValue3059, Sparse.eval] using hc.symm

theorem sound3062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3062 node3062Labels = Sparse.eval nodeValue3062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3062) = mixedMoment B node3062 node3062Labels := rfl
  simpa [nodeValue3062, Sparse.eval] using hc.symm

theorem sound3064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3064 node3064Labels = Sparse.eval nodeValue3064 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3064) = mixedMoment B node3064 node3064Labels := rfl
  simpa [nodeValue3064, Sparse.eval] using hc.symm

theorem sound3065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3065 node3065Labels = Sparse.eval nodeValue3065 (mixedVector B) := by
  simpa only [nodeValue3065, Sparse.eval_nil] using zero3065 B _hB _hF

theorem sound3066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3066 node3066Labels = Sparse.eval nodeValue3066 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3066) = mixedMoment B node3066 node3066Labels := rfl
  simpa [nodeValue3066, Sparse.eval] using hc.symm

theorem sound3068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3068 node3068Labels = Sparse.eval nodeValue3068 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3068) = mixedMoment B node3068 node3068Labels := rfl
  simpa [nodeValue3068, Sparse.eval] using hc.symm

theorem sound3069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3069 node3069Labels = Sparse.eval nodeValue3069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3069) = mixedMoment B node3069 node3069Labels := rfl
  simpa [nodeValue3069, Sparse.eval] using hc.symm

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

theorem sound390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node390 node390Labels = Sparse.eval nodeValue390 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue390 (familyPairVector B) := singlePair390 B _hB
    _ = _ := by
      norm_num [singlePairValue390, nodeValue390, Sparse.eval, mixedVector]
      ring

theorem sound401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node401 node401Labels = Sparse.eval nodeValue401 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue401 (familyPairVector B) := singlePair401 B _hB
    _ = _ := by
      norm_num [singlePairValue401, nodeValue401, Sparse.eval, mixedVector]
      ring

theorem sound402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node402 node402Labels = Sparse.eval nodeValue402 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue402 (familyPairVector B) := singlePair402 B _hB
    _ = _ := by
      norm_num [singlePairValue402, nodeValue402, Sparse.eval, mixedVector]
      ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3085 node3085Labels = 0 := by
  exact mixedMoment_alpha B hF node3085 node3085Labels 2 permutation158
    (by decide +kernel)

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

theorem sound3073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3073 node3073Labels = Sparse.eval nodeValue3073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3073) = mixedMoment B node3073 node3073Labels := rfl
  simpa [nodeValue3073, Sparse.eval] using hc.symm

theorem sound3074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3074 node3074Labels = Sparse.eval nodeValue3074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3074) = mixedMoment B node3074 node3074Labels := rfl
  simpa [nodeValue3074, Sparse.eval] using hc.symm

theorem sound3075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3075 node3075Labels = Sparse.eval nodeValue3075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3075) = mixedMoment B node3075 node3075Labels := rfl
  simpa [nodeValue3075, Sparse.eval] using hc.symm

theorem sound3077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3077 node3077Labels = Sparse.eval nodeValue3077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3077) = mixedMoment B node3077 node3077Labels := rfl
  simpa [nodeValue3077, Sparse.eval] using hc.symm

theorem sound3078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3078 node3078Labels = Sparse.eval nodeValue3078 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3078) = mixedMoment B node3078 node3078Labels := rfl
  simpa [nodeValue3078, Sparse.eval] using hc.symm

theorem sound3079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3079 node3079Labels = Sparse.eval nodeValue3079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3079) = mixedMoment B node3079 node3079Labels := rfl
  simpa [nodeValue3079, Sparse.eval] using hc.symm

theorem sound3083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3083 node3083Labels = Sparse.eval nodeValue3083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3083) = mixedMoment B node3083 node3083Labels := rfl
  simpa [nodeValue3083, Sparse.eval] using hc.symm

theorem sound3084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3084 node3084Labels = Sparse.eval nodeValue3084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3084) = mixedMoment B node3084 node3084Labels := rfl
  simpa [nodeValue3084, Sparse.eval] using hc.symm

theorem sound3085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3085 node3085Labels = Sparse.eval nodeValue3085 (mixedVector B) := by
  simpa only [nodeValue3085, Sparse.eval_nil] using zero3085 B _hB _hF

theorem sound3086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3086 node3086Labels = Sparse.eval nodeValue3086 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3086) = mixedMoment B node3086 node3086Labels := rfl
  simpa [nodeValue3086, Sparse.eval] using hc.symm

theorem sound3092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3092 node3092Labels = Sparse.eval nodeValue3092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3092) = mixedMoment B node3092 node3092Labels := rfl
  simpa [nodeValue3092, Sparse.eval] using hc.symm

theorem sound3096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3096 node3096Labels = Sparse.eval nodeValue3096 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3096) = mixedMoment B node3096 node3096Labels := rfl
  simpa [nodeValue3096, Sparse.eval] using hc.symm

theorem sound3097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3097 node3097Labels = Sparse.eval nodeValue3097 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3097) = mixedMoment B node3097 node3097Labels := rfl
  simpa [nodeValue3097, Sparse.eval] using hc.symm

theorem sound3098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3098 node3098Labels = Sparse.eval nodeValue3098 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3098) = mixedMoment B node3098 node3098Labels := rfl
  simpa [nodeValue3098, Sparse.eval] using hc.symm

theorem sound3099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3099 node3099Labels = Sparse.eval nodeValue3099 (mixedVector B) := by
  have h := singleton3099 B _hB
  rw [sound401 B _hB _hF] at h
  norm_num [nodeValue3099, nodeValue401, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3103 node3103Labels = Sparse.eval nodeValue3103 (mixedVector B) := by
  have h := singleton3103 B _hB
  rw [sound402 B _hB _hF] at h
  norm_num [nodeValue3103, nodeValue402, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3108 node3108Labels = Sparse.eval nodeValue3108 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3108) = mixedMoment B node3108 node3108Labels := rfl
  simpa [nodeValue3108, Sparse.eval] using hc.symm

theorem sound3110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3110 node3110Labels = Sparse.eval nodeValue3110 (mixedVector B) := by
  have h := singleton3110 B _hB
  rw [sound390 B _hB _hF] at h
  norm_num [nodeValue3110, nodeValue390, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1139 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1139 x = (-12088519805730816000000 : ℝ) * Sparse.eval nodeValue2964 x := by
  norm_num [reducedTerm1139, nodeValue2964, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1140 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1140 x = (-15967457567244288000000 : ℝ) * Sparse.eval nodeValue2967 x := by
  norm_num [reducedTerm1140, nodeValue2967, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1141 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1141 x = (-421979070165811200000 : ℝ) * Sparse.eval nodeValue2979 x := by
  norm_num [reducedTerm1141, nodeValue2979, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1142 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1142 x = (669848715789926400000 : ℝ) * Sparse.eval nodeValue2981 x := by
  norm_num [reducedTerm1142, nodeValue2981, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1143 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1143 x = (15200456282416742400000 : ℝ) * Sparse.eval nodeValue2984 x := by
  norm_num [reducedTerm1143, nodeValue2984, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1144 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1144 x = (-4525925648641818624000 : ℝ) * Sparse.eval nodeValue3016 x := by
  norm_num [reducedTerm1144, nodeValue3016, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1145 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1145 x = (-5814069266409062400000 : ℝ) * Sparse.eval nodeValue3023 x := by
  norm_num [reducedTerm1145, nodeValue3023, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1146 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1146 x = (1699294017721466880000 : ℝ) * Sparse.eval nodeValue3024 x := by
  norm_num [reducedTerm1146, nodeValue3024, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1147 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1147 x = (-3657804786659229696000 : ℝ) * Sparse.eval nodeValue3025 x := by
  norm_num [reducedTerm1147, nodeValue3025, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1148 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1148 x = (-12883500708986880000000 : ℝ) * Sparse.eval nodeValue3029 x := by
  norm_num [reducedTerm1148, nodeValue3029, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1149 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1149 x = (-4222719607976755200000 : ℝ) * Sparse.eval nodeValue3030 x := by
  norm_num [reducedTerm1149, nodeValue3030, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1150 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1150 x = (4597326756229939200000 : ℝ) * Sparse.eval nodeValue3031 x := by
  norm_num [reducedTerm1150, nodeValue3031, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1151 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1151 x = (2216831132152627200000 : ℝ) * Sparse.eval nodeValue3032 x := by
  norm_num [reducedTerm1151, nodeValue3032, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1152 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1152 x = (-4250125755517501440000 : ℝ) * Sparse.eval nodeValue3033 x := by
  norm_num [reducedTerm1152, nodeValue3033, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1153 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1153 x = (3735836684119572480000 : ℝ) * Sparse.eval nodeValue3036 x := by
  norm_num [reducedTerm1153, nodeValue3036, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1154 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1154 x = (-12943331682486976512000 : ℝ) * Sparse.eval nodeValue3037 x := by
  norm_num [reducedTerm1154, nodeValue3037, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1155 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1155 x = (14492549870804533248000 : ℝ) * Sparse.eval nodeValue3038 x := by
  norm_num [reducedTerm1155, nodeValue3038, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1156 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1156 x = (9313996009718808576000 : ℝ) * Sparse.eval nodeValue3039 x := by
  norm_num [reducedTerm1156, nodeValue3039, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1157 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1157 x = (919241958555648000000 : ℝ) * Sparse.eval nodeValue3040 x := by
  norm_num [reducedTerm1157, nodeValue3040, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1158 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1158 x = (-2589617639009157120000 : ℝ) * Sparse.eval nodeValue3043 x := by
  norm_num [reducedTerm1158, nodeValue3043, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1159 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1159 x = (-16300334708112752640000 : ℝ) * Sparse.eval nodeValue3044 x := by
  norm_num [reducedTerm1159, nodeValue3044, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1160 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1160 x = (4564186441588408320000 : ℝ) * Sparse.eval nodeValue3045 x := by
  norm_num [reducedTerm1160, nodeValue3045, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1161 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1161 x = (3365072991753338880000 : ℝ) * Sparse.eval nodeValue3046 x := by
  norm_num [reducedTerm1161, nodeValue3046, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1162 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1162 x = (-4404201698619555840000 : ℝ) * Sparse.eval nodeValue3050 x := by
  norm_num [reducedTerm1162, nodeValue3050, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1163 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1163 x = (3906032471591878656000 : ℝ) * Sparse.eval nodeValue3051 x := by
  norm_num [reducedTerm1163, nodeValue3051, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1164 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1164 x = (7967955760767959040000 : ℝ) * Sparse.eval nodeValue3052 x := by
  norm_num [reducedTerm1164, nodeValue3052, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1165 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1165 x = (-4769146164905902080000 : ℝ) * Sparse.eval nodeValue3053 x := by
  norm_num [reducedTerm1165, nodeValue3053, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1166 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1166 x = (-6384294458848051200000 : ℝ) * Sparse.eval nodeValue3054 x := by
  norm_num [reducedTerm1166, nodeValue3054, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1167 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1167 x = (16753008632221532160000 : ℝ) * Sparse.eval nodeValue3055 x := by
  norm_num [reducedTerm1167, nodeValue3055, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1168 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1168 x = (-4052239562185113600000 : ℝ) * Sparse.eval nodeValue3056 x := by
  norm_num [reducedTerm1168, nodeValue3056, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1169 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1169 x = (259351328607436800000 : ℝ) * Sparse.eval nodeValue3058 x := by
  norm_num [reducedTerm1169, nodeValue3058, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1170 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1170 x = (-1852188959337873408000 : ℝ) * Sparse.eval nodeValue3059 x := by
  norm_num [reducedTerm1170, nodeValue3059, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1171 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1171 x = (-4597326756229939200000 : ℝ) * Sparse.eval nodeValue3062 x := by
  norm_num [reducedTerm1171, nodeValue3062, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1172 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1172 x = (7350751094580117504000 : ℝ) * Sparse.eval nodeValue3064 x := by
  norm_num [reducedTerm1172, nodeValue3064, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1173 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1173 x = (2108824540752642048000 : ℝ) * Sparse.eval nodeValue3065 x := by
  norm_num [reducedTerm1173, nodeValue3065, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1174 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1174 x = (-5639933671031439360000 : ℝ) * Sparse.eval nodeValue3066 x := by
  norm_num [reducedTerm1174, nodeValue3066, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1175 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1175 x = (-8048462097973248000000 : ℝ) * Sparse.eval nodeValue3068 x := by
  norm_num [reducedTerm1175, nodeValue3068, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1176 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1176 x = (1668709084299264000000 : ℝ) * Sparse.eval nodeValue3069 x := by
  norm_num [reducedTerm1176, nodeValue3069, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1177 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1177 x = (4020809998518190080000 : ℝ) * Sparse.eval nodeValue3073 x := by
  norm_num [reducedTerm1177, nodeValue3073, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1178 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1178 x = (15546685904170057728000 : ℝ) * Sparse.eval nodeValue3074 x := by
  norm_num [reducedTerm1178, nodeValue3074, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1179 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1179 x = (-1716666600863563776000 : ℝ) * Sparse.eval nodeValue3075 x := by
  norm_num [reducedTerm1179, nodeValue3075, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1180 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1180 x = (-16333431861191639040000 : ℝ) * Sparse.eval nodeValue3077 x := by
  norm_num [reducedTerm1180, nodeValue3077, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1181 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1181 x = (18561918376033320960000 : ℝ) * Sparse.eval nodeValue3078 x := by
  norm_num [reducedTerm1181, nodeValue3078, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1182 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1182 x = (-12298111992747786240000 : ℝ) * Sparse.eval nodeValue3079 x := by
  norm_num [reducedTerm1182, nodeValue3079, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1183 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1183 x = (-1415934024744960000000 : ℝ) * Sparse.eval nodeValue3083 x := by
  norm_num [reducedTerm1183, nodeValue3083, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1184 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1184 x = (-50941984034146222080000 : ℝ) * Sparse.eval nodeValue3084 x := by
  norm_num [reducedTerm1184, nodeValue3084, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1185 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1185 x = (-5020201290366517248000 : ℝ) * Sparse.eval nodeValue3085 x := by
  norm_num [reducedTerm1185, nodeValue3085, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1186 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1186 x = (-22351245374360125440000 : ℝ) * Sparse.eval nodeValue3086 x := by
  norm_num [reducedTerm1186, nodeValue3086, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1187 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1187 x = (-3811256349900668928000 : ℝ) * Sparse.eval nodeValue3087 x := by
  norm_num [reducedTerm1187, nodeValue3087, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1188 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1188 x = (-1418854997041348608000 : ℝ) * Sparse.eval nodeValue3088 x := by
  norm_num [reducedTerm1188, nodeValue3088, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1189 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1189 x = (-5665773180262809600000 : ℝ) * Sparse.eval nodeValue3089 x := by
  norm_num [reducedTerm1189, nodeValue3089, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1190 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1190 x = (-3891082594516992000000 : ℝ) * Sparse.eval nodeValue3092 x := by
  norm_num [reducedTerm1190, nodeValue3092, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1191 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1191 x = (-10769461456860610560000 : ℝ) * Sparse.eval nodeValue3096 x := by
  norm_num [reducedTerm1191, nodeValue3096, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1192 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1192 x = (23327342262493839360000 : ℝ) * Sparse.eval nodeValue3097 x := by
  norm_num [reducedTerm1192, nodeValue3097, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1193 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1193 x = (34405213211462467584000 : ℝ) * Sparse.eval nodeValue3098 x := by
  norm_num [reducedTerm1193, nodeValue3098, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1194 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1194 x = (-9468178881528987648000 : ℝ) * Sparse.eval nodeValue3099 x := by
  norm_num [reducedTerm1194, nodeValue3099, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1195 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1195 x = (-2736289857142259712000 : ℝ) * Sparse.eval nodeValue3103 x := by
  norm_num [reducedTerm1195, nodeValue3103, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1196 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1196 x = (12622627890148147200000 : ℝ) * Sparse.eval nodeValue3108 x := by
  norm_num [reducedTerm1196, nodeValue3108, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1197 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1197 x = (9991713240911904768000 : ℝ) * Sparse.eval nodeValue3109 x := by
  norm_num [reducedTerm1197, nodeValue3109, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1198 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1198 x = (2131060763813216256000 : ℝ) * Sparse.eval nodeValue3110 x := by
  norm_num [reducedTerm1198, nodeValue3110, Integer.Sparse.eval, Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1136Check : reducedMerge1136 = Integer.Sparse.mergeBy masterLess reducedTerm1140 reducedTerm1141 := by decide +kernel

theorem reducedMerge1137Check : reducedMerge1137 = Integer.Sparse.mergeBy masterLess reducedTerm1139 reducedMerge1136 := by decide +kernel

theorem reducedMerge1138Check : reducedMerge1138 = Integer.Sparse.mergeBy masterLess reducedTerm1142 reducedTerm1143 := by decide +kernel

theorem reducedMerge1139Check : reducedMerge1139 = Integer.Sparse.mergeBy masterLess reducedTerm1144 reducedTerm1145 := by decide +kernel

theorem reducedMerge1140Check : reducedMerge1140 = Integer.Sparse.mergeBy masterLess reducedMerge1138 reducedMerge1139 := by decide +kernel

theorem reducedMerge1141Check : reducedMerge1141 = Integer.Sparse.mergeBy masterLess reducedMerge1137 reducedMerge1140 := by decide +kernel

theorem reducedMerge1142Check : reducedMerge1142 = Integer.Sparse.mergeBy masterLess reducedTerm1146 reducedTerm1147 := by decide +kernel

theorem reducedMerge1143Check : reducedMerge1143 = Integer.Sparse.mergeBy masterLess reducedTerm1148 reducedTerm1149 := by decide +kernel

theorem reducedMerge1144Check : reducedMerge1144 = Integer.Sparse.mergeBy masterLess reducedMerge1142 reducedMerge1143 := by decide +kernel

theorem reducedMerge1145Check : reducedMerge1145 = Integer.Sparse.mergeBy masterLess reducedTerm1150 reducedTerm1151 := by decide +kernel

theorem reducedMerge1146Check : reducedMerge1146 = Integer.Sparse.mergeBy masterLess reducedTerm1152 reducedTerm1153 := by decide +kernel

theorem reducedMerge1147Check : reducedMerge1147 = Integer.Sparse.mergeBy masterLess reducedMerge1145 reducedMerge1146 := by decide +kernel

theorem reducedMerge1148Check : reducedMerge1148 = Integer.Sparse.mergeBy masterLess reducedMerge1144 reducedMerge1147 := by decide +kernel

theorem reducedMerge1149Check : reducedMerge1149 = Integer.Sparse.mergeBy masterLess reducedMerge1141 reducedMerge1148 := by decide +kernel

theorem reducedMerge1150Check : reducedMerge1150 = Integer.Sparse.mergeBy masterLess reducedTerm1155 reducedTerm1156 := by decide +kernel

theorem reducedMerge1151Check : reducedMerge1151 = Integer.Sparse.mergeBy masterLess reducedTerm1154 reducedMerge1150 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1152Check : reducedMerge1152 = Integer.Sparse.mergeBy masterLess reducedTerm1157 reducedTerm1158 := by decide +kernel

theorem reducedMerge1153Check : reducedMerge1153 = Integer.Sparse.mergeBy masterLess reducedTerm1159 reducedTerm1160 := by decide +kernel

theorem reducedMerge1154Check : reducedMerge1154 = Integer.Sparse.mergeBy masterLess reducedMerge1152 reducedMerge1153 := by decide +kernel

theorem reducedMerge1155Check : reducedMerge1155 = Integer.Sparse.mergeBy masterLess reducedMerge1151 reducedMerge1154 := by decide +kernel

theorem reducedMerge1156Check : reducedMerge1156 = Integer.Sparse.mergeBy masterLess reducedTerm1161 reducedTerm1162 := by decide +kernel

theorem reducedMerge1157Check : reducedMerge1157 = Integer.Sparse.mergeBy masterLess reducedTerm1163 reducedTerm1164 := by decide +kernel

theorem reducedMerge1158Check : reducedMerge1158 = Integer.Sparse.mergeBy masterLess reducedMerge1156 reducedMerge1157 := by decide +kernel

theorem reducedMerge1159Check : reducedMerge1159 = Integer.Sparse.mergeBy masterLess reducedTerm1165 reducedTerm1166 := by decide +kernel

theorem reducedMerge1160Check : reducedMerge1160 = Integer.Sparse.mergeBy masterLess reducedTerm1167 reducedTerm1168 := by decide +kernel

theorem reducedMerge1161Check : reducedMerge1161 = Integer.Sparse.mergeBy masterLess reducedMerge1159 reducedMerge1160 := by decide +kernel

theorem reducedMerge1162Check : reducedMerge1162 = Integer.Sparse.mergeBy masterLess reducedMerge1158 reducedMerge1161 := by decide +kernel

theorem reducedMerge1163Check : reducedMerge1163 = Integer.Sparse.mergeBy masterLess reducedMerge1155 reducedMerge1162 := by decide +kernel

theorem reducedMerge1164Check : reducedMerge1164 = Integer.Sparse.mergeBy masterLess reducedMerge1149 reducedMerge1163 := by decide +kernel

theorem reducedMerge1165Check : reducedMerge1165 = Integer.Sparse.mergeBy masterLess reducedTerm1170 reducedTerm1171 := by decide +kernel

theorem reducedMerge1166Check : reducedMerge1166 = Integer.Sparse.mergeBy masterLess reducedTerm1169 reducedMerge1165 := by decide +kernel

theorem reducedMerge1167Check : reducedMerge1167 = Integer.Sparse.mergeBy masterLess reducedTerm1172 reducedTerm1173 := by decide +kernel

theorem reducedMerge1168Check : reducedMerge1168 = Integer.Sparse.mergeBy masterLess reducedTerm1174 reducedTerm1175 := by decide +kernel

theorem reducedMerge1169Check : reducedMerge1169 = Integer.Sparse.mergeBy masterLess reducedMerge1167 reducedMerge1168 := by decide +kernel

theorem reducedMerge1170Check : reducedMerge1170 = Integer.Sparse.mergeBy masterLess reducedMerge1166 reducedMerge1169 := by decide +kernel

theorem reducedMerge1171Check : reducedMerge1171 = Integer.Sparse.mergeBy masterLess reducedTerm1176 reducedTerm1177 := by decide +kernel

theorem reducedMerge1172Check : reducedMerge1172 = Integer.Sparse.mergeBy masterLess reducedTerm1178 reducedTerm1179 := by decide +kernel

theorem reducedMerge1173Check : reducedMerge1173 = Integer.Sparse.mergeBy masterLess reducedMerge1171 reducedMerge1172 := by decide +kernel

theorem reducedMerge1174Check : reducedMerge1174 = Integer.Sparse.mergeBy masterLess reducedTerm1180 reducedTerm1181 := by decide +kernel

theorem reducedMerge1175Check : reducedMerge1175 = Integer.Sparse.mergeBy masterLess reducedTerm1182 reducedTerm1183 := by decide +kernel

theorem reducedMerge1176Check : reducedMerge1176 = Integer.Sparse.mergeBy masterLess reducedMerge1174 reducedMerge1175 := by decide +kernel

theorem reducedMerge1177Check : reducedMerge1177 = Integer.Sparse.mergeBy masterLess reducedMerge1173 reducedMerge1176 := by decide +kernel

theorem reducedMerge1178Check : reducedMerge1178 = Integer.Sparse.mergeBy masterLess reducedMerge1170 reducedMerge1177 := by decide +kernel

theorem reducedMerge1179Check : reducedMerge1179 = Integer.Sparse.mergeBy masterLess reducedTerm1185 reducedTerm1186 := by decide +kernel

theorem reducedMerge1180Check : reducedMerge1180 = Integer.Sparse.mergeBy masterLess reducedTerm1184 reducedMerge1179 := by decide +kernel

theorem reducedMerge1181Check : reducedMerge1181 = Integer.Sparse.mergeBy masterLess reducedTerm1187 reducedTerm1188 := by decide +kernel

theorem reducedMerge1182Check : reducedMerge1182 = Integer.Sparse.mergeBy masterLess reducedTerm1189 reducedTerm1190 := by decide +kernel

theorem reducedMerge1183Check : reducedMerge1183 = Integer.Sparse.mergeBy masterLess reducedMerge1181 reducedMerge1182 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1184Check : reducedMerge1184 = Integer.Sparse.mergeBy masterLess reducedMerge1180 reducedMerge1183 := by decide +kernel

theorem reducedMerge1185Check : reducedMerge1185 = Integer.Sparse.mergeBy masterLess reducedTerm1191 reducedTerm1192 := by decide +kernel

theorem reducedMerge1186Check : reducedMerge1186 = Integer.Sparse.mergeBy masterLess reducedTerm1193 reducedTerm1194 := by decide +kernel

theorem reducedMerge1187Check : reducedMerge1187 = Integer.Sparse.mergeBy masterLess reducedMerge1185 reducedMerge1186 := by decide +kernel

theorem reducedMerge1188Check : reducedMerge1188 = Integer.Sparse.mergeBy masterLess reducedTerm1195 reducedTerm1196 := by decide +kernel

theorem reducedMerge1189Check : reducedMerge1189 = Integer.Sparse.mergeBy masterLess reducedTerm1197 reducedTerm1198 := by decide +kernel

theorem reducedMerge1190Check : reducedMerge1190 = Integer.Sparse.mergeBy masterLess reducedMerge1188 reducedMerge1189 := by decide +kernel

theorem reducedMerge1191Check : reducedMerge1191 = Integer.Sparse.mergeBy masterLess reducedMerge1187 reducedMerge1190 := by decide +kernel

theorem reducedMerge1192Check : reducedMerge1192 = Integer.Sparse.mergeBy masterLess reducedMerge1184 reducedMerge1191 := by decide +kernel

theorem reducedMerge1193Check : reducedMerge1193 = Integer.Sparse.mergeBy masterLess reducedMerge1178 reducedMerge1192 := by decide +kernel

theorem reducedMerge1194Check : reducedMerge1194 = Integer.Sparse.mergeBy masterLess reducedMerge1164 reducedMerge1193 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1139 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1139 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1139 (originalVector B) := by
  rw [reducedTermArithmetic1139, ← sound2964 B hB hF]
  change (-12088519805730816000000 : ℝ) * mixedMoment B node2964 node2964Labels =
    (37623398400 : ℝ) * (((-321303240000 : ℤ) : ℝ) * mixedMoment B node2964 node2964Labels + 0)
  ring

theorem reducedTermEval1140 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1140 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1140 (originalVector B) := by
  rw [reducedTermArithmetic1140, ← sound2967 B hB hF]
  change (-15967457567244288000000 : ℝ) * mixedMoment B node2967 node2967Labels =
    (37623398400 : ℝ) * (((-424402320000 : ℤ) : ℝ) * mixedMoment B node2967 node2967Labels + 0)
  ring

theorem reducedTermEval1141 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1141 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1141 (originalVector B) := by
  rw [reducedTermArithmetic1141, ← sound2979 B hB hF]
  change (-421979070165811200000 : ℝ) * mixedMoment B node2979 node2979Labels =
    (37623398400 : ℝ) * (((-11215868000 : ℤ) : ℝ) * mixedMoment B node2979 node2979Labels + 0)
  ring

theorem reducedTermEval1142 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1142 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1142 (originalVector B) := by
  rw [reducedTermArithmetic1142, ← sound2981 B hB hF]
  change (669848715789926400000 : ℝ) * mixedMoment B node2981 node2981Labels =
    (37623398400 : ℝ) * ((17804046000 : ℝ) * mixedMoment B node2981 node2981Labels + 0)
  ring

theorem reducedTermEval1143 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1143 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1143 (originalVector B) := by
  rw [reducedTermArithmetic1143, ← sound2984 B hB hF]
  change (15200456282416742400000 : ℝ) * mixedMoment B node2984 node2984Labels =
    (37623398400 : ℝ) * ((404016036000 : ℝ) * mixedMoment B node2984 node2984Labels + 0)
  ring

theorem reducedTermEval1144 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1144 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1144 (originalVector B) := by
  rw [reducedTermArithmetic1144, ← sound3016 B hB hF]
  change (-4525925648641818624000 : ℝ) * mixedMoment B node3016 node3016Labels =
    (37623398400 : ℝ) * (((-120295503360 : ℤ) : ℝ) * mixedMoment B node3016 node3016Labels + 0)
  ring

theorem reducedTermEval1145 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1145 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1145 (originalVector B) := by
  rw [reducedTermArithmetic1145, ← sound3023 B hB hF]
  change (-5814069266409062400000 : ℝ) * mixedMoment B node3023 node3023Labels =
    (37623398400 : ℝ) * (((-154533336000 : ℤ) : ℝ) * mixedMoment B node3023 node3023Labels + 0)
  ring

theorem reducedTermEval1146 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1146 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1146 (originalVector B) := by
  rw [reducedTermArithmetic1146, ← sound3024 B hB hF]
  change (1699294017721466880000 : ℝ) * mixedMoment B node3024 node3024Labels =
    (37623398400 : ℝ) * ((45165883200 : ℝ) * mixedMoment B node3024 node3024Labels + 0)
  ring

theorem reducedTermEval1147 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1147 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1147 (originalVector B) := by
  rw [reducedTermArithmetic1147, ← sound3025 B hB hF]
  change (-3657804786659229696000 : ℝ) * mixedMoment B node3025 node3025Labels =
    (37623398400 : ℝ) * (((-97221541440 : ℤ) : ℝ) * mixedMoment B node3025 node3025Labels + 0)
  ring

theorem reducedTermEval1148 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1148 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1148 (originalVector B) := by
  rw [reducedTermArithmetic1148, ← sound3029 B hB hF]
  change (-12883500708986880000000 : ℝ) * mixedMoment B node3029 node3029Labels =
    (37623398400 : ℝ) * (((-342433200000 : ℤ) : ℝ) * mixedMoment B node3029 node3029Labels + 0)
  ring

theorem reducedTermEval1149 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1149 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1149 (originalVector B) := by
  rw [reducedTermArithmetic1149, ← sound3030 B hB hF]
  change (-4222719607976755200000 : ℝ) * mixedMoment B node3030 node3030Labels =
    (37623398400 : ℝ) * (((-112236528000 : ℤ) : ℝ) * mixedMoment B node3030 node3030Labels + 0)
  ring

theorem reducedTermEval1150 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1150 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1150 (originalVector B) := by
  rw [reducedTermArithmetic1150, ← sound3031 B hB hF]
  change (4597326756229939200000 : ℝ) * mixedMoment B node3031 node3031Labels =
    (37623398400 : ℝ) * ((122193288000 : ℝ) * mixedMoment B node3031 node3031Labels + 0)
  ring

theorem reducedTermEval1151 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1151 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1151 (originalVector B) := by
  rw [reducedTermArithmetic1151, ← sound3032 B hB hF]
  change (2216831132152627200000 : ℝ) * mixedMoment B node3032 node3032Labels =
    (37623398400 : ℝ) * ((58921608000 : ℝ) * mixedMoment B node3032 node3032Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1152 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1152 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1152 (originalVector B) := by
  rw [reducedTermArithmetic1152, ← sound3033 B hB hF]
  change (-4250125755517501440000 : ℝ) * mixedMoment B node3033 node3033Labels =
    (37623398400 : ℝ) * (((-112964961600 : ℤ) : ℝ) * mixedMoment B node3033 node3033Labels + 0)
  ring

theorem reducedTermEval1153 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1153 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1153 (originalVector B) := by
  rw [reducedTermArithmetic1153, ← sound3036 B hB hF]
  change (3735836684119572480000 : ℝ) * mixedMoment B node3036 node3036Labels =
    (37623398400 : ℝ) * ((99295567200 : ℝ) * mixedMoment B node3036 node3036Labels + 0)
  ring

theorem reducedTermEval1154 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1154 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1154 (originalVector B) := by
  rw [reducedTermArithmetic1154, ← sound3037 B hB hF]
  change (-12943331682486976512000 : ℝ) * mixedMoment B node3037 node3037Labels =
    (37623398400 : ℝ) * (((-344023459680 : ℤ) : ℝ) * mixedMoment B node3037 node3037Labels + 0)
  ring

theorem reducedTermEval1155 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1155 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1155 (originalVector B) := by
  rw [reducedTermArithmetic1155, ← sound3038 B hB hF]
  change (14492549870804533248000 : ℝ) * mixedMoment B node3038 node3038Labels =
    (37623398400 : ℝ) * ((385200446720 : ℝ) * mixedMoment B node3038 node3038Labels + 0)
  ring

theorem reducedTermEval1156 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1156 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1156 (originalVector B) := by
  rw [reducedTermArithmetic1156, ← sound3039 B hB hF]
  change (9313996009718808576000 : ℝ) * mixedMoment B node3039 node3039Labels =
    (37623398400 : ℝ) * ((247558604640 : ℝ) * mixedMoment B node3039 node3039Labels + 0)
  ring

theorem reducedTermEval1157 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1157 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1157 (originalVector B) := by
  rw [reducedTermArithmetic1157, ← sound3040 B hB hF]
  change (919241958555648000000 : ℝ) * mixedMoment B node3040 node3040Labels =
    (37623398400 : ℝ) * ((24432720000 : ℝ) * mixedMoment B node3040 node3040Labels + 0)
  ring

theorem reducedTermEval1158 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1158 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1158 (originalVector B) := by
  rw [reducedTermArithmetic1158, ← sound3043 B hB hF]
  change (-2589617639009157120000 : ℝ) * mixedMoment B node3043 node3043Labels =
    (37623398400 : ℝ) * (((-68829976800 : ℤ) : ℝ) * mixedMoment B node3043 node3043Labels + 0)
  ring

theorem reducedTermEval1159 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1159 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1159 (originalVector B) := by
  rw [reducedTermArithmetic1159, ← sound3044 B hB hF]
  change (-16300334708112752640000 : ℝ) * mixedMoment B node3044 node3044Labels =
    (37623398400 : ℝ) * (((-433249929600 : ℤ) : ℝ) * mixedMoment B node3044 node3044Labels + 0)
  ring

theorem reducedTermEval1160 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1160 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1160 (originalVector B) := by
  rw [reducedTermArithmetic1160, ← sound3045 B hB hF]
  change (4564186441588408320000 : ℝ) * mixedMoment B node3045 node3045Labels =
    (37623398400 : ℝ) * ((121312444800 : ℝ) * mixedMoment B node3045 node3045Labels + 0)
  ring

theorem reducedTermEval1161 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1161 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1161 (originalVector B) := by
  rw [reducedTermArithmetic1161, ← sound3046 B hB hF]
  change (3365072991753338880000 : ℝ) * mixedMoment B node3046 node3046Labels =
    (37623398400 : ℝ) * ((89440963200 : ℝ) * mixedMoment B node3046 node3046Labels + 0)
  ring

theorem reducedTermEval1162 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1162 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1162 (originalVector B) := by
  rw [reducedTermArithmetic1162, ← sound3050 B hB hF]
  change (-4404201698619555840000 : ℝ) * mixedMoment B node3050 node3050Labels =
    (37623398400 : ℝ) * (((-117060177600 : ℤ) : ℝ) * mixedMoment B node3050 node3050Labels + 0)
  ring

theorem reducedTermEval1163 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1163 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1163 (originalVector B) := by
  rw [reducedTermArithmetic1163, ← sound3051 B hB hF]
  change (3906032471591878656000 : ℝ) * mixedMoment B node3051 node3051Labels =
    (37623398400 : ℝ) * ((103819235840 : ℝ) * mixedMoment B node3051 node3051Labels + 0)
  ring

theorem reducedTermEval1164 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1164 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1164 (originalVector B) := by
  rw [reducedTermArithmetic1164, ← sound3052 B hB hF]
  change (7967955760767959040000 : ℝ) * mixedMoment B node3052 node3052Labels =
    (37623398400 : ℝ) * ((211781925600 : ℝ) * mixedMoment B node3052 node3052Labels + 0)
  ring

theorem reducedTermEval1165 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1165 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1165 (originalVector B) := by
  rw [reducedTermArithmetic1165, ← sound3053 B hB hF]
  change (-4769146164905902080000 : ℝ) * mixedMoment B node3053 node3053Labels =
    (37623398400 : ℝ) * (((-126760111200 : ℤ) : ℝ) * mixedMoment B node3053 node3053Labels + 0)
  ring

theorem reducedTermEval1166 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1166 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1166 (originalVector B) := by
  rw [reducedTermArithmetic1166, ← sound3054 B hB hF]
  change (-6384294458848051200000 : ℝ) * mixedMoment B node3054 node3054Labels =
    (37623398400 : ℝ) * (((-169689468000 : ℤ) : ℝ) * mixedMoment B node3054 node3054Labels + 0)
  ring

theorem reducedTermEval1167 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1167 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1167 (originalVector B) := by
  rw [reducedTermArithmetic1167, ← sound3055 B hB hF]
  change (16753008632221532160000 : ℝ) * mixedMoment B node3055 node3055Labels =
    (37623398400 : ℝ) * ((445281642400 : ℝ) * mixedMoment B node3055 node3055Labels + 0)
  ring

theorem reducedTermEval1168 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1168 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1168 (originalVector B) := by
  rw [reducedTermArithmetic1168, ← sound3056 B hB hF]
  change (-4052239562185113600000 : ℝ) * mixedMoment B node3056 node3056Labels =
    (37623398400 : ℝ) * (((-107705304000 : ℤ) : ℝ) * mixedMoment B node3056 node3056Labels + 0)
  ring

theorem reducedTermEval1169 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1169 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1169 (originalVector B) := by
  rw [reducedTermArithmetic1169, ← sound3058 B hB hF]
  change (259351328607436800000 : ℝ) * mixedMoment B node3058 node3058Labels =
    (37623398400 : ℝ) * ((6893352000 : ℝ) * mixedMoment B node3058 node3058Labels + 0)
  ring

theorem reducedTermEval1170 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1170 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1170 (originalVector B) := by
  rw [reducedTermArithmetic1170, ← sound3059 B hB hF]
  change (-1852188959337873408000 : ℝ) * mixedMoment B node3059 node3059Labels =
    (37623398400 : ℝ) * (((-49229709120 : ℤ) : ℝ) * mixedMoment B node3059 node3059Labels + 0)
  ring

theorem reducedTermEval1171 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1171 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1171 (originalVector B) := by
  rw [reducedTermArithmetic1171, ← sound3062 B hB hF]
  change (-4597326756229939200000 : ℝ) * mixedMoment B node3062 node3062Labels =
    (37623398400 : ℝ) * (((-122193288000 : ℤ) : ℝ) * mixedMoment B node3062 node3062Labels + 0)
  ring

theorem reducedTermEval1172 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1172 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1172 (originalVector B) := by
  rw [reducedTermArithmetic1172, ← sound3064 B hB hF]
  change (7350751094580117504000 : ℝ) * mixedMoment B node3064 node3064Labels =
    (37623398400 : ℝ) * ((195377116560 : ℝ) * mixedMoment B node3064 node3064Labels + 0)
  ring

theorem reducedTermEval1173 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1173 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1173 (originalVector B) := by
  rw [reducedTermArithmetic1173, ← sound3065 B hB hF]
  change (2108824540752642048000 : ℝ) * mixedMoment B node3065 node3065Labels =
    (37623398400 : ℝ) * ((56050878720 : ℝ) * mixedMoment B node3065 node3065Labels + 0)
  ring

theorem reducedTermEval1174 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1174 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1174 (originalVector B) := by
  rw [reducedTermArithmetic1174, ← sound3066 B hB hF]
  change (-5639933671031439360000 : ℝ) * mixedMoment B node3066 node3066Labels =
    (37623398400 : ℝ) * (((-149904950400 : ℤ) : ℝ) * mixedMoment B node3066 node3066Labels + 0)
  ring

theorem reducedTermEval1175 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1175 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1175 (originalVector B) := by
  rw [reducedTermArithmetic1175, ← sound3068 B hB hF]
  change (-8048462097973248000000 : ℝ) * mixedMoment B node3068 node3068Labels =
    (37623398400 : ℝ) * (((-213921720000 : ℤ) : ℝ) * mixedMoment B node3068 node3068Labels + 0)
  ring

theorem reducedTermEval1176 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1176 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1176 (originalVector B) := by
  rw [reducedTermArithmetic1176, ← sound3069 B hB hF]
  change (1668709084299264000000 : ℝ) * mixedMoment B node3069 node3069Labels =
    (37623398400 : ℝ) * ((44352960000 : ℝ) * mixedMoment B node3069 node3069Labels + 0)
  ring

theorem reducedTermEval1177 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1177 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1177 (originalVector B) := by
  rw [reducedTermArithmetic1177, ← sound3073 B hB hF]
  change (4020809998518190080000 : ℝ) * mixedMoment B node3073 node3073Labels =
    (37623398400 : ℝ) * ((106869931200 : ℝ) * mixedMoment B node3073 node3073Labels + 0)
  ring

theorem reducedTermEval1178 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1178 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1178 (originalVector B) := by
  rw [reducedTermArithmetic1178, ← sound3074 B hB hF]
  change (15546685904170057728000 : ℝ) * mixedMoment B node3074 node3074Labels =
    (37623398400 : ℝ) * ((413218543920 : ℝ) * mixedMoment B node3074 node3074Labels + 0)
  ring

theorem reducedTermEval1179 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1179 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1179 (originalVector B) := by
  rw [reducedTermArithmetic1179, ← sound3075 B hB hF]
  change (-1716666600863563776000 : ℝ) * mixedMoment B node3075 node3075Labels =
    (37623398400 : ℝ) * (((-45627632640 : ℤ) : ℝ) * mixedMoment B node3075 node3075Labels + 0)
  ring

theorem reducedTermEval1180 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1180 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1180 (originalVector B) := by
  rw [reducedTermArithmetic1180, ← sound3077 B hB hF]
  change (-16333431861191639040000 : ℝ) * mixedMoment B node3077 node3077Labels =
    (37623398400 : ℝ) * (((-434129625600 : ℤ) : ℝ) * mixedMoment B node3077 node3077Labels + 0)
  ring

theorem reducedTermEval1181 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1181 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1181 (originalVector B) := by
  rw [reducedTermArithmetic1181, ← sound3078 B hB hF]
  change (18561918376033320960000 : ℝ) * mixedMoment B node3078 node3078Labels =
    (37623398400 : ℝ) * ((493361024400 : ℝ) * mixedMoment B node3078 node3078Labels + 0)
  ring

theorem reducedTermEval1182 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1182 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1182 (originalVector B) := by
  rw [reducedTermArithmetic1182, ← sound3079 B hB hF]
  change (-12298111992747786240000 : ℝ) * mixedMoment B node3079 node3079Labels =
    (37623398400 : ℝ) * (((-326874033600 : ℤ) : ℝ) * mixedMoment B node3079 node3079Labels + 0)
  ring

theorem reducedTermEval1183 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1183 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1183 (originalVector B) := by
  rw [reducedTermArithmetic1183, ← sound3083 B hB hF]
  change (-1415934024744960000000 : ℝ) * mixedMoment B node3083 node3083Labels =
    (37623398400 : ℝ) * (((-37634400000 : ℤ) : ℝ) * mixedMoment B node3083 node3083Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1136 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1136 (originalVector B) := by
  rw [reducedMerge1136Check, Integer.Sparse.eval_mergeBy, reducedTermEval1140 B hB hF, reducedTermEval1141 B hB hF]
  rw [originalMerge1136, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1137 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1137 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1137 (originalVector B) := by
  rw [reducedMerge1137Check, Integer.Sparse.eval_mergeBy, reducedTermEval1139 B hB hF, reducedMergeEval1136 B hB hF]
  rw [originalMerge1137, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1138 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1138 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1138 (originalVector B) := by
  rw [reducedMerge1138Check, Integer.Sparse.eval_mergeBy, reducedTermEval1142 B hB hF, reducedTermEval1143 B hB hF]
  rw [originalMerge1138, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1139 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1139 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1139 (originalVector B) := by
  rw [reducedMerge1139Check, Integer.Sparse.eval_mergeBy, reducedTermEval1144 B hB hF, reducedTermEval1145 B hB hF]
  rw [originalMerge1139, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1140 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1140 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1140 (originalVector B) := by
  rw [reducedMerge1140Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1138 B hB hF, reducedMergeEval1139 B hB hF]
  rw [originalMerge1140, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1141 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1141 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1141 (originalVector B) := by
  rw [reducedMerge1141Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1137 B hB hF, reducedMergeEval1140 B hB hF]
  rw [originalMerge1141, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1142 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1142 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1142 (originalVector B) := by
  rw [reducedMerge1142Check, Integer.Sparse.eval_mergeBy, reducedTermEval1146 B hB hF, reducedTermEval1147 B hB hF]
  rw [originalMerge1142, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1143 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1143 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1143 (originalVector B) := by
  rw [reducedMerge1143Check, Integer.Sparse.eval_mergeBy, reducedTermEval1148 B hB hF, reducedTermEval1149 B hB hF]
  rw [originalMerge1143, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1144 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1144 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1144 (originalVector B) := by
  rw [reducedMerge1144Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1142 B hB hF, reducedMergeEval1143 B hB hF]
  rw [originalMerge1144, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1145 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1145 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1145 (originalVector B) := by
  rw [reducedMerge1145Check, Integer.Sparse.eval_mergeBy, reducedTermEval1150 B hB hF, reducedTermEval1151 B hB hF]
  rw [originalMerge1145, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1146 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1146 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1146 (originalVector B) := by
  rw [reducedMerge1146Check, Integer.Sparse.eval_mergeBy, reducedTermEval1152 B hB hF, reducedTermEval1153 B hB hF]
  rw [originalMerge1146, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1147 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1147 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1147 (originalVector B) := by
  rw [reducedMerge1147Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1145 B hB hF, reducedMergeEval1146 B hB hF]
  rw [originalMerge1147, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1148 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1148 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1148 (originalVector B) := by
  rw [reducedMerge1148Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1144 B hB hF, reducedMergeEval1147 B hB hF]
  rw [originalMerge1148, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1149 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1149 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1149 (originalVector B) := by
  rw [reducedMerge1149Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1141 B hB hF, reducedMergeEval1148 B hB hF]
  rw [originalMerge1149, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1150 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1150 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1150 (originalVector B) := by
  rw [reducedMerge1150Check, Integer.Sparse.eval_mergeBy, reducedTermEval1155 B hB hF, reducedTermEval1156 B hB hF]
  rw [originalMerge1150, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1151 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1151 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1151 (originalVector B) := by
  rw [reducedMerge1151Check, Integer.Sparse.eval_mergeBy, reducedTermEval1154 B hB hF, reducedMergeEval1150 B hB hF]
  rw [originalMerge1151, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1184 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1184 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1184 (originalVector B) := by
  rw [reducedTermArithmetic1184, ← sound3084 B hB hF]
  change (-50941984034146222080000 : ℝ) * mixedMoment B node3084 node3084Labels =
    (37623398400 : ℝ) * (((-1353997411200 : ℤ) : ℝ) * mixedMoment B node3084 node3084Labels + 0)
  ring

theorem reducedTermEval1185 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1185 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1185 (originalVector B) := by
  rw [reducedTermArithmetic1185, ← sound3085 B hB hF]
  change (-5020201290366517248000 : ℝ) * mixedMoment B node3085 node3085Labels =
    (37623398400 : ℝ) * (((-133432956720 : ℤ) : ℝ) * mixedMoment B node3085 node3085Labels + 0)
  ring

theorem reducedTermEval1186 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1186 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1186 (originalVector B) := by
  rw [reducedTermArithmetic1186, ← sound3086 B hB hF]
  change (-22351245374360125440000 : ℝ) * mixedMoment B node3086 node3086Labels =
    (37623398400 : ℝ) * (((-594078321600 : ℤ) : ℝ) * mixedMoment B node3086 node3086Labels + 0)
  ring

theorem reducedTermEval1187 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1187 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1187 (originalVector B) := by
  rw [reducedTermArithmetic1187, ← sound3087_e B hB hF]
  change (-3811256349900668928000 : ℝ) * mixedMoment B node3087 node3087Labels =
    (37623398400 : ℝ) * (((-101300161920 : ℤ) : ℝ) * mixedMoment B node3087 node3087Labels + 0)
  ring

theorem reducedTermEval1188 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1188 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1188 (originalVector B) := by
  rw [reducedTermArithmetic1188, ← sound3088_e B hB hF]
  change (-1418854997041348608000 : ℝ) * mixedMoment B node3088 node3088Labels =
    (37623398400 : ℝ) * (((-37712037120 : ℤ) : ℝ) * mixedMoment B node3088 node3088Labels + 0)
  ring

theorem reducedTermEval1189 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1189 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1189 (originalVector B) := by
  rw [reducedTermArithmetic1189, ← sound3089_e B hB hF]
  change (-5665773180262809600000 : ℝ) * mixedMoment B node3089 node3089Labels =
    (37623398400 : ℝ) * (((-150591744000 : ℤ) : ℝ) * mixedMoment B node3089 node3089Labels + 0)
  ring

theorem reducedTermEval1190 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1190 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1190 (originalVector B) := by
  rw [reducedTermArithmetic1190, ← sound3092 B hB hF]
  change (-3891082594516992000000 : ℝ) * mixedMoment B node3092 node3092Labels =
    (37623398400 : ℝ) * (((-103421880000 : ℤ) : ℝ) * mixedMoment B node3092 node3092Labels + 0)
  ring

theorem reducedTermEval1191 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1191 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1191 (originalVector B) := by
  rw [reducedTermArithmetic1191, ← sound3096 B hB hF]
  change (-10769461456860610560000 : ℝ) * mixedMoment B node3096 node3096Labels =
    (37623398400 : ℝ) * (((-286243718400 : ℤ) : ℝ) * mixedMoment B node3096 node3096Labels + 0)
  ring

theorem reducedTermEval1192 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1192 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1192 (originalVector B) := by
  rw [reducedTermArithmetic1192, ← sound3097 B hB hF]
  change (23327342262493839360000 : ℝ) * mixedMoment B node3097 node3097Labels =
    (37623398400 : ℝ) * ((620022200400 : ℝ) * mixedMoment B node3097 node3097Labels + 0)
  ring

theorem reducedTermEval1193 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1193 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1193 (originalVector B) := by
  rw [reducedTermArithmetic1193, ← sound3098 B hB hF]
  change (34405213211462467584000 : ℝ) * mixedMoment B node3098 node3098Labels =
    (37623398400 : ℝ) * ((914463197760 : ℝ) * mixedMoment B node3098 node3098Labels + 0)
  ring

theorem reducedTermEval1194 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1194 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1194 (originalVector B) := by
  rw [reducedTermArithmetic1194, ← sound3099 B hB hF]
  change (-9468178881528987648000 : ℝ) * mixedMoment B node3099 node3099Labels =
    (37623398400 : ℝ) * (((-251656662720 : ℤ) : ℝ) * mixedMoment B node3099 node3099Labels + 0)
  ring

theorem reducedTermEval1195 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1195 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1195 (originalVector B) := by
  rw [reducedTermArithmetic1195, ← sound3103 B hB hF]
  change (-2736289857142259712000 : ℝ) * mixedMoment B node3103 node3103Labels =
    (37623398400 : ℝ) * (((-72728407680 : ℤ) : ℝ) * mixedMoment B node3103 node3103Labels + 0)
  ring

theorem reducedTermEval1196 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1196 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1196 (originalVector B) := by
  rw [reducedTermArithmetic1196, ← sound3108 B hB hF]
  change (12622627890148147200000 : ℝ) * mixedMoment B node3108 node3108Labels =
    (37623398400 : ℝ) * ((335499408000 : ℝ) * mixedMoment B node3108 node3108Labels + 0)
  ring

theorem reducedTermEval1197 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1197 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1197 (originalVector B) := by
  rw [reducedTermArithmetic1197, ← sound3109_e B hB hF]
  change (9991713240911904768000 : ℝ) * mixedMoment B node3109 node3109Labels =
    (37623398400 : ℝ) * ((265571789520 : ℝ) * mixedMoment B node3109 node3109Labels + 0)
  ring

theorem reducedTermEval1198 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1198 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1198 (originalVector B) := by
  rw [reducedTermArithmetic1198, ← sound3110 B hB hF]
  change (2131060763813216256000 : ℝ) * mixedMoment B node3110 node3110Labels =
    (37623398400 : ℝ) * ((56641899840 : ℝ) * mixedMoment B node3110 node3110Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1152 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1152 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1152 (originalVector B) := by
  rw [reducedMerge1152Check, Integer.Sparse.eval_mergeBy, reducedTermEval1157 B hB hF, reducedTermEval1158 B hB hF]
  rw [originalMerge1152, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1153 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1153 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1153 (originalVector B) := by
  rw [reducedMerge1153Check, Integer.Sparse.eval_mergeBy, reducedTermEval1159 B hB hF, reducedTermEval1160 B hB hF]
  rw [originalMerge1153, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1154 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1154 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1154 (originalVector B) := by
  rw [reducedMerge1154Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1152 B hB hF, reducedMergeEval1153 B hB hF]
  rw [originalMerge1154, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1155 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1155 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1155 (originalVector B) := by
  rw [reducedMerge1155Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1151 B hB hF, reducedMergeEval1154 B hB hF]
  rw [originalMerge1155, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1156 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1156 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1156 (originalVector B) := by
  rw [reducedMerge1156Check, Integer.Sparse.eval_mergeBy, reducedTermEval1161 B hB hF, reducedTermEval1162 B hB hF]
  rw [originalMerge1156, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1157 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1157 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1157 (originalVector B) := by
  rw [reducedMerge1157Check, Integer.Sparse.eval_mergeBy, reducedTermEval1163 B hB hF, reducedTermEval1164 B hB hF]
  rw [originalMerge1157, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1158 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1158 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1158 (originalVector B) := by
  rw [reducedMerge1158Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1156 B hB hF, reducedMergeEval1157 B hB hF]
  rw [originalMerge1158, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1159 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1159 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1159 (originalVector B) := by
  rw [reducedMerge1159Check, Integer.Sparse.eval_mergeBy, reducedTermEval1165 B hB hF, reducedTermEval1166 B hB hF]
  rw [originalMerge1159, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1160 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1160 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1160 (originalVector B) := by
  rw [reducedMerge1160Check, Integer.Sparse.eval_mergeBy, reducedTermEval1167 B hB hF, reducedTermEval1168 B hB hF]
  rw [originalMerge1160, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1161 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1161 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1161 (originalVector B) := by
  rw [reducedMerge1161Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1159 B hB hF, reducedMergeEval1160 B hB hF]
  rw [originalMerge1161, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1162 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1162 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1162 (originalVector B) := by
  rw [reducedMerge1162Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1158 B hB hF, reducedMergeEval1161 B hB hF]
  rw [originalMerge1162, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1163 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1163 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1163 (originalVector B) := by
  rw [reducedMerge1163Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1155 B hB hF, reducedMergeEval1162 B hB hF]
  rw [originalMerge1163, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1164 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1164 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1164 (originalVector B) := by
  rw [reducedMerge1164Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1149 B hB hF, reducedMergeEval1163 B hB hF]
  rw [originalMerge1164, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1165 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1165 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1165 (originalVector B) := by
  rw [reducedMerge1165Check, Integer.Sparse.eval_mergeBy, reducedTermEval1170 B hB hF, reducedTermEval1171 B hB hF]
  rw [originalMerge1165, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1166 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1166 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1166 (originalVector B) := by
  rw [reducedMerge1166Check, Integer.Sparse.eval_mergeBy, reducedTermEval1169 B hB hF, reducedMergeEval1165 B hB hF]
  rw [originalMerge1166, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1167 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1167 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1167 (originalVector B) := by
  rw [reducedMerge1167Check, Integer.Sparse.eval_mergeBy, reducedTermEval1172 B hB hF, reducedTermEval1173 B hB hF]
  rw [originalMerge1167, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1168 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1168 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1168 (originalVector B) := by
  rw [reducedMerge1168Check, Integer.Sparse.eval_mergeBy, reducedTermEval1174 B hB hF, reducedTermEval1175 B hB hF]
  rw [originalMerge1168, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1169 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1169 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1169 (originalVector B) := by
  rw [reducedMerge1169Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1167 B hB hF, reducedMergeEval1168 B hB hF]
  rw [originalMerge1169, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1170 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1170 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1170 (originalVector B) := by
  rw [reducedMerge1170Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1166 B hB hF, reducedMergeEval1169 B hB hF]
  rw [originalMerge1170, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1171 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1171 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1171 (originalVector B) := by
  rw [reducedMerge1171Check, Integer.Sparse.eval_mergeBy, reducedTermEval1176 B hB hF, reducedTermEval1177 B hB hF]
  rw [originalMerge1171, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1172 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1172 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1172 (originalVector B) := by
  rw [reducedMerge1172Check, Integer.Sparse.eval_mergeBy, reducedTermEval1178 B hB hF, reducedTermEval1179 B hB hF]
  rw [originalMerge1172, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1173 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1173 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1173 (originalVector B) := by
  rw [reducedMerge1173Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1171 B hB hF, reducedMergeEval1172 B hB hF]
  rw [originalMerge1173, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1174 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1174 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1174 (originalVector B) := by
  rw [reducedMerge1174Check, Integer.Sparse.eval_mergeBy, reducedTermEval1180 B hB hF, reducedTermEval1181 B hB hF]
  rw [originalMerge1174, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1175 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1175 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1175 (originalVector B) := by
  rw [reducedMerge1175Check, Integer.Sparse.eval_mergeBy, reducedTermEval1182 B hB hF, reducedTermEval1183 B hB hF]
  rw [originalMerge1175, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1176 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1176 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1176 (originalVector B) := by
  rw [reducedMerge1176Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1174 B hB hF, reducedMergeEval1175 B hB hF]
  rw [originalMerge1176, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1177 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1177 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1177 (originalVector B) := by
  rw [reducedMerge1177Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1173 B hB hF, reducedMergeEval1176 B hB hF]
  rw [originalMerge1177, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1178 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1178 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1178 (originalVector B) := by
  rw [reducedMerge1178Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1170 B hB hF, reducedMergeEval1177 B hB hF]
  rw [originalMerge1178, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1179 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1179 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1179 (originalVector B) := by
  rw [reducedMerge1179Check, Integer.Sparse.eval_mergeBy, reducedTermEval1185 B hB hF, reducedTermEval1186 B hB hF]
  rw [originalMerge1179, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1180 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1180 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1180 (originalVector B) := by
  rw [reducedMerge1180Check, Integer.Sparse.eval_mergeBy, reducedTermEval1184 B hB hF, reducedMergeEval1179 B hB hF]
  rw [originalMerge1180, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1181 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1181 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1181 (originalVector B) := by
  rw [reducedMerge1181Check, Integer.Sparse.eval_mergeBy, reducedTermEval1187 B hB hF, reducedTermEval1188 B hB hF]
  rw [originalMerge1181, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1182 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1182 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1182 (originalVector B) := by
  rw [reducedMerge1182Check, Integer.Sparse.eval_mergeBy, reducedTermEval1189 B hB hF, reducedTermEval1190 B hB hF]
  rw [originalMerge1182, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1183 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1183 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1183 (originalVector B) := by
  rw [reducedMerge1183Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1181 B hB hF, reducedMergeEval1182 B hB hF]
  rw [originalMerge1183, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1184 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1184 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1184 (originalVector B) := by
  rw [reducedMerge1184Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1180 B hB hF, reducedMergeEval1183 B hB hF]
  rw [originalMerge1184, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1185 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1185 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1185 (originalVector B) := by
  rw [reducedMerge1185Check, Integer.Sparse.eval_mergeBy, reducedTermEval1191 B hB hF, reducedTermEval1192 B hB hF]
  rw [originalMerge1185, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1186 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1186 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1186 (originalVector B) := by
  rw [reducedMerge1186Check, Integer.Sparse.eval_mergeBy, reducedTermEval1193 B hB hF, reducedTermEval1194 B hB hF]
  rw [originalMerge1186, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1187 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1187 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1187 (originalVector B) := by
  rw [reducedMerge1187Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1185 B hB hF, reducedMergeEval1186 B hB hF]
  rw [originalMerge1187, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1188 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1188 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1188 (originalVector B) := by
  rw [reducedMerge1188Check, Integer.Sparse.eval_mergeBy, reducedTermEval1195 B hB hF, reducedTermEval1196 B hB hF]
  rw [originalMerge1188, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1189 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1189 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1189 (originalVector B) := by
  rw [reducedMerge1189Check, Integer.Sparse.eval_mergeBy, reducedTermEval1197 B hB hF, reducedTermEval1198 B hB hF]
  rw [originalMerge1189, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1190 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1190 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1190 (originalVector B) := by
  rw [reducedMerge1190Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1188 B hB hF, reducedMergeEval1189 B hB hF]
  rw [originalMerge1190, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1191 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1191 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1191 (originalVector B) := by
  rw [reducedMerge1191Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1187 B hB hF, reducedMergeEval1190 B hB hF]
  rw [originalMerge1191, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1192 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1192 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1192 (originalVector B) := by
  rw [reducedMerge1192Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1184 B hB hF, reducedMergeEval1191 B hB hF]
  rw [originalMerge1192, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1193 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1193 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1193 (originalVector B) := by
  rw [reducedMerge1193Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1178 B hB hF, reducedMergeEval1192 B hB hF]
  rw [originalMerge1193, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1194_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1194 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1194 (originalVector B) := by
  rw [reducedMerge1194Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1164 B hB hF, reducedMergeEval1193 B hB hF]
  rw [originalMerge1194, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e_oai
