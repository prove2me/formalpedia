-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:20:18.376193+00:00
-- url     : https://prove2.me/submissions/05a68876-fdf6-4c27-911a-173f519fe27e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E115
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3223_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3226_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3227_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_reducedMergeEval1225_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw472 raw472Labels = mixedMoment B node3224 node3224Labels := by
  calc
    mixedMoment B raw472 raw472Labels = mixedMoment B raw472step0 raw472step0Labels := by
      have ha : raw472step0 = (fun i j => raw472 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw472step0 raw472; decide +kernel
      have hl : raw472step0Labels = raw472Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw472 raw472Labels permutation8 permutation5
    mixedMoment B raw472step0 raw472step0Labels = mixedMoment B raw472step1 raw472step1Labels := by
      have ha : raw472step1 = raw472step0 := by apply Matrix.ext; unfold raw472step1 raw472step0; decide +kernel
      have hl : raw472step0Labels = labelEmbedding1 ∘ raw472step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw472step0 raw472step0Labels raw472step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3224 node3224Labels := by rfl

theorem canonical473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw473 raw473Labels = mixedMoment B node269 node269Labels := by
  calc
    mixedMoment B raw473 raw473Labels = mixedMoment B raw473step0 raw473step0Labels := by
      have ha : raw473step0 = (fun i j => raw473 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw473step0 raw473; decide +kernel
      have hl : raw473step0Labels = raw473Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw473 raw473Labels permutation8 permutation4
    _ = mixedMoment B node269 node269Labels := by rfl

theorem canonical474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw474 raw474Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw474 raw474Labels = mixedMoment B raw474step0 raw474step0Labels := by
      have ha : raw474step0 = (fun i j => raw474 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw474step0 raw474; decide +kernel
      have hl : raw474step0Labels = raw474Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw474 raw474Labels permutation8 permutation5
    mixedMoment B raw474step0 raw474step0Labels = mixedMoment B raw474step1 raw474step1Labels := by
      have ha : raw474step1 = raw474step0 := by apply Matrix.ext; unfold raw474step1 raw474step0; decide +kernel
      have hl : raw474step0Labels = labelEmbedding1 ∘ raw474step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw474step0 raw474step0Labels raw474step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3225 node3225Labels := by rfl

theorem canonical475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw475 raw475Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw475 raw475Labels = mixedMoment B raw475step0 raw475step0Labels := by
      have ha : raw475step0 = (fun i j => raw475 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw475step0 raw475; decide +kernel
      have hl : raw475step0Labels = raw475Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw475 raw475Labels permutation11 permutation6
    mixedMoment B raw475step0 raw475step0Labels = mixedMoment B raw475step1 raw475step1Labels := by
      have ha : raw475step1 = -raw475step0 := by apply Matrix.ext; change ∀ i j, raw475step1 i j = -(raw475step0 i j); unfold raw475step1 raw475step0; decide +kernel
      have hl : raw475step1Labels = raw475step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node268 node268Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical538 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw538 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw538 = injectiveMoment H raw538step0 := by
      have heq : raw538step0 = (fun i j => raw538 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw538 permutation28 permutation6
    _ = injectiveMoment H node215 := by rfl

end MUB6.Certificate.PairSemantics

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

theorem canonical553 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw553 = injectiveMoment H node204 := by
  calc
    injectiveMoment H raw553 = injectiveMoment H raw553step0 := by
      have heq : raw553step0 = (fun i j => raw553 (permutation31 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw553 permutation31 permutation6
    _ = injectiveMoment H node204 := by rfl

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

theorem canonical918 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw918 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw918 = injectiveMoment H raw918step0 := by
      have hz : ∀ j, raw918 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw918step0 = (fun i j => raw918 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw918 permutation27 hz
    _ = injectiveMoment H node10 := by rfl

theorem canonical925 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw925 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw925 = injectiveMoment H raw925step0 := by
      have hz : ∀ j, raw925 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw925step0 = (fun i j => raw925 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw925 permutation27 hz
    injectiveMoment H raw925step0 = injectiveMoment H raw925step1 := by
      have heq : raw925step1 = (fun i j => raw925step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw925step0 permutation4 permutation1
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

theorem canonical8972 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8972 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8972 = injectiveMoment H raw8972step0 := by
      have hz : ∀ j, raw8972 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw8972step0 = (fun i j => raw8972 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8972 permutation21 hz
    injectiveMoment H raw8972step0 = injectiveMoment H raw8972step1 := by
      have hz : ∀ j, raw8972step0 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8972step1 = (fun i j => raw8972step0 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8972step0 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

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

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

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

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

theorem canonical4147 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4147 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw4147 = injectiveMoment H raw4147step0 := by
      have heq : raw4147step0 = -raw4147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4147).symm
    injectiveMoment H raw4147step0 = injectiveMoment H raw4147step1 := by
      have heq : raw4147step1 = (fun i j => raw4147step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4147step0 permutation8 permutation4
    _ = injectiveMoment H node37 := by rfl

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

theorem canonical2849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2849 = injectiveMoment H node37 := by
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

theorem canonical4161 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4161 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4161 = injectiveMoment H raw4161step0 := by
      have heq : raw4161step0 = -raw4161 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4161).symm
    injectiveMoment H raw4161step0 = injectiveMoment H raw4161step1 := by
      have heq : raw4161step1 = (fun i j => raw4161step0 (permutation5 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4161step0 permutation5 permutation5
    _ = injectiveMoment H node36 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical214
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6870 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6870 = injectiveMoment H node63 := by
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

theorem sound204 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node204 = Sparse.eval value204 (momentVector H) := by
  have heq : pivotMatrix204 = (fun u v => node204 (pivotPermutation204 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node204 = injectiveMoment H pivotMatrix204 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix204 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix204 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix204 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix204 (0 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix204 (1 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix204 (1 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix204 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix204 (2 : Fin 3) = raw4147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4147 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node204 + (injectiveMoment H (mergeFirst pivotMatrix204 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix204 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix204 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value204, value37, value41, Sparse.eval] at hc ⊢
  linarith

theorem sound215 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node215 = Sparse.eval value215 (momentVector H) := by
  have heq : pivotMatrix215 = (fun u v => node215 (pivotPermutation215 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node215 = injectiveMoment H pivotMatrix215 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix215 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix215 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix215 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix215 (0 : Fin 3) = raw6870 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6870 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix215 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix215 (1 : Fin 3) = raw4161 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4161 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix215 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix215 (2 : Fin 3) = raw4147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4147 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node215 + (injectiveMoment H (mergeFirst pivotMatrix215 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix215 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix215 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value215, value36, value37, value63, Sparse.eval] at hc ⊢
  linarith

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

theorem singlePair268 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node268 node268Labels = Sparse.eval singlePairValue268 (familyPairVector B) := by
  have hp := single_label_three B hB node268
  have hl : node268Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node268 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node268 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node268 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node268 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node268 (EqualityPatterns.family3.label 1) = PairSemantics.raw918 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node268 PairSemantics.raw918; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical918 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node268 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node268 (EqualityPatterns.family3.label 2) = PairSemantics.raw9013 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node268 PairSemantics.raw9013; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9013 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node268 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node268 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node268 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node268 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value215 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node268 (EqualityPatterns.family3.label 4) = PairSemantics.raw538 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node268 PairSemantics.raw538; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical538 hH).trans (PairSemantics.sound215 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue268, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value215, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair269 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node269 node269Labels = Sparse.eval singlePairValue269 (familyPairVector B) := by
  have hp := single_label_three B hB node269
  have hl : node269Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node269 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node269 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node269 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node269 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node269 (EqualityPatterns.family3.label 1) = PairSemantics.raw925 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node269 PairSemantics.raw925; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical925 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node269 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node269 (EqualityPatterns.family3.label 2) = PairSemantics.raw8972 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node269 PairSemantics.raw8972; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8972 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node269 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node269 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node269 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node269 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value204 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node269 (EqualityPatterns.family3.label 4) = PairSemantics.raw553 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node269 PairSemantics.raw553; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical553 hH).trans (PairSemantics.sound204 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue269, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value204, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3224 node3224Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node269 node269Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw472 singletonSmall3224
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3224) = raw472Labels := by decide +kernel
  rw [hl, canonical472 B hB] at h
  have hc0 : mixedMoment B raw472 (Fin.cases (0 : Fin 1) singletonSmall3224) =
      mixedMoment B node269 node269Labels := by
    have ha : raw472 = raw473 := by apply Matrix.ext; unfold raw472 raw473; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3224 = raw473Labels := by decide +kernel
    rw [ha, hj, canonical473 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton3225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3225 node3225Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node268 node268Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw474 singletonSmall3225
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3225) = raw474Labels := by decide +kernel
  rw [hl, canonical474 B hB] at h
  have hc0 : mixedMoment B raw474 (Fin.cases (0 : Fin 1) singletonSmall3225) =
      mixedMoment B node268 node268Labels := by
    have ha : raw474 = raw475 := by apply Matrix.ext; unfold raw474 raw475; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3225 = raw475Labels := by decide +kernel
    rw [ha, hj, canonical475 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem sound268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node268 node268Labels = Sparse.eval nodeValue268 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue268 (familyPairVector B) := singlePair268 B _hB
    _ = _ := by norm_num [singlePairValue268, nodeValue268, Sparse.eval, mixedVector] <;> ring

theorem sound269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node269 node269Labels = Sparse.eval nodeValue269 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue269 (familyPairVector B) := singlePair269 B _hB
    _ = _ := by norm_num [singlePairValue269, nodeValue269, Sparse.eval, mixedVector] <;> ring

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

theorem sound3189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3189 node3189Labels = Sparse.eval nodeValue3189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3189) = mixedMoment B node3189 node3189Labels := rfl
  simpa [nodeValue3189, Sparse.eval] using hc.symm

theorem sound3196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3196 node3196Labels = Sparse.eval nodeValue3196 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3196) = mixedMoment B node3196 node3196Labels := rfl
  simpa [nodeValue3196, Sparse.eval] using hc.symm

theorem sound3197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3197 node3197Labels = Sparse.eval nodeValue3197 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3197) = mixedMoment B node3197 node3197Labels := rfl
  simpa [nodeValue3197, Sparse.eval] using hc.symm

theorem sound3198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3198 node3198Labels = Sparse.eval nodeValue3198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3198) = mixedMoment B node3198 node3198Labels := rfl
  simpa [nodeValue3198, Sparse.eval] using hc.symm

theorem sound3199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3199 node3199Labels = Sparse.eval nodeValue3199 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3199) = mixedMoment B node3199 node3199Labels := rfl
  simpa [nodeValue3199, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3228 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3228 node3228Labels = 0 := by
  exact mixedMoment_order_one B hB node3228 node3228Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3229 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3229 node3229Labels = 0 := by
  exact mixedMoment_order_one B hB node3229 node3229Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3230 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3230 node3230Labels = 0 := by
  exact mixedMoment_order_one B hB node3230 node3230Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3231 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3231 node3231Labels = 0 := by
  exact mixedMoment_order_one B hB node3231 node3231Labels 2
    (by decide +kernel) (by decide +kernel)

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

theorem sound3202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3202 node3202Labels = Sparse.eval nodeValue3202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3202) = mixedMoment B node3202 node3202Labels := rfl
  simpa [nodeValue3202, Sparse.eval] using hc.symm

theorem sound3221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3221 node3221Labels = Sparse.eval nodeValue3221 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3221) = mixedMoment B node3221 node3221Labels := rfl
  simpa [nodeValue3221, Sparse.eval] using hc.symm

theorem sound3222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3222 node3222Labels = Sparse.eval nodeValue3222 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3222) = mixedMoment B node3222 node3222Labels := rfl
  simpa [nodeValue3222, Sparse.eval] using hc.symm

theorem sound3224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3224 node3224Labels = Sparse.eval nodeValue3224 (mixedVector B) := by
  have h := singleton3224 B _hB
  rw [sound269 B _hB _hF] at h
  norm_num [nodeValue3224, nodeValue269, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3225 node3225Labels = Sparse.eval nodeValue3225 (mixedVector B) := by
  have h := singleton3225 B _hB
  rw [sound268 B _hB _hF] at h
  norm_num [nodeValue3225, nodeValue268, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3228 node3228Labels = Sparse.eval nodeValue3228 (mixedVector B) := by
  simpa only [nodeValue3228, Sparse.eval_nil] using zero3228 B _hB _hF

theorem sound3229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3229 node3229Labels = Sparse.eval nodeValue3229 (mixedVector B) := by
  simpa only [nodeValue3229, Sparse.eval_nil] using zero3229 B _hB _hF

theorem sound3230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3230 node3230Labels = Sparse.eval nodeValue3230 (mixedVector B) := by
  simpa only [nodeValue3230, Sparse.eval_nil] using zero3230 B _hB _hF

theorem sound3231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3231 node3231Labels = Sparse.eval nodeValue3231 (mixedVector B) := by
  simpa only [nodeValue3231, Sparse.eval_nil] using zero3231 B _hB _hF

theorem sound3255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3255 node3255Labels = Sparse.eval nodeValue3255 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3255) = mixedMoment B node3255 node3255Labels := rfl
  simpa [nodeValue3255, Sparse.eval] using hc.symm

theorem sound3257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3257 node3257Labels = Sparse.eval nodeValue3257 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3257) = mixedMoment B node3257 node3257Labels := rfl
  simpa [nodeValue3257, Sparse.eval] using hc.symm

theorem sound3258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3258 node3258Labels = Sparse.eval nodeValue3258 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3258) = mixedMoment B node3258 node3258Labels := rfl
  simpa [nodeValue3258, Sparse.eval] using hc.symm

theorem sound3259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3259 node3259Labels = Sparse.eval nodeValue3259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3259) = mixedMoment B node3259 node3259Labels := rfl
  simpa [nodeValue3259, Sparse.eval] using hc.symm

theorem sound3260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3260 node3260Labels = Sparse.eval nodeValue3260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3260) = mixedMoment B node3260 node3260Labels := rfl
  simpa [nodeValue3260, Sparse.eval] using hc.symm

theorem sound3261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3261 node3261Labels = Sparse.eval nodeValue3261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3261) = mixedMoment B node3261 node3261Labels := rfl
  simpa [nodeValue3261, Sparse.eval] using hc.symm

theorem sound3262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3262 node3262Labels = Sparse.eval nodeValue3262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3262) = mixedMoment B node3262 node3262Labels := rfl
  simpa [nodeValue3262, Sparse.eval] using hc.symm

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

theorem sound3266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3266 node3266Labels = Sparse.eval nodeValue3266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3266) = mixedMoment B node3266 node3266Labels := rfl
  simpa [nodeValue3266, Sparse.eval] using hc.symm

theorem sound3267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3267 node3267Labels = Sparse.eval nodeValue3267 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3267) = mixedMoment B node3267 node3267Labels := rfl
  simpa [nodeValue3267, Sparse.eval] using hc.symm

theorem sound3268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3268 node3268Labels = Sparse.eval nodeValue3268 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3268) = mixedMoment B node3268 node3268Labels := rfl
  simpa [nodeValue3268, Sparse.eval] using hc.symm

theorem sound3271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3271 node3271Labels = Sparse.eval nodeValue3271 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3271) = mixedMoment B node3271 node3271Labels := rfl
  simpa [nodeValue3271, Sparse.eval] using hc.symm

theorem sound3272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3272 node3272Labels = Sparse.eval nodeValue3272 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3272) = mixedMoment B node3272 node3272Labels := rfl
  simpa [nodeValue3272, Sparse.eval] using hc.symm

theorem sound3288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3288 node3288Labels = Sparse.eval nodeValue3288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3288) = mixedMoment B node3288 node3288Labels := rfl
  simpa [nodeValue3288, Sparse.eval] using hc.symm

theorem sound3289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3289 node3289Labels = Sparse.eval nodeValue3289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3289) = mixedMoment B node3289 node3289Labels := rfl
  simpa [nodeValue3289, Sparse.eval] using hc.symm

theorem sound3290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3290 node3290Labels = Sparse.eval nodeValue3290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3290) = mixedMoment B node3290 node3290Labels := rfl
  simpa [nodeValue3290, Sparse.eval] using hc.symm

theorem sound3291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3291 node3291Labels = Sparse.eval nodeValue3291 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3291) = mixedMoment B node3291 node3291Labels := rfl
  simpa [nodeValue3291, Sparse.eval] using hc.symm

theorem sound3294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3294 node3294Labels = Sparse.eval nodeValue3294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3294) = mixedMoment B node3294 node3294Labels := rfl
  simpa [nodeValue3294, Sparse.eval] using hc.symm

theorem sound3295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3295 node3295Labels = Sparse.eval nodeValue3295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3295) = mixedMoment B node3295 node3295Labels := rfl
  simpa [nodeValue3295, Sparse.eval] using hc.symm

theorem sound3296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3296 node3296Labels = Sparse.eval nodeValue3296 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3296) = mixedMoment B node3296 node3296Labels := rfl
  simpa [nodeValue3296, Sparse.eval] using hc.symm

theorem sound3297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3297 node3297Labels = Sparse.eval nodeValue3297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3297) = mixedMoment B node3297 node3297Labels := rfl
  simpa [nodeValue3297, Sparse.eval] using hc.symm

theorem sound3298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3298 node3298Labels = Sparse.eval nodeValue3298 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3298) = mixedMoment B node3298 node3298Labels := rfl
  simpa [nodeValue3298, Sparse.eval] using hc.symm

theorem sound3302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3302 node3302Labels = Sparse.eval nodeValue3302 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3302) = mixedMoment B node3302 node3302Labels := rfl
  simpa [nodeValue3302, Sparse.eval] using hc.symm

theorem sound3303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3303 node3303Labels = Sparse.eval nodeValue3303 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3303) = mixedMoment B node3303 node3303Labels := rfl
  simpa [nodeValue3303, Sparse.eval] using hc.symm

theorem sound3306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3306 node3306Labels = Sparse.eval nodeValue3306 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3306) = mixedMoment B node3306 node3306Labels := rfl
  simpa [nodeValue3306, Sparse.eval] using hc.symm

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

theorem sound3365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3365 node3365Labels = Sparse.eval nodeValue3365 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3365) = mixedMoment B node3365 node3365Labels := rfl
  simpa [nodeValue3365, Sparse.eval] using hc.symm

theorem sound3375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3375 node3375Labels = Sparse.eval nodeValue3375 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3375) = mixedMoment B node3375 node3375Labels := rfl
  simpa [nodeValue3375, Sparse.eval] using hc.symm

theorem sound3376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3376 node3376Labels = Sparse.eval nodeValue3376 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3376) = mixedMoment B node3376 node3376Labels := rfl
  simpa [nodeValue3376, Sparse.eval] using hc.symm

theorem sound3378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3378 node3378Labels = Sparse.eval nodeValue3378 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3378) = mixedMoment B node3378 node3378Labels := rfl
  simpa [nodeValue3378, Sparse.eval] using hc.symm

theorem sound3379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3379 node3379Labels = Sparse.eval nodeValue3379 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3379) = mixedMoment B node3379 node3379Labels := rfl
  simpa [nodeValue3379, Sparse.eval] using hc.symm

theorem sound3380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3380 node3380Labels = Sparse.eval nodeValue3380 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3380) = mixedMoment B node3380 node3380Labels := rfl
  simpa [nodeValue3380, Sparse.eval] using hc.symm

theorem sound3388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3388 node3388Labels = Sparse.eval nodeValue3388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3388) = mixedMoment B node3388 node3388Labels := rfl
  simpa [nodeValue3388, Sparse.eval] using hc.symm

theorem sound3390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3390 node3390Labels = Sparse.eval nodeValue3390 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3390) = mixedMoment B node3390 node3390Labels := rfl
  simpa [nodeValue3390, Sparse.eval] using hc.symm

theorem sound3391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3391 node3391Labels = Sparse.eval nodeValue3391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3391) = mixedMoment B node3391 node3391Labels := rfl
  simpa [nodeValue3391, Sparse.eval] using hc.symm

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

theorem sound3392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3392 node3392Labels = Sparse.eval nodeValue3392 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3392) = mixedMoment B node3392 node3392Labels := rfl
  simpa [nodeValue3392, Sparse.eval] using hc.symm

theorem sound3394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3394 node3394Labels = Sparse.eval nodeValue3394 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3394) = mixedMoment B node3394 node3394Labels := rfl
  simpa [nodeValue3394, Sparse.eval] using hc.symm

theorem sound3395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3395 node3395Labels = Sparse.eval nodeValue3395 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3395) = mixedMoment B node3395 node3395Labels := rfl
  simpa [nodeValue3395, Sparse.eval] using hc.symm

theorem sound3396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3396 node3396Labels = Sparse.eval nodeValue3396 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3396) = mixedMoment B node3396 node3396Labels := rfl
  simpa [nodeValue3396, Sparse.eval] using hc.symm

theorem sound3397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3397 node3397Labels = Sparse.eval nodeValue3397 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3397) = mixedMoment B node3397 node3397Labels := rfl
  simpa [nodeValue3397, Sparse.eval] using hc.symm

theorem sound3406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3406 node3406Labels = Sparse.eval nodeValue3406 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3406) = mixedMoment B node3406 node3406Labels := rfl
  simpa [nodeValue3406, Sparse.eval] using hc.symm

theorem sound3407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3407 node3407Labels = Sparse.eval nodeValue3407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3407) = mixedMoment B node3407 node3407Labels := rfl
  simpa [nodeValue3407, Sparse.eval] using hc.symm

theorem sound3408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3408 node3408Labels = Sparse.eval nodeValue3408 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3408) = mixedMoment B node3408 node3408Labels := rfl
  simpa [nodeValue3408, Sparse.eval] using hc.symm

theorem sound3413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3413 node3413Labels = Sparse.eval nodeValue3413 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3413) = mixedMoment B node3413 node3413Labels := rfl
  simpa [nodeValue3413, Sparse.eval] using hc.symm

theorem sound3414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3414 node3414Labels = Sparse.eval nodeValue3414 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3414) = mixedMoment B node3414 node3414Labels := rfl
  simpa [nodeValue3414, Sparse.eval] using hc.symm

theorem sound3415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3415 node3415Labels = Sparse.eval nodeValue3415 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3415) = mixedMoment B node3415 node3415Labels := rfl
  simpa [nodeValue3415, Sparse.eval] using hc.symm

theorem sound3418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3418 node3418Labels = Sparse.eval nodeValue3418 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3418) = mixedMoment B node3418 node3418Labels := rfl
  simpa [nodeValue3418, Sparse.eval] using hc.symm

theorem sound3419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3419 node3419Labels = Sparse.eval nodeValue3419 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3419) = mixedMoment B node3419 node3419Labels := rfl
  simpa [nodeValue3419, Sparse.eval] using hc.symm

theorem sound3451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3451 node3451Labels = Sparse.eval nodeValue3451 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3451) = mixedMoment B node3451 node3451Labels := rfl
  simpa [nodeValue3451, Sparse.eval] using hc.symm

theorem sound3452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3452 node3452Labels = Sparse.eval nodeValue3452 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3452) = mixedMoment B node3452 node3452Labels := rfl
  simpa [nodeValue3452, Sparse.eval] using hc.symm

theorem sound3454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3454 node3454Labels = Sparse.eval nodeValue3454 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3454) = mixedMoment B node3454 node3454Labels := rfl
  simpa [nodeValue3454, Sparse.eval] using hc.symm

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

theorem sound3458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3458 node3458Labels = Sparse.eval nodeValue3458 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3458) = mixedMoment B node3458 node3458Labels := rfl
  simpa [nodeValue3458, Sparse.eval] using hc.symm

theorem sound3461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3461 node3461Labels = Sparse.eval nodeValue3461 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3461) = mixedMoment B node3461 node3461Labels := rfl
  simpa [nodeValue3461, Sparse.eval] using hc.symm

theorem sound3462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3462 node3462Labels = Sparse.eval nodeValue3462 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3462) = mixedMoment B node3462 node3462Labels := rfl
  simpa [nodeValue3462, Sparse.eval] using hc.symm

theorem sound3463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3463 node3463Labels = Sparse.eval nodeValue3463 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3463) = mixedMoment B node3463 node3463Labels := rfl
  simpa [nodeValue3463, Sparse.eval] using hc.symm

theorem sound3464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3464 node3464Labels = Sparse.eval nodeValue3464 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3464) = mixedMoment B node3464 node3464Labels := rfl
  simpa [nodeValue3464, Sparse.eval] using hc.symm

theorem sound3465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3465 node3465Labels = Sparse.eval nodeValue3465 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3465) = mixedMoment B node3465 node3465Labels := rfl
  simpa [nodeValue3465, Sparse.eval] using hc.symm

theorem sound3466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3466 node3466Labels = Sparse.eval nodeValue3466 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3466) = mixedMoment B node3466 node3466Labels := rfl
  simpa [nodeValue3466, Sparse.eval] using hc.symm

theorem sound3472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3472 node3472Labels = Sparse.eval nodeValue3472 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3472) = mixedMoment B node3472 node3472Labels := rfl
  simpa [nodeValue3472, Sparse.eval] using hc.symm

theorem sound3474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3474 node3474Labels = Sparse.eval nodeValue3474 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3474) = mixedMoment B node3474 node3474Labels := rfl
  simpa [nodeValue3474, Sparse.eval] using hc.symm

theorem sound3475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3475 node3475Labels = Sparse.eval nodeValue3475 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3475) = mixedMoment B node3475 node3475Labels := rfl
  simpa [nodeValue3475, Sparse.eval] using hc.symm

theorem sound3476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3476 node3476Labels = Sparse.eval nodeValue3476 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3476) = mixedMoment B node3476 node3476Labels := rfl
  simpa [nodeValue3476, Sparse.eval] using hc.symm

theorem sound3480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3480 node3480Labels = Sparse.eval nodeValue3480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3480) = mixedMoment B node3480 node3480Labels := rfl
  simpa [nodeValue3480, Sparse.eval] using hc.symm

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

theorem sound3496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3496 node3496Labels = Sparse.eval nodeValue3496 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3496) = mixedMoment B node3496 node3496Labels := rfl
  simpa [nodeValue3496, Sparse.eval] using hc.symm

theorem sound3497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3497 node3497Labels = Sparse.eval nodeValue3497 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3497) = mixedMoment B node3497 node3497Labels := rfl
  simpa [nodeValue3497, Sparse.eval] using hc.symm

theorem sound3505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3505 node3505Labels = Sparse.eval nodeValue3505 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3505) = mixedMoment B node3505 node3505Labels := rfl
  simpa [nodeValue3505, Sparse.eval] using hc.symm

theorem sound3506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3506 node3506Labels = Sparse.eval nodeValue3506 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3506) = mixedMoment B node3506 node3506Labels := rfl
  simpa [nodeValue3506, Sparse.eval] using hc.symm

theorem sound3508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3508 node3508Labels = Sparse.eval nodeValue3508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3508) = mixedMoment B node3508 node3508Labels := rfl
  simpa [nodeValue3508, Sparse.eval] using hc.symm

theorem sound3509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3509 node3509Labels = Sparse.eval nodeValue3509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3509) = mixedMoment B node3509 node3509Labels := rfl
  simpa [nodeValue3509, Sparse.eval] using hc.symm

theorem sound3510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3510 node3510Labels = Sparse.eval nodeValue3510 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3510) = mixedMoment B node3510 node3510Labels := rfl
  simpa [nodeValue3510, Sparse.eval] using hc.symm

theorem sound3511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3511 node3511Labels = Sparse.eval nodeValue3511 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3511) = mixedMoment B node3511 node3511Labels := rfl
  simpa [nodeValue3511, Sparse.eval] using hc.symm

theorem sound3512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3512 node3512Labels = Sparse.eval nodeValue3512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3512) = mixedMoment B node3512 node3512Labels := rfl
  simpa [nodeValue3512, Sparse.eval] using hc.symm

theorem sound3516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3516 node3516Labels = Sparse.eval nodeValue3516 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3516) = mixedMoment B node3516 node3516Labels := rfl
  simpa [nodeValue3516, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1229 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1229 x = (-1174798139719680000000 : ℝ) * Sparse.eval nodeValue3189 x := by
  norm_num [reducedTerm1229, nodeValue3189, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1230 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1230 x = (6466249688175083520000 : ℝ) * Sparse.eval nodeValue3196 x := by
  norm_num [reducedTerm1230, nodeValue3196, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1231 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1231 x = (1899117244195799040000 : ℝ) * Sparse.eval nodeValue3197 x := by
  norm_num [reducedTerm1231, nodeValue3197, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1232 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1232 x = (419312052798750720000 : ℝ) * Sparse.eval nodeValue3198 x := by
  norm_num [reducedTerm1232, nodeValue3198, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1233 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1233 x = (6894774206306058240000 : ℝ) * Sparse.eval nodeValue3199 x := by
  norm_num [reducedTerm1233, nodeValue3199, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1234 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1234 x = (11475455859405619200000 : ℝ) * Sparse.eval nodeValue3202 x := by
  norm_num [reducedTerm1234, nodeValue3202, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1235 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1235 x = (-12951213345010483200000 : ℝ) * Sparse.eval nodeValue3221 x := by
  norm_num [reducedTerm1235, nodeValue3221, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1236 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1236 x = (-12438782405973245952000 : ℝ) * Sparse.eval nodeValue3222 x := by
  norm_num [reducedTerm1236, nodeValue3222, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1237 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1237 x = (4057256850042912768000 : ℝ) * Sparse.eval nodeValue3223 x := by
  norm_num [reducedTerm1237, nodeValue3223, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1238 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1238 x = (3276781374141628416000 : ℝ) * Sparse.eval nodeValue3224 x := by
  norm_num [reducedTerm1238, nodeValue3224, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1239 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1239 x = (1722459352110465024000 : ℝ) * Sparse.eval nodeValue3225 x := by
  norm_num [reducedTerm1239, nodeValue3225, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1240 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1240 x = (-4686317239001481216000 : ℝ) * Sparse.eval nodeValue3226 x := by
  norm_num [reducedTerm1240, nodeValue3226, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1241 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1241 x = (-2883452798765629440000 : ℝ) * Sparse.eval nodeValue3227 x := by
  norm_num [reducedTerm1241, nodeValue3227, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1242 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1242 x = (7903823872994574336000 : ℝ) * Sparse.eval nodeValue3228 x := by
  norm_num [reducedTerm1242, nodeValue3228, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1243 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1243 x = (25143534921037381632000 : ℝ) * Sparse.eval nodeValue3229 x := by
  norm_num [reducedTerm1243, nodeValue3229, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1244 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1244 x = (9067699888990912512000 : ℝ) * Sparse.eval nodeValue3230 x := by
  norm_num [reducedTerm1244, nodeValue3230, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1245 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1245 x = (2472915735452123136000 : ℝ) * Sparse.eval nodeValue3231 x := by
  norm_num [reducedTerm1245, nodeValue3231, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1246 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1246 x = (1331003266183987200000 : ℝ) * Sparse.eval nodeValue3255 x := by
  norm_num [reducedTerm1246, nodeValue3255, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1247 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1247 x = (5933039869919232000000 : ℝ) * Sparse.eval nodeValue3257 x := by
  norm_num [reducedTerm1247, nodeValue3257, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1248 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1248 x = (-1531997227471011840000 : ℝ) * Sparse.eval nodeValue3258 x := by
  norm_num [reducedTerm1248, nodeValue3258, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1249 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1249 x = (9156607353476481024000 : ℝ) * Sparse.eval nodeValue3259 x := by
  norm_num [reducedTerm1249, nodeValue3259, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1250 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1250 x = (1182595905074626560000 : ℝ) * Sparse.eval nodeValue3260 x := by
  norm_num [reducedTerm1250, nodeValue3260, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1251 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1251 x = (270860476671590400000 : ℝ) * Sparse.eval nodeValue3261 x := by
  norm_num [reducedTerm1251, nodeValue3261, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1252 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1252 x = (1979586319187312640000 : ℝ) * Sparse.eval nodeValue3262 x := by
  norm_num [reducedTerm1252, nodeValue3262, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1253 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1253 x = (3863114615263002624000 : ℝ) * Sparse.eval nodeValue3266 x := by
  norm_num [reducedTerm1253, nodeValue3266, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1254 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1254 x = (53914691091824640000 : ℝ) * Sparse.eval nodeValue3267 x := by
  norm_num [reducedTerm1254, nodeValue3267, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1255 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1255 x = (-2204937138861047808000 : ℝ) * Sparse.eval nodeValue3268 x := by
  norm_num [reducedTerm1255, nodeValue3268, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1256 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1256 x = (-2066297949707894784000 : ℝ) * Sparse.eval nodeValue3271 x := by
  norm_num [reducedTerm1256, nodeValue3271, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1257 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1257 x = (-992147345927700480000 : ℝ) * Sparse.eval nodeValue3272 x := by
  norm_num [reducedTerm1257, nodeValue3272, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1258 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1258 x = (305084947161415680000 : ℝ) * Sparse.eval nodeValue3288 x := by
  norm_num [reducedTerm1258, nodeValue3288, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1259 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1259 x = (2654462499211837440000 : ℝ) * Sparse.eval nodeValue3289 x := by
  norm_num [reducedTerm1259, nodeValue3289, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1260 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1260 x = (1619043489526579200000 : ℝ) * Sparse.eval nodeValue3290 x := by
  norm_num [reducedTerm1260, nodeValue3290, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1261 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1261 x = (-1521451825330913280000 : ℝ) * Sparse.eval nodeValue3291 x := by
  norm_num [reducedTerm1261, nodeValue3291, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1262 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1262 x = (-8946502007384309760000 : ℝ) * Sparse.eval nodeValue3294 x := by
  norm_num [reducedTerm1262, nodeValue3294, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1263 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1263 x = (-3789395265230733312000 : ℝ) * Sparse.eval nodeValue3295 x := by
  norm_num [reducedTerm1263, nodeValue3295, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1264 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1264 x = (-9536788940949946368000 : ℝ) * Sparse.eval nodeValue3296 x := by
  norm_num [reducedTerm1264, nodeValue3296, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1265 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1265 x = (-1889903966198169600000 : ℝ) * Sparse.eval nodeValue3297 x := by
  norm_num [reducedTerm1265, nodeValue3297, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1266 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1266 x = (752859079780663296000 : ℝ) * Sparse.eval nodeValue3298 x := by
  norm_num [reducedTerm1266, nodeValue3298, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1267 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1267 x = (-1389583379072286720000 : ℝ) * Sparse.eval nodeValue3302 x := by
  norm_num [reducedTerm1267, nodeValue3302, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1268 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1268 x = (-565455270900989952000 : ℝ) * Sparse.eval nodeValue3303 x := by
  norm_num [reducedTerm1268, nodeValue3303, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1269 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1269 x = (-186994987012915200000 : ℝ) * Sparse.eval nodeValue3306 x := by
  norm_num [reducedTerm1269, nodeValue3306, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1270 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1270 x = (4501291376384409600000 : ℝ) * Sparse.eval nodeValue3365 x := by
  norm_num [reducedTerm1270, nodeValue3365, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1271 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1271 x = (654308882759024640000 : ℝ) * Sparse.eval nodeValue3375 x := by
  norm_num [reducedTerm1271, nodeValue3375, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1272 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1272 x = (-4735033992735621120000 : ℝ) * Sparse.eval nodeValue3376 x := by
  norm_num [reducedTerm1272, nodeValue3376, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1273 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1273 x = (4935862034835701760000 : ℝ) * Sparse.eval nodeValue3378 x := by
  norm_num [reducedTerm1273, nodeValue3378, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1274 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1274 x = (-379671498467573760000 : ℝ) * Sparse.eval nodeValue3379 x := by
  norm_num [reducedTerm1274, nodeValue3379, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1275 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1275 x = (2452540759969628160000 : ℝ) * Sparse.eval nodeValue3380 x := by
  norm_num [reducedTerm1275, nodeValue3380, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1276 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1276 x = (28541892592926720000 : ℝ) * Sparse.eval nodeValue3388 x := by
  norm_num [reducedTerm1276, nodeValue3388, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1277 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1277 x = (-2426340427298242560000 : ℝ) * Sparse.eval nodeValue3390 x := by
  norm_num [reducedTerm1277, nodeValue3390, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1278 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1278 x = (-3915341740423249920000 : ℝ) * Sparse.eval nodeValue3391 x := by
  norm_num [reducedTerm1278, nodeValue3391, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1279 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1279 x = (-57083785185853440000 : ℝ) * Sparse.eval nodeValue3392 x := by
  norm_num [reducedTerm1279, nodeValue3392, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1280 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1280 x = (6542432374534963200000 : ℝ) * Sparse.eval nodeValue3394 x := by
  norm_num [reducedTerm1280, nodeValue3394, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1281 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1281 x = (16453451164259450880000 : ℝ) * Sparse.eval nodeValue3395 x := by
  norm_num [reducedTerm1281, nodeValue3395, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1282 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1282 x = (10440815232685178880000 : ℝ) * Sparse.eval nodeValue3396 x := by
  norm_num [reducedTerm1282, nodeValue3396, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1283 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1283 x = (-684291540819640320000 : ℝ) * Sparse.eval nodeValue3397 x := by
  norm_num [reducedTerm1283, nodeValue3397, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1284 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1284 x = (652996879610019840000 : ℝ) * Sparse.eval nodeValue3406 x := by
  norm_num [reducedTerm1284, nodeValue3406, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1285 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1285 x = (3344441963460820992000 : ℝ) * Sparse.eval nodeValue3407 x := by
  norm_num [reducedTerm1285, nodeValue3407, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1286 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1286 x = (-1985415998552211456000 : ℝ) * Sparse.eval nodeValue3408 x := by
  norm_num [reducedTerm1286, nodeValue3408, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1287 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1287 x = (-2989726119329660928000 : ℝ) * Sparse.eval nodeValue3413 x := by
  norm_num [reducedTerm1287, nodeValue3413, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1288 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1288 x = (355417517501448192000 : ℝ) * Sparse.eval nodeValue3414 x := by
  norm_num [reducedTerm1288, nodeValue3414, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1289 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1289 x = (-1559990074286407680000 : ℝ) * Sparse.eval nodeValue3415 x := by
  norm_num [reducedTerm1289, nodeValue3415, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1290 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1290 x = (-354715844131160064000 : ℝ) * Sparse.eval nodeValue3418 x := by
  norm_num [reducedTerm1290, nodeValue3418, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1291 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1291 x = (814999240525381632000 : ℝ) * Sparse.eval nodeValue3419 x := by
  norm_num [reducedTerm1291, nodeValue3419, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1292 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1292 x = (744619799330684928000 : ℝ) * Sparse.eval nodeValue3451 x := by
  norm_num [reducedTerm1292, nodeValue3451, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1293 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1293 x = (4783674936826920960000 : ℝ) * Sparse.eval nodeValue3452 x := by
  norm_num [reducedTerm1293, nodeValue3452, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1294 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1294 x = (5808432531870646272000 : ℝ) * Sparse.eval nodeValue3454 x := by
  norm_num [reducedTerm1294, nodeValue3454, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1295 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1295 x = (23220776228880384000 : ℝ) * Sparse.eval nodeValue3458 x := by
  norm_num [reducedTerm1295, nodeValue3458, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1296 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1296 x = (2229127337632333824000 : ℝ) * Sparse.eval nodeValue3461 x := by
  norm_num [reducedTerm1296, nodeValue3461, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1297 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1297 x = (-2370794412740640768000 : ℝ) * Sparse.eval nodeValue3462 x := by
  norm_num [reducedTerm1297, nodeValue3462, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1298 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1298 x = (-3066113985645182976000 : ℝ) * Sparse.eval nodeValue3463 x := by
  norm_num [reducedTerm1298, nodeValue3463, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1299 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1299 x = (3058373744961454080000 : ℝ) * Sparse.eval nodeValue3464 x := by
  norm_num [reducedTerm1299, nodeValue3464, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1300 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1300 x = (-722635406229897216000 : ℝ) * Sparse.eval nodeValue3465 x := by
  norm_num [reducedTerm1300, nodeValue3465, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1301 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1301 x = (-3632663000341315584000 : ℝ) * Sparse.eval nodeValue3466 x := by
  norm_num [reducedTerm1301, nodeValue3466, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1302 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1302 x = (506711554922151936000 : ℝ) * Sparse.eval nodeValue3472 x := by
  norm_num [reducedTerm1302, nodeValue3472, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1303 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1303 x = (-1835451633733337088000 : ℝ) * Sparse.eval nodeValue3474 x := by
  norm_num [reducedTerm1303, nodeValue3474, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1304 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1304 x = (-4633408883520700416000 : ℝ) * Sparse.eval nodeValue3475 x := by
  norm_num [reducedTerm1304, nodeValue3475, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1305 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1305 x = (1856913308405858304000 : ℝ) * Sparse.eval nodeValue3476 x := by
  norm_num [reducedTerm1305, nodeValue3476, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1306 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1306 x = (-4726817018446086144000 : ℝ) * Sparse.eval nodeValue3480 x := by
  norm_num [reducedTerm1306, nodeValue3480, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1307 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1307 x = (-416003421044736000000 : ℝ) * Sparse.eval nodeValue3488 x := by
  norm_num [reducedTerm1307, nodeValue3488, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1308 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1308 x = (4958849630270914560000 : ℝ) * Sparse.eval nodeValue3493 x := by
  norm_num [reducedTerm1308, nodeValue3493, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1309 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1309 x = (-8093713655448207360000 : ℝ) * Sparse.eval nodeValue3496 x := by
  norm_num [reducedTerm1309, nodeValue3496, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1310 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1310 x = (-416003421044736000000 : ℝ) * Sparse.eval nodeValue3497 x := by
  norm_num [reducedTerm1310, nodeValue3497, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1311 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1311 x = (7799955337720627200000 : ℝ) * Sparse.eval nodeValue3505 x := by
  norm_num [reducedTerm1311, nodeValue3505, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1312 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1312 x = (-3146577964923617280000 : ℝ) * Sparse.eval nodeValue3506 x := by
  norm_num [reducedTerm1312, nodeValue3506, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1313 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1313 x = (-1421726643557498880000 : ℝ) * Sparse.eval nodeValue3508 x := by
  norm_num [reducedTerm1313, nodeValue3508, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1314 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1314 x = (7390298065975050240000 : ℝ) * Sparse.eval nodeValue3509 x := by
  norm_num [reducedTerm1314, nodeValue3509, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1315 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1315 x = (-1331003266183987200000 : ℝ) * Sparse.eval nodeValue3510 x := by
  norm_num [reducedTerm1315, nodeValue3510, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1316 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1316 x = (-270860476671590400000 : ℝ) * Sparse.eval nodeValue3511 x := by
  norm_num [reducedTerm1316, nodeValue3511, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1317 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1317 x = (-3141806478252244992000 : ℝ) * Sparse.eval nodeValue3512 x := by
  norm_num [reducedTerm1317, nodeValue3512, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1318 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1318 x = (1646462429022781440000 : ℝ) * Sparse.eval nodeValue3516 x := by
  norm_num [reducedTerm1318, nodeValue3516, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1226Check : reducedMerge1226 = Integer.Sparse.mergeBy masterLess reducedTerm1230 reducedTerm1231 := by decide +kernel

theorem reducedMerge1227Check : reducedMerge1227 = Integer.Sparse.mergeBy masterLess reducedTerm1229 reducedMerge1226 := by decide +kernel

theorem reducedMerge1228Check : reducedMerge1228 = Integer.Sparse.mergeBy masterLess reducedTerm1232 reducedTerm1233 := by decide +kernel

theorem reducedMerge1229Check : reducedMerge1229 = Integer.Sparse.mergeBy masterLess reducedTerm1234 reducedTerm1235 := by decide +kernel

theorem reducedMerge1230Check : reducedMerge1230 = Integer.Sparse.mergeBy masterLess reducedMerge1228 reducedMerge1229 := by decide +kernel

theorem reducedMerge1231Check : reducedMerge1231 = Integer.Sparse.mergeBy masterLess reducedMerge1227 reducedMerge1230 := by decide +kernel

theorem reducedMerge1232Check : reducedMerge1232 = Integer.Sparse.mergeBy masterLess reducedTerm1236 reducedTerm1237 := by decide +kernel

theorem reducedMerge1233Check : reducedMerge1233 = Integer.Sparse.mergeBy masterLess reducedTerm1238 reducedTerm1239 := by decide +kernel

theorem reducedMerge1234Check : reducedMerge1234 = Integer.Sparse.mergeBy masterLess reducedMerge1232 reducedMerge1233 := by decide +kernel

theorem reducedMerge1235Check : reducedMerge1235 = Integer.Sparse.mergeBy masterLess reducedTerm1240 reducedTerm1241 := by decide +kernel

theorem reducedMerge1236Check : reducedMerge1236 = Integer.Sparse.mergeBy masterLess reducedTerm1242 reducedTerm1243 := by decide +kernel

theorem reducedMerge1237Check : reducedMerge1237 = Integer.Sparse.mergeBy masterLess reducedMerge1235 reducedMerge1236 := by decide +kernel

theorem reducedMerge1238Check : reducedMerge1238 = Integer.Sparse.mergeBy masterLess reducedMerge1234 reducedMerge1237 := by decide +kernel

theorem reducedMerge1239Check : reducedMerge1239 = Integer.Sparse.mergeBy masterLess reducedMerge1231 reducedMerge1238 := by decide +kernel

theorem reducedMerge1240Check : reducedMerge1240 = Integer.Sparse.mergeBy masterLess reducedTerm1245 reducedTerm1246 := by decide +kernel

theorem reducedMerge1241Check : reducedMerge1241 = Integer.Sparse.mergeBy masterLess reducedTerm1244 reducedMerge1240 := by decide +kernel

theorem reducedMerge1242Check : reducedMerge1242 = Integer.Sparse.mergeBy masterLess reducedTerm1247 reducedTerm1248 := by decide +kernel

theorem reducedMerge1243Check : reducedMerge1243 = Integer.Sparse.mergeBy masterLess reducedTerm1249 reducedTerm1250 := by decide +kernel

theorem reducedMerge1244Check : reducedMerge1244 = Integer.Sparse.mergeBy masterLess reducedMerge1242 reducedMerge1243 := by decide +kernel

theorem reducedMerge1245Check : reducedMerge1245 = Integer.Sparse.mergeBy masterLess reducedMerge1241 reducedMerge1244 := by decide +kernel

theorem reducedMerge1246Check : reducedMerge1246 = Integer.Sparse.mergeBy masterLess reducedTerm1251 reducedTerm1252 := by decide +kernel

theorem reducedMerge1247Check : reducedMerge1247 = Integer.Sparse.mergeBy masterLess reducedTerm1253 reducedTerm1254 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1248Check : reducedMerge1248 = Integer.Sparse.mergeBy masterLess reducedMerge1246 reducedMerge1247 := by decide +kernel

theorem reducedMerge1249Check : reducedMerge1249 = Integer.Sparse.mergeBy masterLess reducedTerm1255 reducedTerm1256 := by decide +kernel

theorem reducedMerge1250Check : reducedMerge1250 = Integer.Sparse.mergeBy masterLess reducedTerm1257 reducedTerm1258 := by decide +kernel

theorem reducedMerge1251Check : reducedMerge1251 = Integer.Sparse.mergeBy masterLess reducedMerge1249 reducedMerge1250 := by decide +kernel

theorem reducedMerge1252Check : reducedMerge1252 = Integer.Sparse.mergeBy masterLess reducedMerge1248 reducedMerge1251 := by decide +kernel

theorem reducedMerge1253Check : reducedMerge1253 = Integer.Sparse.mergeBy masterLess reducedMerge1245 reducedMerge1252 := by decide +kernel

theorem reducedMerge1254Check : reducedMerge1254 = Integer.Sparse.mergeBy masterLess reducedMerge1239 reducedMerge1253 := by decide +kernel

theorem reducedMerge1255Check : reducedMerge1255 = Integer.Sparse.mergeBy masterLess reducedMerge1225 reducedMerge1254 := by decide +kernel

theorem reducedMerge1256Check : reducedMerge1256 = Integer.Sparse.mergeBy masterLess reducedTerm1260 reducedTerm1261 := by decide +kernel

theorem reducedMerge1257Check : reducedMerge1257 = Integer.Sparse.mergeBy masterLess reducedTerm1259 reducedMerge1256 := by decide +kernel

theorem reducedMerge1258Check : reducedMerge1258 = Integer.Sparse.mergeBy masterLess reducedTerm1262 reducedTerm1263 := by decide +kernel

theorem reducedMerge1259Check : reducedMerge1259 = Integer.Sparse.mergeBy masterLess reducedTerm1264 reducedTerm1265 := by decide +kernel

theorem reducedMerge1260Check : reducedMerge1260 = Integer.Sparse.mergeBy masterLess reducedMerge1258 reducedMerge1259 := by decide +kernel

theorem reducedMerge1261Check : reducedMerge1261 = Integer.Sparse.mergeBy masterLess reducedMerge1257 reducedMerge1260 := by decide +kernel

theorem reducedMerge1262Check : reducedMerge1262 = Integer.Sparse.mergeBy masterLess reducedTerm1266 reducedTerm1267 := by decide +kernel

theorem reducedMerge1263Check : reducedMerge1263 = Integer.Sparse.mergeBy masterLess reducedTerm1268 reducedTerm1269 := by decide +kernel

theorem reducedMerge1264Check : reducedMerge1264 = Integer.Sparse.mergeBy masterLess reducedMerge1262 reducedMerge1263 := by decide +kernel

theorem reducedMerge1265Check : reducedMerge1265 = Integer.Sparse.mergeBy masterLess reducedTerm1270 reducedTerm1271 := by decide +kernel

theorem reducedMerge1266Check : reducedMerge1266 = Integer.Sparse.mergeBy masterLess reducedTerm1272 reducedTerm1273 := by decide +kernel

theorem reducedMerge1267Check : reducedMerge1267 = Integer.Sparse.mergeBy masterLess reducedMerge1265 reducedMerge1266 := by decide +kernel

theorem reducedMerge1268Check : reducedMerge1268 = Integer.Sparse.mergeBy masterLess reducedMerge1264 reducedMerge1267 := by decide +kernel

theorem reducedMerge1269Check : reducedMerge1269 = Integer.Sparse.mergeBy masterLess reducedMerge1261 reducedMerge1268 := by decide +kernel

theorem reducedMerge1270Check : reducedMerge1270 = Integer.Sparse.mergeBy masterLess reducedTerm1275 reducedTerm1276 := by decide +kernel

theorem reducedMerge1271Check : reducedMerge1271 = Integer.Sparse.mergeBy masterLess reducedTerm1274 reducedMerge1270 := by decide +kernel

theorem reducedMerge1272Check : reducedMerge1272 = Integer.Sparse.mergeBy masterLess reducedTerm1277 reducedTerm1278 := by decide +kernel

theorem reducedMerge1273Check : reducedMerge1273 = Integer.Sparse.mergeBy masterLess reducedTerm1279 reducedTerm1280 := by decide +kernel

theorem reducedMerge1274Check : reducedMerge1274 = Integer.Sparse.mergeBy masterLess reducedMerge1272 reducedMerge1273 := by decide +kernel

theorem reducedMerge1275Check : reducedMerge1275 = Integer.Sparse.mergeBy masterLess reducedMerge1271 reducedMerge1274 := by decide +kernel

theorem reducedMerge1276Check : reducedMerge1276 = Integer.Sparse.mergeBy masterLess reducedTerm1281 reducedTerm1282 := by decide +kernel

theorem reducedMerge1277Check : reducedMerge1277 = Integer.Sparse.mergeBy masterLess reducedTerm1283 reducedTerm1284 := by decide +kernel

theorem reducedMerge1278Check : reducedMerge1278 = Integer.Sparse.mergeBy masterLess reducedMerge1276 reducedMerge1277 := by decide +kernel

theorem reducedMerge1279Check : reducedMerge1279 = Integer.Sparse.mergeBy masterLess reducedTerm1285 reducedTerm1286 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1280Check : reducedMerge1280 = Integer.Sparse.mergeBy masterLess reducedTerm1287 reducedTerm1288 := by decide +kernel

theorem reducedMerge1281Check : reducedMerge1281 = Integer.Sparse.mergeBy masterLess reducedMerge1279 reducedMerge1280 := by decide +kernel

theorem reducedMerge1282Check : reducedMerge1282 = Integer.Sparse.mergeBy masterLess reducedMerge1278 reducedMerge1281 := by decide +kernel

theorem reducedMerge1283Check : reducedMerge1283 = Integer.Sparse.mergeBy masterLess reducedMerge1275 reducedMerge1282 := by decide +kernel

theorem reducedMerge1284Check : reducedMerge1284 = Integer.Sparse.mergeBy masterLess reducedMerge1269 reducedMerge1283 := by decide +kernel

theorem reducedMerge1285Check : reducedMerge1285 = Integer.Sparse.mergeBy masterLess reducedTerm1290 reducedTerm1291 := by decide +kernel

theorem reducedMerge1286Check : reducedMerge1286 = Integer.Sparse.mergeBy masterLess reducedTerm1289 reducedMerge1285 := by decide +kernel

theorem reducedMerge1287Check : reducedMerge1287 = Integer.Sparse.mergeBy masterLess reducedTerm1292 reducedTerm1293 := by decide +kernel

theorem reducedMerge1288Check : reducedMerge1288 = Integer.Sparse.mergeBy masterLess reducedTerm1294 reducedTerm1295 := by decide +kernel

theorem reducedMerge1289Check : reducedMerge1289 = Integer.Sparse.mergeBy masterLess reducedMerge1287 reducedMerge1288 := by decide +kernel

theorem reducedMerge1290Check : reducedMerge1290 = Integer.Sparse.mergeBy masterLess reducedMerge1286 reducedMerge1289 := by decide +kernel

theorem reducedMerge1291Check : reducedMerge1291 = Integer.Sparse.mergeBy masterLess reducedTerm1296 reducedTerm1297 := by decide +kernel

theorem reducedMerge1292Check : reducedMerge1292 = Integer.Sparse.mergeBy masterLess reducedTerm1298 reducedTerm1299 := by decide +kernel

theorem reducedMerge1293Check : reducedMerge1293 = Integer.Sparse.mergeBy masterLess reducedMerge1291 reducedMerge1292 := by decide +kernel

theorem reducedMerge1294Check : reducedMerge1294 = Integer.Sparse.mergeBy masterLess reducedTerm1300 reducedTerm1301 := by decide +kernel

theorem reducedMerge1295Check : reducedMerge1295 = Integer.Sparse.mergeBy masterLess reducedTerm1302 reducedTerm1303 := by decide +kernel

theorem reducedMerge1296Check : reducedMerge1296 = Integer.Sparse.mergeBy masterLess reducedMerge1294 reducedMerge1295 := by decide +kernel

theorem reducedMerge1297Check : reducedMerge1297 = Integer.Sparse.mergeBy masterLess reducedMerge1293 reducedMerge1296 := by decide +kernel

theorem reducedMerge1298Check : reducedMerge1298 = Integer.Sparse.mergeBy masterLess reducedMerge1290 reducedMerge1297 := by decide +kernel

theorem reducedMerge1299Check : reducedMerge1299 = Integer.Sparse.mergeBy masterLess reducedTerm1305 reducedTerm1306 := by decide +kernel

theorem reducedMerge1300Check : reducedMerge1300 = Integer.Sparse.mergeBy masterLess reducedTerm1304 reducedMerge1299 := by decide +kernel

theorem reducedMerge1301Check : reducedMerge1301 = Integer.Sparse.mergeBy masterLess reducedTerm1307 reducedTerm1308 := by decide +kernel

theorem reducedMerge1302Check : reducedMerge1302 = Integer.Sparse.mergeBy masterLess reducedTerm1309 reducedTerm1310 := by decide +kernel

theorem reducedMerge1303Check : reducedMerge1303 = Integer.Sparse.mergeBy masterLess reducedMerge1301 reducedMerge1302 := by decide +kernel

theorem reducedMerge1304Check : reducedMerge1304 = Integer.Sparse.mergeBy masterLess reducedMerge1300 reducedMerge1303 := by decide +kernel

theorem reducedMerge1305Check : reducedMerge1305 = Integer.Sparse.mergeBy masterLess reducedTerm1311 reducedTerm1312 := by decide +kernel

theorem reducedMerge1306Check : reducedMerge1306 = Integer.Sparse.mergeBy masterLess reducedTerm1313 reducedTerm1314 := by decide +kernel

theorem reducedMerge1307Check : reducedMerge1307 = Integer.Sparse.mergeBy masterLess reducedMerge1305 reducedMerge1306 := by decide +kernel

theorem reducedMerge1308Check : reducedMerge1308 = Integer.Sparse.mergeBy masterLess reducedTerm1315 reducedTerm1316 := by decide +kernel

theorem reducedMerge1309Check : reducedMerge1309 = Integer.Sparse.mergeBy masterLess reducedTerm1317 reducedTerm1318 := by decide +kernel

theorem reducedMerge1310Check : reducedMerge1310 = Integer.Sparse.mergeBy masterLess reducedMerge1308 reducedMerge1309 := by decide +kernel

theorem reducedMerge1311Check : reducedMerge1311 = Integer.Sparse.mergeBy masterLess reducedMerge1307 reducedMerge1310 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1312Check : reducedMerge1312 = Integer.Sparse.mergeBy masterLess reducedMerge1304 reducedMerge1311 := by decide +kernel

theorem reducedMerge1313Check : reducedMerge1313 = Integer.Sparse.mergeBy masterLess reducedMerge1298 reducedMerge1312 := by decide +kernel

theorem reducedMerge1314Check : reducedMerge1314 = Integer.Sparse.mergeBy masterLess reducedMerge1284 reducedMerge1313 := by decide +kernel

theorem reducedMerge1315Check : reducedMerge1315 = Integer.Sparse.mergeBy masterLess reducedMerge1255 reducedMerge1314 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1229 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1229 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1229 (originalVector B) := by
  rw [reducedTermArithmetic1229, ← sound3189 B hB hF]
  change (-1174798139719680000000 : ℝ) * mixedMoment B node3189 node3189Labels =
    (37623398400 : ℝ) * (((-31225200000 : ℤ) : ℝ) * mixedMoment B node3189 node3189Labels + 0)
  ring

theorem reducedTermEval1230 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1230 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1230 (originalVector B) := by
  rw [reducedTermArithmetic1230, ← sound3196 B hB hF]
  change (6466249688175083520000 : ℝ) * mixedMoment B node3196 node3196Labels =
    (37623398400 : ℝ) * ((171867772800 : ℝ) * mixedMoment B node3196 node3196Labels + 0)
  ring

theorem reducedTermEval1231 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1231 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1231 (originalVector B) := by
  rw [reducedTermArithmetic1231, ← sound3197 B hB hF]
  change (1899117244195799040000 : ℝ) * mixedMoment B node3197 node3197Labels =
    (37623398400 : ℝ) * ((50477025600 : ℝ) * mixedMoment B node3197 node3197Labels + 0)
  ring

theorem reducedTermEval1232 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1232 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1232 (originalVector B) := by
  rw [reducedTermArithmetic1232, ← sound3198 B hB hF]
  change (419312052798750720000 : ℝ) * mixedMoment B node3198 node3198Labels =
    (37623398400 : ℝ) * ((11144980800 : ℝ) * mixedMoment B node3198 node3198Labels + 0)
  ring

theorem reducedTermEval1233 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1233 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1233 (originalVector B) := by
  rw [reducedTermArithmetic1233, ← sound3199 B hB hF]
  change (6894774206306058240000 : ℝ) * mixedMoment B node3199 node3199Labels =
    (37623398400 : ℝ) * ((183257613600 : ℝ) * mixedMoment B node3199 node3199Labels + 0)
  ring

theorem reducedTermEval1234 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1234 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1234 (originalVector B) := by
  rw [reducedTermArithmetic1234, ← sound3202 B hB hF]
  change (11475455859405619200000 : ℝ) * mixedMoment B node3202 node3202Labels =
    (37623398400 : ℝ) * ((305008488000 : ℝ) * mixedMoment B node3202 node3202Labels + 0)
  ring

theorem reducedTermEval1235 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1235 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1235 (originalVector B) := by
  rw [reducedTermArithmetic1235, ← sound3221 B hB hF]
  change (-12951213345010483200000 : ℝ) * mixedMoment B node3221 node3221Labels =
    (37623398400 : ℝ) * (((-344232948000 : ℤ) : ℝ) * mixedMoment B node3221 node3221Labels + 0)
  ring

theorem reducedTermEval1236 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1236 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1236 (originalVector B) := by
  rw [reducedTermArithmetic1236, ← sound3222 B hB hF]
  change (-12438782405973245952000 : ℝ) * mixedMoment B node3222 node3222Labels =
    (37623398400 : ℝ) * (((-330612941280 : ℤ) : ℝ) * mixedMoment B node3222 node3222Labels + 0)
  ring

theorem reducedTermEval1237 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1237 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1237 (originalVector B) := by
  rw [reducedTermArithmetic1237, ← sound3223_e B hB hF]
  change (4057256850042912768000 : ℝ) * mixedMoment B node3223 node3223Labels =
    (37623398400 : ℝ) * ((107838659520 : ℝ) * mixedMoment B node3223 node3223Labels + 0)
  ring

theorem reducedTermEval1238 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1238 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1238 (originalVector B) := by
  rw [reducedTermArithmetic1238, ← sound3224 B hB hF]
  change (3276781374141628416000 : ℝ) * mixedMoment B node3224 node3224Labels =
    (37623398400 : ℝ) * ((87094242240 : ℝ) * mixedMoment B node3224 node3224Labels + 0)
  ring

theorem reducedTermEval1239 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1239 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1239 (originalVector B) := by
  rw [reducedTermArithmetic1239, ← sound3225 B hB hF]
  change (1722459352110465024000 : ℝ) * mixedMoment B node3225 node3225Labels =
    (37623398400 : ℝ) * ((45781599360 : ℝ) * mixedMoment B node3225 node3225Labels + 0)
  ring

theorem reducedTermEval1240 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1240 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1240 (originalVector B) := by
  rw [reducedTermArithmetic1240, ← sound3226_e B hB hF]
  change (-4686317239001481216000 : ℝ) * mixedMoment B node3226 node3226Labels =
    (37623398400 : ℝ) * (((-124558584240 : ℤ) : ℝ) * mixedMoment B node3226 node3226Labels + 0)
  ring

theorem reducedTermEval1241 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1241 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1241 (originalVector B) := by
  rw [reducedTermArithmetic1241, ← sound3227_e B hB hF]
  change (-2883452798765629440000 : ℝ) * mixedMoment B node3227 node3227Labels =
    (37623398400 : ℝ) * (((-76639881600 : ℤ) : ℝ) * mixedMoment B node3227 node3227Labels + 0)
  ring

theorem reducedTermEval1242 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1242 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1242 (originalVector B) := by
  rw [reducedTermArithmetic1242, ← sound3228 B hB hF]
  change (7903823872994574336000 : ℝ) * mixedMoment B node3228 node3228Labels =
    (37623398400 : ℝ) * ((210077351040 : ℝ) * mixedMoment B node3228 node3228Labels + 0)
  ring

theorem reducedTermEval1243 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1243 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1243 (originalVector B) := by
  rw [reducedTermArithmetic1243, ← sound3229 B hB hF]
  change (25143534921037381632000 : ℝ) * mixedMoment B node3229 node3229Labels =
    (37623398400 : ℝ) * ((668295156480 : ℝ) * mixedMoment B node3229 node3229Labels + 0)
  ring

theorem reducedTermEval1244 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1244 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1244 (originalVector B) := by
  rw [reducedTermArithmetic1244, ← sound3230 B hB hF]
  change (9067699888990912512000 : ℝ) * mixedMoment B node3230 node3230Labels =
    (37623398400 : ℝ) * ((241012249680 : ℝ) * mixedMoment B node3230 node3230Labels + 0)
  ring

theorem reducedTermEval1245 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1245 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1245 (originalVector B) := by
  rw [reducedTermArithmetic1245, ← sound3231 B hB hF]
  change (2472915735452123136000 : ℝ) * mixedMoment B node3231 node3231Labels =
    (37623398400 : ℝ) * ((65728133040 : ℝ) * mixedMoment B node3231 node3231Labels + 0)
  ring

theorem reducedTermEval1246 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1246 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1246 (originalVector B) := by
  rw [reducedTermArithmetic1246, ← sound3255 B hB hF]
  change (1331003266183987200000 : ℝ) * mixedMoment B node3255 node3255Labels =
    (37623398400 : ℝ) * ((35377008000 : ℝ) * mixedMoment B node3255 node3255Labels + 0)
  ring

theorem reducedTermEval1247 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1247 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1247 (originalVector B) := by
  rw [reducedTermArithmetic1247, ← sound3257 B hB hF]
  change (5933039869919232000000 : ℝ) * mixedMoment B node3257 node3257Labels =
    (37623398400 : ℝ) * ((157695480000 : ℝ) * mixedMoment B node3257 node3257Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1248 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1248 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1248 (originalVector B) := by
  rw [reducedTermArithmetic1248, ← sound3258 B hB hF]
  change (-1531997227471011840000 : ℝ) * mixedMoment B node3258 node3258Labels =
    (37623398400 : ℝ) * (((-40719267600 : ℤ) : ℝ) * mixedMoment B node3258 node3258Labels + 0)
  ring

theorem reducedTermEval1249 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1249 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1249 (originalVector B) := by
  rw [reducedTermArithmetic1249, ← sound3259 B hB hF]
  change (9156607353476481024000 : ℝ) * mixedMoment B node3259 node3259Labels =
    (37623398400 : ℝ) * ((243375339360 : ℝ) * mixedMoment B node3259 node3259Labels + 0)
  ring

theorem reducedTermEval1250 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1250 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1250 (originalVector B) := by
  rw [reducedTermArithmetic1250, ← sound3260 B hB hF]
  change (1182595905074626560000 : ℝ) * mixedMoment B node3260 node3260Labels =
    (37623398400 : ℝ) * ((31432458400 : ℝ) * mixedMoment B node3260 node3260Labels + 0)
  ring

theorem reducedTermEval1251 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1251 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1251 (originalVector B) := by
  rw [reducedTermArithmetic1251, ← sound3261 B hB hF]
  change (270860476671590400000 : ℝ) * mixedMoment B node3261 node3261Labels =
    (37623398400 : ℝ) * ((7199256000 : ℝ) * mixedMoment B node3261 node3261Labels + 0)
  ring

theorem reducedTermEval1252 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1252 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1252 (originalVector B) := by
  rw [reducedTermArithmetic1252, ← sound3262 B hB hF]
  change (1979586319187312640000 : ℝ) * mixedMoment B node3262 node3262Labels =
    (37623398400 : ℝ) * ((52615829600 : ℝ) * mixedMoment B node3262 node3262Labels + 0)
  ring

theorem reducedTermEval1253 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1253 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1253 (originalVector B) := by
  rw [reducedTermArithmetic1253, ← sound3266 B hB hF]
  change (3863114615263002624000 : ℝ) * mixedMoment B node3266 node3266Labels =
    (37623398400 : ℝ) * ((102678513360 : ℝ) * mixedMoment B node3266 node3266Labels + 0)
  ring

theorem reducedTermEval1254 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1254 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1254 (originalVector B) := by
  rw [reducedTermArithmetic1254, ← sound3267 B hB hF]
  change (53914691091824640000 : ℝ) * mixedMoment B node3267 node3267Labels =
    (37623398400 : ℝ) * ((1433009600 : ℝ) * mixedMoment B node3267 node3267Labels + 0)
  ring

theorem reducedTermEval1255 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1255 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1255 (originalVector B) := by
  rw [reducedTermArithmetic1255, ← sound3268 B hB hF]
  change (-2204937138861047808000 : ℝ) * mixedMoment B node3268 node3268Labels =
    (37623398400 : ℝ) * (((-58605475120 : ℤ) : ℝ) * mixedMoment B node3268 node3268Labels + 0)
  ring

theorem reducedTermEval1256 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1256 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1256 (originalVector B) := by
  rw [reducedTermArithmetic1256, ← sound3271 B hB hF]
  change (-2066297949707894784000 : ℝ) * mixedMoment B node3271 node3271Labels =
    (37623398400 : ℝ) * (((-54920555760 : ℤ) : ℝ) * mixedMoment B node3271 node3271Labels + 0)
  ring

theorem reducedTermEval1257 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1257 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1257 (originalVector B) := by
  rw [reducedTermArithmetic1257, ← sound3272 B hB hF]
  change (-992147345927700480000 : ℝ) * mixedMoment B node3272 node3272Labels =
    (37623398400 : ℝ) * (((-26370487200 : ℤ) : ℝ) * mixedMoment B node3272 node3272Labels + 0)
  ring

theorem reducedTermEval1258 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1258 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1258 (originalVector B) := by
  rw [reducedTermArithmetic1258, ← sound3288 B hB hF]
  change (305084947161415680000 : ℝ) * mixedMoment B node3288 node3288Labels =
    (37623398400 : ℝ) * ((8108915200 : ℝ) * mixedMoment B node3288 node3288Labels + 0)
  ring

theorem reducedTermEval1259 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1259 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1259 (originalVector B) := by
  rw [reducedTermArithmetic1259, ← sound3289 B hB hF]
  change (2654462499211837440000 : ℝ) * mixedMoment B node3289 node3289Labels =
    (37623398400 : ℝ) * ((70553501600 : ℝ) * mixedMoment B node3289 node3289Labels + 0)
  ring

theorem reducedTermEval1260 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1260 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1260 (originalVector B) := by
  rw [reducedTermArithmetic1260, ← sound3290 B hB hF]
  change (1619043489526579200000 : ℝ) * mixedMoment B node3290 node3290Labels =
    (37623398400 : ℝ) * ((43032888000 : ℝ) * mixedMoment B node3290 node3290Labels + 0)
  ring

theorem reducedTermEval1261 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1261 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1261 (originalVector B) := by
  rw [reducedTermArithmetic1261, ← sound3291 B hB hF]
  change (-1521451825330913280000 : ℝ) * mixedMoment B node3291 node3291Labels =
    (37623398400 : ℝ) * (((-40438979200 : ℤ) : ℝ) * mixedMoment B node3291 node3291Labels + 0)
  ring

theorem reducedTermEval1262 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1262 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1262 (originalVector B) := by
  rw [reducedTermArithmetic1262, ← sound3294 B hB hF]
  change (-8946502007384309760000 : ℝ) * mixedMoment B node3294 node3294Labels =
    (37623398400 : ℝ) * (((-237790906400 : ℤ) : ℝ) * mixedMoment B node3294 node3294Labels + 0)
  ring

theorem reducedTermEval1263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1263 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1263 (originalVector B) := by
  rw [reducedTermArithmetic1263, ← sound3295 B hB hF]
  change (-3789395265230733312000 : ℝ) * mixedMoment B node3295 node3295Labels =
    (37623398400 : ℝ) * (((-100719111680 : ℤ) : ℝ) * mixedMoment B node3295 node3295Labels + 0)
  ring

theorem reducedTermEval1264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1264 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1264 (originalVector B) := by
  rw [reducedTermArithmetic1264, ← sound3296 B hB hF]
  change (-9536788940949946368000 : ℝ) * mixedMoment B node3296 node3296Labels =
    (37623398400 : ℝ) * (((-253480263520 : ℤ) : ℝ) * mixedMoment B node3296 node3296Labels + 0)
  ring

theorem reducedTermEval1265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1265 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1265 (originalVector B) := by
  rw [reducedTermArithmetic1265, ← sound3297 B hB hF]
  change (-1889903966198169600000 : ℝ) * mixedMoment B node3297 node3297Labels =
    (37623398400 : ℝ) * (((-50232144000 : ℤ) : ℝ) * mixedMoment B node3297 node3297Labels + 0)
  ring

theorem reducedTermEval1266 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1266 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1266 (originalVector B) := by
  rw [reducedTermArithmetic1266, ← sound3298 B hB hF]
  change (752859079780663296000 : ℝ) * mixedMoment B node3298 node3298Labels =
    (37623398400 : ℝ) * ((20010395440 : ℝ) * mixedMoment B node3298 node3298Labels + 0)
  ring

theorem reducedTermEval1267 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1267 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1267 (originalVector B) := by
  rw [reducedTermArithmetic1267, ← sound3302 B hB hF]
  change (-1389583379072286720000 : ℝ) * mixedMoment B node3302 node3302Labels =
    (37623398400 : ℝ) * (((-36934020800 : ℤ) : ℝ) * mixedMoment B node3302 node3302Labels + 0)
  ring

theorem reducedTermEval1268 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1268 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1268 (originalVector B) := by
  rw [reducedTermArithmetic1268, ← sound3303 B hB hF]
  change (-565455270900989952000 : ℝ) * mixedMoment B node3303 node3303Labels =
    (37623398400 : ℝ) * (((-15029351280 : ℤ) : ℝ) * mixedMoment B node3303 node3303Labels + 0)
  ring

theorem reducedTermEval1269 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1269 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1269 (originalVector B) := by
  rw [reducedTermArithmetic1269, ← sound3306 B hB hF]
  change (-186994987012915200000 : ℝ) * mixedMoment B node3306 node3306Labels =
    (37623398400 : ℝ) * (((-4970178000 : ℤ) : ℝ) * mixedMoment B node3306 node3306Labels + 0)
  ring

theorem reducedTermEval1270 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1270 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1270 (originalVector B) := by
  rw [reducedTermArithmetic1270, ← sound3365 B hB hF]
  change (4501291376384409600000 : ℝ) * mixedMoment B node3365 node3365Labels =
    (37623398400 : ℝ) * ((119640744000 : ℝ) * mixedMoment B node3365 node3365Labels + 0)
  ring

theorem reducedTermEval1271 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1271 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1271 (originalVector B) := by
  rw [reducedTermArithmetic1271, ← sound3375 B hB hF]
  change (654308882759024640000 : ℝ) * mixedMoment B node3375 node3375Labels =
    (37623398400 : ℝ) * ((17391009600 : ℝ) * mixedMoment B node3375 node3375Labels + 0)
  ring

theorem reducedTermEval1272 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1272 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1272 (originalVector B) := by
  rw [reducedTermArithmetic1272, ← sound3376 B hB hF]
  change (-4735033992735621120000 : ℝ) * mixedMoment B node3376 node3376Labels =
    (37623398400 : ℝ) * (((-125853436800 : ℤ) : ℝ) * mixedMoment B node3376 node3376Labels + 0)
  ring

theorem reducedTermEval1273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1273 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1273 (originalVector B) := by
  rw [reducedTermArithmetic1273, ← sound3378 B hB hF]
  change (4935862034835701760000 : ℝ) * mixedMoment B node3378 node3378Labels =
    (37623398400 : ℝ) * ((131191286400 : ℝ) * mixedMoment B node3378 node3378Labels + 0)
  ring

theorem reducedTermEval1274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1274 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1274 (originalVector B) := by
  rw [reducedTermArithmetic1274, ← sound3379 B hB hF]
  change (-379671498467573760000 : ℝ) * mixedMoment B node3379 node3379Labels =
    (37623398400 : ℝ) * (((-10091366400 : ℤ) : ℝ) * mixedMoment B node3379 node3379Labels + 0)
  ring

theorem reducedTermEval1275 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1275 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1275 (originalVector B) := by
  rw [reducedTermArithmetic1275, ← sound3380 B hB hF]
  change (2452540759969628160000 : ℝ) * mixedMoment B node3380 node3380Labels =
    (37623398400 : ℝ) * ((65186582400 : ℝ) * mixedMoment B node3380 node3380Labels + 0)
  ring

theorem reducedTermEval1276 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1276 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1276 (originalVector B) := by
  rw [reducedTermArithmetic1276, ← sound3388 B hB hF]
  change (28541892592926720000 : ℝ) * mixedMoment B node3388 node3388Labels =
    (37623398400 : ℝ) * ((758620800 : ℝ) * mixedMoment B node3388 node3388Labels + 0)
  ring

theorem reducedTermEval1277 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1277 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1277 (originalVector B) := by
  rw [reducedTermArithmetic1277, ← sound3390 B hB hF]
  change (-2426340427298242560000 : ℝ) * mixedMoment B node3390 node3390Labels =
    (37623398400 : ℝ) * (((-64490198400 : ℤ) : ℝ) * mixedMoment B node3390 node3390Labels + 0)
  ring

theorem reducedTermEval1278 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1278 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1278 (originalVector B) := by
  rw [reducedTermArithmetic1278, ← sound3391 B hB hF]
  change (-3915341740423249920000 : ℝ) * mixedMoment B node3391 node3391Labels =
    (37623398400 : ℝ) * (((-104066668800 : ℤ) : ℝ) * mixedMoment B node3391 node3391Labels + 0)
  ring

theorem reducedTermEval1279 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1279 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1279 (originalVector B) := by
  rw [reducedTermArithmetic1279, ← sound3392 B hB hF]
  change (-57083785185853440000 : ℝ) * mixedMoment B node3392 node3392Labels =
    (37623398400 : ℝ) * (((-1517241600 : ℤ) : ℝ) * mixedMoment B node3392 node3392Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1226 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1226 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1226 (originalVector B) := by
  rw [reducedMerge1226Check, Integer.Sparse.eval_mergeBy, reducedTermEval1230 B hB hF, reducedTermEval1231 B hB hF]
  rw [originalMerge1226, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1227 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1227 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1227 (originalVector B) := by
  rw [reducedMerge1227Check, Integer.Sparse.eval_mergeBy, reducedTermEval1229 B hB hF, reducedMergeEval1226 B hB hF]
  rw [originalMerge1227, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1228 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1228 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1228 (originalVector B) := by
  rw [reducedMerge1228Check, Integer.Sparse.eval_mergeBy, reducedTermEval1232 B hB hF, reducedTermEval1233 B hB hF]
  rw [originalMerge1228, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1229 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1229 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1229 (originalVector B) := by
  rw [reducedMerge1229Check, Integer.Sparse.eval_mergeBy, reducedTermEval1234 B hB hF, reducedTermEval1235 B hB hF]
  rw [originalMerge1229, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1230 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1230 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1230 (originalVector B) := by
  rw [reducedMerge1230Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1228 B hB hF, reducedMergeEval1229 B hB hF]
  rw [originalMerge1230, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1231 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1231 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1231 (originalVector B) := by
  rw [reducedMerge1231Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1227 B hB hF, reducedMergeEval1230 B hB hF]
  rw [originalMerge1231, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1232 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1232 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1232 (originalVector B) := by
  rw [reducedMerge1232Check, Integer.Sparse.eval_mergeBy, reducedTermEval1236 B hB hF, reducedTermEval1237 B hB hF]
  rw [originalMerge1232, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1233 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1233 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1233 (originalVector B) := by
  rw [reducedMerge1233Check, Integer.Sparse.eval_mergeBy, reducedTermEval1238 B hB hF, reducedTermEval1239 B hB hF]
  rw [originalMerge1233, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1234 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1234 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1234 (originalVector B) := by
  rw [reducedMerge1234Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1232 B hB hF, reducedMergeEval1233 B hB hF]
  rw [originalMerge1234, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1235 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1235 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1235 (originalVector B) := by
  rw [reducedMerge1235Check, Integer.Sparse.eval_mergeBy, reducedTermEval1240 B hB hF, reducedTermEval1241 B hB hF]
  rw [originalMerge1235, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1236 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1236 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1236 (originalVector B) := by
  rw [reducedMerge1236Check, Integer.Sparse.eval_mergeBy, reducedTermEval1242 B hB hF, reducedTermEval1243 B hB hF]
  rw [originalMerge1236, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1237 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1237 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1237 (originalVector B) := by
  rw [reducedMerge1237Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1235 B hB hF, reducedMergeEval1236 B hB hF]
  rw [originalMerge1237, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1238 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1238 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1238 (originalVector B) := by
  rw [reducedMerge1238Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1234 B hB hF, reducedMergeEval1237 B hB hF]
  rw [originalMerge1238, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1239 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1239 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1239 (originalVector B) := by
  rw [reducedMerge1239Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1231 B hB hF, reducedMergeEval1238 B hB hF]
  rw [originalMerge1239, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1240 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1240 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1240 (originalVector B) := by
  rw [reducedMerge1240Check, Integer.Sparse.eval_mergeBy, reducedTermEval1245 B hB hF, reducedTermEval1246 B hB hF]
  rw [originalMerge1240, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1241 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1241 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1241 (originalVector B) := by
  rw [reducedMerge1241Check, Integer.Sparse.eval_mergeBy, reducedTermEval1244 B hB hF, reducedMergeEval1240 B hB hF]
  rw [originalMerge1241, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1242 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1242 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1242 (originalVector B) := by
  rw [reducedMerge1242Check, Integer.Sparse.eval_mergeBy, reducedTermEval1247 B hB hF, reducedTermEval1248 B hB hF]
  rw [originalMerge1242, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1243 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1243 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1243 (originalVector B) := by
  rw [reducedMerge1243Check, Integer.Sparse.eval_mergeBy, reducedTermEval1249 B hB hF, reducedTermEval1250 B hB hF]
  rw [originalMerge1243, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1244 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1244 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1244 (originalVector B) := by
  rw [reducedMerge1244Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1242 B hB hF, reducedMergeEval1243 B hB hF]
  rw [originalMerge1244, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1245 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1245 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1245 (originalVector B) := by
  rw [reducedMerge1245Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1241 B hB hF, reducedMergeEval1244 B hB hF]
  rw [originalMerge1245, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1246 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1246 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1246 (originalVector B) := by
  rw [reducedMerge1246Check, Integer.Sparse.eval_mergeBy, reducedTermEval1251 B hB hF, reducedTermEval1252 B hB hF]
  rw [originalMerge1246, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1247 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1247 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1247 (originalVector B) := by
  rw [reducedMerge1247Check, Integer.Sparse.eval_mergeBy, reducedTermEval1253 B hB hF, reducedTermEval1254 B hB hF]
  rw [originalMerge1247, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1280 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1280 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1280 (originalVector B) := by
  rw [reducedTermArithmetic1280, ← sound3394 B hB hF]
  change (6542432374534963200000 : ℝ) * mixedMoment B node3394 node3394Labels =
    (37623398400 : ℝ) * ((173892648000 : ℝ) * mixedMoment B node3394 node3394Labels + 0)
  ring

theorem reducedTermEval1281 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1281 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1281 (originalVector B) := by
  rw [reducedTermArithmetic1281, ← sound3395 B hB hF]
  change (16453451164259450880000 : ℝ) * mixedMoment B node3395 node3395Labels =
    (37623398400 : ℝ) * ((437319643200 : ℝ) * mixedMoment B node3395 node3395Labels + 0)
  ring

theorem reducedTermEval1282 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1282 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1282 (originalVector B) := by
  rw [reducedTermArithmetic1282, ← sound3396 B hB hF]
  change (10440815232685178880000 : ℝ) * mixedMoment B node3396 node3396Labels =
    (37623398400 : ℝ) * ((277508563200 : ℝ) * mixedMoment B node3396 node3396Labels + 0)
  ring

theorem reducedTermEval1283 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1283 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1283 (originalVector B) := by
  rw [reducedTermArithmetic1283, ← sound3397 B hB hF]
  change (-684291540819640320000 : ℝ) * mixedMoment B node3397 node3397Labels =
    (37623398400 : ℝ) * (((-18187924800 : ℤ) : ℝ) * mixedMoment B node3397 node3397Labels + 0)
  ring

theorem reducedTermEval1284 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1284 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1284 (originalVector B) := by
  rw [reducedTermArithmetic1284, ← sound3406 B hB hF]
  change (652996879610019840000 : ℝ) * mixedMoment B node3406 node3406Labels =
    (37623398400 : ℝ) * ((17356137600 : ℝ) * mixedMoment B node3406 node3406Labels + 0)
  ring

theorem reducedTermEval1285 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1285 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1285 (originalVector B) := by
  rw [reducedTermArithmetic1285, ← sound3407 B hB hF]
  change (3344441963460820992000 : ℝ) * mixedMoment B node3407 node3407Labels =
    (37623398400 : ℝ) * ((88892606880 : ℝ) * mixedMoment B node3407 node3407Labels + 0)
  ring

theorem reducedTermEval1286 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1286 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1286 (originalVector B) := by
  rw [reducedTermArithmetic1286, ← sound3408 B hB hF]
  change (-1985415998552211456000 : ℝ) * mixedMoment B node3408 node3408Labels =
    (37623398400 : ℝ) * (((-52770777840 : ℤ) : ℝ) * mixedMoment B node3408 node3408Labels + 0)
  ring

theorem reducedTermEval1287 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1287 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1287 (originalVector B) := by
  rw [reducedTermArithmetic1287, ← sound3413 B hB hF]
  change (-2989726119329660928000 : ℝ) * mixedMoment B node3413 node3413Labels =
    (37623398400 : ℝ) * (((-79464541920 : ℤ) : ℝ) * mixedMoment B node3413 node3413Labels + 0)
  ring

theorem reducedTermEval1288 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1288 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1288 (originalVector B) := by
  rw [reducedTermArithmetic1288, ← sound3414 B hB hF]
  change (355417517501448192000 : ℝ) * mixedMoment B node3414 node3414Labels =
    (37623398400 : ℝ) * ((9446714880 : ℝ) * mixedMoment B node3414 node3414Labels + 0)
  ring

theorem reducedTermEval1289 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1289 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1289 (originalVector B) := by
  rw [reducedTermArithmetic1289, ← sound3415 B hB hF]
  change (-1559990074286407680000 : ℝ) * mixedMoment B node3415 node3415Labels =
    (37623398400 : ℝ) * (((-41463295200 : ℤ) : ℝ) * mixedMoment B node3415 node3415Labels + 0)
  ring

theorem reducedTermEval1290 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1290 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1290 (originalVector B) := by
  rw [reducedTermArithmetic1290, ← sound3418 B hB hF]
  change (-354715844131160064000 : ℝ) * mixedMoment B node3418 node3418Labels =
    (37623398400 : ℝ) * (((-9428064960 : ℤ) : ℝ) * mixedMoment B node3418 node3418Labels + 0)
  ring

theorem reducedTermEval1291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1291 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1291 (originalVector B) := by
  rw [reducedTermArithmetic1291, ← sound3419 B hB hF]
  change (814999240525381632000 : ℝ) * mixedMoment B node3419 node3419Labels =
    (37623398400 : ℝ) * ((21662031480 : ℝ) * mixedMoment B node3419 node3419Labels + 0)
  ring

theorem reducedTermEval1292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1292 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1292 (originalVector B) := by
  rw [reducedTermArithmetic1292, ← sound3451 B hB hF]
  change (744619799330684928000 : ℝ) * mixedMoment B node3451 node3451Labels =
    (37623398400 : ℝ) * ((19791401920 : ℝ) * mixedMoment B node3451 node3451Labels + 0)
  ring

theorem reducedTermEval1293 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1293 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1293 (originalVector B) := by
  rw [reducedTermArithmetic1293, ← sound3452 B hB hF]
  change (4783674936826920960000 : ℝ) * mixedMoment B node3452 node3452Labels =
    (37623398400 : ℝ) * ((127146274400 : ℝ) * mixedMoment B node3452 node3452Labels + 0)
  ring

theorem reducedTermEval1294 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1294 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1294 (originalVector B) := by
  rw [reducedTermArithmetic1294, ← sound3454 B hB hF]
  change (5808432531870646272000 : ℝ) * mixedMoment B node3454 node3454Labels =
    (37623398400 : ℝ) * ((154383516080 : ℝ) * mixedMoment B node3454 node3454Labels + 0)
  ring

theorem reducedTermEval1295 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1295 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1295 (originalVector B) := by
  rw [reducedTermArithmetic1295, ← sound3458 B hB hF]
  change (23220776228880384000 : ℝ) * mixedMoment B node3458 node3458Labels =
    (37623398400 : ℝ) * ((617189760 : ℝ) * mixedMoment B node3458 node3458Labels + 0)
  ring

theorem reducedTermEval1296 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1296 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1296 (originalVector B) := by
  rw [reducedTermArithmetic1296, ← sound3461 B hB hF]
  change (2229127337632333824000 : ℝ) * mixedMoment B node3461 node3461Labels =
    (37623398400 : ℝ) * ((59248431360 : ℝ) * mixedMoment B node3461 node3461Labels + 0)
  ring

theorem reducedTermEval1297 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1297 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1297 (originalVector B) := by
  rw [reducedTermArithmetic1297, ← sound3462 B hB hF]
  change (-2370794412740640768000 : ℝ) * mixedMoment B node3462 node3462Labels =
    (37623398400 : ℝ) * (((-63013829520 : ℤ) : ℝ) * mixedMoment B node3462 node3462Labels + 0)
  ring

theorem reducedTermEval1298 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1298 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1298 (originalVector B) := by
  rw [reducedTermArithmetic1298, ← sound3463 B hB hF]
  change (-3066113985645182976000 : ℝ) * mixedMoment B node3463 node3463Labels =
    (37623398400 : ℝ) * (((-81494870640 : ℤ) : ℝ) * mixedMoment B node3463 node3463Labels + 0)
  ring

theorem reducedTermEval1299 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1299 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1299 (originalVector B) := by
  rw [reducedTermArithmetic1299, ← sound3464 B hB hF]
  change (3058373744961454080000 : ℝ) * mixedMoment B node3464 node3464Labels =
    (37623398400 : ℝ) * ((81289141200 : ℝ) * mixedMoment B node3464 node3464Labels + 0)
  ring

theorem reducedTermEval1300 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1300 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1300 (originalVector B) := by
  rw [reducedTermArithmetic1300, ← sound3465 B hB hF]
  change (-722635406229897216000 : ℝ) * mixedMoment B node3465 node3465Labels =
    (37623398400 : ℝ) * (((-19207074240 : ℤ) : ℝ) * mixedMoment B node3465 node3465Labels + 0)
  ring

theorem reducedTermEval1301 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1301 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1301 (originalVector B) := by
  rw [reducedTermArithmetic1301, ← sound3466 B hB hF]
  change (-3632663000341315584000 : ℝ) * mixedMoment B node3466 node3466Labels =
    (37623398400 : ℝ) * (((-96553292760 : ℤ) : ℝ) * mixedMoment B node3466 node3466Labels + 0)
  ring

theorem reducedTermEval1302 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1302 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1302 (originalVector B) := by
  rw [reducedTermArithmetic1302, ← sound3472 B hB hF]
  change (506711554922151936000 : ℝ) * mixedMoment B node3472 node3472Labels =
    (37623398400 : ℝ) * ((13467990040 : ℝ) * mixedMoment B node3472 node3472Labels + 0)
  ring

theorem reducedTermEval1303 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1303 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1303 (originalVector B) := by
  rw [reducedTermArithmetic1303, ← sound3474 B hB hF]
  change (-1835451633733337088000 : ℝ) * mixedMoment B node3474 node3474Labels =
    (37623398400 : ℝ) * (((-48784844320 : ℤ) : ℝ) * mixedMoment B node3474 node3474Labels + 0)
  ring

theorem reducedTermEval1304 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1304 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1304 (originalVector B) := by
  rw [reducedTermArithmetic1304, ← sound3475 B hB hF]
  change (-4633408883520700416000 : ℝ) * mixedMoment B node3475 node3475Labels =
    (37623398400 : ℝ) * (((-123152322240 : ℤ) : ℝ) * mixedMoment B node3475 node3475Labels + 0)
  ring

theorem reducedTermEval1305 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1305 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1305 (originalVector B) := by
  rw [reducedTermArithmetic1305, ← sound3476 B hB hF]
  change (1856913308405858304000 : ℝ) * mixedMoment B node3476 node3476Labels =
    (37623398400 : ℝ) * ((49355278560 : ℝ) * mixedMoment B node3476 node3476Labels + 0)
  ring

theorem reducedTermEval1306 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1306 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1306 (originalVector B) := by
  rw [reducedTermArithmetic1306, ← sound3480 B hB hF]
  change (-4726817018446086144000 : ℝ) * mixedMoment B node3480 node3480Labels =
    (37623398400 : ℝ) * (((-125635036160 : ℤ) : ℝ) * mixedMoment B node3480 node3480Labels + 0)
  ring

theorem reducedTermEval1307 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1307 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1307 (originalVector B) := by
  rw [reducedTermArithmetic1307, ← sound3488 B hB hF]
  change (-416003421044736000000 : ℝ) * mixedMoment B node3488 node3488Labels =
    (37623398400 : ℝ) * (((-11057040000 : ℤ) : ℝ) * mixedMoment B node3488 node3488Labels + 0)
  ring

theorem reducedTermEval1308 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1308 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1308 (originalVector B) := by
  rw [reducedTermArithmetic1308, ← sound3493 B hB hF]
  change (4958849630270914560000 : ℝ) * mixedMoment B node3493 node3493Labels =
    (37623398400 : ℝ) * ((131802278400 : ℝ) * mixedMoment B node3493 node3493Labels + 0)
  ring

theorem reducedTermEval1309 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1309 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1309 (originalVector B) := by
  rw [reducedTermArithmetic1309, ← sound3496 B hB hF]
  change (-8093713655448207360000 : ℝ) * mixedMoment B node3496 node3496Labels =
    (37623398400 : ℝ) * (((-215124470400 : ℤ) : ℝ) * mixedMoment B node3496 node3496Labels + 0)
  ring

theorem reducedTermEval1310 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1310 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1310 (originalVector B) := by
  rw [reducedTermArithmetic1310, ← sound3497 B hB hF]
  change (-416003421044736000000 : ℝ) * mixedMoment B node3497 node3497Labels =
    (37623398400 : ℝ) * (((-11057040000 : ℤ) : ℝ) * mixedMoment B node3497 node3497Labels + 0)
  ring

theorem reducedTermEval1311 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1311 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1311 (originalVector B) := by
  rw [reducedTermArithmetic1311, ← sound3505 B hB hF]
  change (7799955337720627200000 : ℝ) * mixedMoment B node3505 node3505Labels =
    (37623398400 : ℝ) * ((207316608000 : ℝ) * mixedMoment B node3505 node3505Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1248 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1248 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1248 (originalVector B) := by
  rw [reducedMerge1248Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1246 B hB hF, reducedMergeEval1247 B hB hF]
  rw [originalMerge1248, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1249 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1249 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1249 (originalVector B) := by
  rw [reducedMerge1249Check, Integer.Sparse.eval_mergeBy, reducedTermEval1255 B hB hF, reducedTermEval1256 B hB hF]
  rw [originalMerge1249, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1250 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1250 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1250 (originalVector B) := by
  rw [reducedMerge1250Check, Integer.Sparse.eval_mergeBy, reducedTermEval1257 B hB hF, reducedTermEval1258 B hB hF]
  rw [originalMerge1250, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1251 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1251 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1251 (originalVector B) := by
  rw [reducedMerge1251Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1249 B hB hF, reducedMergeEval1250 B hB hF]
  rw [originalMerge1251, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1252 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1252 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1252 (originalVector B) := by
  rw [reducedMerge1252Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1248 B hB hF, reducedMergeEval1251 B hB hF]
  rw [originalMerge1252, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1253 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1253 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1253 (originalVector B) := by
  rw [reducedMerge1253Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1245 B hB hF, reducedMergeEval1252 B hB hF]
  rw [originalMerge1253, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1254 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1254 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1254 (originalVector B) := by
  rw [reducedMerge1254Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1239 B hB hF, reducedMergeEval1253 B hB hF]
  rw [originalMerge1254, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1255 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1255 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1255 (originalVector B) := by
  rw [reducedMerge1255Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1225_e B hB hF, reducedMergeEval1254 B hB hF]
  rw [originalMerge1255, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1256 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1256 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1256 (originalVector B) := by
  rw [reducedMerge1256Check, Integer.Sparse.eval_mergeBy, reducedTermEval1260 B hB hF, reducedTermEval1261 B hB hF]
  rw [originalMerge1256, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1257 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1257 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1257 (originalVector B) := by
  rw [reducedMerge1257Check, Integer.Sparse.eval_mergeBy, reducedTermEval1259 B hB hF, reducedMergeEval1256 B hB hF]
  rw [originalMerge1257, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1258 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1258 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1258 (originalVector B) := by
  rw [reducedMerge1258Check, Integer.Sparse.eval_mergeBy, reducedTermEval1262 B hB hF, reducedTermEval1263 B hB hF]
  rw [originalMerge1258, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1259 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1259 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1259 (originalVector B) := by
  rw [reducedMerge1259Check, Integer.Sparse.eval_mergeBy, reducedTermEval1264 B hB hF, reducedTermEval1265 B hB hF]
  rw [originalMerge1259, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1260 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1260 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1260 (originalVector B) := by
  rw [reducedMerge1260Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1258 B hB hF, reducedMergeEval1259 B hB hF]
  rw [originalMerge1260, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1261 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1261 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1261 (originalVector B) := by
  rw [reducedMerge1261Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1257 B hB hF, reducedMergeEval1260 B hB hF]
  rw [originalMerge1261, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1262 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1262 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1262 (originalVector B) := by
  rw [reducedMerge1262Check, Integer.Sparse.eval_mergeBy, reducedTermEval1266 B hB hF, reducedTermEval1267 B hB hF]
  rw [originalMerge1262, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1263 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1263 (originalVector B) := by
  rw [reducedMerge1263Check, Integer.Sparse.eval_mergeBy, reducedTermEval1268 B hB hF, reducedTermEval1269 B hB hF]
  rw [originalMerge1263, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1264 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1264 (originalVector B) := by
  rw [reducedMerge1264Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1262 B hB hF, reducedMergeEval1263 B hB hF]
  rw [originalMerge1264, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1265 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1265 (originalVector B) := by
  rw [reducedMerge1265Check, Integer.Sparse.eval_mergeBy, reducedTermEval1270 B hB hF, reducedTermEval1271 B hB hF]
  rw [originalMerge1265, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1266 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1266 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1266 (originalVector B) := by
  rw [reducedMerge1266Check, Integer.Sparse.eval_mergeBy, reducedTermEval1272 B hB hF, reducedTermEval1273 B hB hF]
  rw [originalMerge1266, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1267 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1267 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1267 (originalVector B) := by
  rw [reducedMerge1267Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1265 B hB hF, reducedMergeEval1266 B hB hF]
  rw [originalMerge1267, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1268 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1268 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1268 (originalVector B) := by
  rw [reducedMerge1268Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1264 B hB hF, reducedMergeEval1267 B hB hF]
  rw [originalMerge1268, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1269 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1269 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1269 (originalVector B) := by
  rw [reducedMerge1269Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1261 B hB hF, reducedMergeEval1268 B hB hF]
  rw [originalMerge1269, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1270 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1270 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1270 (originalVector B) := by
  rw [reducedMerge1270Check, Integer.Sparse.eval_mergeBy, reducedTermEval1275 B hB hF, reducedTermEval1276 B hB hF]
  rw [originalMerge1270, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1271 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1271 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1271 (originalVector B) := by
  rw [reducedMerge1271Check, Integer.Sparse.eval_mergeBy, reducedTermEval1274 B hB hF, reducedMergeEval1270 B hB hF]
  rw [originalMerge1271, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1272 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1272 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1272 (originalVector B) := by
  rw [reducedMerge1272Check, Integer.Sparse.eval_mergeBy, reducedTermEval1277 B hB hF, reducedTermEval1278 B hB hF]
  rw [originalMerge1272, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1273 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1273 (originalVector B) := by
  rw [reducedMerge1273Check, Integer.Sparse.eval_mergeBy, reducedTermEval1279 B hB hF, reducedTermEval1280 B hB hF]
  rw [originalMerge1273, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1274 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1274 (originalVector B) := by
  rw [reducedMerge1274Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1272 B hB hF, reducedMergeEval1273 B hB hF]
  rw [originalMerge1274, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1275 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1275 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1275 (originalVector B) := by
  rw [reducedMerge1275Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1271 B hB hF, reducedMergeEval1274 B hB hF]
  rw [originalMerge1275, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1276 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1276 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1276 (originalVector B) := by
  rw [reducedMerge1276Check, Integer.Sparse.eval_mergeBy, reducedTermEval1281 B hB hF, reducedTermEval1282 B hB hF]
  rw [originalMerge1276, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1277 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1277 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1277 (originalVector B) := by
  rw [reducedMerge1277Check, Integer.Sparse.eval_mergeBy, reducedTermEval1283 B hB hF, reducedTermEval1284 B hB hF]
  rw [originalMerge1277, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1278 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1278 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1278 (originalVector B) := by
  rw [reducedMerge1278Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1276 B hB hF, reducedMergeEval1277 B hB hF]
  rw [originalMerge1278, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1279 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1279 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1279 (originalVector B) := by
  rw [reducedMerge1279Check, Integer.Sparse.eval_mergeBy, reducedTermEval1285 B hB hF, reducedTermEval1286 B hB hF]
  rw [originalMerge1279, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1312 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1312 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1312 (originalVector B) := by
  rw [reducedTermArithmetic1312, ← sound3506 B hB hF]
  change (-3146577964923617280000 : ℝ) * mixedMoment B node3506 node3506Labels =
    (37623398400 : ℝ) * (((-83633539200 : ℤ) : ℝ) * mixedMoment B node3506 node3506Labels + 0)
  ring

theorem reducedTermEval1313 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1313 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1313 (originalVector B) := by
  rw [reducedTermArithmetic1313, ← sound3508 B hB hF]
  change (-1421726643557498880000 : ℝ) * mixedMoment B node3508 node3508Labels =
    (37623398400 : ℝ) * (((-37788363200 : ℤ) : ℝ) * mixedMoment B node3508 node3508Labels + 0)
  ring

theorem reducedTermEval1314 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1314 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1314 (originalVector B) := by
  rw [reducedTermArithmetic1314, ← sound3509 B hB hF]
  change (7390298065975050240000 : ℝ) * mixedMoment B node3509 node3509Labels =
    (37623398400 : ℝ) * ((196428243600 : ℝ) * mixedMoment B node3509 node3509Labels + 0)
  ring

theorem reducedTermEval1315 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1315 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1315 (originalVector B) := by
  rw [reducedTermArithmetic1315, ← sound3510 B hB hF]
  change (-1331003266183987200000 : ℝ) * mixedMoment B node3510 node3510Labels =
    (37623398400 : ℝ) * (((-35377008000 : ℤ) : ℝ) * mixedMoment B node3510 node3510Labels + 0)
  ring

theorem reducedTermEval1316 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1316 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1316 (originalVector B) := by
  rw [reducedTermArithmetic1316, ← sound3511 B hB hF]
  change (-270860476671590400000 : ℝ) * mixedMoment B node3511 node3511Labels =
    (37623398400 : ℝ) * (((-7199256000 : ℤ) : ℝ) * mixedMoment B node3511 node3511Labels + 0)
  ring

theorem reducedTermEval1317 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1317 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1317 (originalVector B) := by
  rw [reducedTermArithmetic1317, ← sound3512 B hB hF]
  change (-3141806478252244992000 : ℝ) * mixedMoment B node3512 node3512Labels =
    (37623398400 : ℝ) * (((-83506716880 : ℤ) : ℝ) * mixedMoment B node3512 node3512Labels + 0)
  ring

theorem reducedTermEval1318 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1318 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1318 (originalVector B) := by
  rw [reducedTermArithmetic1318, ← sound3516 B hB hF]
  change (1646462429022781440000 : ℝ) * mixedMoment B node3516 node3516Labels =
    (37623398400 : ℝ) * ((43761661600 : ℝ) * mixedMoment B node3516 node3516Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1280 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1280 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1280 (originalVector B) := by
  rw [reducedMerge1280Check, Integer.Sparse.eval_mergeBy, reducedTermEval1287 B hB hF, reducedTermEval1288 B hB hF]
  rw [originalMerge1280, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1281 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1281 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1281 (originalVector B) := by
  rw [reducedMerge1281Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1279 B hB hF, reducedMergeEval1280 B hB hF]
  rw [originalMerge1281, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1282 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1282 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1282 (originalVector B) := by
  rw [reducedMerge1282Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1278 B hB hF, reducedMergeEval1281 B hB hF]
  rw [originalMerge1282, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1283 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1283 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1283 (originalVector B) := by
  rw [reducedMerge1283Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1275 B hB hF, reducedMergeEval1282 B hB hF]
  rw [originalMerge1283, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1284 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1284 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1284 (originalVector B) := by
  rw [reducedMerge1284Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1269 B hB hF, reducedMergeEval1283 B hB hF]
  rw [originalMerge1284, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1285 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1285 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1285 (originalVector B) := by
  rw [reducedMerge1285Check, Integer.Sparse.eval_mergeBy, reducedTermEval1290 B hB hF, reducedTermEval1291 B hB hF]
  rw [originalMerge1285, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1286 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1286 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1286 (originalVector B) := by
  rw [reducedMerge1286Check, Integer.Sparse.eval_mergeBy, reducedTermEval1289 B hB hF, reducedMergeEval1285 B hB hF]
  rw [originalMerge1286, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1287 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1287 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1287 (originalVector B) := by
  rw [reducedMerge1287Check, Integer.Sparse.eval_mergeBy, reducedTermEval1292 B hB hF, reducedTermEval1293 B hB hF]
  rw [originalMerge1287, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1288 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1288 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1288 (originalVector B) := by
  rw [reducedMerge1288Check, Integer.Sparse.eval_mergeBy, reducedTermEval1294 B hB hF, reducedTermEval1295 B hB hF]
  rw [originalMerge1288, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1289 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1289 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1289 (originalVector B) := by
  rw [reducedMerge1289Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1287 B hB hF, reducedMergeEval1288 B hB hF]
  rw [originalMerge1289, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1290 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1290 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1290 (originalVector B) := by
  rw [reducedMerge1290Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1286 B hB hF, reducedMergeEval1289 B hB hF]
  rw [originalMerge1290, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1291 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1291 (originalVector B) := by
  rw [reducedMerge1291Check, Integer.Sparse.eval_mergeBy, reducedTermEval1296 B hB hF, reducedTermEval1297 B hB hF]
  rw [originalMerge1291, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1292 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1292 (originalVector B) := by
  rw [reducedMerge1292Check, Integer.Sparse.eval_mergeBy, reducedTermEval1298 B hB hF, reducedTermEval1299 B hB hF]
  rw [originalMerge1292, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1293 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1293 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1293 (originalVector B) := by
  rw [reducedMerge1293Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1291 B hB hF, reducedMergeEval1292 B hB hF]
  rw [originalMerge1293, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1294 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1294 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1294 (originalVector B) := by
  rw [reducedMerge1294Check, Integer.Sparse.eval_mergeBy, reducedTermEval1300 B hB hF, reducedTermEval1301 B hB hF]
  rw [originalMerge1294, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1295 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1295 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1295 (originalVector B) := by
  rw [reducedMerge1295Check, Integer.Sparse.eval_mergeBy, reducedTermEval1302 B hB hF, reducedTermEval1303 B hB hF]
  rw [originalMerge1295, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1296 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1296 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1296 (originalVector B) := by
  rw [reducedMerge1296Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1294 B hB hF, reducedMergeEval1295 B hB hF]
  rw [originalMerge1296, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1297 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1297 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1297 (originalVector B) := by
  rw [reducedMerge1297Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1293 B hB hF, reducedMergeEval1296 B hB hF]
  rw [originalMerge1297, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1298 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1298 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1298 (originalVector B) := by
  rw [reducedMerge1298Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1290 B hB hF, reducedMergeEval1297 B hB hF]
  rw [originalMerge1298, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1299 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1299 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1299 (originalVector B) := by
  rw [reducedMerge1299Check, Integer.Sparse.eval_mergeBy, reducedTermEval1305 B hB hF, reducedTermEval1306 B hB hF]
  rw [originalMerge1299, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1300 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1300 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1300 (originalVector B) := by
  rw [reducedMerge1300Check, Integer.Sparse.eval_mergeBy, reducedTermEval1304 B hB hF, reducedMergeEval1299 B hB hF]
  rw [originalMerge1300, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1301 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1301 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1301 (originalVector B) := by
  rw [reducedMerge1301Check, Integer.Sparse.eval_mergeBy, reducedTermEval1307 B hB hF, reducedTermEval1308 B hB hF]
  rw [originalMerge1301, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1302 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1302 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1302 (originalVector B) := by
  rw [reducedMerge1302Check, Integer.Sparse.eval_mergeBy, reducedTermEval1309 B hB hF, reducedTermEval1310 B hB hF]
  rw [originalMerge1302, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1303 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1303 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1303 (originalVector B) := by
  rw [reducedMerge1303Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1301 B hB hF, reducedMergeEval1302 B hB hF]
  rw [originalMerge1303, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1304 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1304 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1304 (originalVector B) := by
  rw [reducedMerge1304Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1300 B hB hF, reducedMergeEval1303 B hB hF]
  rw [originalMerge1304, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1305 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1305 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1305 (originalVector B) := by
  rw [reducedMerge1305Check, Integer.Sparse.eval_mergeBy, reducedTermEval1311 B hB hF, reducedTermEval1312 B hB hF]
  rw [originalMerge1305, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1306 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1306 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1306 (originalVector B) := by
  rw [reducedMerge1306Check, Integer.Sparse.eval_mergeBy, reducedTermEval1313 B hB hF, reducedTermEval1314 B hB hF]
  rw [originalMerge1306, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1307 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1307 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1307 (originalVector B) := by
  rw [reducedMerge1307Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1305 B hB hF, reducedMergeEval1306 B hB hF]
  rw [originalMerge1307, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1308 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1308 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1308 (originalVector B) := by
  rw [reducedMerge1308Check, Integer.Sparse.eval_mergeBy, reducedTermEval1315 B hB hF, reducedTermEval1316 B hB hF]
  rw [originalMerge1308, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1309 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1309 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1309 (originalVector B) := by
  rw [reducedMerge1309Check, Integer.Sparse.eval_mergeBy, reducedTermEval1317 B hB hF, reducedTermEval1318 B hB hF]
  rw [originalMerge1309, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1310 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1310 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1310 (originalVector B) := by
  rw [reducedMerge1310Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1308 B hB hF, reducedMergeEval1309 B hB hF]
  rw [originalMerge1310, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1311 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1311 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1311 (originalVector B) := by
  rw [reducedMerge1311Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1307 B hB hF, reducedMergeEval1310 B hB hF]
  rw [originalMerge1311, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1312 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1312 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1312 (originalVector B) := by
  rw [reducedMerge1312Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1304 B hB hF, reducedMergeEval1311 B hB hF]
  rw [originalMerge1312, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1313 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1313 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1313 (originalVector B) := by
  rw [reducedMerge1313Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1298 B hB hF, reducedMergeEval1312 B hB hF]
  rw [originalMerge1313, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1314 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1314 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1314 (originalVector B) := by
  rw [reducedMerge1314Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1284 B hB hF, reducedMergeEval1313 B hB hF]
  rw [originalMerge1314, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1315_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1315 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1315 (originalVector B) := by
  rw [reducedMerge1315Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1255 B hB hF, reducedMergeEval1314 B hB hF]
  rw [originalMerge1315, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e_oai
