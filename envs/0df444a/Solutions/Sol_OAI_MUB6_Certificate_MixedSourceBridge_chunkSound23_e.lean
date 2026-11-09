-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:07:40.64514+00:00
-- url     : https://prove2.me/submissions/a9a0cc79-e30c-4469-915e-4b073137c697

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound368_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound369_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound370_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound371_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound380_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw278 raw278Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw278 raw278Labels = mixedMoment B raw278step0 raw278step0Labels := by
      have ha : raw278step0 = (fun i j => raw278 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw278step0 raw278; decide +kernel
      have hl : raw278step0Labels = raw278Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw278 raw278Labels permutation8 permutation5
    mixedMoment B raw278step0 raw278step0Labels = mixedMoment B raw278step1 raw278step1Labels := by
      have ha : raw278step1 = raw278step0 := by apply Matrix.ext; unfold raw278step1 raw278step0; decide +kernel
      have hl : raw278step0Labels = labelEmbedding1 ∘ raw278step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw278step0 raw278step0Labels raw278step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

theorem canonical279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw279 raw279Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw279 raw279Labels = mixedMoment B raw279step0 raw279step0Labels := by
      have ha : raw279step0 = (fun i j => raw279 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw279step0 raw279; decide +kernel
      have hl : raw279step0Labels = raw279Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw279 raw279Labels permutation8 permutation5
    _ = mixedMoment B node412 node412Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4743 raw4743Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw4743 raw4743Labels = mixedMoment B raw4743step0 raw4743step0Labels := by
      have hz : ∀ j, raw4743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4743step0 = (fun i j => raw4743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4743step0 raw4743; decide +kernel
      have hl : raw4743step0Labels = raw4743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4743 raw4743Labels permutation346 hz
    mixedMoment B raw4743step0 raw4743step0Labels = mixedMoment B raw4743step1 raw4743step1Labels := by
      have hz : ∀ j, raw4743step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4743step1 = (fun i j => raw4743step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4743step1 raw4743step0; decide +kernel
      have hl : raw4743step1Labels = raw4743step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4743step0 raw4743step0Labels permutation56 hz
    mixedMoment B raw4743step1 raw4743step1Labels = mixedMoment B raw4743step2 raw4743step2Labels := by
      have ha : raw4743step2 = (fun i j => raw4743step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4743step2 raw4743step1; decide +kernel
      have hl : raw4743step2Labels = raw4743step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4743step1 raw4743step1Labels permutation29 permutation2
    mixedMoment B raw4743step2 raw4743step2Labels = mixedMoment B raw4743step3 raw4743step3Labels := by
      have ha : raw4743step3 = -raw4743step2 := by apply Matrix.ext; change ∀ i j, raw4743step3 i j = -(raw4743step2 i j); unfold raw4743step3 raw4743step2; decide +kernel
      have hl : raw4743step3Labels = raw4743step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3623 node3623Labels := by rfl

theorem canonical4744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4744 raw4744Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw4744 raw4744Labels = mixedMoment B raw4744step0 raw4744step0Labels := by
      have hz : ∀ j, raw4744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4744step0 = (fun i j => raw4744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4744step0 raw4744; decide +kernel
      have hl : raw4744step0Labels = raw4744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4744 raw4744Labels permutation346 hz
    mixedMoment B raw4744step0 raw4744step0Labels = mixedMoment B raw4744step1 raw4744step1Labels := by
      have hz : ∀ j, raw4744step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4744step1 = (fun i j => raw4744step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4744step1 raw4744step0; decide +kernel
      have hl : raw4744step1Labels = raw4744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4744step0 raw4744step0Labels permutation56 hz
    mixedMoment B raw4744step1 raw4744step1Labels = mixedMoment B raw4744step2 raw4744step2Labels := by
      have ha : raw4744step2 = (fun i j => raw4744step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw4744step2 raw4744step1; decide +kernel
      have hl : raw4744step2Labels = raw4744step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4744step1 raw4744step1Labels permutation26 permutation0
    mixedMoment B raw4744step2 raw4744step2Labels = mixedMoment B raw4744step3 raw4744step3Labels := by
      have ha : raw4744step3 = -raw4744step2 := by apply Matrix.ext; change ∀ i j, raw4744step3 i j = -(raw4744step2 i j); unfold raw4744step3 raw4744step2; decide +kernel
      have hl : raw4744step3Labels = raw4744step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical4748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4748 raw4748Labels = mixedMoment B node1408 node1408Labels := by
  calc
    mixedMoment B raw4748 raw4748Labels = mixedMoment B raw4748step0 raw4748step0Labels := by
      have hz : ∀ j, raw4748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4748step0 = (fun i j => raw4748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4748step0 raw4748; decide +kernel
      have hl : raw4748step0Labels = raw4748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4748 raw4748Labels permutation346 hz
    mixedMoment B raw4748step0 raw4748step0Labels = mixedMoment B raw4748step1 raw4748step1Labels := by
      have hz : ∀ j, raw4748step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4748step1 = (fun i j => raw4748step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4748step1 raw4748step0; decide +kernel
      have hl : raw4748step1Labels = raw4748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4748step0 raw4748step0Labels permutation56 hz
    _ = mixedMoment B node1408 node1408Labels := by rfl

theorem canonical4753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4753 raw4753Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw4753 raw4753Labels = mixedMoment B raw4753step0 raw4753step0Labels := by
      have hz : ∀ j, raw4753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4753step0 = (fun i j => raw4753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4753step0 raw4753; decide +kernel
      have hl : raw4753step0Labels = raw4753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4753 raw4753Labels permutation346 hz
    mixedMoment B raw4753step0 raw4753step0Labels = mixedMoment B raw4753step1 raw4753step1Labels := by
      have ha : raw4753step1 = (fun i j => raw4753step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4753step1 raw4753step0; decide +kernel
      have hl : raw4753step1Labels = raw4753step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4753step0 raw4753step0Labels permutation40 permutation2
    _ = mixedMoment B node3075 node3075Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8130 raw8130Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw8130 raw8130Labels = mixedMoment B raw8130step0 raw8130step0Labels := by
      have hz : ∀ j, raw8130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8130step0 = (fun i j => raw8130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8130step0 raw8130; decide +kernel
      have hl : raw8130step0Labels = raw8130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8130 raw8130Labels permutation346 hz
    mixedMoment B raw8130step0 raw8130step0Labels = mixedMoment B raw8130step1 raw8130step1Labels := by
      have ha : raw8130step1 = (fun i j => raw8130step0 (permutation133 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8130step1 raw8130step0; decide +kernel
      have hl : raw8130step1Labels = raw8130step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8130step0 raw8130step0Labels permutation133 permutation5
    mixedMoment B raw8130step1 raw8130step1Labels = mixedMoment B raw8130step2 raw8130step2Labels := by
      have ha : raw8130step2 = raw8130step1 := by apply Matrix.ext; unfold raw8130step2 raw8130step1; decide +kernel
      have hl : raw8130step1Labels = labelEmbedding1 ∘ raw8130step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8130step1 raw8130step1Labels raw8130step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical8131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8131 raw8131Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw8131 raw8131Labels = mixedMoment B raw8131step0 raw8131step0Labels := by
      have hz : ∀ j, raw8131 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8131step0 = (fun i j => raw8131 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8131step0 raw8131; decide +kernel
      have hl : raw8131step0Labels = raw8131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8131 raw8131Labels permutation265 hz
    mixedMoment B raw8131step0 raw8131step0Labels = mixedMoment B raw8131step1 raw8131step1Labels := by
      have ha : raw8131step1 = (fun i j => raw8131step0 (permutation133 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8131step1 raw8131step0; decide +kernel
      have hl : raw8131step1Labels = raw8131step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8131step0 raw8131step0Labels permutation133 permutation5
    mixedMoment B raw8131step1 raw8131step1Labels = mixedMoment B raw8131step2 raw8131step2Labels := by
      have ha : raw8131step2 = raw8131step1 := by apply Matrix.ext; unfold raw8131step2 raw8131step1; decide +kernel
      have hl : raw8131step1Labels = labelEmbedding1 ∘ raw8131step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8131step1 raw8131step1Labels raw8131step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical8132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8132 raw8132Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw8132 raw8132Labels = mixedMoment B raw8132step0 raw8132step0Labels := by
      have hz : ∀ j, raw8132 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8132step0 = (fun i j => raw8132 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8132step0 raw8132; decide +kernel
      have hl : raw8132step0Labels = raw8132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8132 raw8132Labels permutation346 hz
    mixedMoment B raw8132step0 raw8132step0Labels = mixedMoment B raw8132step1 raw8132step1Labels := by
      have hz : ∀ j, raw8132step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8132step1 = (fun i j => raw8132step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8132step1 raw8132step0; decide +kernel
      have hl : raw8132step1Labels = raw8132step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8132step0 raw8132step0Labels permutation56 hz
    mixedMoment B raw8132step1 raw8132step1Labels = mixedMoment B raw8132step2 raw8132step2Labels := by
      have ha : raw8132step2 = (fun i j => raw8132step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8132step2 raw8132step1; decide +kernel
      have hl : raw8132step2Labels = raw8132step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8132step1 raw8132step1Labels permutation27 permutation5
    mixedMoment B raw8132step2 raw8132step2Labels = mixedMoment B raw8132step3 raw8132step3Labels := by
      have ha : raw8132step3 = raw8132step2 := by apply Matrix.ext; unfold raw8132step3 raw8132step2; decide +kernel
      have hl : raw8132step2Labels = labelEmbedding1 ∘ raw8132step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8132step2 raw8132step2Labels raw8132step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2774 node2774Labels := by rfl

theorem canonical8133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8133 raw8133Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw8133 raw8133Labels = mixedMoment B raw8133step0 raw8133step0Labels := by
      have hz : ∀ j, raw8133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8133step0 = (fun i j => raw8133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8133step0 raw8133; decide +kernel
      have hl : raw8133step0Labels = raw8133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8133 raw8133Labels permutation346 hz
    mixedMoment B raw8133step0 raw8133step0Labels = mixedMoment B raw8133step1 raw8133step1Labels := by
      have hz : ∀ j, raw8133step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8133step1 = (fun i j => raw8133step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8133step1 raw8133step0; decide +kernel
      have hl : raw8133step1Labels = raw8133step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8133step0 raw8133step0Labels permutation56 hz
    mixedMoment B raw8133step1 raw8133step1Labels = mixedMoment B raw8133step2 raw8133step2Labels := by
      have ha : raw8133step2 = (fun i j => raw8133step1 (permutation26 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8133step2 raw8133step1; decide +kernel
      have hl : raw8133step2Labels = raw8133step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8133step1 raw8133step1Labels permutation26 permutation5
    mixedMoment B raw8133step2 raw8133step2Labels = mixedMoment B raw8133step3 raw8133step3Labels := by
      have ha : raw8133step3 = raw8133step2 := by apply Matrix.ext; unfold raw8133step3 raw8133step2; decide +kernel
      have hl : raw8133step2Labels = labelEmbedding1 ∘ raw8133step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8133step2 raw8133step2Labels raw8133step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

theorem canonical8134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8134 raw8134Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw8134 raw8134Labels = mixedMoment B raw8134step0 raw8134step0Labels := by
      have hz : ∀ j, raw8134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8134step0 = (fun i j => raw8134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8134step0 raw8134; decide +kernel
      have hl : raw8134step0Labels = raw8134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8134 raw8134Labels permutation346 hz
    mixedMoment B raw8134step0 raw8134step0Labels = mixedMoment B raw8134step1 raw8134step1Labels := by
      have hz : ∀ j, raw8134step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8134step1 = (fun i j => raw8134step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8134step1 raw8134step0; decide +kernel
      have hl : raw8134step1Labels = raw8134step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8134step0 raw8134step0Labels permutation56 hz
    mixedMoment B raw8134step1 raw8134step1Labels = mixedMoment B raw8134step2 raw8134step2Labels := by
      have ha : raw8134step2 = (fun i j => raw8134step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8134step2 raw8134step1; decide +kernel
      have hl : raw8134step2Labels = raw8134step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8134step1 raw8134step1Labels permutation12 permutation7
    mixedMoment B raw8134step2 raw8134step2Labels = mixedMoment B raw8134step3 raw8134step3Labels := by
      have ha : raw8134step3 = -raw8134step2 := by apply Matrix.ext; change ∀ i j, raw8134step3 i j = -(raw8134step2 i j); unfold raw8134step3 raw8134step2; decide +kernel
      have hl : raw8134step3Labels = raw8134step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8134step3 raw8134step3Labels = mixedMoment B raw8134step4 raw8134step4Labels := by
      have ha : raw8134step4 = raw8134step3 := by apply Matrix.ext; unfold raw8134step4 raw8134step3; decide +kernel
      have hl : raw8134step3Labels = labelEmbedding1 ∘ raw8134step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8134step3 raw8134step3Labels raw8134step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3888 node3888Labels := by rfl

theorem canonical8135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8135 raw8135Labels = mixedMoment B node2502 node2502Labels := by
  calc
    mixedMoment B raw8135 raw8135Labels = mixedMoment B raw8135step0 raw8135step0Labels := by
      have hz : ∀ j, raw8135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8135step0 = (fun i j => raw8135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8135step0 raw8135; decide +kernel
      have hl : raw8135step0Labels = raw8135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8135 raw8135Labels permutation346 hz
    mixedMoment B raw8135step0 raw8135step0Labels = mixedMoment B raw8135step1 raw8135step1Labels := by
      have ha : raw8135step1 = (fun i j => raw8135step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8135step1 raw8135step0; decide +kernel
      have hl : raw8135step1Labels = raw8135step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8135step0 raw8135step0Labels permutation139 permutation5
    mixedMoment B raw8135step1 raw8135step1Labels = mixedMoment B raw8135step2 raw8135step2Labels := by
      have ha : raw8135step2 = raw8135step1 := by apply Matrix.ext; unfold raw8135step2 raw8135step1; decide +kernel
      have hl : raw8135step1Labels = labelEmbedding1 ∘ raw8135step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8135step1 raw8135step1Labels raw8135step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2502 node2502Labels := by rfl

theorem canonical8136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8136 raw8136Labels = mixedMoment B node2500 node2500Labels := by
  calc
    mixedMoment B raw8136 raw8136Labels = mixedMoment B raw8136step0 raw8136step0Labels := by
      have ha : raw8136step0 = (fun i j => raw8136 (permutation622 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8136step0 raw8136; decide +kernel
      have hl : raw8136step0Labels = raw8136Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8136 raw8136Labels permutation622 permutation5
    mixedMoment B raw8136step0 raw8136step0Labels = mixedMoment B raw8136step1 raw8136step1Labels := by
      have ha : raw8136step1 = raw8136step0 := by apply Matrix.ext; unfold raw8136step1 raw8136step0; decide +kernel
      have hl : raw8136step0Labels = labelEmbedding1 ∘ raw8136step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8136step0 raw8136step0Labels raw8136step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2500 node2500Labels := by rfl

theorem canonical8137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8137 raw8137Labels = mixedMoment B node2506 node2506Labels := by
  calc
    mixedMoment B raw8137 raw8137Labels = mixedMoment B raw8137step0 raw8137step0Labels := by
      have hz : ∀ j, raw8137 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8137step0 = (fun i j => raw8137 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8137step0 raw8137; decide +kernel
      have hl : raw8137step0Labels = raw8137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8137 raw8137Labels permutation346 hz
    mixedMoment B raw8137step0 raw8137step0Labels = mixedMoment B raw8137step1 raw8137step1Labels := by
      have ha : raw8137step1 = (fun i j => raw8137step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8137step1 raw8137step0; decide +kernel
      have hl : raw8137step1Labels = raw8137step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8137step0 raw8137step0Labels permutation138 permutation5
    mixedMoment B raw8137step1 raw8137step1Labels = mixedMoment B raw8137step2 raw8137step2Labels := by
      have ha : raw8137step2 = raw8137step1 := by apply Matrix.ext; unfold raw8137step2 raw8137step1; decide +kernel
      have hl : raw8137step1Labels = labelEmbedding1 ∘ raw8137step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8137step1 raw8137step1Labels raw8137step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2506 node2506Labels := by rfl

theorem canonical8138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8138 raw8138Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw8138 raw8138Labels = mixedMoment B raw8138step0 raw8138step0Labels := by
      have hz : ∀ j, raw8138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8138step0 = (fun i j => raw8138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8138step0 raw8138; decide +kernel
      have hl : raw8138step0Labels = raw8138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8138 raw8138Labels permutation346 hz
    mixedMoment B raw8138step0 raw8138step0Labels = mixedMoment B raw8138step1 raw8138step1Labels := by
      have ha : raw8138step1 = (fun i j => raw8138step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8138step1 raw8138step0; decide +kernel
      have hl : raw8138step1Labels = raw8138step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8138step0 raw8138step0Labels permutation136 permutation5
    mixedMoment B raw8138step1 raw8138step1Labels = mixedMoment B raw8138step2 raw8138step2Labels := by
      have ha : raw8138step2 = raw8138step1 := by apply Matrix.ext; unfold raw8138step2 raw8138step1; decide +kernel
      have hl : raw8138step1Labels = labelEmbedding1 ∘ raw8138step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8138step1 raw8138step1Labels raw8138step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2513 node2513Labels := by rfl

theorem canonical8139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8139 raw8139Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw8139 raw8139Labels = mixedMoment B raw8139step0 raw8139step0Labels := by
      have hz : ∀ j, raw8139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8139step0 = (fun i j => raw8139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8139step0 raw8139; decide +kernel
      have hl : raw8139step0Labels = raw8139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8139 raw8139Labels permutation346 hz
    mixedMoment B raw8139step0 raw8139step0Labels = mixedMoment B raw8139step1 raw8139step1Labels := by
      have ha : raw8139step1 = (fun i j => raw8139step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8139step1 raw8139step0; decide +kernel
      have hl : raw8139step1Labels = raw8139step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8139step0 raw8139step0Labels permutation50 permutation7
    mixedMoment B raw8139step1 raw8139step1Labels = mixedMoment B raw8139step2 raw8139step2Labels := by
      have ha : raw8139step2 = -raw8139step1 := by apply Matrix.ext; change ∀ i j, raw8139step2 i j = -(raw8139step1 i j); unfold raw8139step2 raw8139step1; decide +kernel
      have hl : raw8139step2Labels = raw8139step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8139step2 raw8139step2Labels = mixedMoment B raw8139step3 raw8139step3Labels := by
      have ha : raw8139step3 = raw8139step2 := by apply Matrix.ext; unfold raw8139step3 raw8139step2; decide +kernel
      have hl : raw8139step2Labels = labelEmbedding1 ∘ raw8139step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8139step2 raw8139step2Labels raw8139step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical8140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8140 raw8140Labels = mixedMoment B node2502 node2502Labels := by
  calc
    mixedMoment B raw8140 raw8140Labels = mixedMoment B raw8140step0 raw8140step0Labels := by
      have hz : ∀ j, raw8140 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8140step0 = (fun i j => raw8140 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8140step0 raw8140; decide +kernel
      have hl : raw8140step0Labels = raw8140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8140 raw8140Labels permutation265 hz
    mixedMoment B raw8140step0 raw8140step0Labels = mixedMoment B raw8140step1 raw8140step1Labels := by
      have ha : raw8140step1 = (fun i j => raw8140step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8140step1 raw8140step0; decide +kernel
      have hl : raw8140step1Labels = raw8140step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8140step0 raw8140step0Labels permutation139 permutation5
    mixedMoment B raw8140step1 raw8140step1Labels = mixedMoment B raw8140step2 raw8140step2Labels := by
      have ha : raw8140step2 = raw8140step1 := by apply Matrix.ext; unfold raw8140step2 raw8140step1; decide +kernel
      have hl : raw8140step1Labels = labelEmbedding1 ∘ raw8140step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8140step1 raw8140step1Labels raw8140step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2502 node2502Labels := by rfl

theorem canonical8141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8141 raw8141Labels = mixedMoment B node2500 node2500Labels := by
  calc
    mixedMoment B raw8141 raw8141Labels = mixedMoment B raw8141step0 raw8141step0Labels := by
      have ha : raw8141step0 = (fun i j => raw8141 (permutation646 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8141step0 raw8141; decide +kernel
      have hl : raw8141step0Labels = raw8141Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8141 raw8141Labels permutation646 permutation5
    mixedMoment B raw8141step0 raw8141step0Labels = mixedMoment B raw8141step1 raw8141step1Labels := by
      have ha : raw8141step1 = raw8141step0 := by apply Matrix.ext; unfold raw8141step1 raw8141step0; decide +kernel
      have hl : raw8141step0Labels = labelEmbedding1 ∘ raw8141step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8141step0 raw8141step0Labels raw8141step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2500 node2500Labels := by rfl

theorem canonical8142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8142 raw8142Labels = mixedMoment B node2506 node2506Labels := by
  calc
    mixedMoment B raw8142 raw8142Labels = mixedMoment B raw8142step0 raw8142step0Labels := by
      have hz : ∀ j, raw8142 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8142step0 = (fun i j => raw8142 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8142step0 raw8142; decide +kernel
      have hl : raw8142step0Labels = raw8142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8142 raw8142Labels permutation265 hz
    mixedMoment B raw8142step0 raw8142step0Labels = mixedMoment B raw8142step1 raw8142step1Labels := by
      have ha : raw8142step1 = (fun i j => raw8142step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8142step1 raw8142step0; decide +kernel
      have hl : raw8142step1Labels = raw8142step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8142step0 raw8142step0Labels permutation138 permutation5
    mixedMoment B raw8142step1 raw8142step1Labels = mixedMoment B raw8142step2 raw8142step2Labels := by
      have ha : raw8142step2 = raw8142step1 := by apply Matrix.ext; unfold raw8142step2 raw8142step1; decide +kernel
      have hl : raw8142step1Labels = labelEmbedding1 ∘ raw8142step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8142step1 raw8142step1Labels raw8142step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2506 node2506Labels := by rfl

theorem canonical8143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8143 raw8143Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw8143 raw8143Labels = mixedMoment B raw8143step0 raw8143step0Labels := by
      have hz : ∀ j, raw8143 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8143step0 = (fun i j => raw8143 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8143step0 raw8143; decide +kernel
      have hl : raw8143step0Labels = raw8143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8143 raw8143Labels permutation265 hz
    mixedMoment B raw8143step0 raw8143step0Labels = mixedMoment B raw8143step1 raw8143step1Labels := by
      have ha : raw8143step1 = (fun i j => raw8143step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8143step1 raw8143step0; decide +kernel
      have hl : raw8143step1Labels = raw8143step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8143step0 raw8143step0Labels permutation136 permutation5
    mixedMoment B raw8143step1 raw8143step1Labels = mixedMoment B raw8143step2 raw8143step2Labels := by
      have ha : raw8143step2 = raw8143step1 := by apply Matrix.ext; unfold raw8143step2 raw8143step1; decide +kernel
      have hl : raw8143step1Labels = labelEmbedding1 ∘ raw8143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8143step1 raw8143step1Labels raw8143step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2513 node2513Labels := by rfl

theorem canonical8144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8144 raw8144Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw8144 raw8144Labels = mixedMoment B raw8144step0 raw8144step0Labels := by
      have hz : ∀ j, raw8144 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8144step0 = (fun i j => raw8144 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8144step0 raw8144; decide +kernel
      have hl : raw8144step0Labels = raw8144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8144 raw8144Labels permutation265 hz
    mixedMoment B raw8144step0 raw8144step0Labels = mixedMoment B raw8144step1 raw8144step1Labels := by
      have ha : raw8144step1 = (fun i j => raw8144step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8144step1 raw8144step0; decide +kernel
      have hl : raw8144step1Labels = raw8144step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8144step0 raw8144step0Labels permutation50 permutation7
    mixedMoment B raw8144step1 raw8144step1Labels = mixedMoment B raw8144step2 raw8144step2Labels := by
      have ha : raw8144step2 = -raw8144step1 := by apply Matrix.ext; change ∀ i j, raw8144step2 i j = -(raw8144step1 i j); unfold raw8144step2 raw8144step1; decide +kernel
      have hl : raw8144step2Labels = raw8144step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8144step2 raw8144step2Labels = mixedMoment B raw8144step3 raw8144step3Labels := by
      have ha : raw8144step3 = raw8144step2 := by apply Matrix.ext; unfold raw8144step3 raw8144step2; decide +kernel
      have hl : raw8144step2Labels = labelEmbedding1 ∘ raw8144step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8144step2 raw8144step2Labels raw8144step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical8145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8145 raw8145Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw8145 raw8145Labels = mixedMoment B raw8145step0 raw8145step0Labels := by
      have hz : ∀ j, raw8145 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8145step0 = (fun i j => raw8145 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8145step0 raw8145; decide +kernel
      have hl : raw8145step0Labels = raw8145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8145 raw8145Labels permutation346 hz
    mixedMoment B raw8145step0 raw8145step0Labels = mixedMoment B raw8145step1 raw8145step1Labels := by
      have hz : ∀ j, raw8145step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8145step1 = (fun i j => raw8145step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8145step1 raw8145step0; decide +kernel
      have hl : raw8145step1Labels = raw8145step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8145step0 raw8145step0Labels permutation56 hz
    mixedMoment B raw8145step1 raw8145step1Labels = mixedMoment B raw8145step2 raw8145step2Labels := by
      have ha : raw8145step2 = (fun i j => raw8145step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8145step2 raw8145step1; decide +kernel
      have hl : raw8145step2Labels = raw8145step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8145step1 raw8145step1Labels permutation29 permutation5
    mixedMoment B raw8145step2 raw8145step2Labels = mixedMoment B raw8145step3 raw8145step3Labels := by
      have ha : raw8145step3 = raw8145step2 := by apply Matrix.ext; unfold raw8145step3 raw8145step2; decide +kernel
      have hl : raw8145step2Labels = labelEmbedding1 ∘ raw8145step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8145step2 raw8145step2Labels raw8145step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

theorem canonical8146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8146 raw8146Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw8146 raw8146Labels = mixedMoment B raw8146step0 raw8146step0Labels := by
      have hz : ∀ j, raw8146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8146step0 = (fun i j => raw8146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8146step0 raw8146; decide +kernel
      have hl : raw8146step0Labels = raw8146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8146 raw8146Labels permutation346 hz
    mixedMoment B raw8146step0 raw8146step0Labels = mixedMoment B raw8146step1 raw8146step1Labels := by
      have ha : raw8146step1 = (fun i j => raw8146step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8146step1 raw8146step0; decide +kernel
      have hl : raw8146step1Labels = raw8146step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8146step0 raw8146step0Labels permutation145 permutation5
    mixedMoment B raw8146step1 raw8146step1Labels = mixedMoment B raw8146step2 raw8146step2Labels := by
      have ha : raw8146step2 = raw8146step1 := by apply Matrix.ext; unfold raw8146step2 raw8146step1; decide +kernel
      have hl : raw8146step1Labels = labelEmbedding1 ∘ raw8146step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8146step1 raw8146step1Labels raw8146step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

theorem canonical8147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8147 raw8147Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw8147 raw8147Labels = mixedMoment B raw8147step0 raw8147step0Labels := by
      have hz : ∀ j, raw8147 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8147step0 = (fun i j => raw8147 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8147step0 raw8147; decide +kernel
      have hl : raw8147step0Labels = raw8147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8147 raw8147Labels permutation265 hz
    mixedMoment B raw8147step0 raw8147step0Labels = mixedMoment B raw8147step1 raw8147step1Labels := by
      have ha : raw8147step1 = (fun i j => raw8147step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8147step1 raw8147step0; decide +kernel
      have hl : raw8147step1Labels = raw8147step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8147step0 raw8147step0Labels permutation145 permutation5
    mixedMoment B raw8147step1 raw8147step1Labels = mixedMoment B raw8147step2 raw8147step2Labels := by
      have ha : raw8147step2 = raw8147step1 := by apply Matrix.ext; unfold raw8147step2 raw8147step1; decide +kernel
      have hl : raw8147step1Labels = labelEmbedding1 ∘ raw8147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8147step1 raw8147step1Labels raw8147step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

theorem canonical8148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8148 raw8148Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw8148 raw8148Labels = mixedMoment B raw8148step0 raw8148step0Labels := by
      have hz : ∀ j, raw8148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8148step0 = (fun i j => raw8148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8148step0 raw8148; decide +kernel
      have hl : raw8148step0Labels = raw8148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8148 raw8148Labels permutation346 hz
    mixedMoment B raw8148step0 raw8148step0Labels = mixedMoment B raw8148step1 raw8148step1Labels := by
      have hz : ∀ j, raw8148step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8148step1 = (fun i j => raw8148step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8148step1 raw8148step0; decide +kernel
      have hl : raw8148step1Labels = raw8148step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8148step0 raw8148step0Labels permutation56 hz
    mixedMoment B raw8148step1 raw8148step1Labels = mixedMoment B raw8148step2 raw8148step2Labels := by
      have ha : raw8148step2 = (fun i j => raw8148step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8148step2 raw8148step1; decide +kernel
      have hl : raw8148step2Labels = raw8148step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8148step1 raw8148step1Labels permutation28 permutation5
    mixedMoment B raw8148step2 raw8148step2Labels = mixedMoment B raw8148step3 raw8148step3Labels := by
      have ha : raw8148step3 = raw8148step2 := by apply Matrix.ext; unfold raw8148step3 raw8148step2; decide +kernel
      have hl : raw8148step2Labels = labelEmbedding1 ∘ raw8148step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8148step2 raw8148step2Labels raw8148step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

theorem canonical8149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8149 raw8149Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw8149 raw8149Labels = mixedMoment B raw8149step0 raw8149step0Labels := by
      have hz : ∀ j, raw8149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8149step0 = (fun i j => raw8149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8149step0 raw8149; decide +kernel
      have hl : raw8149step0Labels = raw8149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8149 raw8149Labels permutation346 hz
    mixedMoment B raw8149step0 raw8149step0Labels = mixedMoment B raw8149step1 raw8149step1Labels := by
      have hz : ∀ j, raw8149step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8149step1 = (fun i j => raw8149step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8149step1 raw8149step0; decide +kernel
      have hl : raw8149step1Labels = raw8149step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8149step0 raw8149step0Labels permutation56 hz
    mixedMoment B raw8149step1 raw8149step1Labels = mixedMoment B raw8149step2 raw8149step2Labels := by
      have ha : raw8149step2 = (fun i j => raw8149step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8149step2 raw8149step1; decide +kernel
      have hl : raw8149step2Labels = raw8149step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8149step1 raw8149step1Labels permutation12 permutation7
    mixedMoment B raw8149step2 raw8149step2Labels = mixedMoment B raw8149step3 raw8149step3Labels := by
      have ha : raw8149step3 = -raw8149step2 := by apply Matrix.ext; change ∀ i j, raw8149step3 i j = -(raw8149step2 i j); unfold raw8149step3 raw8149step2; decide +kernel
      have hl : raw8149step3Labels = raw8149step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8149step3 raw8149step3Labels = mixedMoment B raw8149step4 raw8149step4Labels := by
      have ha : raw8149step4 = raw8149step3 := by apply Matrix.ext; unfold raw8149step4 raw8149step3; decide +kernel
      have hl : raw8149step3Labels = labelEmbedding1 ∘ raw8149step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8149step3 raw8149step3Labels raw8149step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

theorem canonical8150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8150 raw8150Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw8150 raw8150Labels = mixedMoment B raw8150step0 raw8150step0Labels := by
      have hz : ∀ j, raw8150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8150step0 = (fun i j => raw8150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8150step0 raw8150; decide +kernel
      have hl : raw8150step0Labels = raw8150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8150 raw8150Labels permutation346 hz
    mixedMoment B raw8150step0 raw8150step0Labels = mixedMoment B raw8150step1 raw8150step1Labels := by
      have hz : ∀ j, raw8150step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8150step1 = (fun i j => raw8150step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8150step1 raw8150step0; decide +kernel
      have hl : raw8150step1Labels = raw8150step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8150step0 raw8150step0Labels permutation56 hz
    mixedMoment B raw8150step1 raw8150step1Labels = mixedMoment B raw8150step2 raw8150step2Labels := by
      have ha : raw8150step2 = (fun i j => raw8150step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8150step2 raw8150step1; decide +kernel
      have hl : raw8150step2Labels = raw8150step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8150step1 raw8150step1Labels permutation31 permutation5
    mixedMoment B raw8150step2 raw8150step2Labels = mixedMoment B raw8150step3 raw8150step3Labels := by
      have ha : raw8150step3 = raw8150step2 := by apply Matrix.ext; unfold raw8150step3 raw8150step2; decide +kernel
      have hl : raw8150step2Labels = labelEmbedding1 ∘ raw8150step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8150step2 raw8150step2Labels raw8150step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2683 node2683Labels := by rfl

theorem canonical8151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8151 raw8151Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw8151 raw8151Labels = mixedMoment B raw8151step0 raw8151step0Labels := by
      have hz : ∀ j, raw8151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8151step0 = (fun i j => raw8151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8151step0 raw8151; decide +kernel
      have hl : raw8151step0Labels = raw8151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8151 raw8151Labels permutation346 hz
    mixedMoment B raw8151step0 raw8151step0Labels = mixedMoment B raw8151step1 raw8151step1Labels := by
      have ha : raw8151step1 = (fun i j => raw8151step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8151step1 raw8151step0; decide +kernel
      have hl : raw8151step1Labels = raw8151step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8151step0 raw8151step0Labels permutation151 permutation5
    mixedMoment B raw8151step1 raw8151step1Labels = mixedMoment B raw8151step2 raw8151step2Labels := by
      have ha : raw8151step2 = raw8151step1 := by apply Matrix.ext; unfold raw8151step2 raw8151step1; decide +kernel
      have hl : raw8151step1Labels = labelEmbedding1 ∘ raw8151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8151step1 raw8151step1Labels raw8151step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

theorem canonical8152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8152 raw8152Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw8152 raw8152Labels = mixedMoment B raw8152step0 raw8152step0Labels := by
      have hz : ∀ j, raw8152 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8152step0 = (fun i j => raw8152 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8152step0 raw8152; decide +kernel
      have hl : raw8152step0Labels = raw8152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8152 raw8152Labels permutation265 hz
    mixedMoment B raw8152step0 raw8152step0Labels = mixedMoment B raw8152step1 raw8152step1Labels := by
      have ha : raw8152step1 = (fun i j => raw8152step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8152step1 raw8152step0; decide +kernel
      have hl : raw8152step1Labels = raw8152step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8152step0 raw8152step0Labels permutation151 permutation5
    mixedMoment B raw8152step1 raw8152step1Labels = mixedMoment B raw8152step2 raw8152step2Labels := by
      have ha : raw8152step2 = raw8152step1 := by apply Matrix.ext; unfold raw8152step2 raw8152step1; decide +kernel
      have hl : raw8152step1Labels = labelEmbedding1 ∘ raw8152step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8152step1 raw8152step1Labels raw8152step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

theorem canonical8153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8153 raw8153Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw8153 raw8153Labels = mixedMoment B raw8153step0 raw8153step0Labels := by
      have hz : ∀ j, raw8153 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8153step0 = (fun i j => raw8153 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8153step0 raw8153; decide +kernel
      have hl : raw8153step0Labels = raw8153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8153 raw8153Labels permutation346 hz
    mixedMoment B raw8153step0 raw8153step0Labels = mixedMoment B raw8153step1 raw8153step1Labels := by
      have hz : ∀ j, raw8153step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8153step1 = (fun i j => raw8153step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8153step1 raw8153step0; decide +kernel
      have hl : raw8153step1Labels = raw8153step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8153step0 raw8153step0Labels permutation56 hz
    mixedMoment B raw8153step1 raw8153step1Labels = mixedMoment B raw8153step2 raw8153step2Labels := by
      have ha : raw8153step2 = (fun i j => raw8153step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8153step2 raw8153step1; decide +kernel
      have hl : raw8153step2Labels = raw8153step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8153step1 raw8153step1Labels permutation30 permutation5
    mixedMoment B raw8153step2 raw8153step2Labels = mixedMoment B raw8153step3 raw8153step3Labels := by
      have ha : raw8153step3 = raw8153step2 := by apply Matrix.ext; unfold raw8153step3 raw8153step2; decide +kernel
      have hl : raw8153step2Labels = labelEmbedding1 ∘ raw8153step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8153step2 raw8153step2Labels raw8153step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2687 node2687Labels := by rfl

theorem canonical8154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8154 raw8154Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw8154 raw8154Labels = mixedMoment B raw8154step0 raw8154step0Labels := by
      have hz : ∀ j, raw8154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8154step0 = (fun i j => raw8154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8154step0 raw8154; decide +kernel
      have hl : raw8154step0Labels = raw8154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8154 raw8154Labels permutation346 hz
    mixedMoment B raw8154step0 raw8154step0Labels = mixedMoment B raw8154step1 raw8154step1Labels := by
      have hz : ∀ j, raw8154step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8154step1 = (fun i j => raw8154step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8154step1 raw8154step0; decide +kernel
      have hl : raw8154step1Labels = raw8154step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8154step0 raw8154step0Labels permutation56 hz
    mixedMoment B raw8154step1 raw8154step1Labels = mixedMoment B raw8154step2 raw8154step2Labels := by
      have ha : raw8154step2 = (fun i j => raw8154step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8154step2 raw8154step1; decide +kernel
      have hl : raw8154step2Labels = raw8154step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8154step1 raw8154step1Labels permutation12 permutation7
    mixedMoment B raw8154step2 raw8154step2Labels = mixedMoment B raw8154step3 raw8154step3Labels := by
      have ha : raw8154step3 = -raw8154step2 := by apply Matrix.ext; change ∀ i j, raw8154step3 i j = -(raw8154step2 i j); unfold raw8154step3 raw8154step2; decide +kernel
      have hl : raw8154step3Labels = raw8154step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8154step3 raw8154step3Labels = mixedMoment B raw8154step4 raw8154step4Labels := by
      have ha : raw8154step4 = raw8154step3 := by apply Matrix.ext; unfold raw8154step4 raw8154step3; decide +kernel
      have hl : raw8154step3Labels = labelEmbedding1 ∘ raw8154step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8154step3 raw8154step3Labels raw8154step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

theorem canonical8155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8155 raw8155Labels = mixedMoment B node1072 node1072Labels := by
  calc
    mixedMoment B raw8155 raw8155Labels = mixedMoment B raw8155step0 raw8155step0Labels := by
      have hz : ∀ j, raw8155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8155step0 = (fun i j => raw8155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8155step0 raw8155; decide +kernel
      have hl : raw8155step0Labels = raw8155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8155 raw8155Labels permutation346 hz
    mixedMoment B raw8155step0 raw8155step0Labels = mixedMoment B raw8155step1 raw8155step1Labels := by
      have hz : ∀ j, raw8155step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8155step1 = (fun i j => raw8155step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8155step1 raw8155step0; decide +kernel
      have hl : raw8155step1Labels = raw8155step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8155step0 raw8155step0Labels permutation56 hz
    mixedMoment B raw8155step1 raw8155step1Labels = mixedMoment B raw8155step2 raw8155step2Labels := by
      have ha : raw8155step2 = (fun i j => raw8155step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8155step2 raw8155step1; decide +kernel
      have hl : raw8155step2Labels = raw8155step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8155step1 raw8155step1Labels permutation31 permutation5
    mixedMoment B raw8155step2 raw8155step2Labels = mixedMoment B raw8155step3 raw8155step3Labels := by
      have ha : raw8155step3 = raw8155step2 := by apply Matrix.ext; unfold raw8155step3 raw8155step2; decide +kernel
      have hl : raw8155step2Labels = labelEmbedding1 ∘ raw8155step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8155step2 raw8155step2Labels raw8155step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1072 node1072Labels := by rfl

theorem canonical8156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8156 raw8156Labels = mixedMoment B node1070 node1070Labels := by
  calc
    mixedMoment B raw8156 raw8156Labels = mixedMoment B raw8156step0 raw8156step0Labels := by
      have hz : ∀ j, raw8156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8156step0 = (fun i j => raw8156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8156step0 raw8156; decide +kernel
      have hl : raw8156step0Labels = raw8156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8156 raw8156Labels permutation346 hz
    mixedMoment B raw8156step0 raw8156step0Labels = mixedMoment B raw8156step1 raw8156step1Labels := by
      have ha : raw8156step1 = (fun i j => raw8156step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8156step1 raw8156step0; decide +kernel
      have hl : raw8156step1Labels = raw8156step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8156step0 raw8156step0Labels permutation151 permutation5
    mixedMoment B raw8156step1 raw8156step1Labels = mixedMoment B raw8156step2 raw8156step2Labels := by
      have ha : raw8156step2 = raw8156step1 := by apply Matrix.ext; unfold raw8156step2 raw8156step1; decide +kernel
      have hl : raw8156step1Labels = labelEmbedding1 ∘ raw8156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8156step1 raw8156step1Labels raw8156step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1070 node1070Labels := by rfl

theorem canonical8157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8157 raw8157Labels = mixedMoment B node1070 node1070Labels := by
  calc
    mixedMoment B raw8157 raw8157Labels = mixedMoment B raw8157step0 raw8157step0Labels := by
      have hz : ∀ j, raw8157 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8157step0 = (fun i j => raw8157 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8157step0 raw8157; decide +kernel
      have hl : raw8157step0Labels = raw8157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8157 raw8157Labels permutation265 hz
    mixedMoment B raw8157step0 raw8157step0Labels = mixedMoment B raw8157step1 raw8157step1Labels := by
      have ha : raw8157step1 = (fun i j => raw8157step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8157step1 raw8157step0; decide +kernel
      have hl : raw8157step1Labels = raw8157step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8157step0 raw8157step0Labels permutation151 permutation5
    mixedMoment B raw8157step1 raw8157step1Labels = mixedMoment B raw8157step2 raw8157step2Labels := by
      have ha : raw8157step2 = raw8157step1 := by apply Matrix.ext; unfold raw8157step2 raw8157step1; decide +kernel
      have hl : raw8157step1Labels = labelEmbedding1 ∘ raw8157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8157step1 raw8157step1Labels raw8157step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1070 node1070Labels := by rfl

theorem canonical8158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8158 raw8158Labels = mixedMoment B node1076 node1076Labels := by
  calc
    mixedMoment B raw8158 raw8158Labels = mixedMoment B raw8158step0 raw8158step0Labels := by
      have hz : ∀ j, raw8158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8158step0 = (fun i j => raw8158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8158step0 raw8158; decide +kernel
      have hl : raw8158step0Labels = raw8158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8158 raw8158Labels permutation346 hz
    mixedMoment B raw8158step0 raw8158step0Labels = mixedMoment B raw8158step1 raw8158step1Labels := by
      have hz : ∀ j, raw8158step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8158step1 = (fun i j => raw8158step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8158step1 raw8158step0; decide +kernel
      have hl : raw8158step1Labels = raw8158step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8158step0 raw8158step0Labels permutation56 hz
    mixedMoment B raw8158step1 raw8158step1Labels = mixedMoment B raw8158step2 raw8158step2Labels := by
      have ha : raw8158step2 = (fun i j => raw8158step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8158step2 raw8158step1; decide +kernel
      have hl : raw8158step2Labels = raw8158step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8158step1 raw8158step1Labels permutation30 permutation5
    mixedMoment B raw8158step2 raw8158step2Labels = mixedMoment B raw8158step3 raw8158step3Labels := by
      have ha : raw8158step3 = raw8158step2 := by apply Matrix.ext; unfold raw8158step3 raw8158step2; decide +kernel
      have hl : raw8158step2Labels = labelEmbedding1 ∘ raw8158step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8158step2 raw8158step2Labels raw8158step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1076 node1076Labels := by rfl

theorem canonical8159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8159 raw8159Labels = mixedMoment B node1084 node1084Labels := by
  calc
    mixedMoment B raw8159 raw8159Labels = mixedMoment B raw8159step0 raw8159step0Labels := by
      have hz : ∀ j, raw8159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8159step0 = (fun i j => raw8159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8159step0 raw8159; decide +kernel
      have hl : raw8159step0Labels = raw8159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8159 raw8159Labels permutation346 hz
    mixedMoment B raw8159step0 raw8159step0Labels = mixedMoment B raw8159step1 raw8159step1Labels := by
      have hz : ∀ j, raw8159step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8159step1 = (fun i j => raw8159step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8159step1 raw8159step0; decide +kernel
      have hl : raw8159step1Labels = raw8159step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8159step0 raw8159step0Labels permutation56 hz
    mixedMoment B raw8159step1 raw8159step1Labels = mixedMoment B raw8159step2 raw8159step2Labels := by
      have ha : raw8159step2 = (fun i j => raw8159step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8159step2 raw8159step1; decide +kernel
      have hl : raw8159step2Labels = raw8159step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8159step1 raw8159step1Labels permutation28 permutation5
    mixedMoment B raw8159step2 raw8159step2Labels = mixedMoment B raw8159step3 raw8159step3Labels := by
      have ha : raw8159step3 = raw8159step2 := by apply Matrix.ext; unfold raw8159step3 raw8159step2; decide +kernel
      have hl : raw8159step2Labels = labelEmbedding1 ∘ raw8159step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8159step2 raw8159step2Labels raw8159step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1084 node1084Labels := by rfl

theorem canonical8160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8160 raw8160Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw8160 raw8160Labels = mixedMoment B raw8160step0 raw8160step0Labels := by
      have hz : ∀ j, raw8160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8160step0 = (fun i j => raw8160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8160step0 raw8160; decide +kernel
      have hl : raw8160step0Labels = raw8160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8160 raw8160Labels permutation346 hz
    mixedMoment B raw8160step0 raw8160step0Labels = mixedMoment B raw8160step1 raw8160step1Labels := by
      have hz : ∀ j, raw8160step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8160step1 = (fun i j => raw8160step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8160step1 raw8160step0; decide +kernel
      have hl : raw8160step1Labels = raw8160step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8160step0 raw8160step0Labels permutation56 hz
    _ = mixedMoment B node2769 node2769Labels := by rfl

theorem canonical8161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8161 raw8161Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw8161 raw8161Labels = mixedMoment B raw8161step0 raw8161step0Labels := by
      have hz : ∀ j, raw8161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8161step0 = (fun i j => raw8161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8161step0 raw8161; decide +kernel
      have hl : raw8161step0Labels = raw8161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8161 raw8161Labels permutation346 hz
    mixedMoment B raw8161step0 raw8161step0Labels = mixedMoment B raw8161step1 raw8161step1Labels := by
      have ha : raw8161step1 = (fun i j => raw8161step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8161step1 raw8161step0; decide +kernel
      have hl : raw8161step1Labels = raw8161step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8161step0 raw8161step0Labels permutation128 permutation4
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical8162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8162 raw8162Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw8162 raw8162Labels = mixedMoment B raw8162step0 raw8162step0Labels := by
      have hz : ∀ j, raw8162 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8162step0 = (fun i j => raw8162 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8162step0 raw8162; decide +kernel
      have hl : raw8162step0Labels = raw8162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8162 raw8162Labels permutation265 hz
    mixedMoment B raw8162step0 raw8162step0Labels = mixedMoment B raw8162step1 raw8162step1Labels := by
      have ha : raw8162step1 = (fun i j => raw8162step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8162step1 raw8162step0; decide +kernel
      have hl : raw8162step1Labels = raw8162step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8162step0 raw8162step0Labels permutation128 permutation4
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical8163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8163 raw8163Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw8163 raw8163Labels = mixedMoment B raw8163step0 raw8163step0Labels := by
      have hz : ∀ j, raw8163 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8163step0 = (fun i j => raw8163 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8163step0 raw8163; decide +kernel
      have hl : raw8163step0Labels = raw8163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8163 raw8163Labels permutation346 hz
    mixedMoment B raw8163step0 raw8163step0Labels = mixedMoment B raw8163step1 raw8163step1Labels := by
      have hz : ∀ j, raw8163step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8163step1 = (fun i j => raw8163step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8163step1 raw8163step0; decide +kernel
      have hl : raw8163step1Labels = raw8163step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8163step0 raw8163step0Labels permutation56 hz
    mixedMoment B raw8163step1 raw8163step1Labels = mixedMoment B raw8163step2 raw8163step2Labels := by
      have ha : raw8163step2 = (fun i j => raw8163step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8163step2 raw8163step1; decide +kernel
      have hl : raw8163step2Labels = raw8163step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8163step1 raw8163step1Labels permutation27 permutation4
    _ = mixedMoment B node3055 node3055Labels := by rfl

theorem canonical8164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8164 raw8164Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw8164 raw8164Labels = mixedMoment B raw8164step0 raw8164step0Labels := by
      have hz : ∀ j, raw8164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8164step0 = (fun i j => raw8164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8164step0 raw8164; decide +kernel
      have hl : raw8164step0Labels = raw8164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8164 raw8164Labels permutation346 hz
    mixedMoment B raw8164step0 raw8164step0Labels = mixedMoment B raw8164step1 raw8164step1Labels := by
      have hz : ∀ j, raw8164step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8164step1 = (fun i j => raw8164step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8164step1 raw8164step0; decide +kernel
      have hl : raw8164step1Labels = raw8164step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8164step0 raw8164step0Labels permutation56 hz
    mixedMoment B raw8164step1 raw8164step1Labels = mixedMoment B raw8164step2 raw8164step2Labels := by
      have ha : raw8164step2 = (fun i j => raw8164step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8164step2 raw8164step1; decide +kernel
      have hl : raw8164step2Labels = raw8164step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8164step1 raw8164step1Labels permutation26 permutation4
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical8165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8165 raw8165Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw8165 raw8165Labels = mixedMoment B raw8165step0 raw8165step0Labels := by
      have hz : ∀ j, raw8165 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8165step0 = (fun i j => raw8165 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8165step0 raw8165; decide +kernel
      have hl : raw8165step0Labels = raw8165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8165 raw8165Labels permutation346 hz
    mixedMoment B raw8165step0 raw8165step0Labels = mixedMoment B raw8165step1 raw8165step1Labels := by
      have hz : ∀ j, raw8165step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8165step1 = (fun i j => raw8165step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8165step1 raw8165step0; decide +kernel
      have hl : raw8165step1Labels = raw8165step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8165step0 raw8165step0Labels permutation56 hz
    mixedMoment B raw8165step1 raw8165step1Labels = mixedMoment B raw8165step2 raw8165step2Labels := by
      have ha : raw8165step2 = (fun i j => raw8165step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8165step2 raw8165step1; decide +kernel
      have hl : raw8165step2Labels = raw8165step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8165step1 raw8165step1Labels permutation9 permutation2
    _ = mixedMoment B node3913 node3913Labels := by rfl

theorem canonical8166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8166 raw8166Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw8166 raw8166Labels = mixedMoment B raw8166step0 raw8166step0Labels := by
      have hz : ∀ j, raw8166 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8166step0 = (fun i j => raw8166 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8166step0 raw8166; decide +kernel
      have hl : raw8166step0Labels = raw8166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8166 raw8166Labels permutation346 hz
    mixedMoment B raw8166step0 raw8166step0Labels = mixedMoment B raw8166step1 raw8166step1Labels := by
      have hz : ∀ j, raw8166step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8166step1 = (fun i j => raw8166step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8166step1 raw8166step0; decide +kernel
      have hl : raw8166step1Labels = raw8166step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8166step0 raw8166step0Labels permutation56 hz
    mixedMoment B raw8166step1 raw8166step1Labels = mixedMoment B raw8166step2 raw8166step2Labels := by
      have ha : raw8166step2 = (fun i j => raw8166step1 (permutation12 i) (permutation0 j)) := by apply Matrix.ext; unfold raw8166step2 raw8166step1; decide +kernel
      have hl : raw8166step2Labels = raw8166step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8166step1 raw8166step1Labels permutation12 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical8167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8167 raw8167Labels = mixedMoment B node1268 node1268Labels := by
  calc
    mixedMoment B raw8167 raw8167Labels = mixedMoment B raw8167step0 raw8167step0Labels := by
      have hz : ∀ j, raw8167 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8167step0 = (fun i j => raw8167 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8167step0 raw8167; decide +kernel
      have hl : raw8167step0Labels = raw8167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8167 raw8167Labels permutation346 hz
    mixedMoment B raw8167step0 raw8167step0Labels = mixedMoment B raw8167step1 raw8167step1Labels := by
      have ha : raw8167step1 = (fun i j => raw8167step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8167step1 raw8167step0; decide +kernel
      have hl : raw8167step1Labels = raw8167step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8167step0 raw8167step0Labels permutation38 permutation2
    _ = mixedMoment B node1268 node1268Labels := by rfl

theorem canonical8168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8168 raw8168Labels = mixedMoment B node1268 node1268Labels := by
  calc
    mixedMoment B raw8168 raw8168Labels = mixedMoment B raw8168step0 raw8168step0Labels := by
      have hz : ∀ j, raw8168 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8168step0 = (fun i j => raw8168 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8168step0 raw8168; decide +kernel
      have hl : raw8168step0Labels = raw8168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8168 raw8168Labels permutation265 hz
    mixedMoment B raw8168step0 raw8168step0Labels = mixedMoment B raw8168step1 raw8168step1Labels := by
      have ha : raw8168step1 = (fun i j => raw8168step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8168step1 raw8168step0; decide +kernel
      have hl : raw8168step1Labels = raw8168step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8168step0 raw8168step0Labels permutation38 permutation2
    _ = mixedMoment B node1268 node1268Labels := by rfl

theorem canonical8169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8169 raw8169Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw8169 raw8169Labels = mixedMoment B raw8169step0 raw8169step0Labels := by
      have hz : ∀ j, raw8169 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8169step0 = (fun i j => raw8169 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8169step0 raw8169; decide +kernel
      have hl : raw8169step0Labels = raw8169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8169 raw8169Labels permutation346 hz
    mixedMoment B raw8169step0 raw8169step0Labels = mixedMoment B raw8169step1 raw8169step1Labels := by
      have hz : ∀ j, raw8169step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8169step1 = (fun i j => raw8169step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8169step1 raw8169step0; decide +kernel
      have hl : raw8169step1Labels = raw8169step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8169step0 raw8169step0Labels permutation56 hz
    _ = mixedMoment B node1306 node1306Labels := by rfl

theorem canonical8170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8170 raw8170Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw8170 raw8170Labels = mixedMoment B raw8170step0 raw8170step0Labels := by
      have hz : ∀ j, raw8170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8170step0 = (fun i j => raw8170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8170step0 raw8170; decide +kernel
      have hl : raw8170step0Labels = raw8170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8170 raw8170Labels permutation346 hz
    mixedMoment B raw8170step0 raw8170step0Labels = mixedMoment B raw8170step1 raw8170step1Labels := by
      have hz : ∀ j, raw8170step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8170step1 = (fun i j => raw8170step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8170step1 raw8170step0; decide +kernel
      have hl : raw8170step1Labels = raw8170step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8170step0 raw8170step0Labels permutation56 hz
    mixedMoment B raw8170step1 raw8170step1Labels = mixedMoment B raw8170step2 raw8170step2Labels := by
      have ha : raw8170step2 = (fun i j => raw8170step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8170step2 raw8170step1; decide +kernel
      have hl : raw8170step2Labels = raw8170step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8170step1 raw8170step1Labels permutation9 permutation2
    _ = mixedMoment B node1273 node1273Labels := by rfl

theorem canonical8171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8171 raw8171Labels = mixedMoment B node1272 node1272Labels := by
  calc
    mixedMoment B raw8171 raw8171Labels = mixedMoment B raw8171step0 raw8171step0Labels := by
      have hz : ∀ j, raw8171 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8171step0 = (fun i j => raw8171 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8171step0 raw8171; decide +kernel
      have hl : raw8171step0Labels = raw8171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8171 raw8171Labels permutation346 hz
    mixedMoment B raw8171step0 raw8171step0Labels = mixedMoment B raw8171step1 raw8171step1Labels := by
      have hz : ∀ j, raw8171step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8171step1 = (fun i j => raw8171step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8171step1 raw8171step0; decide +kernel
      have hl : raw8171step1Labels = raw8171step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8171step0 raw8171step0Labels permutation56 hz
    _ = mixedMoment B node1272 node1272Labels := by rfl

theorem canonical8172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8172 raw8172Labels = mixedMoment B node2571 node2571Labels := by
  calc
    mixedMoment B raw8172 raw8172Labels = mixedMoment B raw8172step0 raw8172step0Labels := by
      have ha : raw8172step0 = (fun i j => raw8172 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8172step0 raw8172; decide +kernel
      have hl : raw8172step0Labels = raw8172Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8172 raw8172Labels permutation182 permutation2
    _ = mixedMoment B node2571 node2571Labels := by rfl

theorem canonical8173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8173 raw8173Labels = mixedMoment B node2639 node2639Labels := by
  calc
    mixedMoment B raw8173 raw8173Labels = mixedMoment B raw8173step0 raw8173step0Labels := by
      have hz : ∀ j, raw8173 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8173step0 = (fun i j => raw8173 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8173step0 raw8173; decide +kernel
      have hl : raw8173step0Labels = raw8173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8173 raw8173Labels permutation346 hz
    mixedMoment B raw8173step0 raw8173step0Labels = mixedMoment B raw8173step1 raw8173step1Labels := by
      have ha : raw8173step1 = (fun i j => raw8173step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8173step1 raw8173step0; decide +kernel
      have hl : raw8173step1Labels = raw8173step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8173step0 raw8173step0Labels permutation38 permutation2
    _ = mixedMoment B node2639 node2639Labels := by rfl

theorem canonical8174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8174 raw8174Labels = mixedMoment B node2759 node2759Labels := by
  calc
    mixedMoment B raw8174 raw8174Labels = mixedMoment B raw8174step0 raw8174step0Labels := by
      have hz : ∀ j, raw8174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8174step0 = (fun i j => raw8174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8174step0 raw8174; decide +kernel
      have hl : raw8174step0Labels = raw8174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8174 raw8174Labels permutation346 hz
    mixedMoment B raw8174step0 raw8174step0Labels = mixedMoment B raw8174step1 raw8174step1Labels := by
      have ha : raw8174step1 = (fun i j => raw8174step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8174step1 raw8174step0; decide +kernel
      have hl : raw8174step1Labels = raw8174step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8174step0 raw8174step0Labels permutation40 permutation2
    _ = mixedMoment B node2759 node2759Labels := by rfl

theorem canonical8175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8175 raw8175Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw8175 raw8175Labels = mixedMoment B raw8175step0 raw8175step0Labels := by
      have hz : ∀ j, raw8175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8175step0 = (fun i j => raw8175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8175step0 raw8175; decide +kernel
      have hl : raw8175step0Labels = raw8175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8175 raw8175Labels permutation346 hz
    mixedMoment B raw8175step0 raw8175step0Labels = mixedMoment B raw8175step1 raw8175step1Labels := by
      have ha : raw8175step1 = (fun i j => raw8175step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8175step1 raw8175step0; decide +kernel
      have hl : raw8175step1Labels = raw8175step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8175step0 raw8175step0Labels permutation42 permutation2
    _ = mixedMoment B node2763 node2763Labels := by rfl

theorem canonical8176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8176 raw8176Labels = mixedMoment B node2571 node2571Labels := by
  calc
    mixedMoment B raw8176 raw8176Labels = mixedMoment B raw8176step0 raw8176step0Labels := by
      have ha : raw8176step0 = (fun i j => raw8176 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8176step0 raw8176; decide +kernel
      have hl : raw8176step0Labels = raw8176Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8176 raw8176Labels permutation158 permutation2
    _ = mixedMoment B node2571 node2571Labels := by rfl

theorem canonical8177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8177 raw8177Labels = mixedMoment B node2600 node2600Labels := by
  calc
    mixedMoment B raw8177 raw8177Labels = mixedMoment B raw8177step0 raw8177step0Labels := by
      have hz : ∀ j, raw8177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8177step0 = (fun i j => raw8177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8177step0 raw8177; decide +kernel
      have hl : raw8177step0Labels = raw8177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8177 raw8177Labels permutation346 hz
    _ = mixedMoment B node2600 node2600Labels := by rfl

theorem canonical8178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8178 raw8178Labels = mixedMoment B node2575 node2575Labels := by
  calc
    mixedMoment B raw8178 raw8178Labels = mixedMoment B raw8178step0 raw8178step0Labels := by
      have hz : ∀ j, raw8178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8178step0 = (fun i j => raw8178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8178step0 raw8178; decide +kernel
      have hl : raw8178step0Labels = raw8178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8178 raw8178Labels permutation346 hz
    mixedMoment B raw8178step0 raw8178step0Labels = mixedMoment B raw8178step1 raw8178step1Labels := by
      have ha : raw8178step1 = (fun i j => raw8178step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8178step1 raw8178step0; decide +kernel
      have hl : raw8178step1Labels = raw8178step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8178step0 raw8178step0Labels permutation33 permutation2
    _ = mixedMoment B node2575 node2575Labels := by rfl

theorem canonical8179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8179 raw8179Labels = mixedMoment B node1433 node1433Labels := by
  calc
    mixedMoment B raw8179 raw8179Labels = mixedMoment B raw8179step0 raw8179step0Labels := by
      have hz : ∀ j, raw8179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8179step0 = (fun i j => raw8179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8179step0 raw8179; decide +kernel
      have hl : raw8179step0Labels = raw8179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8179 raw8179Labels permutation346 hz
    mixedMoment B raw8179step0 raw8179step0Labels = mixedMoment B raw8179step1 raw8179step1Labels := by
      have ha : raw8179step1 = (fun i j => raw8179step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8179step1 raw8179step0; decide +kernel
      have hl : raw8179step1Labels = raw8179step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8179step0 raw8179step0Labels permutation128 permutation4
    _ = mixedMoment B node1433 node1433Labels := by rfl

theorem canonical8180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8180 raw8180Labels = mixedMoment B node2639 node2639Labels := by
  calc
    mixedMoment B raw8180 raw8180Labels = mixedMoment B raw8180step0 raw8180step0Labels := by
      have hz : ∀ j, raw8180 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8180step0 = (fun i j => raw8180 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8180step0 raw8180; decide +kernel
      have hl : raw8180step0Labels = raw8180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8180 raw8180Labels permutation265 hz
    mixedMoment B raw8180step0 raw8180step0Labels = mixedMoment B raw8180step1 raw8180step1Labels := by
      have ha : raw8180step1 = (fun i j => raw8180step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8180step1 raw8180step0; decide +kernel
      have hl : raw8180step1Labels = raw8180step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8180step0 raw8180step0Labels permutation38 permutation2
    _ = mixedMoment B node2639 node2639Labels := by rfl

theorem canonical8181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8181 raw8181Labels = mixedMoment B node2643 node2643Labels := by
  calc
    mixedMoment B raw8181 raw8181Labels = mixedMoment B raw8181step0 raw8181step0Labels := by
      have hz : ∀ j, raw8181 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8181step0 = (fun i j => raw8181 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8181step0 raw8181; decide +kernel
      have hl : raw8181step0Labels = raw8181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8181 raw8181Labels permutation346 hz
    mixedMoment B raw8181step0 raw8181step0Labels = mixedMoment B raw8181step1 raw8181step1Labels := by
      have hz : ∀ j, raw8181step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8181step1 = (fun i j => raw8181step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8181step1 raw8181step0; decide +kernel
      have hl : raw8181step1Labels = raw8181step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8181step0 raw8181step0Labels permutation56 hz
    mixedMoment B raw8181step1 raw8181step1Labels = mixedMoment B raw8181step2 raw8181step2Labels := by
      have ha : raw8181step2 = (fun i j => raw8181step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8181step2 raw8181step1; decide +kernel
      have hl : raw8181step2Labels = raw8181step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8181step1 raw8181step1Labels permutation9 permutation2
    _ = mixedMoment B node2643 node2643Labels := by rfl

theorem canonical8182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8182 raw8182Labels = mixedMoment B node1437 node1437Labels := by
  calc
    mixedMoment B raw8182 raw8182Labels = mixedMoment B raw8182step0 raw8182step0Labels := by
      have hz : ∀ j, raw8182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8182step0 = (fun i j => raw8182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8182step0 raw8182; decide +kernel
      have hl : raw8182step0Labels = raw8182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8182 raw8182Labels permutation346 hz
    mixedMoment B raw8182step0 raw8182step0Labels = mixedMoment B raw8182step1 raw8182step1Labels := by
      have hz : ∀ j, raw8182step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8182step1 = (fun i j => raw8182step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8182step1 raw8182step0; decide +kernel
      have hl : raw8182step1Labels = raw8182step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8182step0 raw8182step0Labels permutation56 hz
    mixedMoment B raw8182step1 raw8182step1Labels = mixedMoment B raw8182step2 raw8182step2Labels := by
      have ha : raw8182step2 = (fun i j => raw8182step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8182step2 raw8182step1; decide +kernel
      have hl : raw8182step2Labels = raw8182step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8182step1 raw8182step1Labels permutation27 permutation4
    _ = mixedMoment B node1437 node1437Labels := by rfl

theorem canonical8183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8183 raw8183Labels = mixedMoment B node2575 node2575Labels := by
  calc
    mixedMoment B raw8183 raw8183Labels = mixedMoment B raw8183step0 raw8183step0Labels := by
      have hz : ∀ j, raw8183 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8183step0 = (fun i j => raw8183 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8183step0 raw8183; decide +kernel
      have hl : raw8183step0Labels = raw8183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8183 raw8183Labels permutation265 hz
    mixedMoment B raw8183step0 raw8183step0Labels = mixedMoment B raw8183step1 raw8183step1Labels := by
      have ha : raw8183step1 = (fun i j => raw8183step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8183step1 raw8183step0; decide +kernel
      have hl : raw8183step1Labels = raw8183step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8183step0 raw8183step0Labels permutation33 permutation2
    _ = mixedMoment B node2575 node2575Labels := by rfl

theorem canonical8184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8184 raw8184Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw8184 raw8184Labels = mixedMoment B raw8184step0 raw8184step0Labels := by
      have hz : ∀ j, raw8184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8184step0 = (fun i j => raw8184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8184step0 raw8184; decide +kernel
      have hl : raw8184step0Labels = raw8184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8184 raw8184Labels permutation346 hz
    mixedMoment B raw8184step0 raw8184step0Labels = mixedMoment B raw8184step1 raw8184step1Labels := by
      have hz : ∀ j, raw8184step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8184step1 = (fun i j => raw8184step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8184step1 raw8184step0; decide +kernel
      have hl : raw8184step1Labels = raw8184step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8184step0 raw8184step0Labels permutation56 hz
    mixedMoment B raw8184step1 raw8184step1Labels = mixedMoment B raw8184step2 raw8184step2Labels := by
      have ha : raw8184step2 = (fun i j => raw8184step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8184step2 raw8184step1; decide +kernel
      have hl : raw8184step2Labels = raw8184step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8184step1 raw8184step1Labels permutation9 permutation2
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical8185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8185 raw8185Labels = mixedMoment B node1433 node1433Labels := by
  calc
    mixedMoment B raw8185 raw8185Labels = mixedMoment B raw8185step0 raw8185step0Labels := by
      have hz : ∀ j, raw8185 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8185step0 = (fun i j => raw8185 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8185step0 raw8185; decide +kernel
      have hl : raw8185step0Labels = raw8185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8185 raw8185Labels permutation265 hz
    mixedMoment B raw8185step0 raw8185step0Labels = mixedMoment B raw8185step1 raw8185step1Labels := by
      have ha : raw8185step1 = (fun i j => raw8185step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8185step1 raw8185step0; decide +kernel
      have hl : raw8185step1Labels = raw8185step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8185step0 raw8185step0Labels permutation128 permutation4
    _ = mixedMoment B node1433 node1433Labels := by rfl

theorem canonical8186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8186 raw8186Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw8186 raw8186Labels = mixedMoment B raw8186step0 raw8186step0Labels := by
      have hz : ∀ j, raw8186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8186step0 = (fun i j => raw8186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8186step0 raw8186; decide +kernel
      have hl : raw8186step0Labels = raw8186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8186 raw8186Labels permutation346 hz
    mixedMoment B raw8186step0 raw8186step0Labels = mixedMoment B raw8186step1 raw8186step1Labels := by
      have hz : ∀ j, raw8186step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8186step1 = (fun i j => raw8186step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8186step1 raw8186step0; decide +kernel
      have hl : raw8186step1Labels = raw8186step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8186step0 raw8186step0Labels permutation56 hz
    mixedMoment B raw8186step1 raw8186step1Labels = mixedMoment B raw8186step2 raw8186step2Labels := by
      have ha : raw8186step2 = (fun i j => raw8186step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8186step2 raw8186step1; decide +kernel
      have hl : raw8186step2Labels = raw8186step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8186step1 raw8186step1Labels permutation26 permutation4
    _ = mixedMoment B node1436 node1436Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8253 raw8253Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw8253 raw8253Labels = mixedMoment B raw8253step0 raw8253step0Labels := by
      have hz : ∀ j, raw8253 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8253step0 = (fun i j => raw8253 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8253step0 raw8253; decide +kernel
      have hl : raw8253step0Labels = raw8253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8253 raw8253Labels permutation346 hz
    mixedMoment B raw8253step0 raw8253step0Labels = mixedMoment B raw8253step1 raw8253step1Labels := by
      have hz : ∀ j, raw8253step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8253step1 = (fun i j => raw8253step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8253step1 raw8253step0; decide +kernel
      have hl : raw8253step1Labels = raw8253step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8253step0 raw8253step0Labels permutation56 hz
    _ = mixedMoment B node3098 node3098Labels := by rfl

theorem canonical8254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8254 raw8254Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw8254 raw8254Labels = mixedMoment B raw8254step0 raw8254step0Labels := by
      have hz : ∀ j, raw8254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8254step0 = (fun i j => raw8254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8254step0 raw8254; decide +kernel
      have hl : raw8254step0Labels = raw8254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8254 raw8254Labels permutation346 hz
    mixedMoment B raw8254step0 raw8254step0Labels = mixedMoment B raw8254step1 raw8254step1Labels := by
      have ha : raw8254step1 = (fun i j => raw8254step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8254step1 raw8254step0; decide +kernel
      have hl : raw8254step1Labels = raw8254step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8254step0 raw8254step0Labels permutation151 permutation2
    mixedMoment B raw8254step1 raw8254step1Labels = mixedMoment B raw8254step2 raw8254step2Labels := by
      have ha : raw8254step2 = -raw8254step1 := by apply Matrix.ext; change ∀ i j, raw8254step2 i j = -(raw8254step1 i j); unfold raw8254step2 raw8254step1; decide +kernel
      have hl : raw8254step2Labels = raw8254step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical8255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8255 raw8255Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw8255 raw8255Labels = mixedMoment B raw8255step0 raw8255step0Labels := by
      have hz : ∀ j, raw8255 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8255step0 = (fun i j => raw8255 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8255step0 raw8255; decide +kernel
      have hl : raw8255step0Labels = raw8255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8255 raw8255Labels permutation265 hz
    mixedMoment B raw8255step0 raw8255step0Labels = mixedMoment B raw8255step1 raw8255step1Labels := by
      have ha : raw8255step1 = (fun i j => raw8255step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8255step1 raw8255step0; decide +kernel
      have hl : raw8255step1Labels = raw8255step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8255step0 raw8255step0Labels permutation151 permutation2
    mixedMoment B raw8255step1 raw8255step1Labels = mixedMoment B raw8255step2 raw8255step2Labels := by
      have ha : raw8255step2 = -raw8255step1 := by apply Matrix.ext; change ∀ i j, raw8255step2 i j = -(raw8255step1 i j); unfold raw8255step2 raw8255step1; decide +kernel
      have hl : raw8255step2Labels = raw8255step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical8256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8256 raw8256Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw8256 raw8256Labels = mixedMoment B raw8256step0 raw8256step0Labels := by
      have hz : ∀ j, raw8256 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8256step0 = (fun i j => raw8256 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8256step0 raw8256; decide +kernel
      have hl : raw8256step0Labels = raw8256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8256 raw8256Labels permutation346 hz
    mixedMoment B raw8256step0 raw8256step0Labels = mixedMoment B raw8256step1 raw8256step1Labels := by
      have hz : ∀ j, raw8256step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8256step1 = (fun i j => raw8256step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8256step1 raw8256step0; decide +kernel
      have hl : raw8256step1Labels = raw8256step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8256step0 raw8256step0Labels permutation56 hz
    mixedMoment B raw8256step1 raw8256step1Labels = mixedMoment B raw8256step2 raw8256step2Labels := by
      have ha : raw8256step2 = (fun i j => raw8256step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8256step2 raw8256step1; decide +kernel
      have hl : raw8256step2Labels = raw8256step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8256step1 raw8256step1Labels permutation31 permutation2
    mixedMoment B raw8256step2 raw8256step2Labels = mixedMoment B raw8256step3 raw8256step3Labels := by
      have ha : raw8256step3 = -raw8256step2 := by apply Matrix.ext; change ∀ i j, raw8256step3 i j = -(raw8256step2 i j); unfold raw8256step3 raw8256step2; decide +kernel
      have hl : raw8256step3Labels = raw8256step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3583 node3583Labels := by rfl

theorem canonical8257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8257 raw8257Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw8257 raw8257Labels = mixedMoment B raw8257step0 raw8257step0Labels := by
      have hz : ∀ j, raw8257 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8257step0 = (fun i j => raw8257 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8257step0 raw8257; decide +kernel
      have hl : raw8257step0Labels = raw8257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8257 raw8257Labels permutation346 hz
    mixedMoment B raw8257step0 raw8257step0Labels = mixedMoment B raw8257step1 raw8257step1Labels := by
      have hz : ∀ j, raw8257step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8257step1 = (fun i j => raw8257step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8257step1 raw8257step0; decide +kernel
      have hl : raw8257step1Labels = raw8257step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8257step0 raw8257step0Labels permutation56 hz
    mixedMoment B raw8257step1 raw8257step1Labels = mixedMoment B raw8257step2 raw8257step2Labels := by
      have ha : raw8257step2 = (fun i j => raw8257step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8257step2 raw8257step1; decide +kernel
      have hl : raw8257step2Labels = raw8257step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8257step1 raw8257step1Labels permutation26 permutation4
    mixedMoment B raw8257step2 raw8257step2Labels = mixedMoment B raw8257step3 raw8257step3Labels := by
      have ha : raw8257step3 = -raw8257step2 := by apply Matrix.ext; change ∀ i j, raw8257step3 i j = -(raw8257step2 i j); unfold raw8257step3 raw8257step2; decide +kernel
      have hl : raw8257step3Labels = raw8257step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3583 node3583Labels := by rfl

theorem canonical8258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8258 raw8258Labels = mixedMoment B node1404 node1404Labels := by
  calc
    mixedMoment B raw8258 raw8258Labels = mixedMoment B raw8258step0 raw8258step0Labels := by
      have hz : ∀ j, raw8258 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8258step0 = (fun i j => raw8258 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8258step0 raw8258; decide +kernel
      have hl : raw8258step0Labels = raw8258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8258 raw8258Labels permutation346 hz
    mixedMoment B raw8258step0 raw8258step0Labels = mixedMoment B raw8258step1 raw8258step1Labels := by
      have ha : raw8258step1 = (fun i j => raw8258step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8258step1 raw8258step0; decide +kernel
      have hl : raw8258step1Labels = raw8258step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8258step0 raw8258step0Labels permutation40 permutation2
    _ = mixedMoment B node1404 node1404Labels := by rfl

theorem canonical8259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8259 raw8259Labels = mixedMoment B node1404 node1404Labels := by
  calc
    mixedMoment B raw8259 raw8259Labels = mixedMoment B raw8259step0 raw8259step0Labels := by
      have hz : ∀ j, raw8259 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8259step0 = (fun i j => raw8259 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8259step0 raw8259; decide +kernel
      have hl : raw8259step0Labels = raw8259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8259 raw8259Labels permutation265 hz
    mixedMoment B raw8259step0 raw8259step0Labels = mixedMoment B raw8259step1 raw8259step1Labels := by
      have ha : raw8259step1 = (fun i j => raw8259step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8259step1 raw8259step0; decide +kernel
      have hl : raw8259step1Labels = raw8259step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8259step0 raw8259step0Labels permutation40 permutation2
    _ = mixedMoment B node1404 node1404Labels := by rfl

theorem canonical8260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8260 raw8260Labels = mixedMoment B node1440 node1440Labels := by
  calc
    mixedMoment B raw8260 raw8260Labels = mixedMoment B raw8260step0 raw8260step0Labels := by
      have hz : ∀ j, raw8260 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8260step0 = (fun i j => raw8260 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8260step0 raw8260; decide +kernel
      have hl : raw8260step0Labels = raw8260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8260 raw8260Labels permutation346 hz
    mixedMoment B raw8260step0 raw8260step0Labels = mixedMoment B raw8260step1 raw8260step1Labels := by
      have hz : ∀ j, raw8260step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8260step1 = (fun i j => raw8260step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8260step1 raw8260step0; decide +kernel
      have hl : raw8260step1Labels = raw8260step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8260step0 raw8260step0Labels permutation56 hz
    _ = mixedMoment B node1440 node1440Labels := by rfl

theorem canonical8261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8261 raw8261Labels = mixedMoment B node1418 node1418Labels := by
  calc
    mixedMoment B raw8261 raw8261Labels = mixedMoment B raw8261step0 raw8261step0Labels := by
      have hz : ∀ j, raw8261 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8261step0 = (fun i j => raw8261 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8261step0 raw8261; decide +kernel
      have hl : raw8261step0Labels = raw8261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8261 raw8261Labels permutation346 hz
    mixedMoment B raw8261step0 raw8261step0Labels = mixedMoment B raw8261step1 raw8261step1Labels := by
      have hz : ∀ j, raw8261step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8261step1 = (fun i j => raw8261step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8261step1 raw8261step0; decide +kernel
      have hl : raw8261step1Labels = raw8261step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8261step0 raw8261step0Labels permutation56 hz
    _ = mixedMoment B node1418 node1418Labels := by rfl

theorem canonical8262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8262 raw8262Labels = mixedMoment B node2983 node2983Labels := by
  calc
    mixedMoment B raw8262 raw8262Labels = mixedMoment B raw8262step0 raw8262step0Labels := by
      have ha : raw8262step0 = (fun i j => raw8262 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8262step0 raw8262; decide +kernel
      have hl : raw8262step0Labels = raw8262Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8262 raw8262Labels permutation184 permutation2
    _ = mixedMoment B node2983 node2983Labels := by rfl

theorem canonical8263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8263 raw8263Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw8263 raw8263Labels = mixedMoment B raw8263step0 raw8263step0Labels := by
      have hz : ∀ j, raw8263 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8263step0 = (fun i j => raw8263 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8263step0 raw8263; decide +kernel
      have hl : raw8263step0Labels = raw8263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8263 raw8263Labels permutation346 hz
    mixedMoment B raw8263step0 raw8263step0Labels = mixedMoment B raw8263step1 raw8263step1Labels := by
      have ha : raw8263step1 = (fun i j => raw8263step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8263step1 raw8263step0; decide +kernel
      have hl : raw8263step1Labels = raw8263step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8263step0 raw8263step0Labels permutation40 permutation2
    _ = mixedMoment B node2952 node2952Labels := by rfl

theorem canonical8264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8264 raw8264Labels = mixedMoment B node3096 node3096Labels := by
  calc
    mixedMoment B raw8264 raw8264Labels = mixedMoment B raw8264step0 raw8264step0Labels := by
      have hz : ∀ j, raw8264 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8264step0 = (fun i j => raw8264 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8264step0 raw8264; decide +kernel
      have hl : raw8264step0Labels = raw8264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8264 raw8264Labels permutation346 hz
    mixedMoment B raw8264step0 raw8264step0Labels = mixedMoment B raw8264step1 raw8264step1Labels := by
      have ha : raw8264step1 = (fun i j => raw8264step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8264step1 raw8264step0; decide +kernel
      have hl : raw8264step1Labels = raw8264step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8264step0 raw8264step0Labels permutation40 permutation2
    _ = mixedMoment B node3096 node3096Labels := by rfl

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

theorem canonical5215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5215 = injectiveMoment H raw5215step0 := by
      have hz : ∀ j, raw5215 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5215step0 = (fun i j => raw5215 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5215 permutation27 hz
    injectiveMoment H raw5215step0 = injectiveMoment H raw5215step1 := by
      have hz : ∀ j, raw5215step0 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw5215step1 = (fun i j => raw5215step0 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5215step0 permutation7 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical238
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7636 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7636 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7636 = injectiveMoment H raw7636step0 := by
      have heq : raw7636step0 = (fun i j => raw7636 (permutation15 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7636 permutation15 permutation1
    _ = injectiveMoment H node46 := by rfl

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

theorem canonical792 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw792 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw792 = injectiveMoment H raw792step0 := by
      have heq : raw792step0 = -raw792 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw792).symm
    injectiveMoment H raw792step0 = injectiveMoment H raw792step1 := by
      have heq : raw792step1 = (fun i j => raw792step0 (permutation12 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw792step0 permutation12 permutation8
    _ = injectiveMoment H node177 := by rfl

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

theorem sound37 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node37 = Sparse.eval value37 (momentVector H) := by
  have hc : momentVector H 13 = injectiveMoment H node37 := rfl
  simp [value37, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

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

theorem sound177 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node177 = Sparse.eval value177 (momentVector H) := by
  have heq : pivotMatrix177 = (fun u v => node177 (pivotPermutation177 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node177 = injectiveMoment H pivotMatrix177 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix177 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix177 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix177 (0 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (0 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix177 (1 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (1 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix177 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node177 + (injectiveMoment H (mergeFirst pivotMatrix177 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix177 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix177 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value177, value36, value37, value41, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node412 node412Labels = Sparse.eval singlePairValue412 (familyPairVector B) := by
  have hp := single_label_three B hB node412
  have hl : node412Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node412 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 1) = PairSemantics.raw5215 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node412 PairSemantics.raw5215; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5215 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 2) = PairSemantics.raw7636 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node412 PairSemantics.raw7636; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7636 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node412 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value177 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 4) = PairSemantics.raw792 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node412 PairSemantics.raw792; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical792 hH).trans (PairSemantics.sound177 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue412, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value46, PairSemantics.value177, Sparse.eval] at hp ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton2776 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2776 node2776Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node412 node412Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw278 singletonSmall2776
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2776) = raw278Labels := by decide +kernel
  rw [hl, canonical278 B hB] at h
  have hc0 : mixedMoment B raw278 (Fin.cases (0 : Fin 1) singletonSmall2776) =
      mixedMoment B node412 node412Labels := by
    have ha : raw278 = raw279 := by apply Matrix.ext; unfold raw278 raw279; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2776 = raw279Labels := by decide +kernel
    rw [ha, hj, canonical279 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1070 node1070Labels = Sparse.eval nodeValue1070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1070) = mixedMoment B node1070 node1070Labels := rfl
  simpa [nodeValue1070, Sparse.eval] using hc.symm

theorem sound1072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1072 node1072Labels = Sparse.eval nodeValue1072 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1072) = mixedMoment B node1072 node1072Labels := rfl
  simpa [nodeValue1072, Sparse.eval] using hc.symm

theorem sound1076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1076 node1076Labels = Sparse.eval nodeValue1076 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1076) = mixedMoment B node1076 node1076Labels := rfl
  simpa [nodeValue1076, Sparse.eval] using hc.symm

theorem sound1084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1084 node1084Labels = Sparse.eval nodeValue1084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1084) = mixedMoment B node1084 node1084Labels := rfl
  simpa [nodeValue1084, Sparse.eval] using hc.symm

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

theorem sound1268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1268 node1268Labels = Sparse.eval nodeValue1268 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1268) = mixedMoment B node1268 node1268Labels := rfl
  simpa [nodeValue1268, Sparse.eval] using hc.symm

theorem sound1272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1272 node1272Labels = Sparse.eval nodeValue1272 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1272) = mixedMoment B node1272 node1272Labels := rfl
  simpa [nodeValue1272, Sparse.eval] using hc.symm

theorem sound1273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1273 node1273Labels = Sparse.eval nodeValue1273 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1273) = mixedMoment B node1273 node1273Labels := rfl
  simpa [nodeValue1273, Sparse.eval] using hc.symm

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

theorem sound1306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1306 node1306Labels = Sparse.eval nodeValue1306 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1306) = mixedMoment B node1306 node1306Labels := rfl
  simpa [nodeValue1306, Sparse.eval] using hc.symm

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

theorem sound1404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1404 node1404Labels = Sparse.eval nodeValue1404 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1404) = mixedMoment B node1404 node1404Labels := rfl
  simpa [nodeValue1404, Sparse.eval] using hc.symm

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

theorem sound1408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1408 node1408Labels = Sparse.eval nodeValue1408 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1408) = mixedMoment B node1408 node1408Labels := rfl
  simpa [nodeValue1408, Sparse.eval] using hc.symm

theorem sound1418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1418 node1418Labels = Sparse.eval nodeValue1418 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1418) = mixedMoment B node1418 node1418Labels := rfl
  simpa [nodeValue1418, Sparse.eval] using hc.symm

theorem sound1433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1433 node1433Labels = Sparse.eval nodeValue1433 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1433) = mixedMoment B node1433 node1433Labels := rfl
  simpa [nodeValue1433, Sparse.eval] using hc.symm

theorem sound1436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1436 node1436Labels = Sparse.eval nodeValue1436 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1436) = mixedMoment B node1436 node1436Labels := rfl
  simpa [nodeValue1436, Sparse.eval] using hc.symm

theorem sound1437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1437 node1437Labels = Sparse.eval nodeValue1437 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1437) = mixedMoment B node1437 node1437Labels := rfl
  simpa [nodeValue1437, Sparse.eval] using hc.symm

theorem sound1440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1440 node1440Labels = Sparse.eval nodeValue1440 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1440) = mixedMoment B node1440 node1440Labels := rfl
  simpa [nodeValue1440, Sparse.eval] using hc.symm

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

theorem sound2500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2500 node2500Labels = Sparse.eval nodeValue2500 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2500) = mixedMoment B node2500 node2500Labels := rfl
  simpa [nodeValue2500, Sparse.eval] using hc.symm

theorem sound2502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2502 node2502Labels = Sparse.eval nodeValue2502 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2502) = mixedMoment B node2502 node2502Labels := rfl
  simpa [nodeValue2502, Sparse.eval] using hc.symm

theorem sound2506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2506 node2506Labels = Sparse.eval nodeValue2506 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2506) = mixedMoment B node2506 node2506Labels := rfl
  simpa [nodeValue2506, Sparse.eval] using hc.symm

theorem sound2513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2513 node2513Labels = Sparse.eval nodeValue2513 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2513) = mixedMoment B node2513 node2513Labels := rfl
  simpa [nodeValue2513, Sparse.eval] using hc.symm

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

theorem sound2571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2571 node2571Labels = Sparse.eval nodeValue2571 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2571) = mixedMoment B node2571 node2571Labels := rfl
  simpa [nodeValue2571, Sparse.eval] using hc.symm

theorem sound2575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2575 node2575Labels = Sparse.eval nodeValue2575 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2575) = mixedMoment B node2575 node2575Labels := rfl
  simpa [nodeValue2575, Sparse.eval] using hc.symm

theorem sound2600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2600 node2600Labels = Sparse.eval nodeValue2600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2600) = mixedMoment B node2600 node2600Labels := rfl
  simpa [nodeValue2600, Sparse.eval] using hc.symm

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

theorem sound2639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2639 node2639Labels = Sparse.eval nodeValue2639 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2639) = mixedMoment B node2639 node2639Labels := rfl
  simpa [nodeValue2639, Sparse.eval] using hc.symm

theorem sound2643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2643 node2643Labels = Sparse.eval nodeValue2643 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2643) = mixedMoment B node2643 node2643Labels := rfl
  simpa [nodeValue2643, Sparse.eval] using hc.symm

theorem sound2681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2681 node2681Labels = Sparse.eval nodeValue2681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2681) = mixedMoment B node2681 node2681Labels := rfl
  simpa [nodeValue2681, Sparse.eval] using hc.symm

theorem sound2683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2683 node2683Labels = Sparse.eval nodeValue2683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2683) = mixedMoment B node2683 node2683Labels := rfl
  simpa [nodeValue2683, Sparse.eval] using hc.symm

theorem sound2687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2687 node2687Labels = Sparse.eval nodeValue2687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2687) = mixedMoment B node2687 node2687Labels := rfl
  simpa [nodeValue2687, Sparse.eval] using hc.symm

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

theorem sound2735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2735 node2735Labels = Sparse.eval nodeValue2735 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2735) = mixedMoment B node2735 node2735Labels := rfl
  simpa [nodeValue2735, Sparse.eval] using hc.symm

theorem sound2737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2737 node2737Labels = Sparse.eval nodeValue2737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2737) = mixedMoment B node2737 node2737Labels := rfl
  simpa [nodeValue2737, Sparse.eval] using hc.symm

theorem sound2744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2744 node2744Labels = Sparse.eval nodeValue2744 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2744) = mixedMoment B node2744 node2744Labels := rfl
  simpa [nodeValue2744, Sparse.eval] using hc.symm

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

theorem sound412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node412 node412Labels = Sparse.eval nodeValue412 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue412 (familyPairVector B) := singlePair412 B _hB
    _ = _ := by
      norm_num [singlePairValue412, nodeValue412, Sparse.eval, mixedVector]
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

theorem sound2759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2759 node2759Labels = Sparse.eval nodeValue2759 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2759) = mixedMoment B node2759 node2759Labels := rfl
  simpa [nodeValue2759, Sparse.eval] using hc.symm

theorem sound2763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2763 node2763Labels = Sparse.eval nodeValue2763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2763) = mixedMoment B node2763 node2763Labels := rfl
  simpa [nodeValue2763, Sparse.eval] using hc.symm

theorem sound2765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2765 node2765Labels = Sparse.eval nodeValue2765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2765) = mixedMoment B node2765 node2765Labels := rfl
  simpa [nodeValue2765, Sparse.eval] using hc.symm

theorem sound2769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2769 node2769Labels = Sparse.eval nodeValue2769 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2769) = mixedMoment B node2769 node2769Labels := rfl
  simpa [nodeValue2769, Sparse.eval] using hc.symm

theorem sound2773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2773 node2773Labels = Sparse.eval nodeValue2773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2773) = mixedMoment B node2773 node2773Labels := rfl
  simpa [nodeValue2773, Sparse.eval] using hc.symm

theorem sound2774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2774 node2774Labels = Sparse.eval nodeValue2774 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2774) = mixedMoment B node2774 node2774Labels := rfl
  simpa [nodeValue2774, Sparse.eval] using hc.symm

theorem sound2776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2776 node2776Labels = Sparse.eval nodeValue2776 (mixedVector B) := by
  have h := singleton2776 B _hB
  rw [sound412 B _hB _hF] at h
  norm_num [nodeValue2776, nodeValue412, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound2952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2952 node2952Labels = Sparse.eval nodeValue2952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2952) = mixedMoment B node2952 node2952Labels := rfl
  simpa [nodeValue2952, Sparse.eval] using hc.symm

theorem sound2983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2983 node2983Labels = Sparse.eval nodeValue2983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2983) = mixedMoment B node2983 node2983Labels := rfl
  simpa [nodeValue2983, Sparse.eval] using hc.symm

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

theorem sound3051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3051 node3051Labels = Sparse.eval nodeValue3051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3051) = mixedMoment B node3051 node3051Labels := rfl
  simpa [nodeValue3051, Sparse.eval] using hc.symm

theorem sound3055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3055 node3055Labels = Sparse.eval nodeValue3055 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3055) = mixedMoment B node3055 node3055Labels := rfl
  simpa [nodeValue3055, Sparse.eval] using hc.symm

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

theorem sound3075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3075 node3075Labels = Sparse.eval nodeValue3075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3075) = mixedMoment B node3075 node3075Labels := rfl
  simpa [nodeValue3075, Sparse.eval] using hc.symm

theorem sound3096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3096 node3096Labels = Sparse.eval nodeValue3096 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3096) = mixedMoment B node3096 node3096Labels := rfl
  simpa [nodeValue3096, Sparse.eval] using hc.symm

theorem sound3098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3098 node3098Labels = Sparse.eval nodeValue3098 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3098) = mixedMoment B node3098 node3098Labels := rfl
  simpa [nodeValue3098, Sparse.eval] using hc.symm

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

theorem sound3572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3572 node3572Labels = Sparse.eval nodeValue3572 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3572) = mixedMoment B node3572 node3572Labels := rfl
  simpa [nodeValue3572, Sparse.eval] using hc.symm

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

theorem sound3583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3583 node3583Labels = Sparse.eval nodeValue3583 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3583) = mixedMoment B node3583 node3583Labels := rfl
  simpa [nodeValue3583, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources13
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq441 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm441 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA441 + difference 0 1) (sourceB441 + difference 1 0) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA441 + difference 0 1) (sourceB441 + difference 1 0) sourceC441) = raw8130 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8130; decide +kernel
    rw [ha]
    exact (canonical8130 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA441 + difference 0 2) (sourceB441 + difference 2 0) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA441 + difference 0 2) (sourceB441 + difference 2 0) sourceC441) = raw8131 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8131; decide +kernel
    rw [ha]
    exact (canonical8131 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA441 + difference 0 3) (sourceB441 + difference 3 0) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA441 + difference 0 3) (sourceB441 + difference 3 0) sourceC441) = raw8132 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8132; decide +kernel
    rw [ha]
    exact (canonical8132 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA441 + difference 0 4) (sourceB441 + difference 4 0) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA441 + difference 0 4) (sourceB441 + difference 4 0) sourceC441) = raw8133 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8133; decide +kernel
    rw [ha]
    exact (canonical8133 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA441 + difference 0 5) (sourceB441 + difference 5 0) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA441 + difference 0 5) (sourceB441 + difference 5 0) sourceC441) = raw8134 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8134; decide +kernel
    rw [ha]
    exact (canonical8134 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA441 + difference 1 0) (sourceB441 + difference 0 1) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2502) := by
    have ha : (tripleCharges (sourceA441 + difference 1 0) (sourceB441 + difference 0 1) sourceC441) = raw8135 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8135; decide +kernel
    rw [ha]
    exact (canonical8135 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA441 + difference 1 2) (sourceB441 + difference 2 1) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2500) := by
    have ha : (tripleCharges (sourceA441 + difference 1 2) (sourceB441 + difference 2 1) sourceC441) = raw8136 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8136; decide +kernel
    rw [ha]
    exact (canonical8136 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA441 + difference 1 3) (sourceB441 + difference 3 1) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2506) := by
    have ha : (tripleCharges (sourceA441 + difference 1 3) (sourceB441 + difference 3 1) sourceC441) = raw8137 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8137; decide +kernel
    rw [ha]
    exact (canonical8137 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA441 + difference 1 4) (sourceB441 + difference 4 1) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA441 + difference 1 4) (sourceB441 + difference 4 1) sourceC441) = raw8138 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8138; decide +kernel
    rw [ha]
    exact (canonical8138 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA441 + difference 1 5) (sourceB441 + difference 5 1) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA441 + difference 1 5) (sourceB441 + difference 5 1) sourceC441) = raw8139 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8139; decide +kernel
    rw [ha]
    exact (canonical8139 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA441 + difference 2 0) (sourceB441 + difference 0 2) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2502) := by
    have ha : (tripleCharges (sourceA441 + difference 2 0) (sourceB441 + difference 0 2) sourceC441) = raw8140 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8140; decide +kernel
    rw [ha]
    exact (canonical8140 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA441 + difference 2 1) (sourceB441 + difference 1 2) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2500) := by
    have ha : (tripleCharges (sourceA441 + difference 2 1) (sourceB441 + difference 1 2) sourceC441) = raw8141 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8141; decide +kernel
    rw [ha]
    exact (canonical8141 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA441 + difference 2 3) (sourceB441 + difference 3 2) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2506) := by
    have ha : (tripleCharges (sourceA441 + difference 2 3) (sourceB441 + difference 3 2) sourceC441) = raw8142 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8142; decide +kernel
    rw [ha]
    exact (canonical8142 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA441 + difference 2 4) (sourceB441 + difference 4 2) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA441 + difference 2 4) (sourceB441 + difference 4 2) sourceC441) = raw8143 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8143; decide +kernel
    rw [ha]
    exact (canonical8143 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA441 + difference 2 5) (sourceB441 + difference 5 2) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA441 + difference 2 5) (sourceB441 + difference 5 2) sourceC441) = raw8144 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8144; decide +kernel
    rw [ha]
    exact (canonical8144 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA441 + difference 3 0) (sourceB441 + difference 0 3) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA441 + difference 3 0) (sourceB441 + difference 0 3) sourceC441) = raw8145 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8145; decide +kernel
    rw [ha]
    exact (canonical8145 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA441 + difference 3 1) (sourceB441 + difference 1 3) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA441 + difference 3 1) (sourceB441 + difference 1 3) sourceC441) = raw8146 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8146; decide +kernel
    rw [ha]
    exact (canonical8146 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA441 + difference 3 2) (sourceB441 + difference 2 3) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA441 + difference 3 2) (sourceB441 + difference 2 3) sourceC441) = raw8147 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8147; decide +kernel
    rw [ha]
    exact (canonical8147 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA441 + difference 3 4) (sourceB441 + difference 4 3) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA441 + difference 3 4) (sourceB441 + difference 4 3) sourceC441) = raw8148 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8148; decide +kernel
    rw [ha]
    exact (canonical8148 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA441 + difference 3 5) (sourceB441 + difference 5 3) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA441 + difference 3 5) (sourceB441 + difference 5 3) sourceC441) = raw8149 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8149; decide +kernel
    rw [ha]
    exact (canonical8149 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA441 + difference 4 0) (sourceB441 + difference 0 4) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA441 + difference 4 0) (sourceB441 + difference 0 4) sourceC441) = raw8150 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8150; decide +kernel
    rw [ha]
    exact (canonical8150 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA441 + difference 4 1) (sourceB441 + difference 1 4) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA441 + difference 4 1) (sourceB441 + difference 1 4) sourceC441) = raw8151 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8151; decide +kernel
    rw [ha]
    exact (canonical8151 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA441 + difference 4 2) (sourceB441 + difference 2 4) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA441 + difference 4 2) (sourceB441 + difference 2 4) sourceC441) = raw8152 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8152; decide +kernel
    rw [ha]
    exact (canonical8152 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA441 + difference 4 3) (sourceB441 + difference 3 4) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA441 + difference 4 3) (sourceB441 + difference 3 4) sourceC441) = raw8153 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8153; decide +kernel
    rw [ha]
    exact (canonical8153 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA441 + difference 4 5) (sourceB441 + difference 5 4) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA441 + difference 4 5) (sourceB441 + difference 5 4) sourceC441) = raw8154 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8154; decide +kernel
    rw [ha]
    exact (canonical8154 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA441 + difference 5 0) (sourceB441 + difference 0 5) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1072) := by
    have ha : (tripleCharges (sourceA441 + difference 5 0) (sourceB441 + difference 0 5) sourceC441) = raw8155 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8155; decide +kernel
    rw [ha]
    exact (canonical8155 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA441 + difference 5 1) (sourceB441 + difference 1 5) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1070) := by
    have ha : (tripleCharges (sourceA441 + difference 5 1) (sourceB441 + difference 1 5) sourceC441) = raw8156 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8156; decide +kernel
    rw [ha]
    exact (canonical8156 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA441 + difference 5 2) (sourceB441 + difference 2 5) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1070) := by
    have ha : (tripleCharges (sourceA441 + difference 5 2) (sourceB441 + difference 2 5) sourceC441) = raw8157 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8157; decide +kernel
    rw [ha]
    exact (canonical8157 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA441 + difference 5 3) (sourceB441 + difference 3 5) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1076) := by
    have ha : (tripleCharges (sourceA441 + difference 5 3) (sourceB441 + difference 3 5) sourceC441) = raw8158 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8158; decide +kernel
    rw [ha]
    exact (canonical8158 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA441 + difference 5 4) (sourceB441 + difference 4 5) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1084) := by
    have ha : (tripleCharges (sourceA441 + difference 5 4) (sourceB441 + difference 4 5) sourceC441) = raw8159 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8159; decide +kernel
    rw [ha]
    exact (canonical8159 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA441 sourceB441 sourceC441
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm441, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq442 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm442 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA442 + difference 0 0) (sourceB442 + difference 0 0) sourceC442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA442 + difference 0 0) (sourceB442 + difference 0 0) sourceC442) = raw8160 := by
      apply Matrix.ext; unfold tripleCharges sourceA442 sourceB442 sourceC442 difference raw8160; decide +kernel
    rw [ha]
    exact (canonical8160 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA442 + difference 0 1) (sourceB442 + difference 1 0) sourceC442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA442 + difference 0 1) (sourceB442 + difference 1 0) sourceC442) = raw8161 := by
      apply Matrix.ext; unfold tripleCharges sourceA442 sourceB442 sourceC442 difference raw8161; decide +kernel
    rw [ha]
    exact (canonical8161 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA442 + difference 0 2) (sourceB442 + difference 2 0) sourceC442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA442 + difference 0 2) (sourceB442 + difference 2 0) sourceC442) = raw8162 := by
      apply Matrix.ext; unfold tripleCharges sourceA442 sourceB442 sourceC442 difference raw8162; decide +kernel
    rw [ha]
    exact (canonical8162 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA442 + difference 0 3) (sourceB442 + difference 3 0) sourceC442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA442 + difference 0 3) (sourceB442 + difference 3 0) sourceC442) = raw8163 := by
      apply Matrix.ext; unfold tripleCharges sourceA442 sourceB442 sourceC442 difference raw8163; decide +kernel
    rw [ha]
    exact (canonical8163 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA442 + difference 0 4) (sourceB442 + difference 4 0) sourceC442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA442 + difference 0 4) (sourceB442 + difference 4 0) sourceC442) = raw8164 := by
      apply Matrix.ext; unfold tripleCharges sourceA442 sourceB442 sourceC442 difference raw8164; decide +kernel
    rw [ha]
    exact (canonical8164 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA442 + difference 0 5) (sourceB442 + difference 5 0) sourceC442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA442 + difference 0 5) (sourceB442 + difference 5 0) sourceC442) = raw8165 := by
      apply Matrix.ext; unfold tripleCharges sourceA442 sourceB442 sourceC442 difference raw8165; decide +kernel
    rw [ha]
    exact (canonical8165 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA442 + sourceB442) sourceC442) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA442 + sourceB442) sourceC442) = raw8166 := by
      apply Matrix.ext; unfold doubleCharges sourceA442 sourceB442 sourceC442 raw8166; decide +kernel
    rw [ha]
    exact (canonical8166 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA442 sourceB442 sourceC442
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm442, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm443 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA443 + difference 0 0) (sourceB443 + difference 0 0) sourceC443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA443 + difference 0 0) (sourceB443 + difference 0 0) sourceC443) = raw8160 := by
      apply Matrix.ext; unfold tripleCharges sourceA443 sourceB443 sourceC443 difference raw8160; decide +kernel
    rw [ha]
    exact (canonical8160 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA443 + difference 1 0) (sourceB443 + difference 0 1) sourceC443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1268) := by
    have ha : (tripleCharges (sourceA443 + difference 1 0) (sourceB443 + difference 0 1) sourceC443) = raw8167 := by
      apply Matrix.ext; unfold tripleCharges sourceA443 sourceB443 sourceC443 difference raw8167; decide +kernel
    rw [ha]
    exact (canonical8167 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA443 + difference 2 0) (sourceB443 + difference 0 2) sourceC443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1268) := by
    have ha : (tripleCharges (sourceA443 + difference 2 0) (sourceB443 + difference 0 2) sourceC443) = raw8168 := by
      apply Matrix.ext; unfold tripleCharges sourceA443 sourceB443 sourceC443 difference raw8168; decide +kernel
    rw [ha]
    exact (canonical8168 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA443 + difference 3 0) (sourceB443 + difference 0 3) sourceC443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA443 + difference 3 0) (sourceB443 + difference 0 3) sourceC443) = raw8169 := by
      apply Matrix.ext; unfold tripleCharges sourceA443 sourceB443 sourceC443 difference raw8169; decide +kernel
    rw [ha]
    exact (canonical8169 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA443 + difference 4 0) (sourceB443 + difference 0 4) sourceC443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA443 + difference 4 0) (sourceB443 + difference 0 4) sourceC443) = raw8170 := by
      apply Matrix.ext; unfold tripleCharges sourceA443 sourceB443 sourceC443 difference raw8170; decide +kernel
    rw [ha]
    exact (canonical8170 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA443 + difference 5 0) (sourceB443 + difference 0 5) sourceC443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1272) := by
    have ha : (tripleCharges (sourceA443 + difference 5 0) (sourceB443 + difference 0 5) sourceC443) = raw8171 := by
      apply Matrix.ext; unfold tripleCharges sourceA443 sourceB443 sourceC443 difference raw8171; decide +kernel
    rw [ha]
    exact (canonical8171 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA443 + sourceB443) sourceC443) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA443 + sourceB443) sourceC443) = raw8166 := by
      apply Matrix.ext; unfold doubleCharges sourceA443 sourceB443 sourceC443 raw8166; decide +kernel
    rw [ha]
    exact (canonical8166 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA443 sourceB443 sourceC443
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm443, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq444 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm444 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA444 + difference 1 0) (sourceB444 + difference 0 1) sourceC444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1268) := by
    have ha : (tripleCharges (sourceA444 + difference 1 0) (sourceB444 + difference 0 1) sourceC444) = raw8167 := by
      apply Matrix.ext; unfold tripleCharges sourceA444 sourceB444 sourceC444 difference raw8167; decide +kernel
    rw [ha]
    exact (canonical8167 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA444 + difference 1 1) (sourceB444 + difference 1 1) sourceC444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA444 + difference 1 1) (sourceB444 + difference 1 1) sourceC444) = raw8160 := by
      apply Matrix.ext; unfold tripleCharges sourceA444 sourceB444 sourceC444 difference raw8160; decide +kernel
    rw [ha]
    exact (canonical8160 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA444 + difference 1 2) (sourceB444 + difference 2 1) sourceC444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2571) := by
    have ha : (tripleCharges (sourceA444 + difference 1 2) (sourceB444 + difference 2 1) sourceC444) = raw8172 := by
      apply Matrix.ext; unfold tripleCharges sourceA444 sourceB444 sourceC444 difference raw8172; decide +kernel
    rw [ha]
    exact (canonical8172 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA444 + difference 1 3) (sourceB444 + difference 3 1) sourceC444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2639) := by
    have ha : (tripleCharges (sourceA444 + difference 1 3) (sourceB444 + difference 3 1) sourceC444) = raw8173 := by
      apply Matrix.ext; unfold tripleCharges sourceA444 sourceB444 sourceC444 difference raw8173; decide +kernel
    rw [ha]
    exact (canonical8173 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA444 + difference 1 4) (sourceB444 + difference 4 1) sourceC444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2759) := by
    have ha : (tripleCharges (sourceA444 + difference 1 4) (sourceB444 + difference 4 1) sourceC444) = raw8174 := by
      apply Matrix.ext; unfold tripleCharges sourceA444 sourceB444 sourceC444 difference raw8174; decide +kernel
    rw [ha]
    exact (canonical8174 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA444 + difference 1 5) (sourceB444 + difference 5 1) sourceC444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA444 + difference 1 5) (sourceB444 + difference 5 1) sourceC444) = raw8175 := by
      apply Matrix.ext; unfold tripleCharges sourceA444 sourceB444 sourceC444 difference raw8175; decide +kernel
    rw [ha]
    exact (canonical8175 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA444 + sourceB444) sourceC444) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA444 + sourceB444) sourceC444) = raw8166 := by
      apply Matrix.ext; unfold doubleCharges sourceA444 sourceB444 sourceC444 raw8166; decide +kernel
    rw [ha]
    exact (canonical8166 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA444 sourceB444 sourceC444
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm444, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq445 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm445 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA445 + difference 0 1) (sourceB445 + difference 1 0) sourceC445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA445 + difference 0 1) (sourceB445 + difference 1 0) sourceC445) = raw8161 := by
      apply Matrix.ext; unfold tripleCharges sourceA445 sourceB445 sourceC445 difference raw8161; decide +kernel
    rw [ha]
    exact (canonical8161 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA445 + difference 1 1) (sourceB445 + difference 1 1) sourceC445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA445 + difference 1 1) (sourceB445 + difference 1 1) sourceC445) = raw8160 := by
      apply Matrix.ext; unfold tripleCharges sourceA445 sourceB445 sourceC445 difference raw8160; decide +kernel
    rw [ha]
    exact (canonical8160 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA445 + difference 2 1) (sourceB445 + difference 1 2) sourceC445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2571) := by
    have ha : (tripleCharges (sourceA445 + difference 2 1) (sourceB445 + difference 1 2) sourceC445) = raw8176 := by
      apply Matrix.ext; unfold tripleCharges sourceA445 sourceB445 sourceC445 difference raw8176; decide +kernel
    rw [ha]
    exact (canonical8176 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA445 + difference 3 1) (sourceB445 + difference 1 3) sourceC445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2600) := by
    have ha : (tripleCharges (sourceA445 + difference 3 1) (sourceB445 + difference 1 3) sourceC445) = raw8177 := by
      apply Matrix.ext; unfold tripleCharges sourceA445 sourceB445 sourceC445 difference raw8177; decide +kernel
    rw [ha]
    exact (canonical8177 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA445 + difference 4 1) (sourceB445 + difference 1 4) sourceC445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2575) := by
    have ha : (tripleCharges (sourceA445 + difference 4 1) (sourceB445 + difference 1 4) sourceC445) = raw8178 := by
      apply Matrix.ext; unfold tripleCharges sourceA445 sourceB445 sourceC445 difference raw8178; decide +kernel
    rw [ha]
    exact (canonical8178 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA445 + difference 5 1) (sourceB445 + difference 1 5) sourceC445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1433) := by
    have ha : (tripleCharges (sourceA445 + difference 5 1) (sourceB445 + difference 1 5) sourceC445) = raw8179 := by
      apply Matrix.ext; unfold tripleCharges sourceA445 sourceB445 sourceC445 difference raw8179; decide +kernel
    rw [ha]
    exact (canonical8179 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA445 + sourceB445) sourceC445) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA445 + sourceB445) sourceC445) = raw8166 := by
      apply Matrix.ext; unfold doubleCharges sourceA445 sourceB445 sourceC445 raw8166; decide +kernel
    rw [ha]
    exact (canonical8166 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA445 sourceB445 sourceC445
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm445, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq446 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm446 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA446 + difference 0 3) (sourceB446 + difference 3 0) sourceC446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA446 + difference 0 3) (sourceB446 + difference 3 0) sourceC446) = raw8163 := by
      apply Matrix.ext; unfold tripleCharges sourceA446 sourceB446 sourceC446 difference raw8163; decide +kernel
    rw [ha]
    exact (canonical8163 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA446 + difference 1 3) (sourceB446 + difference 3 1) sourceC446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2639) := by
    have ha : (tripleCharges (sourceA446 + difference 1 3) (sourceB446 + difference 3 1) sourceC446) = raw8173 := by
      apply Matrix.ext; unfold tripleCharges sourceA446 sourceB446 sourceC446 difference raw8173; decide +kernel
    rw [ha]
    exact (canonical8173 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA446 + difference 2 3) (sourceB446 + difference 3 2) sourceC446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2639) := by
    have ha : (tripleCharges (sourceA446 + difference 2 3) (sourceB446 + difference 3 2) sourceC446) = raw8180 := by
      apply Matrix.ext; unfold tripleCharges sourceA446 sourceB446 sourceC446 difference raw8180; decide +kernel
    rw [ha]
    exact (canonical8180 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA446 + difference 3 3) (sourceB446 + difference 3 3) sourceC446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA446 + difference 3 3) (sourceB446 + difference 3 3) sourceC446) = raw8160 := by
      apply Matrix.ext; unfold tripleCharges sourceA446 sourceB446 sourceC446 difference raw8160; decide +kernel
    rw [ha]
    exact (canonical8160 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA446 + difference 4 3) (sourceB446 + difference 3 4) sourceC446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2643) := by
    have ha : (tripleCharges (sourceA446 + difference 4 3) (sourceB446 + difference 3 4) sourceC446) = raw8181 := by
      apply Matrix.ext; unfold tripleCharges sourceA446 sourceB446 sourceC446 difference raw8181; decide +kernel
    rw [ha]
    exact (canonical8181 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA446 + difference 5 3) (sourceB446 + difference 3 5) sourceC446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1437) := by
    have ha : (tripleCharges (sourceA446 + difference 5 3) (sourceB446 + difference 3 5) sourceC446) = raw8182 := by
      apply Matrix.ext; unfold tripleCharges sourceA446 sourceB446 sourceC446 difference raw8182; decide +kernel
    rw [ha]
    exact (canonical8182 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA446 + sourceB446) sourceC446) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA446 + sourceB446) sourceC446) = raw8166 := by
      apply Matrix.ext; unfold doubleCharges sourceA446 sourceB446 sourceC446 raw8166; decide +kernel
    rw [ha]
    exact (canonical8166 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA446 sourceB446 sourceC446
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm446, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm447 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA447 + difference 4 0) (sourceB447 + difference 0 4) sourceC447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA447 + difference 4 0) (sourceB447 + difference 0 4) sourceC447) = raw8170 := by
      apply Matrix.ext; unfold tripleCharges sourceA447 sourceB447 sourceC447 difference raw8170; decide +kernel
    rw [ha]
    exact (canonical8170 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA447 + difference 4 1) (sourceB447 + difference 1 4) sourceC447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2575) := by
    have ha : (tripleCharges (sourceA447 + difference 4 1) (sourceB447 + difference 1 4) sourceC447) = raw8178 := by
      apply Matrix.ext; unfold tripleCharges sourceA447 sourceB447 sourceC447 difference raw8178; decide +kernel
    rw [ha]
    exact (canonical8178 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA447 + difference 4 2) (sourceB447 + difference 2 4) sourceC447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2575) := by
    have ha : (tripleCharges (sourceA447 + difference 4 2) (sourceB447 + difference 2 4) sourceC447) = raw8183 := by
      apply Matrix.ext; unfold tripleCharges sourceA447 sourceB447 sourceC447 difference raw8183; decide +kernel
    rw [ha]
    exact (canonical8183 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA447 + difference 4 3) (sourceB447 + difference 3 4) sourceC447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2643) := by
    have ha : (tripleCharges (sourceA447 + difference 4 3) (sourceB447 + difference 3 4) sourceC447) = raw8181 := by
      apply Matrix.ext; unfold tripleCharges sourceA447 sourceB447 sourceC447 difference raw8181; decide +kernel
    rw [ha]
    exact (canonical8181 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA447 + difference 4 4) (sourceB447 + difference 4 4) sourceC447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA447 + difference 4 4) (sourceB447 + difference 4 4) sourceC447) = raw8160 := by
      apply Matrix.ext; unfold tripleCharges sourceA447 sourceB447 sourceC447 difference raw8160; decide +kernel
    rw [ha]
    exact (canonical8160 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA447 + difference 4 5) (sourceB447 + difference 5 4) sourceC447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA447 + difference 4 5) (sourceB447 + difference 5 4) sourceC447) = raw8184 := by
      apply Matrix.ext; unfold tripleCharges sourceA447 sourceB447 sourceC447 difference raw8184; decide +kernel
    rw [ha]
    exact (canonical8184 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA447 + sourceB447) sourceC447) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA447 + sourceB447) sourceC447) = raw8166 := by
      apply Matrix.ext; unfold doubleCharges sourceA447 sourceB447 sourceC447 raw8166; decide +kernel
    rw [ha]
    exact (canonical8166 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA447 sourceB447 sourceC447
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm447, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources14
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm448 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA448 + difference 5 0) (sourceB448 + difference 0 5) sourceC448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1272) := by
    have ha : (tripleCharges (sourceA448 + difference 5 0) (sourceB448 + difference 0 5) sourceC448) = raw8171 := by
      apply Matrix.ext; unfold tripleCharges sourceA448 sourceB448 sourceC448 difference raw8171; decide +kernel
    rw [ha]
    exact (canonical8171 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA448 + difference 5 1) (sourceB448 + difference 1 5) sourceC448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1433) := by
    have ha : (tripleCharges (sourceA448 + difference 5 1) (sourceB448 + difference 1 5) sourceC448) = raw8179 := by
      apply Matrix.ext; unfold tripleCharges sourceA448 sourceB448 sourceC448 difference raw8179; decide +kernel
    rw [ha]
    exact (canonical8179 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA448 + difference 5 2) (sourceB448 + difference 2 5) sourceC448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1433) := by
    have ha : (tripleCharges (sourceA448 + difference 5 2) (sourceB448 + difference 2 5) sourceC448) = raw8185 := by
      apply Matrix.ext; unfold tripleCharges sourceA448 sourceB448 sourceC448 difference raw8185; decide +kernel
    rw [ha]
    exact (canonical8185 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA448 + difference 5 3) (sourceB448 + difference 3 5) sourceC448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1437) := by
    have ha : (tripleCharges (sourceA448 + difference 5 3) (sourceB448 + difference 3 5) sourceC448) = raw8182 := by
      apply Matrix.ext; unfold tripleCharges sourceA448 sourceB448 sourceC448 difference raw8182; decide +kernel
    rw [ha]
    exact (canonical8182 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA448 + difference 5 4) (sourceB448 + difference 4 5) sourceC448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA448 + difference 5 4) (sourceB448 + difference 4 5) sourceC448) = raw8186 := by
      apply Matrix.ext; unfold tripleCharges sourceA448 sourceB448 sourceC448 difference raw8186; decide +kernel
    rw [ha]
    exact (canonical8186 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA448 + difference 5 5) (sourceB448 + difference 5 5) sourceC448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA448 + difference 5 5) (sourceB448 + difference 5 5) sourceC448) = raw8160 := by
      apply Matrix.ext; unfold tripleCharges sourceA448 sourceB448 sourceC448 difference raw8160; decide +kernel
    rw [ha]
    exact (canonical8160 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA448 + sourceB448) sourceC448) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA448 + sourceB448) sourceC448) = raw8166 := by
      apply Matrix.ext; unfold doubleCharges sourceA448 sourceB448 sourceC448 raw8166; decide +kernel
    rw [ha]
    exact (canonical8166 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA448 sourceB448 sourceC448
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm448, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm452 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA452 + difference 0 0) (sourceB452 + difference 0 0) sourceC452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA452 + difference 0 0) (sourceB452 + difference 0 0) sourceC452) = raw8253 := by
      apply Matrix.ext; unfold tripleCharges sourceA452 sourceB452 sourceC452 difference raw8253; decide +kernel
    rw [ha]
    exact (canonical8253 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA452 + difference 0 1) (sourceB452 + difference 1 0) sourceC452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA452 + difference 0 1) (sourceB452 + difference 1 0) sourceC452) = raw8254 := by
      apply Matrix.ext; unfold tripleCharges sourceA452 sourceB452 sourceC452 difference raw8254; decide +kernel
    rw [ha]
    exact (canonical8254 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA452 + difference 0 2) (sourceB452 + difference 2 0) sourceC452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA452 + difference 0 2) (sourceB452 + difference 2 0) sourceC452) = raw8255 := by
      apply Matrix.ext; unfold tripleCharges sourceA452 sourceB452 sourceC452 difference raw8255; decide +kernel
    rw [ha]
    exact (canonical8255 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA452 + difference 0 3) (sourceB452 + difference 3 0) sourceC452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA452 + difference 0 3) (sourceB452 + difference 3 0) sourceC452) = raw8256 := by
      apply Matrix.ext; unfold tripleCharges sourceA452 sourceB452 sourceC452 difference raw8256; decide +kernel
    rw [ha]
    exact (canonical8256 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA452 + difference 0 4) (sourceB452 + difference 4 0) sourceC452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3623) := by
    have ha : (tripleCharges (sourceA452 + difference 0 4) (sourceB452 + difference 4 0) sourceC452) = raw4743 := by
      apply Matrix.ext; unfold tripleCharges sourceA452 sourceB452 sourceC452 difference raw4743; decide +kernel
    rw [ha]
    exact (canonical4743 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA452 + difference 0 5) (sourceB452 + difference 5 0) sourceC452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA452 + difference 0 5) (sourceB452 + difference 5 0) sourceC452) = raw8257 := by
      apply Matrix.ext; unfold tripleCharges sourceA452 sourceB452 sourceC452 difference raw8257; decide +kernel
    rw [ha]
    exact (canonical8257 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA452 + sourceB452) sourceC452) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA452 + sourceB452) sourceC452) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA452 sourceB452 sourceC452 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA452 sourceB452 sourceC452
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm452, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm453 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA453 + difference 0 0) (sourceB453 + difference 0 0) sourceC453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA453 + difference 0 0) (sourceB453 + difference 0 0) sourceC453) = raw8253 := by
      apply Matrix.ext; unfold tripleCharges sourceA453 sourceB453 sourceC453 difference raw8253; decide +kernel
    rw [ha]
    exact (canonical8253 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA453 + difference 1 0) (sourceB453 + difference 0 1) sourceC453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1404) := by
    have ha : (tripleCharges (sourceA453 + difference 1 0) (sourceB453 + difference 0 1) sourceC453) = raw8258 := by
      apply Matrix.ext; unfold tripleCharges sourceA453 sourceB453 sourceC453 difference raw8258; decide +kernel
    rw [ha]
    exact (canonical8258 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA453 + difference 2 0) (sourceB453 + difference 0 2) sourceC453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1404) := by
    have ha : (tripleCharges (sourceA453 + difference 2 0) (sourceB453 + difference 0 2) sourceC453) = raw8259 := by
      apply Matrix.ext; unfold tripleCharges sourceA453 sourceB453 sourceC453 difference raw8259; decide +kernel
    rw [ha]
    exact (canonical8259 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA453 + difference 3 0) (sourceB453 + difference 0 3) sourceC453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1440) := by
    have ha : (tripleCharges (sourceA453 + difference 3 0) (sourceB453 + difference 0 3) sourceC453) = raw8260 := by
      apply Matrix.ext; unfold tripleCharges sourceA453 sourceB453 sourceC453 difference raw8260; decide +kernel
    rw [ha]
    exact (canonical8260 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA453 + difference 4 0) (sourceB453 + difference 0 4) sourceC453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1418) := by
    have ha : (tripleCharges (sourceA453 + difference 4 0) (sourceB453 + difference 0 4) sourceC453) = raw8261 := by
      apply Matrix.ext; unfold tripleCharges sourceA453 sourceB453 sourceC453 difference raw8261; decide +kernel
    rw [ha]
    exact (canonical8261 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA453 + difference 5 0) (sourceB453 + difference 0 5) sourceC453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA453 + difference 5 0) (sourceB453 + difference 0 5) sourceC453) = raw4748 := by
      apply Matrix.ext; unfold tripleCharges sourceA453 sourceB453 sourceC453 difference raw4748; decide +kernel
    rw [ha]
    exact (canonical4748 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA453 + sourceB453) sourceC453) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA453 + sourceB453) sourceC453) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA453 sourceB453 sourceC453 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA453 sourceB453 sourceC453
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm453, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm454 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA454 + difference 1 0) (sourceB454 + difference 0 1) sourceC454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1404) := by
    have ha : (tripleCharges (sourceA454 + difference 1 0) (sourceB454 + difference 0 1) sourceC454) = raw8258 := by
      apply Matrix.ext; unfold tripleCharges sourceA454 sourceB454 sourceC454 difference raw8258; decide +kernel
    rw [ha]
    exact (canonical8258 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA454 + difference 1 1) (sourceB454 + difference 1 1) sourceC454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA454 + difference 1 1) (sourceB454 + difference 1 1) sourceC454) = raw8253 := by
      apply Matrix.ext; unfold tripleCharges sourceA454 sourceB454 sourceC454 difference raw8253; decide +kernel
    rw [ha]
    exact (canonical8253 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA454 + difference 1 2) (sourceB454 + difference 2 1) sourceC454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2983) := by
    have ha : (tripleCharges (sourceA454 + difference 1 2) (sourceB454 + difference 2 1) sourceC454) = raw8262 := by
      apply Matrix.ext; unfold tripleCharges sourceA454 sourceB454 sourceC454 difference raw8262; decide +kernel
    rw [ha]
    exact (canonical8262 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA454 + difference 1 3) (sourceB454 + difference 3 1) sourceC454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA454 + difference 1 3) (sourceB454 + difference 3 1) sourceC454) = raw8263 := by
      apply Matrix.ext; unfold tripleCharges sourceA454 sourceB454 sourceC454 difference raw8263; decide +kernel
    rw [ha]
    exact (canonical8263 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA454 + difference 1 4) (sourceB454 + difference 4 1) sourceC454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA454 + difference 1 4) (sourceB454 + difference 4 1) sourceC454) = raw4753 := by
      apply Matrix.ext; unfold tripleCharges sourceA454 sourceB454 sourceC454 difference raw4753; decide +kernel
    rw [ha]
    exact (canonical4753 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA454 + difference 1 5) (sourceB454 + difference 5 1) sourceC454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3096) := by
    have ha : (tripleCharges (sourceA454 + difference 1 5) (sourceB454 + difference 5 1) sourceC454) = raw8264 := by
      apply Matrix.ext; unfold tripleCharges sourceA454 sourceB454 sourceC454 difference raw8264; decide +kernel
    rw [ha]
    exact (canonical8264 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA454 + sourceB454) sourceC454) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA454 + sourceB454) sourceC454) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA454 sourceB454 sourceC454 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA454 sourceB454 sourceC454
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm454, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck372 : Integer.Sparse.reindex keyMap MixedData.row372 = numericRow372 := by decide +kernel

theorem numericCheck372 (x : Master → ℝ) : Integer.Sparse.eval numericRow372 x =
    (2160 : ℝ) * reducedSource372 x := by
  norm_num [numericRow372, reducedSource372, Integer.Sparse.eval, Sparse.eval, nodeValue1070, nodeValue1072, nodeValue1076, nodeValue1084, nodeValue2500, nodeValue2502, nodeValue2506, nodeValue2513, nodeValue2681, nodeValue2683, nodeValue2687, nodeValue2735, nodeValue2737, nodeValue2744, nodeValue2773, nodeValue2774, nodeValue2776, nodeValue3572, nodeValue3582, nodeValue3583, nodeValue3888] <;> ring

theorem reindexCheck373 : Integer.Sparse.reindex keyMap MixedData.row373 = numericRow373 := by decide +kernel

theorem numericCheck373 (x : Master → ℝ) : Integer.Sparse.eval numericRow373 x =
    (1 : ℝ) * reducedSource373 x := by
  norm_num [numericRow373, reducedSource373, Integer.Sparse.eval, Sparse.eval, nodeValue2769, nodeValue3051, nodeValue3054, nodeValue3055, nodeValue3913, nodeValue4092]

theorem reindexCheck374 : Integer.Sparse.reindex keyMap MixedData.row374 = numericRow374 := by decide +kernel

theorem numericCheck374 (x : Master → ℝ) : Integer.Sparse.eval numericRow374 x =
    (1 : ℝ) * reducedSource374 x := by
  norm_num [numericRow374, reducedSource374, Integer.Sparse.eval, Sparse.eval, nodeValue1268, nodeValue1272, nodeValue1273, nodeValue1306, nodeValue2769, nodeValue4092]

theorem reindexCheck375 : Integer.Sparse.reindex keyMap MixedData.row375 = numericRow375 := by decide +kernel

theorem numericCheck375 (x : Master → ℝ) : Integer.Sparse.eval numericRow375 x =
    (1 : ℝ) * reducedSource375 x := by
  norm_num [numericRow375, reducedSource375, Integer.Sparse.eval, Sparse.eval, nodeValue1268, nodeValue2571, nodeValue2639, nodeValue2759, nodeValue2763, nodeValue2769, nodeValue4092]

theorem reindexCheck376 : Integer.Sparse.reindex keyMap MixedData.row376 = numericRow376 := by decide +kernel

theorem numericCheck376 (x : Master → ℝ) : Integer.Sparse.eval numericRow376 x =
    (1 : ℝ) * reducedSource376 x := by
  norm_num [numericRow376, reducedSource376, Integer.Sparse.eval, Sparse.eval, nodeValue1433, nodeValue2571, nodeValue2575, nodeValue2600, nodeValue2769, nodeValue3051, nodeValue4092]

theorem reindexCheck377 : Integer.Sparse.reindex keyMap MixedData.row377 = numericRow377 := by decide +kernel

theorem numericCheck377 (x : Master → ℝ) : Integer.Sparse.eval numericRow377 x =
    (1 : ℝ) * reducedSource377 x := by
  norm_num [numericRow377, reducedSource377, Integer.Sparse.eval, Sparse.eval, nodeValue1437, nodeValue2639, nodeValue2643, nodeValue2769, nodeValue3055, nodeValue4092]

theorem reindexCheck378 : Integer.Sparse.reindex keyMap MixedData.row378 = numericRow378 := by decide +kernel

theorem numericCheck378 (x : Master → ℝ) : Integer.Sparse.eval numericRow378 x =
    (1 : ℝ) * reducedSource378 x := by
  norm_num [numericRow378, reducedSource378, Integer.Sparse.eval, Sparse.eval, nodeValue1273, nodeValue2575, nodeValue2643, nodeValue2765, nodeValue2769, nodeValue4092]

theorem reindexCheck379 : Integer.Sparse.reindex keyMap MixedData.row379 = numericRow379 := by decide +kernel

theorem numericCheck379 (x : Master → ℝ) : Integer.Sparse.eval numericRow379 x =
    (1 : ℝ) * reducedSource379 x := by
  norm_num [numericRow379, reducedSource379, Integer.Sparse.eval, Sparse.eval, nodeValue1272, nodeValue1433, nodeValue1436, nodeValue1437, nodeValue2769, nodeValue4092]

theorem reindexCheck381 : Integer.Sparse.reindex keyMap MixedData.row381 = numericRow381 := by decide +kernel

theorem numericCheck381 (x : Master → ℝ) : Integer.Sparse.eval numericRow381 x =
    (1 : ℝ) * reducedSource381 x := by
  norm_num [numericRow381, reducedSource381, Integer.Sparse.eval, Sparse.eval, nodeValue3098, nodeValue3572, nodeValue3583, nodeValue3623, nodeValue4083]

theorem reindexCheck382 : Integer.Sparse.reindex keyMap MixedData.row382 = numericRow382 := by decide +kernel

theorem numericCheck382 (x : Master → ℝ) : Integer.Sparse.eval numericRow382 x =
    (1 : ℝ) * reducedSource382 x := by
  norm_num [numericRow382, reducedSource382, Integer.Sparse.eval, Sparse.eval, nodeValue1404, nodeValue1408, nodeValue1418, nodeValue1440, nodeValue3098, nodeValue4083]

theorem reindexCheck383 : Integer.Sparse.reindex keyMap MixedData.row383 = numericRow383 := by decide +kernel

theorem numericCheck383 (x : Master → ℝ) : Integer.Sparse.eval numericRow383 x =
    (1 : ℝ) * reducedSource383 x := by
  norm_num [numericRow383, reducedSource383, Integer.Sparse.eval, Sparse.eval, nodeValue1404, nodeValue2952, nodeValue2983, nodeValue3075, nodeValue3096, nodeValue3098, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero372 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource372 (mixedVector B) = 0 := by
  have h1070 : mixedVector B (Sum.inr 1070) = Sparse.eval nodeValue1070 (mixedVector B) := by
    change mixedMoment B node1070 node1070Labels = _
    exact sound1070 B hB hF
  have h1072 : mixedVector B (Sum.inr 1072) = Sparse.eval nodeValue1072 (mixedVector B) := by
    change mixedMoment B node1072 node1072Labels = _
    exact sound1072 B hB hF
  have h1076 : mixedVector B (Sum.inr 1076) = Sparse.eval nodeValue1076 (mixedVector B) := by
    change mixedMoment B node1076 node1076Labels = _
    exact sound1076 B hB hF
  have h1084 : mixedVector B (Sum.inr 1084) = Sparse.eval nodeValue1084 (mixedVector B) := by
    change mixedMoment B node1084 node1084Labels = _
    exact sound1084 B hB hF
  have h2500 : mixedVector B (Sum.inr 2500) = Sparse.eval nodeValue2500 (mixedVector B) := by
    change mixedMoment B node2500 node2500Labels = _
    exact sound2500 B hB hF
  have h2502 : mixedVector B (Sum.inr 2502) = Sparse.eval nodeValue2502 (mixedVector B) := by
    change mixedMoment B node2502 node2502Labels = _
    exact sound2502 B hB hF
  have h2506 : mixedVector B (Sum.inr 2506) = Sparse.eval nodeValue2506 (mixedVector B) := by
    change mixedMoment B node2506 node2506Labels = _
    exact sound2506 B hB hF
  have h2513 : mixedVector B (Sum.inr 2513) = Sparse.eval nodeValue2513 (mixedVector B) := by
    change mixedMoment B node2513 node2513Labels = _
    exact sound2513 B hB hF
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h2687 : mixedVector B (Sum.inr 2687) = Sparse.eval nodeValue2687 (mixedVector B) := by
    change mixedMoment B node2687 node2687Labels = _
    exact sound2687 B hB hF
  have h2735 : mixedVector B (Sum.inr 2735) = Sparse.eval nodeValue2735 (mixedVector B) := by
    change mixedMoment B node2735 node2735Labels = _
    exact sound2735 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h2776 : mixedVector B (Sum.inr 2776) = Sparse.eval nodeValue2776 (mixedVector B) := by
    change mixedMoment B node2776 node2776Labels = _
    exact sound2776 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h3888 : mixedVector B (Sum.inr 3888) = Sparse.eval nodeValue3888 (mixedVector B) := by
    change mixedMoment B node3888 node3888Labels = _
    exact sound3888 B hB hF
  simpa only [sourceForm441, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1070, h1072, h1076, h1084, h2500, h2502, h2506, h2513, h2681, h2683, h2687, h2735, h2737, h2744, h2773, h2774, h2776, h3572, h3582, h3583, h3888, reducedSource372] using sourceEq441 B hB

theorem rowSound372 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row372 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck372, numericCheck372, reducedZero372 B hB hF, mul_zero]

theorem reducedZero373 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource373 (mixedVector B) = 0 := by
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3913 : mixedVector B (Sum.inr 3913) = Sparse.eval nodeValue3913 (mixedVector B) := by
    change mixedMoment B node3913 node3913Labels = _
    exact sound3913 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm442, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2769, h3051, h3054, h3055, h3913, h4092, reducedSource373] using sourceEq442 B hB

theorem rowSound373 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row373 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck373, numericCheck373, reducedZero373 B hB hF, mul_zero]

theorem reducedZero374 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource374 (mixedVector B) = 0 := by
  have h1268 : mixedVector B (Sum.inr 1268) = Sparse.eval nodeValue1268 (mixedVector B) := by
    change mixedMoment B node1268 node1268Labels = _
    exact sound1268 B hB hF
  have h1272 : mixedVector B (Sum.inr 1272) = Sparse.eval nodeValue1272 (mixedVector B) := by
    change mixedMoment B node1272 node1272Labels = _
    exact sound1272 B hB hF
  have h1273 : mixedVector B (Sum.inr 1273) = Sparse.eval nodeValue1273 (mixedVector B) := by
    change mixedMoment B node1273 node1273Labels = _
    exact sound1273 B hB hF
  have h1306 : mixedVector B (Sum.inr 1306) = Sparse.eval nodeValue1306 (mixedVector B) := by
    change mixedMoment B node1306 node1306Labels = _
    exact sound1306 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm443, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1268, h1272, h1273, h1306, h2769, h4092, reducedSource374] using sourceEq443 B hB

theorem rowSound374 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row374 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck374, numericCheck374, reducedZero374 B hB hF, mul_zero]

theorem reducedZero375 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource375 (mixedVector B) = 0 := by
  have h1268 : mixedVector B (Sum.inr 1268) = Sparse.eval nodeValue1268 (mixedVector B) := by
    change mixedMoment B node1268 node1268Labels = _
    exact sound1268 B hB hF
  have h2571 : mixedVector B (Sum.inr 2571) = Sparse.eval nodeValue2571 (mixedVector B) := by
    change mixedMoment B node2571 node2571Labels = _
    exact sound2571 B hB hF
  have h2639 : mixedVector B (Sum.inr 2639) = Sparse.eval nodeValue2639 (mixedVector B) := by
    change mixedMoment B node2639 node2639Labels = _
    exact sound2639 B hB hF
  have h2759 : mixedVector B (Sum.inr 2759) = Sparse.eval nodeValue2759 (mixedVector B) := by
    change mixedMoment B node2759 node2759Labels = _
    exact sound2759 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm444, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1268, h2571, h2639, h2759, h2763, h2769, h4092, reducedSource375] using sourceEq444 B hB

theorem rowSound375 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row375 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck375, numericCheck375, reducedZero375 B hB hF, mul_zero]

theorem reducedZero376 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource376 (mixedVector B) = 0 := by
  have h1433 : mixedVector B (Sum.inr 1433) = Sparse.eval nodeValue1433 (mixedVector B) := by
    change mixedMoment B node1433 node1433Labels = _
    exact sound1433 B hB hF
  have h2571 : mixedVector B (Sum.inr 2571) = Sparse.eval nodeValue2571 (mixedVector B) := by
    change mixedMoment B node2571 node2571Labels = _
    exact sound2571 B hB hF
  have h2575 : mixedVector B (Sum.inr 2575) = Sparse.eval nodeValue2575 (mixedVector B) := by
    change mixedMoment B node2575 node2575Labels = _
    exact sound2575 B hB hF
  have h2600 : mixedVector B (Sum.inr 2600) = Sparse.eval nodeValue2600 (mixedVector B) := by
    change mixedMoment B node2600 node2600Labels = _
    exact sound2600 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm445, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1433, h2571, h2575, h2600, h2769, h3051, h4092, reducedSource376] using sourceEq445 B hB

theorem rowSound376 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row376 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck376, numericCheck376, reducedZero376 B hB hF, mul_zero]

theorem reducedZero377 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource377 (mixedVector B) = 0 := by
  have h1437 : mixedVector B (Sum.inr 1437) = Sparse.eval nodeValue1437 (mixedVector B) := by
    change mixedMoment B node1437 node1437Labels = _
    exact sound1437 B hB hF
  have h2639 : mixedVector B (Sum.inr 2639) = Sparse.eval nodeValue2639 (mixedVector B) := by
    change mixedMoment B node2639 node2639Labels = _
    exact sound2639 B hB hF
  have h2643 : mixedVector B (Sum.inr 2643) = Sparse.eval nodeValue2643 (mixedVector B) := by
    change mixedMoment B node2643 node2643Labels = _
    exact sound2643 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm446, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1437, h2639, h2643, h2769, h3055, h4092, reducedSource377] using sourceEq446 B hB

theorem rowSound377 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row377 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck377, numericCheck377, reducedZero377 B hB hF, mul_zero]

theorem reducedZero378 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource378 (mixedVector B) = 0 := by
  have h1273 : mixedVector B (Sum.inr 1273) = Sparse.eval nodeValue1273 (mixedVector B) := by
    change mixedMoment B node1273 node1273Labels = _
    exact sound1273 B hB hF
  have h2575 : mixedVector B (Sum.inr 2575) = Sparse.eval nodeValue2575 (mixedVector B) := by
    change mixedMoment B node2575 node2575Labels = _
    exact sound2575 B hB hF
  have h2643 : mixedVector B (Sum.inr 2643) = Sparse.eval nodeValue2643 (mixedVector B) := by
    change mixedMoment B node2643 node2643Labels = _
    exact sound2643 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm447, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1273, h2575, h2643, h2765, h2769, h4092, reducedSource378] using sourceEq447 B hB

theorem rowSound378 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row378 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck378, numericCheck378, reducedZero378 B hB hF, mul_zero]

theorem reducedZero379 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource379 (mixedVector B) = 0 := by
  have h1272 : mixedVector B (Sum.inr 1272) = Sparse.eval nodeValue1272 (mixedVector B) := by
    change mixedMoment B node1272 node1272Labels = _
    exact sound1272 B hB hF
  have h1433 : mixedVector B (Sum.inr 1433) = Sparse.eval nodeValue1433 (mixedVector B) := by
    change mixedMoment B node1433 node1433Labels = _
    exact sound1433 B hB hF
  have h1436 : mixedVector B (Sum.inr 1436) = Sparse.eval nodeValue1436 (mixedVector B) := by
    change mixedMoment B node1436 node1436Labels = _
    exact sound1436 B hB hF
  have h1437 : mixedVector B (Sum.inr 1437) = Sparse.eval nodeValue1437 (mixedVector B) := by
    change mixedMoment B node1437 node1437Labels = _
    exact sound1437 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm448, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1272, h1433, h1436, h1437, h2769, h4092, reducedSource379] using sourceEq448 B hB

theorem rowSound379 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row379 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck379, numericCheck379, reducedZero379 B hB hF, mul_zero]

theorem reducedZero381 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource381 (mixedVector B) = 0 := by
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h3623 : mixedVector B (Sum.inr 3623) = Sparse.eval nodeValue3623 (mixedVector B) := by
    change mixedMoment B node3623 node3623Labels = _
    exact sound3623 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm452, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3098, h3572, h3583, h3623, h4083, reducedSource381] using sourceEq452 B hB

theorem rowSound381 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row381 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck381, numericCheck381, reducedZero381 B hB hF, mul_zero]

theorem reducedZero382 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource382 (mixedVector B) = 0 := by
  have h1404 : mixedVector B (Sum.inr 1404) = Sparse.eval nodeValue1404 (mixedVector B) := by
    change mixedMoment B node1404 node1404Labels = _
    exact sound1404 B hB hF
  have h1408 : mixedVector B (Sum.inr 1408) = Sparse.eval nodeValue1408 (mixedVector B) := by
    change mixedMoment B node1408 node1408Labels = _
    exact sound1408 B hB hF
  have h1418 : mixedVector B (Sum.inr 1418) = Sparse.eval nodeValue1418 (mixedVector B) := by
    change mixedMoment B node1418 node1418Labels = _
    exact sound1418 B hB hF
  have h1440 : mixedVector B (Sum.inr 1440) = Sparse.eval nodeValue1440 (mixedVector B) := by
    change mixedMoment B node1440 node1440Labels = _
    exact sound1440 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm453, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1404, h1408, h1418, h1440, h3098, h4083, reducedSource382] using sourceEq453 B hB

theorem rowSound382 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row382 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck382, numericCheck382, reducedZero382 B hB hF, mul_zero]

theorem reducedZero383 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource383 (mixedVector B) = 0 := by
  have h1404 : mixedVector B (Sum.inr 1404) = Sparse.eval nodeValue1404 (mixedVector B) := by
    change mixedMoment B node1404 node1404Labels = _
    exact sound1404 B hB hF
  have h2952 : mixedVector B (Sum.inr 2952) = Sparse.eval nodeValue2952 (mixedVector B) := by
    change mixedMoment B node2952 node2952Labels = _
    exact sound2952 B hB hF
  have h2983 : mixedVector B (Sum.inr 2983) = Sparse.eval nodeValue2983 (mixedVector B) := by
    change mixedMoment B node2983 node2983Labels = _
    exact sound2983 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3096 : mixedVector B (Sum.inr 3096) = Sparse.eval nodeValue3096 (mixedVector B) := by
    change mixedMoment B node3096 node3096Labels = _
    exact sound3096 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm454, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1404, h2952, h2983, h3075, h3096, h3098, h4083, reducedSource383] using sourceEq454 B hB

theorem rowSound383 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row383 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck383, numericCheck383, reducedZero383 B hB hF, mul_zero]

theorem sourceRowsAt368 : MixedData.sourceRows (368 : Fin 2425) =
    MixedData.row368 := by decide +kernel

theorem sourceRowsAt369 : MixedData.sourceRows (369 : Fin 2425) =
    MixedData.row369 := by decide +kernel

theorem sourceRowsAt370 : MixedData.sourceRows (370 : Fin 2425) =
    MixedData.row370 := by decide +kernel

theorem sourceRowsAt371 : MixedData.sourceRows (371 : Fin 2425) =
    MixedData.row371 := by decide +kernel

theorem sourceRowsAt372 : MixedData.sourceRows (372 : Fin 2425) =
    MixedData.row372 := by decide +kernel

theorem sourceRowsAt373 : MixedData.sourceRows (373 : Fin 2425) =
    MixedData.row373 := by decide +kernel

theorem sourceRowsAt374 : MixedData.sourceRows (374 : Fin 2425) =
    MixedData.row374 := by decide +kernel

theorem sourceRowsAt375 : MixedData.sourceRows (375 : Fin 2425) =
    MixedData.row375 := by decide +kernel

theorem sourceRowsAt376 : MixedData.sourceRows (376 : Fin 2425) =
    MixedData.row376 := by decide +kernel

theorem sourceRowsAt377 : MixedData.sourceRows (377 : Fin 2425) =
    MixedData.row377 := by decide +kernel

theorem sourceRowsAt378 : MixedData.sourceRows (378 : Fin 2425) =
    MixedData.row378 := by decide +kernel

theorem sourceRowsAt379 : MixedData.sourceRows (379 : Fin 2425) =
    MixedData.row379 := by decide +kernel

theorem sourceRowsAt380 : MixedData.sourceRows (380 : Fin 2425) =
    MixedData.row380 := by decide +kernel

theorem sourceRowsAt381 : MixedData.sourceRows (381 : Fin 2425) =
    MixedData.row381 := by decide +kernel

theorem sourceRowsAt382 : MixedData.sourceRows (382 : Fin 2425) =
    MixedData.row382 := by decide +kernel

theorem sourceRowsAt383 : MixedData.sourceRows (383 : Fin 2425) =
    MixedData.row383 := by decide +kernel

theorem chunkSound23_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 23) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 368 ∨ k.val = 369 ∨ k.val = 370 ∨ k.val = 371 ∨ k.val = 372 ∨ k.val = 373 ∨ k.val = 374 ∨ k.val = 375 ∨ k.val = 376 ∨ k.val = 377 ∨ k.val = 378 ∨ k.val = 379 ∨ k.val = 380 ∨ k.val = 381 ∨ k.val = 382 ∨ k.val = 383 := by omega
  rcases heq with h368 | h369 | h370 | h371 | h372 | h373 | h374 | h375 | h376 | h377 | h378 | h379 | h380 | h381 | h382 | h383
  · have he : k = (368 : Fin 2425) := Fin.ext h368
    subst k
    rw [sourceRowsAt368]
    exact rowSound368_e B hB hF
  · have he : k = (369 : Fin 2425) := Fin.ext h369
    subst k
    rw [sourceRowsAt369]
    exact rowSound369_e B hB hF
  · have he : k = (370 : Fin 2425) := Fin.ext h370
    subst k
    rw [sourceRowsAt370]
    exact rowSound370_e B hB hF
  · have he : k = (371 : Fin 2425) := Fin.ext h371
    subst k
    rw [sourceRowsAt371]
    exact rowSound371_e B hB hF
  · have he : k = (372 : Fin 2425) := Fin.ext h372
    subst k
    rw [sourceRowsAt372]
    exact rowSound372 B hB hF
  · have he : k = (373 : Fin 2425) := Fin.ext h373
    subst k
    rw [sourceRowsAt373]
    exact rowSound373 B hB hF
  · have he : k = (374 : Fin 2425) := Fin.ext h374
    subst k
    rw [sourceRowsAt374]
    exact rowSound374 B hB hF
  · have he : k = (375 : Fin 2425) := Fin.ext h375
    subst k
    rw [sourceRowsAt375]
    exact rowSound375 B hB hF
  · have he : k = (376 : Fin 2425) := Fin.ext h376
    subst k
    rw [sourceRowsAt376]
    exact rowSound376 B hB hF
  · have he : k = (377 : Fin 2425) := Fin.ext h377
    subst k
    rw [sourceRowsAt377]
    exact rowSound377 B hB hF
  · have he : k = (378 : Fin 2425) := Fin.ext h378
    subst k
    rw [sourceRowsAt378]
    exact rowSound378 B hB hF
  · have he : k = (379 : Fin 2425) := Fin.ext h379
    subst k
    rw [sourceRowsAt379]
    exact rowSound379 B hB hF
  · have he : k = (380 : Fin 2425) := Fin.ext h380
    subst k
    rw [sourceRowsAt380]
    exact rowSound380_e B hB hF
  · have he : k = (381 : Fin 2425) := Fin.ext h381
    subst k
    rw [sourceRowsAt381]
    exact rowSound381 B hB hF
  · have he : k = (382 : Fin 2425) := Fin.ext h382
    subst k
    rw [sourceRowsAt382]
    exact rowSound382 B hB hF
  · have he : k = (383 : Fin 2425) := Fin.ext h383
    subst k
    rw [sourceRowsAt383]
    exact rowSound383 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e_oai
