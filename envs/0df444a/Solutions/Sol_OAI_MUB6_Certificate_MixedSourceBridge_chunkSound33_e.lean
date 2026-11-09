-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:10:07.208663+00:00
-- url     : https://prove2.me/submissions/e4c920fd-50c6-4d36-b912-2e59c3432068

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound531_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound532_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound533_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound534_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound537_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound538_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound539_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound540_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound541_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound542_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound543_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem canonical1443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1443 raw1443Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw1443 raw1443Labels = mixedMoment B raw1443step0 raw1443step0Labels := by
      have ha : raw1443step0 = (fun i j => raw1443 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1443step0 raw1443; decide +kernel
      have hl : raw1443step0Labels = raw1443Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1443 raw1443Labels permutation8 permutation4
    mixedMoment B raw1443step0 raw1443step0Labels = mixedMoment B raw1443step1 raw1443step1Labels := by
      have ha : raw1443step1 = raw1443step0 := by apply Matrix.ext; unfold raw1443step1 raw1443step0; decide +kernel
      have hl : raw1443step0Labels = labelEmbedding7 ∘ raw1443step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1443step0 raw1443step0Labels raw1443step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

theorem canonical1444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1444 raw1444Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw1444 raw1444Labels = mixedMoment B raw1444step0 raw1444step0Labels := by
      have ha : raw1444step0 = (fun i j => raw1444 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1444step0 raw1444; decide +kernel
      have hl : raw1444step0Labels = raw1444Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1444 raw1444Labels permutation8 permutation4
    _ = mixedMoment B node1294 node1294Labels := by rfl

theorem canonical1445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1445 raw1445Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw1445 raw1445Labels = mixedMoment B raw1445step0 raw1445step0Labels := by
      have ha : raw1445step0 = (fun i j => raw1445 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1445step0 raw1445; decide +kernel
      have hl : raw1445step0Labels = raw1445Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1445 raw1445Labels permutation8 permutation6
    mixedMoment B raw1445step0 raw1445step0Labels = mixedMoment B raw1445step1 raw1445step1Labels := by
      have ha : raw1445step1 = -raw1445step0 := by apply Matrix.ext; change ∀ i j, raw1445step1 i j = -(raw1445step0 i j); unfold raw1445step1 raw1445step0; decide +kernel
      have hl : raw1445step1Labels = raw1445step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1445step1 raw1445step1Labels = mixedMoment B raw1445step2 raw1445step2Labels := by
      have ha : raw1445step2 = raw1445step1 := by apply Matrix.ext; unfold raw1445step2 raw1445step1; decide +kernel
      have hl : raw1445step1Labels = labelEmbedding1 ∘ raw1445step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1445step1 raw1445step1Labels raw1445step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3305 node3305Labels := by rfl

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

theorem canonical2097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2097 raw2097Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw2097 raw2097Labels = mixedMoment B raw2097step0 raw2097step0Labels := by
      have ha : raw2097step0 = (fun i j => raw2097 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2097step0 raw2097; decide +kernel
      have hl : raw2097step0Labels = raw2097Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2097 raw2097Labels permutation32 permutation4
    mixedMoment B raw2097step0 raw2097step0Labels = mixedMoment B raw2097step1 raw2097step1Labels := by
      have ha : raw2097step1 = raw2097step0 := by apply Matrix.ext; unfold raw2097step1 raw2097step0; decide +kernel
      have hl : raw2097step0Labels = labelEmbedding7 ∘ raw2097step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2097step0 raw2097step0Labels raw2097step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

theorem canonical2098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2098 raw2098Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw2098 raw2098Labels = mixedMoment B raw2098step0 raw2098step0Labels := by
      have ha : raw2098step0 = (fun i j => raw2098 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2098step0 raw2098; decide +kernel
      have hl : raw2098step0Labels = raw2098Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2098 raw2098Labels permutation32 permutation4
    _ = mixedMoment B node2482 node2482Labels := by rfl

theorem canonical2099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2099 raw2099Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw2099 raw2099Labels = mixedMoment B raw2099step0 raw2099step0Labels := by
      have ha : raw2099step0 = (fun i j => raw2099 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2099step0 raw2099; decide +kernel
      have hl : raw2099step0Labels = raw2099Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2099 raw2099Labels permutation34 permutation6
    mixedMoment B raw2099step0 raw2099step0Labels = mixedMoment B raw2099step1 raw2099step1Labels := by
      have ha : raw2099step1 = -raw2099step0 := by apply Matrix.ext; change ∀ i j, raw2099step1 i j = -(raw2099step0 i j); unfold raw2099step1 raw2099step0; decide +kernel
      have hl : raw2099step1Labels = raw2099step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2099step1 raw2099step1Labels = mixedMoment B raw2099step2 raw2099step2Labels := by
      have ha : raw2099step2 = raw2099step1 := by apply Matrix.ext; unfold raw2099step2 raw2099step1; decide +kernel
      have hl : raw2099step1Labels = labelEmbedding1 ∘ raw2099step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2099step1 raw2099step1Labels raw2099step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

theorem canonical2163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2163 raw2163Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw2163 raw2163Labels = mixedMoment B raw2163step0 raw2163step0Labels := by
      have ha : raw2163step0 = (fun i j => raw2163 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2163step0 raw2163; decide +kernel
      have hl : raw2163step0Labels = raw2163Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2163 raw2163Labels permutation152 permutation4
    mixedMoment B raw2163step0 raw2163step0Labels = mixedMoment B raw2163step1 raw2163step1Labels := by
      have ha : raw2163step1 = raw2163step0 := by apply Matrix.ext; unfold raw2163step1 raw2163step0; decide +kernel
      have hl : raw2163step0Labels = labelEmbedding7 ∘ raw2163step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2163step0 raw2163step0Labels raw2163step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical2164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2164 raw2164Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw2164 raw2164Labels = mixedMoment B raw2164step0 raw2164step0Labels := by
      have ha : raw2164step0 = (fun i j => raw2164 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2164step0 raw2164; decide +kernel
      have hl : raw2164step0Labels = raw2164Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2164 raw2164Labels permutation152 permutation4
    _ = mixedMoment B node2553 node2553Labels := by rfl

theorem canonical2165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2165 raw2165Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw2165 raw2165Labels = mixedMoment B raw2165step0 raw2165step0Labels := by
      have ha : raw2165step0 = (fun i j => raw2165 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2165step0 raw2165; decide +kernel
      have hl : raw2165step0Labels = raw2165Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2165 raw2165Labels permutation176 permutation6
    mixedMoment B raw2165step0 raw2165step0Labels = mixedMoment B raw2165step1 raw2165step1Labels := by
      have ha : raw2165step1 = -raw2165step0 := by apply Matrix.ext; change ∀ i j, raw2165step1 i j = -(raw2165step0 i j); unfold raw2165step1 raw2165step0; decide +kernel
      have hl : raw2165step1Labels = raw2165step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2165step1 raw2165step1Labels = mixedMoment B raw2165step2 raw2165step2Labels := by
      have ha : raw2165step2 = raw2165step1 := by apply Matrix.ext; unfold raw2165step2 raw2165step1; decide +kernel
      have hl : raw2165step1Labels = labelEmbedding1 ∘ raw2165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2165step1 raw2165step1Labels raw2165step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

theorem canonical2169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2169 raw2169Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw2169 raw2169Labels = mixedMoment B raw2169step0 raw2169step0Labels := by
      have ha : raw2169step0 = (fun i j => raw2169 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2169step0 raw2169; decide +kernel
      have hl : raw2169step0Labels = raw2169Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2169 raw2169Labels permutation32 permutation4
    mixedMoment B raw2169step0 raw2169step0Labels = mixedMoment B raw2169step1 raw2169step1Labels := by
      have ha : raw2169step1 = raw2169step0 := by apply Matrix.ext; unfold raw2169step1 raw2169step0; decide +kernel
      have hl : raw2169step0Labels = labelEmbedding7 ∘ raw2169step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2169step0 raw2169step0Labels raw2169step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical2170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2170 raw2170Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw2170 raw2170Labels = mixedMoment B raw2170step0 raw2170step0Labels := by
      have ha : raw2170step0 = (fun i j => raw2170 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2170step0 raw2170; decide +kernel
      have hl : raw2170step0Labels = raw2170Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2170 raw2170Labels permutation32 permutation4
    _ = mixedMoment B node2561 node2561Labels := by rfl

theorem canonical2171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2171 raw2171Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw2171 raw2171Labels = mixedMoment B raw2171step0 raw2171step0Labels := by
      have ha : raw2171step0 = (fun i j => raw2171 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2171step0 raw2171; decide +kernel
      have hl : raw2171step0Labels = raw2171Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2171 raw2171Labels permutation38 permutation6
    mixedMoment B raw2171step0 raw2171step0Labels = mixedMoment B raw2171step1 raw2171step1Labels := by
      have ha : raw2171step1 = -raw2171step0 := by apply Matrix.ext; change ∀ i j, raw2171step1 i j = -(raw2171step0 i j); unfold raw2171step1 raw2171step0; decide +kernel
      have hl : raw2171step1Labels = raw2171step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2171step1 raw2171step1Labels = mixedMoment B raw2171step2 raw2171step2Labels := by
      have ha : raw2171step2 = raw2171step1 := by apply Matrix.ext; unfold raw2171step2 raw2171step1; decide +kernel
      have hl : raw2171step1Labels = labelEmbedding1 ∘ raw2171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2171step1 raw2171step1Labels raw2171step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

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

theorem canonical2190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2190 raw2190Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw2190 raw2190Labels = mixedMoment B raw2190step0 raw2190step0Labels := by
      have ha : raw2190step0 = (fun i j => raw2190 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2190step0 raw2190; decide +kernel
      have hl : raw2190step0Labels = raw2190Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2190 raw2190Labels permutation32 permutation4
    mixedMoment B raw2190step0 raw2190step0Labels = mixedMoment B raw2190step1 raw2190step1Labels := by
      have ha : raw2190step1 = raw2190step0 := by apply Matrix.ext; unfold raw2190step1 raw2190step0; decide +kernel
      have hl : raw2190step0Labels = labelEmbedding7 ∘ raw2190step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2190step0 raw2190step0Labels raw2190step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

theorem canonical2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2191 raw2191Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw2191 raw2191Labels = mixedMoment B raw2191step0 raw2191step0Labels := by
      have ha : raw2191step0 = (fun i j => raw2191 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2191step0 raw2191; decide +kernel
      have hl : raw2191step0Labels = raw2191Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2191 raw2191Labels permutation32 permutation4
    _ = mixedMoment B node2590 node2590Labels := by rfl

theorem canonical2192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2192 raw2192Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw2192 raw2192Labels = mixedMoment B raw2192step0 raw2192step0Labels := by
      have ha : raw2192step0 = (fun i j => raw2192 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2192step0 raw2192; decide +kernel
      have hl : raw2192step0Labels = raw2192Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2192 raw2192Labels permutation38 permutation6
    mixedMoment B raw2192step0 raw2192step0Labels = mixedMoment B raw2192step1 raw2192step1Labels := by
      have ha : raw2192step1 = -raw2192step0 := by apply Matrix.ext; change ∀ i j, raw2192step1 i j = -(raw2192step0 i j); unfold raw2192step1 raw2192step0; decide +kernel
      have hl : raw2192step1Labels = raw2192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2192step1 raw2192step1Labels = mixedMoment B raw2192step2 raw2192step2Labels := by
      have ha : raw2192step2 = raw2192step1 := by apply Matrix.ext; unfold raw2192step2 raw2192step1; decide +kernel
      have hl : raw2192step1Labels = labelEmbedding1 ∘ raw2192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2192step1 raw2192step1Labels raw2192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

theorem canonical2271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2271 raw2271Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw2271 raw2271Labels = mixedMoment B raw2271step0 raw2271step0Labels := by
      have ha : raw2271step0 = (fun i j => raw2271 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2271step0 raw2271; decide +kernel
      have hl : raw2271step0Labels = raw2271Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2271 raw2271Labels permutation32 permutation4
    mixedMoment B raw2271step0 raw2271step0Labels = mixedMoment B raw2271step1 raw2271step1Labels := by
      have ha : raw2271step1 = raw2271step0 := by apply Matrix.ext; unfold raw2271step1 raw2271step0; decide +kernel
      have hl : raw2271step0Labels = labelEmbedding7 ∘ raw2271step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2271step0 raw2271step0Labels raw2271step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical2272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2272 raw2272Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw2272 raw2272Labels = mixedMoment B raw2272step0 raw2272step0Labels := by
      have ha : raw2272step0 = (fun i j => raw2272 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2272step0 raw2272; decide +kernel
      have hl : raw2272step0Labels = raw2272Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2272 raw2272Labels permutation32 permutation4
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical2273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2273 raw2273Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw2273 raw2273Labels = mixedMoment B raw2273step0 raw2273step0Labels := by
      have ha : raw2273step0 = (fun i j => raw2273 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2273step0 raw2273; decide +kernel
      have hl : raw2273step0Labels = raw2273Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2273 raw2273Labels permutation34 permutation6
    mixedMoment B raw2273step0 raw2273step0Labels = mixedMoment B raw2273step1 raw2273step1Labels := by
      have ha : raw2273step1 = -raw2273step0 := by apply Matrix.ext; change ∀ i j, raw2273step1 i j = -(raw2273step0 i j); unfold raw2273step1 raw2273step0; decide +kernel
      have hl : raw2273step1Labels = raw2273step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2273step1 raw2273step1Labels = mixedMoment B raw2273step2 raw2273step2Labels := by
      have ha : raw2273step2 = raw2273step1 := by apply Matrix.ext; unfold raw2273step2 raw2273step1; decide +kernel
      have hl : raw2273step1Labels = labelEmbedding1 ∘ raw2273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2273step1 raw2273step1Labels raw2273step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2277 raw2277Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw2277 raw2277Labels = mixedMoment B raw2277step0 raw2277step0Labels := by
      have ha : raw2277step0 = (fun i j => raw2277 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2277step0 raw2277; decide +kernel
      have hl : raw2277step0Labels = raw2277Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2277 raw2277Labels permutation8 permutation4
    mixedMoment B raw2277step0 raw2277step0Labels = mixedMoment B raw2277step1 raw2277step1Labels := by
      have ha : raw2277step1 = raw2277step0 := by apply Matrix.ext; unfold raw2277step1 raw2277step0; decide +kernel
      have hl : raw2277step0Labels = labelEmbedding7 ∘ raw2277step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2277step0 raw2277step0Labels raw2277step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

theorem canonical2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2278 raw2278Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw2278 raw2278Labels = mixedMoment B raw2278step0 raw2278step0Labels := by
      have ha : raw2278step0 = (fun i j => raw2278 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2278step0 raw2278; decide +kernel
      have hl : raw2278step0Labels = raw2278Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2278 raw2278Labels permutation8 permutation4
    _ = mixedMoment B node2726 node2726Labels := by rfl

theorem canonical2279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2279 raw2279Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw2279 raw2279Labels = mixedMoment B raw2279step0 raw2279step0Labels := by
      have ha : raw2279step0 = (fun i j => raw2279 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2279step0 raw2279; decide +kernel
      have hl : raw2279step0Labels = raw2279Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2279 raw2279Labels permutation31 permutation6
    mixedMoment B raw2279step0 raw2279step0Labels = mixedMoment B raw2279step1 raw2279step1Labels := by
      have ha : raw2279step1 = raw2279step0 := by apply Matrix.ext; unfold raw2279step1 raw2279step0; decide +kernel
      have hl : raw2279step0Labels = labelEmbedding1 ∘ raw2279step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2279step0 raw2279step0Labels raw2279step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3545 node3545Labels := by rfl

theorem canonical2280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2280 raw2280Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw2280 raw2280Labels = mixedMoment B raw2280step0 raw2280step0Labels := by
      have ha : raw2280step0 = (fun i j => raw2280 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2280step0 raw2280; decide +kernel
      have hl : raw2280step0Labels = raw2280Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2280 raw2280Labels permutation32 permutation4
    mixedMoment B raw2280step0 raw2280step0Labels = mixedMoment B raw2280step1 raw2280step1Labels := by
      have ha : raw2280step1 = raw2280step0 := by apply Matrix.ext; unfold raw2280step1 raw2280step0; decide +kernel
      have hl : raw2280step0Labels = labelEmbedding7 ∘ raw2280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2280step0 raw2280step0Labels raw2280step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2281 raw2281Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw2281 raw2281Labels = mixedMoment B raw2281step0 raw2281step0Labels := by
      have ha : raw2281step0 = (fun i j => raw2281 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2281step0 raw2281; decide +kernel
      have hl : raw2281step0Labels = raw2281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2281 raw2281Labels permutation32 permutation4
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical2282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2282 raw2282Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw2282 raw2282Labels = mixedMoment B raw2282step0 raw2282step0Labels := by
      have ha : raw2282step0 = (fun i j => raw2282 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2282step0 raw2282; decide +kernel
      have hl : raw2282step0Labels = raw2282Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2282 raw2282Labels permutation32 permutation6
    mixedMoment B raw2282step0 raw2282step0Labels = mixedMoment B raw2282step1 raw2282step1Labels := by
      have ha : raw2282step1 = -raw2282step0 := by apply Matrix.ext; change ∀ i j, raw2282step1 i j = -(raw2282step0 i j); unfold raw2282step1 raw2282step0; decide +kernel
      have hl : raw2282step1Labels = raw2282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2282step1 raw2282step1Labels = mixedMoment B raw2282step2 raw2282step2Labels := by
      have ha : raw2282step2 = raw2282step1 := by apply Matrix.ext; unfold raw2282step2 raw2282step1; decide +kernel
      have hl : raw2282step1Labels = labelEmbedding1 ∘ raw2282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2282step1 raw2282step1Labels raw2282step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical2286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2286 raw2286Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw2286 raw2286Labels = mixedMoment B raw2286step0 raw2286step0Labels := by
      have ha : raw2286step0 = (fun i j => raw2286 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2286step0 raw2286; decide +kernel
      have hl : raw2286step0Labels = raw2286Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2286 raw2286Labels permutation8 permutation4
    mixedMoment B raw2286step0 raw2286step0Labels = mixedMoment B raw2286step1 raw2286step1Labels := by
      have ha : raw2286step1 = raw2286step0 := by apply Matrix.ext; unfold raw2286step1 raw2286step0; decide +kernel
      have hl : raw2286step0Labels = labelEmbedding7 ∘ raw2286step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2286step0 raw2286step0Labels raw2286step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2287 raw2287Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw2287 raw2287Labels = mixedMoment B raw2287step0 raw2287step0Labels := by
      have ha : raw2287step0 = (fun i j => raw2287 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2287step0 raw2287; decide +kernel
      have hl : raw2287step0Labels = raw2287Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2287 raw2287Labels permutation8 permutation4
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical2288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2288 raw2288Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw2288 raw2288Labels = mixedMoment B raw2288step0 raw2288step0Labels := by
      have ha : raw2288step0 = (fun i j => raw2288 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2288step0 raw2288; decide +kernel
      have hl : raw2288step0Labels = raw2288Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2288 raw2288Labels permutation9 permutation6
    mixedMoment B raw2288step0 raw2288step0Labels = mixedMoment B raw2288step1 raw2288step1Labels := by
      have ha : raw2288step1 = -raw2288step0 := by apply Matrix.ext; change ∀ i j, raw2288step1 i j = -(raw2288step0 i j); unfold raw2288step1 raw2288step0; decide +kernel
      have hl : raw2288step1Labels = raw2288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2288step1 raw2288step1Labels = mixedMoment B raw2288step2 raw2288step2Labels := by
      have ha : raw2288step2 = raw2288step1 := by apply Matrix.ext; unfold raw2288step2 raw2288step1; decide +kernel
      have hl : raw2288step1Labels = labelEmbedding1 ∘ raw2288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2288step1 raw2288step1Labels raw2288step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

theorem canonical2295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2295 raw2295Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw2295 raw2295Labels = mixedMoment B raw2295step0 raw2295step0Labels := by
      have ha : raw2295step0 = (fun i j => raw2295 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2295step0 raw2295; decide +kernel
      have hl : raw2295step0Labels = raw2295Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2295 raw2295Labels permutation8 permutation4
    mixedMoment B raw2295step0 raw2295step0Labels = mixedMoment B raw2295step1 raw2295step1Labels := by
      have ha : raw2295step1 = raw2295step0 := by apply Matrix.ext; unfold raw2295step1 raw2295step0; decide +kernel
      have hl : raw2295step0Labels = labelEmbedding7 ∘ raw2295step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2295step0 raw2295step0Labels raw2295step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical2296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2296 raw2296Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw2296 raw2296Labels = mixedMoment B raw2296step0 raw2296step0Labels := by
      have ha : raw2296step0 = (fun i j => raw2296 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2296step0 raw2296; decide +kernel
      have hl : raw2296step0Labels = raw2296Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2296 raw2296Labels permutation8 permutation4
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical2297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2297 raw2297Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw2297 raw2297Labels = mixedMoment B raw2297step0 raw2297step0Labels := by
      have ha : raw2297step0 = (fun i j => raw2297 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2297step0 raw2297; decide +kernel
      have hl : raw2297step0Labels = raw2297Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2297 raw2297Labels permutation10 permutation6
    mixedMoment B raw2297step0 raw2297step0Labels = mixedMoment B raw2297step1 raw2297step1Labels := by
      have ha : raw2297step1 = -raw2297step0 := by apply Matrix.ext; change ∀ i j, raw2297step1 i j = -(raw2297step0 i j); unfold raw2297step1 raw2297step0; decide +kernel
      have hl : raw2297step1Labels = raw2297step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2297step1 raw2297step1Labels = mixedMoment B raw2297step2 raw2297step2Labels := by
      have ha : raw2297step2 = raw2297step1 := by apply Matrix.ext; unfold raw2297step2 raw2297step1; decide +kernel
      have hl : raw2297step1Labels = labelEmbedding1 ∘ raw2297step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2297step1 raw2297step1Labels raw2297step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5754 raw5754Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5754 raw5754Labels = mixedMoment B raw5754step0 raw5754step0Labels := by
      have hz : ∀ j, raw5754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5754step0 = (fun i j => raw5754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5754step0 raw5754; decide +kernel
      have hl : raw5754step0Labels = raw5754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754 raw5754Labels permutation434 hz
    mixedMoment B raw5754step0 raw5754step0Labels = mixedMoment B raw5754step1 raw5754step1Labels := by
      have hz : ∀ j, raw5754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5754step1 = (fun i j => raw5754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5754step1 raw5754step0; decide +kernel
      have hl : raw5754step1Labels = raw5754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step0 raw5754step0Labels permutation80 hz
    mixedMoment B raw5754step1 raw5754step1Labels = mixedMoment B raw5754step2 raw5754step2Labels := by
      have hz : ∀ j, raw5754step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5754step2 = (fun i j => raw5754step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5754step2 raw5754step1; decide +kernel
      have hl : raw5754step2Labels = raw5754step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step1 raw5754step1Labels permutation14 hz
    mixedMoment B raw5754step2 raw5754step2Labels = mixedMoment B raw5754step3 raw5754step3Labels := by
      have ha : raw5754step3 = -raw5754step2 := by apply Matrix.ext; change ∀ i j, raw5754step3 i j = -(raw5754step2 i j); unfold raw5754step3 raw5754step2; decide +kernel
      have hl : raw5754step3Labels = raw5754step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7698 raw7698Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw7698 raw7698Labels = mixedMoment B raw7698step0 raw7698step0Labels := by
      have hz : ∀ j, raw7698 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7698step0 = (fun i j => raw7698 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7698step0 raw7698; decide +kernel
      have hl : raw7698step0Labels = raw7698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7698 raw7698Labels permutation434 hz
    mixedMoment B raw7698step0 raw7698step0Labels = mixedMoment B raw7698step1 raw7698step1Labels := by
      have hz : ∀ j, raw7698step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7698step1 = (fun i j => raw7698step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7698step1 raw7698step0; decide +kernel
      have hl : raw7698step1Labels = raw7698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7698step0 raw7698step0Labels permutation80 hz
    mixedMoment B raw7698step1 raw7698step1Labels = mixedMoment B raw7698step2 raw7698step2Labels := by
      have hz : ∀ j, raw7698step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7698step2 = (fun i j => raw7698step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7698step2 raw7698step1; decide +kernel
      have hl : raw7698step2Labels = raw7698step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7698step1 raw7698step1Labels permutation14 hz
    mixedMoment B raw7698step2 raw7698step2Labels = mixedMoment B raw7698step3 raw7698step3Labels := by
      have ha : raw7698step3 = (fun i j => raw7698step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7698step3 raw7698step2; decide +kernel
      have hl : raw7698step3Labels = raw7698step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7698step2 raw7698step2Labels permutation3 permutation4
    mixedMoment B raw7698step3 raw7698step3Labels = mixedMoment B raw7698step4 raw7698step4Labels := by
      have ha : raw7698step4 = -raw7698step3 := by apply Matrix.ext; change ∀ i j, raw7698step4 i j = -(raw7698step3 i j); unfold raw7698step4 raw7698step3; decide +kernel
      have hl : raw7698step4Labels = raw7698step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2293 node2293Labels := by rfl

theorem canonical7700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7700 raw7700Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw7700 raw7700Labels = mixedMoment B raw7700step0 raw7700step0Labels := by
      have hz : ∀ j, raw7700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7700step0 = (fun i j => raw7700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7700step0 raw7700; decide +kernel
      have hl : raw7700step0Labels = raw7700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7700 raw7700Labels permutation346 hz
    mixedMoment B raw7700step0 raw7700step0Labels = mixedMoment B raw7700step1 raw7700step1Labels := by
      have hz : ∀ j, raw7700step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7700step1 = (fun i j => raw7700step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7700step1 raw7700step0; decide +kernel
      have hl : raw7700step1Labels = raw7700step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7700step0 raw7700step0Labels permutation56 hz
    mixedMoment B raw7700step1 raw7700step1Labels = mixedMoment B raw7700step2 raw7700step2Labels := by
      have ha : raw7700step2 = (fun i j => raw7700step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7700step2 raw7700step1; decide +kernel
      have hl : raw7700step2Labels = raw7700step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7700step1 raw7700step1Labels permutation9 permutation4
    mixedMoment B raw7700step2 raw7700step2Labels = mixedMoment B raw7700step3 raw7700step3Labels := by
      have ha : raw7700step3 = -raw7700step2 := by apply Matrix.ext; change ∀ i j, raw7700step3 i j = -(raw7700step2 i j); unfold raw7700step3 raw7700step2; decide +kernel
      have hl : raw7700step3Labels = raw7700step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3548 node3548Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9967 raw9967Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw9967 raw9967Labels = mixedMoment B raw9967step0 raw9967step0Labels := by
      have hz : ∀ j, raw9967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9967step0 = (fun i j => raw9967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9967step0 raw9967; decide +kernel
      have hl : raw9967step0Labels = raw9967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9967 raw9967Labels permutation346 hz
    mixedMoment B raw9967step0 raw9967step0Labels = mixedMoment B raw9967step1 raw9967step1Labels := by
      have ha : raw9967step1 = (fun i j => raw9967step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9967step1 raw9967step0; decide +kernel
      have hl : raw9967step1Labels = raw9967step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9967step0 raw9967step0Labels permutation39 permutation4
    mixedMoment B raw9967step1 raw9967step1Labels = mixedMoment B raw9967step2 raw9967step2Labels := by
      have ha : raw9967step2 = -raw9967step1 := by apply Matrix.ext; change ∀ i j, raw9967step2 i j = -(raw9967step1 i j); unfold raw9967step2 raw9967step1; decide +kernel
      have hl : raw9967step2Labels = raw9967step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2054 node2054Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10432 raw10432Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw10432 raw10432Labels = mixedMoment B raw10432step0 raw10432step0Labels := by
      have hz : ∀ j, raw10432 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10432step0 = (fun i j => raw10432 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10432step0 raw10432; decide +kernel
      have hl : raw10432step0Labels = raw10432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10432 raw10432Labels permutation346 hz
    mixedMoment B raw10432step0 raw10432step0Labels = mixedMoment B raw10432step1 raw10432step1Labels := by
      have hz : ∀ j, raw10432step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10432step1 = (fun i j => raw10432step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10432step1 raw10432step0; decide +kernel
      have hl : raw10432step1Labels = raw10432step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10432step0 raw10432step0Labels permutation56 hz
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical10433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10433 raw10433Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw10433 raw10433Labels = mixedMoment B raw10433step0 raw10433step0Labels := by
      have hz : ∀ j, raw10433 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10433step0 = (fun i j => raw10433 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10433step0 raw10433; decide +kernel
      have hl : raw10433step0Labels = raw10433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10433 raw10433Labels permutation346 hz
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical10435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10435 raw10435Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw10435 raw10435Labels = mixedMoment B raw10435step0 raw10435step0Labels := by
      have hz : ∀ j, raw10435 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10435step0 = (fun i j => raw10435 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10435step0 raw10435; decide +kernel
      have hl : raw10435step0Labels = raw10435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10435 raw10435Labels permutation346 hz
    mixedMoment B raw10435step0 raw10435step0Labels = mixedMoment B raw10435step1 raw10435step1Labels := by
      have hz : ∀ j, raw10435step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10435step1 = (fun i j => raw10435step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10435step1 raw10435step0; decide +kernel
      have hl : raw10435step1Labels = raw10435step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10435step0 raw10435step0Labels permutation56 hz
    _ = mixedMoment B node3817 node3817Labels := by rfl

theorem canonical10438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10438 raw10438Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw10438 raw10438Labels = mixedMoment B raw10438step0 raw10438step0Labels := by
      have hz : ∀ j, raw10438 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10438step0 = (fun i j => raw10438 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10438step0 raw10438; decide +kernel
      have hl : raw10438step0Labels = raw10438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10438 raw10438Labels permutation346 hz
    mixedMoment B raw10438step0 raw10438step0Labels = mixedMoment B raw10438step1 raw10438step1Labels := by
      have hz : ∀ j, raw10438step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10438step1 = (fun i j => raw10438step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10438step1 raw10438step0; decide +kernel
      have hl : raw10438step1Labels = raw10438step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10438step0 raw10438step0Labels permutation56 hz
    mixedMoment B raw10438step1 raw10438step1Labels = mixedMoment B raw10438step2 raw10438step2Labels := by
      have ha : raw10438step2 = (fun i j => raw10438step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw10438step2 raw10438step1; decide +kernel
      have hl : raw10438step2Labels = raw10438step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10438step1 raw10438step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical10439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10439 raw10439Labels = mixedMoment B node2554 node2554Labels := by
  calc
    mixedMoment B raw10439 raw10439Labels = mixedMoment B raw10439step0 raw10439step0Labels := by
      have ha : raw10439step0 = (fun i j => raw10439 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10439step0 raw10439; decide +kernel
      have hl : raw10439step0Labels = raw10439Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10439 raw10439Labels permutation158 permutation2
    _ = mixedMoment B node2554 node2554Labels := by rfl

theorem canonical10440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10440 raw10440Labels = mixedMoment B node2591 node2591Labels := by
  calc
    mixedMoment B raw10440 raw10440Labels = mixedMoment B raw10440step0 raw10440step0Labels := by
      have hz : ∀ j, raw10440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10440step0 = (fun i j => raw10440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10440step0 raw10440; decide +kernel
      have hl : raw10440step0Labels = raw10440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10440 raw10440Labels permutation346 hz
    _ = mixedMoment B node2591 node2591Labels := by rfl

theorem canonical10441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10441 raw10441Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw10441 raw10441Labels = mixedMoment B raw10441step0 raw10441step0Labels := by
      have hz : ∀ j, raw10441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10441step0 = (fun i j => raw10441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10441step0 raw10441; decide +kernel
      have hl : raw10441step0Labels = raw10441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10441 raw10441Labels permutation346 hz
    mixedMoment B raw10441step0 raw10441step0Labels = mixedMoment B raw10441step1 raw10441step1Labels := by
      have ha : raw10441step1 = (fun i j => raw10441step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10441step1 raw10441step0; decide +kernel
      have hl : raw10441step1Labels = raw10441step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10441step0 raw10441step0Labels permutation33 permutation2
    _ = mixedMoment B node2561 node2561Labels := by rfl

theorem canonical10442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10442 raw10442Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw10442 raw10442Labels = mixedMoment B raw10442step0 raw10442step0Labels := by
      have hz : ∀ j, raw10442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10442step0 = (fun i j => raw10442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10442step0 raw10442; decide +kernel
      have hl : raw10442step0Labels = raw10442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10442 raw10442Labels permutation346 hz
    _ = mixedMoment B node2558 node2558Labels := by rfl

theorem canonical10443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10443 raw10443Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw10443 raw10443Labels = mixedMoment B raw10443step0 raw10443step0Labels := by
      have hz : ∀ j, raw10443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10443step0 = (fun i j => raw10443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10443step0 raw10443; decide +kernel
      have hl : raw10443step0Labels = raw10443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10443 raw10443Labels permutation346 hz
    mixedMoment B raw10443step0 raw10443step0Labels = mixedMoment B raw10443step1 raw10443step1Labels := by
      have ha : raw10443step1 = (fun i j => raw10443step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10443step1 raw10443step0; decide +kernel
      have hl : raw10443step1Labels = raw10443step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10443step0 raw10443step0Labels permutation38 permutation2
    _ = mixedMoment B node2512 node2512Labels := by rfl

theorem canonical10444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10444 raw10444Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw10444 raw10444Labels = mixedMoment B raw10444step0 raw10444step0Labels := by
      have hz : ∀ j, raw10444 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10444step0 = (fun i j => raw10444 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10444step0 raw10444; decide +kernel
      have hl : raw10444step0Labels = raw10444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10444 raw10444Labels permutation265 hz
    mixedMoment B raw10444step0 raw10444step0Labels = mixedMoment B raw10444step1 raw10444step1Labels := by
      have ha : raw10444step1 = (fun i j => raw10444step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10444step1 raw10444step0; decide +kernel
      have hl : raw10444step1Labels = raw10444step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10444step0 raw10444step0Labels permutation38 permutation2
    _ = mixedMoment B node2512 node2512Labels := by rfl

theorem canonical10445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10445 raw10445Labels = mixedMoment B node2523 node2523Labels := by
  calc
    mixedMoment B raw10445 raw10445Labels = mixedMoment B raw10445step0 raw10445step0Labels := by
      have hz : ∀ j, raw10445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10445step0 = (fun i j => raw10445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10445step0 raw10445; decide +kernel
      have hl : raw10445step0Labels = raw10445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10445 raw10445Labels permutation346 hz
    mixedMoment B raw10445step0 raw10445step0Labels = mixedMoment B raw10445step1 raw10445step1Labels := by
      have hz : ∀ j, raw10445step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10445step1 = (fun i j => raw10445step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10445step1 raw10445step0; decide +kernel
      have hl : raw10445step1Labels = raw10445step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10445step0 raw10445step0Labels permutation56 hz
    mixedMoment B raw10445step1 raw10445step1Labels = mixedMoment B raw10445step2 raw10445step2Labels := by
      have ha : raw10445step2 = (fun i j => raw10445step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10445step2 raw10445step1; decide +kernel
      have hl : raw10445step2Labels = raw10445step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10445step1 raw10445step1Labels permutation9 permutation2
    _ = mixedMoment B node2523 node2523Labels := by rfl

theorem canonical10446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10446 raw10446Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw10446 raw10446Labels = mixedMoment B raw10446step0 raw10446step0Labels := by
      have hz : ∀ j, raw10446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10446step0 = (fun i j => raw10446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10446step0 raw10446; decide +kernel
      have hl : raw10446step0Labels = raw10446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10446 raw10446Labels permutation346 hz
    mixedMoment B raw10446step0 raw10446step0Labels = mixedMoment B raw10446step1 raw10446step1Labels := by
      have hz : ∀ j, raw10446step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10446step1 = (fun i j => raw10446step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10446step1 raw10446step0; decide +kernel
      have hl : raw10446step1Labels = raw10446step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10446step0 raw10446step0Labels permutation56 hz
    _ = mixedMoment B node2519 node2519Labels := by rfl

theorem canonical10447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10447 raw10447Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw10447 raw10447Labels = mixedMoment B raw10447step0 raw10447step0Labels := by
      have hz : ∀ j, raw10447 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10447step0 = (fun i j => raw10447 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10447step0 raw10447; decide +kernel
      have hl : raw10447step0Labels = raw10447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10447 raw10447Labels permutation346 hz
    mixedMoment B raw10447step0 raw10447step0Labels = mixedMoment B raw10447step1 raw10447step1Labels := by
      have hz : ∀ j, raw10447step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10447step1 = (fun i j => raw10447step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10447step1 raw10447step0; decide +kernel
      have hl : raw10447step1Labels = raw10447step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10447step0 raw10447step0Labels permutation56 hz
    mixedMoment B raw10447step1 raw10447step1Labels = mixedMoment B raw10447step2 raw10447step2Labels := by
      have ha : raw10447step2 = (fun i j => raw10447step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10447step2 raw10447step1; decide +kernel
      have hl : raw10447step2Labels = raw10447step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10447step1 raw10447step1Labels permutation9 permutation2
    _ = mixedMoment B node1246 node1246Labels := by rfl

theorem canonical10448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10448 raw10448Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw10448 raw10448Labels = mixedMoment B raw10448step0 raw10448step0Labels := by
      have hz : ∀ j, raw10448 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10448step0 = (fun i j => raw10448 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10448step0 raw10448; decide +kernel
      have hl : raw10448step0Labels = raw10448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10448 raw10448Labels permutation265 hz
    mixedMoment B raw10448step0 raw10448step0Labels = mixedMoment B raw10448step1 raw10448step1Labels := by
      have ha : raw10448step1 = (fun i j => raw10448step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10448step1 raw10448step0; decide +kernel
      have hl : raw10448step1Labels = raw10448step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10448step0 raw10448step0Labels permutation33 permutation2
    _ = mixedMoment B node2561 node2561Labels := by rfl

theorem canonical10449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10449 raw10449Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw10449 raw10449Labels = mixedMoment B raw10449step0 raw10449step0Labels := by
      have hz : ∀ j, raw10449 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10449step0 = (fun i j => raw10449 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10449step0 raw10449; decide +kernel
      have hl : raw10449step0Labels = raw10449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10449 raw10449Labels permutation346 hz
    mixedMoment B raw10449step0 raw10449step0Labels = mixedMoment B raw10449step1 raw10449step1Labels := by
      have hz : ∀ j, raw10449step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10449step1 = (fun i j => raw10449step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10449step1 raw10449step0; decide +kernel
      have hl : raw10449step1Labels = raw10449step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10449step0 raw10449step0Labels permutation56 hz
    mixedMoment B raw10449step1 raw10449step1Labels = mixedMoment B raw10449step2 raw10449step2Labels := by
      have ha : raw10449step2 = (fun i j => raw10449step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10449step2 raw10449step1; decide +kernel
      have hl : raw10449step2Labels = raw10449step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10449step1 raw10449step1Labels permutation9 permutation2
    _ = mixedMoment B node2742 node2742Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10536 raw10536Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw10536 raw10536Labels = mixedMoment B raw10536step0 raw10536step0Labels := by
      have hz : ∀ j, raw10536 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10536step0 = (fun i j => raw10536 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10536step0 raw10536; decide +kernel
      have hl : raw10536step0Labels = raw10536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10536 raw10536Labels permutation265 hz
    mixedMoment B raw10536step0 raw10536step0Labels = mixedMoment B raw10536step1 raw10536step1Labels := by
      have ha : raw10536step1 = (fun i j => raw10536step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10536step1 raw10536step0; decide +kernel
      have hl : raw10536step1Labels = raw10536step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10536step0 raw10536step0Labels permutation39 permutation4
    mixedMoment B raw10536step1 raw10536step1Labels = mixedMoment B raw10536step2 raw10536step2Labels := by
      have ha : raw10536step2 = -raw10536step1 := by apply Matrix.ext; change ∀ i j, raw10536step2 i j = -(raw10536step1 i j); unfold raw10536step2 raw10536step1; decide +kernel
      have hl : raw10536step2Labels = raw10536step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2054 node2054Labels := by rfl

theorem canonical10537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10537 raw10537Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw10537 raw10537Labels = mixedMoment B raw10537step0 raw10537step0Labels := by
      have hz : ∀ j, raw10537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10537step0 = (fun i j => raw10537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10537step0 raw10537; decide +kernel
      have hl : raw10537step0Labels = raw10537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10537 raw10537Labels permutation346 hz
    mixedMoment B raw10537step0 raw10537step0Labels = mixedMoment B raw10537step1 raw10537step1Labels := by
      have hz : ∀ j, raw10537step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10537step1 = (fun i j => raw10537step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10537step1 raw10537step0; decide +kernel
      have hl : raw10537step1Labels = raw10537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10537step0 raw10537step0Labels permutation56 hz
    mixedMoment B raw10537step1 raw10537step1Labels = mixedMoment B raw10537step2 raw10537step2Labels := by
      have ha : raw10537step2 = (fun i j => raw10537step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10537step2 raw10537step1; decide +kernel
      have hl : raw10537step2Labels = raw10537step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10537step1 raw10537step1Labels permutation9 permutation4
    mixedMoment B raw10537step2 raw10537step2Labels = mixedMoment B raw10537step3 raw10537step3Labels := by
      have ha : raw10537step3 = -raw10537step2 := by apply Matrix.ext; change ∀ i j, raw10537step3 i j = -(raw10537step2 i j); unfold raw10537step3 raw10537step2; decide +kernel
      have hl : raw10537step3Labels = raw10537step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical10538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10538 raw10538Labels = mixedMoment B node2066 node2066Labels := by
  calc
    mixedMoment B raw10538 raw10538Labels = mixedMoment B raw10538step0 raw10538step0Labels := by
      have hz : ∀ j, raw10538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10538step0 = (fun i j => raw10538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10538step0 raw10538; decide +kernel
      have hl : raw10538step0Labels = raw10538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10538 raw10538Labels permutation346 hz
    mixedMoment B raw10538step0 raw10538step0Labels = mixedMoment B raw10538step1 raw10538step1Labels := by
      have hz : ∀ j, raw10538step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10538step1 = (fun i j => raw10538step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10538step1 raw10538step0; decide +kernel
      have hl : raw10538step1Labels = raw10538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10538step0 raw10538step0Labels permutation56 hz
    mixedMoment B raw10538step1 raw10538step1Labels = mixedMoment B raw10538step2 raw10538step2Labels := by
      have ha : raw10538step2 = (fun i j => raw10538step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10538step2 raw10538step1; decide +kernel
      have hl : raw10538step2Labels = raw10538step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10538step1 raw10538step1Labels permutation8 permutation4
    mixedMoment B raw10538step2 raw10538step2Labels = mixedMoment B raw10538step3 raw10538step3Labels := by
      have ha : raw10538step3 = -raw10538step2 := by apply Matrix.ext; change ∀ i j, raw10538step3 i j = -(raw10538step2 i j); unfold raw10538step3 raw10538step2; decide +kernel
      have hl : raw10538step3Labels = raw10538step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2066 node2066Labels := by rfl

theorem canonical10539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10539 raw10539Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw10539 raw10539Labels = mixedMoment B raw10539step0 raw10539step0Labels := by
      have hz : ∀ j, raw10539 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10539step0 = (fun i j => raw10539 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10539step0 raw10539; decide +kernel
      have hl : raw10539step0Labels = raw10539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10539 raw10539Labels permutation346 hz
    mixedMoment B raw10539step0 raw10539step0Labels = mixedMoment B raw10539step1 raw10539step1Labels := by
      have ha : raw10539step1 = (fun i j => raw10539step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10539step1 raw10539step0; decide +kernel
      have hl : raw10539step1Labels = raw10539step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10539step0 raw10539step0Labels permutation151 permutation2
    mixedMoment B raw10539step1 raw10539step1Labels = mixedMoment B raw10539step2 raw10539step2Labels := by
      have ha : raw10539step2 = -raw10539step1 := by apply Matrix.ext; change ∀ i j, raw10539step2 i j = -(raw10539step1 i j); unfold raw10539step2 raw10539step1; decide +kernel
      have hl : raw10539step2Labels = raw10539step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5409 node5409Labels := by rfl

theorem canonical10540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10540 raw10540Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw10540 raw10540Labels = mixedMoment B raw10540step0 raw10540step0Labels := by
      have hz : ∀ j, raw10540 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10540step0 = (fun i j => raw10540 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10540step0 raw10540; decide +kernel
      have hl : raw10540step0Labels = raw10540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10540 raw10540Labels permutation265 hz
    mixedMoment B raw10540step0 raw10540step0Labels = mixedMoment B raw10540step1 raw10540step1Labels := by
      have ha : raw10540step1 = (fun i j => raw10540step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10540step1 raw10540step0; decide +kernel
      have hl : raw10540step1Labels = raw10540step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10540step0 raw10540step0Labels permutation151 permutation2
    mixedMoment B raw10540step1 raw10540step1Labels = mixedMoment B raw10540step2 raw10540step2Labels := by
      have ha : raw10540step2 = -raw10540step1 := by apply Matrix.ext; change ∀ i j, raw10540step2 i j = -(raw10540step1 i j); unfold raw10540step2 raw10540step1; decide +kernel
      have hl : raw10540step2Labels = raw10540step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5409 node5409Labels := by rfl

theorem canonical10541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10541 raw10541Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw10541 raw10541Labels = mixedMoment B raw10541step0 raw10541step0Labels := by
      have hz : ∀ j, raw10541 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10541step0 = (fun i j => raw10541 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10541step0 raw10541; decide +kernel
      have hl : raw10541step0Labels = raw10541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10541 raw10541Labels permutation346 hz
    mixedMoment B raw10541step0 raw10541step0Labels = mixedMoment B raw10541step1 raw10541step1Labels := by
      have hz : ∀ j, raw10541step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10541step1 = (fun i j => raw10541step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10541step1 raw10541step0; decide +kernel
      have hl : raw10541step1Labels = raw10541step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10541step0 raw10541step0Labels permutation56 hz
    mixedMoment B raw10541step1 raw10541step1Labels = mixedMoment B raw10541step2 raw10541step2Labels := by
      have hz : ∀ i, raw10541step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw10541step2 = (fun i j => raw10541step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw10541step2 raw10541step1; decide +kernel
      have hl : raw10541step2Labels = (fun j => raw10541step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw10541step1 raw10541step1Labels permutation4 hz
    mixedMoment B raw10541step2 raw10541step2Labels = mixedMoment B raw10541step3 raw10541step3Labels := by
      have ha : raw10541step3 = raw10541step2 := by apply Matrix.ext; unfold raw10541step3 raw10541step2; decide +kernel
      have hl : raw10541step2Labels = labelEmbedding2 ∘ raw10541step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10541step2 raw10541step2Labels raw10541step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical10542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10542 raw10542Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw10542 raw10542Labels = mixedMoment B raw10542step0 raw10542step0Labels := by
      have hz : ∀ j, raw10542 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10542step0 = (fun i j => raw10542 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10542step0 raw10542; decide +kernel
      have hl : raw10542step0Labels = raw10542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10542 raw10542Labels permutation346 hz
    mixedMoment B raw10542step0 raw10542step0Labels = mixedMoment B raw10542step1 raw10542step1Labels := by
      have hz : ∀ j, raw10542step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10542step1 = (fun i j => raw10542step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10542step1 raw10542step0; decide +kernel
      have hl : raw10542step1Labels = raw10542step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10542step0 raw10542step0Labels permutation56 hz
    mixedMoment B raw10542step1 raw10542step1Labels = mixedMoment B raw10542step2 raw10542step2Labels := by
      have ha : raw10542step2 = (fun i j => raw10542step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10542step2 raw10542step1; decide +kernel
      have hl : raw10542step2Labels = raw10542step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10542step1 raw10542step1Labels permutation31 permutation7
    mixedMoment B raw10542step2 raw10542step2Labels = mixedMoment B raw10542step3 raw10542step3Labels := by
      have ha : raw10542step3 = raw10542step2 := by apply Matrix.ext; unfold raw10542step3 raw10542step2; decide +kernel
      have hl : raw10542step2Labels = labelEmbedding10 ∘ raw10542step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10542step2 raw10542step2Labels raw10542step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5441 node5441Labels := by rfl

theorem canonical10543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10543 raw10543Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw10543 raw10543Labels = mixedMoment B raw10543step0 raw10543step0Labels := by
      have hz : ∀ j, raw10543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10543step0 = (fun i j => raw10543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10543step0 raw10543; decide +kernel
      have hl : raw10543step0Labels = raw10543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10543 raw10543Labels permutation346 hz
    mixedMoment B raw10543step0 raw10543step0Labels = mixedMoment B raw10543step1 raw10543step1Labels := by
      have hz : ∀ j, raw10543step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10543step1 = (fun i j => raw10543step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10543step1 raw10543step0; decide +kernel
      have hl : raw10543step1Labels = raw10543step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10543step0 raw10543step0Labels permutation56 hz
    mixedMoment B raw10543step1 raw10543step1Labels = mixedMoment B raw10543step2 raw10543step2Labels := by
      have ha : raw10543step2 = (fun i j => raw10543step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10543step2 raw10543step1; decide +kernel
      have hl : raw10543step2Labels = raw10543step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10543step1 raw10543step1Labels permutation8 permutation7
    mixedMoment B raw10543step2 raw10543step2Labels = mixedMoment B raw10543step3 raw10543step3Labels := by
      have ha : raw10543step3 = -raw10543step2 := by apply Matrix.ext; change ∀ i j, raw10543step3 i j = -(raw10543step2 i j); unfold raw10543step3 raw10543step2; decide +kernel
      have hl : raw10543step3Labels = raw10543step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10543step3 raw10543step3Labels = mixedMoment B raw10543step4 raw10543step4Labels := by
      have ha : raw10543step4 = raw10543step3 := by apply Matrix.ext; unfold raw10543step4 raw10543step3; decide +kernel
      have hl : raw10543step3Labels = labelEmbedding10 ∘ raw10543step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10543step3 raw10543step3Labels raw10543step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5442 node5442Labels := by rfl

theorem canonical10544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10544 raw10544Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw10544 raw10544Labels = mixedMoment B raw10544step0 raw10544step0Labels := by
      have hz : ∀ j, raw10544 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10544step0 = (fun i j => raw10544 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10544step0 raw10544; decide +kernel
      have hl : raw10544step0Labels = raw10544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10544 raw10544Labels permutation346 hz
    mixedMoment B raw10544step0 raw10544step0Labels = mixedMoment B raw10544step1 raw10544step1Labels := by
      have ha : raw10544step1 = (fun i j => raw10544step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10544step1 raw10544step0; decide +kernel
      have hl : raw10544step1Labels = raw10544step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10544step0 raw10544step0Labels permutation38 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical10545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10545 raw10545Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw10545 raw10545Labels = mixedMoment B raw10545step0 raw10545step0Labels := by
      have ha : raw10545step0 = (fun i j => raw10545 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10545step0 raw10545; decide +kernel
      have hl : raw10545step0Labels = raw10545Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10545 raw10545Labels permutation182 permutation2
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical10546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10546 raw10546Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw10546 raw10546Labels = mixedMoment B raw10546step0 raw10546step0Labels := by
      have hz : ∀ j, raw10546 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10546step0 = (fun i j => raw10546 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10546step0 raw10546; decide +kernel
      have hl : raw10546step0Labels = raw10546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10546 raw10546Labels permutation346 hz
    mixedMoment B raw10546step0 raw10546step0Labels = mixedMoment B raw10546step1 raw10546step1Labels := by
      have ha : raw10546step1 = (fun i j => raw10546step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10546step1 raw10546step0; decide +kernel
      have hl : raw10546step1Labels = raw10546step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10546step0 raw10546step0Labels permutation38 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

theorem canonical10547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10547 raw10547Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw10547 raw10547Labels = mixedMoment B raw10547step0 raw10547step0Labels := by
      have hz : ∀ j, raw10547 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10547step0 = (fun i j => raw10547 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10547step0 raw10547; decide +kernel
      have hl : raw10547step0Labels = raw10547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10547 raw10547Labels permutation346 hz
    mixedMoment B raw10547step0 raw10547step0Labels = mixedMoment B raw10547step1 raw10547step1Labels := by
      have ha : raw10547step1 = (fun i j => raw10547step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10547step1 raw10547step0; decide +kernel
      have hl : raw10547step1Labels = raw10547step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10547step0 raw10547step0Labels permutation40 permutation2
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical10548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10548 raw10548Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw10548 raw10548Labels = mixedMoment B raw10548step0 raw10548step0Labels := by
      have hz : ∀ j, raw10548 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10548step0 = (fun i j => raw10548 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10548step0 raw10548; decide +kernel
      have hl : raw10548step0Labels = raw10548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10548 raw10548Labels permutation346 hz
    mixedMoment B raw10548step0 raw10548step0Labels = mixedMoment B raw10548step1 raw10548step1Labels := by
      have ha : raw10548step1 = (fun i j => raw10548step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10548step1 raw10548step0; decide +kernel
      have hl : raw10548step1Labels = raw10548step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10548step0 raw10548step0Labels permutation38 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical10549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10549 raw10549Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw10549 raw10549Labels = mixedMoment B raw10549step0 raw10549step0Labels := by
      have hz : ∀ j, raw10549 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10549step0 = (fun i j => raw10549 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10549step0 raw10549; decide +kernel
      have hl : raw10549step0Labels = raw10549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10549 raw10549Labels permutation265 hz
    mixedMoment B raw10549step0 raw10549step0Labels = mixedMoment B raw10549step1 raw10549step1Labels := by
      have ha : raw10549step1 = (fun i j => raw10549step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10549step1 raw10549step0; decide +kernel
      have hl : raw10549step1Labels = raw10549step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10549step0 raw10549step0Labels permutation38 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical10550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10550 raw10550Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw10550 raw10550Labels = mixedMoment B raw10550step0 raw10550step0Labels := by
      have ha : raw10550step0 = (fun i j => raw10550 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10550step0 raw10550; decide +kernel
      have hl : raw10550step0Labels = raw10550Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10550 raw10550Labels permutation158 permutation2
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical10551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10551 raw10551Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw10551 raw10551Labels = mixedMoment B raw10551step0 raw10551step0Labels := by
      have hz : ∀ j, raw10551 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10551step0 = (fun i j => raw10551 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10551step0 raw10551; decide +kernel
      have hl : raw10551step0Labels = raw10551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10551 raw10551Labels permutation265 hz
    mixedMoment B raw10551step0 raw10551step0Labels = mixedMoment B raw10551step1 raw10551step1Labels := by
      have ha : raw10551step1 = (fun i j => raw10551step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10551step1 raw10551step0; decide +kernel
      have hl : raw10551step1Labels = raw10551step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10551step0 raw10551step0Labels permutation38 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

theorem canonical10552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10552 raw10552Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw10552 raw10552Labels = mixedMoment B raw10552step0 raw10552step0Labels := by
      have hz : ∀ j, raw10552 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10552step0 = (fun i j => raw10552 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10552step0 raw10552; decide +kernel
      have hl : raw10552step0Labels = raw10552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10552 raw10552Labels permutation265 hz
    mixedMoment B raw10552step0 raw10552step0Labels = mixedMoment B raw10552step1 raw10552step1Labels := by
      have ha : raw10552step1 = (fun i j => raw10552step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10552step1 raw10552step0; decide +kernel
      have hl : raw10552step1Labels = raw10552step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10552step0 raw10552step0Labels permutation40 permutation2
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical10553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10553 raw10553Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw10553 raw10553Labels = mixedMoment B raw10553step0 raw10553step0Labels := by
      have hz : ∀ j, raw10553 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10553step0 = (fun i j => raw10553 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10553step0 raw10553; decide +kernel
      have hl : raw10553step0Labels = raw10553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10553 raw10553Labels permutation265 hz
    mixedMoment B raw10553step0 raw10553step0Labels = mixedMoment B raw10553step1 raw10553step1Labels := by
      have ha : raw10553step1 = (fun i j => raw10553step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10553step1 raw10553step0; decide +kernel
      have hl : raw10553step1Labels = raw10553step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10553step0 raw10553step0Labels permutation38 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical10554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10554 raw10554Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw10554 raw10554Labels = mixedMoment B raw10554step0 raw10554step0Labels := by
      have hz : ∀ j, raw10554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10554step0 = (fun i j => raw10554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10554step0 raw10554; decide +kernel
      have hl : raw10554step0Labels = raw10554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10554 raw10554Labels permutation346 hz
    mixedMoment B raw10554step0 raw10554step0Labels = mixedMoment B raw10554step1 raw10554step1Labels := by
      have hz : ∀ j, raw10554step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10554step1 = (fun i j => raw10554step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10554step1 raw10554step0; decide +kernel
      have hl : raw10554step1Labels = raw10554step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10554step0 raw10554step0Labels permutation56 hz
    _ = mixedMoment B node4619 node4619Labels := by rfl

theorem canonical10555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10555 raw10555Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw10555 raw10555Labels = mixedMoment B raw10555step0 raw10555step0Labels := by
      have hz : ∀ j, raw10555 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10555step0 = (fun i j => raw10555 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10555step0 raw10555; decide +kernel
      have hl : raw10555step0Labels = raw10555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10555 raw10555Labels permutation346 hz
    _ = mixedMoment B node5163 node5163Labels := by rfl

theorem canonical10556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10556 raw10556Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw10556 raw10556Labels = mixedMoment B raw10556step0 raw10556step0Labels := by
      have hz : ∀ j, raw10556 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10556step0 = (fun i j => raw10556 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10556step0 raw10556; decide +kernel
      have hl : raw10556step0Labels = raw10556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10556 raw10556Labels permutation265 hz
    _ = mixedMoment B node5163 node5163Labels := by rfl

theorem canonical10557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10557 raw10557Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw10557 raw10557Labels = mixedMoment B raw10557step0 raw10557step0Labels := by
      have hz : ∀ j, raw10557 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10557step0 = (fun i j => raw10557 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10557step0 raw10557; decide +kernel
      have hl : raw10557step0Labels = raw10557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10557 raw10557Labels permutation346 hz
    mixedMoment B raw10557step0 raw10557step0Labels = mixedMoment B raw10557step1 raw10557step1Labels := by
      have hz : ∀ j, raw10557step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10557step1 = (fun i j => raw10557step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10557step1 raw10557step0; decide +kernel
      have hl : raw10557step1Labels = raw10557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10557step0 raw10557step0Labels permutation56 hz
    mixedMoment B raw10557step1 raw10557step1Labels = mixedMoment B raw10557step2 raw10557step2Labels := by
      have ha : raw10557step2 = (fun i j => raw10557step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10557step2 raw10557step1; decide +kernel
      have hl : raw10557step2Labels = raw10557step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10557step1 raw10557step1Labels permutation10 permutation2
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical10558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10558 raw10558Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw10558 raw10558Labels = mixedMoment B raw10558step0 raw10558step0Labels := by
      have hz : ∀ j, raw10558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10558step0 = (fun i j => raw10558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10558step0 raw10558; decide +kernel
      have hl : raw10558step0Labels = raw10558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10558 raw10558Labels permutation346 hz
    mixedMoment B raw10558step0 raw10558step0Labels = mixedMoment B raw10558step1 raw10558step1Labels := by
      have hz : ∀ j, raw10558step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10558step1 = (fun i j => raw10558step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10558step1 raw10558step0; decide +kernel
      have hl : raw10558step1Labels = raw10558step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10558step0 raw10558step0Labels permutation56 hz
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical10559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10559 raw10559Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw10559 raw10559Labels = mixedMoment B raw10559step0 raw10559step0Labels := by
      have hz : ∀ j, raw10559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10559step0 = (fun i j => raw10559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10559step0 raw10559; decide +kernel
      have hl : raw10559step0Labels = raw10559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10559 raw10559Labels permutation346 hz
    mixedMoment B raw10559step0 raw10559step0Labels = mixedMoment B raw10559step1 raw10559step1Labels := by
      have hz : ∀ j, raw10559step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10559step1 = (fun i j => raw10559step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10559step1 raw10559step0; decide +kernel
      have hl : raw10559step1Labels = raw10559step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10559step0 raw10559step0Labels permutation56 hz
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical10560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10560 raw10560Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw10560 raw10560Labels = mixedMoment B raw10560step0 raw10560step0Labels := by
      have hz : ∀ j, raw10560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10560step0 = (fun i j => raw10560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10560step0 raw10560; decide +kernel
      have hl : raw10560step0Labels = raw10560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10560 raw10560Labels permutation346 hz
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical10561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10561 raw10561Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw10561 raw10561Labels = mixedMoment B raw10561step0 raw10561step0Labels := by
      have hz : ∀ j, raw10561 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10561step0 = (fun i j => raw10561 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10561step0 raw10561; decide +kernel
      have hl : raw10561step0Labels = raw10561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10561 raw10561Labels permutation265 hz
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical10562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10562 raw10562Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw10562 raw10562Labels = mixedMoment B raw10562step0 raw10562step0Labels := by
      have hz : ∀ j, raw10562 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10562step0 = (fun i j => raw10562 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10562step0 raw10562; decide +kernel
      have hl : raw10562step0Labels = raw10562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10562 raw10562Labels permutation346 hz
    mixedMoment B raw10562step0 raw10562step0Labels = mixedMoment B raw10562step1 raw10562step1Labels := by
      have hz : ∀ j, raw10562step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10562step1 = (fun i j => raw10562step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10562step1 raw10562step0; decide +kernel
      have hl : raw10562step1Labels = raw10562step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10562step0 raw10562step0Labels permutation56 hz
    _ = mixedMoment B node5111 node5111Labels := by rfl

theorem canonical10563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10563 raw10563Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw10563 raw10563Labels = mixedMoment B raw10563step0 raw10563step0Labels := by
      have hz : ∀ j, raw10563 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10563step0 = (fun i j => raw10563 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10563step0 raw10563; decide +kernel
      have hl : raw10563step0Labels = raw10563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10563 raw10563Labels permutation346 hz
    mixedMoment B raw10563step0 raw10563step0Labels = mixedMoment B raw10563step1 raw10563step1Labels := by
      have hz : ∀ j, raw10563step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10563step1 = (fun i j => raw10563step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10563step1 raw10563step0; decide +kernel
      have hl : raw10563step1Labels = raw10563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10563step0 raw10563step0Labels permutation56 hz
    mixedMoment B raw10563step1 raw10563step1Labels = mixedMoment B raw10563step2 raw10563step2Labels := by
      have ha : raw10563step2 = (fun i j => raw10563step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10563step2 raw10563step1; decide +kernel
      have hl : raw10563step2Labels = raw10563step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10563step1 raw10563step1Labels permutation9 permutation2
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical10564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10564 raw10564Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw10564 raw10564Labels = mixedMoment B raw10564step0 raw10564step0Labels := by
      have hz : ∀ j, raw10564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10564step0 = (fun i j => raw10564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10564step0 raw10564; decide +kernel
      have hl : raw10564step0Labels = raw10564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10564 raw10564Labels permutation346 hz
    mixedMoment B raw10564step0 raw10564step0Labels = mixedMoment B raw10564step1 raw10564step1Labels := by
      have hz : ∀ j, raw10564step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10564step1 = (fun i j => raw10564step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10564step1 raw10564step0; decide +kernel
      have hl : raw10564step1Labels = raw10564step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10564step0 raw10564step0Labels permutation56 hz
    _ = mixedMoment B node4608 node4608Labels := by rfl

theorem canonical10565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10565 raw10565Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw10565 raw10565Labels = mixedMoment B raw10565step0 raw10565step0Labels := by
      have hz : ∀ j, raw10565 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10565step0 = (fun i j => raw10565 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10565step0 raw10565; decide +kernel
      have hl : raw10565step0Labels = raw10565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10565 raw10565Labels permutation346 hz
    mixedMoment B raw10565step0 raw10565step0Labels = mixedMoment B raw10565step1 raw10565step1Labels := by
      have ha : raw10565step1 = (fun i j => raw10565step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10565step1 raw10565step0; decide +kernel
      have hl : raw10565step1Labels = raw10565step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10565step0 raw10565step0Labels permutation151 permutation2
    mixedMoment B raw10565step1 raw10565step1Labels = mixedMoment B raw10565step2 raw10565step2Labels := by
      have ha : raw10565step2 = -raw10565step1 := by apply Matrix.ext; change ∀ i j, raw10565step2 i j = -(raw10565step1 i j); unfold raw10565step2 raw10565step1; decide +kernel
      have hl : raw10565step2Labels = raw10565step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5075 node5075Labels := by rfl

theorem canonical10566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10566 raw10566Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw10566 raw10566Labels = mixedMoment B raw10566step0 raw10566step0Labels := by
      have hz : ∀ j, raw10566 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10566step0 = (fun i j => raw10566 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10566step0 raw10566; decide +kernel
      have hl : raw10566step0Labels = raw10566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10566 raw10566Labels permutation265 hz
    mixedMoment B raw10566step0 raw10566step0Labels = mixedMoment B raw10566step1 raw10566step1Labels := by
      have ha : raw10566step1 = (fun i j => raw10566step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10566step1 raw10566step0; decide +kernel
      have hl : raw10566step1Labels = raw10566step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10566step0 raw10566step0Labels permutation151 permutation2
    mixedMoment B raw10566step1 raw10566step1Labels = mixedMoment B raw10566step2 raw10566step2Labels := by
      have ha : raw10566step2 = -raw10566step1 := by apply Matrix.ext; change ∀ i j, raw10566step2 i j = -(raw10566step1 i j); unfold raw10566step2 raw10566step1; decide +kernel
      have hl : raw10566step2Labels = raw10566step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5075 node5075Labels := by rfl

theorem canonical10567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10567 raw10567Labels = mixedMoment B node5107 node5107Labels := by
  calc
    mixedMoment B raw10567 raw10567Labels = mixedMoment B raw10567step0 raw10567step0Labels := by
      have hz : ∀ j, raw10567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10567step0 = (fun i j => raw10567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10567step0 raw10567; decide +kernel
      have hl : raw10567step0Labels = raw10567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10567 raw10567Labels permutation346 hz
    mixedMoment B raw10567step0 raw10567step0Labels = mixedMoment B raw10567step1 raw10567step1Labels := by
      have hz : ∀ j, raw10567step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10567step1 = (fun i j => raw10567step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10567step1 raw10567step0; decide +kernel
      have hl : raw10567step1Labels = raw10567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10567step0 raw10567step0Labels permutation56 hz
    _ = mixedMoment B node5107 node5107Labels := by rfl

theorem canonical10568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10568 raw10568Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw10568 raw10568Labels = mixedMoment B raw10568step0 raw10568step0Labels := by
      have hz : ∀ j, raw10568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10568step0 = (fun i j => raw10568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10568step0 raw10568; decide +kernel
      have hl : raw10568step0Labels = raw10568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10568 raw10568Labels permutation346 hz
    mixedMoment B raw10568step0 raw10568step0Labels = mixedMoment B raw10568step1 raw10568step1Labels := by
      have hz : ∀ j, raw10568step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10568step1 = (fun i j => raw10568step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10568step1 raw10568step0; decide +kernel
      have hl : raw10568step1Labels = raw10568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10568step0 raw10568step0Labels permutation56 hz
    _ = mixedMoment B node5261 node5261Labels := by rfl

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

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ac_rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem singleton4619 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4619 node4619Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1294 node1294Labels + mixedMoment B node3305 node3305Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1443 singletonSmall4619
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4619) = raw1443Labels := by decide +kernel
  rw [hl, canonical1443 B hB] at h
  have hc0 : mixedMoment B raw1443 (Fin.cases (0 : Fin 2) singletonSmall4619) =
      mixedMoment B node1294 node1294Labels := by
    have ha : raw1443 = raw1444 := by apply Matrix.ext; unfold raw1443 raw1444; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4619 = raw1444Labels := by decide +kernel
    rw [ha, hj, canonical1444 B hB]
  have hc1 : mixedMoment B raw1443 (Fin.cases (1 : Fin 2) singletonSmall4619) =
      mixedMoment B node3305 node3305Labels := by
    have ha : raw1443 = raw1445 := by apply Matrix.ext; unfold raw1443 raw1445; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4619 = raw1445Labels := by decide +kernel
    rw [ha, hj, canonical1445 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5075 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5075 node5075Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2482 node2482Labels + mixedMoment B node3468 node3468Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2097 singletonSmall5075
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5075) = raw2097Labels := by decide +kernel
  rw [hl, canonical2097 B hB] at h
  have hc0 : mixedMoment B raw2097 (Fin.cases (0 : Fin 2) singletonSmall5075) =
      mixedMoment B node2482 node2482Labels := by
    have ha : raw2097 = raw2098 := by apply Matrix.ext; unfold raw2097 raw2098; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5075 = raw2098Labels := by decide +kernel
    rw [ha, hj, canonical2098 B hB]
  have hc1 : mixedMoment B raw2097 (Fin.cases (1 : Fin 2) singletonSmall5075) =
      mixedMoment B node3468 node3468Labels := by
    have ha : raw2097 = raw2099 := by apply Matrix.ext; unfold raw2097 raw2099; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5075 = raw2099Labels := by decide +kernel
    rw [ha, hj, canonical2099 B hB]
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

theorem singleton5134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5134 node5134Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2553 node2553Labels + mixedMoment B node3514 node3514Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2163 singletonSmall5134
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5134) = raw2163Labels := by decide +kernel
  rw [hl, canonical2163 B hB] at h
  have hc0 : mixedMoment B raw2163 (Fin.cases (0 : Fin 2) singletonSmall5134) =
      mixedMoment B node2553 node2553Labels := by
    have ha : raw2163 = raw2164 := by apply Matrix.ext; unfold raw2163 raw2164; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5134 = raw2164Labels := by decide +kernel
    rw [ha, hj, canonical2164 B hB]
  have hc1 : mixedMoment B raw2163 (Fin.cases (1 : Fin 2) singletonSmall5134) =
      mixedMoment B node3514 node3514Labels := by
    have ha : raw2163 = raw2165 := by apply Matrix.ext; unfold raw2163 raw2165; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5134 = raw2165Labels := by decide +kernel
    rw [ha, hj, canonical2165 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5141 node5141Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2561 node2561Labels + mixedMoment B node3522 node3522Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2169 singletonSmall5141
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5141) = raw2169Labels := by decide +kernel
  rw [hl, canonical2169 B hB] at h
  have hc0 : mixedMoment B raw2169 (Fin.cases (0 : Fin 2) singletonSmall5141) =
      mixedMoment B node2561 node2561Labels := by
    have ha : raw2169 = raw2170 := by apply Matrix.ext; unfold raw2169 raw2170; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5141 = raw2170Labels := by decide +kernel
    rw [ha, hj, canonical2170 B hB]
  have hc1 : mixedMoment B raw2169 (Fin.cases (1 : Fin 2) singletonSmall5141) =
      mixedMoment B node3522 node3522Labels := by
    have ha : raw2169 = raw2171 := by apply Matrix.ext; unfold raw2169 raw2171; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5141 = raw2171Labels := by decide +kernel
    rw [ha, hj, canonical2171 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5163 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5163 node5163Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2590 node2590Labels + mixedMoment B node3564 node3564Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2190 singletonSmall5163
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5163) = raw2190Labels := by decide +kernel
  rw [hl, canonical2190 B hB] at h
  have hc0 : mixedMoment B raw2190 (Fin.cases (0 : Fin 2) singletonSmall5163) =
      mixedMoment B node2590 node2590Labels := by
    have ha : raw2190 = raw2191 := by apply Matrix.ext; unfold raw2190 raw2191; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5163 = raw2191Labels := by decide +kernel
    rw [ha, hj, canonical2191 B hB]
  have hc1 : mixedMoment B raw2190 (Fin.cases (1 : Fin 2) singletonSmall5163) =
      mixedMoment B node3564 node3564Labels := by
    have ha : raw2190 = raw2192 := by apply Matrix.ext; unfold raw2190 raw2192; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5163 = raw2192Labels := by decide +kernel
    rw [ha, hj, canonical2192 B hB]
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

theorem singleton5258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5258 node5258Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2722 node2722Labels + mixedMoment B node3533 node3533Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2271 singletonSmall5258
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5258) = raw2271Labels := by decide +kernel
  rw [hl, canonical2271 B hB] at h
  have hc0 : mixedMoment B raw2271 (Fin.cases (0 : Fin 2) singletonSmall5258) =
      mixedMoment B node2722 node2722Labels := by
    have ha : raw2271 = raw2272 := by apply Matrix.ext; unfold raw2271 raw2272; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5258 = raw2272Labels := by decide +kernel
    rw [ha, hj, canonical2272 B hB]
  have hc1 : mixedMoment B raw2271 (Fin.cases (1 : Fin 2) singletonSmall5258) =
      mixedMoment B node3533 node3533Labels := by
    have ha : raw2271 = raw2273 := by apply Matrix.ext; unfold raw2271 raw2273; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5258 = raw2273Labels := by decide +kernel
    rw [ha, hj, canonical2273 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5261 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5261 node5261Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2726 node2726Labels + mixedMoment B node3545 node3545Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2277 singletonSmall5261
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5261) = raw2277Labels := by decide +kernel
  rw [hl, canonical2277 B hB] at h
  have hc0 : mixedMoment B raw2277 (Fin.cases (0 : Fin 2) singletonSmall5261) =
      mixedMoment B node2726 node2726Labels := by
    have ha : raw2277 = raw2278 := by apply Matrix.ext; unfold raw2277 raw2278; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5261 = raw2278Labels := by decide +kernel
    rw [ha, hj, canonical2278 B hB]
  have hc1 : mixedMoment B raw2277 (Fin.cases (1 : Fin 2) singletonSmall5261) =
      mixedMoment B node3545 node3545Labels := by
    have ha : raw2277 = raw2279 := by apply Matrix.ext; unfold raw2277 raw2279; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5261 = raw2279Labels := by decide +kernel
    rw [ha, hj, canonical2279 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5271 node5271Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2739 node2739Labels + mixedMoment B node3534 node3534Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2280 singletonSmall5271
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5271) = raw2280Labels := by decide +kernel
  rw [hl, canonical2280 B hB] at h
  have hc0 : mixedMoment B raw2280 (Fin.cases (0 : Fin 2) singletonSmall5271) =
      mixedMoment B node2739 node2739Labels := by
    have ha : raw2280 = raw2281 := by apply Matrix.ext; unfold raw2280 raw2281; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5271 = raw2281Labels := by decide +kernel
    rw [ha, hj, canonical2281 B hB]
  have hc1 : mixedMoment B raw2280 (Fin.cases (1 : Fin 2) singletonSmall5271) =
      mixedMoment B node3534 node3534Labels := by
    have ha : raw2280 = raw2282 := by apply Matrix.ext; unfold raw2280 raw2282; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5271 = raw2282Labels := by decide +kernel
    rw [ha, hj, canonical2282 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5275 node5275Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2743 node2743Labels + mixedMoment B node3548 node3548Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2286 singletonSmall5275
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5275) = raw2286Labels := by decide +kernel
  rw [hl, canonical2286 B hB] at h
  have hc0 : mixedMoment B raw2286 (Fin.cases (0 : Fin 2) singletonSmall5275) =
      mixedMoment B node2743 node2743Labels := by
    have ha : raw2286 = raw2287 := by apply Matrix.ext; unfold raw2286 raw2287; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5275 = raw2287Labels := by decide +kernel
    rw [ha, hj, canonical2287 B hB]
  have hc1 : mixedMoment B raw2286 (Fin.cases (1 : Fin 2) singletonSmall5275) =
      mixedMoment B node3548 node3548Labels := by
    have ha : raw2286 = raw2288 := by apply Matrix.ext; unfold raw2286 raw2288; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5275 = raw2288Labels := by decide +kernel
    rw [ha, hj, canonical2288 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5291 node5291Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2765 node2765Labels + mixedMoment B node3582 node3582Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2295 singletonSmall5291
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5291) = raw2295Labels := by decide +kernel
  rw [hl, canonical2295 B hB] at h
  have hc0 : mixedMoment B raw2295 (Fin.cases (0 : Fin 2) singletonSmall5291) =
      mixedMoment B node2765 node2765Labels := by
    have ha : raw2295 = raw2296 := by apply Matrix.ext; unfold raw2295 raw2296; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5291 = raw2296Labels := by decide +kernel
    rw [ha, hj, canonical2296 B hB]
  have hc1 : mixedMoment B raw2295 (Fin.cases (1 : Fin 2) singletonSmall5291) =
      mixedMoment B node3582 node3582Labels := by
    have ha : raw2295 = raw2297 := by apply Matrix.ext; unfold raw2295 raw2297; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5291 = raw2297Labels := by decide +kernel
    rw [ha, hj, canonical2297 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem zero5442 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5442 node5442Labels = 0 := by
  exact mixedMoment_order_one B hB node5442 node5442Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1236 node1236Labels = Sparse.eval nodeValue1236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1236) = mixedMoment B node1236 node1236Labels := rfl
  simpa [nodeValue1236, Sparse.eval] using hc.symm

theorem sound1242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1242 node1242Labels = Sparse.eval nodeValue1242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1242) = mixedMoment B node1242 node1242Labels := rfl
  simpa [nodeValue1242, Sparse.eval] using hc.symm

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

theorem sound1294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1294 node1294Labels = Sparse.eval nodeValue1294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1294) = mixedMoment B node1294 node1294Labels := rfl
  simpa [nodeValue1294, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2066 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2066 node2066Labels = 0 := by
  exact mixedMoment_order_one B hB node2066 node2066Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

theorem sound2062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2062 node2062Labels = Sparse.eval nodeValue2062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2062) = mixedMoment B node2062 node2062Labels := rfl
  simpa [nodeValue2062, Sparse.eval] using hc.symm

theorem sound2066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2066 node2066Labels = Sparse.eval nodeValue2066 (mixedVector B) := by
  simpa only [nodeValue2066, Sparse.eval_nil] using zero2066 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2293 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2293 node2293Labels = 0 := by
  exact mixedMoment_order_one B hB node2293 node2293Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2293 node2293Labels = Sparse.eval nodeValue2293 (mixedVector B) := by
  simpa only [nodeValue2293, Sparse.eval_nil] using zero2293 B _hB _hF

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

theorem sound2482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2482 node2482Labels = Sparse.eval nodeValue2482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2482) = mixedMoment B node2482 node2482Labels := rfl
  simpa [nodeValue2482, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2523 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2523 node2523Labels = 0 := by
  exact mixedMoment_order_one B hB node2523 node2523Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2554 node2554Labels = 0 := by
  exact mixedMoment_alpha B hF node2554 node2554Labels 1 permutation160
    (by decide +kernel)

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

theorem sound2512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2512 node2512Labels = Sparse.eval nodeValue2512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2512) = mixedMoment B node2512 node2512Labels := rfl
  simpa [nodeValue2512, Sparse.eval] using hc.symm

theorem sound2519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2519 node2519Labels = Sparse.eval nodeValue2519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2519) = mixedMoment B node2519 node2519Labels := rfl
  simpa [nodeValue2519, Sparse.eval] using hc.symm

theorem sound2523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2523 node2523Labels = Sparse.eval nodeValue2523 (mixedVector B) := by
  simpa only [nodeValue2523, Sparse.eval_nil] using zero2523 B _hB _hF

theorem sound2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2553 node2553Labels = Sparse.eval nodeValue2553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2553) = mixedMoment B node2553 node2553Labels := rfl
  simpa [nodeValue2553, Sparse.eval] using hc.symm

theorem sound2554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2554 node2554Labels = Sparse.eval nodeValue2554 (mixedVector B) := by
  simpa only [nodeValue2554, Sparse.eval_nil] using zero2554 B _hB _hF

theorem sound2558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2558 node2558Labels = Sparse.eval nodeValue2558 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2558) = mixedMoment B node2558 node2558Labels := rfl
  simpa [nodeValue2558, Sparse.eval] using hc.symm

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

theorem sound2561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2561 node2561Labels = Sparse.eval nodeValue2561 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2561) = mixedMoment B node2561 node2561Labels := rfl
  simpa [nodeValue2561, Sparse.eval] using hc.symm

theorem sound2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2590 node2590Labels = Sparse.eval nodeValue2590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2590) = mixedMoment B node2590 node2590Labels := rfl
  simpa [nodeValue2590, Sparse.eval] using hc.symm

theorem sound2591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2591 node2591Labels = Sparse.eval nodeValue2591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2591) = mixedMoment B node2591 node2591Labels := rfl
  simpa [nodeValue2591, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2742 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = 0 := by
  exact mixedMoment_order_one B hB node2742 node2742Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2722 node2722Labels = Sparse.eval nodeValue2722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2722) = mixedMoment B node2722 node2722Labels := rfl
  simpa [nodeValue2722, Sparse.eval] using hc.symm

theorem sound2726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2726 node2726Labels = Sparse.eval nodeValue2726 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2726) = mixedMoment B node2726 node2726Labels := rfl
  simpa [nodeValue2726, Sparse.eval] using hc.symm

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

theorem sound2742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = Sparse.eval nodeValue2742 (mixedVector B) := by
  simpa only [nodeValue2742, Sparse.eval_nil] using zero2742 B _hB _hF

theorem sound2743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2743 node2743Labels = Sparse.eval nodeValue2743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2743) = mixedMoment B node2743 node2743Labels := rfl
  simpa [nodeValue2743, Sparse.eval] using hc.symm

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

theorem sound2765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2765 node2765Labels = Sparse.eval nodeValue2765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2765) = mixedMoment B node2765 node2765Labels := rfl
  simpa [nodeValue2765, Sparse.eval] using hc.symm

theorem sound2782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2782 node2782Labels = Sparse.eval nodeValue2782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2782) = mixedMoment B node2782 node2782Labels := rfl
  simpa [nodeValue2782, Sparse.eval] using hc.symm

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

theorem sound3293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3293 node3293Labels = Sparse.eval nodeValue3293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3293) = mixedMoment B node3293 node3293Labels := rfl
  simpa [nodeValue3293, Sparse.eval] using hc.symm

theorem sound3300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3300 node3300Labels = Sparse.eval nodeValue3300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3300) = mixedMoment B node3300 node3300Labels := rfl
  simpa [nodeValue3300, Sparse.eval] using hc.symm

theorem sound3301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3301 node3301Labels = Sparse.eval nodeValue3301 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3301) = mixedMoment B node3301 node3301Labels := rfl
  simpa [nodeValue3301, Sparse.eval] using hc.symm

theorem sound3305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3305 node3305Labels = Sparse.eval nodeValue3305 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3305) = mixedMoment B node3305 node3305Labels := rfl
  simpa [nodeValue3305, Sparse.eval] using hc.symm

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

theorem sound3468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3468 node3468Labels = Sparse.eval nodeValue3468 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3468) = mixedMoment B node3468 node3468Labels := rfl
  simpa [nodeValue3468, Sparse.eval] using hc.symm

theorem sound3514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3514 node3514Labels = Sparse.eval nodeValue3514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3514) = mixedMoment B node3514 node3514Labels := rfl
  simpa [nodeValue3514, Sparse.eval] using hc.symm

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

theorem sound3522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3522 node3522Labels = Sparse.eval nodeValue3522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3522) = mixedMoment B node3522 node3522Labels := rfl
  simpa [nodeValue3522, Sparse.eval] using hc.symm

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

theorem sound3545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3545 node3545Labels = Sparse.eval nodeValue3545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3545) = mixedMoment B node3545 node3545Labels := rfl
  simpa [nodeValue3545, Sparse.eval] using hc.symm

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

theorem sound3564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3564 node3564Labels = Sparse.eval nodeValue3564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3564) = mixedMoment B node3564 node3564Labels := rfl
  simpa [nodeValue3564, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3817 node3817Labels = 0 := by
  exact mixedMoment_order_one B hB node3817 node3817Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3817 node3817Labels = Sparse.eval nodeValue3817 (mixedVector B) := by
  simpa only [nodeValue3817, Sparse.eval_nil] using zero3817 B _hB _hF

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

theorem sound3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3845 node3845Labels = Sparse.eval nodeValue3845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3845) = mixedMoment B node3845 node3845Labels := rfl
  simpa [nodeValue3845, Sparse.eval] using hc.symm

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

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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

theorem sound4602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4602 node4602Labels = Sparse.eval nodeValue4602 (mixedVector B) := by
  have h := singleton4602 B _hB
  rw [sound1236 B _hB _hF, sound3293 B _hB _hF] at h
  norm_num [nodeValue4602, nodeValue1236, nodeValue3293, Sparse.eval] at h ⊢
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

theorem sound4612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4612 node4612Labels = Sparse.eval nodeValue4612 (mixedVector B) := by
  have h := singleton4612 B _hB
  rw [sound1246 B _hB _hF, sound3301 B _hB _hF] at h
  norm_num [nodeValue4612, nodeValue1246, nodeValue3301, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4619 node4619Labels = Sparse.eval nodeValue4619 (mixedVector B) := by
  have h := singleton4619 B _hB
  rw [sound1294 B _hB _hF, sound3305 B _hB _hF] at h
  norm_num [nodeValue4619, nodeValue1294, nodeValue3305, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5101 node5101Labels = 0 := by
  exact mixedMoment_order_one B hB node5101 node5101Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5107 node5107Labels = 0 := by
  exact mixedMoment_order_one B hB node5107 node5107Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5111 node5111Labels = 0 := by
  exact mixedMoment_order_one B hB node5111 node5111Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5075 node5075Labels = Sparse.eval nodeValue5075 (mixedVector B) := by
  have h := singleton5075 B _hB
  rw [sound2482 B _hB _hF, sound3468 B _hB _hF] at h
  norm_num [nodeValue5075, nodeValue2482, nodeValue3468, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5101 node5101Labels = Sparse.eval nodeValue5101 (mixedVector B) := by
  simpa only [nodeValue5101, Sparse.eval_nil] using zero5101 B _hB _hF

theorem sound5107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5107 node5107Labels = Sparse.eval nodeValue5107 (mixedVector B) := by
  simpa only [nodeValue5107, Sparse.eval_nil] using zero5107 B _hB _hF

theorem sound5111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5111 node5111Labels = Sparse.eval nodeValue5111 (mixedVector B) := by
  simpa only [nodeValue5111, Sparse.eval_nil] using zero5111 B _hB _hF

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

theorem sound5134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5134 node5134Labels = Sparse.eval nodeValue5134 (mixedVector B) := by
  have h := singleton5134 B _hB
  rw [sound2553 B _hB _hF, sound3514 B _hB _hF] at h
  norm_num [nodeValue5134, nodeValue2553, nodeValue3514, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5141 node5141Labels = Sparse.eval nodeValue5141 (mixedVector B) := by
  have h := singleton5141 B _hB
  rw [sound2561 B _hB _hF, sound3522 B _hB _hF] at h
  norm_num [nodeValue5141, nodeValue2561, nodeValue3522, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5163 node5163Labels = Sparse.eval nodeValue5163 (mixedVector B) := by
  have h := singleton5163 B _hB
  rw [sound2590 B _hB _hF, sound3564 B _hB _hF] at h
  norm_num [nodeValue5163, nodeValue2590, nodeValue3564, Sparse.eval] at h ⊢
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

theorem sound5258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5258 node5258Labels = Sparse.eval nodeValue5258 (mixedVector B) := by
  have h := singleton5258 B _hB
  rw [sound2722 B _hB _hF, sound3533 B _hB _hF] at h
  norm_num [nodeValue5258, nodeValue2722, nodeValue3533, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5261 node5261Labels = Sparse.eval nodeValue5261 (mixedVector B) := by
  have h := singleton5261 B _hB
  rw [sound2726 B _hB _hF, sound3545 B _hB _hF] at h
  norm_num [nodeValue5261, nodeValue2726, nodeValue3545, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5271 node5271Labels = Sparse.eval nodeValue5271 (mixedVector B) := by
  have h := singleton5271 B _hB
  rw [sound2739 B _hB _hF, sound3534 B _hB _hF] at h
  norm_num [nodeValue5271, nodeValue2739, nodeValue3534, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5275 node5275Labels = Sparse.eval nodeValue5275 (mixedVector B) := by
  have h := singleton5275 B _hB
  rw [sound2743 B _hB _hF, sound3548 B _hB _hF] at h
  norm_num [nodeValue5275, nodeValue2743, nodeValue3548, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5291 node5291Labels = Sparse.eval nodeValue5291 (mixedVector B) := by
  have h := singleton5291 B _hB
  rw [sound2765 B _hB _hF, sound3582 B _hB _hF] at h
  norm_num [nodeValue5291, nodeValue2765, nodeValue3582, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5304 node5304Labels = Sparse.eval nodeValue5304 (mixedVector B) := by
  have h := singleton5304 B _hB
  rw [sound2782 B _hB _hF, sound3583 B _hB _hF] at h
  norm_num [nodeValue5304, nodeValue2782, nodeValue3583, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5409 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5409 node5409Labels = 0 := by
  exact mixedMoment_order_one B hB node5409 node5409Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5409 node5409Labels = Sparse.eval nodeValue5409 (mixedVector B) := by
  simpa only [nodeValue5409, Sparse.eval_nil] using zero5409 B _hB _hF

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

theorem sound5442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5442 node5442Labels = Sparse.eval nodeValue5442 (mixedVector B) := by
  simpa only [nodeValue5442, Sparse.eval_nil] using zero5442 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources19
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq619 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm619 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA619 + difference 0 1) (sourceB619 + difference 1 0) sourceC619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA619 + difference 0 1) (sourceB619 + difference 1 0) sourceC619) = raw10433 := by
      apply Matrix.ext; unfold tripleCharges sourceA619 sourceB619 sourceC619 difference raw10433; decide +kernel
    rw [ha]
    exact (canonical10433 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA619 + difference 1 1) (sourceB619 + difference 1 1) sourceC619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA619 + difference 1 1) (sourceB619 + difference 1 1) sourceC619) = raw10432 := by
      apply Matrix.ext; unfold tripleCharges sourceA619 sourceB619 sourceC619 difference raw10432; decide +kernel
    rw [ha]
    exact (canonical10432 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA619 + difference 2 1) (sourceB619 + difference 1 2) sourceC619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2554) := by
    have ha : (tripleCharges (sourceA619 + difference 2 1) (sourceB619 + difference 1 2) sourceC619) = raw10439 := by
      apply Matrix.ext; unfold tripleCharges sourceA619 sourceB619 sourceC619 difference raw10439; decide +kernel
    rw [ha]
    exact (canonical10439 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA619 + difference 3 1) (sourceB619 + difference 1 3) sourceC619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2591) := by
    have ha : (tripleCharges (sourceA619 + difference 3 1) (sourceB619 + difference 1 3) sourceC619) = raw10440 := by
      apply Matrix.ext; unfold tripleCharges sourceA619 sourceB619 sourceC619 difference raw10440; decide +kernel
    rw [ha]
    exact (canonical10440 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA619 + difference 4 1) (sourceB619 + difference 1 4) sourceC619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA619 + difference 4 1) (sourceB619 + difference 1 4) sourceC619) = raw10441 := by
      apply Matrix.ext; unfold tripleCharges sourceA619 sourceB619 sourceC619 difference raw10441; decide +kernel
    rw [ha]
    exact (canonical10441 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA619 + difference 5 1) (sourceB619 + difference 1 5) sourceC619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA619 + difference 5 1) (sourceB619 + difference 1 5) sourceC619) = raw10442 := by
      apply Matrix.ext; unfold tripleCharges sourceA619 sourceB619 sourceC619 difference raw10442; decide +kernel
    rw [ha]
    exact (canonical10442 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA619 + sourceB619) sourceC619) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA619 + sourceB619) sourceC619) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA619 sourceB619 sourceC619 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA619 sourceB619 sourceC619
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm619, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq620 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm620 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA620 + difference 0 3) (sourceB620 + difference 3 0) sourceC620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA620 + difference 0 3) (sourceB620 + difference 3 0) sourceC620) = raw10435 := by
      apply Matrix.ext; unfold tripleCharges sourceA620 sourceB620 sourceC620 difference raw10435; decide +kernel
    rw [ha]
    exact (canonical10435 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA620 + difference 1 3) (sourceB620 + difference 3 1) sourceC620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA620 + difference 1 3) (sourceB620 + difference 3 1) sourceC620) = raw10443 := by
      apply Matrix.ext; unfold tripleCharges sourceA620 sourceB620 sourceC620 difference raw10443; decide +kernel
    rw [ha]
    exact (canonical10443 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA620 + difference 2 3) (sourceB620 + difference 3 2) sourceC620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA620 + difference 2 3) (sourceB620 + difference 3 2) sourceC620) = raw10444 := by
      apply Matrix.ext; unfold tripleCharges sourceA620 sourceB620 sourceC620 difference raw10444; decide +kernel
    rw [ha]
    exact (canonical10444 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA620 + difference 3 3) (sourceB620 + difference 3 3) sourceC620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA620 + difference 3 3) (sourceB620 + difference 3 3) sourceC620) = raw10432 := by
      apply Matrix.ext; unfold tripleCharges sourceA620 sourceB620 sourceC620 difference raw10432; decide +kernel
    rw [ha]
    exact (canonical10432 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA620 + difference 4 3) (sourceB620 + difference 3 4) sourceC620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2523) := by
    have ha : (tripleCharges (sourceA620 + difference 4 3) (sourceB620 + difference 3 4) sourceC620) = raw10445 := by
      apply Matrix.ext; unfold tripleCharges sourceA620 sourceB620 sourceC620 difference raw10445; decide +kernel
    rw [ha]
    exact (canonical10445 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA620 + difference 5 3) (sourceB620 + difference 3 5) sourceC620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA620 + difference 5 3) (sourceB620 + difference 3 5) sourceC620) = raw10446 := by
      apply Matrix.ext; unfold tripleCharges sourceA620 sourceB620 sourceC620 difference raw10446; decide +kernel
    rw [ha]
    exact (canonical10446 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA620 + sourceB620) sourceC620) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA620 + sourceB620) sourceC620) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA620 sourceB620 sourceC620 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA620 sourceB620 sourceC620
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm620, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm621 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA621 + difference 4 0) (sourceB621 + difference 0 4) sourceC621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA621 + difference 4 0) (sourceB621 + difference 0 4) sourceC621) = raw10447 := by
      apply Matrix.ext; unfold tripleCharges sourceA621 sourceB621 sourceC621 difference raw10447; decide +kernel
    rw [ha]
    exact (canonical10447 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA621 + difference 4 1) (sourceB621 + difference 1 4) sourceC621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA621 + difference 4 1) (sourceB621 + difference 1 4) sourceC621) = raw10441 := by
      apply Matrix.ext; unfold tripleCharges sourceA621 sourceB621 sourceC621 difference raw10441; decide +kernel
    rw [ha]
    exact (canonical10441 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA621 + difference 4 2) (sourceB621 + difference 2 4) sourceC621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA621 + difference 4 2) (sourceB621 + difference 2 4) sourceC621) = raw10448 := by
      apply Matrix.ext; unfold tripleCharges sourceA621 sourceB621 sourceC621 difference raw10448; decide +kernel
    rw [ha]
    exact (canonical10448 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA621 + difference 4 3) (sourceB621 + difference 3 4) sourceC621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2523) := by
    have ha : (tripleCharges (sourceA621 + difference 4 3) (sourceB621 + difference 3 4) sourceC621) = raw10445 := by
      apply Matrix.ext; unfold tripleCharges sourceA621 sourceB621 sourceC621 difference raw10445; decide +kernel
    rw [ha]
    exact (canonical10445 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA621 + difference 4 4) (sourceB621 + difference 4 4) sourceC621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA621 + difference 4 4) (sourceB621 + difference 4 4) sourceC621) = raw10432 := by
      apply Matrix.ext; unfold tripleCharges sourceA621 sourceB621 sourceC621 difference raw10432; decide +kernel
    rw [ha]
    exact (canonical10432 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA621 + difference 4 5) (sourceB621 + difference 5 4) sourceC621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA621 + difference 4 5) (sourceB621 + difference 5 4) sourceC621) = raw10449 := by
      apply Matrix.ext; unfold tripleCharges sourceA621 sourceB621 sourceC621 difference raw10449; decide +kernel
    rw [ha]
    exact (canonical10449 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA621 + sourceB621) sourceC621) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA621 + sourceB621) sourceC621) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA621 sourceB621 sourceC621 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA621 sourceB621 sourceC621
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm621, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq626 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm626 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA626 + difference 0 0) (sourceB626 + difference 0 0) sourceC626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA626 + difference 0 0) (sourceB626 + difference 0 0) sourceC626) = raw7700 := by
      apply Matrix.ext; unfold tripleCharges sourceA626 sourceB626 sourceC626 difference raw7700; decide +kernel
    rw [ha]
    exact (canonical7700 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA626 + difference 1 0) (sourceB626 + difference 0 1) sourceC626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA626 + difference 1 0) (sourceB626 + difference 0 1) sourceC626) = raw9967 := by
      apply Matrix.ext; unfold tripleCharges sourceA626 sourceB626 sourceC626 difference raw9967; decide +kernel
    rw [ha]
    exact (canonical9967 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA626 + difference 2 0) (sourceB626 + difference 0 2) sourceC626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA626 + difference 2 0) (sourceB626 + difference 0 2) sourceC626) = raw10536 := by
      apply Matrix.ext; unfold tripleCharges sourceA626 sourceB626 sourceC626 difference raw10536; decide +kernel
    rw [ha]
    exact (canonical10536 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA626 + difference 3 0) (sourceB626 + difference 0 3) sourceC626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA626 + difference 3 0) (sourceB626 + difference 0 3) sourceC626) = raw7698 := by
      apply Matrix.ext; unfold tripleCharges sourceA626 sourceB626 sourceC626 difference raw7698; decide +kernel
    rw [ha]
    exact (canonical7698 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA626 + difference 4 0) (sourceB626 + difference 0 4) sourceC626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA626 + difference 4 0) (sourceB626 + difference 0 4) sourceC626) = raw10537 := by
      apply Matrix.ext; unfold tripleCharges sourceA626 sourceB626 sourceC626 difference raw10537; decide +kernel
    rw [ha]
    exact (canonical10537 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA626 + difference 5 0) (sourceB626 + difference 0 5) sourceC626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2066) := by
    have ha : (tripleCharges (sourceA626 + difference 5 0) (sourceB626 + difference 0 5) sourceC626) = raw10538 := by
      apply Matrix.ext; unfold tripleCharges sourceA626 sourceB626 sourceC626 difference raw10538; decide +kernel
    rw [ha]
    exact (canonical10538 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA626 + sourceB626) sourceC626) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA626 + sourceB626) sourceC626) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA626 sourceB626 sourceC626 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA626 sourceB626 sourceC626
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm626, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq627 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm627 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA627 + difference 0 1) (sourceB627 + difference 1 0) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA627 + difference 0 1) (sourceB627 + difference 1 0) sourceC627) = raw10539 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10539; decide +kernel
    rw [ha]
    exact (canonical10539 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA627 + difference 0 2) (sourceB627 + difference 2 0) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA627 + difference 0 2) (sourceB627 + difference 2 0) sourceC627) = raw10540 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10540; decide +kernel
    rw [ha]
    exact (canonical10540 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA627 + difference 0 3) (sourceB627 + difference 3 0) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA627 + difference 0 3) (sourceB627 + difference 3 0) sourceC627) = raw10541 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10541; decide +kernel
    rw [ha]
    exact (canonical10541 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA627 + difference 0 4) (sourceB627 + difference 4 0) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA627 + difference 0 4) (sourceB627 + difference 4 0) sourceC627) = raw10542 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10542; decide +kernel
    rw [ha]
    exact (canonical10542 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA627 + difference 0 5) (sourceB627 + difference 5 0) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA627 + difference 0 5) (sourceB627 + difference 5 0) sourceC627) = raw10543 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10543; decide +kernel
    rw [ha]
    exact (canonical10543 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA627 + difference 1 0) (sourceB627 + difference 0 1) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA627 + difference 1 0) (sourceB627 + difference 0 1) sourceC627) = raw10544 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10544; decide +kernel
    rw [ha]
    exact (canonical10544 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA627 + difference 1 2) (sourceB627 + difference 2 1) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA627 + difference 1 2) (sourceB627 + difference 2 1) sourceC627) = raw10545 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10545; decide +kernel
    rw [ha]
    exact (canonical10545 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA627 + difference 1 3) (sourceB627 + difference 3 1) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA627 + difference 1 3) (sourceB627 + difference 3 1) sourceC627) = raw10546 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10546; decide +kernel
    rw [ha]
    exact (canonical10546 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA627 + difference 1 4) (sourceB627 + difference 4 1) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA627 + difference 1 4) (sourceB627 + difference 4 1) sourceC627) = raw10547 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10547; decide +kernel
    rw [ha]
    exact (canonical10547 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA627 + difference 1 5) (sourceB627 + difference 5 1) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA627 + difference 1 5) (sourceB627 + difference 5 1) sourceC627) = raw10548 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10548; decide +kernel
    rw [ha]
    exact (canonical10548 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA627 + difference 2 0) (sourceB627 + difference 0 2) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA627 + difference 2 0) (sourceB627 + difference 0 2) sourceC627) = raw10549 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10549; decide +kernel
    rw [ha]
    exact (canonical10549 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA627 + difference 2 1) (sourceB627 + difference 1 2) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA627 + difference 2 1) (sourceB627 + difference 1 2) sourceC627) = raw10550 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10550; decide +kernel
    rw [ha]
    exact (canonical10550 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA627 + difference 2 3) (sourceB627 + difference 3 2) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA627 + difference 2 3) (sourceB627 + difference 3 2) sourceC627) = raw10551 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10551; decide +kernel
    rw [ha]
    exact (canonical10551 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA627 + difference 2 4) (sourceB627 + difference 4 2) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA627 + difference 2 4) (sourceB627 + difference 4 2) sourceC627) = raw10552 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10552; decide +kernel
    rw [ha]
    exact (canonical10552 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA627 + difference 2 5) (sourceB627 + difference 5 2) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA627 + difference 2 5) (sourceB627 + difference 5 2) sourceC627) = raw10553 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10553; decide +kernel
    rw [ha]
    exact (canonical10553 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA627 + difference 3 0) (sourceB627 + difference 0 3) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA627 + difference 3 0) (sourceB627 + difference 0 3) sourceC627) = raw10554 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10554; decide +kernel
    rw [ha]
    exact (canonical10554 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA627 + difference 3 1) (sourceB627 + difference 1 3) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA627 + difference 3 1) (sourceB627 + difference 1 3) sourceC627) = raw10555 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10555; decide +kernel
    rw [ha]
    exact (canonical10555 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA627 + difference 3 2) (sourceB627 + difference 2 3) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA627 + difference 3 2) (sourceB627 + difference 2 3) sourceC627) = raw10556 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10556; decide +kernel
    rw [ha]
    exact (canonical10556 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA627 + difference 3 4) (sourceB627 + difference 4 3) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA627 + difference 3 4) (sourceB627 + difference 4 3) sourceC627) = raw10557 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10557; decide +kernel
    rw [ha]
    exact (canonical10557 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA627 + difference 3 5) (sourceB627 + difference 5 3) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA627 + difference 3 5) (sourceB627 + difference 5 3) sourceC627) = raw10558 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10558; decide +kernel
    rw [ha]
    exact (canonical10558 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA627 + difference 4 0) (sourceB627 + difference 0 4) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA627 + difference 4 0) (sourceB627 + difference 0 4) sourceC627) = raw10559 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10559; decide +kernel
    rw [ha]
    exact (canonical10559 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA627 + difference 4 1) (sourceB627 + difference 1 4) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA627 + difference 4 1) (sourceB627 + difference 1 4) sourceC627) = raw10560 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10560; decide +kernel
    rw [ha]
    exact (canonical10560 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA627 + difference 4 2) (sourceB627 + difference 2 4) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA627 + difference 4 2) (sourceB627 + difference 2 4) sourceC627) = raw10561 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10561; decide +kernel
    rw [ha]
    exact (canonical10561 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA627 + difference 4 3) (sourceB627 + difference 3 4) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA627 + difference 4 3) (sourceB627 + difference 3 4) sourceC627) = raw10562 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10562; decide +kernel
    rw [ha]
    exact (canonical10562 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA627 + difference 4 5) (sourceB627 + difference 5 4) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA627 + difference 4 5) (sourceB627 + difference 5 4) sourceC627) = raw10563 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10563; decide +kernel
    rw [ha]
    exact (canonical10563 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA627 + difference 5 0) (sourceB627 + difference 0 5) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA627 + difference 5 0) (sourceB627 + difference 0 5) sourceC627) = raw10564 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10564; decide +kernel
    rw [ha]
    exact (canonical10564 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA627 + difference 5 1) (sourceB627 + difference 1 5) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA627 + difference 5 1) (sourceB627 + difference 1 5) sourceC627) = raw10565 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10565; decide +kernel
    rw [ha]
    exact (canonical10565 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA627 + difference 5 2) (sourceB627 + difference 2 5) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA627 + difference 5 2) (sourceB627 + difference 2 5) sourceC627) = raw10566 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10566; decide +kernel
    rw [ha]
    exact (canonical10566 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA627 + difference 5 3) (sourceB627 + difference 3 5) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5107) := by
    have ha : (tripleCharges (sourceA627 + difference 5 3) (sourceB627 + difference 3 5) sourceC627) = raw10567 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10567; decide +kernel
    rw [ha]
    exact (canonical10567 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA627 + difference 5 4) (sourceB627 + difference 4 5) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA627 + difference 5 4) (sourceB627 + difference 4 5) sourceC627) = raw10568 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10568; decide +kernel
    rw [ha]
    exact (canonical10568 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA627 sourceB627 sourceC627
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm627, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck528 : Integer.Sparse.reindex keyMap MixedData.row528 = numericRow528 := by decide +kernel

theorem numericCheck528 (x : Master → ℝ) : Integer.Sparse.eval numericRow528 x =
    (1 : ℝ) * reducedSource528 x := by
  norm_num [numericRow528, reducedSource528, Integer.Sparse.eval, Sparse.eval, nodeValue2554, nodeValue2558, nodeValue2561, nodeValue2591, nodeValue2743, nodeValue3845, nodeValue4092]

theorem reindexCheck529 : Integer.Sparse.reindex keyMap MixedData.row529 = numericRow529 := by decide +kernel

theorem numericCheck529 (x : Master → ℝ) : Integer.Sparse.eval numericRow529 x =
    (1 : ℝ) * reducedSource529 x := by
  norm_num [numericRow529, reducedSource529, Integer.Sparse.eval, Sparse.eval, nodeValue2512, nodeValue2519, nodeValue2523, nodeValue2743, nodeValue3817, nodeValue4092]

theorem reindexCheck530 : Integer.Sparse.reindex keyMap MixedData.row530 = numericRow530 := by decide +kernel

theorem numericCheck530 (x : Master → ℝ) : Integer.Sparse.eval numericRow530 x =
    (1 : ℝ) * reducedSource530 x := by
  norm_num [numericRow530, reducedSource530, Integer.Sparse.eval, Sparse.eval, nodeValue1246, nodeValue2523, nodeValue2561, nodeValue2742, nodeValue2743, nodeValue4092]

theorem reindexCheck535 : Integer.Sparse.reindex keyMap MixedData.row535 = numericRow535 := by decide +kernel

theorem numericCheck535 (x : Master → ℝ) : Integer.Sparse.eval numericRow535 x =
    (1 : ℝ) * reducedSource535 x := by
  norm_num [numericRow535, reducedSource535, Integer.Sparse.eval, Sparse.eval, nodeValue2054, nodeValue2062, nodeValue2066, nodeValue2293, nodeValue3548, nodeValue4084]

theorem reindexCheck536 : Integer.Sparse.reindex keyMap MixedData.row536 = numericRow536 := by decide +kernel

theorem numericCheck536 (x : Master → ℝ) : Integer.Sparse.eval numericRow536 x =
    (4 : ℝ) * reducedSource536 x := by
  norm_num [numericRow536, reducedSource536, Integer.Sparse.eval, Sparse.eval, nodeValue4092, nodeValue4602, nodeValue4608, nodeValue4612, nodeValue4619, nodeValue5075, nodeValue5101, nodeValue5107, nodeValue5111, nodeValue5134, nodeValue5141, nodeValue5163, nodeValue5258, nodeValue5261, nodeValue5271, nodeValue5275, nodeValue5291, nodeValue5304, nodeValue5409, nodeValue5441, nodeValue5442]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero528 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource528 (mixedVector B) = 0 := by
  have h2554 : mixedVector B (Sum.inr 2554) = Sparse.eval nodeValue2554 (mixedVector B) := by
    change mixedMoment B node2554 node2554Labels = _
    exact sound2554 B hB hF
  have h2558 : mixedVector B (Sum.inr 2558) = Sparse.eval nodeValue2558 (mixedVector B) := by
    change mixedMoment B node2558 node2558Labels = _
    exact sound2558 B hB hF
  have h2561 : mixedVector B (Sum.inr 2561) = Sparse.eval nodeValue2561 (mixedVector B) := by
    change mixedMoment B node2561 node2561Labels = _
    exact sound2561 B hB hF
  have h2591 : mixedVector B (Sum.inr 2591) = Sparse.eval nodeValue2591 (mixedVector B) := by
    change mixedMoment B node2591 node2591Labels = _
    exact sound2591 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm619, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2554, h2558, h2561, h2591, h2743, h3845, h4092, reducedSource528] using sourceEq619 B hB

theorem rowSound528 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row528 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck528, numericCheck528, reducedZero528 B hB hF, mul_zero]

theorem reducedZero529 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource529 (mixedVector B) = 0 := by
  have h2512 : mixedVector B (Sum.inr 2512) = Sparse.eval nodeValue2512 (mixedVector B) := by
    change mixedMoment B node2512 node2512Labels = _
    exact sound2512 B hB hF
  have h2519 : mixedVector B (Sum.inr 2519) = Sparse.eval nodeValue2519 (mixedVector B) := by
    change mixedMoment B node2519 node2519Labels = _
    exact sound2519 B hB hF
  have h2523 : mixedVector B (Sum.inr 2523) = Sparse.eval nodeValue2523 (mixedVector B) := by
    change mixedMoment B node2523 node2523Labels = _
    exact sound2523 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h3817 : mixedVector B (Sum.inr 3817) = Sparse.eval nodeValue3817 (mixedVector B) := by
    change mixedMoment B node3817 node3817Labels = _
    exact sound3817 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm620, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2512, h2519, h2523, h2743, h3817, h4092, reducedSource529] using sourceEq620 B hB

theorem rowSound529 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row529 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck529, numericCheck529, reducedZero529 B hB hF, mul_zero]

theorem reducedZero530 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource530 (mixedVector B) = 0 := by
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h2523 : mixedVector B (Sum.inr 2523) = Sparse.eval nodeValue2523 (mixedVector B) := by
    change mixedMoment B node2523 node2523Labels = _
    exact sound2523 B hB hF
  have h2561 : mixedVector B (Sum.inr 2561) = Sparse.eval nodeValue2561 (mixedVector B) := by
    change mixedMoment B node2561 node2561Labels = _
    exact sound2561 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm621, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1246, h2523, h2561, h2742, h2743, h4092, reducedSource530] using sourceEq621 B hB

theorem rowSound530 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row530 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck530, numericCheck530, reducedZero530 B hB hF, mul_zero]

theorem reducedZero535 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource535 (mixedVector B) = 0 := by
  have h2054 : mixedVector B (Sum.inr 2054) = Sparse.eval nodeValue2054 (mixedVector B) := by
    change mixedMoment B node2054 node2054Labels = _
    exact sound2054 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h2066 : mixedVector B (Sum.inr 2066) = Sparse.eval nodeValue2066 (mixedVector B) := by
    change mixedMoment B node2066 node2066Labels = _
    exact sound2066 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm626, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2054, h2062, h2066, h2293, h3548, h4084, reducedSource535] using sourceEq626 B hB

theorem rowSound535 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row535 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck535, numericCheck535, reducedZero535 B hB hF, mul_zero]

theorem reducedZero536 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource536 (mixedVector B) = 0 := by
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4619 : mixedVector B (Sum.inr 4619) = Sparse.eval nodeValue4619 (mixedVector B) := by
    change mixedMoment B node4619 node4619Labels = _
    exact sound4619 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5101 : mixedVector B (Sum.inr 5101) = Sparse.eval nodeValue5101 (mixedVector B) := by
    change mixedMoment B node5101 node5101Labels = _
    exact sound5101 B hB hF
  have h5107 : mixedVector B (Sum.inr 5107) = Sparse.eval nodeValue5107 (mixedVector B) := by
    change mixedMoment B node5107 node5107Labels = _
    exact sound5107 B hB hF
  have h5111 : mixedVector B (Sum.inr 5111) = Sparse.eval nodeValue5111 (mixedVector B) := by
    change mixedMoment B node5111 node5111Labels = _
    exact sound5111 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5163 : mixedVector B (Sum.inr 5163) = Sparse.eval nodeValue5163 (mixedVector B) := by
    change mixedMoment B node5163 node5163Labels = _
    exact sound5163 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5291 : mixedVector B (Sum.inr 5291) = Sparse.eval nodeValue5291 (mixedVector B) := by
    change mixedMoment B node5291 node5291Labels = _
    exact sound5291 B hB hF
  have h5304 : mixedVector B (Sum.inr 5304) = Sparse.eval nodeValue5304 (mixedVector B) := by
    change mixedMoment B node5304 node5304Labels = _
    exact sound5304 B hB hF
  have h5409 : mixedVector B (Sum.inr 5409) = Sparse.eval nodeValue5409 (mixedVector B) := by
    change mixedMoment B node5409 node5409Labels = _
    exact sound5409 B hB hF
  have h5441 : mixedVector B (Sum.inr 5441) = Sparse.eval nodeValue5441 (mixedVector B) := by
    change mixedMoment B node5441 node5441Labels = _
    exact sound5441 B hB hF
  have h5442 : mixedVector B (Sum.inr 5442) = Sparse.eval nodeValue5442 (mixedVector B) := by
    change mixedMoment B node5442 node5442Labels = _
    exact sound5442 B hB hF
  simpa only [sourceForm627, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4092, h4602, h4608, h4612, h4619, h5075, h5101, h5107, h5111, h5134, h5141, h5163, h5258, h5261, h5271, h5275, h5291, h5304, h5409, h5441, h5442, reducedSource536] using sourceEq627 B hB

theorem rowSound536 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row536 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck536, numericCheck536, reducedZero536 B hB hF, mul_zero]

theorem sourceRowsAt528 : MixedData.sourceRows (528 : Fin 2425) =
    MixedData.row528 := by decide +kernel

theorem sourceRowsAt529 : MixedData.sourceRows (529 : Fin 2425) =
    MixedData.row529 := by decide +kernel

theorem sourceRowsAt530 : MixedData.sourceRows (530 : Fin 2425) =
    MixedData.row530 := by decide +kernel

theorem sourceRowsAt531 : MixedData.sourceRows (531 : Fin 2425) =
    MixedData.row531 := by decide +kernel

theorem sourceRowsAt532 : MixedData.sourceRows (532 : Fin 2425) =
    MixedData.row532 := by decide +kernel

theorem sourceRowsAt533 : MixedData.sourceRows (533 : Fin 2425) =
    MixedData.row533 := by decide +kernel

theorem sourceRowsAt534 : MixedData.sourceRows (534 : Fin 2425) =
    MixedData.row534 := by decide +kernel

theorem sourceRowsAt535 : MixedData.sourceRows (535 : Fin 2425) =
    MixedData.row535 := by decide +kernel

theorem sourceRowsAt536 : MixedData.sourceRows (536 : Fin 2425) =
    MixedData.row536 := by decide +kernel

theorem sourceRowsAt537 : MixedData.sourceRows (537 : Fin 2425) =
    MixedData.row537 := by decide +kernel

theorem sourceRowsAt538 : MixedData.sourceRows (538 : Fin 2425) =
    MixedData.row538 := by decide +kernel

theorem sourceRowsAt539 : MixedData.sourceRows (539 : Fin 2425) =
    MixedData.row539 := by decide +kernel

theorem sourceRowsAt540 : MixedData.sourceRows (540 : Fin 2425) =
    MixedData.row540 := by decide +kernel

theorem sourceRowsAt541 : MixedData.sourceRows (541 : Fin 2425) =
    MixedData.row541 := by decide +kernel

theorem sourceRowsAt542 : MixedData.sourceRows (542 : Fin 2425) =
    MixedData.row542 := by decide +kernel

theorem sourceRowsAt543 : MixedData.sourceRows (543 : Fin 2425) =
    MixedData.row543 := by decide +kernel

theorem chunkSound33_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 33) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 528 ∨ k.val = 529 ∨ k.val = 530 ∨ k.val = 531 ∨ k.val = 532 ∨ k.val = 533 ∨ k.val = 534 ∨ k.val = 535 ∨ k.val = 536 ∨ k.val = 537 ∨ k.val = 538 ∨ k.val = 539 ∨ k.val = 540 ∨ k.val = 541 ∨ k.val = 542 ∨ k.val = 543 := by omega
  rcases heq with h528 | h529 | h530 | h531 | h532 | h533 | h534 | h535 | h536 | h537 | h538 | h539 | h540 | h541 | h542 | h543
  · have he : k = (528 : Fin 2425) := Fin.ext h528
    subst k
    rw [sourceRowsAt528]
    exact rowSound528 B hB hF
  · have he : k = (529 : Fin 2425) := Fin.ext h529
    subst k
    rw [sourceRowsAt529]
    exact rowSound529 B hB hF
  · have he : k = (530 : Fin 2425) := Fin.ext h530
    subst k
    rw [sourceRowsAt530]
    exact rowSound530 B hB hF
  · have he : k = (531 : Fin 2425) := Fin.ext h531
    subst k
    rw [sourceRowsAt531]
    exact rowSound531_e B hB hF
  · have he : k = (532 : Fin 2425) := Fin.ext h532
    subst k
    rw [sourceRowsAt532]
    exact rowSound532_e B hB hF
  · have he : k = (533 : Fin 2425) := Fin.ext h533
    subst k
    rw [sourceRowsAt533]
    exact rowSound533_e B hB hF
  · have he : k = (534 : Fin 2425) := Fin.ext h534
    subst k
    rw [sourceRowsAt534]
    exact rowSound534_e B hB hF
  · have he : k = (535 : Fin 2425) := Fin.ext h535
    subst k
    rw [sourceRowsAt535]
    exact rowSound535 B hB hF
  · have he : k = (536 : Fin 2425) := Fin.ext h536
    subst k
    rw [sourceRowsAt536]
    exact rowSound536 B hB hF
  · have he : k = (537 : Fin 2425) := Fin.ext h537
    subst k
    rw [sourceRowsAt537]
    exact rowSound537_e B hB hF
  · have he : k = (538 : Fin 2425) := Fin.ext h538
    subst k
    rw [sourceRowsAt538]
    exact rowSound538_e B hB hF
  · have he : k = (539 : Fin 2425) := Fin.ext h539
    subst k
    rw [sourceRowsAt539]
    exact rowSound539_e B hB hF
  · have he : k = (540 : Fin 2425) := Fin.ext h540
    subst k
    rw [sourceRowsAt540]
    exact rowSound540_e B hB hF
  · have he : k = (541 : Fin 2425) := Fin.ext h541
    subst k
    rw [sourceRowsAt541]
    exact rowSound541_e B hB hF
  · have he : k = (542 : Fin 2425) := Fin.ext h542
    subst k
    rw [sourceRowsAt542]
    exact rowSound542_e B hB hF
  · have he : k = (543 : Fin 2425) := Fin.ext h543
    subst k
    rw [sourceRowsAt543]
    exact rowSound543_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33_e_oai
