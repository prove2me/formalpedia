-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:12:07.323206+00:00
-- url     : https://prove2.me/submissions/5a1c24c5-084c-4f3e-adf3-e2d5f85be940

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E128
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_reducedZero14_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_reducedZero15_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound0_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound10_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound12_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound13_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound3_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound4_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound5_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound6_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound7_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound9_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2844 raw2844Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw2844 raw2844Labels = mixedMoment B raw2844step0 raw2844step0Labels := by
      have hz : ∀ j, raw2844 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2844step0 = (fun i j => raw2844 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2844step0 raw2844; decide +kernel
      have hl : raw2844step0Labels = raw2844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2844 raw2844Labels permutation434 hz
    mixedMoment B raw2844step0 raw2844step0Labels = mixedMoment B raw2844step1 raw2844step1Labels := by
      have ha : raw2844step1 = (fun i j => raw2844step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2844step1 raw2844step0; decide +kernel
      have hl : raw2844step1Labels = raw2844step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2844step0 raw2844step0Labels permutation32 permutation4
    mixedMoment B raw2844step1 raw2844step1Labels = mixedMoment B raw2844step2 raw2844step2Labels := by
      have ha : raw2844step2 = -raw2844step1 := by apply Matrix.ext; change ∀ i j, raw2844step2 i j = -(raw2844step1 i j); unfold raw2844step2 raw2844step1; decide +kernel
      have hl : raw2844step2Labels = raw2844step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node494 node494Labels := by rfl

theorem canonical2845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2845 raw2845Labels = mixedMoment B node500 node500Labels := by
  calc
    mixedMoment B raw2845 raw2845Labels = mixedMoment B raw2845step0 raw2845step0Labels := by
      have hz : ∀ j, raw2845 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2845step0 = (fun i j => raw2845 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2845step0 raw2845; decide +kernel
      have hl : raw2845step0Labels = raw2845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2845 raw2845Labels permutation434 hz
    mixedMoment B raw2845step0 raw2845step0Labels = mixedMoment B raw2845step1 raw2845step1Labels := by
      have ha : raw2845step1 = (fun i j => raw2845step0 (permutation74 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2845step1 raw2845step0; decide +kernel
      have hl : raw2845step1Labels = raw2845step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2845step0 raw2845step0Labels permutation74 permutation3
    _ = mixedMoment B node500 node500Labels := by rfl

theorem canonical2846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2846 raw2846Labels = mixedMoment B node527 node527Labels := by
  calc
    mixedMoment B raw2846 raw2846Labels = mixedMoment B raw2846step0 raw2846step0Labels := by
      have hz : ∀ j, raw2846 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2846step0 = (fun i j => raw2846 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2846step0 raw2846; decide +kernel
      have hl : raw2846step0Labels = raw2846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2846 raw2846Labels permutation434 hz
    mixedMoment B raw2846step0 raw2846step0Labels = mixedMoment B raw2846step1 raw2846step1Labels := by
      have hz : ∀ j, raw2846step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2846step1 = (fun i j => raw2846step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2846step1 raw2846step0; decide +kernel
      have hl : raw2846step1Labels = raw2846step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2846step0 raw2846step0Labels permutation80 hz
    mixedMoment B raw2846step1 raw2846step1Labels = mixedMoment B raw2846step2 raw2846step2Labels := by
      have ha : raw2846step2 = (fun i j => raw2846step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2846step2 raw2846step1; decide +kernel
      have hl : raw2846step2Labels = raw2846step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2846step1 raw2846step1Labels permutation8 permutation6
    _ = mixedMoment B node527 node527Labels := by rfl

theorem canonical2847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2847 raw2847Labels = mixedMoment B node524 node524Labels := by
  calc
    mixedMoment B raw2847 raw2847Labels = mixedMoment B raw2847step0 raw2847step0Labels := by
      have ha : raw2847step0 = (fun i j => raw2847 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2847step0 raw2847; decide +kernel
      have hl : raw2847step0Labels = raw2847Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2847 raw2847Labels permutation158 permutation6
    _ = mixedMoment B node524 node524Labels := by rfl

theorem canonical2848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2848 raw2848Labels = mixedMoment B node527 node527Labels := by
  calc
    mixedMoment B raw2848 raw2848Labels = mixedMoment B raw2848step0 raw2848step0Labels := by
      have hz : ∀ j, raw2848 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2848step0 = (fun i j => raw2848 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2848step0 raw2848; decide +kernel
      have hl : raw2848step0Labels = raw2848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2848 raw2848Labels permutation520 hz
    mixedMoment B raw2848step0 raw2848step0Labels = mixedMoment B raw2848step1 raw2848step1Labels := by
      have hz : ∀ j, raw2848step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2848step1 = (fun i j => raw2848step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2848step1 raw2848step0; decide +kernel
      have hl : raw2848step1Labels = raw2848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2848step0 raw2848step0Labels permutation104 hz
    mixedMoment B raw2848step1 raw2848step1Labels = mixedMoment B raw2848step2 raw2848step2Labels := by
      have ha : raw2848step2 = (fun i j => raw2848step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2848step2 raw2848step1; decide +kernel
      have hl : raw2848step2Labels = raw2848step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2848step1 raw2848step1Labels permutation8 permutation6
    _ = mixedMoment B node527 node527Labels := by rfl

theorem canonical2849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2849 raw2849Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw2849 raw2849Labels = mixedMoment B raw2849step0 raw2849step0Labels := by
      have hz : ∀ j, raw2849 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2849step0 = (fun i j => raw2849 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2849step0 raw2849; decide +kernel
      have hl : raw2849step0Labels = raw2849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2849 raw2849Labels permutation434 hz
    mixedMoment B raw2849step0 raw2849step0Labels = mixedMoment B raw2849step1 raw2849step1Labels := by
      have ha : raw2849step1 = (fun i j => raw2849step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2849step1 raw2849step0; decide +kernel
      have hl : raw2849step1Labels = raw2849step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2849step0 raw2849step0Labels permutation137 permutation2
    _ = mixedMoment B node494 node494Labels := by rfl

theorem canonical2850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2850 raw2850Labels = mixedMoment B node6 node6Labels := by
  calc
    mixedMoment B raw2850 raw2850Labels = mixedMoment B raw2850step0 raw2850step0Labels := by
      have hz : ∀ j, raw2850 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2850step0 = (fun i j => raw2850 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2850step0 raw2850; decide +kernel
      have hl : raw2850step0Labels = raw2850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2850 raw2850Labels permutation520 hz
    mixedMoment B raw2850step0 raw2850step0Labels = mixedMoment B raw2850step1 raw2850step1Labels := by
      have hz : ∀ j, raw2850step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2850step1 = (fun i j => raw2850step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2850step1 raw2850step0; decide +kernel
      have hl : raw2850step1Labels = raw2850step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2850step0 raw2850step0Labels permutation104 hz
    mixedMoment B raw2850step1 raw2850step1Labels = mixedMoment B raw2850step2 raw2850step2Labels := by
      have hz : ∀ j, raw2850step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2850step2 = (fun i j => raw2850step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2850step2 raw2850step1; decide +kernel
      have hl : raw2850step2Labels = raw2850step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2850step1 raw2850step1Labels permutation20 hz
    mixedMoment B raw2850step2 raw2850step2Labels = mixedMoment B raw2850step3 raw2850step3Labels := by
      have hz : ∀ j, raw2850step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw2850step3 = (fun i j => raw2850step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw2850step3 raw2850step2; decide +kernel
      have hl : raw2850step3Labels = raw2850step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2850step2 raw2850step2Labels permutation4 hz
    mixedMoment B raw2850step3 raw2850step3Labels = mixedMoment B raw2850step4 raw2850step4Labels := by
      have ha : raw2850step4 = (fun i j => raw2850step3 (permutation1 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2850step4 raw2850step3; decide +kernel
      have hl : raw2850step4Labels = raw2850step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2850step3 raw2850step3Labels permutation1 permutation0
    _ = mixedMoment B node6 node6Labels := by rfl

theorem canonical2909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2909 raw2909Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2909 raw2909Labels = mixedMoment B raw2909step0 raw2909step0Labels := by
      have hz : ∀ j, raw2909 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2909step0 = (fun i j => raw2909 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2909step0 raw2909; decide +kernel
      have hl : raw2909step0Labels = raw2909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2909 raw2909Labels permutation520 hz
    mixedMoment B raw2909step0 raw2909step0Labels = mixedMoment B raw2909step1 raw2909step1Labels := by
      have hz : ∀ j, raw2909step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2909step1 = (fun i j => raw2909step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2909step1 raw2909step0; decide +kernel
      have hl : raw2909step1Labels = raw2909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2909step0 raw2909step0Labels permutation104 hz
    mixedMoment B raw2909step1 raw2909step1Labels = mixedMoment B raw2909step2 raw2909step2Labels := by
      have hz : ∀ j, raw2909step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2909step2 = (fun i j => raw2909step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2909step2 raw2909step1; decide +kernel
      have hl : raw2909step2Labels = raw2909step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2909step1 raw2909step1Labels permutation20 hz
    mixedMoment B raw2909step2 raw2909step2Labels = mixedMoment B raw2909step3 raw2909step3Labels := by
      have hz : ∀ i, raw2909step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2909step3 = (fun i j => raw2909step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2909step3 raw2909step2; decide +kernel
      have hl : raw2909step3Labels = (fun j => raw2909step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2909step2 raw2909step2Labels permutation6 hz
    mixedMoment B raw2909step3 raw2909step3Labels = mixedMoment B raw2909step4 raw2909step4Labels := by
      have ha : raw2909step4 = (fun i j => raw2909step3 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2909step4 raw2909step3; decide +kernel
      have hl : raw2909step4Labels = raw2909step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2909step3 raw2909step3Labels permutation6 permutation0
    mixedMoment B raw2909step4 raw2909step4Labels = mixedMoment B raw2909step5 raw2909step5Labels := by
      have ha : raw2909step5 = -raw2909step4 := by apply Matrix.ext; change ∀ i j, raw2909step5 i j = -(raw2909step4 i j); unfold raw2909step5 raw2909step4; decide +kernel
      have hl : raw2909step5Labels = raw2909step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical2910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2910 raw2910Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2910 raw2910Labels = mixedMoment B raw2910step0 raw2910step0Labels := by
      have hz : ∀ j, raw2910 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2910step0 = (fun i j => raw2910 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2910step0 raw2910; decide +kernel
      have hl : raw2910step0Labels = raw2910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2910 raw2910Labels permutation520 hz
    mixedMoment B raw2910step0 raw2910step0Labels = mixedMoment B raw2910step1 raw2910step1Labels := by
      have hz : ∀ j, raw2910step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2910step1 = (fun i j => raw2910step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2910step1 raw2910step0; decide +kernel
      have hl : raw2910step1Labels = raw2910step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2910step0 raw2910step0Labels permutation104 hz
    mixedMoment B raw2910step1 raw2910step1Labels = mixedMoment B raw2910step2 raw2910step2Labels := by
      have hz : ∀ j, raw2910step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2910step2 = (fun i j => raw2910step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2910step2 raw2910step1; decide +kernel
      have hl : raw2910step2Labels = raw2910step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2910step1 raw2910step1Labels permutation14 hz
    mixedMoment B raw2910step2 raw2910step2Labels = mixedMoment B raw2910step3 raw2910step3Labels := by
      have hz : ∀ i, raw2910step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2910step3 = (fun i j => raw2910step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2910step3 raw2910step2; decide +kernel
      have hl : raw2910step3Labels = (fun j => raw2910step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2910step2 raw2910step2Labels permutation6 hz
    mixedMoment B raw2910step3 raw2910step3Labels = mixedMoment B raw2910step4 raw2910step4Labels := by
      have ha : raw2910step4 = (fun i j => raw2910step3 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2910step4 raw2910step3; decide +kernel
      have hl : raw2910step4Labels = raw2910step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2910step3 raw2910step3Labels permutation6 permutation0
    mixedMoment B raw2910step4 raw2910step4Labels = mixedMoment B raw2910step5 raw2910step5Labels := by
      have ha : raw2910step5 = -raw2910step4 := by apply Matrix.ext; change ∀ i j, raw2910step5 i j = -(raw2910step4 i j); unfold raw2910step5 raw2910step4; decide +kernel
      have hl : raw2910step5Labels = raw2910step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical2911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2911 raw2911Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2911 raw2911Labels = mixedMoment B raw2911step0 raw2911step0Labels := by
      have hz : ∀ j, raw2911 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2911step0 = (fun i j => raw2911 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2911step0 raw2911; decide +kernel
      have hl : raw2911step0Labels = raw2911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2911 raw2911Labels permutation520 hz
    mixedMoment B raw2911step0 raw2911step0Labels = mixedMoment B raw2911step1 raw2911step1Labels := by
      have hz : ∀ j, raw2911step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2911step1 = (fun i j => raw2911step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2911step1 raw2911step0; decide +kernel
      have hl : raw2911step1Labels = raw2911step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2911step0 raw2911step0Labels permutation80 hz
    mixedMoment B raw2911step1 raw2911step1Labels = mixedMoment B raw2911step2 raw2911step2Labels := by
      have hz : ∀ j, raw2911step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2911step2 = (fun i j => raw2911step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2911step2 raw2911step1; decide +kernel
      have hl : raw2911step2Labels = raw2911step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2911step1 raw2911step1Labels permutation14 hz
    mixedMoment B raw2911step2 raw2911step2Labels = mixedMoment B raw2911step3 raw2911step3Labels := by
      have hz : ∀ i, raw2911step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2911step3 = (fun i j => raw2911step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2911step3 raw2911step2; decide +kernel
      have hl : raw2911step3Labels = (fun j => raw2911step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2911step2 raw2911step2Labels permutation6 hz
    mixedMoment B raw2911step3 raw2911step3Labels = mixedMoment B raw2911step4 raw2911step4Labels := by
      have ha : raw2911step4 = (fun i j => raw2911step3 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2911step4 raw2911step3; decide +kernel
      have hl : raw2911step4Labels = raw2911step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2911step3 raw2911step3Labels permutation6 permutation0
    mixedMoment B raw2911step4 raw2911step4Labels = mixedMoment B raw2911step5 raw2911step5Labels := by
      have ha : raw2911step5 = -raw2911step4 := by apply Matrix.ext; change ∀ i j, raw2911step5 i j = -(raw2911step4 i j); unfold raw2911step5 raw2911step4; decide +kernel
      have hl : raw2911step5Labels = raw2911step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical2912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2912 raw2912Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2912 raw2912Labels = mixedMoment B raw2912step0 raw2912step0Labels := by
      have hz : ∀ j, raw2912 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2912step0 = (fun i j => raw2912 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2912step0 raw2912; decide +kernel
      have hl : raw2912step0Labels = raw2912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2912 raw2912Labels permutation434 hz
    mixedMoment B raw2912step0 raw2912step0Labels = mixedMoment B raw2912step1 raw2912step1Labels := by
      have hz : ∀ j, raw2912step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2912step1 = (fun i j => raw2912step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2912step1 raw2912step0; decide +kernel
      have hl : raw2912step1Labels = raw2912step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2912step0 raw2912step0Labels permutation80 hz
    mixedMoment B raw2912step1 raw2912step1Labels = mixedMoment B raw2912step2 raw2912step2Labels := by
      have hz : ∀ j, raw2912step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2912step2 = (fun i j => raw2912step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2912step2 raw2912step1; decide +kernel
      have hl : raw2912step2Labels = raw2912step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2912step1 raw2912step1Labels permutation14 hz
    mixedMoment B raw2912step2 raw2912step2Labels = mixedMoment B raw2912step3 raw2912step3Labels := by
      have hz : ∀ i, raw2912step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2912step3 = (fun i j => raw2912step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2912step3 raw2912step2; decide +kernel
      have hl : raw2912step3Labels = (fun j => raw2912step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2912step2 raw2912step2Labels permutation6 hz
    mixedMoment B raw2912step3 raw2912step3Labels = mixedMoment B raw2912step4 raw2912step4Labels := by
      have ha : raw2912step4 = (fun i j => raw2912step3 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2912step4 raw2912step3; decide +kernel
      have hl : raw2912step4Labels = raw2912step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2912step3 raw2912step3Labels permutation6 permutation0
    mixedMoment B raw2912step4 raw2912step4Labels = mixedMoment B raw2912step5 raw2912step5Labels := by
      have ha : raw2912step5 = -raw2912step4 := by apply Matrix.ext; change ∀ i j, raw2912step5 i j = -(raw2912step4 i j); unfold raw2912step5 raw2912step4; decide +kernel
      have hl : raw2912step5Labels = raw2912step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical2913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2913 raw2913Labels = mixedMoment B node4097 node4097Labels := by
  calc
    mixedMoment B raw2913 raw2913Labels = mixedMoment B raw2913step0 raw2913step0Labels := by
      have hz : ∀ j, raw2913 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2913step0 = (fun i j => raw2913 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2913step0 raw2913; decide +kernel
      have hl : raw2913step0Labels = raw2913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2913 raw2913Labels permutation520 hz
    mixedMoment B raw2913step0 raw2913step0Labels = mixedMoment B raw2913step1 raw2913step1Labels := by
      have hz : ∀ j, raw2913step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2913step1 = (fun i j => raw2913step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2913step1 raw2913step0; decide +kernel
      have hl : raw2913step1Labels = raw2913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2913step0 raw2913step0Labels permutation104 hz
    mixedMoment B raw2913step1 raw2913step1Labels = mixedMoment B raw2913step2 raw2913step2Labels := by
      have hz : ∀ j, raw2913step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2913step2 = (fun i j => raw2913step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2913step2 raw2913step1; decide +kernel
      have hl : raw2913step2Labels = raw2913step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2913step1 raw2913step1Labels permutation20 hz
    mixedMoment B raw2913step2 raw2913step2Labels = mixedMoment B raw2913step3 raw2913step3Labels := by
      have hz : ∀ j, raw2913step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw2913step3 = (fun i j => raw2913step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw2913step3 raw2913step2; decide +kernel
      have hl : raw2913step3Labels = raw2913step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2913step2 raw2913step2Labels permutation4 hz
    mixedMoment B raw2913step3 raw2913step3Labels = mixedMoment B raw2913step4 raw2913step4Labels := by
      have hz : ∀ i, raw2913step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2913step4 = (fun i j => raw2913step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2913step4 raw2913step3; decide +kernel
      have hl : raw2913step4Labels = (fun j => raw2913step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2913step3 raw2913step3Labels permutation6 hz
    _ = mixedMoment B node4097 node4097Labels := by rfl

theorem canonical2914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2914 raw2914Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2914 raw2914Labels = mixedMoment B raw2914step0 raw2914step0Labels := by
      have hz : ∀ j, raw2914 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2914step0 = (fun i j => raw2914 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2914step0 raw2914; decide +kernel
      have hl : raw2914step0Labels = raw2914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2914 raw2914Labels permutation520 hz
    mixedMoment B raw2914step0 raw2914step0Labels = mixedMoment B raw2914step1 raw2914step1Labels := by
      have hz : ∀ j, raw2914step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2914step1 = (fun i j => raw2914step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2914step1 raw2914step0; decide +kernel
      have hl : raw2914step1Labels = raw2914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2914step0 raw2914step0Labels permutation104 hz
    mixedMoment B raw2914step1 raw2914step1Labels = mixedMoment B raw2914step2 raw2914step2Labels := by
      have hz : ∀ j, raw2914step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2914step2 = (fun i j => raw2914step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2914step2 raw2914step1; decide +kernel
      have hl : raw2914step2Labels = raw2914step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2914step1 raw2914step1Labels permutation20 hz
    mixedMoment B raw2914step2 raw2914step2Labels = mixedMoment B raw2914step3 raw2914step3Labels := by
      have hz : ∀ i, raw2914step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2914step3 = (fun i j => raw2914step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2914step3 raw2914step2; decide +kernel
      have hl : raw2914step3Labels = (fun j => raw2914step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2914step2 raw2914step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2915 raw2915Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2915 raw2915Labels = mixedMoment B raw2915step0 raw2915step0Labels := by
      have hz : ∀ j, raw2915 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2915step0 = (fun i j => raw2915 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2915step0 raw2915; decide +kernel
      have hl : raw2915step0Labels = raw2915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2915 raw2915Labels permutation520 hz
    mixedMoment B raw2915step0 raw2915step0Labels = mixedMoment B raw2915step1 raw2915step1Labels := by
      have hz : ∀ j, raw2915step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2915step1 = (fun i j => raw2915step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2915step1 raw2915step0; decide +kernel
      have hl : raw2915step1Labels = raw2915step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2915step0 raw2915step0Labels permutation104 hz
    mixedMoment B raw2915step1 raw2915step1Labels = mixedMoment B raw2915step2 raw2915step2Labels := by
      have hz : ∀ i, raw2915step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2915step2 = (fun i j => raw2915step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2915step2 raw2915step1; decide +kernel
      have hl : raw2915step2Labels = (fun j => raw2915step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2915step1 raw2915step1Labels permutation6 hz
    mixedMoment B raw2915step2 raw2915step2Labels = mixedMoment B raw2915step3 raw2915step3Labels := by
      have ha : raw2915step3 = (fun i j => raw2915step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2915step3 raw2915step2; decide +kernel
      have hl : raw2915step3Labels = raw2915step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2915step2 raw2915step2Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2916 raw2916Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2916 raw2916Labels = mixedMoment B raw2916step0 raw2916step0Labels := by
      have hz : ∀ j, raw2916 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2916step0 = (fun i j => raw2916 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2916step0 raw2916; decide +kernel
      have hl : raw2916step0Labels = raw2916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2916 raw2916Labels permutation520 hz
    mixedMoment B raw2916step0 raw2916step0Labels = mixedMoment B raw2916step1 raw2916step1Labels := by
      have hz : ∀ j, raw2916step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2916step1 = (fun i j => raw2916step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2916step1 raw2916step0; decide +kernel
      have hl : raw2916step1Labels = raw2916step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2916step0 raw2916step0Labels permutation80 hz
    mixedMoment B raw2916step1 raw2916step1Labels = mixedMoment B raw2916step2 raw2916step2Labels := by
      have hz : ∀ i, raw2916step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2916step2 = (fun i j => raw2916step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2916step2 raw2916step1; decide +kernel
      have hl : raw2916step2Labels = (fun j => raw2916step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2916step1 raw2916step1Labels permutation6 hz
    mixedMoment B raw2916step2 raw2916step2Labels = mixedMoment B raw2916step3 raw2916step3Labels := by
      have ha : raw2916step3 = (fun i j => raw2916step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2916step3 raw2916step2; decide +kernel
      have hl : raw2916step3Labels = raw2916step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2916step2 raw2916step2Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2917 raw2917Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2917 raw2917Labels = mixedMoment B raw2917step0 raw2917step0Labels := by
      have hz : ∀ j, raw2917 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2917step0 = (fun i j => raw2917 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2917step0 raw2917; decide +kernel
      have hl : raw2917step0Labels = raw2917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2917 raw2917Labels permutation434 hz
    mixedMoment B raw2917step0 raw2917step0Labels = mixedMoment B raw2917step1 raw2917step1Labels := by
      have hz : ∀ j, raw2917step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2917step1 = (fun i j => raw2917step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2917step1 raw2917step0; decide +kernel
      have hl : raw2917step1Labels = raw2917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2917step0 raw2917step0Labels permutation80 hz
    mixedMoment B raw2917step1 raw2917step1Labels = mixedMoment B raw2917step2 raw2917step2Labels := by
      have hz : ∀ i, raw2917step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2917step2 = (fun i j => raw2917step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2917step2 raw2917step1; decide +kernel
      have hl : raw2917step2Labels = (fun j => raw2917step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2917step1 raw2917step1Labels permutation6 hz
    mixedMoment B raw2917step2 raw2917step2Labels = mixedMoment B raw2917step3 raw2917step3Labels := by
      have ha : raw2917step3 = (fun i j => raw2917step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2917step3 raw2917step2; decide +kernel
      have hl : raw2917step3Labels = raw2917step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2917step2 raw2917step2Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2918 raw2918Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2918 raw2918Labels = mixedMoment B raw2918step0 raw2918step0Labels := by
      have hz : ∀ j, raw2918 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2918step0 = (fun i j => raw2918 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2918step0 raw2918; decide +kernel
      have hl : raw2918step0Labels = raw2918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2918 raw2918Labels permutation520 hz
    mixedMoment B raw2918step0 raw2918step0Labels = mixedMoment B raw2918step1 raw2918step1Labels := by
      have hz : ∀ j, raw2918step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2918step1 = (fun i j => raw2918step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2918step1 raw2918step0; decide +kernel
      have hl : raw2918step1Labels = raw2918step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2918step0 raw2918step0Labels permutation104 hz
    mixedMoment B raw2918step1 raw2918step1Labels = mixedMoment B raw2918step2 raw2918step2Labels := by
      have hz : ∀ j, raw2918step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2918step2 = (fun i j => raw2918step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2918step2 raw2918step1; decide +kernel
      have hl : raw2918step2Labels = raw2918step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2918step1 raw2918step1Labels permutation20 hz
    mixedMoment B raw2918step2 raw2918step2Labels = mixedMoment B raw2918step3 raw2918step3Labels := by
      have hz : ∀ i, raw2918step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2918step3 = (fun i j => raw2918step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2918step3 raw2918step2; decide +kernel
      have hl : raw2918step3Labels = (fun j => raw2918step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2918step2 raw2918step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical2919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2919 raw2919Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2919 raw2919Labels = mixedMoment B raw2919step0 raw2919step0Labels := by
      have hz : ∀ j, raw2919 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2919step0 = (fun i j => raw2919 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2919step0 raw2919; decide +kernel
      have hl : raw2919step0Labels = raw2919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2919 raw2919Labels permutation520 hz
    mixedMoment B raw2919step0 raw2919step0Labels = mixedMoment B raw2919step1 raw2919step1Labels := by
      have hz : ∀ j, raw2919step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2919step1 = (fun i j => raw2919step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2919step1 raw2919step0; decide +kernel
      have hl : raw2919step1Labels = raw2919step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2919step0 raw2919step0Labels permutation104 hz
    mixedMoment B raw2919step1 raw2919step1Labels = mixedMoment B raw2919step2 raw2919step2Labels := by
      have hz : ∀ j, raw2919step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2919step2 = (fun i j => raw2919step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2919step2 raw2919step1; decide +kernel
      have hl : raw2919step2Labels = raw2919step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2919step1 raw2919step1Labels permutation14 hz
    mixedMoment B raw2919step2 raw2919step2Labels = mixedMoment B raw2919step3 raw2919step3Labels := by
      have hz : ∀ i, raw2919step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2919step3 = (fun i j => raw2919step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2919step3 raw2919step2; decide +kernel
      have hl : raw2919step3Labels = (fun j => raw2919step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2919step2 raw2919step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2920 raw2920Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2920 raw2920Labels = mixedMoment B raw2920step0 raw2920step0Labels := by
      have hz : ∀ j, raw2920 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2920step0 = (fun i j => raw2920 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2920step0 raw2920; decide +kernel
      have hl : raw2920step0Labels = raw2920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2920 raw2920Labels permutation520 hz
    mixedMoment B raw2920step0 raw2920step0Labels = mixedMoment B raw2920step1 raw2920step1Labels := by
      have hz : ∀ j, raw2920step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2920step1 = (fun i j => raw2920step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2920step1 raw2920step0; decide +kernel
      have hl : raw2920step1Labels = raw2920step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2920step0 raw2920step0Labels permutation104 hz
    mixedMoment B raw2920step1 raw2920step1Labels = mixedMoment B raw2920step2 raw2920step2Labels := by
      have hz : ∀ i, raw2920step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2920step2 = (fun i j => raw2920step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2920step2 raw2920step1; decide +kernel
      have hl : raw2920step2Labels = (fun j => raw2920step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2920step1 raw2920step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2921 raw2921Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2921 raw2921Labels = mixedMoment B raw2921step0 raw2921step0Labels := by
      have hz : ∀ j, raw2921 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2921step0 = (fun i j => raw2921 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2921step0 raw2921; decide +kernel
      have hl : raw2921step0Labels = raw2921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2921 raw2921Labels permutation520 hz
    mixedMoment B raw2921step0 raw2921step0Labels = mixedMoment B raw2921step1 raw2921step1Labels := by
      have hz : ∀ j, raw2921step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2921step1 = (fun i j => raw2921step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2921step1 raw2921step0; decide +kernel
      have hl : raw2921step1Labels = raw2921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2921step0 raw2921step0Labels permutation56 hz
    mixedMoment B raw2921step1 raw2921step1Labels = mixedMoment B raw2921step2 raw2921step2Labels := by
      have hz : ∀ i, raw2921step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2921step2 = (fun i j => raw2921step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2921step2 raw2921step1; decide +kernel
      have hl : raw2921step2Labels = (fun j => raw2921step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2921step1 raw2921step1Labels permutation6 hz
    mixedMoment B raw2921step2 raw2921step2Labels = mixedMoment B raw2921step3 raw2921step3Labels := by
      have ha : raw2921step3 = (fun i j => raw2921step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2921step3 raw2921step2; decide +kernel
      have hl : raw2921step3Labels = raw2921step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2921step2 raw2921step2Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2922 raw2922Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2922 raw2922Labels = mixedMoment B raw2922step0 raw2922step0Labels := by
      have hz : ∀ j, raw2922 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2922step0 = (fun i j => raw2922 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2922step0 raw2922; decide +kernel
      have hl : raw2922step0Labels = raw2922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2922 raw2922Labels permutation434 hz
    mixedMoment B raw2922step0 raw2922step0Labels = mixedMoment B raw2922step1 raw2922step1Labels := by
      have hz : ∀ j, raw2922step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2922step1 = (fun i j => raw2922step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2922step1 raw2922step0; decide +kernel
      have hl : raw2922step1Labels = raw2922step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2922step0 raw2922step0Labels permutation56 hz
    mixedMoment B raw2922step1 raw2922step1Labels = mixedMoment B raw2922step2 raw2922step2Labels := by
      have hz : ∀ i, raw2922step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2922step2 = (fun i j => raw2922step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2922step2 raw2922step1; decide +kernel
      have hl : raw2922step2Labels = (fun j => raw2922step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2922step1 raw2922step1Labels permutation6 hz
    mixedMoment B raw2922step2 raw2922step2Labels = mixedMoment B raw2922step3 raw2922step3Labels := by
      have ha : raw2922step3 = (fun i j => raw2922step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2922step3 raw2922step2; decide +kernel
      have hl : raw2922step3Labels = raw2922step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2922step2 raw2922step2Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2923 raw2923Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2923 raw2923Labels = mixedMoment B raw2923step0 raw2923step0Labels := by
      have hz : ∀ j, raw2923 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2923step0 = (fun i j => raw2923 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2923step0 raw2923; decide +kernel
      have hl : raw2923step0Labels = raw2923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2923 raw2923Labels permutation520 hz
    mixedMoment B raw2923step0 raw2923step0Labels = mixedMoment B raw2923step1 raw2923step1Labels := by
      have hz : ∀ j, raw2923step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2923step1 = (fun i j => raw2923step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2923step1 raw2923step0; decide +kernel
      have hl : raw2923step1Labels = raw2923step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2923step0 raw2923step0Labels permutation104 hz
    mixedMoment B raw2923step1 raw2923step1Labels = mixedMoment B raw2923step2 raw2923step2Labels := by
      have hz : ∀ j, raw2923step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2923step2 = (fun i j => raw2923step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2923step2 raw2923step1; decide +kernel
      have hl : raw2923step2Labels = raw2923step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2923step1 raw2923step1Labels permutation14 hz
    mixedMoment B raw2923step2 raw2923step2Labels = mixedMoment B raw2923step3 raw2923step3Labels := by
      have hz : ∀ i, raw2923step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2923step3 = (fun i j => raw2923step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2923step3 raw2923step2; decide +kernel
      have hl : raw2923step3Labels = (fun j => raw2923step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2923step2 raw2923step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2924 raw2924Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2924 raw2924Labels = mixedMoment B raw2924step0 raw2924step0Labels := by
      have hz : ∀ j, raw2924 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2924step0 = (fun i j => raw2924 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2924step0 raw2924; decide +kernel
      have hl : raw2924step0Labels = raw2924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924 raw2924Labels permutation520 hz
    mixedMoment B raw2924step0 raw2924step0Labels = mixedMoment B raw2924step1 raw2924step1Labels := by
      have hz : ∀ j, raw2924step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2924step1 = (fun i j => raw2924step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2924step1 raw2924step0; decide +kernel
      have hl : raw2924step1Labels = raw2924step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924step0 raw2924step0Labels permutation80 hz
    mixedMoment B raw2924step1 raw2924step1Labels = mixedMoment B raw2924step2 raw2924step2Labels := by
      have hz : ∀ j, raw2924step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2924step2 = (fun i j => raw2924step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2924step2 raw2924step1; decide +kernel
      have hl : raw2924step2Labels = raw2924step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924step1 raw2924step1Labels permutation14 hz
    mixedMoment B raw2924step2 raw2924step2Labels = mixedMoment B raw2924step3 raw2924step3Labels := by
      have hz : ∀ i, raw2924step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2924step3 = (fun i j => raw2924step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2924step3 raw2924step2; decide +kernel
      have hl : raw2924step3Labels = (fun j => raw2924step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2924step2 raw2924step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2925 raw2925Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2925 raw2925Labels = mixedMoment B raw2925step0 raw2925step0Labels := by
      have hz : ∀ j, raw2925 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2925step0 = (fun i j => raw2925 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2925step0 raw2925; decide +kernel
      have hl : raw2925step0Labels = raw2925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2925 raw2925Labels permutation520 hz
    mixedMoment B raw2925step0 raw2925step0Labels = mixedMoment B raw2925step1 raw2925step1Labels := by
      have hz : ∀ j, raw2925step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2925step1 = (fun i j => raw2925step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2925step1 raw2925step0; decide +kernel
      have hl : raw2925step1Labels = raw2925step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2925step0 raw2925step0Labels permutation80 hz
    mixedMoment B raw2925step1 raw2925step1Labels = mixedMoment B raw2925step2 raw2925step2Labels := by
      have hz : ∀ i, raw2925step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2925step2 = (fun i j => raw2925step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2925step2 raw2925step1; decide +kernel
      have hl : raw2925step2Labels = (fun j => raw2925step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2925step1 raw2925step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2926 raw2926Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2926 raw2926Labels = mixedMoment B raw2926step0 raw2926step0Labels := by
      have hz : ∀ j, raw2926 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2926step0 = (fun i j => raw2926 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2926step0 raw2926; decide +kernel
      have hl : raw2926step0Labels = raw2926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2926 raw2926Labels permutation520 hz
    mixedMoment B raw2926step0 raw2926step0Labels = mixedMoment B raw2926step1 raw2926step1Labels := by
      have hz : ∀ j, raw2926step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2926step1 = (fun i j => raw2926step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2926step1 raw2926step0; decide +kernel
      have hl : raw2926step1Labels = raw2926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2926step0 raw2926step0Labels permutation56 hz
    mixedMoment B raw2926step1 raw2926step1Labels = mixedMoment B raw2926step2 raw2926step2Labels := by
      have hz : ∀ i, raw2926step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2926step2 = (fun i j => raw2926step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2926step2 raw2926step1; decide +kernel
      have hl : raw2926step2Labels = (fun j => raw2926step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2926step1 raw2926step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2927 raw2927Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2927 raw2927Labels = mixedMoment B raw2927step0 raw2927step0Labels := by
      have hz : ∀ j, raw2927 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2927step0 = (fun i j => raw2927 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2927step0 raw2927; decide +kernel
      have hl : raw2927step0Labels = raw2927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2927 raw2927Labels permutation346 hz
    mixedMoment B raw2927step0 raw2927step0Labels = mixedMoment B raw2927step1 raw2927step1Labels := by
      have hz : ∀ j, raw2927step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2927step1 = (fun i j => raw2927step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2927step1 raw2927step0; decide +kernel
      have hl : raw2927step1Labels = raw2927step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2927step0 raw2927step0Labels permutation56 hz
    mixedMoment B raw2927step1 raw2927step1Labels = mixedMoment B raw2927step2 raw2927step2Labels := by
      have hz : ∀ i, raw2927step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2927step2 = (fun i j => raw2927step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2927step2 raw2927step1; decide +kernel
      have hl : raw2927step2Labels = (fun j => raw2927step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2927step1 raw2927step1Labels permutation6 hz
    mixedMoment B raw2927step2 raw2927step2Labels = mixedMoment B raw2927step3 raw2927step3Labels := by
      have ha : raw2927step3 = (fun i j => raw2927step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2927step3 raw2927step2; decide +kernel
      have hl : raw2927step3Labels = raw2927step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2927step2 raw2927step2Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2928 raw2928Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2928 raw2928Labels = mixedMoment B raw2928step0 raw2928step0Labels := by
      have hz : ∀ j, raw2928 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2928step0 = (fun i j => raw2928 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2928step0 raw2928; decide +kernel
      have hl : raw2928step0Labels = raw2928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2928 raw2928Labels permutation520 hz
    mixedMoment B raw2928step0 raw2928step0Labels = mixedMoment B raw2928step1 raw2928step1Labels := by
      have hz : ∀ j, raw2928step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2928step1 = (fun i j => raw2928step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2928step1 raw2928step0; decide +kernel
      have hl : raw2928step1Labels = raw2928step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2928step0 raw2928step0Labels permutation80 hz
    mixedMoment B raw2928step1 raw2928step1Labels = mixedMoment B raw2928step2 raw2928step2Labels := by
      have hz : ∀ j, raw2928step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2928step2 = (fun i j => raw2928step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2928step2 raw2928step1; decide +kernel
      have hl : raw2928step2Labels = raw2928step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2928step1 raw2928step1Labels permutation14 hz
    mixedMoment B raw2928step2 raw2928step2Labels = mixedMoment B raw2928step3 raw2928step3Labels := by
      have hz : ∀ i, raw2928step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2928step3 = (fun i j => raw2928step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2928step3 raw2928step2; decide +kernel
      have hl : raw2928step3Labels = (fun j => raw2928step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2928step2 raw2928step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical2929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2929 raw2929Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2929 raw2929Labels = mixedMoment B raw2929step0 raw2929step0Labels := by
      have hz : ∀ j, raw2929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2929step0 = (fun i j => raw2929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2929step0 raw2929; decide +kernel
      have hl : raw2929step0Labels = raw2929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929 raw2929Labels permutation434 hz
    mixedMoment B raw2929step0 raw2929step0Labels = mixedMoment B raw2929step1 raw2929step1Labels := by
      have hz : ∀ j, raw2929step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2929step1 = (fun i j => raw2929step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2929step1 raw2929step0; decide +kernel
      have hl : raw2929step1Labels = raw2929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929step0 raw2929step0Labels permutation80 hz
    mixedMoment B raw2929step1 raw2929step1Labels = mixedMoment B raw2929step2 raw2929step2Labels := by
      have hz : ∀ j, raw2929step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2929step2 = (fun i j => raw2929step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2929step2 raw2929step1; decide +kernel
      have hl : raw2929step2Labels = raw2929step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929step1 raw2929step1Labels permutation14 hz
    mixedMoment B raw2929step2 raw2929step2Labels = mixedMoment B raw2929step3 raw2929step3Labels := by
      have hz : ∀ i, raw2929step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2929step3 = (fun i j => raw2929step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2929step3 raw2929step2; decide +kernel
      have hl : raw2929step3Labels = (fun j => raw2929step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2929step2 raw2929step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2930 raw2930Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2930 raw2930Labels = mixedMoment B raw2930step0 raw2930step0Labels := by
      have hz : ∀ j, raw2930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2930step0 = (fun i j => raw2930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2930step0 raw2930; decide +kernel
      have hl : raw2930step0Labels = raw2930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2930 raw2930Labels permutation434 hz
    mixedMoment B raw2930step0 raw2930step0Labels = mixedMoment B raw2930step1 raw2930step1Labels := by
      have hz : ∀ j, raw2930step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2930step1 = (fun i j => raw2930step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2930step1 raw2930step0; decide +kernel
      have hl : raw2930step1Labels = raw2930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2930step0 raw2930step0Labels permutation80 hz
    mixedMoment B raw2930step1 raw2930step1Labels = mixedMoment B raw2930step2 raw2930step2Labels := by
      have hz : ∀ i, raw2930step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2930step2 = (fun i j => raw2930step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2930step2 raw2930step1; decide +kernel
      have hl : raw2930step2Labels = (fun j => raw2930step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2930step1 raw2930step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2931 raw2931Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2931 raw2931Labels = mixedMoment B raw2931step0 raw2931step0Labels := by
      have hz : ∀ j, raw2931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2931step0 = (fun i j => raw2931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2931step0 raw2931; decide +kernel
      have hl : raw2931step0Labels = raw2931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2931 raw2931Labels permutation434 hz
    mixedMoment B raw2931step0 raw2931step0Labels = mixedMoment B raw2931step1 raw2931step1Labels := by
      have hz : ∀ j, raw2931step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2931step1 = (fun i j => raw2931step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2931step1 raw2931step0; decide +kernel
      have hl : raw2931step1Labels = raw2931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2931step0 raw2931step0Labels permutation56 hz
    mixedMoment B raw2931step1 raw2931step1Labels = mixedMoment B raw2931step2 raw2931step2Labels := by
      have hz : ∀ i, raw2931step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2931step2 = (fun i j => raw2931step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2931step2 raw2931step1; decide +kernel
      have hl : raw2931step2Labels = (fun j => raw2931step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2931step1 raw2931step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2932 raw2932Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2932 raw2932Labels = mixedMoment B raw2932step0 raw2932step0Labels := by
      have hz : ∀ j, raw2932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2932step0 = (fun i j => raw2932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2932step0 raw2932; decide +kernel
      have hl : raw2932step0Labels = raw2932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2932 raw2932Labels permutation346 hz
    mixedMoment B raw2932step0 raw2932step0Labels = mixedMoment B raw2932step1 raw2932step1Labels := by
      have hz : ∀ j, raw2932step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2932step1 = (fun i j => raw2932step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2932step1 raw2932step0; decide +kernel
      have hl : raw2932step1Labels = raw2932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2932step0 raw2932step0Labels permutation56 hz
    mixedMoment B raw2932step1 raw2932step1Labels = mixedMoment B raw2932step2 raw2932step2Labels := by
      have hz : ∀ i, raw2932step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2932step2 = (fun i j => raw2932step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2932step2 raw2932step1; decide +kernel
      have hl : raw2932step2Labels = (fun j => raw2932step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2932step1 raw2932step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2933 raw2933Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2933 raw2933Labels = mixedMoment B raw2933step0 raw2933step0Labels := by
      have hz : ∀ j, raw2933 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2933step0 = (fun i j => raw2933 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2933step0 raw2933; decide +kernel
      have hl : raw2933step0Labels = raw2933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2933 raw2933Labels permutation434 hz
    mixedMoment B raw2933step0 raw2933step0Labels = mixedMoment B raw2933step1 raw2933step1Labels := by
      have hz : ∀ j, raw2933step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2933step1 = (fun i j => raw2933step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2933step1 raw2933step0; decide +kernel
      have hl : raw2933step1Labels = raw2933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2933step0 raw2933step0Labels permutation80 hz
    mixedMoment B raw2933step1 raw2933step1Labels = mixedMoment B raw2933step2 raw2933step2Labels := by
      have hz : ∀ j, raw2933step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2933step2 = (fun i j => raw2933step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2933step2 raw2933step1; decide +kernel
      have hl : raw2933step2Labels = raw2933step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2933step1 raw2933step1Labels permutation14 hz
    mixedMoment B raw2933step2 raw2933step2Labels = mixedMoment B raw2933step3 raw2933step3Labels := by
      have hz : ∀ i, raw2933step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2933step3 = (fun i j => raw2933step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2933step3 raw2933step2; decide +kernel
      have hl : raw2933step3Labels = (fun j => raw2933step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2933step2 raw2933step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical2934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2934 raw2934Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw2934 raw2934Labels = mixedMoment B raw2934step0 raw2934step0Labels := by
      have hz : ∀ j, raw2934 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2934step0 = (fun i j => raw2934 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2934step0 raw2934; decide +kernel
      have hl : raw2934step0Labels = raw2934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934 raw2934Labels permutation520 hz
    mixedMoment B raw2934step0 raw2934step0Labels = mixedMoment B raw2934step1 raw2934step1Labels := by
      have hz : ∀ j, raw2934step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2934step1 = (fun i j => raw2934step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2934step1 raw2934step0; decide +kernel
      have hl : raw2934step1Labels = raw2934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step0 raw2934step0Labels permutation104 hz
    mixedMoment B raw2934step1 raw2934step1Labels = mixedMoment B raw2934step2 raw2934step2Labels := by
      have hz : ∀ j, raw2934step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2934step2 = (fun i j => raw2934step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2934step2 raw2934step1; decide +kernel
      have hl : raw2934step2Labels = raw2934step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step1 raw2934step1Labels permutation20 hz
    mixedMoment B raw2934step2 raw2934step2Labels = mixedMoment B raw2934step3 raw2934step3Labels := by
      have hz : ∀ j, raw2934step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw2934step3 = (fun i j => raw2934step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw2934step3 raw2934step2; decide +kernel
      have hl : raw2934step3Labels = raw2934step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step2 raw2934step2Labels permutation4 hz
    mixedMoment B raw2934step3 raw2934step3Labels = mixedMoment B raw2934step4 raw2934step4Labels := by
      have hz : ∀ i, raw2934step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2934step4 = (fun i j => raw2934step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2934step4 raw2934step3; decide +kernel
      have hl : raw2934step4Labels = (fun j => raw2934step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2934step3 raw2934step3Labels permutation6 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

theorem canonical2935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2935 raw2935Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2935 raw2935Labels = mixedMoment B raw2935step0 raw2935step0Labels := by
      have hz : ∀ j, raw2935 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2935step0 = (fun i j => raw2935 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2935step0 raw2935; decide +kernel
      have hl : raw2935step0Labels = raw2935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2935 raw2935Labels permutation520 hz
    mixedMoment B raw2935step0 raw2935step0Labels = mixedMoment B raw2935step1 raw2935step1Labels := by
      have hz : ∀ j, raw2935step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2935step1 = (fun i j => raw2935step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2935step1 raw2935step0; decide +kernel
      have hl : raw2935step1Labels = raw2935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2935step0 raw2935step0Labels permutation104 hz
    mixedMoment B raw2935step1 raw2935step1Labels = mixedMoment B raw2935step2 raw2935step2Labels := by
      have hz : ∀ j, raw2935step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2935step2 = (fun i j => raw2935step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2935step2 raw2935step1; decide +kernel
      have hl : raw2935step2Labels = raw2935step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2935step1 raw2935step1Labels permutation20 hz
    mixedMoment B raw2935step2 raw2935step2Labels = mixedMoment B raw2935step3 raw2935step3Labels := by
      have hz : ∀ i, raw2935step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2935step3 = (fun i j => raw2935step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2935step3 raw2935step2; decide +kernel
      have hl : raw2935step3Labels = (fun j => raw2935step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2935step2 raw2935step2Labels permutation6 hz
    mixedMoment B raw2935step3 raw2935step3Labels = mixedMoment B raw2935step4 raw2935step4Labels := by
      have ha : raw2935step4 = (fun i j => raw2935step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2935step4 raw2935step3; decide +kernel
      have hl : raw2935step4Labels = raw2935step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2935step3 raw2935step3Labels permutation7 permutation0
    mixedMoment B raw2935step4 raw2935step4Labels = mixedMoment B raw2935step5 raw2935step5Labels := by
      have ha : raw2935step5 = -raw2935step4 := by apply Matrix.ext; change ∀ i j, raw2935step5 i j = -(raw2935step4 i j); unfold raw2935step5 raw2935step4; decide +kernel
      have hl : raw2935step5Labels = raw2935step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2936 raw2936Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2936 raw2936Labels = mixedMoment B raw2936step0 raw2936step0Labels := by
      have hz : ∀ j, raw2936 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2936step0 = (fun i j => raw2936 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2936step0 raw2936; decide +kernel
      have hl : raw2936step0Labels = raw2936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2936 raw2936Labels permutation520 hz
    mixedMoment B raw2936step0 raw2936step0Labels = mixedMoment B raw2936step1 raw2936step1Labels := by
      have hz : ∀ j, raw2936step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2936step1 = (fun i j => raw2936step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2936step1 raw2936step0; decide +kernel
      have hl : raw2936step1Labels = raw2936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2936step0 raw2936step0Labels permutation104 hz
    mixedMoment B raw2936step1 raw2936step1Labels = mixedMoment B raw2936step2 raw2936step2Labels := by
      have hz : ∀ j, raw2936step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2936step2 = (fun i j => raw2936step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2936step2 raw2936step1; decide +kernel
      have hl : raw2936step2Labels = raw2936step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2936step1 raw2936step1Labels permutation14 hz
    mixedMoment B raw2936step2 raw2936step2Labels = mixedMoment B raw2936step3 raw2936step3Labels := by
      have hz : ∀ i, raw2936step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2936step3 = (fun i j => raw2936step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2936step3 raw2936step2; decide +kernel
      have hl : raw2936step3Labels = (fun j => raw2936step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2936step2 raw2936step2Labels permutation6 hz
    mixedMoment B raw2936step3 raw2936step3Labels = mixedMoment B raw2936step4 raw2936step4Labels := by
      have ha : raw2936step4 = (fun i j => raw2936step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2936step4 raw2936step3; decide +kernel
      have hl : raw2936step4Labels = raw2936step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2936step3 raw2936step3Labels permutation7 permutation0
    mixedMoment B raw2936step4 raw2936step4Labels = mixedMoment B raw2936step5 raw2936step5Labels := by
      have ha : raw2936step5 = -raw2936step4 := by apply Matrix.ext; change ∀ i j, raw2936step5 i j = -(raw2936step4 i j); unfold raw2936step5 raw2936step4; decide +kernel
      have hl : raw2936step5Labels = raw2936step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2937 raw2937Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2937 raw2937Labels = mixedMoment B raw2937step0 raw2937step0Labels := by
      have hz : ∀ j, raw2937 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2937step0 = (fun i j => raw2937 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2937step0 raw2937; decide +kernel
      have hl : raw2937step0Labels = raw2937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2937 raw2937Labels permutation520 hz
    mixedMoment B raw2937step0 raw2937step0Labels = mixedMoment B raw2937step1 raw2937step1Labels := by
      have hz : ∀ j, raw2937step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2937step1 = (fun i j => raw2937step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2937step1 raw2937step0; decide +kernel
      have hl : raw2937step1Labels = raw2937step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2937step0 raw2937step0Labels permutation80 hz
    mixedMoment B raw2937step1 raw2937step1Labels = mixedMoment B raw2937step2 raw2937step2Labels := by
      have hz : ∀ j, raw2937step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2937step2 = (fun i j => raw2937step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2937step2 raw2937step1; decide +kernel
      have hl : raw2937step2Labels = raw2937step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2937step1 raw2937step1Labels permutation14 hz
    mixedMoment B raw2937step2 raw2937step2Labels = mixedMoment B raw2937step3 raw2937step3Labels := by
      have hz : ∀ i, raw2937step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2937step3 = (fun i j => raw2937step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2937step3 raw2937step2; decide +kernel
      have hl : raw2937step3Labels = (fun j => raw2937step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2937step2 raw2937step2Labels permutation6 hz
    mixedMoment B raw2937step3 raw2937step3Labels = mixedMoment B raw2937step4 raw2937step4Labels := by
      have ha : raw2937step4 = (fun i j => raw2937step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2937step4 raw2937step3; decide +kernel
      have hl : raw2937step4Labels = raw2937step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2937step3 raw2937step3Labels permutation7 permutation0
    mixedMoment B raw2937step4 raw2937step4Labels = mixedMoment B raw2937step5 raw2937step5Labels := by
      have ha : raw2937step5 = -raw2937step4 := by apply Matrix.ext; change ∀ i j, raw2937step5 i j = -(raw2937step4 i j); unfold raw2937step5 raw2937step4; decide +kernel
      have hl : raw2937step5Labels = raw2937step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2938 raw2938Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2938 raw2938Labels = mixedMoment B raw2938step0 raw2938step0Labels := by
      have hz : ∀ j, raw2938 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2938step0 = (fun i j => raw2938 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2938step0 raw2938; decide +kernel
      have hl : raw2938step0Labels = raw2938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2938 raw2938Labels permutation434 hz
    mixedMoment B raw2938step0 raw2938step0Labels = mixedMoment B raw2938step1 raw2938step1Labels := by
      have hz : ∀ j, raw2938step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2938step1 = (fun i j => raw2938step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2938step1 raw2938step0; decide +kernel
      have hl : raw2938step1Labels = raw2938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2938step0 raw2938step0Labels permutation80 hz
    mixedMoment B raw2938step1 raw2938step1Labels = mixedMoment B raw2938step2 raw2938step2Labels := by
      have hz : ∀ j, raw2938step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2938step2 = (fun i j => raw2938step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2938step2 raw2938step1; decide +kernel
      have hl : raw2938step2Labels = raw2938step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2938step1 raw2938step1Labels permutation14 hz
    mixedMoment B raw2938step2 raw2938step2Labels = mixedMoment B raw2938step3 raw2938step3Labels := by
      have hz : ∀ i, raw2938step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2938step3 = (fun i j => raw2938step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2938step3 raw2938step2; decide +kernel
      have hl : raw2938step3Labels = (fun j => raw2938step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2938step2 raw2938step2Labels permutation6 hz
    mixedMoment B raw2938step3 raw2938step3Labels = mixedMoment B raw2938step4 raw2938step4Labels := by
      have ha : raw2938step4 = (fun i j => raw2938step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2938step4 raw2938step3; decide +kernel
      have hl : raw2938step4Labels = raw2938step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2938step3 raw2938step3Labels permutation7 permutation0
    mixedMoment B raw2938step4 raw2938step4Labels = mixedMoment B raw2938step5 raw2938step5Labels := by
      have ha : raw2938step5 = -raw2938step4 := by apply Matrix.ext; change ∀ i j, raw2938step5 i j = -(raw2938step4 i j); unfold raw2938step5 raw2938step4; decide +kernel
      have hl : raw2938step5Labels = raw2938step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

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

theorem canonical660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw660 raw660Labels = mixedMoment B node4093 node4093Labels := by
  calc
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw661 raw661Labels = mixedMoment B node5 node5Labels := by
  calc
    _ = mixedMoment B node5 node5Labels := by rfl

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

theorem canonical5190 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5190 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw5190 = injectiveMoment H raw5190step0 := by
      have heq : raw5190step0 = (fun i j => raw5190 (permutation39 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5190 permutation39 permutation1
    _ = injectiveMoment H node232 := by rfl

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

theorem canonical5165 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5165 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5165 = injectiveMoment H raw5165step0 := by
      have hz : ∀ j, raw5165 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5165step0 = (fun i j => raw5165 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5165 permutation104 hz
    injectiveMoment H raw5165step0 = injectiveMoment H raw5165step1 := by
      have hz : ∀ j, raw5165step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5165step1 = (fun i j => raw5165step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5165step0 permutation21 hz
    injectiveMoment H raw5165step1 = injectiveMoment H raw5165step2 := by
      have hz : ∀ j, raw5165step1 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5165step2 = (fun i j => raw5165step1 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5165step1 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5 node5Labels = Sparse.eval singlePairValue5 (familyPairVector B) := by
  have hp := single_label_two B hB node5
  have hl : node5Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node5 (EqualityPatterns.family2.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node5 (EqualityPatterns.family2.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family2_0]
      apply Matrix.ext
      unfold node5 PairSemantics.raw7979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node5 (EqualityPatterns.family2.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node5 (EqualityPatterns.family2.label 1) = PairSemantics.raw5199 := by
      rw [groupedColumns_family2_1]
      apply Matrix.ext
      unfold node5 PairSemantics.raw5199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  rw [hm0, hm1] at hp
  norm_num [singlePairValue5, PairSemantics.value0, PairSemantics.value11, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3960 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3960 = injectiveMoment H node655 := by
  calc
    injectiveMoment H raw3960 = injectiveMoment H raw3960step0 := by
      have heq : raw3960step0 = -raw3960 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3960).symm
    injectiveMoment H raw3960step0 = injectiveMoment H raw3960step1 := by
      have heq : raw3960step1 = (fun i j => raw3960step0 (permutation33 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3960step0 permutation33 permutation8
    _ = injectiveMoment H node655 := by rfl

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

theorem canonical3975 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3975 = injectiveMoment H node704 := by
  calc
    injectiveMoment H raw3975 = injectiveMoment H raw3975step0 := by
      have heq : raw3975step0 = (fun i j => raw3975 (permutation83 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3975 permutation83 permutation5
    _ = injectiveMoment H node704 := by rfl

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

theorem canonical4096 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4096 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4096 = injectiveMoment H raw4096step0 := by
      have hz : ∀ j, raw4096 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw4096step0 = (fun i j => raw4096 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4096 permutation15 hz
    injectiveMoment H raw4096step0 = injectiveMoment H raw4096step1 := by
      have heq : raw4096step1 = (fun i j => raw4096step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4096step0 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

theorem canonical4110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4110 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4110 = injectiveMoment H raw4110step0 := by
      have hz : ∀ j, raw4110 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw4110step0 = (fun i j => raw4110 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4110 permutation21 hz
    injectiveMoment H raw4110step0 = injectiveMoment H raw4110step1 := by
      have heq : raw4110step1 = (fun i j => raw4110step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4110step0 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

theorem canonical4117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4117 = injectiveMoment H node207 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5139 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5139 = injectiveMoment H node232 := by
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

theorem canonical8988 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8988 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8988 = injectiveMoment H raw8988step0 := by
      have hz : ∀ j, raw8988 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8988step0 = (fun i j => raw8988 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8988 permutation128 hz
    injectiveMoment H raw8988step0 = injectiveMoment H raw8988step1 := by
      have hz : ∀ j, raw8988step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw8988step1 = (fun i j => raw8988step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8988step0 permutation27 hz
    injectiveMoment H raw8988step1 = injectiveMoment H raw8988step2 := by
      have hz : ∀ j, raw8988step1 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8988step2 = (fun i j => raw8988step1 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8988step1 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical282
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9030 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9030 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw9030 = injectiveMoment H raw9030step0 := by
      have hz : ∀ j, raw9030 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9030step0 = (fun i j => raw9030 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9030 permutation33 hz
    injectiveMoment H raw9030step0 = injectiveMoment H raw9030step1 := by
      have heq : raw9030step1 = (fun i j => raw9030step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9030step0 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4915 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4915 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw4915 = injectiveMoment H raw4915step0 := by
      have heq : raw4915step0 = -raw4915 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4915).symm
    injectiveMoment H raw4915step0 = injectiveMoment H raw4915step1 := by
      have heq : raw4915step1 = (fun i j => raw4915step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4915step0 permutation32 permutation3
    _ = injectiveMoment H node203 := by rfl

theorem canonical4918 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4918 = injectiveMoment H node224 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5384 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5384 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw5384 = injectiveMoment H raw5384step0 := by
      have heq : raw5384step0 = (fun i j => raw5384 (permutation11 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5384 permutation11 permutation4
    _ = injectiveMoment H node203 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2803 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2803 = injectiveMoment H node176 := by
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

theorem sound224 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node224 = Sparse.eval value224 (momentVector H) := by
  have hc : momentVector H 25 = injectiveMoment H node224 := rfl
  simp [value224, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound10
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound655 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node655 = Sparse.eval value655 (momentVector H) := by
  have heq : pivotMatrix655 = (fun u v => node655 (pivotPermutation655 u) v) := by apply Matrix.ext; unfold pivotMatrix655 node655 pivotPermutation655; decide +kernel
  have hmoment : injectiveMoment H node655 = injectiveMoment H pivotMatrix655 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix655 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix655 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix655 (0 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix655 (0 : Fin 4) = raw2803 := by apply Matrix.ext; unfold mergeFirst pivotMatrix655 raw2803; decide +kernel
    rw [heq]
    exact (canonical2803 hH).trans (sound176 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix655 (1 : Fin 4)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix655 (1 : Fin 4) = raw4096 := by apply Matrix.ext; unfold mergeFirst pivotMatrix655 raw4096; decide +kernel
    rw [heq]
    exact (canonical4096 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix655 (2 : Fin 4)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix655 (2 : Fin 4) = raw4110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix655 raw4110; decide +kernel
    rw [heq]
    exact (canonical4110 hH).trans (sound62 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix655 (3 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix655 (3 : Fin 4) = raw4117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix655 raw4117; decide +kernel
    rw [heq]
    exact (canonical4117 hH).trans (sound207 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node655 + (injectiveMoment H (mergeFirst pivotMatrix655 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix655 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix655 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix655 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value655, value176, value207, value62, Sparse.eval] at hc ⊢
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

theorem sound704 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node704 = Sparse.eval value704 (momentVector H) := by
  have heq : pivotMatrix704 = (fun u v => node704 (pivotPermutation704 u) v) := by apply Matrix.ext; unfold pivotMatrix704 node704 pivotPermutation704; decide +kernel
  have hmoment : injectiveMoment H node704 = injectiveMoment H pivotMatrix704 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix704 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix704 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix704 (0 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix704 (0 : Fin 4) = raw5384 := by apply Matrix.ext; unfold mergeFirst pivotMatrix704 raw5384; decide +kernel
    rw [heq]
    exact (canonical5384 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix704 (1 : Fin 4)) =
      Sparse.eval value227 (momentVector H) := by
    have heq : mergeFirst pivotMatrix704 (1 : Fin 4) = raw4943 := by apply Matrix.ext; unfold mergeFirst pivotMatrix704 raw4943; decide +kernel
    rw [heq]
    exact (canonical4943 hH).trans (sound227 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix704 (2 : Fin 4)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix704 (2 : Fin 4) = raw4918 := by apply Matrix.ext; unfold mergeFirst pivotMatrix704 raw4918; decide +kernel
    rw [heq]
    exact (canonical4918 hH).trans (sound224 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix704 (3 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix704 (3 : Fin 4) = raw4915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix704 raw4915; decide +kernel
    rw [heq]
    exact (canonical4915 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node704 + (injectiveMoment H (mergeFirst pivotMatrix704 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix704 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix704 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix704 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value704, value203, value224, value227, Sparse.eval] at hc ⊢
  linarith

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair494 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node494 node494Labels = Sparse.eval singlePairValue494 (familyPairVector B) := by
  have hp := single_label_three B hB node494
  have hl : node494Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node494 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 1) = PairSemantics.raw5165 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node494 PairSemantics.raw5165; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5165 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 2) = PairSemantics.raw9030 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node494 PairSemantics.raw9030; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9030 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 3) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node494 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value655 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 4) = PairSemantics.raw3960 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node494 PairSemantics.raw3960; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3960 hH).trans (PairSemantics.sound655 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue494, PairSemantics.value0, PairSemantics.value4, PairSemantics.value65, PairSemantics.value232, PairSemantics.value655, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair500 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node500 node500Labels = Sparse.eval singlePairValue500 (familyPairVector B) := by
  have hp := single_label_three B hB node500
  have hl : node500Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node500 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node500 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node500 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node500 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node500 (EqualityPatterns.family3.label 1) = PairSemantics.raw5190 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node500 PairSemantics.raw5190; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5190 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node500 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node500 (EqualityPatterns.family3.label 2) = PairSemantics.raw8988 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node500 PairSemantics.raw8988; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8988 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node500 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node500 (EqualityPatterns.family3.label 3) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node500 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node500 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value704 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node500 (EqualityPatterns.family3.label 4) = PairSemantics.raw3975 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node500 PairSemantics.raw3975; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3975 hH).trans (PairSemantics.sound704 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue500, PairSemantics.value0, PairSemantics.value4, PairSemantics.value232, PairSemantics.value704, Sparse.eval] at hp ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4093 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4093 node4093Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node5 node5Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw660 singletonSmall4093
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4093) = raw660Labels := by decide +kernel
  rw [hl, canonical660 B hB] at h
  have hc0 : mixedMoment B raw660 (Fin.cases (0 : Fin 1) singletonSmall4093) =
      mixedMoment B node5 node5Labels := by
    have ha : raw660 = raw661 := by apply Matrix.ext; unfold raw660 raw661; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4093 = raw661Labels := by decide +kernel
    rw [ha, hj, canonical661 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem sound5 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5 node5Labels = Sparse.eval nodeValue5 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue5 (familyPairVector B) := singlePair5 B _hB
    _ = _ := by norm_num [singlePairValue5, nodeValue5, Sparse.eval, mixedVector]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node494 node494Labels = Sparse.eval nodeValue494 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue494 (familyPairVector B) := singlePair494 B _hB
    _ = _ := by norm_num [singlePairValue494, nodeValue494, Sparse.eval, mixedVector] <;> ring

theorem sound500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node500 node500Labels = Sparse.eval nodeValue500 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue500 (familyPairVector B) := singlePair500 B _hB
    _ = _ := by norm_num [singlePairValue500, nodeValue500, Sparse.eval, mixedVector] <;> ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node524 node524Labels = 0 := by
  exact mixedMoment_alpha B hF node524 node524Labels 1 permutation212
    (by decide +kernel)

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

theorem sound524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node524 node524Labels = Sparse.eval nodeValue524 (mixedVector B) := by
  simpa only [nodeValue524, Sparse.eval_nil] using zero524 B _hB _hF

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

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

theorem sound4093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4093 node4093Labels = Sparse.eval nodeValue4093 (mixedVector B) := by
  have h := singleton4093 B _hB
  rw [sound5 B _hB _hF] at h
  norm_num [nodeValue4093, nodeValue5, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4097 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4097 node4097Labels = 0 := by
  exact mixedMoment_order_one B hB node4097 node4097Labels 0
    (by decide +kernel) (by decide +kernel)

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

theorem sound4097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4097 node4097Labels = Sparse.eval nodeValue4097 (mixedVector B) := by
  simpa only [nodeValue4097, Sparse.eval_nil] using zero4097 B _hB _hF

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

theorem sourceEq8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm8 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA8 + difference 2 0) (sourceB8 + difference 0 2) sourceC8) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 494) := by
    have ha : (tripleCharges (sourceA8 + difference 2 0) (sourceB8 + difference 0 2) sourceC8) = raw2844 := by
      apply Matrix.ext; unfold tripleCharges sourceA8 sourceB8 sourceC8 difference raw2844; decide +kernel
    rw [ha]
    exact (canonical2844 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA8 + difference 2 1) (sourceB8 + difference 1 2) sourceC8) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 500) := by
    have ha : (tripleCharges (sourceA8 + difference 2 1) (sourceB8 + difference 1 2) sourceC8) = raw2845 := by
      apply Matrix.ext; unfold tripleCharges sourceA8 sourceB8 sourceC8 difference raw2845; decide +kernel
    rw [ha]
    exact (canonical2845 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA8 + difference 2 2) (sourceB8 + difference 2 2) sourceC8) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 527) := by
    have ha : (tripleCharges (sourceA8 + difference 2 2) (sourceB8 + difference 2 2) sourceC8) = raw2846 := by
      apply Matrix.ext; unfold tripleCharges sourceA8 sourceB8 sourceC8 difference raw2846; decide +kernel
    rw [ha]
    exact (canonical2846 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA8 + difference 2 3) (sourceB8 + difference 3 2) sourceC8) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 524) := by
    have ha : (tripleCharges (sourceA8 + difference 2 3) (sourceB8 + difference 3 2) sourceC8) = raw2847 := by
      apply Matrix.ext; unfold tripleCharges sourceA8 sourceB8 sourceC8 difference raw2847; decide +kernel
    rw [ha]
    exact (canonical2847 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA8 + difference 2 4) (sourceB8 + difference 4 2) sourceC8) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 527) := by
    have ha : (tripleCharges (sourceA8 + difference 2 4) (sourceB8 + difference 4 2) sourceC8) = raw2848 := by
      apply Matrix.ext; unfold tripleCharges sourceA8 sourceB8 sourceC8 difference raw2848; decide +kernel
    rw [ha]
    exact (canonical2848 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA8 + difference 2 5) (sourceB8 + difference 5 2) sourceC8) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 494) := by
    have ha : (tripleCharges (sourceA8 + difference 2 5) (sourceB8 + difference 5 2) sourceC8) = raw2849 := by
      apply Matrix.ext; unfold tripleCharges sourceA8 sourceB8 sourceC8 difference raw2849; decide +kernel
    rw [ha]
    exact (canonical2849 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA8 + sourceB8) sourceC8) (![0, 0] : Fin 2 → Fin 1) =
      mixedVector B (Sum.inr 6) := by
    have ha : (doubleCharges (sourceA8 + sourceB8) sourceC8) = raw2850 := by
      apply Matrix.ext; unfold doubleCharges sourceA8 sourceB8 sourceC8 raw2850; decide +kernel
    rw [ha]
    exact (canonical2850 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA8 sourceB8 sourceC8
    (0 : Fin 1) 0 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm8, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm11 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA11 + difference 0 1) (sourceB11 + difference 1 0) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA11 + difference 0 1) (sourceB11 + difference 1 0) sourceC11) = raw2909 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2909; decide +kernel
    rw [ha]
    exact (canonical2909 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA11 + difference 0 2) (sourceB11 + difference 2 0) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA11 + difference 0 2) (sourceB11 + difference 2 0) sourceC11) = raw2910 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2910; decide +kernel
    rw [ha]
    exact (canonical2910 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA11 + difference 0 3) (sourceB11 + difference 3 0) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA11 + difference 0 3) (sourceB11 + difference 3 0) sourceC11) = raw2911 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2911; decide +kernel
    rw [ha]
    exact (canonical2911 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA11 + difference 0 4) (sourceB11 + difference 4 0) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA11 + difference 0 4) (sourceB11 + difference 4 0) sourceC11) = raw2912 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2912; decide +kernel
    rw [ha]
    exact (canonical2912 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA11 + difference 0 5) (sourceB11 + difference 5 0) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4097) := by
    have ha : (tripleCharges (sourceA11 + difference 0 5) (sourceB11 + difference 5 0) sourceC11) = raw2913 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2913; decide +kernel
    rw [ha]
    exact (canonical2913 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA11 + difference 1 0) (sourceB11 + difference 0 1) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA11 + difference 1 0) (sourceB11 + difference 0 1) sourceC11) = raw2914 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2914; decide +kernel
    rw [ha]
    exact (canonical2914 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA11 + difference 1 2) (sourceB11 + difference 2 1) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 1 2) (sourceB11 + difference 2 1) sourceC11) = raw2915 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2915; decide +kernel
    rw [ha]
    exact (canonical2915 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA11 + difference 1 3) (sourceB11 + difference 3 1) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 1 3) (sourceB11 + difference 3 1) sourceC11) = raw2916 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2916; decide +kernel
    rw [ha]
    exact (canonical2916 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA11 + difference 1 4) (sourceB11 + difference 4 1) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 1 4) (sourceB11 + difference 4 1) sourceC11) = raw2917 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2917; decide +kernel
    rw [ha]
    exact (canonical2917 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA11 + difference 1 5) (sourceB11 + difference 5 1) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA11 + difference 1 5) (sourceB11 + difference 5 1) sourceC11) = raw2918 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2918; decide +kernel
    rw [ha]
    exact (canonical2918 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA11 + difference 2 0) (sourceB11 + difference 0 2) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA11 + difference 2 0) (sourceB11 + difference 0 2) sourceC11) = raw2919 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2919; decide +kernel
    rw [ha]
    exact (canonical2919 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA11 + difference 2 1) (sourceB11 + difference 1 2) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 2 1) (sourceB11 + difference 1 2) sourceC11) = raw2920 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2920; decide +kernel
    rw [ha]
    exact (canonical2920 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA11 + difference 2 3) (sourceB11 + difference 3 2) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 2 3) (sourceB11 + difference 3 2) sourceC11) = raw2921 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2921; decide +kernel
    rw [ha]
    exact (canonical2921 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA11 + difference 2 4) (sourceB11 + difference 4 2) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 2 4) (sourceB11 + difference 4 2) sourceC11) = raw2922 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2922; decide +kernel
    rw [ha]
    exact (canonical2922 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA11 + difference 2 5) (sourceB11 + difference 5 2) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA11 + difference 2 5) (sourceB11 + difference 5 2) sourceC11) = raw2923 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2923; decide +kernel
    rw [ha]
    exact (canonical2923 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA11 + difference 3 0) (sourceB11 + difference 0 3) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA11 + difference 3 0) (sourceB11 + difference 0 3) sourceC11) = raw2924 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2924; decide +kernel
    rw [ha]
    exact (canonical2924 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA11 + difference 3 1) (sourceB11 + difference 1 3) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 3 1) (sourceB11 + difference 1 3) sourceC11) = raw2925 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2925; decide +kernel
    rw [ha]
    exact (canonical2925 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA11 + difference 3 2) (sourceB11 + difference 2 3) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 3 2) (sourceB11 + difference 2 3) sourceC11) = raw2926 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2926; decide +kernel
    rw [ha]
    exact (canonical2926 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA11 + difference 3 4) (sourceB11 + difference 4 3) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 3 4) (sourceB11 + difference 4 3) sourceC11) = raw2927 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2927; decide +kernel
    rw [ha]
    exact (canonical2927 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA11 + difference 3 5) (sourceB11 + difference 5 3) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA11 + difference 3 5) (sourceB11 + difference 5 3) sourceC11) = raw2928 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2928; decide +kernel
    rw [ha]
    exact (canonical2928 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA11 + difference 4 0) (sourceB11 + difference 0 4) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA11 + difference 4 0) (sourceB11 + difference 0 4) sourceC11) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA11 + difference 4 1) (sourceB11 + difference 1 4) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 4 1) (sourceB11 + difference 1 4) sourceC11) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA11 + difference 4 2) (sourceB11 + difference 2 4) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 4 2) (sourceB11 + difference 2 4) sourceC11) = raw2931 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2931; decide +kernel
    rw [ha]
    exact (canonical2931 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA11 + difference 4 3) (sourceB11 + difference 3 4) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 4 3) (sourceB11 + difference 3 4) sourceC11) = raw2932 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2932; decide +kernel
    rw [ha]
    exact (canonical2932 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA11 + difference 4 5) (sourceB11 + difference 5 4) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA11 + difference 4 5) (sourceB11 + difference 5 4) sourceC11) = raw2933 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2933; decide +kernel
    rw [ha]
    exact (canonical2933 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA11 + difference 5 0) (sourceB11 + difference 0 5) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA11 + difference 5 0) (sourceB11 + difference 0 5) sourceC11) = raw2934 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2934; decide +kernel
    rw [ha]
    exact (canonical2934 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA11 + difference 5 1) (sourceB11 + difference 1 5) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA11 + difference 5 1) (sourceB11 + difference 1 5) sourceC11) = raw2935 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2935; decide +kernel
    rw [ha]
    exact (canonical2935 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA11 + difference 5 2) (sourceB11 + difference 2 5) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA11 + difference 5 2) (sourceB11 + difference 2 5) sourceC11) = raw2936 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2936; decide +kernel
    rw [ha]
    exact (canonical2936 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA11 + difference 5 3) (sourceB11 + difference 3 5) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA11 + difference 5 3) (sourceB11 + difference 3 5) sourceC11) = raw2937 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2937; decide +kernel
    rw [ha]
    exact (canonical2937 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA11 + difference 5 4) (sourceB11 + difference 4 5) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA11 + difference 5 4) (sourceB11 + difference 4 5) sourceC11) = raw2938 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2938; decide +kernel
    rw [ha]
    exact (canonical2938 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA11 sourceB11 sourceC11
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm11, Integer.Sparse.eval]
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

theorem reindexCheck8 : Integer.Sparse.reindex keyMap MixedData.row8 = numericRow8 := by decide +kernel

theorem numericCheck8 (x : Master → ℝ) : Integer.Sparse.eval numericRow8 x =
    (432 : ℝ) * reducedSource8 x := by
  norm_num [numericRow8, reducedSource8, Integer.Sparse.eval, Sparse.eval, nodeValue6, nodeValue494, nodeValue500, nodeValue524, nodeValue527]
  ring

theorem reindexCheck11 : Integer.Sparse.reindex keyMap MixedData.row11 = numericRow11 := by decide +kernel

theorem numericCheck11 (x : Master → ℝ) : Integer.Sparse.eval numericRow11 x =
    (3 : ℝ) * reducedSource11 x := by
  norm_num [numericRow11, reducedSource11, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4085, nodeValue4092, nodeValue4093, nodeValue4097]
  ring

theorem reindexCheck14 : Integer.Sparse.reindex keyMap MixedData.row14 = numericRow14 := by decide +kernel

theorem numericCheck14 (x : Master → ℝ) : Integer.Sparse.eval numericRow14 x =
    (1440 : ℝ) * reducedSource14 x := by
  norm_num [numericRow14, reducedSource14, Integer.Sparse.eval, Sparse.eval, nodeValue4887, nodeValue4888, nodeValue5405, nodeValue5433, nodeValue5434, nodeValue5439, nodeValue5498, nodeValue5499]
  ring

theorem reindexCheck15 : Integer.Sparse.reindex keyMap MixedData.row15 = numericRow15 := by decide +kernel

theorem numericCheck15 (x : Master → ℝ) : Integer.Sparse.eval numericRow15 x =
    (8640 : ℝ) * reducedSource15 x := by
  norm_num [numericRow15, reducedSource15, Integer.Sparse.eval, Sparse.eval, nodeValue5290, nodeValue5291, nodeValue5294, nodeValue5304, nodeValue5434, nodeValue5438, nodeValue5442, nodeValue5443, nodeValue5450, nodeValue5451, nodeValue5454, nodeValue5455, nodeValue5481, nodeValue5484, nodeValue5485, nodeValue5490, nodeValue5492, nodeValue5493, nodeValue5494, nodeValue5495]
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

theorem reducedZero8 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource8 (mixedVector B) = 0 := by
  have h6 : mixedVector B (Sum.inr 6) = Sparse.eval nodeValue6 (mixedVector B) := by
    change mixedMoment B node6 node6Labels = _
    exact sound6 B hB hF
  have h494 : mixedVector B (Sum.inr 494) = Sparse.eval nodeValue494 (mixedVector B) := by
    change mixedMoment B node494 node494Labels = _
    exact sound494 B hB hF
  have h500 : mixedVector B (Sum.inr 500) = Sparse.eval nodeValue500 (mixedVector B) := by
    change mixedMoment B node500 node500Labels = _
    exact sound500 B hB hF
  have h524 : mixedVector B (Sum.inr 524) = Sparse.eval nodeValue524 (mixedVector B) := by
    change mixedMoment B node524 node524Labels = _
    exact sound524 B hB hF
  have h527 : mixedVector B (Sum.inr 527) = Sparse.eval nodeValue527 (mixedVector B) := by
    change mixedMoment B node527 node527Labels = _
    exact sound527 B hB hF
  simpa only [sourceForm8, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h6, h494, h500, h524, h527, reducedSource8] using sourceEq8 B hB

theorem rowSound8 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row8 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck8, numericCheck8, reducedZero8 B hB hF, mul_zero]

theorem reducedZero11 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource11 (mixedVector B) = 0 := by
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  have h4093 : mixedVector B (Sum.inr 4093) = Sparse.eval nodeValue4093 (mixedVector B) := by
    change mixedMoment B node4093 node4093Labels = _
    exact sound4093 B hB hF
  have h4097 : mixedVector B (Sum.inr 4097) = Sparse.eval nodeValue4097 (mixedVector B) := by
    change mixedMoment B node4097 node4097Labels = _
    exact sound4097 B hB hF
  simpa only [sourceForm11, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4084, h4085, h4092, h4093, h4097, reducedSource11] using sourceEq11 B hB

theorem rowSound11 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row11 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck11, numericCheck11, reducedZero11 B hB hF, mul_zero]

theorem rowSound14 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row14 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck14, numericCheck14, reducedZero14_e B hB hF, mul_zero]

theorem rowSound15 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row15 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck15, numericCheck15, reducedZero15_e B hB hF, mul_zero]

theorem sourceRowsAt0 : MixedData.sourceRows (0 : Fin 2425) =
    MixedData.row0 := by decide +kernel

theorem sourceRowsAt1 : MixedData.sourceRows (1 : Fin 2425) =
    MixedData.row1 := by decide +kernel

theorem sourceRowsAt2 : MixedData.sourceRows (2 : Fin 2425) =
    MixedData.row2 := by decide +kernel

theorem sourceRowsAt3 : MixedData.sourceRows (3 : Fin 2425) =
    MixedData.row3 := by decide +kernel

theorem sourceRowsAt4 : MixedData.sourceRows (4 : Fin 2425) =
    MixedData.row4 := by decide +kernel

theorem sourceRowsAt5 : MixedData.sourceRows (5 : Fin 2425) =
    MixedData.row5 := by decide +kernel

theorem sourceRowsAt6 : MixedData.sourceRows (6 : Fin 2425) =
    MixedData.row6 := by decide +kernel

theorem sourceRowsAt7 : MixedData.sourceRows (7 : Fin 2425) =
    MixedData.row7 := by decide +kernel

theorem sourceRowsAt8 : MixedData.sourceRows (8 : Fin 2425) =
    MixedData.row8 := by decide +kernel

theorem sourceRowsAt9 : MixedData.sourceRows (9 : Fin 2425) =
    MixedData.row9 := by decide +kernel

theorem sourceRowsAt10 : MixedData.sourceRows (10 : Fin 2425) =
    MixedData.row10 := by decide +kernel

theorem sourceRowsAt11 : MixedData.sourceRows (11 : Fin 2425) =
    MixedData.row11 := by decide +kernel

theorem sourceRowsAt12 : MixedData.sourceRows (12 : Fin 2425) =
    MixedData.row12 := by decide +kernel

theorem sourceRowsAt13 : MixedData.sourceRows (13 : Fin 2425) =
    MixedData.row13 := by decide +kernel

theorem sourceRowsAt14 : MixedData.sourceRows (14 : Fin 2425) =
    MixedData.row14 := by decide +kernel

theorem sourceRowsAt15 : MixedData.sourceRows (15 : Fin 2425) =
    MixedData.row15 := by decide +kernel

theorem chunkSound0_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 0) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 ∨ k.val = 4 ∨ k.val = 5 ∨ k.val = 6 ∨ k.val = 7 ∨ k.val = 8 ∨ k.val = 9 ∨ k.val = 10 ∨ k.val = 11 ∨ k.val = 12 ∨ k.val = 13 ∨ k.val = 14 ∨ k.val = 15 := by omega
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  · have he : k = (0 : Fin 2425) := Fin.ext h0
    subst k
    rw [sourceRowsAt0]
    exact rowSound0_e B hB hF
  · have he : k = (1 : Fin 2425) := Fin.ext h1
    subst k
    rw [sourceRowsAt1]
    exact rowSound1_e B hB hF
  · have he : k = (2 : Fin 2425) := Fin.ext h2
    subst k
    rw [sourceRowsAt2]
    exact rowSound2_e B hB hF
  · have he : k = (3 : Fin 2425) := Fin.ext h3
    subst k
    rw [sourceRowsAt3]
    exact rowSound3_e B hB hF
  · have he : k = (4 : Fin 2425) := Fin.ext h4
    subst k
    rw [sourceRowsAt4]
    exact rowSound4_e B hB hF
  · have he : k = (5 : Fin 2425) := Fin.ext h5
    subst k
    rw [sourceRowsAt5]
    exact rowSound5_e B hB hF
  · have he : k = (6 : Fin 2425) := Fin.ext h6
    subst k
    rw [sourceRowsAt6]
    exact rowSound6_e B hB hF
  · have he : k = (7 : Fin 2425) := Fin.ext h7
    subst k
    rw [sourceRowsAt7]
    exact rowSound7_e B hB hF
  · have he : k = (8 : Fin 2425) := Fin.ext h8
    subst k
    rw [sourceRowsAt8]
    exact rowSound8 B hB hF
  · have he : k = (9 : Fin 2425) := Fin.ext h9
    subst k
    rw [sourceRowsAt9]
    exact rowSound9_e B hB hF
  · have he : k = (10 : Fin 2425) := Fin.ext h10
    subst k
    rw [sourceRowsAt10]
    exact rowSound10_e B hB hF
  · have he : k = (11 : Fin 2425) := Fin.ext h11
    subst k
    rw [sourceRowsAt11]
    exact rowSound11 B hB hF
  · have he : k = (12 : Fin 2425) := Fin.ext h12
    subst k
    rw [sourceRowsAt12]
    exact rowSound12_e B hB hF
  · have he : k = (13 : Fin 2425) := Fin.ext h13
    subst k
    rw [sourceRowsAt13]
    exact rowSound13_e B hB hF
  · have he : k = (14 : Fin 2425) := Fin.ext h14
    subst k
    rw [sourceRowsAt14]
    exact rowSound14 B hB hF
  · have he : k = (15 : Fin 2425) := Fin.ext h15
    subst k
    rw [sourceRowsAt15]
    exact rowSound15 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e_oai
