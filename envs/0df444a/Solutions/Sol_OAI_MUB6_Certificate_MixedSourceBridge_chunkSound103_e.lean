-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:39:39.809045+00:00
-- url     : https://prove2.me/submissions/1ad85f58-8dbc-4816-9d49-83beeba04a82

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5174_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1648_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1649_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1650_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1651_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1652_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1653_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1654_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1655_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1656_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1662_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1284 raw1284Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw1284 raw1284Labels = mixedMoment B raw1284step0 raw1284step0Labels := by
      have ha : raw1284step0 = (fun i j => raw1284 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1284step0 raw1284; decide +kernel
      have hl : raw1284step0Labels = raw1284Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1284 raw1284Labels permutation8 permutation4
    mixedMoment B raw1284step0 raw1284step0Labels = mixedMoment B raw1284step1 raw1284step1Labels := by
      have ha : raw1284step1 = raw1284step0 := by apply Matrix.ext; unfold raw1284step1 raw1284step0; decide +kernel
      have hl : raw1284step0Labels = labelEmbedding7 ∘ raw1284step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1284step0 raw1284step0Labels raw1284step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

theorem canonical1285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1285 raw1285Labels = mixedMoment B node1074 node1074Labels := by
  calc
    mixedMoment B raw1285 raw1285Labels = mixedMoment B raw1285step0 raw1285step0Labels := by
      have ha : raw1285step0 = (fun i j => raw1285 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1285step0 raw1285; decide +kernel
      have hl : raw1285step0Labels = raw1285Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1285 raw1285Labels permutation8 permutation4
    _ = mixedMoment B node1074 node1074Labels := by rfl

theorem canonical1286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1286 raw1286Labels = mixedMoment B node1650 node1650Labels := by
  calc
    mixedMoment B raw1286 raw1286Labels = mixedMoment B raw1286step0 raw1286step0Labels := by
      have ha : raw1286step0 = (fun i j => raw1286 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1286step0 raw1286; decide +kernel
      have hl : raw1286step0Labels = raw1286Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1286 raw1286Labels permutation8 permutation6
    mixedMoment B raw1286step0 raw1286step0Labels = mixedMoment B raw1286step1 raw1286step1Labels := by
      have ha : raw1286step1 = -raw1286step0 := by apply Matrix.ext; change ∀ i j, raw1286step1 i j = -(raw1286step0 i j); unfold raw1286step1 raw1286step0; decide +kernel
      have hl : raw1286step1Labels = raw1286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1286step1 raw1286step1Labels = mixedMoment B raw1286step2 raw1286step2Labels := by
      have ha : raw1286step2 = raw1286step1 := by apply Matrix.ext; unfold raw1286step2 raw1286step1; decide +kernel
      have hl : raw1286step1Labels = labelEmbedding1 ∘ raw1286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1286step1 raw1286step1Labels raw1286step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1650 node1650Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1743 raw1743Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw1743 raw1743Labels = mixedMoment B raw1743step0 raw1743step0Labels := by
      have ha : raw1743step0 = (fun i j => raw1743 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1743step0 raw1743; decide +kernel
      have hl : raw1743step0Labels = raw1743Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1743 raw1743Labels permutation32 permutation4
    mixedMoment B raw1743step0 raw1743step0Labels = mixedMoment B raw1743step1 raw1743step1Labels := by
      have ha : raw1743step1 = raw1743step0 := by apply Matrix.ext; unfold raw1743step1 raw1743step0; decide +kernel
      have hl : raw1743step0Labels = labelEmbedding7 ∘ raw1743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1743step0 raw1743step0Labels raw1743step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical1744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1744 raw1744Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw1744 raw1744Labels = mixedMoment B raw1744step0 raw1744step0Labels := by
      have ha : raw1744step0 = (fun i j => raw1744 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1744step0 raw1744; decide +kernel
      have hl : raw1744step0Labels = raw1744Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1744 raw1744Labels permutation32 permutation4
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical1745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1745 raw1745Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw1745 raw1745Labels = mixedMoment B raw1745step0 raw1745step0Labels := by
      have ha : raw1745step0 = (fun i j => raw1745 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1745step0 raw1745; decide +kernel
      have hl : raw1745step0Labels = raw1745Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1745 raw1745Labels permutation32 permutation6
    mixedMoment B raw1745step0 raw1745step0Labels = mixedMoment B raw1745step1 raw1745step1Labels := by
      have ha : raw1745step1 = -raw1745step0 := by apply Matrix.ext; change ∀ i j, raw1745step1 i j = -(raw1745step0 i j); unfold raw1745step1 raw1745step0; decide +kernel
      have hl : raw1745step1Labels = raw1745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1745step1 raw1745step1Labels = mixedMoment B raw1745step2 raw1745step2Labels := by
      have ha : raw1745step2 = raw1745step1 := by apply Matrix.ext; unfold raw1745step2 raw1745step1; decide +kernel
      have hl : raw1745step1Labels = labelEmbedding1 ∘ raw1745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1745step1 raw1745step1Labels raw1745step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical1755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1755 raw1755Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw1755 raw1755Labels = mixedMoment B raw1755step0 raw1755step0Labels := by
      have ha : raw1755step0 = (fun i j => raw1755 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1755step0 raw1755; decide +kernel
      have hl : raw1755step0Labels = raw1755Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1755 raw1755Labels permutation32 permutation4
    mixedMoment B raw1755step0 raw1755step0Labels = mixedMoment B raw1755step1 raw1755step1Labels := by
      have ha : raw1755step1 = raw1755step0 := by apply Matrix.ext; unfold raw1755step1 raw1755step0; decide +kernel
      have hl : raw1755step0Labels = labelEmbedding7 ∘ raw1755step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1755step0 raw1755step0Labels raw1755step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

theorem canonical1756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1756 raw1756Labels = mixedMoment B node2047 node2047Labels := by
  calc
    mixedMoment B raw1756 raw1756Labels = mixedMoment B raw1756step0 raw1756step0Labels := by
      have ha : raw1756step0 = (fun i j => raw1756 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1756step0 raw1756; decide +kernel
      have hl : raw1756step0Labels = raw1756Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1756 raw1756Labels permutation32 permutation4
    _ = mixedMoment B node2047 node2047Labels := by rfl

theorem canonical1757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1757 raw1757Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw1757 raw1757Labels = mixedMoment B raw1757step0 raw1757step0Labels := by
      have ha : raw1757step0 = (fun i j => raw1757 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1757step0 raw1757; decide +kernel
      have hl : raw1757step0Labels = raw1757Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1757 raw1757Labels permutation38 permutation6
    mixedMoment B raw1757step0 raw1757step0Labels = mixedMoment B raw1757step1 raw1757step1Labels := by
      have ha : raw1757step1 = -raw1757step0 := by apply Matrix.ext; change ∀ i j, raw1757step1 i j = -(raw1757step0 i j); unfold raw1757step1 raw1757step0; decide +kernel
      have hl : raw1757step1Labels = raw1757step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1757step1 raw1757step1Labels = mixedMoment B raw1757step2 raw1757step2Labels := by
      have ha : raw1757step2 = raw1757step1 := by apply Matrix.ext; unfold raw1757step2 raw1757step1; decide +kernel
      have hl : raw1757step1Labels = labelEmbedding1 ∘ raw1757step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1757step1 raw1757step1Labels raw1757step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2079 node2079Labels := by rfl

theorem canonical1773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1773 raw1773Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw1773 raw1773Labels = mixedMoment B raw1773step0 raw1773step0Labels := by
      have ha : raw1773step0 = (fun i j => raw1773 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1773step0 raw1773; decide +kernel
      have hl : raw1773step0Labels = raw1773Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1773 raw1773Labels permutation8 permutation4
    mixedMoment B raw1773step0 raw1773step0Labels = mixedMoment B raw1773step1 raw1773step1Labels := by
      have ha : raw1773step1 = raw1773step0 := by apply Matrix.ext; unfold raw1773step1 raw1773step0; decide +kernel
      have hl : raw1773step0Labels = labelEmbedding7 ∘ raw1773step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1773step0 raw1773step0Labels raw1773step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

theorem canonical1774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1774 raw1774Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw1774 raw1774Labels = mixedMoment B raw1774step0 raw1774step0Labels := by
      have ha : raw1774step0 = (fun i j => raw1774 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1774step0 raw1774; decide +kernel
      have hl : raw1774step0Labels = raw1774Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1774 raw1774Labels permutation8 permutation4
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical1775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1775 raw1775Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw1775 raw1775Labels = mixedMoment B raw1775step0 raw1775step0Labels := by
      have ha : raw1775step0 = (fun i j => raw1775 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1775step0 raw1775; decide +kernel
      have hl : raw1775step0Labels = raw1775Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1775 raw1775Labels permutation9 permutation6
    mixedMoment B raw1775step0 raw1775step0Labels = mixedMoment B raw1775step1 raw1775step1Labels := by
      have ha : raw1775step1 = -raw1775step0 := by apply Matrix.ext; change ∀ i j, raw1775step1 i j = -(raw1775step0 i j); unfold raw1775step1 raw1775step0; decide +kernel
      have hl : raw1775step1Labels = raw1775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1775step1 raw1775step1Labels = mixedMoment B raw1775step2 raw1775step2Labels := by
      have ha : raw1775step2 = raw1775step1 := by apply Matrix.ext; unfold raw1775step2 raw1775step1; decide +kernel
      have hl : raw1775step1Labels = labelEmbedding1 ∘ raw1775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1775step1 raw1775step1Labels raw1775step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

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

theorem canonical1794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1794 raw1794Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw1794 raw1794Labels = mixedMoment B raw1794step0 raw1794step0Labels := by
      have ha : raw1794step0 = (fun i j => raw1794 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1794step0 raw1794; decide +kernel
      have hl : raw1794step0Labels = raw1794Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1794 raw1794Labels permutation32 permutation4
    mixedMoment B raw1794step0 raw1794step0Labels = mixedMoment B raw1794step1 raw1794step1Labels := by
      have ha : raw1794step1 = raw1794step0 := by apply Matrix.ext; unfold raw1794step1 raw1794step0; decide +kernel
      have hl : raw1794step0Labels = labelEmbedding7 ∘ raw1794step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1794step0 raw1794step0Labels raw1794step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical1795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1795 raw1795Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw1795 raw1795Labels = mixedMoment B raw1795step0 raw1795step0Labels := by
      have ha : raw1795step0 = (fun i j => raw1795 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1795step0 raw1795; decide +kernel
      have hl : raw1795step0Labels = raw1795Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1795 raw1795Labels permutation32 permutation4
    _ = mixedMoment B node2107 node2107Labels := by rfl

theorem canonical1796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1796 raw1796Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw1796 raw1796Labels = mixedMoment B raw1796step0 raw1796step0Labels := by
      have ha : raw1796step0 = (fun i j => raw1796 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1796step0 raw1796; decide +kernel
      have hl : raw1796step0Labels = raw1796Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1796 raw1796Labels permutation38 permutation6
    mixedMoment B raw1796step0 raw1796step0Labels = mixedMoment B raw1796step1 raw1796step1Labels := by
      have ha : raw1796step1 = -raw1796step0 := by apply Matrix.ext; change ∀ i j, raw1796step1 i j = -(raw1796step0 i j); unfold raw1796step1 raw1796step0; decide +kernel
      have hl : raw1796step1Labels = raw1796step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1796step1 raw1796step1Labels = mixedMoment B raw1796step2 raw1796step2Labels := by
      have ha : raw1796step2 = raw1796step1 := by apply Matrix.ext; unfold raw1796step2 raw1796step1; decide +kernel
      have hl : raw1796step1Labels = labelEmbedding1 ∘ raw1796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1796step1 raw1796step1Labels raw1796step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical1797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1797 raw1797Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw1797 raw1797Labels = mixedMoment B raw1797step0 raw1797step0Labels := by
      have ha : raw1797step0 = (fun i j => raw1797 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1797step0 raw1797; decide +kernel
      have hl : raw1797step0Labels = raw1797Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1797 raw1797Labels permutation8 permutation4
    mixedMoment B raw1797step0 raw1797step0Labels = mixedMoment B raw1797step1 raw1797step1Labels := by
      have ha : raw1797step1 = raw1797step0 := by apply Matrix.ext; unfold raw1797step1 raw1797step0; decide +kernel
      have hl : raw1797step0Labels = labelEmbedding7 ∘ raw1797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1797step0 raw1797step0Labels raw1797step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical1798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1798 raw1798Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw1798 raw1798Labels = mixedMoment B raw1798step0 raw1798step0Labels := by
      have ha : raw1798step0 = (fun i j => raw1798 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1798step0 raw1798; decide +kernel
      have hl : raw1798step0Labels = raw1798Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1798 raw1798Labels permutation8 permutation4
    _ = mixedMoment B node2109 node2109Labels := by rfl

theorem canonical1799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1799 raw1799Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw1799 raw1799Labels = mixedMoment B raw1799step0 raw1799step0Labels := by
      have ha : raw1799step0 = (fun i j => raw1799 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1799step0 raw1799; decide +kernel
      have hl : raw1799step0Labels = raw1799Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1799 raw1799Labels permutation10 permutation6
    mixedMoment B raw1799step0 raw1799step0Labels = mixedMoment B raw1799step1 raw1799step1Labels := by
      have ha : raw1799step1 = -raw1799step0 := by apply Matrix.ext; change ∀ i j, raw1799step1 i j = -(raw1799step0 i j); unfold raw1799step1 raw1799step0; decide +kernel
      have hl : raw1799step1Labels = raw1799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1799step1 raw1799step1Labels = mixedMoment B raw1799step2 raw1799step2Labels := by
      have ha : raw1799step2 = raw1799step1 := by apply Matrix.ext; unfold raw1799step2 raw1799step1; decide +kernel
      have hl : raw1799step1Labels = labelEmbedding1 ∘ raw1799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1799step1 raw1799step1Labels raw1799step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical1809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1809 raw1809Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw1809 raw1809Labels = mixedMoment B raw1809step0 raw1809step0Labels := by
      have ha : raw1809step0 = (fun i j => raw1809 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1809step0 raw1809; decide +kernel
      have hl : raw1809step0Labels = raw1809Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1809 raw1809Labels permutation8 permutation4
    mixedMoment B raw1809step0 raw1809step0Labels = mixedMoment B raw1809step1 raw1809step1Labels := by
      have ha : raw1809step1 = raw1809step0 := by apply Matrix.ext; unfold raw1809step1 raw1809step0; decide +kernel
      have hl : raw1809step0Labels = labelEmbedding7 ∘ raw1809step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1809step0 raw1809step0Labels raw1809step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4875 node4875Labels := by rfl

theorem canonical1810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1810 raw1810Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw1810 raw1810Labels = mixedMoment B raw1810step0 raw1810step0Labels := by
      have ha : raw1810step0 = (fun i j => raw1810 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1810step0 raw1810; decide +kernel
      have hl : raw1810step0Labels = raw1810Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1810 raw1810Labels permutation8 permutation4
    _ = mixedMoment B node2116 node2116Labels := by rfl

theorem canonical1811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1811 raw1811Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw1811 raw1811Labels = mixedMoment B raw1811step0 raw1811step0Labels := by
      have ha : raw1811step0 = (fun i j => raw1811 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1811step0 raw1811; decide +kernel
      have hl : raw1811step0Labels = raw1811Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1811 raw1811Labels permutation8 permutation6
    mixedMoment B raw1811step0 raw1811step0Labels = mixedMoment B raw1811step1 raw1811step1Labels := by
      have ha : raw1811step1 = -raw1811step0 := by apply Matrix.ext; change ∀ i j, raw1811step1 i j = -(raw1811step0 i j); unfold raw1811step1 raw1811step0; decide +kernel
      have hl : raw1811step1Labels = raw1811step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1811step1 raw1811step1Labels = mixedMoment B raw1811step2 raw1811step2Labels := by
      have ha : raw1811step2 = raw1811step1 := by apply Matrix.ext; unfold raw1811step2 raw1811step1; decide +kernel
      have hl : raw1811step1Labels = labelEmbedding1 ∘ raw1811step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1811step1 raw1811step1Labels raw1811step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2288 node2288Labels := by rfl

theorem canonical1821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1821 raw1821Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw1821 raw1821Labels = mixedMoment B raw1821step0 raw1821step0Labels := by
      have ha : raw1821step0 = (fun i j => raw1821 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1821step0 raw1821; decide +kernel
      have hl : raw1821step0Labels = raw1821Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1821 raw1821Labels permutation8 permutation4
    mixedMoment B raw1821step0 raw1821step0Labels = mixedMoment B raw1821step1 raw1821step1Labels := by
      have ha : raw1821step1 = raw1821step0 := by apply Matrix.ext; unfold raw1821step1 raw1821step0; decide +kernel
      have hl : raw1821step0Labels = labelEmbedding7 ∘ raw1821step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1821step0 raw1821step0Labels raw1821step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical1822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1822 raw1822Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw1822 raw1822Labels = mixedMoment B raw1822step0 raw1822step0Labels := by
      have ha : raw1822step0 = (fun i j => raw1822 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1822step0 raw1822; decide +kernel
      have hl : raw1822step0Labels = raw1822Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1822 raw1822Labels permutation8 permutation4
    _ = mixedMoment B node2247 node2247Labels := by rfl

theorem canonical1823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1823 raw1823Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw1823 raw1823Labels = mixedMoment B raw1823step0 raw1823step0Labels := by
      have ha : raw1823step0 = (fun i j => raw1823 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1823step0 raw1823; decide +kernel
      have hl : raw1823step0Labels = raw1823Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1823 raw1823Labels permutation8 permutation6
    mixedMoment B raw1823step0 raw1823step0Labels = mixedMoment B raw1823step1 raw1823step1Labels := by
      have ha : raw1823step1 = -raw1823step0 := by apply Matrix.ext; change ∀ i j, raw1823step1 i j = -(raw1823step0 i j); unfold raw1823step1 raw1823step0; decide +kernel
      have hl : raw1823step1Labels = raw1823step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1823step1 raw1823step1Labels = mixedMoment B raw1823step2 raw1823step2Labels := by
      have ha : raw1823step2 = raw1823step1 := by apply Matrix.ext; unfold raw1823step2 raw1823step1; decide +kernel
      have hl : raw1823step1Labels = labelEmbedding1 ∘ raw1823step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1823step1 raw1823step1Labels raw1823step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

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

theorem canonical2133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2133 raw2133Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw2133 raw2133Labels = mixedMoment B raw2133step0 raw2133step0Labels := by
      have ha : raw2133step0 = (fun i j => raw2133 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2133step0 raw2133; decide +kernel
      have hl : raw2133step0Labels = raw2133Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2133 raw2133Labels permutation8 permutation4
    mixedMoment B raw2133step0 raw2133step0Labels = mixedMoment B raw2133step1 raw2133step1Labels := by
      have ha : raw2133step1 = raw2133step0 := by apply Matrix.ext; unfold raw2133step1 raw2133step0; decide +kernel
      have hl : raw2133step0Labels = labelEmbedding7 ∘ raw2133step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2133step0 raw2133step0Labels raw2133step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

theorem canonical2134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2134 raw2134Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw2134 raw2134Labels = mixedMoment B raw2134step0 raw2134step0Labels := by
      have ha : raw2134step0 = (fun i j => raw2134 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2134step0 raw2134; decide +kernel
      have hl : raw2134step0Labels = raw2134Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2134 raw2134Labels permutation8 permutation4
    _ = mixedMoment B node2519 node2519Labels := by rfl

theorem canonical2135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2135 raw2135Labels = mixedMoment B node3486 node3486Labels := by
  calc
    mixedMoment B raw2135 raw2135Labels = mixedMoment B raw2135step0 raw2135step0Labels := by
      have ha : raw2135step0 = (fun i j => raw2135 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2135step0 raw2135; decide +kernel
      have hl : raw2135step0Labels = raw2135Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2135 raw2135Labels permutation9 permutation6
    mixedMoment B raw2135step0 raw2135step0Labels = mixedMoment B raw2135step1 raw2135step1Labels := by
      have ha : raw2135step1 = -raw2135step0 := by apply Matrix.ext; change ∀ i j, raw2135step1 i j = -(raw2135step0 i j); unfold raw2135step1 raw2135step0; decide +kernel
      have hl : raw2135step1Labels = raw2135step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2135step1 raw2135step1Labels = mixedMoment B raw2135step2 raw2135step2Labels := by
      have ha : raw2135step2 = raw2135step1 := by apply Matrix.ext; unfold raw2135step2 raw2135step1; decide +kernel
      have hl : raw2135step1Labels = labelEmbedding1 ∘ raw2135step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2135step1 raw2135step1Labels raw2135step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3486 node3486Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical190
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24400 raw24400Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw24400 raw24400Labels = mixedMoment B raw24400step0 raw24400step0Labels := by
      have hz : ∀ j, raw24400 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24400step0 = (fun i j => raw24400 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24400step0 raw24400; decide +kernel
      have hl : raw24400step0Labels = raw24400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24400 raw24400Labels permutation346 hz
    mixedMoment B raw24400step0 raw24400step0Labels = mixedMoment B raw24400step1 raw24400step1Labels := by
      have hz : ∀ j, raw24400step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24400step1 = (fun i j => raw24400step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24400step1 raw24400step0; decide +kernel
      have hl : raw24400step1Labels = raw24400step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24400step0 raw24400step0Labels permutation56 hz
    mixedMoment B raw24400step1 raw24400step1Labels = mixedMoment B raw24400step2 raw24400step2Labels := by
      have ha : raw24400step2 = (fun i j => raw24400step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24400step2 raw24400step1; decide +kernel
      have hl : raw24400step2Labels = raw24400step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24400step1 raw24400step1Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27642 raw27642Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw27642 raw27642Labels = mixedMoment B raw27642step0 raw27642step0Labels := by
      have hz : ∀ j, raw27642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27642step0 = (fun i j => raw27642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27642step0 raw27642; decide +kernel
      have hl : raw27642step0Labels = raw27642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27642 raw27642Labels permutation434 hz
    mixedMoment B raw27642step0 raw27642step0Labels = mixedMoment B raw27642step1 raw27642step1Labels := by
      have hz : ∀ j, raw27642step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27642step1 = (fun i j => raw27642step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27642step1 raw27642step0; decide +kernel
      have hl : raw27642step1Labels = raw27642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27642step0 raw27642step0Labels permutation80 hz
    mixedMoment B raw27642step1 raw27642step1Labels = mixedMoment B raw27642step2 raw27642step2Labels := by
      have ha : raw27642step2 = (fun i j => raw27642step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27642step2 raw27642step1; decide +kernel
      have hl : raw27642step2Labels = raw27642step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27642step1 raw27642step1Labels permutation31 permutation7
    mixedMoment B raw27642step2 raw27642step2Labels = mixedMoment B raw27642step3 raw27642step3Labels := by
      have ha : raw27642step3 = -raw27642step2 := by apply Matrix.ext; change ∀ i j, raw27642step3 i j = -(raw27642step2 i j); unfold raw27642step3 raw27642step2; decide +kernel
      have hl : raw27642step3Labels = raw27642step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27642step3 raw27642step3Labels = mixedMoment B raw27642step4 raw27642step4Labels := by
      have ha : raw27642step4 = raw27642step3 := by apply Matrix.ext; unfold raw27642step4 raw27642step3; decide +kernel
      have hl : raw27642step3Labels = labelEmbedding10 ∘ raw27642step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27642step3 raw27642step3Labels raw27642step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4841 node4841Labels := by rfl

theorem canonical27647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27647 raw27647Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw27647 raw27647Labels = mixedMoment B raw27647step0 raw27647step0Labels := by
      have hz : ∀ j, raw27647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27647step0 = (fun i j => raw27647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27647step0 raw27647; decide +kernel
      have hl : raw27647step0Labels = raw27647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27647 raw27647Labels permutation434 hz
    mixedMoment B raw27647step0 raw27647step0Labels = mixedMoment B raw27647step1 raw27647step1Labels := by
      have hz : ∀ j, raw27647step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27647step1 = (fun i j => raw27647step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27647step1 raw27647step0; decide +kernel
      have hl : raw27647step1Labels = raw27647step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27647step0 raw27647step0Labels permutation80 hz
    mixedMoment B raw27647step1 raw27647step1Labels = mixedMoment B raw27647step2 raw27647step2Labels := by
      have ha : raw27647step2 = (fun i j => raw27647step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27647step2 raw27647step1; decide +kernel
      have hl : raw27647step2Labels = raw27647step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27647step1 raw27647step1Labels permutation31 permutation7
    mixedMoment B raw27647step2 raw27647step2Labels = mixedMoment B raw27647step3 raw27647step3Labels := by
      have ha : raw27647step3 = -raw27647step2 := by apply Matrix.ext; change ∀ i j, raw27647step3 i j = -(raw27647step2 i j); unfold raw27647step3 raw27647step2; decide +kernel
      have hl : raw27647step3Labels = raw27647step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27647step3 raw27647step3Labels = mixedMoment B raw27647step4 raw27647step4Labels := by
      have ha : raw27647step4 = raw27647step3 := by apply Matrix.ext; unfold raw27647step4 raw27647step3; decide +kernel
      have hl : raw27647step3Labels = labelEmbedding10 ∘ raw27647step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27647step3 raw27647step3Labels raw27647step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical216
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27652 raw27652Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw27652 raw27652Labels = mixedMoment B raw27652step0 raw27652step0Labels := by
      have hz : ∀ j, raw27652 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27652step0 = (fun i j => raw27652 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27652step0 raw27652; decide +kernel
      have hl : raw27652step0Labels = raw27652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27652 raw27652Labels permutation434 hz
    mixedMoment B raw27652step0 raw27652step0Labels = mixedMoment B raw27652step1 raw27652step1Labels := by
      have ha : raw27652step1 = (fun i j => raw27652step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27652step1 raw27652step0; decide +kernel
      have hl : raw27652step1Labels = raw27652step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27652step0 raw27652step0Labels permutation151 permutation7
    mixedMoment B raw27652step1 raw27652step1Labels = mixedMoment B raw27652step2 raw27652step2Labels := by
      have ha : raw27652step2 = -raw27652step1 := by apply Matrix.ext; change ∀ i j, raw27652step2 i j = -(raw27652step1 i j); unfold raw27652step2 raw27652step1; decide +kernel
      have hl : raw27652step2Labels = raw27652step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27652step2 raw27652step2Labels = mixedMoment B raw27652step3 raw27652step3Labels := by
      have ha : raw27652step3 = raw27652step2 := by apply Matrix.ext; unfold raw27652step3 raw27652step2; decide +kernel
      have hl : raw27652step2Labels = labelEmbedding10 ∘ raw27652step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27652step2 raw27652step2Labels raw27652step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical27657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27657 raw27657Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw27657 raw27657Labels = mixedMoment B raw27657step0 raw27657step0Labels := by
      have hz : ∀ j, raw27657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27657step0 = (fun i j => raw27657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27657step0 raw27657; decide +kernel
      have hl : raw27657step0Labels = raw27657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27657 raw27657Labels permutation346 hz
    mixedMoment B raw27657step0 raw27657step0Labels = mixedMoment B raw27657step1 raw27657step1Labels := by
      have ha : raw27657step1 = (fun i j => raw27657step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27657step1 raw27657step0; decide +kernel
      have hl : raw27657step1Labels = raw27657step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27657step0 raw27657step0Labels permutation151 permutation7
    mixedMoment B raw27657step1 raw27657step1Labels = mixedMoment B raw27657step2 raw27657step2Labels := by
      have ha : raw27657step2 = -raw27657step1 := by apply Matrix.ext; change ∀ i j, raw27657step2 i j = -(raw27657step1 i j); unfold raw27657step2 raw27657step1; decide +kernel
      have hl : raw27657step2Labels = raw27657step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27657step2 raw27657step2Labels = mixedMoment B raw27657step3 raw27657step3Labels := by
      have ha : raw27657step3 = raw27657step2 := by apply Matrix.ext; unfold raw27657step3 raw27657step2; decide +kernel
      have hl : raw27657step2Labels = labelEmbedding10 ∘ raw27657step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27657step2 raw27657step2Labels raw27657step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical27658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27658 raw27658Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw27658 raw27658Labels = mixedMoment B raw27658step0 raw27658step0Labels := by
      have hz : ∀ j, raw27658 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27658step0 = (fun i j => raw27658 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27658step0 raw27658; decide +kernel
      have hl : raw27658step0Labels = raw27658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27658 raw27658Labels permutation434 hz
    mixedMoment B raw27658step0 raw27658step0Labels = mixedMoment B raw27658step1 raw27658step1Labels := by
      have hz : ∀ j, raw27658step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27658step1 = (fun i j => raw27658step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27658step1 raw27658step0; decide +kernel
      have hl : raw27658step1Labels = raw27658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27658step0 raw27658step0Labels permutation80 hz
    mixedMoment B raw27658step1 raw27658step1Labels = mixedMoment B raw27658step2 raw27658step2Labels := by
      have ha : raw27658step2 = (fun i j => raw27658step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27658step2 raw27658step1; decide +kernel
      have hl : raw27658step2Labels = raw27658step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27658step1 raw27658step1Labels permutation8 permutation6
    mixedMoment B raw27658step2 raw27658step2Labels = mixedMoment B raw27658step3 raw27658step3Labels := by
      have ha : raw27658step3 = raw27658step2 := by apply Matrix.ext; unfold raw27658step3 raw27658step2; decide +kernel
      have hl : raw27658step2Labels = labelEmbedding9 ∘ raw27658step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27658step2 raw27658step2Labels raw27658step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

theorem canonical27659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27659 raw27659Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw27659 raw27659Labels = mixedMoment B raw27659step0 raw27659step0Labels := by
      have hz : ∀ j, raw27659 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27659step0 = (fun i j => raw27659 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27659step0 raw27659; decide +kernel
      have hl : raw27659step0Labels = raw27659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27659 raw27659Labels permutation434 hz
    mixedMoment B raw27659step0 raw27659step0Labels = mixedMoment B raw27659step1 raw27659step1Labels := by
      have hz : ∀ j, raw27659step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27659step1 = (fun i j => raw27659step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27659step1 raw27659step0; decide +kernel
      have hl : raw27659step1Labels = raw27659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27659step0 raw27659step0Labels permutation80 hz
    mixedMoment B raw27659step1 raw27659step1Labels = mixedMoment B raw27659step2 raw27659step2Labels := by
      have ha : raw27659step2 = (fun i j => raw27659step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27659step2 raw27659step1; decide +kernel
      have hl : raw27659step2Labels = raw27659step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27659step1 raw27659step1Labels permutation8 permutation6
    mixedMoment B raw27659step2 raw27659step2Labels = mixedMoment B raw27659step3 raw27659step3Labels := by
      have ha : raw27659step3 = raw27659step2 := by apply Matrix.ext; unfold raw27659step3 raw27659step2; decide +kernel
      have hl : raw27659step2Labels = labelEmbedding9 ∘ raw27659step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27659step2 raw27659step2Labels raw27659step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

theorem canonical27660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27660 raw27660Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw27660 raw27660Labels = mixedMoment B raw27660step0 raw27660step0Labels := by
      have hz : ∀ j, raw27660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27660step0 = (fun i j => raw27660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27660step0 raw27660; decide +kernel
      have hl : raw27660step0Labels = raw27660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27660 raw27660Labels permutation434 hz
    mixedMoment B raw27660step0 raw27660step0Labels = mixedMoment B raw27660step1 raw27660step1Labels := by
      have ha : raw27660step1 = (fun i j => raw27660step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27660step1 raw27660step0; decide +kernel
      have hl : raw27660step1Labels = raw27660step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27660step0 raw27660step0Labels permutation32 permutation6
    mixedMoment B raw27660step1 raw27660step1Labels = mixedMoment B raw27660step2 raw27660step2Labels := by
      have ha : raw27660step2 = raw27660step1 := by apply Matrix.ext; unfold raw27660step2 raw27660step1; decide +kernel
      have hl : raw27660step1Labels = labelEmbedding9 ∘ raw27660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27660step1 raw27660step1Labels raw27660step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5139 node5139Labels := by rfl

theorem canonical27661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27661 raw27661Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw27661 raw27661Labels = mixedMoment B raw27661step0 raw27661step0Labels := by
      have hz : ∀ j, raw27661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27661step0 = (fun i j => raw27661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27661step0 raw27661; decide +kernel
      have hl : raw27661step0Labels = raw27661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27661 raw27661Labels permutation346 hz
    mixedMoment B raw27661step0 raw27661step0Labels = mixedMoment B raw27661step1 raw27661step1Labels := by
      have ha : raw27661step1 = (fun i j => raw27661step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27661step1 raw27661step0; decide +kernel
      have hl : raw27661step1Labels = raw27661step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27661step0 raw27661step0Labels permutation32 permutation6
    mixedMoment B raw27661step1 raw27661step1Labels = mixedMoment B raw27661step2 raw27661step2Labels := by
      have ha : raw27661step2 = raw27661step1 := by apply Matrix.ext; unfold raw27661step2 raw27661step1; decide +kernel
      have hl : raw27661step1Labels = labelEmbedding9 ∘ raw27661step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27661step1 raw27661step1Labels raw27661step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5139 node5139Labels := by rfl

theorem canonical27688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27688 raw27688Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw27688 raw27688Labels = mixedMoment B raw27688step0 raw27688step0Labels := by
      have hz : ∀ j, raw27688 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27688step0 = (fun i j => raw27688 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27688step0 raw27688; decide +kernel
      have hl : raw27688step0Labels = raw27688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27688 raw27688Labels permutation434 hz
    mixedMoment B raw27688step0 raw27688step0Labels = mixedMoment B raw27688step1 raw27688step1Labels := by
      have hz : ∀ j, raw27688step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27688step1 = (fun i j => raw27688step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27688step1 raw27688step0; decide +kernel
      have hl : raw27688step1Labels = raw27688step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27688step0 raw27688step0Labels permutation80 hz
    mixedMoment B raw27688step1 raw27688step1Labels = mixedMoment B raw27688step2 raw27688step2Labels := by
      have ha : raw27688step2 = (fun i j => raw27688step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27688step2 raw27688step1; decide +kernel
      have hl : raw27688step2Labels = raw27688step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27688step1 raw27688step1Labels permutation30 permutation2
    mixedMoment B raw27688step2 raw27688step2Labels = mixedMoment B raw27688step3 raw27688step3Labels := by
      have ha : raw27688step3 = -raw27688step2 := by apply Matrix.ext; change ∀ i j, raw27688step3 i j = -(raw27688step2 i j); unfold raw27688step3 raw27688step2; decide +kernel
      have hl : raw27688step3Labels = raw27688step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4875 node4875Labels := by rfl

theorem canonical27689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27689 raw27689Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw27689 raw27689Labels = mixedMoment B raw27689step0 raw27689step0Labels := by
      have hz : ∀ j, raw27689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27689step0 = (fun i j => raw27689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27689step0 raw27689; decide +kernel
      have hl : raw27689step0Labels = raw27689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27689 raw27689Labels permutation434 hz
    mixedMoment B raw27689step0 raw27689step0Labels = mixedMoment B raw27689step1 raw27689step1Labels := by
      have ha : raw27689step1 = (fun i j => raw27689step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27689step1 raw27689step0; decide +kernel
      have hl : raw27689step1Labels = raw27689step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27689step0 raw27689step0Labels permutation151 permutation2
    mixedMoment B raw27689step1 raw27689step1Labels = mixedMoment B raw27689step2 raw27689step2Labels := by
      have ha : raw27689step2 = -raw27689step1 := by apply Matrix.ext; change ∀ i j, raw27689step2 i j = -(raw27689step1 i j); unfold raw27689step2 raw27689step1; decide +kernel
      have hl : raw27689step2Labels = raw27689step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical27690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27690 raw27690Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw27690 raw27690Labels = mixedMoment B raw27690step0 raw27690step0Labels := by
      have hz : ∀ j, raw27690 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27690step0 = (fun i j => raw27690 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27690step0 raw27690; decide +kernel
      have hl : raw27690step0Labels = raw27690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27690 raw27690Labels permutation346 hz
    mixedMoment B raw27690step0 raw27690step0Labels = mixedMoment B raw27690step1 raw27690step1Labels := by
      have ha : raw27690step1 = (fun i j => raw27690step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27690step1 raw27690step0; decide +kernel
      have hl : raw27690step1Labels = raw27690step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27690step0 raw27690step0Labels permutation151 permutation2
    mixedMoment B raw27690step1 raw27690step1Labels = mixedMoment B raw27690step2 raw27690step2Labels := by
      have ha : raw27690step2 = -raw27690step1 := by apply Matrix.ext; change ∀ i j, raw27690step2 i j = -(raw27690step1 i j); unfold raw27690step2 raw27690step1; decide +kernel
      have hl : raw27690step2Labels = raw27690step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical27691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27691 raw27691Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw27691 raw27691Labels = mixedMoment B raw27691step0 raw27691step0Labels := by
      have hz : ∀ j, raw27691 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27691step0 = (fun i j => raw27691 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27691step0 raw27691; decide +kernel
      have hl : raw27691step0Labels = raw27691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27691 raw27691Labels permutation434 hz
    mixedMoment B raw27691step0 raw27691step0Labels = mixedMoment B raw27691step1 raw27691step1Labels := by
      have hz : ∀ j, raw27691step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27691step1 = (fun i j => raw27691step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27691step1 raw27691step0; decide +kernel
      have hl : raw27691step1Labels = raw27691step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27691step0 raw27691step0Labels permutation80 hz
    mixedMoment B raw27691step1 raw27691step1Labels = mixedMoment B raw27691step2 raw27691step2Labels := by
      have ha : raw27691step2 = (fun i j => raw27691step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27691step2 raw27691step1; decide +kernel
      have hl : raw27691step2Labels = raw27691step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27691step1 raw27691step1Labels permutation31 permutation2
    mixedMoment B raw27691step2 raw27691step2Labels = mixedMoment B raw27691step3 raw27691step3Labels := by
      have ha : raw27691step3 = -raw27691step2 := by apply Matrix.ext; change ∀ i j, raw27691step3 i j = -(raw27691step2 i j); unfold raw27691step3 raw27691step2; decide +kernel
      have hl : raw27691step3Labels = raw27691step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical27692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27692 raw27692Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw27692 raw27692Labels = mixedMoment B raw27692step0 raw27692step0Labels := by
      have hz : ∀ j, raw27692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27692step0 = (fun i j => raw27692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27692step0 raw27692; decide +kernel
      have hl : raw27692step0Labels = raw27692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27692 raw27692Labels permutation434 hz
    mixedMoment B raw27692step0 raw27692step0Labels = mixedMoment B raw27692step1 raw27692step1Labels := by
      have hz : ∀ j, raw27692step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27692step1 = (fun i j => raw27692step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27692step1 raw27692step0; decide +kernel
      have hl : raw27692step1Labels = raw27692step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27692step0 raw27692step0Labels permutation80 hz
    mixedMoment B raw27692step1 raw27692step1Labels = mixedMoment B raw27692step2 raw27692step2Labels := by
      have ha : raw27692step2 = (fun i j => raw27692step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27692step2 raw27692step1; decide +kernel
      have hl : raw27692step2Labels = raw27692step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27692step1 raw27692step1Labels permutation31 permutation7
    mixedMoment B raw27692step2 raw27692step2Labels = mixedMoment B raw27692step3 raw27692step3Labels := by
      have ha : raw27692step3 = raw27692step2 := by apply Matrix.ext; unfold raw27692step3 raw27692step2; decide +kernel
      have hl : raw27692step2Labels = labelEmbedding10 ∘ raw27692step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27692step2 raw27692step2Labels raw27692step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical27693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27693 raw27693Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw27693 raw27693Labels = mixedMoment B raw27693step0 raw27693step0Labels := by
      have hz : ∀ j, raw27693 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27693step0 = (fun i j => raw27693 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27693step0 raw27693; decide +kernel
      have hl : raw27693step0Labels = raw27693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27693 raw27693Labels permutation434 hz
    mixedMoment B raw27693step0 raw27693step0Labels = mixedMoment B raw27693step1 raw27693step1Labels := by
      have hz : ∀ j, raw27693step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27693step1 = (fun i j => raw27693step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27693step1 raw27693step0; decide +kernel
      have hl : raw27693step1Labels = raw27693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27693step0 raw27693step0Labels permutation80 hz
    mixedMoment B raw27693step1 raw27693step1Labels = mixedMoment B raw27693step2 raw27693step2Labels := by
      have ha : raw27693step2 = (fun i j => raw27693step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27693step2 raw27693step1; decide +kernel
      have hl : raw27693step2Labels = raw27693step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27693step1 raw27693step1Labels permutation8 permutation3
    mixedMoment B raw27693step2 raw27693step2Labels = mixedMoment B raw27693step3 raw27693step3Labels := by
      have ha : raw27693step3 = raw27693step2 := by apply Matrix.ext; unfold raw27693step3 raw27693step2; decide +kernel
      have hl : raw27693step2Labels = labelEmbedding6 ∘ raw27693step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27693step2 raw27693step2Labels raw27693step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4464 node4464Labels := by rfl

theorem canonical27694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27694 raw27694Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw27694 raw27694Labels = mixedMoment B raw27694step0 raw27694step0Labels := by
      have hz : ∀ j, raw27694 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27694step0 = (fun i j => raw27694 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27694step0 raw27694; decide +kernel
      have hl : raw27694step0Labels = raw27694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27694 raw27694Labels permutation434 hz
    mixedMoment B raw27694step0 raw27694step0Labels = mixedMoment B raw27694step1 raw27694step1Labels := by
      have ha : raw27694step1 = (fun i j => raw27694step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27694step1 raw27694step0; decide +kernel
      have hl : raw27694step1Labels = raw27694step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27694step0 raw27694step0Labels permutation149 permutation2
    mixedMoment B raw27694step1 raw27694step1Labels = mixedMoment B raw27694step2 raw27694step2Labels := by
      have ha : raw27694step2 = -raw27694step1 := by apply Matrix.ext; change ∀ i j, raw27694step2 i j = -(raw27694step1 i j); unfold raw27694step2 raw27694step1; decide +kernel
      have hl : raw27694step2Labels = raw27694step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4853 node4853Labels := by rfl

theorem canonical27695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27695 raw27695Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw27695 raw27695Labels = mixedMoment B raw27695step0 raw27695step0Labels := by
      have hz : ∀ j, raw27695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27695step0 = (fun i j => raw27695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27695step0 raw27695; decide +kernel
      have hl : raw27695step0Labels = raw27695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27695 raw27695Labels permutation346 hz
    mixedMoment B raw27695step0 raw27695step0Labels = mixedMoment B raw27695step1 raw27695step1Labels := by
      have ha : raw27695step1 = (fun i j => raw27695step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27695step1 raw27695step0; decide +kernel
      have hl : raw27695step1Labels = raw27695step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27695step0 raw27695step0Labels permutation149 permutation2
    mixedMoment B raw27695step1 raw27695step1Labels = mixedMoment B raw27695step2 raw27695step2Labels := by
      have ha : raw27695step2 = -raw27695step1 := by apply Matrix.ext; change ∀ i j, raw27695step2 i j = -(raw27695step1 i j); unfold raw27695step2 raw27695step1; decide +kernel
      have hl : raw27695step2Labels = raw27695step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4853 node4853Labels := by rfl

theorem canonical27696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27696 raw27696Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw27696 raw27696Labels = mixedMoment B raw27696step0 raw27696step0Labels := by
      have hz : ∀ j, raw27696 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27696step0 = (fun i j => raw27696 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27696step0 raw27696; decide +kernel
      have hl : raw27696step0Labels = raw27696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27696 raw27696Labels permutation434 hz
    mixedMoment B raw27696step0 raw27696step0Labels = mixedMoment B raw27696step1 raw27696step1Labels := by
      have hz : ∀ j, raw27696step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27696step1 = (fun i j => raw27696step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27696step1 raw27696step0; decide +kernel
      have hl : raw27696step1Labels = raw27696step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27696step0 raw27696step0Labels permutation80 hz
    mixedMoment B raw27696step1 raw27696step1Labels = mixedMoment B raw27696step2 raw27696step2Labels := by
      have ha : raw27696step2 = (fun i j => raw27696step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27696step2 raw27696step1; decide +kernel
      have hl : raw27696step2Labels = raw27696step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27696step1 raw27696step1Labels permutation29 permutation2
    mixedMoment B raw27696step2 raw27696step2Labels = mixedMoment B raw27696step3 raw27696step3Labels := by
      have ha : raw27696step3 = -raw27696step2 := by apply Matrix.ext; change ∀ i j, raw27696step3 i j = -(raw27696step2 i j); unfold raw27696step3 raw27696step2; decide +kernel
      have hl : raw27696step3Labels = raw27696step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical27697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27697 raw27697Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw27697 raw27697Labels = mixedMoment B raw27697step0 raw27697step0Labels := by
      have hz : ∀ j, raw27697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27697step0 = (fun i j => raw27697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27697step0 raw27697; decide +kernel
      have hl : raw27697step0Labels = raw27697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27697 raw27697Labels permutation434 hz
    mixedMoment B raw27697step0 raw27697step0Labels = mixedMoment B raw27697step1 raw27697step1Labels := by
      have hz : ∀ j, raw27697step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27697step1 = (fun i j => raw27697step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27697step1 raw27697step0; decide +kernel
      have hl : raw27697step1Labels = raw27697step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27697step0 raw27697step0Labels permutation80 hz
    mixedMoment B raw27697step1 raw27697step1Labels = mixedMoment B raw27697step2 raw27697step2Labels := by
      have ha : raw27697step2 = (fun i j => raw27697step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27697step2 raw27697step1; decide +kernel
      have hl : raw27697step2Labels = raw27697step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27697step1 raw27697step1Labels permutation8 permutation3
    mixedMoment B raw27697step2 raw27697step2Labels = mixedMoment B raw27697step3 raw27697step3Labels := by
      have ha : raw27697step3 = raw27697step2 := by apply Matrix.ext; unfold raw27697step3 raw27697step2; decide +kernel
      have hl : raw27697step2Labels = labelEmbedding6 ∘ raw27697step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27697step2 raw27697step2Labels raw27697step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

theorem canonical27698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27698 raw27698Labels = mixedMoment B node4353 node4353Labels := by
  calc
    mixedMoment B raw27698 raw27698Labels = mixedMoment B raw27698step0 raw27698step0Labels := by
      have hz : ∀ j, raw27698 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27698step0 = (fun i j => raw27698 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27698step0 raw27698; decide +kernel
      have hl : raw27698step0Labels = raw27698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27698 raw27698Labels permutation434 hz
    mixedMoment B raw27698step0 raw27698step0Labels = mixedMoment B raw27698step1 raw27698step1Labels := by
      have ha : raw27698step1 = (fun i j => raw27698step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27698step1 raw27698step0; decide +kernel
      have hl : raw27698step1Labels = raw27698step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27698step0 raw27698step0Labels permutation32 permutation3
    mixedMoment B raw27698step1 raw27698step1Labels = mixedMoment B raw27698step2 raw27698step2Labels := by
      have ha : raw27698step2 = raw27698step1 := by apply Matrix.ext; unfold raw27698step2 raw27698step1; decide +kernel
      have hl : raw27698step1Labels = labelEmbedding6 ∘ raw27698step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27698step1 raw27698step1Labels raw27698step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4353 node4353Labels := by rfl

theorem canonical27699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27699 raw27699Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw27699 raw27699Labels = mixedMoment B raw27699step0 raw27699step0Labels := by
      have hz : ∀ j, raw27699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27699step0 = (fun i j => raw27699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27699step0 raw27699; decide +kernel
      have hl : raw27699step0Labels = raw27699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27699 raw27699Labels permutation434 hz
    mixedMoment B raw27699step0 raw27699step0Labels = mixedMoment B raw27699step1 raw27699step1Labels := by
      have ha : raw27699step1 = (fun i j => raw27699step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27699step1 raw27699step0; decide +kernel
      have hl : raw27699step1Labels = raw27699step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27699step0 raw27699step0Labels permutation145 permutation2
    mixedMoment B raw27699step1 raw27699step1Labels = mixedMoment B raw27699step2 raw27699step2Labels := by
      have ha : raw27699step2 = -raw27699step1 := by apply Matrix.ext; change ∀ i j, raw27699step2 i j = -(raw27699step1 i j); unfold raw27699step2 raw27699step1; decide +kernel
      have hl : raw27699step2Labels = raw27699step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4777 node4777Labels := by rfl

theorem canonical27700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27700 raw27700Labels = mixedMoment B node4772 node4772Labels := by
  calc
    mixedMoment B raw27700 raw27700Labels = mixedMoment B raw27700step0 raw27700step0Labels := by
      have ha : raw27700step0 = (fun i j => raw27700 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27700step0 raw27700; decide +kernel
      have hl : raw27700step0Labels = raw27700Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27700 raw27700Labels permutation646 permutation2
    mixedMoment B raw27700step0 raw27700step0Labels = mixedMoment B raw27700step1 raw27700step1Labels := by
      have ha : raw27700step1 = -raw27700step0 := by apply Matrix.ext; change ∀ i j, raw27700step1 i j = -(raw27700step0 i j); unfold raw27700step1 raw27700step0; decide +kernel
      have hl : raw27700step1Labels = raw27700step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4772 node4772Labels := by rfl

theorem canonical27701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27701 raw27701Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw27701 raw27701Labels = mixedMoment B raw27701step0 raw27701step0Labels := by
      have hz : ∀ j, raw27701 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27701step0 = (fun i j => raw27701 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27701step0 raw27701; decide +kernel
      have hl : raw27701step0Labels = raw27701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27701 raw27701Labels permutation434 hz
    mixedMoment B raw27701step0 raw27701step0Labels = mixedMoment B raw27701step1 raw27701step1Labels := by
      have ha : raw27701step1 = (fun i j => raw27701step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27701step1 raw27701step0; decide +kernel
      have hl : raw27701step1Labels = raw27701step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27701step0 raw27701step0Labels permutation145 permutation2
    mixedMoment B raw27701step1 raw27701step1Labels = mixedMoment B raw27701step2 raw27701step2Labels := by
      have ha : raw27701step2 = -raw27701step1 := by apply Matrix.ext; change ∀ i j, raw27701step2 i j = -(raw27701step1 i j); unfold raw27701step2 raw27701step1; decide +kernel
      have hl : raw27701step2Labels = raw27701step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical27702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27702 raw27702Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw27702 raw27702Labels = mixedMoment B raw27702step0 raw27702step0Labels := by
      have hz : ∀ j, raw27702 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27702step0 = (fun i j => raw27702 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27702step0 raw27702; decide +kernel
      have hl : raw27702step0Labels = raw27702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27702 raw27702Labels permutation434 hz
    mixedMoment B raw27702step0 raw27702step0Labels = mixedMoment B raw27702step1 raw27702step1Labels := by
      have ha : raw27702step1 = (fun i j => raw27702step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27702step1 raw27702step0; decide +kernel
      have hl : raw27702step1Labels = raw27702step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27702step0 raw27702step0Labels permutation32 permutation3
    mixedMoment B raw27702step1 raw27702step1Labels = mixedMoment B raw27702step2 raw27702step2Labels := by
      have ha : raw27702step2 = raw27702step1 := by apply Matrix.ext; unfold raw27702step2 raw27702step1; decide +kernel
      have hl : raw27702step1Labels = labelEmbedding6 ∘ raw27702step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27702step1 raw27702step1Labels raw27702step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

theorem canonical27703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27703 raw27703Labels = mixedMoment B node4353 node4353Labels := by
  calc
    mixedMoment B raw27703 raw27703Labels = mixedMoment B raw27703step0 raw27703step0Labels := by
      have hz : ∀ j, raw27703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27703step0 = (fun i j => raw27703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27703step0 raw27703; decide +kernel
      have hl : raw27703step0Labels = raw27703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27703 raw27703Labels permutation346 hz
    mixedMoment B raw27703step0 raw27703step0Labels = mixedMoment B raw27703step1 raw27703step1Labels := by
      have ha : raw27703step1 = (fun i j => raw27703step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27703step1 raw27703step0; decide +kernel
      have hl : raw27703step1Labels = raw27703step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27703step0 raw27703step0Labels permutation32 permutation3
    mixedMoment B raw27703step1 raw27703step1Labels = mixedMoment B raw27703step2 raw27703step2Labels := by
      have ha : raw27703step2 = raw27703step1 := by apply Matrix.ext; unfold raw27703step2 raw27703step1; decide +kernel
      have hl : raw27703step1Labels = labelEmbedding6 ∘ raw27703step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27703step1 raw27703step1Labels raw27703step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4353 node4353Labels := by rfl

theorem canonical27704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27704 raw27704Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw27704 raw27704Labels = mixedMoment B raw27704step0 raw27704step0Labels := by
      have hz : ∀ j, raw27704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27704step0 = (fun i j => raw27704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27704step0 raw27704; decide +kernel
      have hl : raw27704step0Labels = raw27704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27704 raw27704Labels permutation346 hz
    mixedMoment B raw27704step0 raw27704step0Labels = mixedMoment B raw27704step1 raw27704step1Labels := by
      have ha : raw27704step1 = (fun i j => raw27704step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27704step1 raw27704step0; decide +kernel
      have hl : raw27704step1Labels = raw27704step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27704step0 raw27704step0Labels permutation145 permutation2
    mixedMoment B raw27704step1 raw27704step1Labels = mixedMoment B raw27704step2 raw27704step2Labels := by
      have ha : raw27704step2 = -raw27704step1 := by apply Matrix.ext; change ∀ i j, raw27704step2 i j = -(raw27704step1 i j); unfold raw27704step2 raw27704step1; decide +kernel
      have hl : raw27704step2Labels = raw27704step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4777 node4777Labels := by rfl

theorem canonical27705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27705 raw27705Labels = mixedMoment B node4772 node4772Labels := by
  calc
    mixedMoment B raw27705 raw27705Labels = mixedMoment B raw27705step0 raw27705step0Labels := by
      have ha : raw27705step0 = (fun i j => raw27705 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27705step0 raw27705; decide +kernel
      have hl : raw27705step0Labels = raw27705Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27705 raw27705Labels permutation664 permutation2
    mixedMoment B raw27705step0 raw27705step0Labels = mixedMoment B raw27705step1 raw27705step1Labels := by
      have ha : raw27705step1 = -raw27705step0 := by apply Matrix.ext; change ∀ i j, raw27705step1 i j = -(raw27705step0 i j); unfold raw27705step1 raw27705step0; decide +kernel
      have hl : raw27705step1Labels = raw27705step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4772 node4772Labels := by rfl

theorem canonical27706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27706 raw27706Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw27706 raw27706Labels = mixedMoment B raw27706step0 raw27706step0Labels := by
      have hz : ∀ j, raw27706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27706step0 = (fun i j => raw27706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27706step0 raw27706; decide +kernel
      have hl : raw27706step0Labels = raw27706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27706 raw27706Labels permutation346 hz
    mixedMoment B raw27706step0 raw27706step0Labels = mixedMoment B raw27706step1 raw27706step1Labels := by
      have ha : raw27706step1 = (fun i j => raw27706step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27706step1 raw27706step0; decide +kernel
      have hl : raw27706step1Labels = raw27706step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27706step0 raw27706step0Labels permutation145 permutation2
    mixedMoment B raw27706step1 raw27706step1Labels = mixedMoment B raw27706step2 raw27706step2Labels := by
      have ha : raw27706step2 = -raw27706step1 := by apply Matrix.ext; change ∀ i j, raw27706step2 i j = -(raw27706step1 i j); unfold raw27706step2 raw27706step1; decide +kernel
      have hl : raw27706step2Labels = raw27706step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical27707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27707 raw27707Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw27707 raw27707Labels = mixedMoment B raw27707step0 raw27707step0Labels := by
      have hz : ∀ j, raw27707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27707step0 = (fun i j => raw27707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27707step0 raw27707; decide +kernel
      have hl : raw27707step0Labels = raw27707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27707 raw27707Labels permutation346 hz
    mixedMoment B raw27707step0 raw27707step0Labels = mixedMoment B raw27707step1 raw27707step1Labels := by
      have ha : raw27707step1 = (fun i j => raw27707step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27707step1 raw27707step0; decide +kernel
      have hl : raw27707step1Labels = raw27707step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27707step0 raw27707step0Labels permutation32 permutation3
    mixedMoment B raw27707step1 raw27707step1Labels = mixedMoment B raw27707step2 raw27707step2Labels := by
      have ha : raw27707step2 = raw27707step1 := by apply Matrix.ext; unfold raw27707step2 raw27707step1; decide +kernel
      have hl : raw27707step1Labels = labelEmbedding6 ∘ raw27707step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27707step1 raw27707step1Labels raw27707step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

theorem canonical27708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27708 raw27708Labels = mixedMoment B node4362 node4362Labels := by
  calc
    mixedMoment B raw27708 raw27708Labels = mixedMoment B raw27708step0 raw27708step0Labels := by
      have hz : ∀ j, raw27708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27708step0 = (fun i j => raw27708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27708step0 raw27708; decide +kernel
      have hl : raw27708step0Labels = raw27708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27708 raw27708Labels permutation434 hz
    mixedMoment B raw27708step0 raw27708step0Labels = mixedMoment B raw27708step1 raw27708step1Labels := by
      have hz : ∀ j, raw27708step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27708step1 = (fun i j => raw27708step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27708step1 raw27708step0; decide +kernel
      have hl : raw27708step1Labels = raw27708step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27708step0 raw27708step0Labels permutation80 hz
    mixedMoment B raw27708step1 raw27708step1Labels = mixedMoment B raw27708step2 raw27708step2Labels := by
      have ha : raw27708step2 = (fun i j => raw27708step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27708step2 raw27708step1; decide +kernel
      have hl : raw27708step2Labels = raw27708step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27708step1 raw27708step1Labels permutation8 permutation3
    mixedMoment B raw27708step2 raw27708step2Labels = mixedMoment B raw27708step3 raw27708step3Labels := by
      have ha : raw27708step3 = raw27708step2 := by apply Matrix.ext; unfold raw27708step3 raw27708step2; decide +kernel
      have hl : raw27708step2Labels = labelEmbedding6 ∘ raw27708step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27708step2 raw27708step2Labels raw27708step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4362 node4362Labels := by rfl

theorem canonical27709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27709 raw27709Labels = mixedMoment B node4705 node4705Labels := by
  calc
    mixedMoment B raw27709 raw27709Labels = mixedMoment B raw27709step0 raw27709step0Labels := by
      have hz : ∀ j, raw27709 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27709step0 = (fun i j => raw27709 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27709step0 raw27709; decide +kernel
      have hl : raw27709step0Labels = raw27709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27709 raw27709Labels permutation434 hz
    mixedMoment B raw27709step0 raw27709step0Labels = mixedMoment B raw27709step1 raw27709step1Labels := by
      have hz : ∀ j, raw27709step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27709step1 = (fun i j => raw27709step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27709step1 raw27709step0; decide +kernel
      have hl : raw27709step1Labels = raw27709step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27709step0 raw27709step0Labels permutation80 hz
    mixedMoment B raw27709step1 raw27709step1Labels = mixedMoment B raw27709step2 raw27709step2Labels := by
      have ha : raw27709step2 = (fun i j => raw27709step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27709step2 raw27709step1; decide +kernel
      have hl : raw27709step2Labels = raw27709step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27709step1 raw27709step1Labels permutation31 permutation2
    mixedMoment B raw27709step2 raw27709step2Labels = mixedMoment B raw27709step3 raw27709step3Labels := by
      have ha : raw27709step3 = -raw27709step2 := by apply Matrix.ext; change ∀ i j, raw27709step3 i j = -(raw27709step2 i j); unfold raw27709step3 raw27709step2; decide +kernel
      have hl : raw27709step3Labels = raw27709step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4705 node4705Labels := by rfl

theorem canonical27710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27710 raw27710Labels = mixedMoment B node4699 node4699Labels := by
  calc
    mixedMoment B raw27710 raw27710Labels = mixedMoment B raw27710step0 raw27710step0Labels := by
      have hz : ∀ j, raw27710 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27710step0 = (fun i j => raw27710 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27710step0 raw27710; decide +kernel
      have hl : raw27710step0Labels = raw27710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27710 raw27710Labels permutation434 hz
    mixedMoment B raw27710step0 raw27710step0Labels = mixedMoment B raw27710step1 raw27710step1Labels := by
      have ha : raw27710step1 = (fun i j => raw27710step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27710step1 raw27710step0; decide +kernel
      have hl : raw27710step1Labels = raw27710step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27710step0 raw27710step0Labels permutation151 permutation2
    mixedMoment B raw27710step1 raw27710step1Labels = mixedMoment B raw27710step2 raw27710step2Labels := by
      have ha : raw27710step2 = -raw27710step1 := by apply Matrix.ext; change ∀ i j, raw27710step2 i j = -(raw27710step1 i j); unfold raw27710step2 raw27710step1; decide +kernel
      have hl : raw27710step2Labels = raw27710step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4699 node4699Labels := by rfl

theorem canonical27711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27711 raw27711Labels = mixedMoment B node4699 node4699Labels := by
  calc
    mixedMoment B raw27711 raw27711Labels = mixedMoment B raw27711step0 raw27711step0Labels := by
      have hz : ∀ j, raw27711 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27711step0 = (fun i j => raw27711 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27711step0 raw27711; decide +kernel
      have hl : raw27711step0Labels = raw27711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27711 raw27711Labels permutation346 hz
    mixedMoment B raw27711step0 raw27711step0Labels = mixedMoment B raw27711step1 raw27711step1Labels := by
      have ha : raw27711step1 = (fun i j => raw27711step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27711step1 raw27711step0; decide +kernel
      have hl : raw27711step1Labels = raw27711step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27711step0 raw27711step0Labels permutation151 permutation2
    mixedMoment B raw27711step1 raw27711step1Labels = mixedMoment B raw27711step2 raw27711step2Labels := by
      have ha : raw27711step2 = -raw27711step1 := by apply Matrix.ext; change ∀ i j, raw27711step2 i j = -(raw27711step1 i j); unfold raw27711step2 raw27711step1; decide +kernel
      have hl : raw27711step2Labels = raw27711step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4699 node4699Labels := by rfl

theorem canonical27712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27712 raw27712Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw27712 raw27712Labels = mixedMoment B raw27712step0 raw27712step0Labels := by
      have hz : ∀ j, raw27712 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27712step0 = (fun i j => raw27712 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27712step0 raw27712; decide +kernel
      have hl : raw27712step0Labels = raw27712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27712 raw27712Labels permutation434 hz
    mixedMoment B raw27712step0 raw27712step0Labels = mixedMoment B raw27712step1 raw27712step1Labels := by
      have hz : ∀ j, raw27712step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27712step1 = (fun i j => raw27712step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27712step1 raw27712step0; decide +kernel
      have hl : raw27712step1Labels = raw27712step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27712step0 raw27712step0Labels permutation80 hz
    mixedMoment B raw27712step1 raw27712step1Labels = mixedMoment B raw27712step2 raw27712step2Labels := by
      have ha : raw27712step2 = (fun i j => raw27712step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27712step2 raw27712step1; decide +kernel
      have hl : raw27712step2Labels = raw27712step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27712step1 raw27712step1Labels permutation9 permutation3
    mixedMoment B raw27712step2 raw27712step2Labels = mixedMoment B raw27712step3 raw27712step3Labels := by
      have ha : raw27712step3 = raw27712step2 := by apply Matrix.ext; unfold raw27712step3 raw27712step2; decide +kernel
      have hl : raw27712step2Labels = labelEmbedding6 ∘ raw27712step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27712step2 raw27712step2Labels raw27712step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5175 node5175Labels := by rfl

theorem canonical27713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27713 raw27713Labels = mixedMoment B node4358 node4358Labels := by
  calc
    mixedMoment B raw27713 raw27713Labels = mixedMoment B raw27713step0 raw27713step0Labels := by
      have hz : ∀ j, raw27713 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27713step0 = (fun i j => raw27713 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27713step0 raw27713; decide +kernel
      have hl : raw27713step0Labels = raw27713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27713 raw27713Labels permutation434 hz
    mixedMoment B raw27713step0 raw27713step0Labels = mixedMoment B raw27713step1 raw27713step1Labels := by
      have hz : ∀ j, raw27713step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27713step1 = (fun i j => raw27713step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27713step1 raw27713step0; decide +kernel
      have hl : raw27713step1Labels = raw27713step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27713step0 raw27713step0Labels permutation80 hz
    mixedMoment B raw27713step1 raw27713step1Labels = mixedMoment B raw27713step2 raw27713step2Labels := by
      have ha : raw27713step2 = (fun i j => raw27713step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27713step2 raw27713step1; decide +kernel
      have hl : raw27713step2Labels = raw27713step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27713step1 raw27713step1Labels permutation8 permutation3
    mixedMoment B raw27713step2 raw27713step2Labels = mixedMoment B raw27713step3 raw27713step3Labels := by
      have ha : raw27713step3 = raw27713step2 := by apply Matrix.ext; unfold raw27713step3 raw27713step2; decide +kernel
      have hl : raw27713step2Labels = labelEmbedding6 ∘ raw27713step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27713step2 raw27713step2Labels raw27713step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4358 node4358Labels := by rfl

theorem canonical27714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27714 raw27714Labels = mixedMoment B node4374 node4374Labels := by
  calc
    mixedMoment B raw27714 raw27714Labels = mixedMoment B raw27714step0 raw27714step0Labels := by
      have hz : ∀ j, raw27714 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27714step0 = (fun i j => raw27714 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27714step0 raw27714; decide +kernel
      have hl : raw27714step0Labels = raw27714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27714 raw27714Labels permutation434 hz
    mixedMoment B raw27714step0 raw27714step0Labels = mixedMoment B raw27714step1 raw27714step1Labels := by
      have hz : ∀ j, raw27714step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27714step1 = (fun i j => raw27714step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27714step1 raw27714step0; decide +kernel
      have hl : raw27714step1Labels = raw27714step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27714step0 raw27714step0Labels permutation80 hz
    mixedMoment B raw27714step1 raw27714step1Labels = mixedMoment B raw27714step2 raw27714step2Labels := by
      have ha : raw27714step2 = (fun i j => raw27714step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27714step2 raw27714step1; decide +kernel
      have hl : raw27714step2Labels = raw27714step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27714step1 raw27714step1Labels permutation31 permutation2
    mixedMoment B raw27714step2 raw27714step2Labels = mixedMoment B raw27714step3 raw27714step3Labels := by
      have ha : raw27714step3 = -raw27714step2 := by apply Matrix.ext; change ∀ i j, raw27714step3 i j = -(raw27714step2 i j); unfold raw27714step3 raw27714step2; decide +kernel
      have hl : raw27714step3Labels = raw27714step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4374 node4374Labels := by rfl

theorem canonical27715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27715 raw27715Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw27715 raw27715Labels = mixedMoment B raw27715step0 raw27715step0Labels := by
      have hz : ∀ j, raw27715 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27715step0 = (fun i j => raw27715 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27715step0 raw27715; decide +kernel
      have hl : raw27715step0Labels = raw27715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27715 raw27715Labels permutation434 hz
    mixedMoment B raw27715step0 raw27715step0Labels = mixedMoment B raw27715step1 raw27715step1Labels := by
      have ha : raw27715step1 = (fun i j => raw27715step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27715step1 raw27715step0; decide +kernel
      have hl : raw27715step1Labels = raw27715step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27715step0 raw27715step0Labels permutation151 permutation2
    mixedMoment B raw27715step1 raw27715step1Labels = mixedMoment B raw27715step2 raw27715step2Labels := by
      have ha : raw27715step2 = -raw27715step1 := by apply Matrix.ext; change ∀ i j, raw27715step2 i j = -(raw27715step1 i j); unfold raw27715step2 raw27715step1; decide +kernel
      have hl : raw27715step2Labels = raw27715step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4367 node4367Labels := by rfl

theorem canonical27716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27716 raw27716Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw27716 raw27716Labels = mixedMoment B raw27716step0 raw27716step0Labels := by
      have hz : ∀ j, raw27716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27716step0 = (fun i j => raw27716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27716step0 raw27716; decide +kernel
      have hl : raw27716step0Labels = raw27716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27716 raw27716Labels permutation346 hz
    mixedMoment B raw27716step0 raw27716step0Labels = mixedMoment B raw27716step1 raw27716step1Labels := by
      have ha : raw27716step1 = (fun i j => raw27716step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27716step1 raw27716step0; decide +kernel
      have hl : raw27716step1Labels = raw27716step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27716step0 raw27716step0Labels permutation151 permutation2
    mixedMoment B raw27716step1 raw27716step1Labels = mixedMoment B raw27716step2 raw27716step2Labels := by
      have ha : raw27716step2 = -raw27716step1 := by apply Matrix.ext; change ∀ i j, raw27716step2 i j = -(raw27716step1 i j); unfold raw27716step2 raw27716step1; decide +kernel
      have hl : raw27716step2Labels = raw27716step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4367 node4367Labels := by rfl

theorem canonical27717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27717 raw27717Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw27717 raw27717Labels = mixedMoment B raw27717step0 raw27717step0Labels := by
      have hz : ∀ j, raw27717 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27717step0 = (fun i j => raw27717 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27717step0 raw27717; decide +kernel
      have hl : raw27717step0Labels = raw27717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27717 raw27717Labels permutation434 hz
    mixedMoment B raw27717step0 raw27717step0Labels = mixedMoment B raw27717step1 raw27717step1Labels := by
      have hz : ∀ j, raw27717step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27717step1 = (fun i j => raw27717step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27717step1 raw27717step0; decide +kernel
      have hl : raw27717step1Labels = raw27717step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27717step0 raw27717step0Labels permutation80 hz
    mixedMoment B raw27717step1 raw27717step1Labels = mixedMoment B raw27717step2 raw27717step2Labels := by
      have ha : raw27717step2 = (fun i j => raw27717step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27717step2 raw27717step1; decide +kernel
      have hl : raw27717step2Labels = raw27717step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27717step1 raw27717step1Labels permutation31 permutation2
    mixedMoment B raw27717step2 raw27717step2Labels = mixedMoment B raw27717step3 raw27717step3Labels := by
      have ha : raw27717step3 = -raw27717step2 := by apply Matrix.ext; change ∀ i j, raw27717step3 i j = -(raw27717step2 i j); unfold raw27717step3 raw27717step2; decide +kernel
      have hl : raw27717step3Labels = raw27717step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4463 node4463Labels := by rfl

theorem canonical27718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27718 raw27718Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw27718 raw27718Labels = mixedMoment B raw27718step0 raw27718step0Labels := by
      have hz : ∀ j, raw27718 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27718step0 = (fun i j => raw27718 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27718step0 raw27718; decide +kernel
      have hl : raw27718step0Labels = raw27718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27718 raw27718Labels permutation434 hz
    mixedMoment B raw27718step0 raw27718step0Labels = mixedMoment B raw27718step1 raw27718step1Labels := by
      have hz : ∀ j, raw27718step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27718step1 = (fun i j => raw27718step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27718step1 raw27718step0; decide +kernel
      have hl : raw27718step1Labels = raw27718step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27718step0 raw27718step0Labels permutation80 hz
    mixedMoment B raw27718step1 raw27718step1Labels = mixedMoment B raw27718step2 raw27718step2Labels := by
      have ha : raw27718step2 = (fun i j => raw27718step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27718step2 raw27718step1; decide +kernel
      have hl : raw27718step2Labels = raw27718step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27718step1 raw27718step1Labels permutation30 permutation7
    mixedMoment B raw27718step2 raw27718step2Labels = mixedMoment B raw27718step3 raw27718step3Labels := by
      have ha : raw27718step3 = raw27718step2 := by apply Matrix.ext; unfold raw27718step3 raw27718step2; decide +kernel
      have hl : raw27718step2Labels = labelEmbedding1 ∘ raw27718step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27718step2 raw27718step2Labels raw27718step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2288 node2288Labels := by rfl

theorem canonical27719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27719 raw27719Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw27719 raw27719Labels = mixedMoment B raw27719step0 raw27719step0Labels := by
      have hz : ∀ j, raw27719 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27719step0 = (fun i j => raw27719 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27719step0 raw27719; decide +kernel
      have hl : raw27719step0Labels = raw27719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27719 raw27719Labels permutation434 hz
    mixedMoment B raw27719step0 raw27719step0Labels = mixedMoment B raw27719step1 raw27719step1Labels := by
      have ha : raw27719step1 = (fun i j => raw27719step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27719step1 raw27719step0; decide +kernel
      have hl : raw27719step1Labels = raw27719step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27719step0 raw27719step0Labels permutation145 permutation7
    mixedMoment B raw27719step1 raw27719step1Labels = mixedMoment B raw27719step2 raw27719step2Labels := by
      have ha : raw27719step2 = raw27719step1 := by apply Matrix.ext; unfold raw27719step2 raw27719step1; decide +kernel
      have hl : raw27719step1Labels = labelEmbedding1 ∘ raw27719step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27719step1 raw27719step1Labels raw27719step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical27720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27720 raw27720Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw27720 raw27720Labels = mixedMoment B raw27720step0 raw27720step0Labels := by
      have hz : ∀ j, raw27720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27720step0 = (fun i j => raw27720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27720step0 raw27720; decide +kernel
      have hl : raw27720step0Labels = raw27720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27720 raw27720Labels permutation346 hz
    mixedMoment B raw27720step0 raw27720step0Labels = mixedMoment B raw27720step1 raw27720step1Labels := by
      have ha : raw27720step1 = (fun i j => raw27720step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27720step1 raw27720step0; decide +kernel
      have hl : raw27720step1Labels = raw27720step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27720step0 raw27720step0Labels permutation145 permutation7
    mixedMoment B raw27720step1 raw27720step1Labels = mixedMoment B raw27720step2 raw27720step2Labels := by
      have ha : raw27720step2 = raw27720step1 := by apply Matrix.ext; unfold raw27720step2 raw27720step1; decide +kernel
      have hl : raw27720step1Labels = labelEmbedding1 ∘ raw27720step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27720step1 raw27720step1Labels raw27720step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical27721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27721 raw27721Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw27721 raw27721Labels = mixedMoment B raw27721step0 raw27721step0Labels := by
      have hz : ∀ j, raw27721 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27721step0 = (fun i j => raw27721 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27721step0 raw27721; decide +kernel
      have hl : raw27721step0Labels = raw27721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27721 raw27721Labels permutation434 hz
    mixedMoment B raw27721step0 raw27721step0Labels = mixedMoment B raw27721step1 raw27721step1Labels := by
      have hz : ∀ j, raw27721step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27721step1 = (fun i j => raw27721step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27721step1 raw27721step0; decide +kernel
      have hl : raw27721step1Labels = raw27721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27721step0 raw27721step0Labels permutation80 hz
    mixedMoment B raw27721step1 raw27721step1Labels = mixedMoment B raw27721step2 raw27721step2Labels := by
      have ha : raw27721step2 = (fun i j => raw27721step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27721step2 raw27721step1; decide +kernel
      have hl : raw27721step2Labels = raw27721step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27721step1 raw27721step1Labels permutation31 permutation7
    mixedMoment B raw27721step2 raw27721step2Labels = mixedMoment B raw27721step3 raw27721step3Labels := by
      have ha : raw27721step3 = raw27721step2 := by apply Matrix.ext; unfold raw27721step3 raw27721step2; decide +kernel
      have hl : raw27721step2Labels = labelEmbedding1 ∘ raw27721step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27721step2 raw27721step2Labels raw27721step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical27722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27722 raw27722Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw27722 raw27722Labels = mixedMoment B raw27722step0 raw27722step0Labels := by
      have hz : ∀ j, raw27722 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27722step0 = (fun i j => raw27722 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27722step0 raw27722; decide +kernel
      have hl : raw27722step0Labels = raw27722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27722 raw27722Labels permutation434 hz
    mixedMoment B raw27722step0 raw27722step0Labels = mixedMoment B raw27722step1 raw27722step1Labels := by
      have hz : ∀ j, raw27722step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27722step1 = (fun i j => raw27722step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27722step1 raw27722step0; decide +kernel
      have hl : raw27722step1Labels = raw27722step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27722step0 raw27722step0Labels permutation80 hz
    mixedMoment B raw27722step1 raw27722step1Labels = mixedMoment B raw27722step2 raw27722step2Labels := by
      have ha : raw27722step2 = (fun i j => raw27722step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27722step2 raw27722step1; decide +kernel
      have hl : raw27722step2Labels = raw27722step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27722step1 raw27722step1Labels permutation31 permutation7
    mixedMoment B raw27722step2 raw27722step2Labels = mixedMoment B raw27722step3 raw27722step3Labels := by
      have ha : raw27722step3 = raw27722step2 := by apply Matrix.ext; unfold raw27722step3 raw27722step2; decide +kernel
      have hl : raw27722step2Labels = labelEmbedding1 ∘ raw27722step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27722step2 raw27722step2Labels raw27722step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2782 node2782Labels := by rfl

theorem canonical27723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27723 raw27723Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw27723 raw27723Labels = mixedMoment B raw27723step0 raw27723step0Labels := by
      have hz : ∀ j, raw27723 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27723step0 = (fun i j => raw27723 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27723step0 raw27723; decide +kernel
      have hl : raw27723step0Labels = raw27723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27723 raw27723Labels permutation434 hz
    mixedMoment B raw27723step0 raw27723step0Labels = mixedMoment B raw27723step1 raw27723step1Labels := by
      have hz : ∀ j, raw27723step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27723step1 = (fun i j => raw27723step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27723step1 raw27723step0; decide +kernel
      have hl : raw27723step1Labels = raw27723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27723step0 raw27723step0Labels permutation80 hz
    mixedMoment B raw27723step1 raw27723step1Labels = mixedMoment B raw27723step2 raw27723step2Labels := by
      have ha : raw27723step2 = (fun i j => raw27723step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27723step2 raw27723step1; decide +kernel
      have hl : raw27723step2Labels = raw27723step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27723step1 raw27723step1Labels permutation12 permutation5
    mixedMoment B raw27723step2 raw27723step2Labels = mixedMoment B raw27723step3 raw27723step3Labels := by
      have ha : raw27723step3 = -raw27723step2 := by apply Matrix.ext; change ∀ i j, raw27723step3 i j = -(raw27723step2 i j); unfold raw27723step3 raw27723step2; decide +kernel
      have hl : raw27723step3Labels = raw27723step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27723step3 raw27723step3Labels = mixedMoment B raw27723step4 raw27723step4Labels := by
      have ha : raw27723step4 = raw27723step3 := by apply Matrix.ext; unfold raw27723step4 raw27723step3; decide +kernel
      have hl : raw27723step3Labels = labelEmbedding1 ∘ raw27723step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27723step3 raw27723step3Labels raw27723step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1745 node1745Labels := by rfl

theorem canonical27724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27724 raw27724Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw27724 raw27724Labels = mixedMoment B raw27724step0 raw27724step0Labels := by
      have hz : ∀ j, raw27724 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27724step0 = (fun i j => raw27724 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27724step0 raw27724; decide +kernel
      have hl : raw27724step0Labels = raw27724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27724 raw27724Labels permutation434 hz
    mixedMoment B raw27724step0 raw27724step0Labels = mixedMoment B raw27724step1 raw27724step1Labels := by
      have ha : raw27724step1 = (fun i j => raw27724step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27724step1 raw27724step0; decide +kernel
      have hl : raw27724step1Labels = raw27724step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27724step0 raw27724step0Labels permutation145 permutation7
    mixedMoment B raw27724step1 raw27724step1Labels = mixedMoment B raw27724step2 raw27724step2Labels := by
      have ha : raw27724step2 = raw27724step1 := by apply Matrix.ext; unfold raw27724step2 raw27724step1; decide +kernel
      have hl : raw27724step1Labels = labelEmbedding1 ∘ raw27724step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27724step1 raw27724step1Labels raw27724step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

theorem canonical27725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27725 raw27725Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw27725 raw27725Labels = mixedMoment B raw27725step0 raw27725step0Labels := by
      have hz : ∀ j, raw27725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27725step0 = (fun i j => raw27725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27725step0 raw27725; decide +kernel
      have hl : raw27725step0Labels = raw27725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27725 raw27725Labels permutation346 hz
    mixedMoment B raw27725step0 raw27725step0Labels = mixedMoment B raw27725step1 raw27725step1Labels := by
      have ha : raw27725step1 = (fun i j => raw27725step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27725step1 raw27725step0; decide +kernel
      have hl : raw27725step1Labels = raw27725step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27725step0 raw27725step0Labels permutation145 permutation7
    mixedMoment B raw27725step1 raw27725step1Labels = mixedMoment B raw27725step2 raw27725step2Labels := by
      have ha : raw27725step2 = raw27725step1 := by apply Matrix.ext; unfold raw27725step2 raw27725step1; decide +kernel
      have hl : raw27725step1Labels = labelEmbedding1 ∘ raw27725step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27725step1 raw27725step1Labels raw27725step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

theorem canonical27726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27726 raw27726Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw27726 raw27726Labels = mixedMoment B raw27726step0 raw27726step0Labels := by
      have hz : ∀ j, raw27726 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27726step0 = (fun i j => raw27726 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27726step0 raw27726; decide +kernel
      have hl : raw27726step0Labels = raw27726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27726 raw27726Labels permutation434 hz
    mixedMoment B raw27726step0 raw27726step0Labels = mixedMoment B raw27726step1 raw27726step1Labels := by
      have hz : ∀ j, raw27726step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27726step1 = (fun i j => raw27726step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27726step1 raw27726step0; decide +kernel
      have hl : raw27726step1Labels = raw27726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27726step0 raw27726step0Labels permutation80 hz
    mixedMoment B raw27726step1 raw27726step1Labels = mixedMoment B raw27726step2 raw27726step2Labels := by
      have ha : raw27726step2 = (fun i j => raw27726step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27726step2 raw27726step1; decide +kernel
      have hl : raw27726step2Labels = raw27726step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27726step1 raw27726step1Labels permutation29 permutation7
    mixedMoment B raw27726step2 raw27726step2Labels = mixedMoment B raw27726step3 raw27726step3Labels := by
      have ha : raw27726step3 = raw27726step2 := by apply Matrix.ext; unfold raw27726step3 raw27726step2; decide +kernel
      have hl : raw27726step2Labels = labelEmbedding1 ∘ raw27726step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27726step2 raw27726step2Labels raw27726step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

theorem canonical27727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27727 raw27727Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw27727 raw27727Labels = mixedMoment B raw27727step0 raw27727step0Labels := by
      have hz : ∀ j, raw27727 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27727step0 = (fun i j => raw27727 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27727step0 raw27727; decide +kernel
      have hl : raw27727step0Labels = raw27727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27727 raw27727Labels permutation434 hz
    mixedMoment B raw27727step0 raw27727step0Labels = mixedMoment B raw27727step1 raw27727step1Labels := by
      have hz : ∀ j, raw27727step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27727step1 = (fun i j => raw27727step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27727step1 raw27727step0; decide +kernel
      have hl : raw27727step1Labels = raw27727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27727step0 raw27727step0Labels permutation80 hz
    mixedMoment B raw27727step1 raw27727step1Labels = mixedMoment B raw27727step2 raw27727step2Labels := by
      have ha : raw27727step2 = (fun i j => raw27727step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27727step2 raw27727step1; decide +kernel
      have hl : raw27727step2Labels = raw27727step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27727step1 raw27727step1Labels permutation31 permutation7
    mixedMoment B raw27727step2 raw27727step2Labels = mixedMoment B raw27727step3 raw27727step3Labels := by
      have ha : raw27727step3 = raw27727step2 := by apply Matrix.ext; unfold raw27727step3 raw27727step2; decide +kernel
      have hl : raw27727step2Labels = labelEmbedding1 ∘ raw27727step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27727step2 raw27727step2Labels raw27727step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

theorem canonical27728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27728 raw27728Labels = mixedMoment B node1686 node1686Labels := by
  calc
    mixedMoment B raw27728 raw27728Labels = mixedMoment B raw27728step0 raw27728step0Labels := by
      have hz : ∀ j, raw27728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27728step0 = (fun i j => raw27728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27728step0 raw27728; decide +kernel
      have hl : raw27728step0Labels = raw27728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27728 raw27728Labels permutation434 hz
    mixedMoment B raw27728step0 raw27728step0Labels = mixedMoment B raw27728step1 raw27728step1Labels := by
      have ha : raw27728step1 = (fun i j => raw27728step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27728step1 raw27728step0; decide +kernel
      have hl : raw27728step1Labels = raw27728step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27728step0 raw27728step0Labels permutation36 permutation5
    mixedMoment B raw27728step1 raw27728step1Labels = mixedMoment B raw27728step2 raw27728step2Labels := by
      have ha : raw27728step2 = -raw27728step1 := by apply Matrix.ext; change ∀ i j, raw27728step2 i j = -(raw27728step1 i j); unfold raw27728step2 raw27728step1; decide +kernel
      have hl : raw27728step2Labels = raw27728step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27728step2 raw27728step2Labels = mixedMoment B raw27728step3 raw27728step3Labels := by
      have ha : raw27728step3 = raw27728step2 := by apply Matrix.ext; unfold raw27728step3 raw27728step2; decide +kernel
      have hl : raw27728step2Labels = labelEmbedding1 ∘ raw27728step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27728step2 raw27728step2Labels raw27728step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1686 node1686Labels := by rfl

theorem canonical27729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27729 raw27729Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw27729 raw27729Labels = mixedMoment B raw27729step0 raw27729step0Labels := by
      have hz : ∀ j, raw27729 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27729step0 = (fun i j => raw27729 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27729step0 raw27729; decide +kernel
      have hl : raw27729step0Labels = raw27729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27729 raw27729Labels permutation434 hz
    mixedMoment B raw27729step0 raw27729step0Labels = mixedMoment B raw27729step1 raw27729step1Labels := by
      have ha : raw27729step1 = (fun i j => raw27729step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27729step1 raw27729step0; decide +kernel
      have hl : raw27729step1Labels = raw27729step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27729step0 raw27729step0Labels permutation145 permutation7
    mixedMoment B raw27729step1 raw27729step1Labels = mixedMoment B raw27729step2 raw27729step2Labels := by
      have ha : raw27729step2 = raw27729step1 := by apply Matrix.ext; unfold raw27729step2 raw27729step1; decide +kernel
      have hl : raw27729step1Labels = labelEmbedding1 ∘ raw27729step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27729step1 raw27729step1Labels raw27729step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

theorem canonical27730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27730 raw27730Labels = mixedMoment B node2198 node2198Labels := by
  calc
    mixedMoment B raw27730 raw27730Labels = mixedMoment B raw27730step0 raw27730step0Labels := by
      have ha : raw27730step0 = (fun i j => raw27730 (permutation640 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27730step0 raw27730; decide +kernel
      have hl : raw27730step0Labels = raw27730Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27730 raw27730Labels permutation640 permutation7
    mixedMoment B raw27730step0 raw27730step0Labels = mixedMoment B raw27730step1 raw27730step1Labels := by
      have ha : raw27730step1 = raw27730step0 := by apply Matrix.ext; unfold raw27730step1 raw27730step0; decide +kernel
      have hl : raw27730step0Labels = labelEmbedding1 ∘ raw27730step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27730step0 raw27730step0Labels raw27730step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2198 node2198Labels := by rfl

theorem canonical27731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27731 raw27731Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw27731 raw27731Labels = mixedMoment B raw27731step0 raw27731step0Labels := by
      have hz : ∀ j, raw27731 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27731step0 = (fun i j => raw27731 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27731step0 raw27731; decide +kernel
      have hl : raw27731step0Labels = raw27731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27731 raw27731Labels permutation434 hz
    mixedMoment B raw27731step0 raw27731step0Labels = mixedMoment B raw27731step1 raw27731step1Labels := by
      have ha : raw27731step1 = (fun i j => raw27731step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27731step1 raw27731step0; decide +kernel
      have hl : raw27731step1Labels = raw27731step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27731step0 raw27731step0Labels permutation145 permutation7
    mixedMoment B raw27731step1 raw27731step1Labels = mixedMoment B raw27731step2 raw27731step2Labels := by
      have ha : raw27731step2 = raw27731step1 := by apply Matrix.ext; unfold raw27731step2 raw27731step1; decide +kernel
      have hl : raw27731step1Labels = labelEmbedding1 ∘ raw27731step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27731step1 raw27731step1Labels raw27731step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical27732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27732 raw27732Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw27732 raw27732Labels = mixedMoment B raw27732step0 raw27732step0Labels := by
      have hz : ∀ j, raw27732 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27732step0 = (fun i j => raw27732 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27732step0 raw27732; decide +kernel
      have hl : raw27732step0Labels = raw27732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27732 raw27732Labels permutation434 hz
    mixedMoment B raw27732step0 raw27732step0Labels = mixedMoment B raw27732step1 raw27732step1Labels := by
      have ha : raw27732step1 = (fun i j => raw27732step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27732step1 raw27732step0; decide +kernel
      have hl : raw27732step1Labels = raw27732step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27732step0 raw27732step0Labels permutation145 permutation7
    mixedMoment B raw27732step1 raw27732step1Labels = mixedMoment B raw27732step2 raw27732step2Labels := by
      have ha : raw27732step2 = raw27732step1 := by apply Matrix.ext; unfold raw27732step2 raw27732step1; decide +kernel
      have hl : raw27732step1Labels = labelEmbedding1 ∘ raw27732step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27732step1 raw27732step1Labels raw27732step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

theorem canonical27733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27733 raw27733Labels = mixedMoment B node1686 node1686Labels := by
  calc
    mixedMoment B raw27733 raw27733Labels = mixedMoment B raw27733step0 raw27733step0Labels := by
      have hz : ∀ j, raw27733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27733step0 = (fun i j => raw27733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27733step0 raw27733; decide +kernel
      have hl : raw27733step0Labels = raw27733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27733 raw27733Labels permutation346 hz
    mixedMoment B raw27733step0 raw27733step0Labels = mixedMoment B raw27733step1 raw27733step1Labels := by
      have ha : raw27733step1 = (fun i j => raw27733step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27733step1 raw27733step0; decide +kernel
      have hl : raw27733step1Labels = raw27733step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27733step0 raw27733step0Labels permutation36 permutation5
    mixedMoment B raw27733step1 raw27733step1Labels = mixedMoment B raw27733step2 raw27733step2Labels := by
      have ha : raw27733step2 = -raw27733step1 := by apply Matrix.ext; change ∀ i j, raw27733step2 i j = -(raw27733step1 i j); unfold raw27733step2 raw27733step1; decide +kernel
      have hl : raw27733step2Labels = raw27733step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27733step2 raw27733step2Labels = mixedMoment B raw27733step3 raw27733step3Labels := by
      have ha : raw27733step3 = raw27733step2 := by apply Matrix.ext; unfold raw27733step3 raw27733step2; decide +kernel
      have hl : raw27733step2Labels = labelEmbedding1 ∘ raw27733step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27733step2 raw27733step2Labels raw27733step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1686 node1686Labels := by rfl

theorem canonical27734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27734 raw27734Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw27734 raw27734Labels = mixedMoment B raw27734step0 raw27734step0Labels := by
      have hz : ∀ j, raw27734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27734step0 = (fun i j => raw27734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27734step0 raw27734; decide +kernel
      have hl : raw27734step0Labels = raw27734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27734 raw27734Labels permutation346 hz
    mixedMoment B raw27734step0 raw27734step0Labels = mixedMoment B raw27734step1 raw27734step1Labels := by
      have ha : raw27734step1 = (fun i j => raw27734step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27734step1 raw27734step0; decide +kernel
      have hl : raw27734step1Labels = raw27734step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27734step0 raw27734step0Labels permutation145 permutation7
    mixedMoment B raw27734step1 raw27734step1Labels = mixedMoment B raw27734step2 raw27734step2Labels := by
      have ha : raw27734step2 = raw27734step1 := by apply Matrix.ext; unfold raw27734step2 raw27734step1; decide +kernel
      have hl : raw27734step1Labels = labelEmbedding1 ∘ raw27734step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27734step1 raw27734step1Labels raw27734step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

theorem canonical27735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27735 raw27735Labels = mixedMoment B node2198 node2198Labels := by
  calc
    mixedMoment B raw27735 raw27735Labels = mixedMoment B raw27735step0 raw27735step0Labels := by
      have ha : raw27735step0 = (fun i j => raw27735 (permutation658 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27735step0 raw27735; decide +kernel
      have hl : raw27735step0Labels = raw27735Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27735 raw27735Labels permutation658 permutation7
    mixedMoment B raw27735step0 raw27735step0Labels = mixedMoment B raw27735step1 raw27735step1Labels := by
      have ha : raw27735step1 = raw27735step0 := by apply Matrix.ext; unfold raw27735step1 raw27735step0; decide +kernel
      have hl : raw27735step0Labels = labelEmbedding1 ∘ raw27735step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27735step0 raw27735step0Labels raw27735step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2198 node2198Labels := by rfl

theorem canonical27736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27736 raw27736Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw27736 raw27736Labels = mixedMoment B raw27736step0 raw27736step0Labels := by
      have hz : ∀ j, raw27736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27736step0 = (fun i j => raw27736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27736step0 raw27736; decide +kernel
      have hl : raw27736step0Labels = raw27736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27736 raw27736Labels permutation346 hz
    mixedMoment B raw27736step0 raw27736step0Labels = mixedMoment B raw27736step1 raw27736step1Labels := by
      have ha : raw27736step1 = (fun i j => raw27736step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27736step1 raw27736step0; decide +kernel
      have hl : raw27736step1Labels = raw27736step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27736step0 raw27736step0Labels permutation145 permutation7
    mixedMoment B raw27736step1 raw27736step1Labels = mixedMoment B raw27736step2 raw27736step2Labels := by
      have ha : raw27736step2 = raw27736step1 := by apply Matrix.ext; unfold raw27736step2 raw27736step1; decide +kernel
      have hl : raw27736step1Labels = labelEmbedding1 ∘ raw27736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27736step1 raw27736step1Labels raw27736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical27737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27737 raw27737Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw27737 raw27737Labels = mixedMoment B raw27737step0 raw27737step0Labels := by
      have hz : ∀ j, raw27737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27737step0 = (fun i j => raw27737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27737step0 raw27737; decide +kernel
      have hl : raw27737step0Labels = raw27737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27737 raw27737Labels permutation346 hz
    mixedMoment B raw27737step0 raw27737step0Labels = mixedMoment B raw27737step1 raw27737step1Labels := by
      have ha : raw27737step1 = (fun i j => raw27737step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27737step1 raw27737step0; decide +kernel
      have hl : raw27737step1Labels = raw27737step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27737step0 raw27737step0Labels permutation145 permutation7
    mixedMoment B raw27737step1 raw27737step1Labels = mixedMoment B raw27737step2 raw27737step2Labels := by
      have ha : raw27737step2 = raw27737step1 := by apply Matrix.ext; unfold raw27737step2 raw27737step1; decide +kernel
      have hl : raw27737step1Labels = labelEmbedding1 ∘ raw27737step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27737step1 raw27737step1Labels raw27737step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

theorem canonical27738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27738 raw27738Labels = mixedMoment B node1687 node1687Labels := by
  calc
    mixedMoment B raw27738 raw27738Labels = mixedMoment B raw27738step0 raw27738step0Labels := by
      have hz : ∀ j, raw27738 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27738step0 = (fun i j => raw27738 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27738step0 raw27738; decide +kernel
      have hl : raw27738step0Labels = raw27738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27738 raw27738Labels permutation434 hz
    mixedMoment B raw27738step0 raw27738step0Labels = mixedMoment B raw27738step1 raw27738step1Labels := by
      have hz : ∀ j, raw27738step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27738step1 = (fun i j => raw27738step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27738step1 raw27738step0; decide +kernel
      have hl : raw27738step1Labels = raw27738step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27738step0 raw27738step0Labels permutation80 hz
    mixedMoment B raw27738step1 raw27738step1Labels = mixedMoment B raw27738step2 raw27738step2Labels := by
      have ha : raw27738step2 = (fun i j => raw27738step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27738step2 raw27738step1; decide +kernel
      have hl : raw27738step2Labels = raw27738step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27738step1 raw27738step1Labels permutation9 permutation5
    mixedMoment B raw27738step2 raw27738step2Labels = mixedMoment B raw27738step3 raw27738step3Labels := by
      have ha : raw27738step3 = -raw27738step2 := by apply Matrix.ext; change ∀ i j, raw27738step3 i j = -(raw27738step2 i j); unfold raw27738step3 raw27738step2; decide +kernel
      have hl : raw27738step3Labels = raw27738step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27738step3 raw27738step3Labels = mixedMoment B raw27738step4 raw27738step4Labels := by
      have ha : raw27738step4 = raw27738step3 := by apply Matrix.ext; unfold raw27738step4 raw27738step3; decide +kernel
      have hl : raw27738step3Labels = labelEmbedding1 ∘ raw27738step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27738step3 raw27738step3Labels raw27738step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1687 node1687Labels := by rfl

theorem canonical27739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27739 raw27739Labels = mixedMoment B node2286 node2286Labels := by
  calc
    mixedMoment B raw27739 raw27739Labels = mixedMoment B raw27739step0 raw27739step0Labels := by
      have hz : ∀ j, raw27739 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27739step0 = (fun i j => raw27739 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27739step0 raw27739; decide +kernel
      have hl : raw27739step0Labels = raw27739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27739 raw27739Labels permutation434 hz
    mixedMoment B raw27739step0 raw27739step0Labels = mixedMoment B raw27739step1 raw27739step1Labels := by
      have hz : ∀ j, raw27739step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27739step1 = (fun i j => raw27739step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27739step1 raw27739step0; decide +kernel
      have hl : raw27739step1Labels = raw27739step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27739step0 raw27739step0Labels permutation80 hz
    mixedMoment B raw27739step1 raw27739step1Labels = mixedMoment B raw27739step2 raw27739step2Labels := by
      have ha : raw27739step2 = (fun i j => raw27739step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27739step2 raw27739step1; decide +kernel
      have hl : raw27739step2Labels = raw27739step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27739step1 raw27739step1Labels permutation31 permutation7
    mixedMoment B raw27739step2 raw27739step2Labels = mixedMoment B raw27739step3 raw27739step3Labels := by
      have ha : raw27739step3 = raw27739step2 := by apply Matrix.ext; unfold raw27739step3 raw27739step2; decide +kernel
      have hl : raw27739step2Labels = labelEmbedding1 ∘ raw27739step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27739step2 raw27739step2Labels raw27739step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2286 node2286Labels := by rfl

theorem canonical27740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27740 raw27740Labels = mixedMoment B node2256 node2256Labels := by
  calc
    mixedMoment B raw27740 raw27740Labels = mixedMoment B raw27740step0 raw27740step0Labels := by
      have hz : ∀ j, raw27740 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27740step0 = (fun i j => raw27740 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27740step0 raw27740; decide +kernel
      have hl : raw27740step0Labels = raw27740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27740 raw27740Labels permutation434 hz
    mixedMoment B raw27740step0 raw27740step0Labels = mixedMoment B raw27740step1 raw27740step1Labels := by
      have ha : raw27740step1 = (fun i j => raw27740step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27740step1 raw27740step0; decide +kernel
      have hl : raw27740step1Labels = raw27740step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27740step0 raw27740step0Labels permutation145 permutation7
    mixedMoment B raw27740step1 raw27740step1Labels = mixedMoment B raw27740step2 raw27740step2Labels := by
      have ha : raw27740step2 = raw27740step1 := by apply Matrix.ext; unfold raw27740step2 raw27740step1; decide +kernel
      have hl : raw27740step1Labels = labelEmbedding1 ∘ raw27740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27740step1 raw27740step1Labels raw27740step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2256 node2256Labels := by rfl

theorem canonical27741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27741 raw27741Labels = mixedMoment B node2256 node2256Labels := by
  calc
    mixedMoment B raw27741 raw27741Labels = mixedMoment B raw27741step0 raw27741step0Labels := by
      have hz : ∀ j, raw27741 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27741step0 = (fun i j => raw27741 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27741step0 raw27741; decide +kernel
      have hl : raw27741step0Labels = raw27741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27741 raw27741Labels permutation346 hz
    mixedMoment B raw27741step0 raw27741step0Labels = mixedMoment B raw27741step1 raw27741step1Labels := by
      have ha : raw27741step1 = (fun i j => raw27741step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27741step1 raw27741step0; decide +kernel
      have hl : raw27741step1Labels = raw27741step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27741step0 raw27741step0Labels permutation145 permutation7
    mixedMoment B raw27741step1 raw27741step1Labels = mixedMoment B raw27741step2 raw27741step2Labels := by
      have ha : raw27741step2 = raw27741step1 := by apply Matrix.ext; unfold raw27741step2 raw27741step1; decide +kernel
      have hl : raw27741step1Labels = labelEmbedding1 ∘ raw27741step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27741step1 raw27741step1Labels raw27741step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2256 node2256Labels := by rfl

theorem canonical27742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27742 raw27742Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw27742 raw27742Labels = mixedMoment B raw27742step0 raw27742step0Labels := by
      have hz : ∀ j, raw27742 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27742step0 = (fun i j => raw27742 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27742step0 raw27742; decide +kernel
      have hl : raw27742step0Labels = raw27742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27742 raw27742Labels permutation434 hz
    mixedMoment B raw27742step0 raw27742step0Labels = mixedMoment B raw27742step1 raw27742step1Labels := by
      have hz : ∀ j, raw27742step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27742step1 = (fun i j => raw27742step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27742step1 raw27742step0; decide +kernel
      have hl : raw27742step1Labels = raw27742step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27742step0 raw27742step0Labels permutation80 hz
    mixedMoment B raw27742step1 raw27742step1Labels = mixedMoment B raw27742step2 raw27742step2Labels := by
      have ha : raw27742step2 = (fun i j => raw27742step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27742step2 raw27742step1; decide +kernel
      have hl : raw27742step2Labels = raw27742step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27742step1 raw27742step1Labels permutation23 permutation5
    mixedMoment B raw27742step2 raw27742step2Labels = mixedMoment B raw27742step3 raw27742step3Labels := by
      have ha : raw27742step3 = raw27742step2 := by apply Matrix.ext; unfold raw27742step3 raw27742step2; decide +kernel
      have hl : raw27742step2Labels = labelEmbedding1 ∘ raw27742step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27742step2 raw27742step2Labels raw27742step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

theorem canonical27743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27743 raw27743Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw27743 raw27743Labels = mixedMoment B raw27743step0 raw27743step0Labels := by
      have hz : ∀ j, raw27743 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27743step0 = (fun i j => raw27743 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27743step0 raw27743; decide +kernel
      have hl : raw27743step0Labels = raw27743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27743 raw27743Labels permutation434 hz
    mixedMoment B raw27743step0 raw27743step0Labels = mixedMoment B raw27743step1 raw27743step1Labels := by
      have hz : ∀ j, raw27743step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27743step1 = (fun i j => raw27743step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27743step1 raw27743step0; decide +kernel
      have hl : raw27743step1Labels = raw27743step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27743step0 raw27743step0Labels permutation80 hz
    mixedMoment B raw27743step1 raw27743step1Labels = mixedMoment B raw27743step2 raw27743step2Labels := by
      have ha : raw27743step2 = (fun i j => raw27743step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27743step2 raw27743step1; decide +kernel
      have hl : raw27743step2Labels = raw27743step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27743step1 raw27743step1Labels permutation9 permutation5
    mixedMoment B raw27743step2 raw27743step2Labels = mixedMoment B raw27743step3 raw27743step3Labels := by
      have ha : raw27743step3 = -raw27743step2 := by apply Matrix.ext; change ∀ i j, raw27743step3 i j = -(raw27743step2 i j); unfold raw27743step3 raw27743step2; decide +kernel
      have hl : raw27743step3Labels = raw27743step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27743step3 raw27743step3Labels = mixedMoment B raw27743step4 raw27743step4Labels := by
      have ha : raw27743step4 = raw27743step3 := by apply Matrix.ext; unfold raw27743step4 raw27743step3; decide +kernel
      have hl : raw27743step3Labels = labelEmbedding1 ∘ raw27743step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27743step3 raw27743step3Labels raw27743step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1695 node1695Labels := by rfl

theorem canonical27744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27744 raw27744Labels = mixedMoment B node1748 node1748Labels := by
  calc
    mixedMoment B raw27744 raw27744Labels = mixedMoment B raw27744step0 raw27744step0Labels := by
      have hz : ∀ j, raw27744 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27744step0 = (fun i j => raw27744 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27744step0 raw27744; decide +kernel
      have hl : raw27744step0Labels = raw27744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27744 raw27744Labels permutation434 hz
    mixedMoment B raw27744step0 raw27744step0Labels = mixedMoment B raw27744step1 raw27744step1Labels := by
      have hz : ∀ j, raw27744step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27744step1 = (fun i j => raw27744step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27744step1 raw27744step0; decide +kernel
      have hl : raw27744step1Labels = raw27744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27744step0 raw27744step0Labels permutation80 hz
    mixedMoment B raw27744step1 raw27744step1Labels = mixedMoment B raw27744step2 raw27744step2Labels := by
      have ha : raw27744step2 = (fun i j => raw27744step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27744step2 raw27744step1; decide +kernel
      have hl : raw27744step2Labels = raw27744step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27744step1 raw27744step1Labels permutation31 permutation7
    mixedMoment B raw27744step2 raw27744step2Labels = mixedMoment B raw27744step3 raw27744step3Labels := by
      have ha : raw27744step3 = raw27744step2 := by apply Matrix.ext; unfold raw27744step3 raw27744step2; decide +kernel
      have hl : raw27744step2Labels = labelEmbedding1 ∘ raw27744step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27744step2 raw27744step2Labels raw27744step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1748 node1748Labels := by rfl

theorem canonical27745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27745 raw27745Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw27745 raw27745Labels = mixedMoment B raw27745step0 raw27745step0Labels := by
      have hz : ∀ j, raw27745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27745step0 = (fun i j => raw27745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27745step0 raw27745; decide +kernel
      have hl : raw27745step0Labels = raw27745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27745 raw27745Labels permutation434 hz
    mixedMoment B raw27745step0 raw27745step0Labels = mixedMoment B raw27745step1 raw27745step1Labels := by
      have ha : raw27745step1 = (fun i j => raw27745step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27745step1 raw27745step0; decide +kernel
      have hl : raw27745step1Labels = raw27745step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27745step0 raw27745step0Labels permutation145 permutation7
    mixedMoment B raw27745step1 raw27745step1Labels = mixedMoment B raw27745step2 raw27745step2Labels := by
      have ha : raw27745step2 = raw27745step1 := by apply Matrix.ext; unfold raw27745step2 raw27745step1; decide +kernel
      have hl : raw27745step1Labels = labelEmbedding1 ∘ raw27745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27745step1 raw27745step1Labels raw27745step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

theorem canonical27746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27746 raw27746Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw27746 raw27746Labels = mixedMoment B raw27746step0 raw27746step0Labels := by
      have hz : ∀ j, raw27746 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27746step0 = (fun i j => raw27746 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27746step0 raw27746; decide +kernel
      have hl : raw27746step0Labels = raw27746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27746 raw27746Labels permutation346 hz
    mixedMoment B raw27746step0 raw27746step0Labels = mixedMoment B raw27746step1 raw27746step1Labels := by
      have ha : raw27746step1 = (fun i j => raw27746step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27746step1 raw27746step0; decide +kernel
      have hl : raw27746step1Labels = raw27746step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27746step0 raw27746step0Labels permutation145 permutation7
    mixedMoment B raw27746step1 raw27746step1Labels = mixedMoment B raw27746step2 raw27746step2Labels := by
      have ha : raw27746step2 = raw27746step1 := by apply Matrix.ext; unfold raw27746step2 raw27746step1; decide +kernel
      have hl : raw27746step1Labels = labelEmbedding1 ∘ raw27746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27746step1 raw27746step1Labels raw27746step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

theorem canonical27747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27747 raw27747Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw27747 raw27747Labels = mixedMoment B raw27747step0 raw27747step0Labels := by
      have hz : ∀ j, raw27747 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27747step0 = (fun i j => raw27747 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27747step0 raw27747; decide +kernel
      have hl : raw27747step0Labels = raw27747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27747 raw27747Labels permutation434 hz
    mixedMoment B raw27747step0 raw27747step0Labels = mixedMoment B raw27747step1 raw27747step1Labels := by
      have hz : ∀ j, raw27747step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27747step1 = (fun i j => raw27747step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27747step1 raw27747step0; decide +kernel
      have hl : raw27747step1Labels = raw27747step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27747step0 raw27747step0Labels permutation80 hz
    mixedMoment B raw27747step1 raw27747step1Labels = mixedMoment B raw27747step2 raw27747step2Labels := by
      have ha : raw27747step2 = (fun i j => raw27747step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27747step2 raw27747step1; decide +kernel
      have hl : raw27747step2Labels = raw27747step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27747step1 raw27747step1Labels permutation31 permutation7
    mixedMoment B raw27747step2 raw27747step2Labels = mixedMoment B raw27747step3 raw27747step3Labels := by
      have ha : raw27747step3 = raw27747step2 := by apply Matrix.ext; unfold raw27747step3 raw27747step2; decide +kernel
      have hl : raw27747step2Labels = labelEmbedding1 ∘ raw27747step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27747step2 raw27747step2Labels raw27747step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical27748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27748 raw27748Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw27748 raw27748Labels = mixedMoment B raw27748step0 raw27748step0Labels := by
      have hz : ∀ j, raw27748 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27748step0 = (fun i j => raw27748 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27748step0 raw27748; decide +kernel
      have hl : raw27748step0Labels = raw27748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27748 raw27748Labels permutation434 hz
    mixedMoment B raw27748step0 raw27748step0Labels = mixedMoment B raw27748step1 raw27748step1Labels := by
      have hz : ∀ j, raw27748step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27748step1 = (fun i j => raw27748step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27748step1 raw27748step0; decide +kernel
      have hl : raw27748step1Labels = raw27748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27748step0 raw27748step0Labels permutation80 hz
    mixedMoment B raw27748step1 raw27748step1Labels = mixedMoment B raw27748step2 raw27748step2Labels := by
      have ha : raw27748step2 = (fun i j => raw27748step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27748step2 raw27748step1; decide +kernel
      have hl : raw27748step2Labels = raw27748step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27748step1 raw27748step1Labels permutation30 permutation2
    mixedMoment B raw27748step2 raw27748step2Labels = mixedMoment B raw27748step3 raw27748step3Labels := by
      have ha : raw27748step3 = -raw27748step2 := by apply Matrix.ext; change ∀ i j, raw27748step3 i j = -(raw27748step2 i j); unfold raw27748step3 raw27748step2; decide +kernel
      have hl : raw27748step3Labels = raw27748step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2116 node2116Labels := by rfl

theorem canonical27749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27749 raw27749Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw27749 raw27749Labels = mixedMoment B raw27749step0 raw27749step0Labels := by
      have hz : ∀ j, raw27749 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27749step0 = (fun i j => raw27749 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27749step0 raw27749; decide +kernel
      have hl : raw27749step0Labels = raw27749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27749 raw27749Labels permutation434 hz
    mixedMoment B raw27749step0 raw27749step0Labels = mixedMoment B raw27749step1 raw27749step1Labels := by
      have hz : ∀ j, raw27749step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27749step1 = (fun i j => raw27749step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27749step1 raw27749step0; decide +kernel
      have hl : raw27749step1Labels = raw27749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27749step0 raw27749step0Labels permutation80 hz
    mixedMoment B raw27749step1 raw27749step1Labels = mixedMoment B raw27749step2 raw27749step2Labels := by
      have ha : raw27749step2 = (fun i j => raw27749step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27749step2 raw27749step1; decide +kernel
      have hl : raw27749step2Labels = raw27749step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27749step1 raw27749step1Labels permutation31 permutation2
    mixedMoment B raw27749step2 raw27749step2Labels = mixedMoment B raw27749step3 raw27749step3Labels := by
      have ha : raw27749step3 = -raw27749step2 := by apply Matrix.ext; change ∀ i j, raw27749step3 i j = -(raw27749step2 i j); unfold raw27749step3 raw27749step2; decide +kernel
      have hl : raw27749step3Labels = raw27749step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2112 node2112Labels := by rfl

theorem canonical27750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27750 raw27750Labels = mixedMoment B node1979 node1979Labels := by
  calc
    mixedMoment B raw27750 raw27750Labels = mixedMoment B raw27750step0 raw27750step0Labels := by
      have hz : ∀ j, raw27750 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27750step0 = (fun i j => raw27750 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27750step0 raw27750; decide +kernel
      have hl : raw27750step0Labels = raw27750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27750 raw27750Labels permutation434 hz
    mixedMoment B raw27750step0 raw27750step0Labels = mixedMoment B raw27750step1 raw27750step1Labels := by
      have ha : raw27750step1 = (fun i j => raw27750step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27750step1 raw27750step0; decide +kernel
      have hl : raw27750step1Labels = raw27750step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27750step0 raw27750step0Labels permutation145 permutation2
    mixedMoment B raw27750step1 raw27750step1Labels = mixedMoment B raw27750step2 raw27750step2Labels := by
      have ha : raw27750step2 = -raw27750step1 := by apply Matrix.ext; change ∀ i j, raw27750step2 i j = -(raw27750step1 i j); unfold raw27750step2 raw27750step1; decide +kernel
      have hl : raw27750step2Labels = raw27750step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1979 node1979Labels := by rfl

theorem canonical27751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27751 raw27751Labels = mixedMoment B node1979 node1979Labels := by
  calc
    mixedMoment B raw27751 raw27751Labels = mixedMoment B raw27751step0 raw27751step0Labels := by
      have hz : ∀ j, raw27751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27751step0 = (fun i j => raw27751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27751step0 raw27751; decide +kernel
      have hl : raw27751step0Labels = raw27751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27751 raw27751Labels permutation346 hz
    mixedMoment B raw27751step0 raw27751step0Labels = mixedMoment B raw27751step1 raw27751step1Labels := by
      have ha : raw27751step1 = (fun i j => raw27751step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27751step1 raw27751step0; decide +kernel
      have hl : raw27751step1Labels = raw27751step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27751step0 raw27751step0Labels permutation145 permutation2
    mixedMoment B raw27751step1 raw27751step1Labels = mixedMoment B raw27751step2 raw27751step2Labels := by
      have ha : raw27751step2 = -raw27751step1 := by apply Matrix.ext; change ∀ i j, raw27751step2 i j = -(raw27751step1 i j); unfold raw27751step2 raw27751step1; decide +kernel
      have hl : raw27751step2Labels = raw27751step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1979 node1979Labels := by rfl

theorem canonical27752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27752 raw27752Labels = mixedMoment B node1831 node1831Labels := by
  calc
    mixedMoment B raw27752 raw27752Labels = mixedMoment B raw27752step0 raw27752step0Labels := by
      have hz : ∀ j, raw27752 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27752step0 = (fun i j => raw27752 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27752step0 raw27752; decide +kernel
      have hl : raw27752step0Labels = raw27752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27752 raw27752Labels permutation434 hz
    mixedMoment B raw27752step0 raw27752step0Labels = mixedMoment B raw27752step1 raw27752step1Labels := by
      have hz : ∀ j, raw27752step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27752step1 = (fun i j => raw27752step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27752step1 raw27752step0; decide +kernel
      have hl : raw27752step1Labels = raw27752step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27752step0 raw27752step0Labels permutation80 hz
    mixedMoment B raw27752step1 raw27752step1Labels = mixedMoment B raw27752step2 raw27752step2Labels := by
      have ha : raw27752step2 = (fun i j => raw27752step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27752step2 raw27752step1; decide +kernel
      have hl : raw27752step2Labels = raw27752step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27752step1 raw27752step1Labels permutation31 permutation2
    mixedMoment B raw27752step2 raw27752step2Labels = mixedMoment B raw27752step3 raw27752step3Labels := by
      have ha : raw27752step3 = -raw27752step2 := by apply Matrix.ext; change ∀ i j, raw27752step3 i j = -(raw27752step2 i j); unfold raw27752step3 raw27752step2; decide +kernel
      have hl : raw27752step3Labels = raw27752step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1831 node1831Labels := by rfl

theorem canonical27753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27753 raw27753Labels = mixedMoment B node953 node953Labels := by
  calc
    mixedMoment B raw27753 raw27753Labels = mixedMoment B raw27753step0 raw27753step0Labels := by
      have hz : ∀ j, raw27753 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27753step0 = (fun i j => raw27753 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27753step0 raw27753; decide +kernel
      have hl : raw27753step0Labels = raw27753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27753 raw27753Labels permutation434 hz
    mixedMoment B raw27753step0 raw27753step0Labels = mixedMoment B raw27753step1 raw27753step1Labels := by
      have hz : ∀ j, raw27753step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27753step1 = (fun i j => raw27753step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27753step1 raw27753step0; decide +kernel
      have hl : raw27753step1Labels = raw27753step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27753step0 raw27753step0Labels permutation80 hz
    mixedMoment B raw27753step1 raw27753step1Labels = mixedMoment B raw27753step2 raw27753step2Labels := by
      have ha : raw27753step2 = (fun i j => raw27753step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27753step2 raw27753step1; decide +kernel
      have hl : raw27753step2Labels = raw27753step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27753step1 raw27753step1Labels permutation31 permutation2
    mixedMoment B raw27753step2 raw27753step2Labels = mixedMoment B raw27753step3 raw27753step3Labels := by
      have ha : raw27753step3 = -raw27753step2 := by apply Matrix.ext; change ∀ i j, raw27753step3 i j = -(raw27753step2 i j); unfold raw27753step3 raw27753step2; decide +kernel
      have hl : raw27753step3Labels = raw27753step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node953 node953Labels := by rfl

theorem canonical27754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27754 raw27754Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw27754 raw27754Labels = mixedMoment B raw27754step0 raw27754step0Labels := by
      have hz : ∀ j, raw27754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27754step0 = (fun i j => raw27754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27754step0 raw27754; decide +kernel
      have hl : raw27754step0Labels = raw27754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27754 raw27754Labels permutation434 hz
    mixedMoment B raw27754step0 raw27754step0Labels = mixedMoment B raw27754step1 raw27754step1Labels := by
      have hz : ∀ j, raw27754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27754step1 = (fun i j => raw27754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27754step1 raw27754step0; decide +kernel
      have hl : raw27754step1Labels = raw27754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27754step0 raw27754step0Labels permutation80 hz
    mixedMoment B raw27754step1 raw27754step1Labels = mixedMoment B raw27754step2 raw27754step2Labels := by
      have ha : raw27754step2 = (fun i j => raw27754step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27754step2 raw27754step1; decide +kernel
      have hl : raw27754step2Labels = raw27754step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27754step1 raw27754step1Labels permutation26 permutation0
    mixedMoment B raw27754step2 raw27754step2Labels = mixedMoment B raw27754step3 raw27754step3Labels := by
      have ha : raw27754step3 = -raw27754step2 := by apply Matrix.ext; change ∀ i j, raw27754step3 i j = -(raw27754step2 i j); unfold raw27754step3 raw27754step2; decide +kernel
      have hl : raw27754step3Labels = raw27754step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical27755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27755 raw27755Labels = mixedMoment B node1336 node1336Labels := by
  calc
    mixedMoment B raw27755 raw27755Labels = mixedMoment B raw27755step0 raw27755step0Labels := by
      have hz : ∀ j, raw27755 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27755step0 = (fun i j => raw27755 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27755step0 raw27755; decide +kernel
      have hl : raw27755step0Labels = raw27755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27755 raw27755Labels permutation434 hz
    mixedMoment B raw27755step0 raw27755step0Labels = mixedMoment B raw27755step1 raw27755step1Labels := by
      have ha : raw27755step1 = (fun i j => raw27755step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27755step1 raw27755step0; decide +kernel
      have hl : raw27755step1Labels = raw27755step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27755step0 raw27755step0Labels permutation34 permutation2
    _ = mixedMoment B node1336 node1336Labels := by rfl

theorem canonical27756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27756 raw27756Labels = mixedMoment B node1973 node1973Labels := by
  calc
    mixedMoment B raw27756 raw27756Labels = mixedMoment B raw27756step0 raw27756step0Labels := by
      have ha : raw27756step0 = (fun i j => raw27756 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27756step0 raw27756; decide +kernel
      have hl : raw27756step0Labels = raw27756Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27756 raw27756Labels permutation646 permutation2
    mixedMoment B raw27756step0 raw27756step0Labels = mixedMoment B raw27756step1 raw27756step1Labels := by
      have ha : raw27756step1 = -raw27756step0 := by apply Matrix.ext; change ∀ i j, raw27756step1 i j = -(raw27756step0 i j); unfold raw27756step1 raw27756step0; decide +kernel
      have hl : raw27756step1Labels = raw27756step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1973 node1973Labels := by rfl

theorem canonical27757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27757 raw27757Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw27757 raw27757Labels = mixedMoment B raw27757step0 raw27757step0Labels := by
      have hz : ∀ j, raw27757 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27757step0 = (fun i j => raw27757 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27757step0 raw27757; decide +kernel
      have hl : raw27757step0Labels = raw27757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27757 raw27757Labels permutation434 hz
    mixedMoment B raw27757step0 raw27757step0Labels = mixedMoment B raw27757step1 raw27757step1Labels := by
      have ha : raw27757step1 = (fun i j => raw27757step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27757step1 raw27757step0; decide +kernel
      have hl : raw27757step1Labels = raw27757step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27757step0 raw27757step0Labels permutation145 permutation2
    mixedMoment B raw27757step1 raw27757step1Labels = mixedMoment B raw27757step2 raw27757step2Labels := by
      have ha : raw27757step2 = -raw27757step1 := by apply Matrix.ext; change ∀ i j, raw27757step2 i j = -(raw27757step1 i j); unfold raw27757step2 raw27757step1; decide +kernel
      have hl : raw27757step2Labels = raw27757step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical27758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27758 raw27758Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw27758 raw27758Labels = mixedMoment B raw27758step0 raw27758step0Labels := by
      have hz : ∀ j, raw27758 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27758step0 = (fun i j => raw27758 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27758step0 raw27758; decide +kernel
      have hl : raw27758step0Labels = raw27758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27758 raw27758Labels permutation434 hz
    mixedMoment B raw27758step0 raw27758step0Labels = mixedMoment B raw27758step1 raw27758step1Labels := by
      have ha : raw27758step1 = (fun i j => raw27758step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27758step1 raw27758step0; decide +kernel
      have hl : raw27758step1Labels = raw27758step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27758step0 raw27758step0Labels permutation34 permutation2
    _ = mixedMoment B node2952 node2952Labels := by rfl

theorem canonical27759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27759 raw27759Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw27759 raw27759Labels = mixedMoment B raw27759step0 raw27759step0Labels := by
      have hz : ∀ j, raw27759 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27759step0 = (fun i j => raw27759 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27759step0 raw27759; decide +kernel
      have hl : raw27759step0Labels = raw27759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27759 raw27759Labels permutation434 hz
    mixedMoment B raw27759step0 raw27759step0Labels = mixedMoment B raw27759step1 raw27759step1Labels := by
      have hz : ∀ j, raw27759step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27759step1 = (fun i j => raw27759step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27759step1 raw27759step0; decide +kernel
      have hl : raw27759step1Labels = raw27759step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27759step0 raw27759step0Labels permutation80 hz
    mixedMoment B raw27759step1 raw27759step1Labels = mixedMoment B raw27759step2 raw27759step2Labels := by
      have ha : raw27759step2 = (fun i j => raw27759step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27759step2 raw27759step1; decide +kernel
      have hl : raw27759step2Labels = raw27759step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27759step1 raw27759step1Labels permutation31 permutation7
    mixedMoment B raw27759step2 raw27759step2Labels = mixedMoment B raw27759step3 raw27759step3Labels := by
      have ha : raw27759step3 = -raw27759step2 := by apply Matrix.ext; change ∀ i j, raw27759step3 i j = -(raw27759step2 i j); unfold raw27759step3 raw27759step2; decide +kernel
      have hl : raw27759step3Labels = raw27759step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27759step3 raw27759step3Labels = mixedMoment B raw27759step4 raw27759step4Labels := by
      have ha : raw27759step4 = raw27759step3 := by apply Matrix.ext; unfold raw27759step4 raw27759step3; decide +kernel
      have hl : raw27759step3Labels = labelEmbedding10 ∘ raw27759step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27759step3 raw27759step3Labels raw27759step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical27760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27760 raw27760Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw27760 raw27760Labels = mixedMoment B raw27760step0 raw27760step0Labels := by
      have hz : ∀ j, raw27760 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27760step0 = (fun i j => raw27760 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27760step0 raw27760; decide +kernel
      have hl : raw27760step0Labels = raw27760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27760 raw27760Labels permutation434 hz
    mixedMoment B raw27760step0 raw27760step0Labels = mixedMoment B raw27760step1 raw27760step1Labels := by
      have ha : raw27760step1 = (fun i j => raw27760step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27760step1 raw27760step0; decide +kernel
      have hl : raw27760step1Labels = raw27760step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27760step0 raw27760step0Labels permutation145 permutation2
    _ = mixedMoment B node4827 node4827Labels := by rfl

theorem canonical27761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27761 raw27761Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw27761 raw27761Labels = mixedMoment B raw27761step0 raw27761step0Labels := by
      have hz : ∀ j, raw27761 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27761step0 = (fun i j => raw27761 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27761step0 raw27761; decide +kernel
      have hl : raw27761step0Labels = raw27761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27761 raw27761Labels permutation346 hz
    mixedMoment B raw27761step0 raw27761step0Labels = mixedMoment B raw27761step1 raw27761step1Labels := by
      have ha : raw27761step1 = (fun i j => raw27761step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27761step1 raw27761step0; decide +kernel
      have hl : raw27761step1Labels = raw27761step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27761step0 raw27761step0Labels permutation145 permutation2
    _ = mixedMoment B node4827 node4827Labels := by rfl

theorem canonical27762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27762 raw27762Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw27762 raw27762Labels = mixedMoment B raw27762step0 raw27762step0Labels := by
      have hz : ∀ j, raw27762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27762step0 = (fun i j => raw27762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27762step0 raw27762; decide +kernel
      have hl : raw27762step0Labels = raw27762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27762 raw27762Labels permutation434 hz
    mixedMoment B raw27762step0 raw27762step0Labels = mixedMoment B raw27762step1 raw27762step1Labels := by
      have hz : ∀ j, raw27762step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27762step1 = (fun i j => raw27762step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27762step1 raw27762step0; decide +kernel
      have hl : raw27762step1Labels = raw27762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27762step0 raw27762step0Labels permutation80 hz
    mixedMoment B raw27762step1 raw27762step1Labels = mixedMoment B raw27762step2 raw27762step2Labels := by
      have ha : raw27762step2 = (fun i j => raw27762step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27762step2 raw27762step1; decide +kernel
      have hl : raw27762step2Labels = raw27762step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27762step1 raw27762step1Labels permutation31 permutation2
    _ = mixedMoment B node4490 node4490Labels := by rfl

theorem canonical27763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27763 raw27763Labels = mixedMoment B node4872 node4872Labels := by
  calc
    mixedMoment B raw27763 raw27763Labels = mixedMoment B raw27763step0 raw27763step0Labels := by
      have hz : ∀ j, raw27763 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27763step0 = (fun i j => raw27763 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27763step0 raw27763; decide +kernel
      have hl : raw27763step0Labels = raw27763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27763 raw27763Labels permutation434 hz
    mixedMoment B raw27763step0 raw27763step0Labels = mixedMoment B raw27763step1 raw27763step1Labels := by
      have hz : ∀ j, raw27763step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27763step1 = (fun i j => raw27763step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27763step1 raw27763step0; decide +kernel
      have hl : raw27763step1Labels = raw27763step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27763step0 raw27763step0Labels permutation80 hz
    mixedMoment B raw27763step1 raw27763step1Labels = mixedMoment B raw27763step2 raw27763step2Labels := by
      have ha : raw27763step2 = (fun i j => raw27763step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27763step2 raw27763step1; decide +kernel
      have hl : raw27763step2Labels = raw27763step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27763step1 raw27763step1Labels permutation8 permutation6
    mixedMoment B raw27763step2 raw27763step2Labels = mixedMoment B raw27763step3 raw27763step3Labels := by
      have ha : raw27763step3 = raw27763step2 := by apply Matrix.ext; unfold raw27763step3 raw27763step2; decide +kernel
      have hl : raw27763step2Labels = labelEmbedding9 ∘ raw27763step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27763step2 raw27763step2Labels raw27763step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4872 node4872Labels := by rfl

theorem canonical27764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27764 raw27764Labels = mixedMoment B node4829 node4829Labels := by
  calc
    mixedMoment B raw27764 raw27764Labels = mixedMoment B raw27764step0 raw27764step0Labels := by
      have hz : ∀ j, raw27764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27764step0 = (fun i j => raw27764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27764step0 raw27764; decide +kernel
      have hl : raw27764step0Labels = raw27764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27764 raw27764Labels permutation434 hz
    mixedMoment B raw27764step0 raw27764step0Labels = mixedMoment B raw27764step1 raw27764step1Labels := by
      have ha : raw27764step1 = (fun i j => raw27764step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27764step1 raw27764step0; decide +kernel
      have hl : raw27764step1Labels = raw27764step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27764step0 raw27764step0Labels permutation144 permutation2
    _ = mixedMoment B node4829 node4829Labels := by rfl

theorem canonical27765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27765 raw27765Labels = mixedMoment B node4829 node4829Labels := by
  calc
    mixedMoment B raw27765 raw27765Labels = mixedMoment B raw27765step0 raw27765step0Labels := by
      have hz : ∀ j, raw27765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27765step0 = (fun i j => raw27765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27765step0 raw27765; decide +kernel
      have hl : raw27765step0Labels = raw27765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27765 raw27765Labels permutation346 hz
    mixedMoment B raw27765step0 raw27765step0Labels = mixedMoment B raw27765step1 raw27765step1Labels := by
      have ha : raw27765step1 = (fun i j => raw27765step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27765step1 raw27765step0; decide +kernel
      have hl : raw27765step1Labels = raw27765step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27765step0 raw27765step0Labels permutation144 permutation2
    _ = mixedMoment B node4829 node4829Labels := by rfl

theorem canonical27766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27766 raw27766Labels = mixedMoment B node4492 node4492Labels := by
  calc
    mixedMoment B raw27766 raw27766Labels = mixedMoment B raw27766step0 raw27766step0Labels := by
      have hz : ∀ j, raw27766 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27766step0 = (fun i j => raw27766 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27766step0 raw27766; decide +kernel
      have hl : raw27766step0Labels = raw27766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27766 raw27766Labels permutation434 hz
    mixedMoment B raw27766step0 raw27766step0Labels = mixedMoment B raw27766step1 raw27766step1Labels := by
      have hz : ∀ j, raw27766step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27766step1 = (fun i j => raw27766step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27766step1 raw27766step0; decide +kernel
      have hl : raw27766step1Labels = raw27766step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27766step0 raw27766step0Labels permutation80 hz
    mixedMoment B raw27766step1 raw27766step1Labels = mixedMoment B raw27766step2 raw27766step2Labels := by
      have ha : raw27766step2 = (fun i j => raw27766step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27766step2 raw27766step1; decide +kernel
      have hl : raw27766step2Labels = raw27766step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27766step1 raw27766step1Labels permutation30 permutation2
    _ = mixedMoment B node4492 node4492Labels := by rfl

theorem canonical27767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27767 raw27767Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw27767 raw27767Labels = mixedMoment B raw27767step0 raw27767step0Labels := by
      have hz : ∀ j, raw27767 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27767step0 = (fun i j => raw27767 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27767step0 raw27767; decide +kernel
      have hl : raw27767step0Labels = raw27767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27767 raw27767Labels permutation434 hz
    mixedMoment B raw27767step0 raw27767step0Labels = mixedMoment B raw27767step1 raw27767step1Labels := by
      have ha : raw27767step1 = (fun i j => raw27767step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27767step1 raw27767step0; decide +kernel
      have hl : raw27767step1Labels = raw27767step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27767step0 raw27767step0Labels permutation32 permutation6
    mixedMoment B raw27767step1 raw27767step1Labels = mixedMoment B raw27767step2 raw27767step2Labels := by
      have ha : raw27767step2 = raw27767step1 := by apply Matrix.ext; unfold raw27767step2 raw27767step1; decide +kernel
      have hl : raw27767step1Labels = labelEmbedding9 ∘ raw27767step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27767step1 raw27767step1Labels raw27767step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

theorem canonical27768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27768 raw27768Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw27768 raw27768Labels = mixedMoment B raw27768step0 raw27768step0Labels := by
      have hz : ∀ j, raw27768 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27768step0 = (fun i j => raw27768 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27768step0 raw27768; decide +kernel
      have hl : raw27768step0Labels = raw27768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27768 raw27768Labels permutation434 hz
    mixedMoment B raw27768step0 raw27768step0Labels = mixedMoment B raw27768step1 raw27768step1Labels := by
      have ha : raw27768step1 = (fun i j => raw27768step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27768step1 raw27768step0; decide +kernel
      have hl : raw27768step1Labels = raw27768step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27768step0 raw27768step0Labels permutation151 permutation7
    mixedMoment B raw27768step1 raw27768step1Labels = mixedMoment B raw27768step2 raw27768step2Labels := by
      have ha : raw27768step2 = -raw27768step1 := by apply Matrix.ext; change ∀ i j, raw27768step2 i j = -(raw27768step1 i j); unfold raw27768step2 raw27768step1; decide +kernel
      have hl : raw27768step2Labels = raw27768step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27768step2 raw27768step2Labels = mixedMoment B raw27768step3 raw27768step3Labels := by
      have ha : raw27768step3 = raw27768step2 := by apply Matrix.ext; unfold raw27768step3 raw27768step2; decide +kernel
      have hl : raw27768step2Labels = labelEmbedding10 ∘ raw27768step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27768step2 raw27768step2Labels raw27768step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4853 node4853Labels := by rfl

theorem canonical27769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27769 raw27769Labels = mixedMoment B node4824 node4824Labels := by
  calc
    mixedMoment B raw27769 raw27769Labels = mixedMoment B raw27769step0 raw27769step0Labels := by
      have ha : raw27769step0 = (fun i j => raw27769 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27769step0 raw27769; decide +kernel
      have hl : raw27769step0Labels = raw27769Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27769 raw27769Labels permutation664 permutation2
    _ = mixedMoment B node4824 node4824Labels := by rfl

theorem canonical27770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27770 raw27770Labels = mixedMoment B node4486 node4486Labels := by
  calc
    mixedMoment B raw27770 raw27770Labels = mixedMoment B raw27770step0 raw27770step0Labels := by
      have hz : ∀ j, raw27770 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27770step0 = (fun i j => raw27770 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27770step0 raw27770; decide +kernel
      have hl : raw27770step0Labels = raw27770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27770 raw27770Labels permutation434 hz
    mixedMoment B raw27770step0 raw27770step0Labels = mixedMoment B raw27770step1 raw27770step1Labels := by
      have ha : raw27770step1 = (fun i j => raw27770step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27770step1 raw27770step0; decide +kernel
      have hl : raw27770step1Labels = raw27770step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27770step0 raw27770step0Labels permutation151 permutation2
    _ = mixedMoment B node4486 node4486Labels := by rfl

theorem canonical27771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27771 raw27771Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw27771 raw27771Labels = mixedMoment B raw27771step0 raw27771step0Labels := by
      have hz : ∀ j, raw27771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27771step0 = (fun i j => raw27771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27771step0 raw27771; decide +kernel
      have hl : raw27771step0Labels = raw27771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27771 raw27771Labels permutation346 hz
    mixedMoment B raw27771step0 raw27771step0Labels = mixedMoment B raw27771step1 raw27771step1Labels := by
      have ha : raw27771step1 = (fun i j => raw27771step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27771step1 raw27771step0; decide +kernel
      have hl : raw27771step1Labels = raw27771step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27771step0 raw27771step0Labels permutation32 permutation6
    mixedMoment B raw27771step1 raw27771step1Labels = mixedMoment B raw27771step2 raw27771step2Labels := by
      have ha : raw27771step2 = raw27771step1 := by apply Matrix.ext; unfold raw27771step2 raw27771step1; decide +kernel
      have hl : raw27771step1Labels = labelEmbedding9 ∘ raw27771step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27771step1 raw27771step1Labels raw27771step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

theorem canonical27772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27772 raw27772Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw27772 raw27772Labels = mixedMoment B raw27772step0 raw27772step0Labels := by
      have hz : ∀ j, raw27772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27772step0 = (fun i j => raw27772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27772step0 raw27772; decide +kernel
      have hl : raw27772step0Labels = raw27772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27772 raw27772Labels permutation346 hz
    mixedMoment B raw27772step0 raw27772step0Labels = mixedMoment B raw27772step1 raw27772step1Labels := by
      have ha : raw27772step1 = (fun i j => raw27772step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27772step1 raw27772step0; decide +kernel
      have hl : raw27772step1Labels = raw27772step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27772step0 raw27772step0Labels permutation151 permutation7
    mixedMoment B raw27772step1 raw27772step1Labels = mixedMoment B raw27772step2 raw27772step2Labels := by
      have ha : raw27772step2 = -raw27772step1 := by apply Matrix.ext; change ∀ i j, raw27772step2 i j = -(raw27772step1 i j); unfold raw27772step2 raw27772step1; decide +kernel
      have hl : raw27772step2Labels = raw27772step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27772step2 raw27772step2Labels = mixedMoment B raw27772step3 raw27772step3Labels := by
      have ha : raw27772step3 = raw27772step2 := by apply Matrix.ext; unfold raw27772step3 raw27772step2; decide +kernel
      have hl : raw27772step2Labels = labelEmbedding10 ∘ raw27772step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27772step2 raw27772step2Labels raw27772step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4853 node4853Labels := by rfl

theorem canonical27773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27773 raw27773Labels = mixedMoment B node4824 node4824Labels := by
  calc
    mixedMoment B raw27773 raw27773Labels = mixedMoment B raw27773step0 raw27773step0Labels := by
      have ha : raw27773step0 = (fun i j => raw27773 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27773step0 raw27773; decide +kernel
      have hl : raw27773step0Labels = raw27773Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27773 raw27773Labels permutation646 permutation2
    _ = mixedMoment B node4824 node4824Labels := by rfl

theorem canonical27774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27774 raw27774Labels = mixedMoment B node4486 node4486Labels := by
  calc
    mixedMoment B raw27774 raw27774Labels = mixedMoment B raw27774step0 raw27774step0Labels := by
      have hz : ∀ j, raw27774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27774step0 = (fun i j => raw27774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27774step0 raw27774; decide +kernel
      have hl : raw27774step0Labels = raw27774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27774 raw27774Labels permutation346 hz
    mixedMoment B raw27774step0 raw27774step0Labels = mixedMoment B raw27774step1 raw27774step1Labels := by
      have ha : raw27774step1 = (fun i j => raw27774step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27774step1 raw27774step0; decide +kernel
      have hl : raw27774step1Labels = raw27774step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27774step0 raw27774step0Labels permutation151 permutation2
    _ = mixedMoment B node4486 node4486Labels := by rfl

theorem canonical27775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27775 raw27775Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw27775 raw27775Labels = mixedMoment B raw27775step0 raw27775step0Labels := by
      have hz : ∀ j, raw27775 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27775step0 = (fun i j => raw27775 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27775step0 raw27775; decide +kernel
      have hl : raw27775step0Labels = raw27775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27775 raw27775Labels permutation434 hz
    mixedMoment B raw27775step0 raw27775step0Labels = mixedMoment B raw27775step1 raw27775step1Labels := by
      have hz : ∀ j, raw27775step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27775step1 = (fun i j => raw27775step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27775step1 raw27775step0; decide +kernel
      have hl : raw27775step1Labels = raw27775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27775step0 raw27775step0Labels permutation80 hz
    mixedMoment B raw27775step1 raw27775step1Labels = mixedMoment B raw27775step2 raw27775step2Labels := by
      have ha : raw27775step2 = (fun i j => raw27775step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27775step2 raw27775step1; decide +kernel
      have hl : raw27775step2Labels = raw27775step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27775step1 raw27775step1Labels permutation8 permutation6
    mixedMoment B raw27775step2 raw27775step2Labels = mixedMoment B raw27775step3 raw27775step3Labels := by
      have ha : raw27775step3 = raw27775step2 := by apply Matrix.ext; unfold raw27775step3 raw27775step2; decide +kernel
      have hl : raw27775step2Labels = labelEmbedding9 ∘ raw27775step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27775step2 raw27775step2Labels raw27775step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4844 node4844Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical217
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27776 raw27776Labels = mixedMoment B node4881 node4881Labels := by
  calc
    mixedMoment B raw27776 raw27776Labels = mixedMoment B raw27776step0 raw27776step0Labels := by
      have hz : ∀ j, raw27776 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27776step0 = (fun i j => raw27776 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27776step0 raw27776; decide +kernel
      have hl : raw27776step0Labels = raw27776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27776 raw27776Labels permutation434 hz
    mixedMoment B raw27776step0 raw27776step0Labels = mixedMoment B raw27776step1 raw27776step1Labels := by
      have hz : ∀ j, raw27776step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27776step1 = (fun i j => raw27776step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27776step1 raw27776step0; decide +kernel
      have hl : raw27776step1Labels = raw27776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27776step0 raw27776step0Labels permutation80 hz
    mixedMoment B raw27776step1 raw27776step1Labels = mixedMoment B raw27776step2 raw27776step2Labels := by
      have ha : raw27776step2 = (fun i j => raw27776step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27776step2 raw27776step1; decide +kernel
      have hl : raw27776step2Labels = raw27776step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27776step1 raw27776step1Labels permutation31 permutation7
    mixedMoment B raw27776step2 raw27776step2Labels = mixedMoment B raw27776step3 raw27776step3Labels := by
      have ha : raw27776step3 = -raw27776step2 := by apply Matrix.ext; change ∀ i j, raw27776step3 i j = -(raw27776step2 i j); unfold raw27776step3 raw27776step2; decide +kernel
      have hl : raw27776step3Labels = raw27776step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27776step3 raw27776step3Labels = mixedMoment B raw27776step4 raw27776step4Labels := by
      have ha : raw27776step4 = raw27776step3 := by apply Matrix.ext; unfold raw27776step4 raw27776step3; decide +kernel
      have hl : raw27776step3Labels = labelEmbedding10 ∘ raw27776step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27776step3 raw27776step3Labels raw27776step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4881 node4881Labels := by rfl

theorem canonical27777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27777 raw27777Labels = mixedMoment B node4840 node4840Labels := by
  calc
    mixedMoment B raw27777 raw27777Labels = mixedMoment B raw27777step0 raw27777step0Labels := by
      have hz : ∀ j, raw27777 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27777step0 = (fun i j => raw27777 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27777step0 raw27777; decide +kernel
      have hl : raw27777step0Labels = raw27777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27777 raw27777Labels permutation434 hz
    mixedMoment B raw27777step0 raw27777step0Labels = mixedMoment B raw27777step1 raw27777step1Labels := by
      have ha : raw27777step1 = (fun i j => raw27777step0 (permutation142 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27777step1 raw27777step0; decide +kernel
      have hl : raw27777step1Labels = raw27777step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27777step0 raw27777step0Labels permutation142 permutation2
    _ = mixedMoment B node4840 node4840Labels := by rfl

theorem canonical27778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27778 raw27778Labels = mixedMoment B node4840 node4840Labels := by
  calc
    mixedMoment B raw27778 raw27778Labels = mixedMoment B raw27778step0 raw27778step0Labels := by
      have hz : ∀ j, raw27778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27778step0 = (fun i j => raw27778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27778step0 raw27778; decide +kernel
      have hl : raw27778step0Labels = raw27778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27778 raw27778Labels permutation346 hz
    mixedMoment B raw27778step0 raw27778step0Labels = mixedMoment B raw27778step1 raw27778step1Labels := by
      have ha : raw27778step1 = (fun i j => raw27778step0 (permutation142 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27778step1 raw27778step0; decide +kernel
      have hl : raw27778step1Labels = raw27778step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27778step0 raw27778step0Labels permutation142 permutation2
    _ = mixedMoment B node4840 node4840Labels := by rfl

theorem canonical27779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27779 raw27779Labels = mixedMoment B node4504 node4504Labels := by
  calc
    mixedMoment B raw27779 raw27779Labels = mixedMoment B raw27779step0 raw27779step0Labels := by
      have hz : ∀ j, raw27779 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27779step0 = (fun i j => raw27779 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27779step0 raw27779; decide +kernel
      have hl : raw27779step0Labels = raw27779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27779 raw27779Labels permutation434 hz
    mixedMoment B raw27779step0 raw27779step0Labels = mixedMoment B raw27779step1 raw27779step1Labels := by
      have hz : ∀ j, raw27779step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27779step1 = (fun i j => raw27779step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27779step1 raw27779step0; decide +kernel
      have hl : raw27779step1Labels = raw27779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27779step0 raw27779step0Labels permutation80 hz
    mixedMoment B raw27779step1 raw27779step1Labels = mixedMoment B raw27779step2 raw27779step2Labels := by
      have ha : raw27779step2 = (fun i j => raw27779step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27779step2 raw27779step1; decide +kernel
      have hl : raw27779step2Labels = raw27779step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27779step1 raw27779step1Labels permutation28 permutation2
    _ = mixedMoment B node4504 node4504Labels := by rfl

theorem canonical27780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27780 raw27780Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw27780 raw27780Labels = mixedMoment B raw27780step0 raw27780step0Labels := by
      have hz : ∀ j, raw27780 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27780step0 = (fun i j => raw27780 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27780step0 raw27780; decide +kernel
      have hl : raw27780step0Labels = raw27780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27780 raw27780Labels permutation434 hz
    mixedMoment B raw27780step0 raw27780step0Labels = mixedMoment B raw27780step1 raw27780step1Labels := by
      have hz : ∀ j, raw27780step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27780step1 = (fun i j => raw27780step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27780step1 raw27780step0; decide +kernel
      have hl : raw27780step1Labels = raw27780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27780step0 raw27780step0Labels permutation80 hz
    mixedMoment B raw27780step1 raw27780step1Labels = mixedMoment B raw27780step2 raw27780step2Labels := by
      have ha : raw27780step2 = (fun i j => raw27780step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27780step2 raw27780step1; decide +kernel
      have hl : raw27780step2Labels = raw27780step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27780step1 raw27780step1Labels permutation8 permutation6
    mixedMoment B raw27780step2 raw27780step2Labels = mixedMoment B raw27780step3 raw27780step3Labels := by
      have ha : raw27780step3 = raw27780step2 := by apply Matrix.ext; unfold raw27780step3 raw27780step2; decide +kernel
      have hl : raw27780step2Labels = labelEmbedding9 ∘ raw27780step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27780step2 raw27780step2Labels raw27780step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5174 node5174Labels := by rfl

theorem canonical27811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27811 raw27811Labels = mixedMoment B node1159 node1159Labels := by
  calc
    mixedMoment B raw27811 raw27811Labels = mixedMoment B raw27811step0 raw27811step0Labels := by
      have hz : ∀ j, raw27811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27811step0 = (fun i j => raw27811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27811step0 raw27811; decide +kernel
      have hl : raw27811step0Labels = raw27811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27811 raw27811Labels permutation346 hz
    mixedMoment B raw27811step0 raw27811step0Labels = mixedMoment B raw27811step1 raw27811step1Labels := by
      have ha : raw27811step1 = (fun i j => raw27811step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27811step1 raw27811step0; decide +kernel
      have hl : raw27811step1Labels = raw27811step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27811step0 raw27811step0Labels permutation34 permutation2
    _ = mixedMoment B node1159 node1159Labels := by rfl

theorem canonical27812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27812 raw27812Labels = mixedMoment B node2355 node2355Labels := by
  calc
    mixedMoment B raw27812 raw27812Labels = mixedMoment B raw27812step0 raw27812step0Labels := by
      have hz : ∀ j, raw27812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27812step0 = (fun i j => raw27812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27812step0 raw27812; decide +kernel
      have hl : raw27812step0Labels = raw27812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27812 raw27812Labels permutation346 hz
    mixedMoment B raw27812step0 raw27812step0Labels = mixedMoment B raw27812step1 raw27812step1Labels := by
      have ha : raw27812step1 = (fun i j => raw27812step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27812step1 raw27812step0; decide +kernel
      have hl : raw27812step1Labels = raw27812step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27812step0 raw27812step0Labels permutation34 permutation2
    _ = mixedMoment B node2355 node2355Labels := by rfl

theorem canonical27813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27813 raw27813Labels = mixedMoment B node2436 node2436Labels := by
  calc
    mixedMoment B raw27813 raw27813Labels = mixedMoment B raw27813step0 raw27813step0Labels := by
      have ha : raw27813step0 = (fun i j => raw27813 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27813step0 raw27813; decide +kernel
      have hl : raw27813step0Labels = raw27813Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27813 raw27813Labels permutation662 permutation2
    mixedMoment B raw27813step0 raw27813step0Labels = mixedMoment B raw27813step1 raw27813step1Labels := by
      have ha : raw27813step1 = -raw27813step0 := by apply Matrix.ext; change ∀ i j, raw27813step1 i j = -(raw27813step0 i j); unfold raw27813step1 raw27813step0; decide +kernel
      have hl : raw27813step1Labels = raw27813step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2436 node2436Labels := by rfl

theorem canonical27814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27814 raw27814Labels = mixedMoment B node2569 node2569Labels := by
  calc
    mixedMoment B raw27814 raw27814Labels = mixedMoment B raw27814step0 raw27814step0Labels := by
      have hz : ∀ j, raw27814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27814step0 = (fun i j => raw27814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27814step0 raw27814; decide +kernel
      have hl : raw27814step0Labels = raw27814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27814 raw27814Labels permutation346 hz
    _ = mixedMoment B node2569 node2569Labels := by rfl

theorem canonical27815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27815 raw27815Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw27815 raw27815Labels = mixedMoment B raw27815step0 raw27815step0Labels := by
      have hz : ∀ j, raw27815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27815step0 = (fun i j => raw27815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27815step0 raw27815; decide +kernel
      have hl : raw27815step0Labels = raw27815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27815 raw27815Labels permutation346 hz
    mixedMoment B raw27815step0 raw27815step0Labels = mixedMoment B raw27815step1 raw27815step1Labels := by
      have ha : raw27815step1 = (fun i j => raw27815step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27815step1 raw27815step0; decide +kernel
      have hl : raw27815step1Labels = raw27815step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27815step0 raw27815step0Labels permutation145 permutation2
    mixedMoment B raw27815step1 raw27815step1Labels = mixedMoment B raw27815step2 raw27815step2Labels := by
      have ha : raw27815step2 = -raw27815step1 := by apply Matrix.ext; change ∀ i j, raw27815step2 i j = -(raw27815step1 i j); unfold raw27815step2 raw27815step1; decide +kernel
      have hl : raw27815step2Labels = raw27815step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2482 node2482Labels := by rfl

theorem canonical27816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27816 raw27816Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw27816 raw27816Labels = mixedMoment B raw27816step0 raw27816step0Labels := by
      have hz : ∀ j, raw27816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27816step0 = (fun i j => raw27816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27816step0 raw27816; decide +kernel
      have hl : raw27816step0Labels = raw27816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27816 raw27816Labels permutation346 hz
    mixedMoment B raw27816step0 raw27816step0Labels = mixedMoment B raw27816step1 raw27816step1Labels := by
      have ha : raw27816step1 = (fun i j => raw27816step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27816step1 raw27816step0; decide +kernel
      have hl : raw27816step1Labels = raw27816step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27816step0 raw27816step0Labels permutation34 permutation2
    _ = mixedMoment B node2590 node2590Labels := by rfl

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

theorem canonical1269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1269 raw1269Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw1269 raw1269Labels = mixedMoment B raw1269step0 raw1269step0Labels := by
      have ha : raw1269step0 = (fun i j => raw1269 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1269step0 raw1269; decide +kernel
      have hl : raw1269step0Labels = raw1269Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1269 raw1269Labels permutation8 permutation4
    mixedMoment B raw1269step0 raw1269step0Labels = mixedMoment B raw1269step1 raw1269step1Labels := by
      have ha : raw1269step1 = raw1269step0 := by apply Matrix.ext; unfold raw1269step1 raw1269step0; decide +kernel
      have hl : raw1269step0Labels = labelEmbedding7 ∘ raw1269step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1269step0 raw1269step0Labels raw1269step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

theorem canonical1270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1270 raw1270Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw1270 raw1270Labels = mixedMoment B raw1270step0 raw1270step0Labels := by
      have ha : raw1270step0 = (fun i j => raw1270 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1270step0 raw1270; decide +kernel
      have hl : raw1270step0Labels = raw1270Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1270 raw1270Labels permutation8 permutation4
    _ = mixedMoment B node1046 node1046Labels := by rfl

theorem canonical1271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1271 raw1271Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw1271 raw1271Labels = mixedMoment B raw1271step0 raw1271step0Labels := by
      have ha : raw1271step0 = (fun i j => raw1271 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1271step0 raw1271; decide +kernel
      have hl : raw1271step0Labels = raw1271Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1271 raw1271Labels permutation8 permutation6
    mixedMoment B raw1271step0 raw1271step0Labels = mixedMoment B raw1271step1 raw1271step1Labels := by
      have ha : raw1271step1 = -raw1271step0 := by apply Matrix.ext; change ∀ i j, raw1271step1 i j = -(raw1271step0 i j); unfold raw1271step1 raw1271step0; decide +kernel
      have hl : raw1271step1Labels = raw1271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1271step1 raw1271step1Labels = mixedMoment B raw1271step2 raw1271step2Labels := by
      have ha : raw1271step2 = raw1271step1 := by apply Matrix.ext; unfold raw1271step2 raw1271step1; decide +kernel
      have hl : raw1271step1Labels = labelEmbedding1 ∘ raw1271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1271step1 raw1271step1Labels raw1271step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4463 node4463Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1046 node1046Labels + mixedMoment B node1750 node1750Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1269 singletonSmall4463
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4463) = raw1269Labels := by decide +kernel
  rw [hl, canonical1269 B hB] at h
  have hc0 : mixedMoment B raw1269 (Fin.cases (0 : Fin 2) singletonSmall4463) =
      mixedMoment B node1046 node1046Labels := by
    have ha : raw1269 = raw1270 := by apply Matrix.ext; unfold raw1269 raw1270; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4463 = raw1270Labels := by decide +kernel
    rw [ha, hj, canonical1270 B hB]
  have hc1 : mixedMoment B raw1269 (Fin.cases (1 : Fin 2) singletonSmall4463) =
      mixedMoment B node1750 node1750Labels := by
    have ha : raw1269 = raw1271 := by apply Matrix.ext; unfold raw1269 raw1271; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4463 = raw1271Labels := by decide +kernel
    rw [ha, hj, canonical1271 B hB]
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

theorem singleton4490 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4490 node4490Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1074 node1074Labels + mixedMoment B node1650 node1650Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1284 singletonSmall4490
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4490) = raw1284Labels := by decide +kernel
  rw [hl, canonical1284 B hB] at h
  have hc0 : mixedMoment B raw1284 (Fin.cases (0 : Fin 2) singletonSmall4490) =
      mixedMoment B node1074 node1074Labels := by
    have ha : raw1284 = raw1285 := by apply Matrix.ext; unfold raw1284 raw1285; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4490 = raw1285Labels := by decide +kernel
    rw [ha, hj, canonical1285 B hB]
  have hc1 : mixedMoment B raw1284 (Fin.cases (1 : Fin 2) singletonSmall4490) =
      mixedMoment B node1650 node1650Labels := by
    have ha : raw1284 = raw1286 := by apply Matrix.ext; unfold raw1284 raw1286; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4490 = raw1286Labels := by decide +kernel
    rw [ha, hj, canonical1286 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4807 node4807Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2025 node2025Labels + mixedMoment B node2224 node2224Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1743 singletonSmall4807
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4807) = raw1743Labels := by decide +kernel
  rw [hl, canonical1743 B hB] at h
  have hc0 : mixedMoment B raw1743 (Fin.cases (0 : Fin 2) singletonSmall4807) =
      mixedMoment B node2025 node2025Labels := by
    have ha : raw1743 = raw1744 := by apply Matrix.ext; unfold raw1743 raw1744; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4807 = raw1744Labels := by decide +kernel
    rw [ha, hj, canonical1744 B hB]
  have hc1 : mixedMoment B raw1743 (Fin.cases (1 : Fin 2) singletonSmall4807) =
      mixedMoment B node2224 node2224Labels := by
    have ha : raw1743 = raw1745 := by apply Matrix.ext; unfold raw1743 raw1745; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4807 = raw1745Labels := by decide +kernel
    rw [ha, hj, canonical1745 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4827 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4827 node4827Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2047 node2047Labels + mixedMoment B node2079 node2079Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1755 singletonSmall4827
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4827) = raw1755Labels := by decide +kernel
  rw [hl, canonical1755 B hB] at h
  have hc0 : mixedMoment B raw1755 (Fin.cases (0 : Fin 2) singletonSmall4827) =
      mixedMoment B node2047 node2047Labels := by
    have ha : raw1755 = raw1756 := by apply Matrix.ext; unfold raw1755 raw1756; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4827 = raw1756Labels := by decide +kernel
    rw [ha, hj, canonical1756 B hB]
  have hc1 : mixedMoment B raw1755 (Fin.cases (1 : Fin 2) singletonSmall4827) =
      mixedMoment B node2079 node2079Labels := by
    have ha : raw1755 = raw1757 := by apply Matrix.ext; unfold raw1755 raw1757; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4827 = raw1757Labels := by decide +kernel
    rw [ha, hj, canonical1757 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4843 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4843 node4843Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2062 node2062Labels + mixedMoment B node2230 node2230Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1773 singletonSmall4843
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4843) = raw1773Labels := by decide +kernel
  rw [hl, canonical1773 B hB] at h
  have hc0 : mixedMoment B raw1773 (Fin.cases (0 : Fin 2) singletonSmall4843) =
      mixedMoment B node2062 node2062Labels := by
    have ha : raw1773 = raw1774 := by apply Matrix.ext; unfold raw1773 raw1774; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4843 = raw1774Labels := by decide +kernel
    rw [ha, hj, canonical1774 B hB]
  have hc1 : mixedMoment B raw1773 (Fin.cases (1 : Fin 2) singletonSmall4843) =
      mixedMoment B node2230 node2230Labels := by
    have ha : raw1773 = raw1775 := by apply Matrix.ext; unfold raw1773 raw1775; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4843 = raw1775Labels := by decide +kernel
    rw [ha, hj, canonical1775 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4866 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4866 node4866Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2107 node2107Labels + mixedMoment B node2260 node2260Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1794 singletonSmall4866
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4866) = raw1794Labels := by decide +kernel
  rw [hl, canonical1794 B hB] at h
  have hc0 : mixedMoment B raw1794 (Fin.cases (0 : Fin 2) singletonSmall4866) =
      mixedMoment B node2107 node2107Labels := by
    have ha : raw1794 = raw1795 := by apply Matrix.ext; unfold raw1794 raw1795; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4866 = raw1795Labels := by decide +kernel
    rw [ha, hj, canonical1795 B hB]
  have hc1 : mixedMoment B raw1794 (Fin.cases (1 : Fin 2) singletonSmall4866) =
      mixedMoment B node2260 node2260Labels := by
    have ha : raw1794 = raw1796 := by apply Matrix.ext; unfold raw1794 raw1796; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4866 = raw1796Labels := by decide +kernel
    rw [ha, hj, canonical1796 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4868 node4868Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2109 node2109Labels + mixedMoment B node2261 node2261Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1797 singletonSmall4868
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4868) = raw1797Labels := by decide +kernel
  rw [hl, canonical1797 B hB] at h
  have hc0 : mixedMoment B raw1797 (Fin.cases (0 : Fin 2) singletonSmall4868) =
      mixedMoment B node2109 node2109Labels := by
    have ha : raw1797 = raw1798 := by apply Matrix.ext; unfold raw1797 raw1798; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4868 = raw1798Labels := by decide +kernel
    rw [ha, hj, canonical1798 B hB]
  have hc1 : mixedMoment B raw1797 (Fin.cases (1 : Fin 2) singletonSmall4868) =
      mixedMoment B node2261 node2261Labels := by
    have ha : raw1797 = raw1799 := by apply Matrix.ext; unfold raw1797 raw1799; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4868 = raw1799Labels := by decide +kernel
    rw [ha, hj, canonical1799 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4875 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4875 node4875Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2116 node2116Labels + mixedMoment B node2288 node2288Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1809 singletonSmall4875
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4875) = raw1809Labels := by decide +kernel
  rw [hl, canonical1809 B hB] at h
  have hc0 : mixedMoment B raw1809 (Fin.cases (0 : Fin 2) singletonSmall4875) =
      mixedMoment B node2116 node2116Labels := by
    have ha : raw1809 = raw1810 := by apply Matrix.ext; unfold raw1809 raw1810; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4875 = raw1810Labels := by decide +kernel
    rw [ha, hj, canonical1810 B hB]
  have hc1 : mixedMoment B raw1809 (Fin.cases (1 : Fin 2) singletonSmall4875) =
      mixedMoment B node2288 node2288Labels := by
    have ha : raw1809 = raw1811 := by apply Matrix.ext; unfold raw1809 raw1811; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4875 = raw1811Labels := by decide +kernel
    rw [ha, hj, canonical1811 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4890 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4890 node4890Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2247 node2247Labels + mixedMoment B node2290 node2290Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1821 singletonSmall4890
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4890) = raw1821Labels := by decide +kernel
  rw [hl, canonical1821 B hB] at h
  have hc0 : mixedMoment B raw1821 (Fin.cases (0 : Fin 2) singletonSmall4890) =
      mixedMoment B node2247 node2247Labels := by
    have ha : raw1821 = raw1822 := by apply Matrix.ext; unfold raw1821 raw1822; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4890 = raw1822Labels := by decide +kernel
    rw [ha, hj, canonical1822 B hB]
  have hc1 : mixedMoment B raw1821 (Fin.cases (1 : Fin 2) singletonSmall4890) =
      mixedMoment B node2290 node2290Labels := by
    have ha : raw1821 = raw1823 := by apply Matrix.ext; unfold raw1821 raw1823; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4890 = raw1823Labels := by decide +kernel
    rw [ha, hj, canonical1823 B hB]
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

theorem singleton5109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5109 node5109Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2519 node2519Labels + mixedMoment B node3486 node3486Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2133 singletonSmall5109
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5109) = raw2133Labels := by decide +kernel
  rw [hl, canonical2133 B hB] at h
  have hc0 : mixedMoment B raw2133 (Fin.cases (0 : Fin 2) singletonSmall5109) =
      mixedMoment B node2519 node2519Labels := by
    have ha : raw2133 = raw2134 := by apply Matrix.ext; unfold raw2133 raw2134; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5109 = raw2134Labels := by decide +kernel
    rw [ha, hj, canonical2134 B hB]
  have hc1 : mixedMoment B raw2133 (Fin.cases (1 : Fin 2) singletonSmall5109) =
      mixedMoment B node3486 node3486Labels := by
    have ha : raw2133 = raw2135 := by apply Matrix.ext; unfold raw2133 raw2135; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5109 = raw2135Labels := by decide +kernel
    rw [ha, hj, canonical2135 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node953 node953Labels = Sparse.eval nodeValue953 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 953) = mixedMoment B node953 node953Labels := rfl
  simpa [nodeValue953, Sparse.eval] using hc.symm

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

theorem sound1046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1046 node1046Labels = Sparse.eval nodeValue1046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1046) = mixedMoment B node1046 node1046Labels := rfl
  simpa [nodeValue1046, Sparse.eval] using hc.symm

theorem sound1074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1074 node1074Labels = Sparse.eval nodeValue1074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1074) = mixedMoment B node1074 node1074Labels := rfl
  simpa [nodeValue1074, Sparse.eval] using hc.symm

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

theorem sound1159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1159 node1159Labels = Sparse.eval nodeValue1159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1159) = mixedMoment B node1159 node1159Labels := rfl
  simpa [nodeValue1159, Sparse.eval] using hc.symm

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

theorem sound1336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1336 node1336Labels = Sparse.eval nodeValue1336 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1336) = mixedMoment B node1336 node1336Labels := rfl
  simpa [nodeValue1336, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1650 node1650Labels = Sparse.eval nodeValue1650 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1650) = mixedMoment B node1650 node1650Labels := rfl
  simpa [nodeValue1650, Sparse.eval] using hc.symm

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

theorem sound1686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1686 node1686Labels = Sparse.eval nodeValue1686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1686) = mixedMoment B node1686 node1686Labels := rfl
  simpa [nodeValue1686, Sparse.eval] using hc.symm

theorem sound1687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1687 node1687Labels = Sparse.eval nodeValue1687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1687) = mixedMoment B node1687 node1687Labels := rfl
  simpa [nodeValue1687, Sparse.eval] using hc.symm

theorem sound1695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1695 node1695Labels = Sparse.eval nodeValue1695 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1695) = mixedMoment B node1695 node1695Labels := rfl
  simpa [nodeValue1695, Sparse.eval] using hc.symm

theorem sound1720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1720 node1720Labels = Sparse.eval nodeValue1720 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1720) = mixedMoment B node1720 node1720Labels := rfl
  simpa [nodeValue1720, Sparse.eval] using hc.symm

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

theorem sound1745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1745 node1745Labels = Sparse.eval nodeValue1745 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1745) = mixedMoment B node1745 node1745Labels := rfl
  simpa [nodeValue1745, Sparse.eval] using hc.symm

theorem sound1748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1748 node1748Labels = Sparse.eval nodeValue1748 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1748) = mixedMoment B node1748 node1748Labels := rfl
  simpa [nodeValue1748, Sparse.eval] using hc.symm

theorem sound1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1750 node1750Labels = Sparse.eval nodeValue1750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1750) = mixedMoment B node1750 node1750Labels := rfl
  simpa [nodeValue1750, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1831 node1831Labels = Sparse.eval nodeValue1831 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1831) = mixedMoment B node1831 node1831Labels := rfl
  simpa [nodeValue1831, Sparse.eval] using hc.symm

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

theorem sound1973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1973 node1973Labels = Sparse.eval nodeValue1973 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1973) = mixedMoment B node1973 node1973Labels := rfl
  simpa [nodeValue1973, Sparse.eval] using hc.symm

theorem sound1979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1979 node1979Labels = Sparse.eval nodeValue1979 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1979) = mixedMoment B node1979 node1979Labels := rfl
  simpa [nodeValue1979, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2025 node2025Labels = Sparse.eval nodeValue2025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2025) = mixedMoment B node2025 node2025Labels := rfl
  simpa [nodeValue2025, Sparse.eval] using hc.symm

theorem sound2047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2047 node2047Labels = Sparse.eval nodeValue2047 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2047) = mixedMoment B node2047 node2047Labels := rfl
  simpa [nodeValue2047, Sparse.eval] using hc.symm

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

theorem sound2062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2062 node2062Labels = Sparse.eval nodeValue2062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2062) = mixedMoment B node2062 node2062Labels := rfl
  simpa [nodeValue2062, Sparse.eval] using hc.symm

theorem sound2079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2079 node2079Labels = Sparse.eval nodeValue2079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2079) = mixedMoment B node2079 node2079Labels := rfl
  simpa [nodeValue2079, Sparse.eval] using hc.symm

theorem sound2107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2107 node2107Labels = Sparse.eval nodeValue2107 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2107) = mixedMoment B node2107 node2107Labels := rfl
  simpa [nodeValue2107, Sparse.eval] using hc.symm

theorem sound2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2109 node2109Labels = Sparse.eval nodeValue2109 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2109) = mixedMoment B node2109 node2109Labels := rfl
  simpa [nodeValue2109, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2112 node2112Labels = Sparse.eval nodeValue2112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2112) = mixedMoment B node2112 node2112Labels := rfl
  simpa [nodeValue2112, Sparse.eval] using hc.symm

theorem sound2116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2116 node2116Labels = Sparse.eval nodeValue2116 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2116) = mixedMoment B node2116 node2116Labels := rfl
  simpa [nodeValue2116, Sparse.eval] using hc.symm

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

theorem sound2198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2198 node2198Labels = Sparse.eval nodeValue2198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2198) = mixedMoment B node2198 node2198Labels := rfl
  simpa [nodeValue2198, Sparse.eval] using hc.symm

theorem sound2223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2223 node2223Labels = Sparse.eval nodeValue2223 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2223) = mixedMoment B node2223 node2223Labels := rfl
  simpa [nodeValue2223, Sparse.eval] using hc.symm

theorem sound2224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2224 node2224Labels = Sparse.eval nodeValue2224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2224) = mixedMoment B node2224 node2224Labels := rfl
  simpa [nodeValue2224, Sparse.eval] using hc.symm

theorem sound2230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2230 node2230Labels = Sparse.eval nodeValue2230 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2230) = mixedMoment B node2230 node2230Labels := rfl
  simpa [nodeValue2230, Sparse.eval] using hc.symm

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

theorem zero2291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = 0 := by
  exact mixedMoment_order_one B hB node2291 node2291Labels 1
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

theorem sound2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2247 node2247Labels = Sparse.eval nodeValue2247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2247) = mixedMoment B node2247 node2247Labels := rfl
  simpa [nodeValue2247, Sparse.eval] using hc.symm

theorem sound2256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2256 node2256Labels = Sparse.eval nodeValue2256 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2256) = mixedMoment B node2256 node2256Labels := rfl
  simpa [nodeValue2256, Sparse.eval] using hc.symm

theorem sound2259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2259 node2259Labels = Sparse.eval nodeValue2259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2259) = mixedMoment B node2259 node2259Labels := rfl
  simpa [nodeValue2259, Sparse.eval] using hc.symm

theorem sound2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2260 node2260Labels = Sparse.eval nodeValue2260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2260) = mixedMoment B node2260 node2260Labels := rfl
  simpa [nodeValue2260, Sparse.eval] using hc.symm

theorem sound2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2261 node2261Labels = Sparse.eval nodeValue2261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2261) = mixedMoment B node2261 node2261Labels := rfl
  simpa [nodeValue2261, Sparse.eval] using hc.symm

theorem sound2286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2286 node2286Labels = Sparse.eval nodeValue2286 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2286) = mixedMoment B node2286 node2286Labels := rfl
  simpa [nodeValue2286, Sparse.eval] using hc.symm

theorem sound2288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2288 node2288Labels = Sparse.eval nodeValue2288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2288) = mixedMoment B node2288 node2288Labels := rfl
  simpa [nodeValue2288, Sparse.eval] using hc.symm

theorem sound2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2290 node2290Labels = Sparse.eval nodeValue2290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2290) = mixedMoment B node2290 node2290Labels := rfl
  simpa [nodeValue2290, Sparse.eval] using hc.symm

theorem sound2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = Sparse.eval nodeValue2291 (mixedVector B) := by
  simpa only [nodeValue2291, Sparse.eval_nil] using zero2291 B _hB _hF

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

theorem sound2355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2355 node2355Labels = Sparse.eval nodeValue2355 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2355) = mixedMoment B node2355 node2355Labels := rfl
  simpa [nodeValue2355, Sparse.eval] using hc.symm

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

theorem sound2436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2436 node2436Labels = Sparse.eval nodeValue2436 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2436) = mixedMoment B node2436 node2436Labels := rfl
  simpa [nodeValue2436, Sparse.eval] using hc.symm

theorem sound2482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2482 node2482Labels = Sparse.eval nodeValue2482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2482) = mixedMoment B node2482 node2482Labels := rfl
  simpa [nodeValue2482, Sparse.eval] using hc.symm

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

theorem sound2519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2519 node2519Labels = Sparse.eval nodeValue2519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2519) = mixedMoment B node2519 node2519Labels := rfl
  simpa [nodeValue2519, Sparse.eval] using hc.symm

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

theorem sound2569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2569 node2569Labels = Sparse.eval nodeValue2569 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2569) = mixedMoment B node2569 node2569Labels := rfl
  simpa [nodeValue2569, Sparse.eval] using hc.symm

theorem sound2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2590 node2590Labels = Sparse.eval nodeValue2590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2590) = mixedMoment B node2590 node2590Labels := rfl
  simpa [nodeValue2590, Sparse.eval] using hc.symm

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

theorem sound2761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2761 node2761Labels = Sparse.eval nodeValue2761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2761) = mixedMoment B node2761 node2761Labels := rfl
  simpa [nodeValue2761, Sparse.eval] using hc.symm

theorem sound2781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2781 node2781Labels = Sparse.eval nodeValue2781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2781) = mixedMoment B node2781 node2781Labels := rfl
  simpa [nodeValue2781, Sparse.eval] using hc.symm

theorem sound2782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2782 node2782Labels = Sparse.eval nodeValue2782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2782) = mixedMoment B node2782 node2782Labels := rfl
  simpa [nodeValue2782, Sparse.eval] using hc.symm

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

theorem sound3486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3486 node3486Labels = Sparse.eval nodeValue3486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3486) = mixedMoment B node3486 node3486Labels := rfl
  simpa [nodeValue3486, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4353 node4353Labels = Sparse.eval nodeValue4353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4353) = mixedMoment B node4353 node4353Labels := rfl
  simpa [nodeValue4353, Sparse.eval] using hc.symm

theorem sound4358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4358 node4358Labels = Sparse.eval nodeValue4358 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4358) = mixedMoment B node4358 node4358Labels := rfl
  simpa [nodeValue4358, Sparse.eval] using hc.symm

theorem sound4362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4362 node4362Labels = Sparse.eval nodeValue4362 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4362) = mixedMoment B node4362 node4362Labels := rfl
  simpa [nodeValue4362, Sparse.eval] using hc.symm

theorem sound4367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4367 node4367Labels = Sparse.eval nodeValue4367 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4367) = mixedMoment B node4367 node4367Labels := rfl
  simpa [nodeValue4367, Sparse.eval] using hc.symm

theorem sound4374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4374 node4374Labels = Sparse.eval nodeValue4374 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4374) = mixedMoment B node4374 node4374Labels := rfl
  simpa [nodeValue4374, Sparse.eval] using hc.symm

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

theorem sound4463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4463 node4463Labels = Sparse.eval nodeValue4463 (mixedVector B) := by
  have h := singleton4463 B _hB
  rw [sound1046 B _hB _hF, sound1750 B _hB _hF] at h
  norm_num [nodeValue4463, nodeValue1046, nodeValue1750, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4464 node4464Labels = Sparse.eval nodeValue4464 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4464) = mixedMoment B node4464 node4464Labels := rfl
  simpa [nodeValue4464, Sparse.eval] using hc.symm

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

theorem sound4486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4486 node4486Labels = Sparse.eval nodeValue4486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4486) = mixedMoment B node4486 node4486Labels := rfl
  simpa [nodeValue4486, Sparse.eval] using hc.symm

theorem sound4490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4490 node4490Labels = Sparse.eval nodeValue4490 (mixedVector B) := by
  have h := singleton4490 B _hB
  rw [sound1074 B _hB _hF, sound1650 B _hB _hF] at h
  norm_num [nodeValue4490, nodeValue1074, nodeValue1650, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4492 node4492Labels = Sparse.eval nodeValue4492 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4492) = mixedMoment B node4492 node4492Labels := rfl
  simpa [nodeValue4492, Sparse.eval] using hc.symm

theorem sound4504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4504 node4504Labels = Sparse.eval nodeValue4504 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4504) = mixedMoment B node4504 node4504Labels := rfl
  simpa [nodeValue4504, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4699 node4699Labels = Sparse.eval nodeValue4699 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4699) = mixedMoment B node4699 node4699Labels := rfl
  simpa [nodeValue4699, Sparse.eval] using hc.symm

theorem sound4705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4705 node4705Labels = Sparse.eval nodeValue4705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4705) = mixedMoment B node4705 node4705Labels := rfl
  simpa [nodeValue4705, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4772 node4772Labels = Sparse.eval nodeValue4772 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4772) = mixedMoment B node4772 node4772Labels := rfl
  simpa [nodeValue4772, Sparse.eval] using hc.symm

theorem sound4777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4777 node4777Labels = Sparse.eval nodeValue4777 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4777) = mixedMoment B node4777 node4777Labels := rfl
  simpa [nodeValue4777, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = 0 := by
  exact mixedMoment_order_one B hB node4841 node4841Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4807 node4807Labels = Sparse.eval nodeValue4807 (mixedVector B) := by
  have h := singleton4807 B _hB
  rw [sound2025 B _hB _hF, sound2224 B _hB _hF] at h
  norm_num [nodeValue4807, nodeValue2025, nodeValue2224, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4808 node4808Labels = Sparse.eval nodeValue4808 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4808) = mixedMoment B node4808 node4808Labels := rfl
  simpa [nodeValue4808, Sparse.eval] using hc.symm

theorem sound4824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4824 node4824Labels = Sparse.eval nodeValue4824 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4824) = mixedMoment B node4824 node4824Labels := rfl
  simpa [nodeValue4824, Sparse.eval] using hc.symm

theorem sound4827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4827 node4827Labels = Sparse.eval nodeValue4827 (mixedVector B) := by
  have h := singleton4827 B _hB
  rw [sound2047 B _hB _hF, sound2079 B _hB _hF] at h
  norm_num [nodeValue4827, nodeValue2047, nodeValue2079, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4829 node4829Labels = Sparse.eval nodeValue4829 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4829) = mixedMoment B node4829 node4829Labels := rfl
  simpa [nodeValue4829, Sparse.eval] using hc.symm

theorem sound4840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4840 node4840Labels = Sparse.eval nodeValue4840 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4840) = mixedMoment B node4840 node4840Labels := rfl
  simpa [nodeValue4840, Sparse.eval] using hc.symm

theorem sound4841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = Sparse.eval nodeValue4841 (mixedVector B) := by
  simpa only [nodeValue4841, Sparse.eval_nil] using zero4841 B _hB _hF

theorem sound4843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4843 node4843Labels = Sparse.eval nodeValue4843 (mixedVector B) := by
  have h := singleton4843 B _hB
  rw [sound2062 B _hB _hF, sound2230 B _hB _hF] at h
  norm_num [nodeValue4843, nodeValue2062, nodeValue2230, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4844 node4844Labels = Sparse.eval nodeValue4844 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4844) = mixedMoment B node4844 node4844Labels := rfl
  simpa [nodeValue4844, Sparse.eval] using hc.symm

theorem sound4853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4853 node4853Labels = Sparse.eval nodeValue4853 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4853) = mixedMoment B node4853 node4853Labels := rfl
  simpa [nodeValue4853, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4895 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = 0 := by
  exact mixedMoment_order_one B hB node4895 node4895Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4866 node4866Labels = Sparse.eval nodeValue4866 (mixedVector B) := by
  have h := singleton4866 B _hB
  rw [sound2107 B _hB _hF, sound2260 B _hB _hF] at h
  norm_num [nodeValue4866, nodeValue2107, nodeValue2260, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4868 node4868Labels = Sparse.eval nodeValue4868 (mixedVector B) := by
  have h := singleton4868 B _hB
  rw [sound2109 B _hB _hF, sound2261 B _hB _hF] at h
  norm_num [nodeValue4868, nodeValue2109, nodeValue2261, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4872 node4872Labels = Sparse.eval nodeValue4872 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4872) = mixedMoment B node4872 node4872Labels := rfl
  simpa [nodeValue4872, Sparse.eval] using hc.symm

theorem sound4875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4875 node4875Labels = Sparse.eval nodeValue4875 (mixedVector B) := by
  have h := singleton4875 B _hB
  rw [sound2116 B _hB _hF, sound2288 B _hB _hF] at h
  norm_num [nodeValue4875, nodeValue2116, nodeValue2288, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4881 node4881Labels = Sparse.eval nodeValue4881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4881) = mixedMoment B node4881 node4881Labels := rfl
  simpa [nodeValue4881, Sparse.eval] using hc.symm

theorem sound4890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4890 node4890Labels = Sparse.eval nodeValue4890 (mixedVector B) := by
  have h := singleton4890 B _hB
  rw [sound2247 B _hB _hF, sound2290 B _hB _hF] at h
  norm_num [nodeValue4890, nodeValue2247, nodeValue2290, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = Sparse.eval nodeValue4895 (mixedVector B) := by
  simpa only [nodeValue4895, Sparse.eval_nil] using zero4895 B _hB _hF

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

theorem sound5109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5109 node5109Labels = Sparse.eval nodeValue5109 (mixedVector B) := by
  have h := singleton5109 B _hB
  rw [sound2519 B _hB _hF, sound3486 B _hB _hF] at h
  norm_num [nodeValue5109, nodeValue2519, nodeValue3486, Sparse.eval] at h ⊢
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

theorem sound5139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5139 node5139Labels = Sparse.eval nodeValue5139 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5139) = mixedMoment B node5139 node5139Labels := rfl
  simpa [nodeValue5139, Sparse.eval] using hc.symm

theorem sound5173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5173 node5173Labels = Sparse.eval nodeValue5173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5173) = mixedMoment B node5173 node5173Labels := rfl
  simpa [nodeValue5173, Sparse.eval] using hc.symm

theorem sound5175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5175 node5175Labels = Sparse.eval nodeValue5175 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5175) = mixedMoment B node5175 node5175Labels := rfl
  simpa [nodeValue5175, Sparse.eval] using hc.symm

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

theorem sound5295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5295 node5295Labels = Sparse.eval nodeValue5295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5295) = mixedMoment B node5295 node5295Labels := rfl
  simpa [nodeValue5295, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources61
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1952 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1952 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1952 + difference 0 1) (sourceB1952 + difference 1 0) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA1952 + difference 0 1) (sourceB1952 + difference 1 0) sourceC1952) = raw27688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27688; decide +kernel
    rw [ha]
    exact (canonical27688 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1952 + difference 0 2) (sourceB1952 + difference 2 0) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA1952 + difference 0 2) (sourceB1952 + difference 2 0) sourceC1952) = raw27689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27689; decide +kernel
    rw [ha]
    exact (canonical27689 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1952 + difference 0 3) (sourceB1952 + difference 3 0) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA1952 + difference 0 3) (sourceB1952 + difference 3 0) sourceC1952) = raw27690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27690; decide +kernel
    rw [ha]
    exact (canonical27690 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1952 + difference 0 4) (sourceB1952 + difference 4 0) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1952 + difference 0 4) (sourceB1952 + difference 4 0) sourceC1952) = raw27691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27691; decide +kernel
    rw [ha]
    exact (canonical27691 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1952 + difference 0 5) (sourceB1952 + difference 5 0) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA1952 + difference 0 5) (sourceB1952 + difference 5 0) sourceC1952) = raw27692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27692; decide +kernel
    rw [ha]
    exact (canonical27692 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1952 + difference 1 0) (sourceB1952 + difference 0 1) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA1952 + difference 1 0) (sourceB1952 + difference 0 1) sourceC1952) = raw27693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27693; decide +kernel
    rw [ha]
    exact (canonical27693 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1952 + difference 1 2) (sourceB1952 + difference 2 1) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA1952 + difference 1 2) (sourceB1952 + difference 2 1) sourceC1952) = raw27694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27694; decide +kernel
    rw [ha]
    exact (canonical27694 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1952 + difference 1 3) (sourceB1952 + difference 3 1) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA1952 + difference 1 3) (sourceB1952 + difference 3 1) sourceC1952) = raw27695 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27695; decide +kernel
    rw [ha]
    exact (canonical27695 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1952 + difference 1 4) (sourceB1952 + difference 4 1) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA1952 + difference 1 4) (sourceB1952 + difference 4 1) sourceC1952) = raw27696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27696; decide +kernel
    rw [ha]
    exact (canonical27696 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1952 + difference 1 5) (sourceB1952 + difference 5 1) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA1952 + difference 1 5) (sourceB1952 + difference 5 1) sourceC1952) = raw27697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27697; decide +kernel
    rw [ha]
    exact (canonical27697 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1952 + difference 2 0) (sourceB1952 + difference 0 2) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4353) := by
    have ha : (tripleCharges (sourceA1952 + difference 2 0) (sourceB1952 + difference 0 2) sourceC1952) = raw27698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27698; decide +kernel
    rw [ha]
    exact (canonical27698 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1952 + difference 2 1) (sourceB1952 + difference 1 2) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA1952 + difference 2 1) (sourceB1952 + difference 1 2) sourceC1952) = raw27699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27699; decide +kernel
    rw [ha]
    exact (canonical27699 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1952 + difference 2 3) (sourceB1952 + difference 3 2) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4772) := by
    have ha : (tripleCharges (sourceA1952 + difference 2 3) (sourceB1952 + difference 3 2) sourceC1952) = raw27700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27700; decide +kernel
    rw [ha]
    exact (canonical27700 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1952 + difference 2 4) (sourceB1952 + difference 4 2) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1952 + difference 2 4) (sourceB1952 + difference 4 2) sourceC1952) = raw27701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27701; decide +kernel
    rw [ha]
    exact (canonical27701 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1952 + difference 2 5) (sourceB1952 + difference 5 2) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA1952 + difference 2 5) (sourceB1952 + difference 5 2) sourceC1952) = raw27702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27702; decide +kernel
    rw [ha]
    exact (canonical27702 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1952 + difference 3 0) (sourceB1952 + difference 0 3) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4353) := by
    have ha : (tripleCharges (sourceA1952 + difference 3 0) (sourceB1952 + difference 0 3) sourceC1952) = raw27703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27703; decide +kernel
    rw [ha]
    exact (canonical27703 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1952 + difference 3 1) (sourceB1952 + difference 1 3) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA1952 + difference 3 1) (sourceB1952 + difference 1 3) sourceC1952) = raw27704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27704; decide +kernel
    rw [ha]
    exact (canonical27704 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1952 + difference 3 2) (sourceB1952 + difference 2 3) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4772) := by
    have ha : (tripleCharges (sourceA1952 + difference 3 2) (sourceB1952 + difference 2 3) sourceC1952) = raw27705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27705; decide +kernel
    rw [ha]
    exact (canonical27705 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1952 + difference 3 4) (sourceB1952 + difference 4 3) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1952 + difference 3 4) (sourceB1952 + difference 4 3) sourceC1952) = raw27706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27706; decide +kernel
    rw [ha]
    exact (canonical27706 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1952 + difference 3 5) (sourceB1952 + difference 5 3) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA1952 + difference 3 5) (sourceB1952 + difference 5 3) sourceC1952) = raw27707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27707; decide +kernel
    rw [ha]
    exact (canonical27707 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1952 + difference 4 0) (sourceB1952 + difference 0 4) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4362) := by
    have ha : (tripleCharges (sourceA1952 + difference 4 0) (sourceB1952 + difference 0 4) sourceC1952) = raw27708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27708; decide +kernel
    rw [ha]
    exact (canonical27708 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1952 + difference 4 1) (sourceB1952 + difference 1 4) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4705) := by
    have ha : (tripleCharges (sourceA1952 + difference 4 1) (sourceB1952 + difference 1 4) sourceC1952) = raw27709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27709; decide +kernel
    rw [ha]
    exact (canonical27709 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1952 + difference 4 2) (sourceB1952 + difference 2 4) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4699) := by
    have ha : (tripleCharges (sourceA1952 + difference 4 2) (sourceB1952 + difference 2 4) sourceC1952) = raw27710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27710; decide +kernel
    rw [ha]
    exact (canonical27710 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1952 + difference 4 3) (sourceB1952 + difference 3 4) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4699) := by
    have ha : (tripleCharges (sourceA1952 + difference 4 3) (sourceB1952 + difference 3 4) sourceC1952) = raw27711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27711; decide +kernel
    rw [ha]
    exact (canonical27711 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1952 + difference 4 5) (sourceB1952 + difference 5 4) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA1952 + difference 4 5) (sourceB1952 + difference 5 4) sourceC1952) = raw27712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27712; decide +kernel
    rw [ha]
    exact (canonical27712 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1952 + difference 5 0) (sourceB1952 + difference 0 5) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4358) := by
    have ha : (tripleCharges (sourceA1952 + difference 5 0) (sourceB1952 + difference 0 5) sourceC1952) = raw27713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27713; decide +kernel
    rw [ha]
    exact (canonical27713 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1952 + difference 5 1) (sourceB1952 + difference 1 5) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4374) := by
    have ha : (tripleCharges (sourceA1952 + difference 5 1) (sourceB1952 + difference 1 5) sourceC1952) = raw27714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27714; decide +kernel
    rw [ha]
    exact (canonical27714 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1952 + difference 5 2) (sourceB1952 + difference 2 5) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4367) := by
    have ha : (tripleCharges (sourceA1952 + difference 5 2) (sourceB1952 + difference 2 5) sourceC1952) = raw27715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27715; decide +kernel
    rw [ha]
    exact (canonical27715 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1952 + difference 5 3) (sourceB1952 + difference 3 5) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4367) := by
    have ha : (tripleCharges (sourceA1952 + difference 5 3) (sourceB1952 + difference 3 5) sourceC1952) = raw27716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27716; decide +kernel
    rw [ha]
    exact (canonical27716 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1952 + difference 5 4) (sourceB1952 + difference 4 5) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1952 + difference 5 4) (sourceB1952 + difference 4 5) sourceC1952) = raw27717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27717; decide +kernel
    rw [ha]
    exact (canonical27717 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1952 sourceB1952 sourceC1952
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1952, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1953 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1953 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1953 + difference 0 1) (sourceB1953 + difference 1 0) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA1953 + difference 0 1) (sourceB1953 + difference 1 0) sourceC1953) = raw27718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27718; decide +kernel
    rw [ha]
    exact (canonical27718 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1953 + difference 0 2) (sourceB1953 + difference 2 0) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1953 + difference 0 2) (sourceB1953 + difference 2 0) sourceC1953) = raw27719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27719; decide +kernel
    rw [ha]
    exact (canonical27719 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1953 + difference 0 3) (sourceB1953 + difference 3 0) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1953 + difference 0 3) (sourceB1953 + difference 3 0) sourceC1953) = raw27720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27720; decide +kernel
    rw [ha]
    exact (canonical27720 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1953 + difference 0 4) (sourceB1953 + difference 4 0) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA1953 + difference 0 4) (sourceB1953 + difference 4 0) sourceC1953) = raw27721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27721; decide +kernel
    rw [ha]
    exact (canonical27721 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1953 + difference 0 5) (sourceB1953 + difference 5 0) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA1953 + difference 0 5) (sourceB1953 + difference 5 0) sourceC1953) = raw27722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27722; decide +kernel
    rw [ha]
    exact (canonical27722 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1953 + difference 1 0) (sourceB1953 + difference 0 1) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1953 + difference 1 0) (sourceB1953 + difference 0 1) sourceC1953) = raw27723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27723; decide +kernel
    rw [ha]
    exact (canonical27723 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1953 + difference 1 2) (sourceB1953 + difference 2 1) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1953 + difference 1 2) (sourceB1953 + difference 2 1) sourceC1953) = raw27724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27724; decide +kernel
    rw [ha]
    exact (canonical27724 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1953 + difference 1 3) (sourceB1953 + difference 3 1) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1953 + difference 1 3) (sourceB1953 + difference 3 1) sourceC1953) = raw27725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27725; decide +kernel
    rw [ha]
    exact (canonical27725 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1953 + difference 1 4) (sourceB1953 + difference 4 1) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA1953 + difference 1 4) (sourceB1953 + difference 4 1) sourceC1953) = raw27726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27726; decide +kernel
    rw [ha]
    exact (canonical27726 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1953 + difference 1 5) (sourceB1953 + difference 5 1) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA1953 + difference 1 5) (sourceB1953 + difference 5 1) sourceC1953) = raw27727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27727; decide +kernel
    rw [ha]
    exact (canonical27727 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1953 + difference 2 0) (sourceB1953 + difference 0 2) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1686) := by
    have ha : (tripleCharges (sourceA1953 + difference 2 0) (sourceB1953 + difference 0 2) sourceC1953) = raw27728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27728; decide +kernel
    rw [ha]
    exact (canonical27728 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1953 + difference 2 1) (sourceB1953 + difference 1 2) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA1953 + difference 2 1) (sourceB1953 + difference 1 2) sourceC1953) = raw27729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27729; decide +kernel
    rw [ha]
    exact (canonical27729 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1953 + difference 2 3) (sourceB1953 + difference 3 2) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2198) := by
    have ha : (tripleCharges (sourceA1953 + difference 2 3) (sourceB1953 + difference 3 2) sourceC1953) = raw27730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27730; decide +kernel
    rw [ha]
    exact (canonical27730 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1953 + difference 2 4) (sourceB1953 + difference 4 2) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1953 + difference 2 4) (sourceB1953 + difference 4 2) sourceC1953) = raw27731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27731; decide +kernel
    rw [ha]
    exact (canonical27731 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1953 + difference 2 5) (sourceB1953 + difference 5 2) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA1953 + difference 2 5) (sourceB1953 + difference 5 2) sourceC1953) = raw27732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27732; decide +kernel
    rw [ha]
    exact (canonical27732 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1953 + difference 3 0) (sourceB1953 + difference 0 3) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1686) := by
    have ha : (tripleCharges (sourceA1953 + difference 3 0) (sourceB1953 + difference 0 3) sourceC1953) = raw27733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27733; decide +kernel
    rw [ha]
    exact (canonical27733 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1953 + difference 3 1) (sourceB1953 + difference 1 3) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA1953 + difference 3 1) (sourceB1953 + difference 1 3) sourceC1953) = raw27734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27734; decide +kernel
    rw [ha]
    exact (canonical27734 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1953 + difference 3 2) (sourceB1953 + difference 2 3) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2198) := by
    have ha : (tripleCharges (sourceA1953 + difference 3 2) (sourceB1953 + difference 2 3) sourceC1953) = raw27735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27735; decide +kernel
    rw [ha]
    exact (canonical27735 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1953 + difference 3 4) (sourceB1953 + difference 4 3) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1953 + difference 3 4) (sourceB1953 + difference 4 3) sourceC1953) = raw27736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27736; decide +kernel
    rw [ha]
    exact (canonical27736 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1953 + difference 3 5) (sourceB1953 + difference 5 3) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA1953 + difference 3 5) (sourceB1953 + difference 5 3) sourceC1953) = raw27737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27737; decide +kernel
    rw [ha]
    exact (canonical27737 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1953 + difference 4 0) (sourceB1953 + difference 0 4) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1687) := by
    have ha : (tripleCharges (sourceA1953 + difference 4 0) (sourceB1953 + difference 0 4) sourceC1953) = raw27738 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27738; decide +kernel
    rw [ha]
    exact (canonical27738 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1953 + difference 4 1) (sourceB1953 + difference 1 4) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2286) := by
    have ha : (tripleCharges (sourceA1953 + difference 4 1) (sourceB1953 + difference 1 4) sourceC1953) = raw27739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27739; decide +kernel
    rw [ha]
    exact (canonical27739 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1953 + difference 4 2) (sourceB1953 + difference 2 4) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2256) := by
    have ha : (tripleCharges (sourceA1953 + difference 4 2) (sourceB1953 + difference 2 4) sourceC1953) = raw27740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27740; decide +kernel
    rw [ha]
    exact (canonical27740 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1953 + difference 4 3) (sourceB1953 + difference 3 4) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2256) := by
    have ha : (tripleCharges (sourceA1953 + difference 4 3) (sourceB1953 + difference 3 4) sourceC1953) = raw27741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27741; decide +kernel
    rw [ha]
    exact (canonical27741 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1953 + difference 4 5) (sourceB1953 + difference 5 4) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA1953 + difference 4 5) (sourceB1953 + difference 5 4) sourceC1953) = raw27742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27742; decide +kernel
    rw [ha]
    exact (canonical27742 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1953 + difference 5 0) (sourceB1953 + difference 0 5) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1695) := by
    have ha : (tripleCharges (sourceA1953 + difference 5 0) (sourceB1953 + difference 0 5) sourceC1953) = raw27743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27743; decide +kernel
    rw [ha]
    exact (canonical27743 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1953 + difference 5 1) (sourceB1953 + difference 1 5) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA1953 + difference 5 1) (sourceB1953 + difference 1 5) sourceC1953) = raw27744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27744; decide +kernel
    rw [ha]
    exact (canonical27744 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1953 + difference 5 2) (sourceB1953 + difference 2 5) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA1953 + difference 5 2) (sourceB1953 + difference 2 5) sourceC1953) = raw27745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27745; decide +kernel
    rw [ha]
    exact (canonical27745 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1953 + difference 5 3) (sourceB1953 + difference 3 5) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA1953 + difference 5 3) (sourceB1953 + difference 3 5) sourceC1953) = raw27746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27746; decide +kernel
    rw [ha]
    exact (canonical27746 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1953 + difference 5 4) (sourceB1953 + difference 4 5) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1953 + difference 5 4) (sourceB1953 + difference 4 5) sourceC1953) = raw27747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27747; decide +kernel
    rw [ha]
    exact (canonical27747 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1953 sourceB1953 sourceC1953
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1953, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1954 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1954 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1954 + difference 0 1) (sourceB1954 + difference 1 0) sourceC1954) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2116) := by
    have ha : (tripleCharges (sourceA1954 + difference 0 1) (sourceB1954 + difference 1 0) sourceC1954) = raw27748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1954 sourceB1954 sourceC1954 difference raw27748; decide +kernel
    rw [ha]
    exact (canonical27748 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1954 + difference 1 1) (sourceB1954 + difference 1 1) sourceC1954) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA1954 + difference 1 1) (sourceB1954 + difference 1 1) sourceC1954) = raw27749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1954 sourceB1954 sourceC1954 difference raw27749; decide +kernel
    rw [ha]
    exact (canonical27749 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1954 + difference 2 1) (sourceB1954 + difference 1 2) sourceC1954) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1979) := by
    have ha : (tripleCharges (sourceA1954 + difference 2 1) (sourceB1954 + difference 1 2) sourceC1954) = raw27750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1954 sourceB1954 sourceC1954 difference raw27750; decide +kernel
    rw [ha]
    exact (canonical27750 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1954 + difference 3 1) (sourceB1954 + difference 1 3) sourceC1954) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1979) := by
    have ha : (tripleCharges (sourceA1954 + difference 3 1) (sourceB1954 + difference 1 3) sourceC1954) = raw27751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1954 sourceB1954 sourceC1954 difference raw27751; decide +kernel
    rw [ha]
    exact (canonical27751 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1954 + difference 4 1) (sourceB1954 + difference 1 4) sourceC1954) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1831) := by
    have ha : (tripleCharges (sourceA1954 + difference 4 1) (sourceB1954 + difference 1 4) sourceC1954) = raw27752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1954 sourceB1954 sourceC1954 difference raw27752; decide +kernel
    rw [ha]
    exact (canonical27752 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1954 + difference 5 1) (sourceB1954 + difference 1 5) sourceC1954) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 953) := by
    have ha : (tripleCharges (sourceA1954 + difference 5 1) (sourceB1954 + difference 1 5) sourceC1954) = raw27753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1954 sourceB1954 sourceC1954 difference raw27753; decide +kernel
    rw [ha]
    exact (canonical27753 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1954 + sourceB1954) sourceC1954) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1954 + sourceB1954) sourceC1954) = raw27754 := by
      apply Matrix.ext; unfold doubleCharges sourceA1954 sourceB1954 sourceC1954 raw27754; decide +kernel
    rw [ha]
    exact (canonical27754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1954 sourceB1954 sourceC1954
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1954, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1955 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1955 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1955 + difference 2 0) (sourceB1955 + difference 0 2) sourceC1955) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1336) := by
    have ha : (tripleCharges (sourceA1955 + difference 2 0) (sourceB1955 + difference 0 2) sourceC1955) = raw27755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1955 sourceB1955 sourceC1955 difference raw27755; decide +kernel
    rw [ha]
    exact (canonical27755 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1955 + difference 2 1) (sourceB1955 + difference 1 2) sourceC1955) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1979) := by
    have ha : (tripleCharges (sourceA1955 + difference 2 1) (sourceB1955 + difference 1 2) sourceC1955) = raw27750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1955 sourceB1955 sourceC1955 difference raw27750; decide +kernel
    rw [ha]
    exact (canonical27750 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1955 + difference 2 2) (sourceB1955 + difference 2 2) sourceC1955) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA1955 + difference 2 2) (sourceB1955 + difference 2 2) sourceC1955) = raw27749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1955 sourceB1955 sourceC1955 difference raw27749; decide +kernel
    rw [ha]
    exact (canonical27749 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1955 + difference 2 3) (sourceB1955 + difference 3 2) sourceC1955) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1973) := by
    have ha : (tripleCharges (sourceA1955 + difference 2 3) (sourceB1955 + difference 3 2) sourceC1955) = raw27756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1955 sourceB1955 sourceC1955 difference raw27756; decide +kernel
    rw [ha]
    exact (canonical27756 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1955 + difference 2 4) (sourceB1955 + difference 4 2) sourceC1955) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1955 + difference 2 4) (sourceB1955 + difference 4 2) sourceC1955) = raw27757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1955 sourceB1955 sourceC1955 difference raw27757; decide +kernel
    rw [ha]
    exact (canonical27757 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1955 + difference 2 5) (sourceB1955 + difference 5 2) sourceC1955) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA1955 + difference 2 5) (sourceB1955 + difference 5 2) sourceC1955) = raw27758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1955 sourceB1955 sourceC1955 difference raw27758; decide +kernel
    rw [ha]
    exact (canonical27758 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1955 + sourceB1955) sourceC1955) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1955 + sourceB1955) sourceC1955) = raw27754 := by
      apply Matrix.ext; unfold doubleCharges sourceA1955 sourceB1955 sourceC1955 raw27754; decide +kernel
    rw [ha]
    exact (canonical27754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1955 sourceB1955 sourceC1955
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1955, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1956 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1956 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1956 + difference 0 1) (sourceB1956 + difference 1 0) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA1956 + difference 0 1) (sourceB1956 + difference 1 0) sourceC1956) = raw27759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27759; decide +kernel
    rw [ha]
    exact (canonical27759 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1956 + difference 0 2) (sourceB1956 + difference 2 0) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA1956 + difference 0 2) (sourceB1956 + difference 2 0) sourceC1956) = raw27760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27760; decide +kernel
    rw [ha]
    exact (canonical27760 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1956 + difference 0 3) (sourceB1956 + difference 3 0) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA1956 + difference 0 3) (sourceB1956 + difference 3 0) sourceC1956) = raw27761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27761; decide +kernel
    rw [ha]
    exact (canonical27761 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1956 + difference 0 4) (sourceB1956 + difference 4 0) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA1956 + difference 0 4) (sourceB1956 + difference 4 0) sourceC1956) = raw27642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27642; decide +kernel
    rw [ha]
    exact (canonical27642 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1956 + difference 0 5) (sourceB1956 + difference 5 0) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA1956 + difference 0 5) (sourceB1956 + difference 5 0) sourceC1956) = raw27762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27762; decide +kernel
    rw [ha]
    exact (canonical27762 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1956 + difference 1 0) (sourceB1956 + difference 0 1) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4872) := by
    have ha : (tripleCharges (sourceA1956 + difference 1 0) (sourceB1956 + difference 0 1) sourceC1956) = raw27763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27763; decide +kernel
    rw [ha]
    exact (canonical27763 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1956 + difference 1 2) (sourceB1956 + difference 2 1) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4829) := by
    have ha : (tripleCharges (sourceA1956 + difference 1 2) (sourceB1956 + difference 2 1) sourceC1956) = raw27764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27764; decide +kernel
    rw [ha]
    exact (canonical27764 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1956 + difference 1 3) (sourceB1956 + difference 3 1) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4829) := by
    have ha : (tripleCharges (sourceA1956 + difference 1 3) (sourceB1956 + difference 3 1) sourceC1956) = raw27765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27765; decide +kernel
    rw [ha]
    exact (canonical27765 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1956 + difference 1 4) (sourceB1956 + difference 4 1) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA1956 + difference 1 4) (sourceB1956 + difference 4 1) sourceC1956) = raw27647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27647; decide +kernel
    rw [ha]
    exact (canonical27647 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1956 + difference 1 5) (sourceB1956 + difference 5 1) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4492) := by
    have ha : (tripleCharges (sourceA1956 + difference 1 5) (sourceB1956 + difference 5 1) sourceC1956) = raw27766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27766; decide +kernel
    rw [ha]
    exact (canonical27766 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1956 + difference 2 0) (sourceB1956 + difference 0 2) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA1956 + difference 2 0) (sourceB1956 + difference 0 2) sourceC1956) = raw27767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27767; decide +kernel
    rw [ha]
    exact (canonical27767 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1956 + difference 2 1) (sourceB1956 + difference 1 2) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA1956 + difference 2 1) (sourceB1956 + difference 1 2) sourceC1956) = raw27768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27768; decide +kernel
    rw [ha]
    exact (canonical27768 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1956 + difference 2 3) (sourceB1956 + difference 3 2) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4824) := by
    have ha : (tripleCharges (sourceA1956 + difference 2 3) (sourceB1956 + difference 3 2) sourceC1956) = raw27769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27769; decide +kernel
    rw [ha]
    exact (canonical27769 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1956 + difference 2 4) (sourceB1956 + difference 4 2) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1956 + difference 2 4) (sourceB1956 + difference 4 2) sourceC1956) = raw27652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27652; decide +kernel
    rw [ha]
    exact (canonical27652 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1956 + difference 2 5) (sourceB1956 + difference 5 2) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4486) := by
    have ha : (tripleCharges (sourceA1956 + difference 2 5) (sourceB1956 + difference 5 2) sourceC1956) = raw27770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27770; decide +kernel
    rw [ha]
    exact (canonical27770 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1956 + difference 3 0) (sourceB1956 + difference 0 3) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA1956 + difference 3 0) (sourceB1956 + difference 0 3) sourceC1956) = raw27771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27771; decide +kernel
    rw [ha]
    exact (canonical27771 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1956 + difference 3 1) (sourceB1956 + difference 1 3) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA1956 + difference 3 1) (sourceB1956 + difference 1 3) sourceC1956) = raw27772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27772; decide +kernel
    rw [ha]
    exact (canonical27772 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1956 + difference 3 2) (sourceB1956 + difference 2 3) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4824) := by
    have ha : (tripleCharges (sourceA1956 + difference 3 2) (sourceB1956 + difference 2 3) sourceC1956) = raw27773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27773; decide +kernel
    rw [ha]
    exact (canonical27773 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1956 + difference 3 4) (sourceB1956 + difference 4 3) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1956 + difference 3 4) (sourceB1956 + difference 4 3) sourceC1956) = raw27657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27657; decide +kernel
    rw [ha]
    exact (canonical27657 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1956 + difference 3 5) (sourceB1956 + difference 5 3) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4486) := by
    have ha : (tripleCharges (sourceA1956 + difference 3 5) (sourceB1956 + difference 5 3) sourceC1956) = raw27774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27774; decide +kernel
    rw [ha]
    exact (canonical27774 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1956 + difference 4 0) (sourceB1956 + difference 0 4) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA1956 + difference 4 0) (sourceB1956 + difference 0 4) sourceC1956) = raw27775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27775; decide +kernel
    rw [ha]
    exact (canonical27775 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1956 + difference 4 1) (sourceB1956 + difference 1 4) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4881) := by
    have ha : (tripleCharges (sourceA1956 + difference 4 1) (sourceB1956 + difference 1 4) sourceC1956) = raw27776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27776; decide +kernel
    rw [ha]
    exact (canonical27776 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1956 + difference 4 2) (sourceB1956 + difference 2 4) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4840) := by
    have ha : (tripleCharges (sourceA1956 + difference 4 2) (sourceB1956 + difference 2 4) sourceC1956) = raw27777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27777; decide +kernel
    rw [ha]
    exact (canonical27777 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1956 + difference 4 3) (sourceB1956 + difference 3 4) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4840) := by
    have ha : (tripleCharges (sourceA1956 + difference 4 3) (sourceB1956 + difference 3 4) sourceC1956) = raw27778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27778; decide +kernel
    rw [ha]
    exact (canonical27778 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1956 + difference 4 5) (sourceB1956 + difference 5 4) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4504) := by
    have ha : (tripleCharges (sourceA1956 + difference 4 5) (sourceB1956 + difference 5 4) sourceC1956) = raw27779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27779; decide +kernel
    rw [ha]
    exact (canonical27779 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1956 + difference 5 0) (sourceB1956 + difference 0 5) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA1956 + difference 5 0) (sourceB1956 + difference 0 5) sourceC1956) = raw27658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27658; decide +kernel
    rw [ha]
    exact (canonical27658 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1956 + difference 5 1) (sourceB1956 + difference 1 5) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA1956 + difference 5 1) (sourceB1956 + difference 1 5) sourceC1956) = raw27659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27659; decide +kernel
    rw [ha]
    exact (canonical27659 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1956 + difference 5 2) (sourceB1956 + difference 2 5) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA1956 + difference 5 2) (sourceB1956 + difference 2 5) sourceC1956) = raw27660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27660; decide +kernel
    rw [ha]
    exact (canonical27660 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1956 + difference 5 3) (sourceB1956 + difference 3 5) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA1956 + difference 5 3) (sourceB1956 + difference 3 5) sourceC1956) = raw27661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27661; decide +kernel
    rw [ha]
    exact (canonical27661 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1956 + difference 5 4) (sourceB1956 + difference 4 5) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA1956 + difference 5 4) (sourceB1956 + difference 4 5) sourceC1956) = raw27780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27780; decide +kernel
    rw [ha]
    exact (canonical27780 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1956 sourceB1956 sourceC1956
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1956, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1958 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1958 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1958 + difference 3 0) (sourceB1958 + difference 0 3) sourceC1958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1159) := by
    have ha : (tripleCharges (sourceA1958 + difference 3 0) (sourceB1958 + difference 0 3) sourceC1958) = raw27811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1958 sourceB1958 sourceC1958 difference raw27811; decide +kernel
    rw [ha]
    exact (canonical27811 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1958 + difference 3 1) (sourceB1958 + difference 1 3) sourceC1958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2355) := by
    have ha : (tripleCharges (sourceA1958 + difference 3 1) (sourceB1958 + difference 1 3) sourceC1958) = raw27812 := by
      apply Matrix.ext; unfold tripleCharges sourceA1958 sourceB1958 sourceC1958 difference raw27812; decide +kernel
    rw [ha]
    exact (canonical27812 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1958 + difference 3 2) (sourceB1958 + difference 2 3) sourceC1958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2436) := by
    have ha : (tripleCharges (sourceA1958 + difference 3 2) (sourceB1958 + difference 2 3) sourceC1958) = raw27813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1958 sourceB1958 sourceC1958 difference raw27813; decide +kernel
    rw [ha]
    exact (canonical27813 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1958 + difference 3 3) (sourceB1958 + difference 3 3) sourceC1958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2569) := by
    have ha : (tripleCharges (sourceA1958 + difference 3 3) (sourceB1958 + difference 3 3) sourceC1958) = raw27814 := by
      apply Matrix.ext; unfold tripleCharges sourceA1958 sourceB1958 sourceC1958 difference raw27814; decide +kernel
    rw [ha]
    exact (canonical27814 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1958 + difference 3 4) (sourceB1958 + difference 4 3) sourceC1958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA1958 + difference 3 4) (sourceB1958 + difference 4 3) sourceC1958) = raw27815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1958 sourceB1958 sourceC1958 difference raw27815; decide +kernel
    rw [ha]
    exact (canonical27815 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1958 + difference 3 5) (sourceB1958 + difference 5 3) sourceC1958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA1958 + difference 3 5) (sourceB1958 + difference 5 3) sourceC1958) = raw27816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1958 sourceB1958 sourceC1958 difference raw27816; decide +kernel
    rw [ha]
    exact (canonical27816 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1958 + sourceB1958) sourceC1958) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1958 + sourceB1958) sourceC1958) = raw24400 := by
      apply Matrix.ext; unfold doubleCharges sourceA1958 sourceB1958 sourceC1958 raw24400; decide +kernel
    rw [ha]
    exact (canonical24400 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1958 sourceB1958 sourceC1958
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1958, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1657 : Integer.Sparse.reindex keyMap MixedData.row1657 = numericRow1657 := by decide +kernel

theorem numericCheck1657 (x : Master → ℝ) : Integer.Sparse.eval numericRow1657 x =
    (4 : ℝ) * reducedSource1657 x := by
  norm_num [numericRow1657, reducedSource1657, Integer.Sparse.eval, Sparse.eval, nodeValue4353, nodeValue4358, nodeValue4362, nodeValue4367, nodeValue4374, nodeValue4463, nodeValue4464, nodeValue4699, nodeValue4705, nodeValue4772, nodeValue4777, nodeValue4807, nodeValue4853, nodeValue4866, nodeValue4875, nodeValue4890, nodeValue4895, nodeValue5173, nodeValue5175, nodeValue5295, nodeValue5304]
  ring

theorem reindexCheck1658 : Integer.Sparse.reindex keyMap MixedData.row1658 = numericRow1658 := by decide +kernel

theorem numericCheck1658 (x : Master → ℝ) : Integer.Sparse.eval numericRow1658 x =
    (1 : ℝ) * reducedSource1658 x := by
  norm_num [numericRow1658, reducedSource1658, Integer.Sparse.eval, Sparse.eval, nodeValue1686, nodeValue1687, nodeValue1695, nodeValue1720, nodeValue1745, nodeValue1748, nodeValue1750, nodeValue2198, nodeValue2223, nodeValue2224, nodeValue2256, nodeValue2259, nodeValue2260, nodeValue2286, nodeValue2288, nodeValue2290, nodeValue2291, nodeValue2735, nodeValue2761, nodeValue2781, nodeValue2782]

theorem reindexCheck1659 : Integer.Sparse.reindex keyMap MixedData.row1659 = numericRow1659 := by decide +kernel

theorem numericCheck1659 (x : Master → ℝ) : Integer.Sparse.eval numericRow1659 x =
    (1 : ℝ) * reducedSource1659 x := by
  norm_num [numericRow1659, reducedSource1659, Integer.Sparse.eval, Sparse.eval, nodeValue953, nodeValue1831, nodeValue1979, nodeValue2112, nodeValue2116, nodeValue4083]

theorem reindexCheck1660 : Integer.Sparse.reindex keyMap MixedData.row1660 = numericRow1660 := by decide +kernel

theorem numericCheck1660 (x : Master → ℝ) : Integer.Sparse.eval numericRow1660 x =
    (1 : ℝ) * reducedSource1660 x := by
  norm_num [numericRow1660, reducedSource1660, Integer.Sparse.eval, Sparse.eval, nodeValue1336, nodeValue1973, nodeValue1979, nodeValue2025, nodeValue2112, nodeValue2952, nodeValue4083]

theorem reindexCheck1661 : Integer.Sparse.reindex keyMap MixedData.row1661 = numericRow1661 := by decide +kernel

theorem numericCheck1661 (x : Master → ℝ) : Integer.Sparse.eval numericRow1661 x =
    (8640 : ℝ) * reducedSource1661 x := by
  norm_num [numericRow1661, reducedSource1661, Integer.Sparse.eval, Sparse.eval, nodeValue4486, nodeValue4490, nodeValue4492, nodeValue4504, nodeValue4807, nodeValue4808, nodeValue4824, nodeValue4827, nodeValue4829, nodeValue4840, nodeValue4841, nodeValue4843, nodeValue4844, nodeValue4853, nodeValue4868, nodeValue4872, nodeValue4881, nodeValue5109, nodeValue5139, nodeValue5174]
  ring

theorem reindexCheck1663 : Integer.Sparse.reindex keyMap MixedData.row1663 = numericRow1663 := by decide +kernel

theorem numericCheck1663 (x : Master → ℝ) : Integer.Sparse.eval numericRow1663 x =
    (1 : ℝ) * reducedSource1663 x := by
  norm_num [numericRow1663, reducedSource1663, Integer.Sparse.eval, Sparse.eval, nodeValue1159, nodeValue2355, nodeValue2436, nodeValue2482, nodeValue2569, nodeValue2590, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1657 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1657 (mixedVector B) = 0 := by
  have h4353 : mixedVector B (Sum.inr 4353) = Sparse.eval nodeValue4353 (mixedVector B) := by
    change mixedMoment B node4353 node4353Labels = _
    exact sound4353 B hB hF
  have h4358 : mixedVector B (Sum.inr 4358) = Sparse.eval nodeValue4358 (mixedVector B) := by
    change mixedMoment B node4358 node4358Labels = _
    exact sound4358 B hB hF
  have h4362 : mixedVector B (Sum.inr 4362) = Sparse.eval nodeValue4362 (mixedVector B) := by
    change mixedMoment B node4362 node4362Labels = _
    exact sound4362 B hB hF
  have h4367 : mixedVector B (Sum.inr 4367) = Sparse.eval nodeValue4367 (mixedVector B) := by
    change mixedMoment B node4367 node4367Labels = _
    exact sound4367 B hB hF
  have h4374 : mixedVector B (Sum.inr 4374) = Sparse.eval nodeValue4374 (mixedVector B) := by
    change mixedMoment B node4374 node4374Labels = _
    exact sound4374 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4464 : mixedVector B (Sum.inr 4464) = Sparse.eval nodeValue4464 (mixedVector B) := by
    change mixedMoment B node4464 node4464Labels = _
    exact sound4464 B hB hF
  have h4699 : mixedVector B (Sum.inr 4699) = Sparse.eval nodeValue4699 (mixedVector B) := by
    change mixedMoment B node4699 node4699Labels = _
    exact sound4699 B hB hF
  have h4705 : mixedVector B (Sum.inr 4705) = Sparse.eval nodeValue4705 (mixedVector B) := by
    change mixedMoment B node4705 node4705Labels = _
    exact sound4705 B hB hF
  have h4772 : mixedVector B (Sum.inr 4772) = Sparse.eval nodeValue4772 (mixedVector B) := by
    change mixedMoment B node4772 node4772Labels = _
    exact sound4772 B hB hF
  have h4777 : mixedVector B (Sum.inr 4777) = Sparse.eval nodeValue4777 (mixedVector B) := by
    change mixedMoment B node4777 node4777Labels = _
    exact sound4777 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4853 : mixedVector B (Sum.inr 4853) = Sparse.eval nodeValue4853 (mixedVector B) := by
    change mixedMoment B node4853 node4853Labels = _
    exact sound4853 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4875 : mixedVector B (Sum.inr 4875) = Sparse.eval nodeValue4875 (mixedVector B) := by
    change mixedMoment B node4875 node4875Labels = _
    exact sound4875 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h5173 : mixedVector B (Sum.inr 5173) = Sparse.eval nodeValue5173 (mixedVector B) := by
    change mixedMoment B node5173 node5173Labels = _
    exact sound5173 B hB hF
  have h5175 : mixedVector B (Sum.inr 5175) = Sparse.eval nodeValue5175 (mixedVector B) := by
    change mixedMoment B node5175 node5175Labels = _
    exact sound5175 B hB hF
  have h5295 : mixedVector B (Sum.inr 5295) = Sparse.eval nodeValue5295 (mixedVector B) := by
    change mixedMoment B node5295 node5295Labels = _
    exact sound5295 B hB hF
  have h5304 : mixedVector B (Sum.inr 5304) = Sparse.eval nodeValue5304 (mixedVector B) := by
    change mixedMoment B node5304 node5304Labels = _
    exact sound5304 B hB hF
  simpa only [sourceForm1952, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4353, h4358, h4362, h4367, h4374, h4463, h4464, h4699, h4705, h4772, h4777, h4807, h4853, h4866, h4875, h4890, h4895, h5173, h5175, h5295, h5304, reducedSource1657] using sourceEq1952 B hB

theorem rowSound1657 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1657 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1657, numericCheck1657, reducedZero1657 B hB hF, mul_zero]

theorem reducedZero1658 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1658 (mixedVector B) = 0 := by
  have h1686 : mixedVector B (Sum.inr 1686) = Sparse.eval nodeValue1686 (mixedVector B) := by
    change mixedMoment B node1686 node1686Labels = _
    exact sound1686 B hB hF
  have h1687 : mixedVector B (Sum.inr 1687) = Sparse.eval nodeValue1687 (mixedVector B) := by
    change mixedMoment B node1687 node1687Labels = _
    exact sound1687 B hB hF
  have h1695 : mixedVector B (Sum.inr 1695) = Sparse.eval nodeValue1695 (mixedVector B) := by
    change mixedMoment B node1695 node1695Labels = _
    exact sound1695 B hB hF
  have h1720 : mixedVector B (Sum.inr 1720) = Sparse.eval nodeValue1720 (mixedVector B) := by
    change mixedMoment B node1720 node1720Labels = _
    exact sound1720 B hB hF
  have h1745 : mixedVector B (Sum.inr 1745) = Sparse.eval nodeValue1745 (mixedVector B) := by
    change mixedMoment B node1745 node1745Labels = _
    exact sound1745 B hB hF
  have h1748 : mixedVector B (Sum.inr 1748) = Sparse.eval nodeValue1748 (mixedVector B) := by
    change mixedMoment B node1748 node1748Labels = _
    exact sound1748 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h2198 : mixedVector B (Sum.inr 2198) = Sparse.eval nodeValue2198 (mixedVector B) := by
    change mixedMoment B node2198 node2198Labels = _
    exact sound2198 B hB hF
  have h2223 : mixedVector B (Sum.inr 2223) = Sparse.eval nodeValue2223 (mixedVector B) := by
    change mixedMoment B node2223 node2223Labels = _
    exact sound2223 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2256 : mixedVector B (Sum.inr 2256) = Sparse.eval nodeValue2256 (mixedVector B) := by
    change mixedMoment B node2256 node2256Labels = _
    exact sound2256 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h2286 : mixedVector B (Sum.inr 2286) = Sparse.eval nodeValue2286 (mixedVector B) := by
    change mixedMoment B node2286 node2286Labels = _
    exact sound2286 B hB hF
  have h2288 : mixedVector B (Sum.inr 2288) = Sparse.eval nodeValue2288 (mixedVector B) := by
    change mixedMoment B node2288 node2288Labels = _
    exact sound2288 B hB hF
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h2735 : mixedVector B (Sum.inr 2735) = Sparse.eval nodeValue2735 (mixedVector B) := by
    change mixedMoment B node2735 node2735Labels = _
    exact sound2735 B hB hF
  have h2761 : mixedVector B (Sum.inr 2761) = Sparse.eval nodeValue2761 (mixedVector B) := by
    change mixedMoment B node2761 node2761Labels = _
    exact sound2761 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  simpa only [sourceForm1953, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1686, h1687, h1695, h1720, h1745, h1748, h1750, h2198, h2223, h2224, h2256, h2259, h2260, h2286, h2288, h2290, h2291, h2735, h2761, h2781, h2782, reducedSource1658] using sourceEq1953 B hB

theorem rowSound1658 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1658 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1658, numericCheck1658, reducedZero1658 B hB hF, mul_zero]

theorem reducedZero1659 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1659 (mixedVector B) = 0 := by
  have h953 : mixedVector B (Sum.inr 953) = Sparse.eval nodeValue953 (mixedVector B) := by
    change mixedMoment B node953 node953Labels = _
    exact sound953 B hB hF
  have h1831 : mixedVector B (Sum.inr 1831) = Sparse.eval nodeValue1831 (mixedVector B) := by
    change mixedMoment B node1831 node1831Labels = _
    exact sound1831 B hB hF
  have h1979 : mixedVector B (Sum.inr 1979) = Sparse.eval nodeValue1979 (mixedVector B) := by
    change mixedMoment B node1979 node1979Labels = _
    exact sound1979 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2116 : mixedVector B (Sum.inr 2116) = Sparse.eval nodeValue2116 (mixedVector B) := by
    change mixedMoment B node2116 node2116Labels = _
    exact sound2116 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1954, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h953, h1831, h1979, h2112, h2116, h4083, reducedSource1659] using sourceEq1954 B hB

theorem rowSound1659 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1659 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1659, numericCheck1659, reducedZero1659 B hB hF, mul_zero]

theorem reducedZero1660 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1660 (mixedVector B) = 0 := by
  have h1336 : mixedVector B (Sum.inr 1336) = Sparse.eval nodeValue1336 (mixedVector B) := by
    change mixedMoment B node1336 node1336Labels = _
    exact sound1336 B hB hF
  have h1973 : mixedVector B (Sum.inr 1973) = Sparse.eval nodeValue1973 (mixedVector B) := by
    change mixedMoment B node1973 node1973Labels = _
    exact sound1973 B hB hF
  have h1979 : mixedVector B (Sum.inr 1979) = Sparse.eval nodeValue1979 (mixedVector B) := by
    change mixedMoment B node1979 node1979Labels = _
    exact sound1979 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2952 : mixedVector B (Sum.inr 2952) = Sparse.eval nodeValue2952 (mixedVector B) := by
    change mixedMoment B node2952 node2952Labels = _
    exact sound2952 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1955, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1336, h1973, h1979, h2025, h2112, h2952, h4083, reducedSource1660] using sourceEq1955 B hB

theorem rowSound1660 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1660 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1660, numericCheck1660, reducedZero1660 B hB hF, mul_zero]

theorem reducedZero1661 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1661 (mixedVector B) = 0 := by
  have h4486 : mixedVector B (Sum.inr 4486) = Sparse.eval nodeValue4486 (mixedVector B) := by
    change mixedMoment B node4486 node4486Labels = _
    exact sound4486 B hB hF
  have h4490 : mixedVector B (Sum.inr 4490) = Sparse.eval nodeValue4490 (mixedVector B) := by
    change mixedMoment B node4490 node4490Labels = _
    exact sound4490 B hB hF
  have h4492 : mixedVector B (Sum.inr 4492) = Sparse.eval nodeValue4492 (mixedVector B) := by
    change mixedMoment B node4492 node4492Labels = _
    exact sound4492 B hB hF
  have h4504 : mixedVector B (Sum.inr 4504) = Sparse.eval nodeValue4504 (mixedVector B) := by
    change mixedMoment B node4504 node4504Labels = _
    exact sound4504 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4808 : mixedVector B (Sum.inr 4808) = Sparse.eval nodeValue4808 (mixedVector B) := by
    change mixedMoment B node4808 node4808Labels = _
    exact sound4808 B hB hF
  have h4824 : mixedVector B (Sum.inr 4824) = Sparse.eval nodeValue4824 (mixedVector B) := by
    change mixedMoment B node4824 node4824Labels = _
    exact sound4824 B hB hF
  have h4827 : mixedVector B (Sum.inr 4827) = Sparse.eval nodeValue4827 (mixedVector B) := by
    change mixedMoment B node4827 node4827Labels = _
    exact sound4827 B hB hF
  have h4829 : mixedVector B (Sum.inr 4829) = Sparse.eval nodeValue4829 (mixedVector B) := by
    change mixedMoment B node4829 node4829Labels = _
    exact sound4829 B hB hF
  have h4840 : mixedVector B (Sum.inr 4840) = Sparse.eval nodeValue4840 (mixedVector B) := by
    change mixedMoment B node4840 node4840Labels = _
    exact sound4840 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h4844 : mixedVector B (Sum.inr 4844) = Sparse.eval nodeValue4844 (mixedVector B) := by
    change mixedMoment B node4844 node4844Labels = _
    exact sound4844 B hB hF
  have h4853 : mixedVector B (Sum.inr 4853) = Sparse.eval nodeValue4853 (mixedVector B) := by
    change mixedMoment B node4853 node4853Labels = _
    exact sound4853 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4872 : mixedVector B (Sum.inr 4872) = Sparse.eval nodeValue4872 (mixedVector B) := by
    change mixedMoment B node4872 node4872Labels = _
    exact sound4872 B hB hF
  have h4881 : mixedVector B (Sum.inr 4881) = Sparse.eval nodeValue4881 (mixedVector B) := by
    change mixedMoment B node4881 node4881Labels = _
    exact sound4881 B hB hF
  have h5109 : mixedVector B (Sum.inr 5109) = Sparse.eval nodeValue5109 (mixedVector B) := by
    change mixedMoment B node5109 node5109Labels = _
    exact sound5109 B hB hF
  have h5139 : mixedVector B (Sum.inr 5139) = Sparse.eval nodeValue5139 (mixedVector B) := by
    change mixedMoment B node5139 node5139Labels = _
    exact sound5139 B hB hF
  have h5174 : mixedVector B (Sum.inr 5174) = Sparse.eval nodeValue5174 (mixedVector B) := by
    change mixedMoment B node5174 node5174Labels = _
    exact sound5174_e B hB hF
  simpa only [sourceForm1956, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4486, h4490, h4492, h4504, h4807, h4808, h4824, h4827, h4829, h4840, h4841, h4843, h4844, h4853, h4868, h4872, h4881, h5109, h5139, h5174, reducedSource1661] using sourceEq1956 B hB

theorem rowSound1661 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1661 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1661, numericCheck1661, reducedZero1661 B hB hF, mul_zero]

theorem reducedZero1663 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1663 (mixedVector B) = 0 := by
  have h1159 : mixedVector B (Sum.inr 1159) = Sparse.eval nodeValue1159 (mixedVector B) := by
    change mixedMoment B node1159 node1159Labels = _
    exact sound1159 B hB hF
  have h2355 : mixedVector B (Sum.inr 2355) = Sparse.eval nodeValue2355 (mixedVector B) := by
    change mixedMoment B node2355 node2355Labels = _
    exact sound2355 B hB hF
  have h2436 : mixedVector B (Sum.inr 2436) = Sparse.eval nodeValue2436 (mixedVector B) := by
    change mixedMoment B node2436 node2436Labels = _
    exact sound2436 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h2569 : mixedVector B (Sum.inr 2569) = Sparse.eval nodeValue2569 (mixedVector B) := by
    change mixedMoment B node2569 node2569Labels = _
    exact sound2569 B hB hF
  have h2590 : mixedVector B (Sum.inr 2590) = Sparse.eval nodeValue2590 (mixedVector B) := by
    change mixedMoment B node2590 node2590Labels = _
    exact sound2590 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1958, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1159, h2355, h2436, h2482, h2569, h2590, h4092, reducedSource1663] using sourceEq1958 B hB

theorem rowSound1663 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1663 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1663, numericCheck1663, reducedZero1663 B hB hF, mul_zero]

theorem sourceRowsAt1648 : MixedData.sourceRows (1648 : Fin 2425) =
    MixedData.row1648 := by decide +kernel

theorem sourceRowsAt1649 : MixedData.sourceRows (1649 : Fin 2425) =
    MixedData.row1649 := by decide +kernel

theorem sourceRowsAt1650 : MixedData.sourceRows (1650 : Fin 2425) =
    MixedData.row1650 := by decide +kernel

theorem sourceRowsAt1651 : MixedData.sourceRows (1651 : Fin 2425) =
    MixedData.row1651 := by decide +kernel

theorem sourceRowsAt1652 : MixedData.sourceRows (1652 : Fin 2425) =
    MixedData.row1652 := by decide +kernel

theorem sourceRowsAt1653 : MixedData.sourceRows (1653 : Fin 2425) =
    MixedData.row1653 := by decide +kernel

theorem sourceRowsAt1654 : MixedData.sourceRows (1654 : Fin 2425) =
    MixedData.row1654 := by decide +kernel

theorem sourceRowsAt1655 : MixedData.sourceRows (1655 : Fin 2425) =
    MixedData.row1655 := by decide +kernel

theorem sourceRowsAt1656 : MixedData.sourceRows (1656 : Fin 2425) =
    MixedData.row1656 := by decide +kernel

theorem sourceRowsAt1657 : MixedData.sourceRows (1657 : Fin 2425) =
    MixedData.row1657 := by decide +kernel

theorem sourceRowsAt1658 : MixedData.sourceRows (1658 : Fin 2425) =
    MixedData.row1658 := by decide +kernel

theorem sourceRowsAt1659 : MixedData.sourceRows (1659 : Fin 2425) =
    MixedData.row1659 := by decide +kernel

theorem sourceRowsAt1660 : MixedData.sourceRows (1660 : Fin 2425) =
    MixedData.row1660 := by decide +kernel

theorem sourceRowsAt1661 : MixedData.sourceRows (1661 : Fin 2425) =
    MixedData.row1661 := by decide +kernel

theorem sourceRowsAt1662 : MixedData.sourceRows (1662 : Fin 2425) =
    MixedData.row1662 := by decide +kernel

theorem sourceRowsAt1663 : MixedData.sourceRows (1663 : Fin 2425) =
    MixedData.row1663 := by decide +kernel

theorem chunkSound103_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 103) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1648 ∨ k.val = 1649 ∨ k.val = 1650 ∨ k.val = 1651 ∨ k.val = 1652 ∨ k.val = 1653 ∨ k.val = 1654 ∨ k.val = 1655 ∨ k.val = 1656 ∨ k.val = 1657 ∨ k.val = 1658 ∨ k.val = 1659 ∨ k.val = 1660 ∨ k.val = 1661 ∨ k.val = 1662 ∨ k.val = 1663 := by omega
  rcases heq with h1648 | h1649 | h1650 | h1651 | h1652 | h1653 | h1654 | h1655 | h1656 | h1657 | h1658 | h1659 | h1660 | h1661 | h1662 | h1663
  · have he : k = (1648 : Fin 2425) := Fin.ext h1648
    subst k
    rw [sourceRowsAt1648]
    exact rowSound1648_e B hB hF
  · have he : k = (1649 : Fin 2425) := Fin.ext h1649
    subst k
    rw [sourceRowsAt1649]
    exact rowSound1649_e B hB hF
  · have he : k = (1650 : Fin 2425) := Fin.ext h1650
    subst k
    rw [sourceRowsAt1650]
    exact rowSound1650_e B hB hF
  · have he : k = (1651 : Fin 2425) := Fin.ext h1651
    subst k
    rw [sourceRowsAt1651]
    exact rowSound1651_e B hB hF
  · have he : k = (1652 : Fin 2425) := Fin.ext h1652
    subst k
    rw [sourceRowsAt1652]
    exact rowSound1652_e B hB hF
  · have he : k = (1653 : Fin 2425) := Fin.ext h1653
    subst k
    rw [sourceRowsAt1653]
    exact rowSound1653_e B hB hF
  · have he : k = (1654 : Fin 2425) := Fin.ext h1654
    subst k
    rw [sourceRowsAt1654]
    exact rowSound1654_e B hB hF
  · have he : k = (1655 : Fin 2425) := Fin.ext h1655
    subst k
    rw [sourceRowsAt1655]
    exact rowSound1655_e B hB hF
  · have he : k = (1656 : Fin 2425) := Fin.ext h1656
    subst k
    rw [sourceRowsAt1656]
    exact rowSound1656_e B hB hF
  · have he : k = (1657 : Fin 2425) := Fin.ext h1657
    subst k
    rw [sourceRowsAt1657]
    exact rowSound1657 B hB hF
  · have he : k = (1658 : Fin 2425) := Fin.ext h1658
    subst k
    rw [sourceRowsAt1658]
    exact rowSound1658 B hB hF
  · have he : k = (1659 : Fin 2425) := Fin.ext h1659
    subst k
    rw [sourceRowsAt1659]
    exact rowSound1659 B hB hF
  · have he : k = (1660 : Fin 2425) := Fin.ext h1660
    subst k
    rw [sourceRowsAt1660]
    exact rowSound1660 B hB hF
  · have he : k = (1661 : Fin 2425) := Fin.ext h1661
    subst k
    rw [sourceRowsAt1661]
    exact rowSound1661 B hB hF
  · have he : k = (1662 : Fin 2425) := Fin.ext h1662
    subst k
    rw [sourceRowsAt1662]
    exact rowSound1662_e B hB hF
  · have he : k = (1663 : Fin 2425) := Fin.ext h1663
    subst k
    rw [sourceRowsAt1663]
    exact rowSound1663 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103_e_oai
