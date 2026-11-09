-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:15:44.675018+00:00
-- url     : https://prove2.me/submissions/f9558ebe-e4e7-4b9b-8234-1a61725448b3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E127
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5292_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound656_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound657_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound658_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound659_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound663_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound664_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound666_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound667_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound668_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12855 raw12855Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw12855 raw12855Labels = mixedMoment B raw12855step0 raw12855step0Labels := by
      have hz : ∀ j, raw12855 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12855step0 = (fun i j => raw12855 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12855step0 raw12855; decide +kernel
      have hl : raw12855step0Labels = raw12855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12855 raw12855Labels permutation265 hz
    mixedMoment B raw12855step0 raw12855step0Labels = mixedMoment B raw12855step1 raw12855step1Labels := by
      have ha : raw12855step1 = (fun i j => raw12855step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12855step1 raw12855step0; decide +kernel
      have hl : raw12855step1Labels = raw12855step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12855step0 raw12855step0Labels permutation37 permutation2
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical12856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12856 raw12856Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw12856 raw12856Labels = mixedMoment B raw12856step0 raw12856step0Labels := by
      have ha : raw12856step0 = (fun i j => raw12856 (permutation428 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12856step0 raw12856; decide +kernel
      have hl : raw12856step0Labels = raw12856Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12856 raw12856Labels permutation428 permutation4
    _ = mixedMoment B node3848 node3848Labels := by rfl

theorem canonical12857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12857 raw12857Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw12857 raw12857Labels = mixedMoment B raw12857step0 raw12857step0Labels := by
      have hz : ∀ j, raw12857 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12857step0 = (fun i j => raw12857 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12857step0 raw12857; decide +kernel
      have hl : raw12857step0Labels = raw12857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12857 raw12857Labels permutation265 hz
    mixedMoment B raw12857step0 raw12857step0Labels = mixedMoment B raw12857step1 raw12857step1Labels := by
      have ha : raw12857step1 = (fun i j => raw12857step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12857step1 raw12857step0; decide +kernel
      have hl : raw12857step1Labels = raw12857step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12857step0 raw12857step0Labels permutation37 permutation2
    _ = mixedMoment B node3961 node3961Labels := by rfl

theorem canonical12858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12858 raw12858Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw12858 raw12858Labels = mixedMoment B raw12858step0 raw12858step0Labels := by
      have hz : ∀ j, raw12858 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12858step0 = (fun i j => raw12858 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12858step0 raw12858; decide +kernel
      have hl : raw12858step0Labels = raw12858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12858 raw12858Labels permutation265 hz
    mixedMoment B raw12858step0 raw12858step0Labels = mixedMoment B raw12858step1 raw12858step1Labels := by
      have ha : raw12858step1 = (fun i j => raw12858step0 (permutation78 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12858step1 raw12858step0; decide +kernel
      have hl : raw12858step1Labels = raw12858step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12858step0 raw12858step0Labels permutation78 permutation4
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical12859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12859 raw12859Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw12859 raw12859Labels = mixedMoment B raw12859step0 raw12859step0Labels := by
      have hz : ∀ j, raw12859 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12859step0 = (fun i j => raw12859 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12859step0 raw12859; decide +kernel
      have hl : raw12859step0Labels = raw12859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12859 raw12859Labels permutation265 hz
    mixedMoment B raw12859step0 raw12859step0Labels = mixedMoment B raw12859step1 raw12859step1Labels := by
      have ha : raw12859step1 = (fun i j => raw12859step0 (permutation75 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12859step1 raw12859step0; decide +kernel
      have hl : raw12859step1Labels = raw12859step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12859step0 raw12859step0Labels permutation75 permutation4
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical12860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12860 raw12860Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw12860 raw12860Labels = mixedMoment B raw12860step0 raw12860step0Labels := by
      have hz : ∀ j, raw12860 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12860step0 = (fun i j => raw12860 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12860step0 raw12860; decide +kernel
      have hl : raw12860step0Labels = raw12860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12860 raw12860Labels permutation590 hz
    mixedMoment B raw12860step0 raw12860step0Labels = mixedMoment B raw12860step1 raw12860step1Labels := by
      have hz : ∀ j, raw12860step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12860step1 = (fun i j => raw12860step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12860step1 raw12860step0; decide +kernel
      have hl : raw12860step1Labels = raw12860step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12860step0 raw12860step0Labels permutation56 hz
    mixedMoment B raw12860step1 raw12860step1Labels = mixedMoment B raw12860step2 raw12860step2Labels := by
      have ha : raw12860step2 = (fun i j => raw12860step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12860step2 raw12860step1; decide +kernel
      have hl : raw12860step2Labels = raw12860step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12860step1 raw12860step1Labels permutation18 permutation4
    _ = mixedMoment B node3913 node3913Labels := by rfl

theorem canonical12861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12861 raw12861Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw12861 raw12861Labels = mixedMoment B raw12861step0 raw12861step0Labels := by
      have hz : ∀ j, raw12861 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12861step0 = (fun i j => raw12861 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12861step0 raw12861; decide +kernel
      have hl : raw12861step0Labels = raw12861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12861 raw12861Labels permutation590 hz
    mixedMoment B raw12861step0 raw12861step0Labels = mixedMoment B raw12861step1 raw12861step1Labels := by
      have hz : ∀ j, raw12861step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12861step1 = (fun i j => raw12861step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12861step1 raw12861step0; decide +kernel
      have hl : raw12861step1Labels = raw12861step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12861step0 raw12861step0Labels permutation56 hz
    mixedMoment B raw12861step1 raw12861step1Labels = mixedMoment B raw12861step2 raw12861step2Labels := by
      have ha : raw12861step2 = (fun i j => raw12861step1 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw12861step2 raw12861step1; decide +kernel
      have hl : raw12861step2Labels = raw12861step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12861step1 raw12861step1Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical12862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12862 raw12862Labels = mixedMoment B node1364 node1364Labels := by
  calc
    mixedMoment B raw12862 raw12862Labels = mixedMoment B raw12862step0 raw12862step0Labels := by
      have ha : raw12862step0 = (fun i j => raw12862 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12862step0 raw12862; decide +kernel
      have hl : raw12862step0Labels = raw12862Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12862 raw12862Labels permutation181 permutation2
    _ = mixedMoment B node1364 node1364Labels := by rfl

theorem canonical12863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12863 raw12863Labels = mixedMoment B node1433 node1433Labels := by
  calc
    mixedMoment B raw12863 raw12863Labels = mixedMoment B raw12863step0 raw12863step0Labels := by
      have hz : ∀ j, raw12863 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12863step0 = (fun i j => raw12863 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12863step0 raw12863; decide +kernel
      have hl : raw12863step0Labels = raw12863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12863 raw12863Labels permutation265 hz
    mixedMoment B raw12863step0 raw12863step0Labels = mixedMoment B raw12863step1 raw12863step1Labels := by
      have ha : raw12863step1 = (fun i j => raw12863step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12863step1 raw12863step0; decide +kernel
      have hl : raw12863step1Labels = raw12863step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12863step0 raw12863step0Labels permutation37 permutation2
    _ = mixedMoment B node1433 node1433Labels := by rfl

theorem canonical12864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12864 raw12864Labels = mixedMoment B node1367 node1367Labels := by
  calc
    mixedMoment B raw12864 raw12864Labels = mixedMoment B raw12864step0 raw12864step0Labels := by
      have hz : ∀ j, raw12864 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12864step0 = (fun i j => raw12864 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12864step0 raw12864; decide +kernel
      have hl : raw12864step0Labels = raw12864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12864 raw12864Labels permutation265 hz
    mixedMoment B raw12864step0 raw12864step0Labels = mixedMoment B raw12864step1 raw12864step1Labels := by
      have ha : raw12864step1 = (fun i j => raw12864step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12864step1 raw12864step0; decide +kernel
      have hl : raw12864step1Labels = raw12864step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12864step0 raw12864step0Labels permutation37 permutation2
    _ = mixedMoment B node1367 node1367Labels := by rfl

theorem canonical12865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12865 raw12865Labels = mixedMoment B node1368 node1368Labels := by
  calc
    mixedMoment B raw12865 raw12865Labels = mixedMoment B raw12865step0 raw12865step0Labels := by
      have hz : ∀ j, raw12865 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12865step0 = (fun i j => raw12865 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12865step0 raw12865; decide +kernel
      have hl : raw12865step0Labels = raw12865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12865 raw12865Labels permutation265 hz
    mixedMoment B raw12865step0 raw12865step0Labels = mixedMoment B raw12865step1 raw12865step1Labels := by
      have ha : raw12865step1 = (fun i j => raw12865step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12865step1 raw12865step0; decide +kernel
      have hl : raw12865step1Labels = raw12865step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12865step0 raw12865step0Labels permutation36 permutation2
    _ = mixedMoment B node1368 node1368Labels := by rfl

theorem canonical12866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12866 raw12866Labels = mixedMoment B node1371 node1371Labels := by
  calc
    mixedMoment B raw12866 raw12866Labels = mixedMoment B raw12866step0 raw12866step0Labels := by
      have hz : ∀ j, raw12866 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12866step0 = (fun i j => raw12866 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12866step0 raw12866; decide +kernel
      have hl : raw12866step0Labels = raw12866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12866 raw12866Labels permutation265 hz
    mixedMoment B raw12866step0 raw12866step0Labels = mixedMoment B raw12866step1 raw12866step1Labels := by
      have ha : raw12866step1 = (fun i j => raw12866step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12866step1 raw12866step0; decide +kernel
      have hl : raw12866step1Labels = raw12866step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12866step0 raw12866step0Labels permutation34 permutation2
    _ = mixedMoment B node1371 node1371Labels := by rfl

theorem canonical12867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12867 raw12867Labels = mixedMoment B node2878 node2878Labels := by
  calc
    mixedMoment B raw12867 raw12867Labels = mixedMoment B raw12867step0 raw12867step0Labels := by
      have ha : raw12867step0 = (fun i j => raw12867 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12867step0 raw12867; decide +kernel
      have hl : raw12867step0Labels = raw12867Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12867 raw12867Labels permutation181 permutation2
    _ = mixedMoment B node2878 node2878Labels := by rfl

theorem canonical12868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12868 raw12868Labels = mixedMoment B node3043 node3043Labels := by
  calc
    mixedMoment B raw12868 raw12868Labels = mixedMoment B raw12868step0 raw12868step0Labels := by
      have ha : raw12868step0 = (fun i j => raw12868 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12868step0 raw12868; decide +kernel
      have hl : raw12868step0Labels = raw12868Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12868 raw12868Labels permutation183 permutation2
    _ = mixedMoment B node3043 node3043Labels := by rfl

theorem canonical12869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12869 raw12869Labels = mixedMoment B node3036 node3036Labels := by
  calc
    mixedMoment B raw12869 raw12869Labels = mixedMoment B raw12869step0 raw12869step0Labels := by
      have ha : raw12869step0 = (fun i j => raw12869 (permutation189 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12869step0 raw12869; decide +kernel
      have hl : raw12869step0Labels = raw12869Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12869 raw12869Labels permutation189 permutation2
    _ = mixedMoment B node3036 node3036Labels := by rfl

theorem canonical12870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12870 raw12870Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw12870 raw12870Labels = mixedMoment B raw12870step0 raw12870step0Labels := by
      have hz : ∀ j, raw12870 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12870step0 = (fun i j => raw12870 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12870step0 raw12870; decide +kernel
      have hl : raw12870step0Labels = raw12870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12870 raw12870Labels permutation590 hz
    mixedMoment B raw12870step0 raw12870step0Labels = mixedMoment B raw12870step1 raw12870step1Labels := by
      have ha : raw12870step1 = (fun i j => raw12870step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12870step1 raw12870step0; decide +kernel
      have hl : raw12870step1Labels = raw12870step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12870step0 raw12870step0Labels permutation39 permutation2
    _ = mixedMoment B node3051 node3051Labels := by rfl

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

theorem canonical1812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1812 raw1812Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw1812 raw1812Labels = mixedMoment B raw1812step0 raw1812step0Labels := by
      have ha : raw1812step0 = (fun i j => raw1812 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1812step0 raw1812; decide +kernel
      have hl : raw1812step0Labels = raw1812Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1812 raw1812Labels permutation152 permutation4
    mixedMoment B raw1812step0 raw1812step0Labels = mixedMoment B raw1812step1 raw1812step1Labels := by
      have ha : raw1812step1 = raw1812step0 := by apply Matrix.ext; unfold raw1812step1 raw1812step0; decide +kernel
      have hl : raw1812step0Labels = labelEmbedding7 ∘ raw1812step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1812step0 raw1812step0Labels raw1812step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

theorem canonical1813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1813 raw1813Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw1813 raw1813Labels = mixedMoment B raw1813step0 raw1813step0Labels := by
      have ha : raw1813step0 = (fun i j => raw1813 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1813step0 raw1813; decide +kernel
      have hl : raw1813step0Labels = raw1813Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1813 raw1813Labels permutation152 permutation4
    _ = mixedMoment B node2243 node2243Labels := by rfl

theorem canonical1814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1814 raw1814Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw1814 raw1814Labels = mixedMoment B raw1814step0 raw1814step0Labels := by
      have ha : raw1814step0 = (fun i j => raw1814 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1814step0 raw1814; decide +kernel
      have hl : raw1814step0Labels = raw1814Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1814 raw1814Labels permutation212 permutation6
    mixedMoment B raw1814step0 raw1814step0Labels = mixedMoment B raw1814step1 raw1814step1Labels := by
      have ha : raw1814step1 = -raw1814step0 := by apply Matrix.ext; change ∀ i j, raw1814step1 i j = -(raw1814step0 i j); unfold raw1814step1 raw1814step0; decide +kernel
      have hl : raw1814step1Labels = raw1814step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1814step1 raw1814step1Labels = mixedMoment B raw1814step2 raw1814step2Labels := by
      have ha : raw1814step2 = raw1814step1 := by apply Matrix.ext; unfold raw1814step2 raw1814step1; decide +kernel
      have hl : raw1814step1Labels = labelEmbedding1 ∘ raw1814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1814step1 raw1814step1Labels raw1814step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

theorem canonical1815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1815 raw1815Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw1815 raw1815Labels = mixedMoment B raw1815step0 raw1815step0Labels := by
      have ha : raw1815step0 = (fun i j => raw1815 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1815step0 raw1815; decide +kernel
      have hl : raw1815step0Labels = raw1815Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1815 raw1815Labels permutation32 permutation4
    mixedMoment B raw1815step0 raw1815step0Labels = mixedMoment B raw1815step1 raw1815step1Labels := by
      have ha : raw1815step1 = raw1815step0 := by apply Matrix.ext; unfold raw1815step1 raw1815step0; decide +kernel
      have hl : raw1815step0Labels = labelEmbedding7 ∘ raw1815step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1815step0 raw1815step0Labels raw1815step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical1816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1816 raw1816Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw1816 raw1816Labels = mixedMoment B raw1816step0 raw1816step0Labels := by
      have ha : raw1816step0 = (fun i j => raw1816 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1816step0 raw1816; decide +kernel
      have hl : raw1816step0Labels = raw1816Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1816 raw1816Labels permutation32 permutation4
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical1817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1817 raw1817Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw1817 raw1817Labels = mixedMoment B raw1817step0 raw1817step0Labels := by
      have ha : raw1817step0 = (fun i j => raw1817 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1817step0 raw1817; decide +kernel
      have hl : raw1817step0Labels = raw1817Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1817 raw1817Labels permutation44 permutation6
    mixedMoment B raw1817step0 raw1817step0Labels = mixedMoment B raw1817step1 raw1817step1Labels := by
      have ha : raw1817step1 = -raw1817step0 := by apply Matrix.ext; change ∀ i j, raw1817step1 i j = -(raw1817step0 i j); unfold raw1817step1 raw1817step0; decide +kernel
      have hl : raw1817step1Labels = raw1817step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1817step1 raw1817step1Labels = mixedMoment B raw1817step2 raw1817step2Labels := by
      have ha : raw1817step2 = raw1817step1 := by apply Matrix.ext; unfold raw1817step2 raw1817step1; decide +kernel
      have hl : raw1817step1Labels = labelEmbedding1 ∘ raw1817step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1817step1 raw1817step1Labels raw1817step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

theorem canonical1818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1818 raw1818Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw1818 raw1818Labels = mixedMoment B raw1818step0 raw1818step0Labels := by
      have ha : raw1818step0 = (fun i j => raw1818 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1818step0 raw1818; decide +kernel
      have hl : raw1818step0Labels = raw1818Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1818 raw1818Labels permutation32 permutation4
    mixedMoment B raw1818step0 raw1818step0Labels = mixedMoment B raw1818step1 raw1818step1Labels := by
      have ha : raw1818step1 = raw1818step0 := by apply Matrix.ext; unfold raw1818step1 raw1818step0; decide +kernel
      have hl : raw1818step0Labels = labelEmbedding7 ∘ raw1818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1818step0 raw1818step0Labels raw1818step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical1819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1819 raw1819Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw1819 raw1819Labels = mixedMoment B raw1819step0 raw1819step0Labels := by
      have ha : raw1819step0 = (fun i j => raw1819 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1819step0 raw1819; decide +kernel
      have hl : raw1819step0Labels = raw1819Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1819 raw1819Labels permutation32 permutation4
    _ = mixedMoment B node2245 node2245Labels := by rfl

theorem canonical1820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1820 raw1820Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw1820 raw1820Labels = mixedMoment B raw1820step0 raw1820step0Labels := by
      have ha : raw1820step0 = (fun i j => raw1820 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1820step0 raw1820; decide +kernel
      have hl : raw1820step0Labels = raw1820Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1820 raw1820Labels permutation50 permutation6
    mixedMoment B raw1820step0 raw1820step0Labels = mixedMoment B raw1820step1 raw1820step1Labels := by
      have ha : raw1820step1 = -raw1820step0 := by apply Matrix.ext; change ∀ i j, raw1820step1 i j = -(raw1820step0 i j); unfold raw1820step1 raw1820step0; decide +kernel
      have hl : raw1820step1Labels = raw1820step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1820step1 raw1820step1Labels = mixedMoment B raw1820step2 raw1820step2Labels := by
      have ha : raw1820step2 = raw1820step1 := by apply Matrix.ext; unfold raw1820step2 raw1820step1; decide +kernel
      have hl : raw1820step1Labels = labelEmbedding1 ∘ raw1820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1820step1 raw1820step1Labels raw1820step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

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

theorem canonical2268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2268 raw2268Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw2268 raw2268Labels = mixedMoment B raw2268step0 raw2268step0Labels := by
      have ha : raw2268step0 = (fun i j => raw2268 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2268step0 raw2268; decide +kernel
      have hl : raw2268step0Labels = raw2268Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2268 raw2268Labels permutation152 permutation4
    mixedMoment B raw2268step0 raw2268step0Labels = mixedMoment B raw2268step1 raw2268step1Labels := by
      have ha : raw2268step1 = raw2268step0 := by apply Matrix.ext; unfold raw2268step1 raw2268step0; decide +kernel
      have hl : raw2268step0Labels = labelEmbedding7 ∘ raw2268step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2268step0 raw2268step0Labels raw2268step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical2269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2269 raw2269Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw2269 raw2269Labels = mixedMoment B raw2269step0 raw2269step0Labels := by
      have ha : raw2269step0 = (fun i j => raw2269 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2269step0 raw2269; decide +kernel
      have hl : raw2269step0Labels = raw2269Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2269 raw2269Labels permutation152 permutation4
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical2270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2270 raw2270Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw2270 raw2270Labels = mixedMoment B raw2270step0 raw2270step0Labels := by
      have ha : raw2270step0 = (fun i j => raw2270 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2270step0 raw2270; decide +kernel
      have hl : raw2270step0Labels = raw2270Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2270 raw2270Labels permutation158 permutation6
    mixedMoment B raw2270step0 raw2270step0Labels = mixedMoment B raw2270step1 raw2270step1Labels := by
      have ha : raw2270step1 = -raw2270step0 := by apply Matrix.ext; change ∀ i j, raw2270step1 i j = -(raw2270step0 i j); unfold raw2270step1 raw2270step0; decide +kernel
      have hl : raw2270step1Labels = raw2270step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2270step1 raw2270step1Labels = mixedMoment B raw2270step2 raw2270step2Labels := by
      have ha : raw2270step2 = raw2270step1 := by apply Matrix.ext; unfold raw2270step2 raw2270step1; decide +kernel
      have hl : raw2270step1Labels = labelEmbedding1 ∘ raw2270step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2270step1 raw2270step1Labels raw2270step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

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

theorem canonical2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2292 raw2292Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw2292 raw2292Labels = mixedMoment B raw2292step0 raw2292step0Labels := by
      have ha : raw2292step0 = (fun i j => raw2292 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2292step0 raw2292; decide +kernel
      have hl : raw2292step0Labels = raw2292Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2292 raw2292Labels permutation32 permutation4
    mixedMoment B raw2292step0 raw2292step0Labels = mixedMoment B raw2292step1 raw2292step1Labels := by
      have ha : raw2292step1 = raw2292step0 := by apply Matrix.ext; unfold raw2292step1 raw2292step0; decide +kernel
      have hl : raw2292step0Labels = labelEmbedding7 ∘ raw2292step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2292step0 raw2292step0Labels raw2292step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2293 raw2293Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw2293 raw2293Labels = mixedMoment B raw2293step0 raw2293step0Labels := by
      have ha : raw2293step0 = (fun i j => raw2293 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2293step0 raw2293; decide +kernel
      have hl : raw2293step0Labels = raw2293Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2293 raw2293Labels permutation32 permutation4
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2294 raw2294Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw2294 raw2294Labels = mixedMoment B raw2294step0 raw2294step0Labels := by
      have ha : raw2294step0 = (fun i j => raw2294 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2294step0 raw2294; decide +kernel
      have hl : raw2294step0Labels = raw2294Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2294 raw2294Labels permutation38 permutation6
    mixedMoment B raw2294step0 raw2294step0Labels = mixedMoment B raw2294step1 raw2294step1Labels := by
      have ha : raw2294step1 = -raw2294step0 := by apply Matrix.ext; change ∀ i j, raw2294step1 i j = -(raw2294step0 i j); unfold raw2294step1 raw2294step0; decide +kernel
      have hl : raw2294step1Labels = raw2294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2294step1 raw2294step1Labels = mixedMoment B raw2294step2 raw2294step2Labels := by
      have ha : raw2294step2 = raw2294step1 := by apply Matrix.ext; unfold raw2294step2 raw2294step1; decide +kernel
      have hl : raw2294step1Labels = labelEmbedding1 ∘ raw2294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2294step1 raw2294step1Labels raw2294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

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

theorem canonical2310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2310 raw2310Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw2310 raw2310Labels = mixedMoment B raw2310step0 raw2310step0Labels := by
      have ha : raw2310step0 = (fun i j => raw2310 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2310step0 raw2310; decide +kernel
      have hl : raw2310step0Labels = raw2310Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2310 raw2310Labels permutation32 permutation5
    mixedMoment B raw2310step0 raw2310step0Labels = mixedMoment B raw2310step1 raw2310step1Labels := by
      have ha : raw2310step1 = raw2310step0 := by apply Matrix.ext; unfold raw2310step1 raw2310step0; decide +kernel
      have hl : raw2310step0Labels = labelEmbedding8 ∘ raw2310step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2310step0 raw2310step0Labels raw2310step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical2311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2311 raw2311Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw2311 raw2311Labels = mixedMoment B raw2311step0 raw2311step0Labels := by
      have ha : raw2311step0 = (fun i j => raw2311 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2311step0 raw2311; decide +kernel
      have hl : raw2311step0Labels = raw2311Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2311 raw2311Labels permutation32 permutation4
    _ = mixedMoment B node3053 node3053Labels := by rfl

theorem canonical2312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2312 raw2312Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw2312 raw2312Labels = mixedMoment B raw2312step0 raw2312step0Labels := by
      have ha : raw2312step0 = (fun i j => raw2312 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2312step0 raw2312; decide +kernel
      have hl : raw2312step0Labels = raw2312Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2312 raw2312Labels permutation41 permutation3
    mixedMoment B raw2312step0 raw2312step0Labels = mixedMoment B raw2312step1 raw2312step1Labels := by
      have ha : raw2312step1 = -raw2312step0 := by apply Matrix.ext; change ∀ i j, raw2312step1 i j = -(raw2312step0 i j); unfold raw2312step1 raw2312step0; decide +kernel
      have hl : raw2312step1Labels = raw2312step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2312step1 raw2312step1Labels = mixedMoment B raw2312step2 raw2312step2Labels := by
      have ha : raw2312step2 = raw2312step1 := by apply Matrix.ext; unfold raw2312step2 raw2312step1; decide +kernel
      have hl : raw2312step1Labels = labelEmbedding1 ∘ raw2312step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2312step1 raw2312step1Labels raw2312step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3619 node3619Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11664 raw11664Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw11664 raw11664Labels = mixedMoment B raw11664step0 raw11664step0Labels := by
      have ha : raw11664step0 = (fun i j => raw11664 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11664step0 raw11664; decide +kernel
      have hl : raw11664step0Labels = raw11664Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11664 raw11664Labels permutation180 permutation7
    mixedMoment B raw11664step0 raw11664step0Labels = mixedMoment B raw11664step1 raw11664step1Labels := by
      have ha : raw11664step1 = raw11664step0 := by apply Matrix.ext; unfold raw11664step1 raw11664step0; decide +kernel
      have hl : raw11664step0Labels = labelEmbedding10 ∘ raw11664step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11664step0 raw11664step0Labels raw11664step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical11665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11665 raw11665Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11665 raw11665Labels = mixedMoment B raw11665step0 raw11665step0Labels := by
      have hz : ∀ j, raw11665 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11665step0 = (fun i j => raw11665 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11665step0 raw11665; decide +kernel
      have hl : raw11665step0Labels = raw11665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11665 raw11665Labels permutation265 hz
    mixedMoment B raw11665step0 raw11665step0Labels = mixedMoment B raw11665step1 raw11665step1Labels := by
      have ha : raw11665step1 = (fun i j => raw11665step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11665step1 raw11665step0; decide +kernel
      have hl : raw11665step1Labels = raw11665step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11665step0 raw11665step0Labels permutation40 permutation4
    mixedMoment B raw11665step1 raw11665step1Labels = mixedMoment B raw11665step2 raw11665step2Labels := by
      have ha : raw11665step2 = -raw11665step1 := by apply Matrix.ext; change ∀ i j, raw11665step2 i j = -(raw11665step1 i j); unfold raw11665step2 raw11665step1; decide +kernel
      have hl : raw11665step2Labels = raw11665step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11665step2 raw11665step2Labels = mixedMoment B raw11665step3 raw11665step3Labels := by
      have ha : raw11665step3 = raw11665step2 := by apply Matrix.ext; unfold raw11665step3 raw11665step2; decide +kernel
      have hl : raw11665step2Labels = labelEmbedding7 ∘ raw11665step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11665step2 raw11665step2Labels raw11665step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical11666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11666 raw11666Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw11666 raw11666Labels = mixedMoment B raw11666step0 raw11666step0Labels := by
      have hz : ∀ j, raw11666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11666step0 = (fun i j => raw11666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11666step0 raw11666; decide +kernel
      have hl : raw11666step0Labels = raw11666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11666 raw11666Labels permutation346 hz
    mixedMoment B raw11666step0 raw11666step0Labels = mixedMoment B raw11666step1 raw11666step1Labels := by
      have hz : ∀ j, raw11666step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11666step1 = (fun i j => raw11666step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11666step1 raw11666step0; decide +kernel
      have hl : raw11666step1Labels = raw11666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11666step0 raw11666step0Labels permutation56 hz
    mixedMoment B raw11666step1 raw11666step1Labels = mixedMoment B raw11666step2 raw11666step2Labels := by
      have ha : raw11666step2 = (fun i j => raw11666step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11666step2 raw11666step1; decide +kernel
      have hl : raw11666step2Labels = raw11666step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11666step1 raw11666step1Labels permutation8 permutation6
    mixedMoment B raw11666step2 raw11666step2Labels = mixedMoment B raw11666step3 raw11666step3Labels := by
      have ha : raw11666step3 = raw11666step2 := by apply Matrix.ext; unfold raw11666step3 raw11666step2; decide +kernel
      have hl : raw11666step2Labels = labelEmbedding9 ∘ raw11666step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11666step2 raw11666step2Labels raw11666step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

theorem canonical11667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11667 raw11667Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw11667 raw11667Labels = mixedMoment B raw11667step0 raw11667step0Labels := by
      have hz : ∀ j, raw11667 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11667step0 = (fun i j => raw11667 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11667step0 raw11667; decide +kernel
      have hl : raw11667step0Labels = raw11667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11667 raw11667Labels permutation265 hz
    mixedMoment B raw11667step0 raw11667step0Labels = mixedMoment B raw11667step1 raw11667step1Labels := by
      have ha : raw11667step1 = (fun i j => raw11667step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11667step1 raw11667step0; decide +kernel
      have hl : raw11667step1Labels = raw11667step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11667step0 raw11667step0Labels permutation32 permutation6
    mixedMoment B raw11667step1 raw11667step1Labels = mixedMoment B raw11667step2 raw11667step2Labels := by
      have ha : raw11667step2 = raw11667step1 := by apply Matrix.ext; unfold raw11667step2 raw11667step1; decide +kernel
      have hl : raw11667step1Labels = labelEmbedding9 ∘ raw11667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11667step1 raw11667step1Labels raw11667step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical11668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11668 raw11668Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw11668 raw11668Labels = mixedMoment B raw11668step0 raw11668step0Labels := by
      have hz : ∀ j, raw11668 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11668step0 = (fun i j => raw11668 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11668step0 raw11668; decide +kernel
      have hl : raw11668step0Labels = raw11668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11668 raw11668Labels permutation265 hz
    mixedMoment B raw11668step0 raw11668step0Labels = mixedMoment B raw11668step1 raw11668step1Labels := by
      have ha : raw11668step1 = (fun i j => raw11668step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11668step1 raw11668step0; decide +kernel
      have hl : raw11668step1Labels = raw11668step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11668step0 raw11668step0Labels permutation34 permutation6
    mixedMoment B raw11668step1 raw11668step1Labels = mixedMoment B raw11668step2 raw11668step2Labels := by
      have ha : raw11668step2 = raw11668step1 := by apply Matrix.ext; unfold raw11668step2 raw11668step1; decide +kernel
      have hl : raw11668step1Labels = labelEmbedding9 ∘ raw11668step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11668step1 raw11668step1Labels raw11668step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical11674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11674 raw11674Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw11674 raw11674Labels = mixedMoment B raw11674step0 raw11674step0Labels := by
      have ha : raw11674step0 = (fun i j => raw11674 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11674step0 raw11674; decide +kernel
      have hl : raw11674step0Labels = raw11674Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11674 raw11674Labels permutation152 permutation6
    mixedMoment B raw11674step0 raw11674step0Labels = mixedMoment B raw11674step1 raw11674step1Labels := by
      have ha : raw11674step1 = raw11674step0 := by apply Matrix.ext; unfold raw11674step1 raw11674step0; decide +kernel
      have hl : raw11674step0Labels = labelEmbedding9 ∘ raw11674step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11674step0 raw11674step0Labels raw11674step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical11679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11679 raw11679Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw11679 raw11679Labels = mixedMoment B raw11679step0 raw11679step0Labels := by
      have ha : raw11679step0 = (fun i j => raw11679 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11679step0 raw11679; decide +kernel
      have hl : raw11679step0Labels = raw11679Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11679 raw11679Labels permutation154 permutation6
    mixedMoment B raw11679step0 raw11679step0Labels = mixedMoment B raw11679step1 raw11679step1Labels := by
      have ha : raw11679step1 = raw11679step0 := by apply Matrix.ext; unfold raw11679step1 raw11679step0; decide +kernel
      have hl : raw11679step0Labels = labelEmbedding9 ∘ raw11679step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11679step0 raw11679step0Labels raw11679step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical11684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11684 raw11684Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw11684 raw11684Labels = mixedMoment B raw11684step0 raw11684step0Labels := by
      have ha : raw11684step0 = (fun i j => raw11684 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11684step0 raw11684; decide +kernel
      have hl : raw11684step0Labels = raw11684Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11684 raw11684Labels permutation152 permutation6
    mixedMoment B raw11684step0 raw11684step0Labels = mixedMoment B raw11684step1 raw11684step1Labels := by
      have ha : raw11684step1 = raw11684step0 := by apply Matrix.ext; unfold raw11684step1 raw11684step0; decide +kernel
      have hl : raw11684step0Labels = labelEmbedding9 ∘ raw11684step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11684step0 raw11684step0Labels raw11684step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical11755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11755 raw11755Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw11755 raw11755Labels = mixedMoment B raw11755step0 raw11755step0Labels := by
      have ha : raw11755step0 = (fun i j => raw11755 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11755step0 raw11755; decide +kernel
      have hl : raw11755step0Labels = raw11755Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11755 raw11755Labels permutation194 permutation2
    mixedMoment B raw11755step0 raw11755step0Labels = mixedMoment B raw11755step1 raw11755step1Labels := by
      have ha : raw11755step1 = -raw11755step0 := by apply Matrix.ext; change ∀ i j, raw11755step1 i j = -(raw11755step0 i j); unfold raw11755step1 raw11755step0; decide +kernel
      have hl : raw11755step1Labels = raw11755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3532 node3532Labels := by rfl

theorem canonical11756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11756 raw11756Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11756 raw11756Labels = mixedMoment B raw11756step0 raw11756step0Labels := by
      have hz : ∀ j, raw11756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11756step0 = (fun i j => raw11756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11756step0 raw11756; decide +kernel
      have hl : raw11756step0Labels = raw11756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11756 raw11756Labels permutation346 hz
    mixedMoment B raw11756step0 raw11756step0Labels = mixedMoment B raw11756step1 raw11756step1Labels := by
      have hz : ∀ j, raw11756step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11756step1 = (fun i j => raw11756step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11756step1 raw11756step0; decide +kernel
      have hl : raw11756step1Labels = raw11756step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11756step0 raw11756step0Labels permutation56 hz
    mixedMoment B raw11756step1 raw11756step1Labels = mixedMoment B raw11756step2 raw11756step2Labels := by
      have ha : raw11756step2 = -raw11756step1 := by apply Matrix.ext; change ∀ i j, raw11756step2 i j = -(raw11756step1 i j); unfold raw11756step2 raw11756step1; decide +kernel
      have hl : raw11756step2Labels = raw11756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12002 raw12002Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw12002 raw12002Labels = mixedMoment B raw12002step0 raw12002step0Labels := by
      have hz : ∀ j, raw12002 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12002step0 = (fun i j => raw12002 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12002step0 raw12002; decide +kernel
      have hl : raw12002step0Labels = raw12002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12002 raw12002Labels permutation265 hz
    mixedMoment B raw12002step0 raw12002step0Labels = mixedMoment B raw12002step1 raw12002step1Labels := by
      have ha : raw12002step1 = (fun i j => raw12002step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12002step1 raw12002step0; decide +kernel
      have hl : raw12002step1Labels = raw12002step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12002step0 raw12002step0Labels permutation41 permutation4
    mixedMoment B raw12002step1 raw12002step1Labels = mixedMoment B raw12002step2 raw12002step2Labels := by
      have ha : raw12002step2 = -raw12002step1 := by apply Matrix.ext; change ∀ i j, raw12002step2 i j = -(raw12002step1 i j); unfold raw12002step2 raw12002step1; decide +kernel
      have hl : raw12002step2Labels = raw12002step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12002step2 raw12002step2Labels = mixedMoment B raw12002step3 raw12002step3Labels := by
      have ha : raw12002step3 = raw12002step2 := by apply Matrix.ext; unfold raw12002step3 raw12002step2; decide +kernel
      have hl : raw12002step2Labels = labelEmbedding7 ∘ raw12002step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12002step2 raw12002step2Labels raw12002step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical12003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12003 raw12003Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw12003 raw12003Labels = mixedMoment B raw12003step0 raw12003step0Labels := by
      have hz : ∀ j, raw12003 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12003step0 = (fun i j => raw12003 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12003step0 raw12003; decide +kernel
      have hl : raw12003step0Labels = raw12003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12003 raw12003Labels permutation265 hz
    mixedMoment B raw12003step0 raw12003step0Labels = mixedMoment B raw12003step1 raw12003step1Labels := by
      have ha : raw12003step1 = (fun i j => raw12003step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12003step1 raw12003step0; decide +kernel
      have hl : raw12003step1Labels = raw12003step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12003step0 raw12003step0Labels permutation32 permutation6
    mixedMoment B raw12003step1 raw12003step1Labels = mixedMoment B raw12003step2 raw12003step2Labels := by
      have ha : raw12003step2 = raw12003step1 := by apply Matrix.ext; unfold raw12003step2 raw12003step1; decide +kernel
      have hl : raw12003step1Labels = labelEmbedding9 ∘ raw12003step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12003step1 raw12003step1Labels raw12003step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical12004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12004 raw12004Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw12004 raw12004Labels = mixedMoment B raw12004step0 raw12004step0Labels := by
      have hz : ∀ j, raw12004 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12004step0 = (fun i j => raw12004 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12004step0 raw12004; decide +kernel
      have hl : raw12004step0Labels = raw12004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12004 raw12004Labels permutation265 hz
    mixedMoment B raw12004step0 raw12004step0Labels = mixedMoment B raw12004step1 raw12004step1Labels := by
      have ha : raw12004step1 = (fun i j => raw12004step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12004step1 raw12004step0; decide +kernel
      have hl : raw12004step1Labels = raw12004step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12004step0 raw12004step0Labels permutation34 permutation6
    mixedMoment B raw12004step1 raw12004step1Labels = mixedMoment B raw12004step2 raw12004step2Labels := by
      have ha : raw12004step2 = raw12004step1 := by apply Matrix.ext; unfold raw12004step2 raw12004step1; decide +kernel
      have hl : raw12004step1Labels = labelEmbedding9 ∘ raw12004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12004step1 raw12004step1Labels raw12004step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical12005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12005 raw12005Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw12005 raw12005Labels = mixedMoment B raw12005step0 raw12005step0Labels := by
      have hz : ∀ j, raw12005 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12005step0 = (fun i j => raw12005 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12005step0 raw12005; decide +kernel
      have hl : raw12005step0Labels = raw12005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12005 raw12005Labels permutation265 hz
    mixedMoment B raw12005step0 raw12005step0Labels = mixedMoment B raw12005step1 raw12005step1Labels := by
      have ha : raw12005step1 = (fun i j => raw12005step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12005step1 raw12005step0; decide +kernel
      have hl : raw12005step1Labels = raw12005step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12005step0 raw12005step0Labels permutation32 permutation6
    mixedMoment B raw12005step1 raw12005step1Labels = mixedMoment B raw12005step2 raw12005step2Labels := by
      have ha : raw12005step2 = raw12005step1 := by apply Matrix.ext; unfold raw12005step2 raw12005step1; decide +kernel
      have hl : raw12005step1Labels = labelEmbedding9 ∘ raw12005step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12005step1 raw12005step1Labels raw12005step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical12019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12019 raw12019Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw12019 raw12019Labels = mixedMoment B raw12019step0 raw12019step0Labels := by
      have ha : raw12019step0 = (fun i j => raw12019 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12019step0 raw12019; decide +kernel
      have hl : raw12019step0Labels = raw12019Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12019 raw12019Labels permutation152 permutation6
    mixedMoment B raw12019step0 raw12019step0Labels = mixedMoment B raw12019step1 raw12019step1Labels := by
      have ha : raw12019step1 = raw12019step0 := by apply Matrix.ext; unfold raw12019step1 raw12019step0; decide +kernel
      have hl : raw12019step0Labels = labelEmbedding9 ∘ raw12019step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12019step0 raw12019step0Labels raw12019step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12186 raw12186Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw12186 raw12186Labels = mixedMoment B raw12186step0 raw12186step0Labels := by
      have hz : ∀ j, raw12186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12186step0 = (fun i j => raw12186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12186step0 raw12186; decide +kernel
      have hl : raw12186step0Labels = raw12186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12186 raw12186Labels permutation346 hz
    mixedMoment B raw12186step0 raw12186step0Labels = mixedMoment B raw12186step1 raw12186step1Labels := by
      have hz : ∀ j, raw12186step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12186step1 = (fun i j => raw12186step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12186step1 raw12186step0; decide +kernel
      have hl : raw12186step1Labels = raw12186step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12186step0 raw12186step0Labels permutation56 hz
    mixedMoment B raw12186step1 raw12186step1Labels = mixedMoment B raw12186step2 raw12186step2Labels := by
      have ha : raw12186step2 = (fun i j => raw12186step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12186step2 raw12186step1; decide +kernel
      have hl : raw12186step2Labels = raw12186step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12186step1 raw12186step1Labels permutation12 permutation7
    mixedMoment B raw12186step2 raw12186step2Labels = mixedMoment B raw12186step3 raw12186step3Labels := by
      have ha : raw12186step3 = raw12186step2 := by apply Matrix.ext; unfold raw12186step3 raw12186step2; decide +kernel
      have hl : raw12186step2Labels = labelEmbedding10 ∘ raw12186step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12186step2 raw12186step2Labels raw12186step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5307 node5307Labels := by rfl

theorem canonical12191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12191 raw12191Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12191 raw12191Labels = mixedMoment B raw12191step0 raw12191step0Labels := by
      have hz : ∀ j, raw12191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12191step0 = (fun i j => raw12191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12191step0 raw12191; decide +kernel
      have hl : raw12191step0Labels = raw12191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12191 raw12191Labels permutation346 hz
    mixedMoment B raw12191step0 raw12191step0Labels = mixedMoment B raw12191step1 raw12191step1Labels := by
      have ha : raw12191step1 = (fun i j => raw12191step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12191step1 raw12191step0; decide +kernel
      have hl : raw12191step1Labels = raw12191step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12191step0 raw12191step0Labels permutation32 permutation6
    mixedMoment B raw12191step1 raw12191step1Labels = mixedMoment B raw12191step2 raw12191step2Labels := by
      have ha : raw12191step2 = raw12191step1 := by apply Matrix.ext; unfold raw12191step2 raw12191step1; decide +kernel
      have hl : raw12191step1Labels = labelEmbedding9 ∘ raw12191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12191step1 raw12191step1Labels raw12191step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical12195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12195 raw12195Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw12195 raw12195Labels = mixedMoment B raw12195step0 raw12195step0Labels := by
      have hz : ∀ j, raw12195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12195step0 = (fun i j => raw12195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12195step0 raw12195; decide +kernel
      have hl : raw12195step0Labels = raw12195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12195 raw12195Labels permutation346 hz
    mixedMoment B raw12195step0 raw12195step0Labels = mixedMoment B raw12195step1 raw12195step1Labels := by
      have hz : ∀ j, raw12195step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12195step1 = (fun i j => raw12195step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12195step1 raw12195step0; decide +kernel
      have hl : raw12195step1Labels = raw12195step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12195step0 raw12195step0Labels permutation56 hz
    mixedMoment B raw12195step1 raw12195step1Labels = mixedMoment B raw12195step2 raw12195step2Labels := by
      have ha : raw12195step2 = (fun i j => raw12195step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12195step2 raw12195step1; decide +kernel
      have hl : raw12195step2Labels = raw12195step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12195step1 raw12195step1Labels permutation10 permutation6
    mixedMoment B raw12195step2 raw12195step2Labels = mixedMoment B raw12195step3 raw12195step3Labels := by
      have ha : raw12195step3 = raw12195step2 := by apply Matrix.ext; unfold raw12195step3 raw12195step2; decide +kernel
      have hl : raw12195step2Labels = labelEmbedding9 ∘ raw12195step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12195step2 raw12195step2Labels raw12195step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5307 node5307Labels := by rfl

theorem canonical12199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12199 raw12199Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw12199 raw12199Labels = mixedMoment B raw12199step0 raw12199step0Labels := by
      have hz : ∀ j, raw12199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12199step0 = (fun i j => raw12199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12199step0 raw12199; decide +kernel
      have hl : raw12199step0Labels = raw12199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12199 raw12199Labels permutation346 hz
    mixedMoment B raw12199step0 raw12199step0Labels = mixedMoment B raw12199step1 raw12199step1Labels := by
      have hz : ∀ j, raw12199step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12199step1 = (fun i j => raw12199step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12199step1 raw12199step0; decide +kernel
      have hl : raw12199step1Labels = raw12199step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12199step0 raw12199step0Labels permutation56 hz
    mixedMoment B raw12199step1 raw12199step1Labels = mixedMoment B raw12199step2 raw12199step2Labels := by
      have ha : raw12199step2 = (fun i j => raw12199step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12199step2 raw12199step1; decide +kernel
      have hl : raw12199step2Labels = raw12199step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12199step1 raw12199step1Labels permutation8 permutation6
    mixedMoment B raw12199step2 raw12199step2Labels = mixedMoment B raw12199step3 raw12199step3Labels := by
      have ha : raw12199step3 = raw12199step2 := by apply Matrix.ext; unfold raw12199step3 raw12199step2; decide +kernel
      have hl : raw12199step2Labels = labelEmbedding9 ∘ raw12199step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12199step2 raw12199step2Labels raw12199step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5307 node5307Labels := by rfl

theorem canonical12229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12229 raw12229Labels = mixedMoment B node3628 node3628Labels := by
  calc
    mixedMoment B raw12229 raw12229Labels = mixedMoment B raw12229step0 raw12229step0Labels := by
      have hz : ∀ j, raw12229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12229step0 = (fun i j => raw12229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12229step0 raw12229; decide +kernel
      have hl : raw12229step0Labels = raw12229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12229 raw12229Labels permutation346 hz
    mixedMoment B raw12229step0 raw12229step0Labels = mixedMoment B raw12229step1 raw12229step1Labels := by
      have hz : ∀ j, raw12229step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12229step1 = (fun i j => raw12229step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12229step1 raw12229step0; decide +kernel
      have hl : raw12229step1Labels = raw12229step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12229step0 raw12229step0Labels permutation56 hz
    mixedMoment B raw12229step1 raw12229step1Labels = mixedMoment B raw12229step2 raw12229step2Labels := by
      have ha : raw12229step2 = (fun i j => raw12229step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12229step2 raw12229step1; decide +kernel
      have hl : raw12229step2Labels = raw12229step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12229step1 raw12229step1Labels permutation12 permutation2
    mixedMoment B raw12229step2 raw12229step2Labels = mixedMoment B raw12229step3 raw12229step3Labels := by
      have ha : raw12229step3 = -raw12229step2 := by apply Matrix.ext; change ∀ i j, raw12229step3 i j = -(raw12229step2 i j); unfold raw12229step3 raw12229step2; decide +kernel
      have hl : raw12229step3Labels = raw12229step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3628 node3628Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12463 raw12463Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw12463 raw12463Labels = mixedMoment B raw12463step0 raw12463step0Labels := by
      have hz : ∀ j, raw12463 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12463step0 = (fun i j => raw12463 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12463step0 raw12463; decide +kernel
      have hl : raw12463step0Labels = raw12463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12463 raw12463Labels permutation265 hz
    mixedMoment B raw12463step0 raw12463step0Labels = mixedMoment B raw12463step1 raw12463step1Labels := by
      have ha : raw12463step1 = (fun i j => raw12463step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12463step1 raw12463step0; decide +kernel
      have hl : raw12463step1Labels = raw12463step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12463step0 raw12463step0Labels permutation37 permutation7
    mixedMoment B raw12463step1 raw12463step1Labels = mixedMoment B raw12463step2 raw12463step2Labels := by
      have ha : raw12463step2 = raw12463step1 := by apply Matrix.ext; unfold raw12463step2 raw12463step1; decide +kernel
      have hl : raw12463step1Labels = labelEmbedding10 ∘ raw12463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12463step1 raw12463step1Labels raw12463step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical12467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12467 raw12467Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw12467 raw12467Labels = mixedMoment B raw12467step0 raw12467step0Labels := by
      have ha : raw12467step0 = (fun i j => raw12467 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12467step0 raw12467; decide +kernel
      have hl : raw12467step0Labels = raw12467Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12467 raw12467Labels permutation152 permutation6
    mixedMoment B raw12467step0 raw12467step0Labels = mixedMoment B raw12467step1 raw12467step1Labels := by
      have ha : raw12467step1 = raw12467step0 := by apply Matrix.ext; unfold raw12467step1 raw12467step0; decide +kernel
      have hl : raw12467step0Labels = labelEmbedding9 ∘ raw12467step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12467step0 raw12467step0Labels raw12467step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical12473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12473 raw12473Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw12473 raw12473Labels = mixedMoment B raw12473step0 raw12473step0Labels := by
      have hz : ∀ j, raw12473 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12473step0 = (fun i j => raw12473 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12473step0 raw12473; decide +kernel
      have hl : raw12473step0Labels = raw12473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12473 raw12473Labels permutation265 hz
    mixedMoment B raw12473step0 raw12473step0Labels = mixedMoment B raw12473step1 raw12473step1Labels := by
      have ha : raw12473step1 = (fun i j => raw12473step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12473step1 raw12473step0; decide +kernel
      have hl : raw12473step1Labels = raw12473step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12473step0 raw12473step0Labels permutation32 permutation6
    mixedMoment B raw12473step1 raw12473step1Labels = mixedMoment B raw12473step2 raw12473step2Labels := by
      have ha : raw12473step2 = raw12473step1 := by apply Matrix.ext; unfold raw12473step2 raw12473step1; decide +kernel
      have hl : raw12473step1Labels = labelEmbedding9 ∘ raw12473step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12473step1 raw12473step1Labels raw12473step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical12515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12515 raw12515Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw12515 raw12515Labels = mixedMoment B raw12515step0 raw12515step0Labels := by
      have hz : ∀ j, raw12515 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12515step0 = (fun i j => raw12515 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12515step0 raw12515; decide +kernel
      have hl : raw12515step0Labels = raw12515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12515 raw12515Labels permutation265 hz
    mixedMoment B raw12515step0 raw12515step0Labels = mixedMoment B raw12515step1 raw12515step1Labels := by
      have ha : raw12515step1 = (fun i j => raw12515step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12515step1 raw12515step0; decide +kernel
      have hl : raw12515step1Labels = raw12515step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12515step0 raw12515step0Labels permutation37 permutation2
    mixedMoment B raw12515step1 raw12515step1Labels = mixedMoment B raw12515step2 raw12515step2Labels := by
      have ha : raw12515step2 = -raw12515step1 := by apply Matrix.ext; change ∀ i j, raw12515step2 i j = -(raw12515step1 i j); unfold raw12515step2 raw12515step1; decide +kernel
      have hl : raw12515step2Labels = raw12515step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical12520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12520 raw12520Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw12520 raw12520Labels = mixedMoment B raw12520step0 raw12520step0Labels := by
      have ha : raw12520step0 = (fun i j => raw12520 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12520step0 raw12520; decide +kernel
      have hl : raw12520step0Labels = raw12520Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12520 raw12520Labels permutation212 permutation4
    mixedMoment B raw12520step0 raw12520step0Labels = mixedMoment B raw12520step1 raw12520step1Labels := by
      have ha : raw12520step1 = -raw12520step0 := by apply Matrix.ext; change ∀ i j, raw12520step1 i j = -(raw12520step0 i j); unfold raw12520step1 raw12520step0; decide +kernel
      have hl : raw12520step1Labels = raw12520step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3571 node3571Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12651 raw12651Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw12651 raw12651Labels = mixedMoment B raw12651step0 raw12651step0Labels := by
      have hz : ∀ j, raw12651 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12651step0 = (fun i j => raw12651 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12651step0 raw12651; decide +kernel
      have hl : raw12651step0Labels = raw12651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12651 raw12651Labels permutation265 hz
    mixedMoment B raw12651step0 raw12651step0Labels = mixedMoment B raw12651step1 raw12651step1Labels := by
      have ha : raw12651step1 = (fun i j => raw12651step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12651step1 raw12651step0; decide +kernel
      have hl : raw12651step1Labels = raw12651step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12651step0 raw12651step0Labels permutation36 permutation7
    mixedMoment B raw12651step1 raw12651step1Labels = mixedMoment B raw12651step2 raw12651step2Labels := by
      have ha : raw12651step2 = raw12651step1 := by apply Matrix.ext; unfold raw12651step2 raw12651step1; decide +kernel
      have hl : raw12651step1Labels = labelEmbedding10 ∘ raw12651step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12651step1 raw12651step1Labels raw12651step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical12652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12652 raw12652Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw12652 raw12652Labels = mixedMoment B raw12652step0 raw12652step0Labels := by
      have hz : ∀ j, raw12652 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12652step0 = (fun i j => raw12652 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12652step0 raw12652; decide +kernel
      have hl : raw12652step0Labels = raw12652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12652 raw12652Labels permutation265 hz
    mixedMoment B raw12652step0 raw12652step0Labels = mixedMoment B raw12652step1 raw12652step1Labels := by
      have ha : raw12652step1 = (fun i j => raw12652step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12652step1 raw12652step0; decide +kernel
      have hl : raw12652step1Labels = raw12652step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12652step0 raw12652step0Labels permutation32 permutation7
    mixedMoment B raw12652step1 raw12652step1Labels = mixedMoment B raw12652step2 raw12652step2Labels := by
      have ha : raw12652step2 = raw12652step1 := by apply Matrix.ext; unfold raw12652step2 raw12652step1; decide +kernel
      have hl : raw12652step1Labels = labelEmbedding10 ∘ raw12652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12652step1 raw12652step1Labels raw12652step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

theorem canonical12653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12653 raw12653Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw12653 raw12653Labels = mixedMoment B raw12653step0 raw12653step0Labels := by
      have ha : raw12653step0 = (fun i j => raw12653 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12653step0 raw12653; decide +kernel
      have hl : raw12653step0Labels = raw12653Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12653 raw12653Labels permutation212 permutation4
    mixedMoment B raw12653step0 raw12653step0Labels = mixedMoment B raw12653step1 raw12653step1Labels := by
      have ha : raw12653step1 = -raw12653step0 := by apply Matrix.ext; change ∀ i j, raw12653step1 i j = -(raw12653step0 i j); unfold raw12653step1 raw12653step0; decide +kernel
      have hl : raw12653step1Labels = raw12653step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12653step1 raw12653step1Labels = mixedMoment B raw12653step2 raw12653step2Labels := by
      have ha : raw12653step2 = raw12653step1 := by apply Matrix.ext; unfold raw12653step2 raw12653step1; decide +kernel
      have hl : raw12653step1Labels = labelEmbedding7 ∘ raw12653step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12653step1 raw12653step1Labels raw12653step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

theorem canonical12654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12654 raw12654Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw12654 raw12654Labels = mixedMoment B raw12654step0 raw12654step0Labels := by
      have ha : raw12654step0 = (fun i j => raw12654 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12654step0 raw12654; decide +kernel
      have hl : raw12654step0Labels = raw12654Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12654 raw12654Labels permutation154 permutation6
    mixedMoment B raw12654step0 raw12654step0Labels = mixedMoment B raw12654step1 raw12654step1Labels := by
      have ha : raw12654step1 = raw12654step0 := by apply Matrix.ext; unfold raw12654step1 raw12654step0; decide +kernel
      have hl : raw12654step0Labels = labelEmbedding9 ∘ raw12654step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12654step0 raw12654step0Labels raw12654step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical12655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12655 raw12655Labels = mixedMoment B node5283 node5283Labels := by
  calc
    mixedMoment B raw12655 raw12655Labels = mixedMoment B raw12655step0 raw12655step0Labels := by
      have ha : raw12655step0 = (fun i j => raw12655 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12655step0 raw12655; decide +kernel
      have hl : raw12655step0Labels = raw12655Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12655 raw12655Labels permutation152 permutation6
    mixedMoment B raw12655step0 raw12655step0Labels = mixedMoment B raw12655step1 raw12655step1Labels := by
      have ha : raw12655step1 = raw12655step0 := by apply Matrix.ext; unfold raw12655step1 raw12655step0; decide +kernel
      have hl : raw12655step0Labels = labelEmbedding9 ∘ raw12655step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12655step0 raw12655step0Labels raw12655step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5283 node5283Labels := by rfl

theorem canonical12656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12656 raw12656Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw12656 raw12656Labels = mixedMoment B raw12656step0 raw12656step0Labels := by
      have hz : ∀ j, raw12656 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12656step0 = (fun i j => raw12656 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12656step0 raw12656; decide +kernel
      have hl : raw12656step0Labels = raw12656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12656 raw12656Labels permutation265 hz
    mixedMoment B raw12656step0 raw12656step0Labels = mixedMoment B raw12656step1 raw12656step1Labels := by
      have ha : raw12656step1 = (fun i j => raw12656step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12656step1 raw12656step0; decide +kernel
      have hl : raw12656step1Labels = raw12656step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12656step0 raw12656step0Labels permutation44 permutation4
    mixedMoment B raw12656step1 raw12656step1Labels = mixedMoment B raw12656step2 raw12656step2Labels := by
      have ha : raw12656step2 = -raw12656step1 := by apply Matrix.ext; change ∀ i j, raw12656step2 i j = -(raw12656step1 i j); unfold raw12656step2 raw12656step1; decide +kernel
      have hl : raw12656step2Labels = raw12656step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12656step2 raw12656step2Labels = mixedMoment B raw12656step3 raw12656step3Labels := by
      have ha : raw12656step3 = raw12656step2 := by apply Matrix.ext; unfold raw12656step3 raw12656step2; decide +kernel
      have hl : raw12656step2Labels = labelEmbedding7 ∘ raw12656step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12656step2 raw12656step2Labels raw12656step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4893 node4893Labels := by rfl

theorem canonical12657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12657 raw12657Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw12657 raw12657Labels = mixedMoment B raw12657step0 raw12657step0Labels := by
      have hz : ∀ j, raw12657 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12657step0 = (fun i j => raw12657 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12657step0 raw12657; decide +kernel
      have hl : raw12657step0Labels = raw12657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12657 raw12657Labels permutation265 hz
    mixedMoment B raw12657step0 raw12657step0Labels = mixedMoment B raw12657step1 raw12657step1Labels := by
      have ha : raw12657step1 = (fun i j => raw12657step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12657step1 raw12657step0; decide +kernel
      have hl : raw12657step1Labels = raw12657step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12657step0 raw12657step0Labels permutation34 permutation6
    mixedMoment B raw12657step1 raw12657step1Labels = mixedMoment B raw12657step2 raw12657step2Labels := by
      have ha : raw12657step2 = raw12657step1 := by apply Matrix.ext; unfold raw12657step2 raw12657step1; decide +kernel
      have hl : raw12657step1Labels = labelEmbedding9 ∘ raw12657step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12657step1 raw12657step1Labels raw12657step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical12658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12658 raw12658Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12658 raw12658Labels = mixedMoment B raw12658step0 raw12658step0Labels := by
      have hz : ∀ j, raw12658 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12658step0 = (fun i j => raw12658 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12658step0 raw12658; decide +kernel
      have hl : raw12658step0Labels = raw12658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12658 raw12658Labels permutation265 hz
    mixedMoment B raw12658step0 raw12658step0Labels = mixedMoment B raw12658step1 raw12658step1Labels := by
      have ha : raw12658step1 = (fun i j => raw12658step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12658step1 raw12658step0; decide +kernel
      have hl : raw12658step1Labels = raw12658step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12658step0 raw12658step0Labels permutation35 permutation6
    mixedMoment B raw12658step1 raw12658step1Labels = mixedMoment B raw12658step2 raw12658step2Labels := by
      have ha : raw12658step2 = raw12658step1 := by apply Matrix.ext; unfold raw12658step2 raw12658step1; decide +kernel
      have hl : raw12658step1Labels = labelEmbedding9 ∘ raw12658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12658step1 raw12658step1Labels raw12658step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical12659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12659 raw12659Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw12659 raw12659Labels = mixedMoment B raw12659step0 raw12659step0Labels := by
      have hz : ∀ j, raw12659 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12659step0 = (fun i j => raw12659 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12659step0 raw12659; decide +kernel
      have hl : raw12659step0Labels = raw12659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12659 raw12659Labels permutation265 hz
    mixedMoment B raw12659step0 raw12659step0Labels = mixedMoment B raw12659step1 raw12659step1Labels := by
      have ha : raw12659step1 = (fun i j => raw12659step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12659step1 raw12659step0; decide +kernel
      have hl : raw12659step1Labels = raw12659step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12659step0 raw12659step0Labels permutation38 permutation4
    mixedMoment B raw12659step1 raw12659step1Labels = mixedMoment B raw12659step2 raw12659step2Labels := by
      have ha : raw12659step2 = -raw12659step1 := by apply Matrix.ext; change ∀ i j, raw12659step2 i j = -(raw12659step1 i j); unfold raw12659step2 raw12659step1; decide +kernel
      have hl : raw12659step2Labels = raw12659step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12659step2 raw12659step2Labels = mixedMoment B raw12659step3 raw12659step3Labels := by
      have ha : raw12659step3 = raw12659step2 := by apply Matrix.ext; unfold raw12659step3 raw12659step2; decide +kernel
      have hl : raw12659step2Labels = labelEmbedding7 ∘ raw12659step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12659step2 raw12659step2Labels raw12659step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4893 node4893Labels := by rfl

theorem canonical12660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12660 raw12660Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12660 raw12660Labels = mixedMoment B raw12660step0 raw12660step0Labels := by
      have hz : ∀ j, raw12660 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12660step0 = (fun i j => raw12660 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12660step0 raw12660; decide +kernel
      have hl : raw12660step0Labels = raw12660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12660 raw12660Labels permutation265 hz
    mixedMoment B raw12660step0 raw12660step0Labels = mixedMoment B raw12660step1 raw12660step1Labels := by
      have ha : raw12660step1 = (fun i j => raw12660step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12660step1 raw12660step0; decide +kernel
      have hl : raw12660step1Labels = raw12660step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12660step0 raw12660step0Labels permutation33 permutation6
    mixedMoment B raw12660step1 raw12660step1Labels = mixedMoment B raw12660step2 raw12660step2Labels := by
      have ha : raw12660step2 = raw12660step1 := by apply Matrix.ext; unfold raw12660step2 raw12660step1; decide +kernel
      have hl : raw12660step1Labels = labelEmbedding9 ∘ raw12660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12660step1 raw12660step1Labels raw12660step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical12661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12661 raw12661Labels = mixedMoment B node3622 node3622Labels := by
  calc
    mixedMoment B raw12661 raw12661Labels = mixedMoment B raw12661step0 raw12661step0Labels := by
      have hz : ∀ j, raw12661 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12661step0 = (fun i j => raw12661 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12661step0 raw12661; decide +kernel
      have hl : raw12661step0Labels = raw12661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12661 raw12661Labels permutation265 hz
    mixedMoment B raw12661step0 raw12661step0Labels = mixedMoment B raw12661step1 raw12661step1Labels := by
      have ha : raw12661step1 = (fun i j => raw12661step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12661step1 raw12661step0; decide +kernel
      have hl : raw12661step1Labels = raw12661step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12661step0 raw12661step0Labels permutation40 permutation4
    mixedMoment B raw12661step1 raw12661step1Labels = mixedMoment B raw12661step2 raw12661step2Labels := by
      have ha : raw12661step2 = -raw12661step1 := by apply Matrix.ext; change ∀ i j, raw12661step2 i j = -(raw12661step1 i j); unfold raw12661step2 raw12661step1; decide +kernel
      have hl : raw12661step2Labels = raw12661step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3622 node3622Labels := by rfl

theorem canonical12662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12662 raw12662Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw12662 raw12662Labels = mixedMoment B raw12662step0 raw12662step0Labels := by
      have hz : ∀ j, raw12662 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12662step0 = (fun i j => raw12662 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12662step0 raw12662; decide +kernel
      have hl : raw12662step0Labels = raw12662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12662 raw12662Labels permutation265 hz
    mixedMoment B raw12662step0 raw12662step0Labels = mixedMoment B raw12662step1 raw12662step1Labels := by
      have ha : raw12662step1 = (fun i j => raw12662step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12662step1 raw12662step0; decide +kernel
      have hl : raw12662step1Labels = raw12662step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12662step0 raw12662step0Labels permutation36 permutation2
    mixedMoment B raw12662step1 raw12662step1Labels = mixedMoment B raw12662step2 raw12662step2Labels := by
      have ha : raw12662step2 = -raw12662step1 := by apply Matrix.ext; change ∀ i j, raw12662step2 i j = -(raw12662step1 i j); unfold raw12662step2 raw12662step1; decide +kernel
      have hl : raw12662step2Labels = raw12662step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical12663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12663 raw12663Labels = mixedMoment B node3546 node3546Labels := by
  calc
    mixedMoment B raw12663 raw12663Labels = mixedMoment B raw12663step0 raw12663step0Labels := by
      have hz : ∀ j, raw12663 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12663step0 = (fun i j => raw12663 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12663step0 raw12663; decide +kernel
      have hl : raw12663step0Labels = raw12663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12663 raw12663Labels permutation265 hz
    mixedMoment B raw12663step0 raw12663step0Labels = mixedMoment B raw12663step1 raw12663step1Labels := by
      have ha : raw12663step1 = -raw12663step0 := by apply Matrix.ext; change ∀ i j, raw12663step1 i j = -(raw12663step0 i j); unfold raw12663step1 raw12663step0; decide +kernel
      have hl : raw12663step1Labels = raw12663step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3546 node3546Labels := by rfl

theorem canonical12664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12664 raw12664Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw12664 raw12664Labels = mixedMoment B raw12664step0 raw12664step0Labels := by
      have ha : raw12664step0 = (fun i j => raw12664 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12664step0 raw12664; decide +kernel
      have hl : raw12664step0Labels = raw12664Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12664 raw12664Labels permutation212 permutation4
    mixedMoment B raw12664step0 raw12664step0Labels = mixedMoment B raw12664step1 raw12664step1Labels := by
      have ha : raw12664step1 = -raw12664step0 := by apply Matrix.ext; change ∀ i j, raw12664step1 i j = -(raw12664step0 i j); unfold raw12664step1 raw12664step0; decide +kernel
      have hl : raw12664step1Labels = raw12664step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2243 node2243Labels := by rfl

theorem canonical12665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12665 raw12665Labels = mixedMoment B node3622 node3622Labels := by
  calc
    mixedMoment B raw12665 raw12665Labels = mixedMoment B raw12665step0 raw12665step0Labels := by
      have hz : ∀ j, raw12665 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12665step0 = (fun i j => raw12665 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12665step0 raw12665; decide +kernel
      have hl : raw12665step0Labels = raw12665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12665 raw12665Labels permutation346 hz
    mixedMoment B raw12665step0 raw12665step0Labels = mixedMoment B raw12665step1 raw12665step1Labels := by
      have ha : raw12665step1 = (fun i j => raw12665step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12665step1 raw12665step0; decide +kernel
      have hl : raw12665step1Labels = raw12665step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12665step0 raw12665step0Labels permutation40 permutation4
    mixedMoment B raw12665step1 raw12665step1Labels = mixedMoment B raw12665step2 raw12665step2Labels := by
      have ha : raw12665step2 = -raw12665step1 := by apply Matrix.ext; change ∀ i j, raw12665step2 i j = -(raw12665step1 i j); unfold raw12665step2 raw12665step1; decide +kernel
      have hl : raw12665step2Labels = raw12665step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3622 node3622Labels := by rfl

theorem canonical12666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12666 raw12666Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw12666 raw12666Labels = mixedMoment B raw12666step0 raw12666step0Labels := by
      have ha : raw12666step0 = (fun i j => raw12666 (permutation234 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12666step0 raw12666; decide +kernel
      have hl : raw12666step0Labels = raw12666Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12666 raw12666Labels permutation234 permutation4
    mixedMoment B raw12666step0 raw12666step0Labels = mixedMoment B raw12666step1 raw12666step1Labels := by
      have ha : raw12666step1 = -raw12666step0 := by apply Matrix.ext; change ∀ i j, raw12666step1 i j = -(raw12666step0 i j); unfold raw12666step1 raw12666step0; decide +kernel
      have hl : raw12666step1Labels = raw12666step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3571 node3571Labels := by rfl

theorem canonical12667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12667 raw12667Labels = mixedMoment B node3618 node3618Labels := by
  calc
    mixedMoment B raw12667 raw12667Labels = mixedMoment B raw12667step0 raw12667step0Labels := by
      have ha : raw12667step0 = (fun i j => raw12667 (permutation216 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12667step0 raw12667; decide +kernel
      have hl : raw12667step0Labels = raw12667Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12667 raw12667Labels permutation216 permutation4
    mixedMoment B raw12667step0 raw12667step0Labels = mixedMoment B raw12667step1 raw12667step1Labels := by
      have ha : raw12667step1 = -raw12667step0 := by apply Matrix.ext; change ∀ i j, raw12667step1 i j = -(raw12667step0 i j); unfold raw12667step1 raw12667step0; decide +kernel
      have hl : raw12667step1Labels = raw12667step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3618 node3618Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12758 raw12758Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw12758 raw12758Labels = mixedMoment B raw12758step0 raw12758step0Labels := by
      have hz : ∀ j, raw12758 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12758step0 = (fun i j => raw12758 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12758step0 raw12758; decide +kernel
      have hl : raw12758step0Labels = raw12758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12758 raw12758Labels permutation265 hz
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical12759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12759 raw12759Labels = mixedMoment B node1276 node1276Labels := by
  calc
    mixedMoment B raw12759 raw12759Labels = mixedMoment B raw12759step0 raw12759step0Labels := by
      have ha : raw12759step0 = (fun i j => raw12759 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12759step0 raw12759; decide +kernel
      have hl : raw12759step0Labels = raw12759Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12759 raw12759Labels permutation182 permutation2
    _ = mixedMoment B node1276 node1276Labels := by rfl

theorem canonical12760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12760 raw12760Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw12760 raw12760Labels = mixedMoment B raw12760step0 raw12760step0Labels := by
      have hz : ∀ j, raw12760 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12760step0 = (fun i j => raw12760 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12760step0 raw12760; decide +kernel
      have hl : raw12760step0Labels = raw12760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12760 raw12760Labels permutation265 hz
    mixedMoment B raw12760step0 raw12760step0Labels = mixedMoment B raw12760step1 raw12760step1Labels := by
      have ha : raw12760step1 = (fun i j => raw12760step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12760step1 raw12760step0; decide +kernel
      have hl : raw12760step1Labels = raw12760step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12760step0 raw12760step0Labels permutation41 permutation2
    _ = mixedMoment B node1291 node1291Labels := by rfl

theorem canonical12761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12761 raw12761Labels = mixedMoment B node1280 node1280Labels := by
  calc
    mixedMoment B raw12761 raw12761Labels = mixedMoment B raw12761step0 raw12761step0Labels := by
      have hz : ∀ j, raw12761 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12761step0 = (fun i j => raw12761 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12761step0 raw12761; decide +kernel
      have hl : raw12761step0Labels = raw12761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12761 raw12761Labels permutation265 hz
    mixedMoment B raw12761step0 raw12761step0Labels = mixedMoment B raw12761step1 raw12761step1Labels := by
      have ha : raw12761step1 = (fun i j => raw12761step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12761step1 raw12761step0; decide +kernel
      have hl : raw12761step1Labels = raw12761step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12761step0 raw12761step0Labels permutation35 permutation2
    _ = mixedMoment B node1280 node1280Labels := by rfl

theorem canonical12762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12762 raw12762Labels = mixedMoment B node1278 node1278Labels := by
  calc
    mixedMoment B raw12762 raw12762Labels = mixedMoment B raw12762step0 raw12762step0Labels := by
      have hz : ∀ j, raw12762 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12762step0 = (fun i j => raw12762 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12762step0 raw12762; decide +kernel
      have hl : raw12762step0Labels = raw12762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12762 raw12762Labels permutation265 hz
    mixedMoment B raw12762step0 raw12762step0Labels = mixedMoment B raw12762step1 raw12762step1Labels := by
      have ha : raw12762step1 = (fun i j => raw12762step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12762step1 raw12762step0; decide +kernel
      have hl : raw12762step1Labels = raw12762step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12762step0 raw12762step0Labels permutation33 permutation2
    _ = mixedMoment B node1278 node1278Labels := by rfl

theorem canonical12763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12763 raw12763Labels = mixedMoment B node1277 node1277Labels := by
  calc
    mixedMoment B raw12763 raw12763Labels = mixedMoment B raw12763step0 raw12763step0Labels := by
      have hz : ∀ j, raw12763 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12763step0 = (fun i j => raw12763 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12763step0 raw12763; decide +kernel
      have hl : raw12763step0Labels = raw12763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12763 raw12763Labels permutation265 hz
    _ = mixedMoment B node1277 node1277Labels := by rfl

theorem canonical12764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12764 raw12764Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw12764 raw12764Labels = mixedMoment B raw12764step0 raw12764step0Labels := by
      have hz : ∀ j, raw12764 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12764step0 = (fun i j => raw12764 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12764step0 raw12764; decide +kernel
      have hl : raw12764step0Labels = raw12764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12764 raw12764Labels permutation520 hz
    mixedMoment B raw12764step0 raw12764step0Labels = mixedMoment B raw12764step1 raw12764step1Labels := by
      have hz : ∀ j, raw12764step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12764step1 = (fun i j => raw12764step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12764step1 raw12764step0; decide +kernel
      have hl : raw12764step1Labels = raw12764step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12764step0 raw12764step0Labels permutation56 hz
    mixedMoment B raw12764step1 raw12764step1Labels = mixedMoment B raw12764step2 raw12764step2Labels := by
      have ha : raw12764step2 = (fun i j => raw12764step1 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw12764step2 raw12764step1; decide +kernel
      have hl : raw12764step2Labels = raw12764step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12764step1 raw12764step1Labels permutation11 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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

theorem singleton4887 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4887 node4887Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2243 node2243Labels + mixedMoment B node2243 node2243Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1812 singletonSmall4887
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4887) = raw1812Labels := by decide +kernel
  rw [hl, canonical1812 B hB] at h
  have hc0 : mixedMoment B raw1812 (Fin.cases (0 : Fin 2) singletonSmall4887) =
      mixedMoment B node2243 node2243Labels := by
    have ha : raw1812 = raw1813 := by apply Matrix.ext; unfold raw1812 raw1813; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4887 = raw1813Labels := by decide +kernel
    rw [ha, hj, canonical1813 B hB]
  have hc1 : mixedMoment B raw1812 (Fin.cases (1 : Fin 2) singletonSmall4887) =
      mixedMoment B node2243 node2243Labels := by
    have ha : raw1812 = raw1814 := by apply Matrix.ext; unfold raw1812 raw1814; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4887 = raw1814Labels := by decide +kernel
    rw [ha, hj, canonical1814 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4888 node4888Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2244 node2244Labels + mixedMoment B node2262 node2262Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1815 singletonSmall4888
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4888) = raw1815Labels := by decide +kernel
  rw [hl, canonical1815 B hB] at h
  have hc0 : mixedMoment B raw1815 (Fin.cases (0 : Fin 2) singletonSmall4888) =
      mixedMoment B node2244 node2244Labels := by
    have ha : raw1815 = raw1816 := by apply Matrix.ext; unfold raw1815 raw1816; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4888 = raw1816Labels := by decide +kernel
    rw [ha, hj, canonical1816 B hB]
  have hc1 : mixedMoment B raw1815 (Fin.cases (1 : Fin 2) singletonSmall4888) =
      mixedMoment B node2262 node2262Labels := by
    have ha : raw1815 = raw1817 := by apply Matrix.ext; unfold raw1815 raw1817; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4888 = raw1817Labels := by decide +kernel
    rw [ha, hj, canonical1817 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4889 node4889Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2245 node2245Labels + mixedMoment B node2277 node2277Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1818 singletonSmall4889
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4889) = raw1818Labels := by decide +kernel
  rw [hl, canonical1818 B hB] at h
  have hc0 : mixedMoment B raw1818 (Fin.cases (0 : Fin 2) singletonSmall4889) =
      mixedMoment B node2245 node2245Labels := by
    have ha : raw1818 = raw1819 := by apply Matrix.ext; unfold raw1818 raw1819; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4889 = raw1819Labels := by decide +kernel
    rw [ha, hj, canonical1819 B hB]
  have hc1 : mixedMoment B raw1818 (Fin.cases (1 : Fin 2) singletonSmall4889) =
      mixedMoment B node2277 node2277Labels := by
    have ha : raw1818 = raw1820 := by apply Matrix.ext; unfold raw1818 raw1820; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4889 = raw1820Labels := by decide +kernel
    rw [ha, hj, canonical1820 B hB]
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

theorem singleton5257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5257 node5257Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2721 node2721Labels + mixedMoment B node3532 node3532Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2268 singletonSmall5257
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5257) = raw2268Labels := by decide +kernel
  rw [hl, canonical2268 B hB] at h
  have hc0 : mixedMoment B raw2268 (Fin.cases (0 : Fin 2) singletonSmall5257) =
      mixedMoment B node2721 node2721Labels := by
    have ha : raw2268 = raw2269 := by apply Matrix.ext; unfold raw2268 raw2269; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5257 = raw2269Labels := by decide +kernel
    rw [ha, hj, canonical2269 B hB]
  have hc1 : mixedMoment B raw2268 (Fin.cases (1 : Fin 2) singletonSmall5257) =
      mixedMoment B node3532 node3532Labels := by
    have ha : raw2268 = raw2270 := by apply Matrix.ext; unfold raw2268 raw2270; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5257 = raw2270Labels := by decide +kernel
    rw [ha, hj, canonical2270 B hB]
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

theorem singleton5290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5290 node5290Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2764 node2764Labels + mixedMoment B node3581 node3581Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2292 singletonSmall5290
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5290) = raw2292Labels := by decide +kernel
  rw [hl, canonical2292 B hB] at h
  have hc0 : mixedMoment B raw2292 (Fin.cases (0 : Fin 2) singletonSmall5290) =
      mixedMoment B node2764 node2764Labels := by
    have ha : raw2292 = raw2293 := by apply Matrix.ext; unfold raw2292 raw2293; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5290 = raw2293Labels := by decide +kernel
    rw [ha, hj, canonical2293 B hB]
  have hc1 : mixedMoment B raw2292 (Fin.cases (1 : Fin 2) singletonSmall5290) =
      mixedMoment B node3581 node3581Labels := by
    have ha : raw2292 = raw2294 := by apply Matrix.ext; unfold raw2292 raw2294; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5290 = raw2294Labels := by decide +kernel
    rw [ha, hj, canonical2294 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5301 node5301Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3053 node3053Labels + mixedMoment B node3619 node3619Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2310 singletonSmall5301
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5301) = raw2310Labels := by decide +kernel
  rw [hl, canonical2310 B hB] at h
  have hc0 : mixedMoment B raw2310 (Fin.cases (0 : Fin 2) singletonSmall5301) =
      mixedMoment B node3053 node3053Labels := by
    have ha : raw2310 = raw2311 := by apply Matrix.ext; unfold raw2310 raw2311; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5301 = raw2311Labels := by decide +kernel
    rw [ha, hj, canonical2311 B hB]
  have hc1 : mixedMoment B raw2310 (Fin.cases (1 : Fin 2) singletonSmall5301) =
      mixedMoment B node3619 node3619Labels := by
    have ha : raw2310 = raw2312 := by apply Matrix.ext; unfold raw2310 raw2312; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5301 = raw2312Labels := by decide +kernel
    rw [ha, hj, canonical2312 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound1276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1276 node1276Labels = Sparse.eval nodeValue1276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1276) = mixedMoment B node1276 node1276Labels := rfl
  simpa [nodeValue1276, Sparse.eval] using hc.symm

theorem sound1277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1277 node1277Labels = Sparse.eval nodeValue1277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1277) = mixedMoment B node1277 node1277Labels := rfl
  simpa [nodeValue1277, Sparse.eval] using hc.symm

theorem sound1278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1278 node1278Labels = Sparse.eval nodeValue1278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1278) = mixedMoment B node1278 node1278Labels := rfl
  simpa [nodeValue1278, Sparse.eval] using hc.symm

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

theorem sound1280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1280 node1280Labels = Sparse.eval nodeValue1280 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1280) = mixedMoment B node1280 node1280Labels := rfl
  simpa [nodeValue1280, Sparse.eval] using hc.symm

theorem sound1291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1291 node1291Labels = Sparse.eval nodeValue1291 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1291) = mixedMoment B node1291 node1291Labels := rfl
  simpa [nodeValue1291, Sparse.eval] using hc.symm

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

theorem sound1364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1364 node1364Labels = Sparse.eval nodeValue1364 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1364) = mixedMoment B node1364 node1364Labels := rfl
  simpa [nodeValue1364, Sparse.eval] using hc.symm

theorem sound1367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1367 node1367Labels = Sparse.eval nodeValue1367 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1367) = mixedMoment B node1367 node1367Labels := rfl
  simpa [nodeValue1367, Sparse.eval] using hc.symm

theorem sound1368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1368 node1368Labels = Sparse.eval nodeValue1368 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1368) = mixedMoment B node1368 node1368Labels := rfl
  simpa [nodeValue1368, Sparse.eval] using hc.symm

theorem sound1371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1371 node1371Labels = Sparse.eval nodeValue1371 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1371) = mixedMoment B node1371 node1371Labels := rfl
  simpa [nodeValue1371, Sparse.eval] using hc.symm

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

theorem sound1433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1433 node1433Labels = Sparse.eval nodeValue1433 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1433) = mixedMoment B node1433 node1433Labels := rfl
  simpa [nodeValue1433, Sparse.eval] using hc.symm

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

theorem sound2243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2243 node2243Labels = Sparse.eval nodeValue2243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2243) = mixedMoment B node2243 node2243Labels := rfl
  simpa [nodeValue2243, Sparse.eval] using hc.symm

theorem sound2244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2244 node2244Labels = Sparse.eval nodeValue2244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2244) = mixedMoment B node2244 node2244Labels := rfl
  simpa [nodeValue2244, Sparse.eval] using hc.symm

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

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

theorem sound2721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2721 node2721Labels = Sparse.eval nodeValue2721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2721) = mixedMoment B node2721 node2721Labels := rfl
  simpa [nodeValue2721, Sparse.eval] using hc.symm

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

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

theorem sound2764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2764 node2764Labels = Sparse.eval nodeValue2764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2764) = mixedMoment B node2764 node2764Labels := rfl
  simpa [nodeValue2764, Sparse.eval] using hc.symm

theorem sound2773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2773 node2773Labels = Sparse.eval nodeValue2773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2773) = mixedMoment B node2773 node2773Labels := rfl
  simpa [nodeValue2773, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2878 node2878Labels = Sparse.eval nodeValue2878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2878) = mixedMoment B node2878 node2878Labels := rfl
  simpa [nodeValue2878, Sparse.eval] using hc.symm

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

theorem sound3036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3036 node3036Labels = Sparse.eval nodeValue3036 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3036) = mixedMoment B node3036 node3036Labels := rfl
  simpa [nodeValue3036, Sparse.eval] using hc.symm

theorem sound3043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3043 node3043Labels = Sparse.eval nodeValue3043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3043) = mixedMoment B node3043 node3043Labels := rfl
  simpa [nodeValue3043, Sparse.eval] using hc.symm

theorem sound3051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3051 node3051Labels = Sparse.eval nodeValue3051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3051) = mixedMoment B node3051 node3051Labels := rfl
  simpa [nodeValue3051, Sparse.eval] using hc.symm

theorem sound3053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3053 node3053Labels = Sparse.eval nodeValue3053 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3053) = mixedMoment B node3053 node3053Labels := rfl
  simpa [nodeValue3053, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3546 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3546 node3546Labels = 0 := by
  exact mixedMoment_order_one B hB node3546 node3546Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3532 node3532Labels = Sparse.eval nodeValue3532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3532) = mixedMoment B node3532 node3532Labels := rfl
  simpa [nodeValue3532, Sparse.eval] using hc.symm

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

theorem sound3546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3546 node3546Labels = Sparse.eval nodeValue3546 (mixedVector B) := by
  simpa only [nodeValue3546, Sparse.eval_nil] using zero3546 B _hB _hF

theorem sound3571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3571 node3571Labels = Sparse.eval nodeValue3571 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3571) = mixedMoment B node3571 node3571Labels := rfl
  simpa [nodeValue3571, Sparse.eval] using hc.symm

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3618 node3618Labels = 0 := by
  exact mixedMoment_alpha B hF node3618 node3618Labels 1 permutation434
    (by decide +kernel)

theorem zero3628 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3628 node3628Labels = 0 := by
  exact mixedMoment_order_one B hB node3628 node3628Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3618 node3618Labels = Sparse.eval nodeValue3618 (mixedVector B) := by
  simpa only [nodeValue3618, Sparse.eval_nil] using zero3618 B _hB _hF

theorem sound3619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3619 node3619Labels = Sparse.eval nodeValue3619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3619) = mixedMoment B node3619 node3619Labels := rfl
  simpa [nodeValue3619, Sparse.eval] using hc.symm

theorem sound3622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3622 node3622Labels = Sparse.eval nodeValue3622 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3622) = mixedMoment B node3622 node3622Labels := rfl
  simpa [nodeValue3622, Sparse.eval] using hc.symm

theorem sound3623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3623 node3623Labels = Sparse.eval nodeValue3623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3623) = mixedMoment B node3623 node3623Labels := rfl
  simpa [nodeValue3623, Sparse.eval] using hc.symm

theorem sound3628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3628 node3628Labels = Sparse.eval nodeValue3628 (mixedVector B) := by
  simpa only [nodeValue3628, Sparse.eval_nil] using zero3628 B _hB _hF

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

theorem sound3848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3848 node3848Labels = Sparse.eval nodeValue3848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3848) = mixedMoment B node3848 node3848Labels := rfl
  simpa [nodeValue3848, Sparse.eval] using hc.symm

theorem sound3850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3850 node3850Labels = Sparse.eval nodeValue3850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3850) = mixedMoment B node3850 node3850Labels := rfl
  simpa [nodeValue3850, Sparse.eval] using hc.symm

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

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

theorem sound3961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3961 node3961Labels = Sparse.eval nodeValue3961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3961) = mixedMoment B node3961 node3961Labels := rfl
  simpa [nodeValue3961, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4893 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4893 node4893Labels = 0 := by
  exact mixedMoment_order_one B hB node4893 node4893Labels 1
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

theorem sound4887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4887 node4887Labels = Sparse.eval nodeValue4887 (mixedVector B) := by
  have h := singleton4887 B _hB
  rw [sound2243 B _hB _hF] at h
  norm_num [nodeValue4887, nodeValue2243, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4888 node4888Labels = Sparse.eval nodeValue4888 (mixedVector B) := by
  have h := singleton4888 B _hB
  rw [sound2244 B _hB _hF, sound2262 B _hB _hF] at h
  norm_num [nodeValue4888, nodeValue2244, nodeValue2262, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4889 node4889Labels = Sparse.eval nodeValue4889 (mixedVector B) := by
  have h := singleton4889 B _hB
  rw [sound2245 B _hB _hF, sound2277 B _hB _hF] at h
  norm_num [nodeValue4889, nodeValue2245, nodeValue2277, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4893 node4893Labels = Sparse.eval nodeValue4893 (mixedVector B) := by
  simpa only [nodeValue4893, Sparse.eval_nil] using zero4893 B _hB _hF

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

theorem zero5256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5256 node5256Labels = 0 := by
  exact mixedMoment_alpha B hF node5256 node5256Labels 1 permutation203
    (by decide +kernel)

theorem zero5273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5273 node5273Labels = 0 := by
  exact mixedMoment_order_one B hB node5273 node5273Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5283 node5283Labels = 0 := by
  exact mixedMoment_alpha B hF node5283 node5283Labels 1 permutation152
    (by decide +kernel)

theorem zero5307 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5307 node5307Labels = 0 := by
  exact mixedMoment_order_one B hB node5307 node5307Labels 1
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

theorem sound5256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5256 node5256Labels = Sparse.eval nodeValue5256 (mixedVector B) := by
  simpa only [nodeValue5256, Sparse.eval_nil] using zero5256 B _hB _hF

theorem sound5257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5257 node5257Labels = Sparse.eval nodeValue5257 (mixedVector B) := by
  have h := singleton5257 B _hB
  rw [sound2721 B _hB _hF, sound3532 B _hB _hF] at h
  norm_num [nodeValue5257, nodeValue2721, nodeValue3532, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5265 node5265Labels = Sparse.eval nodeValue5265 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5265) = mixedMoment B node5265 node5265Labels := rfl
  simpa [nodeValue5265, Sparse.eval] using hc.symm

theorem sound5271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5271 node5271Labels = Sparse.eval nodeValue5271 (mixedVector B) := by
  have h := singleton5271 B _hB
  rw [sound2739 B _hB _hF, sound3534 B _hB _hF] at h
  norm_num [nodeValue5271, nodeValue2739, nodeValue3534, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5273 node5273Labels = Sparse.eval nodeValue5273 (mixedVector B) := by
  simpa only [nodeValue5273, Sparse.eval_nil] using zero5273 B _hB _hF

theorem sound5281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5281 node5281Labels = Sparse.eval nodeValue5281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5281) = mixedMoment B node5281 node5281Labels := rfl
  simpa [nodeValue5281, Sparse.eval] using hc.symm

theorem sound5283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5283 node5283Labels = Sparse.eval nodeValue5283 (mixedVector B) := by
  simpa only [nodeValue5283, Sparse.eval_nil] using zero5283 B _hB _hF

theorem sound5289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5289 node5289Labels = Sparse.eval nodeValue5289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5289) = mixedMoment B node5289 node5289Labels := rfl
  simpa [nodeValue5289, Sparse.eval] using hc.symm

theorem sound5290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5290 node5290Labels = Sparse.eval nodeValue5290 (mixedVector B) := by
  have h := singleton5290 B _hB
  rw [sound2764 B _hB _hF, sound3581 B _hB _hF] at h
  norm_num [nodeValue5290, nodeValue2764, nodeValue3581, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5299 node5299Labels = Sparse.eval nodeValue5299 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5299) = mixedMoment B node5299 node5299Labels := rfl
  simpa [nodeValue5299, Sparse.eval] using hc.symm

theorem sound5301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5301 node5301Labels = Sparse.eval nodeValue5301 (mixedVector B) := by
  have h := singleton5301 B _hB
  rw [sound3053 B _hB _hF, sound3619 B _hB _hF] at h
  norm_num [nodeValue5301, nodeValue3053, nodeValue3619, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5306 node5306Labels = Sparse.eval nodeValue5306 (mixedVector B) := by
  have h := singleton5306 B _hB
  rw [sound2784 B _hB _hF, sound3623 B _hB _hF] at h
  norm_num [nodeValue5306, nodeValue2784, nodeValue3623, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5307 node5307Labels = Sparse.eval nodeValue5307 (mixedVector B) := by
  simpa only [nodeValue5307, Sparse.eval_nil] using zero5307 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources23
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq761 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm761 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA761 + difference 0 1) (sourceB761 + difference 1 0) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA761 + difference 0 1) (sourceB761 + difference 1 0) sourceC761) = raw11664 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw11664; decide +kernel
    rw [ha]
    exact (canonical11664 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA761 + difference 0 2) (sourceB761 + difference 2 0) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA761 + difference 0 2) (sourceB761 + difference 2 0) sourceC761) = raw12186 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12186; decide +kernel
    rw [ha]
    exact (canonical12186 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA761 + difference 0 3) (sourceB761 + difference 3 0) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA761 + difference 0 3) (sourceB761 + difference 3 0) sourceC761) = raw12463 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12463; decide +kernel
    rw [ha]
    exact (canonical12463 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA761 + difference 0 4) (sourceB761 + difference 4 0) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA761 + difference 0 4) (sourceB761 + difference 4 0) sourceC761) = raw12651 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12651; decide +kernel
    rw [ha]
    exact (canonical12651 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA761 + difference 0 5) (sourceB761 + difference 5 0) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA761 + difference 0 5) (sourceB761 + difference 5 0) sourceC761) = raw12652 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12652; decide +kernel
    rw [ha]
    exact (canonical12652 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA761 + difference 1 0) (sourceB761 + difference 0 1) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA761 + difference 1 0) (sourceB761 + difference 0 1) sourceC761) = raw12653 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12653; decide +kernel
    rw [ha]
    exact (canonical12653 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA761 + difference 1 2) (sourceB761 + difference 2 1) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA761 + difference 1 2) (sourceB761 + difference 2 1) sourceC761) = raw12191 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12191; decide +kernel
    rw [ha]
    exact (canonical12191 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA761 + difference 1 3) (sourceB761 + difference 3 1) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA761 + difference 1 3) (sourceB761 + difference 3 1) sourceC761) = raw12467 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12467; decide +kernel
    rw [ha]
    exact (canonical12467 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA761 + difference 1 4) (sourceB761 + difference 4 1) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA761 + difference 1 4) (sourceB761 + difference 4 1) sourceC761) = raw12654 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12654; decide +kernel
    rw [ha]
    exact (canonical12654 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA761 + difference 1 5) (sourceB761 + difference 5 1) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5283) := by
    have ha : (tripleCharges (sourceA761 + difference 1 5) (sourceB761 + difference 5 1) sourceC761) = raw12655 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12655; decide +kernel
    rw [ha]
    exact (canonical12655 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA761 + difference 2 0) (sourceB761 + difference 0 2) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA761 + difference 2 0) (sourceB761 + difference 0 2) sourceC761) = raw12002 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12002; decide +kernel
    rw [ha]
    exact (canonical12002 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA761 + difference 2 1) (sourceB761 + difference 1 2) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA761 + difference 2 1) (sourceB761 + difference 1 2) sourceC761) = raw11674 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw11674; decide +kernel
    rw [ha]
    exact (canonical11674 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA761 + difference 2 3) (sourceB761 + difference 3 2) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA761 + difference 2 3) (sourceB761 + difference 3 2) sourceC761) = raw12003 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12003; decide +kernel
    rw [ha]
    exact (canonical12003 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA761 + difference 2 4) (sourceB761 + difference 4 2) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA761 + difference 2 4) (sourceB761 + difference 4 2) sourceC761) = raw12004 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12004; decide +kernel
    rw [ha]
    exact (canonical12004 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA761 + difference 2 5) (sourceB761 + difference 5 2) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA761 + difference 2 5) (sourceB761 + difference 5 2) sourceC761) = raw12005 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12005; decide +kernel
    rw [ha]
    exact (canonical12005 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA761 + difference 3 0) (sourceB761 + difference 0 3) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA761 + difference 3 0) (sourceB761 + difference 0 3) sourceC761) = raw12656 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12656; decide +kernel
    rw [ha]
    exact (canonical12656 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA761 + difference 3 1) (sourceB761 + difference 1 3) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA761 + difference 3 1) (sourceB761 + difference 1 3) sourceC761) = raw11679 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw11679; decide +kernel
    rw [ha]
    exact (canonical11679 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA761 + difference 3 2) (sourceB761 + difference 2 3) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA761 + difference 3 2) (sourceB761 + difference 2 3) sourceC761) = raw12195 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12195; decide +kernel
    rw [ha]
    exact (canonical12195 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA761 + difference 3 4) (sourceB761 + difference 4 3) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA761 + difference 3 4) (sourceB761 + difference 4 3) sourceC761) = raw12657 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12657; decide +kernel
    rw [ha]
    exact (canonical12657 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA761 + difference 3 5) (sourceB761 + difference 5 3) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA761 + difference 3 5) (sourceB761 + difference 5 3) sourceC761) = raw12658 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12658; decide +kernel
    rw [ha]
    exact (canonical12658 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA761 + difference 4 0) (sourceB761 + difference 0 4) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA761 + difference 4 0) (sourceB761 + difference 0 4) sourceC761) = raw12659 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12659; decide +kernel
    rw [ha]
    exact (canonical12659 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA761 + difference 4 1) (sourceB761 + difference 1 4) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA761 + difference 4 1) (sourceB761 + difference 1 4) sourceC761) = raw11684 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw11684; decide +kernel
    rw [ha]
    exact (canonical11684 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA761 + difference 4 2) (sourceB761 + difference 2 4) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA761 + difference 4 2) (sourceB761 + difference 2 4) sourceC761) = raw12199 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12199; decide +kernel
    rw [ha]
    exact (canonical12199 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA761 + difference 4 3) (sourceB761 + difference 3 4) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA761 + difference 4 3) (sourceB761 + difference 3 4) sourceC761) = raw12473 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12473; decide +kernel
    rw [ha]
    exact (canonical12473 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA761 + difference 4 5) (sourceB761 + difference 5 4) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA761 + difference 4 5) (sourceB761 + difference 5 4) sourceC761) = raw12660 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12660; decide +kernel
    rw [ha]
    exact (canonical12660 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA761 + difference 5 0) (sourceB761 + difference 0 5) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA761 + difference 5 0) (sourceB761 + difference 0 5) sourceC761) = raw11665 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw11665; decide +kernel
    rw [ha]
    exact (canonical11665 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA761 + difference 5 1) (sourceB761 + difference 1 5) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA761 + difference 5 1) (sourceB761 + difference 1 5) sourceC761) = raw12019 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12019; decide +kernel
    rw [ha]
    exact (canonical12019 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA761 + difference 5 2) (sourceB761 + difference 2 5) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA761 + difference 5 2) (sourceB761 + difference 2 5) sourceC761) = raw11666 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw11666; decide +kernel
    rw [ha]
    exact (canonical11666 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA761 + difference 5 3) (sourceB761 + difference 3 5) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA761 + difference 5 3) (sourceB761 + difference 3 5) sourceC761) = raw11667 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw11667; decide +kernel
    rw [ha]
    exact (canonical11667 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA761 + difference 5 4) (sourceB761 + difference 4 5) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA761 + difference 5 4) (sourceB761 + difference 4 5) sourceC761) = raw11668 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw11668; decide +kernel
    rw [ha]
    exact (canonical11668 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA761 sourceB761 sourceC761
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm761, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq762 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm762 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA762 + difference 0 0) (sourceB762 + difference 0 0) sourceC762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3622) := by
    have ha : (tripleCharges (sourceA762 + difference 0 0) (sourceB762 + difference 0 0) sourceC762) = raw12661 := by
      apply Matrix.ext; unfold tripleCharges sourceA762 sourceB762 sourceC762 difference raw12661; decide +kernel
    rw [ha]
    exact (canonical12661 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA762 + difference 0 1) (sourceB762 + difference 1 0) sourceC762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA762 + difference 0 1) (sourceB762 + difference 1 0) sourceC762) = raw11755 := by
      apply Matrix.ext; unfold tripleCharges sourceA762 sourceB762 sourceC762 difference raw11755; decide +kernel
    rw [ha]
    exact (canonical11755 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA762 + difference 0 2) (sourceB762 + difference 2 0) sourceC762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3628) := by
    have ha : (tripleCharges (sourceA762 + difference 0 2) (sourceB762 + difference 2 0) sourceC762) = raw12229 := by
      apply Matrix.ext; unfold tripleCharges sourceA762 sourceB762 sourceC762 difference raw12229; decide +kernel
    rw [ha]
    exact (canonical12229 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA762 + difference 0 3) (sourceB762 + difference 3 0) sourceC762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA762 + difference 0 3) (sourceB762 + difference 3 0) sourceC762) = raw12515 := by
      apply Matrix.ext; unfold tripleCharges sourceA762 sourceB762 sourceC762 difference raw12515; decide +kernel
    rw [ha]
    exact (canonical12515 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA762 + difference 0 4) (sourceB762 + difference 4 0) sourceC762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA762 + difference 0 4) (sourceB762 + difference 4 0) sourceC762) = raw12662 := by
      apply Matrix.ext; unfold tripleCharges sourceA762 sourceB762 sourceC762 difference raw12662; decide +kernel
    rw [ha]
    exact (canonical12662 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA762 + difference 0 5) (sourceB762 + difference 5 0) sourceC762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3546) := by
    have ha : (tripleCharges (sourceA762 + difference 0 5) (sourceB762 + difference 5 0) sourceC762) = raw12663 := by
      apply Matrix.ext; unfold tripleCharges sourceA762 sourceB762 sourceC762 difference raw12663; decide +kernel
    rw [ha]
    exact (canonical12663 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA762 + sourceB762) sourceC762) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA762 + sourceB762) sourceC762) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA762 sourceB762 sourceC762 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA762 sourceB762 sourceC762
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm762, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq763 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm763 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA763 + difference 1 0) (sourceB763 + difference 0 1) sourceC763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA763 + difference 1 0) (sourceB763 + difference 0 1) sourceC763) = raw12664 := by
      apply Matrix.ext; unfold tripleCharges sourceA763 sourceB763 sourceC763 difference raw12664; decide +kernel
    rw [ha]
    exact (canonical12664 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA763 + difference 1 1) (sourceB763 + difference 1 1) sourceC763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3622) := by
    have ha : (tripleCharges (sourceA763 + difference 1 1) (sourceB763 + difference 1 1) sourceC763) = raw12661 := by
      apply Matrix.ext; unfold tripleCharges sourceA763 sourceB763 sourceC763 difference raw12661; decide +kernel
    rw [ha]
    exact (canonical12661 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA763 + difference 1 2) (sourceB763 + difference 2 1) sourceC763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3622) := by
    have ha : (tripleCharges (sourceA763 + difference 1 2) (sourceB763 + difference 2 1) sourceC763) = raw12665 := by
      apply Matrix.ext; unfold tripleCharges sourceA763 sourceB763 sourceC763 difference raw12665; decide +kernel
    rw [ha]
    exact (canonical12665 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA763 + difference 1 3) (sourceB763 + difference 3 1) sourceC763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA763 + difference 1 3) (sourceB763 + difference 3 1) sourceC763) = raw12520 := by
      apply Matrix.ext; unfold tripleCharges sourceA763 sourceB763 sourceC763 difference raw12520; decide +kernel
    rw [ha]
    exact (canonical12520 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA763 + difference 1 4) (sourceB763 + difference 4 1) sourceC763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA763 + difference 1 4) (sourceB763 + difference 4 1) sourceC763) = raw12666 := by
      apply Matrix.ext; unfold tripleCharges sourceA763 sourceB763 sourceC763 difference raw12666; decide +kernel
    rw [ha]
    exact (canonical12666 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA763 + difference 1 5) (sourceB763 + difference 5 1) sourceC763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3618) := by
    have ha : (tripleCharges (sourceA763 + difference 1 5) (sourceB763 + difference 5 1) sourceC763) = raw12667 := by
      apply Matrix.ext; unfold tripleCharges sourceA763 sourceB763 sourceC763 difference raw12667; decide +kernel
    rw [ha]
    exact (canonical12667 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA763 + sourceB763) sourceC763) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA763 + sourceB763) sourceC763) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA763 sourceB763 sourceC763 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA763 sourceB763 sourceC763
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm763, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm767 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA767 + difference 0 0) (sourceB767 + difference 0 0) sourceC767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA767 + difference 0 0) (sourceB767 + difference 0 0) sourceC767) = raw12758 := by
      apply Matrix.ext; unfold tripleCharges sourceA767 sourceB767 sourceC767 difference raw12758; decide +kernel
    rw [ha]
    exact (canonical12758 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA767 + difference 1 0) (sourceB767 + difference 0 1) sourceC767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1276) := by
    have ha : (tripleCharges (sourceA767 + difference 1 0) (sourceB767 + difference 0 1) sourceC767) = raw12759 := by
      apply Matrix.ext; unfold tripleCharges sourceA767 sourceB767 sourceC767 difference raw12759; decide +kernel
    rw [ha]
    exact (canonical12759 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA767 + difference 2 0) (sourceB767 + difference 0 2) sourceC767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA767 + difference 2 0) (sourceB767 + difference 0 2) sourceC767) = raw12760 := by
      apply Matrix.ext; unfold tripleCharges sourceA767 sourceB767 sourceC767 difference raw12760; decide +kernel
    rw [ha]
    exact (canonical12760 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA767 + difference 3 0) (sourceB767 + difference 0 3) sourceC767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1280) := by
    have ha : (tripleCharges (sourceA767 + difference 3 0) (sourceB767 + difference 0 3) sourceC767) = raw12761 := by
      apply Matrix.ext; unfold tripleCharges sourceA767 sourceB767 sourceC767 difference raw12761; decide +kernel
    rw [ha]
    exact (canonical12761 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA767 + difference 4 0) (sourceB767 + difference 0 4) sourceC767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1278) := by
    have ha : (tripleCharges (sourceA767 + difference 4 0) (sourceB767 + difference 0 4) sourceC767) = raw12762 := by
      apply Matrix.ext; unfold tripleCharges sourceA767 sourceB767 sourceC767 difference raw12762; decide +kernel
    rw [ha]
    exact (canonical12762 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA767 + difference 5 0) (sourceB767 + difference 0 5) sourceC767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1277) := by
    have ha : (tripleCharges (sourceA767 + difference 5 0) (sourceB767 + difference 0 5) sourceC767) = raw12763 := by
      apply Matrix.ext; unfold tripleCharges sourceA767 sourceB767 sourceC767 difference raw12763; decide +kernel
    rw [ha]
    exact (canonical12763 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA767 + sourceB767) sourceC767) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA767 + sourceB767) sourceC767) = raw12764 := by
      apply Matrix.ext; unfold doubleCharges sourceA767 sourceB767 sourceC767 raw12764; decide +kernel
    rw [ha]
    exact (canonical12764 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA767 sourceB767 sourceC767
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm767, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources24
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq771 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm771 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA771 + difference 0 0) (sourceB771 + difference 0 0) sourceC771) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA771 + difference 0 0) (sourceB771 + difference 0 0) sourceC771) = raw12855 := by
      apply Matrix.ext; unfold tripleCharges sourceA771 sourceB771 sourceC771 difference raw12855; decide +kernel
    rw [ha]
    exact (canonical12855 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA771 + difference 0 1) (sourceB771 + difference 1 0) sourceC771) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA771 + difference 0 1) (sourceB771 + difference 1 0) sourceC771) = raw12856 := by
      apply Matrix.ext; unfold tripleCharges sourceA771 sourceB771 sourceC771 difference raw12856; decide +kernel
    rw [ha]
    exact (canonical12856 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA771 + difference 0 2) (sourceB771 + difference 2 0) sourceC771) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA771 + difference 0 2) (sourceB771 + difference 2 0) sourceC771) = raw12857 := by
      apply Matrix.ext; unfold tripleCharges sourceA771 sourceB771 sourceC771 difference raw12857; decide +kernel
    rw [ha]
    exact (canonical12857 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA771 + difference 0 3) (sourceB771 + difference 3 0) sourceC771) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA771 + difference 0 3) (sourceB771 + difference 3 0) sourceC771) = raw12858 := by
      apply Matrix.ext; unfold tripleCharges sourceA771 sourceB771 sourceC771 difference raw12858; decide +kernel
    rw [ha]
    exact (canonical12858 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA771 + difference 0 4) (sourceB771 + difference 4 0) sourceC771) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA771 + difference 0 4) (sourceB771 + difference 4 0) sourceC771) = raw12859 := by
      apply Matrix.ext; unfold tripleCharges sourceA771 sourceB771 sourceC771 difference raw12859; decide +kernel
    rw [ha]
    exact (canonical12859 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA771 + difference 0 5) (sourceB771 + difference 5 0) sourceC771) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA771 + difference 0 5) (sourceB771 + difference 5 0) sourceC771) = raw12860 := by
      apply Matrix.ext; unfold tripleCharges sourceA771 sourceB771 sourceC771 difference raw12860; decide +kernel
    rw [ha]
    exact (canonical12860 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA771 + sourceB771) sourceC771) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA771 + sourceB771) sourceC771) = raw12861 := by
      apply Matrix.ext; unfold doubleCharges sourceA771 sourceB771 sourceC771 raw12861; decide +kernel
    rw [ha]
    exact (canonical12861 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA771 sourceB771 sourceC771
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm771, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq772 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm772 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA772 + difference 0 0) (sourceB772 + difference 0 0) sourceC772) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA772 + difference 0 0) (sourceB772 + difference 0 0) sourceC772) = raw12855 := by
      apply Matrix.ext; unfold tripleCharges sourceA772 sourceB772 sourceC772 difference raw12855; decide +kernel
    rw [ha]
    exact (canonical12855 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA772 + difference 1 0) (sourceB772 + difference 0 1) sourceC772) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1364) := by
    have ha : (tripleCharges (sourceA772 + difference 1 0) (sourceB772 + difference 0 1) sourceC772) = raw12862 := by
      apply Matrix.ext; unfold tripleCharges sourceA772 sourceB772 sourceC772 difference raw12862; decide +kernel
    rw [ha]
    exact (canonical12862 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA772 + difference 2 0) (sourceB772 + difference 0 2) sourceC772) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1433) := by
    have ha : (tripleCharges (sourceA772 + difference 2 0) (sourceB772 + difference 0 2) sourceC772) = raw12863 := by
      apply Matrix.ext; unfold tripleCharges sourceA772 sourceB772 sourceC772 difference raw12863; decide +kernel
    rw [ha]
    exact (canonical12863 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA772 + difference 3 0) (sourceB772 + difference 0 3) sourceC772) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1367) := by
    have ha : (tripleCharges (sourceA772 + difference 3 0) (sourceB772 + difference 0 3) sourceC772) = raw12864 := by
      apply Matrix.ext; unfold tripleCharges sourceA772 sourceB772 sourceC772 difference raw12864; decide +kernel
    rw [ha]
    exact (canonical12864 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA772 + difference 4 0) (sourceB772 + difference 0 4) sourceC772) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1368) := by
    have ha : (tripleCharges (sourceA772 + difference 4 0) (sourceB772 + difference 0 4) sourceC772) = raw12865 := by
      apply Matrix.ext; unfold tripleCharges sourceA772 sourceB772 sourceC772 difference raw12865; decide +kernel
    rw [ha]
    exact (canonical12865 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA772 + difference 5 0) (sourceB772 + difference 0 5) sourceC772) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1371) := by
    have ha : (tripleCharges (sourceA772 + difference 5 0) (sourceB772 + difference 0 5) sourceC772) = raw12866 := by
      apply Matrix.ext; unfold tripleCharges sourceA772 sourceB772 sourceC772 difference raw12866; decide +kernel
    rw [ha]
    exact (canonical12866 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA772 + sourceB772) sourceC772) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA772 + sourceB772) sourceC772) = raw12861 := by
      apply Matrix.ext; unfold doubleCharges sourceA772 sourceB772 sourceC772 raw12861; decide +kernel
    rw [ha]
    exact (canonical12861 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA772 sourceB772 sourceC772
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm772, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq773 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm773 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA773 + difference 1 0) (sourceB773 + difference 0 1) sourceC773) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1364) := by
    have ha : (tripleCharges (sourceA773 + difference 1 0) (sourceB773 + difference 0 1) sourceC773) = raw12862 := by
      apply Matrix.ext; unfold tripleCharges sourceA773 sourceB773 sourceC773 difference raw12862; decide +kernel
    rw [ha]
    exact (canonical12862 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA773 + difference 1 1) (sourceB773 + difference 1 1) sourceC773) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA773 + difference 1 1) (sourceB773 + difference 1 1) sourceC773) = raw12855 := by
      apply Matrix.ext; unfold tripleCharges sourceA773 sourceB773 sourceC773 difference raw12855; decide +kernel
    rw [ha]
    exact (canonical12855 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA773 + difference 1 2) (sourceB773 + difference 2 1) sourceC773) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2878) := by
    have ha : (tripleCharges (sourceA773 + difference 1 2) (sourceB773 + difference 2 1) sourceC773) = raw12867 := by
      apply Matrix.ext; unfold tripleCharges sourceA773 sourceB773 sourceC773 difference raw12867; decide +kernel
    rw [ha]
    exact (canonical12867 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA773 + difference 1 3) (sourceB773 + difference 3 1) sourceC773) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3043) := by
    have ha : (tripleCharges (sourceA773 + difference 1 3) (sourceB773 + difference 3 1) sourceC773) = raw12868 := by
      apply Matrix.ext; unfold tripleCharges sourceA773 sourceB773 sourceC773 difference raw12868; decide +kernel
    rw [ha]
    exact (canonical12868 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA773 + difference 1 4) (sourceB773 + difference 4 1) sourceC773) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3036) := by
    have ha : (tripleCharges (sourceA773 + difference 1 4) (sourceB773 + difference 4 1) sourceC773) = raw12869 := by
      apply Matrix.ext; unfold tripleCharges sourceA773 sourceB773 sourceC773 difference raw12869; decide +kernel
    rw [ha]
    exact (canonical12869 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA773 + difference 1 5) (sourceB773 + difference 5 1) sourceC773) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA773 + difference 1 5) (sourceB773 + difference 5 1) sourceC773) = raw12870 := by
      apply Matrix.ext; unfold tripleCharges sourceA773 sourceB773 sourceC773 difference raw12870; decide +kernel
    rw [ha]
    exact (canonical12870 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA773 + sourceB773) sourceC773) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA773 + sourceB773) sourceC773) = raw12861 := by
      apply Matrix.ext; unfold doubleCharges sourceA773 sourceB773 sourceC773 raw12861; decide +kernel
    rw [ha]
    exact (canonical12861 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA773 sourceB773 sourceC773
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm773, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck660 : Integer.Sparse.reindex keyMap MixedData.row660 = numericRow660 := by decide +kernel

theorem numericCheck660 (x : Master → ℝ) : Integer.Sparse.eval numericRow660 x =
    (17280 : ℝ) * reducedSource660 x := by
  norm_num [numericRow660, reducedSource660, Integer.Sparse.eval, Sparse.eval, nodeValue4887, nodeValue4888, nodeValue4889, nodeValue4893, nodeValue5256, nodeValue5257, nodeValue5265, nodeValue5271, nodeValue5273, nodeValue5281, nodeValue5283, nodeValue5289, nodeValue5290, nodeValue5292, nodeValue5299, nodeValue5301, nodeValue5306, nodeValue5307]
  ring

theorem reindexCheck661 : Integer.Sparse.reindex keyMap MixedData.row661 = numericRow661 := by decide +kernel

theorem numericCheck661 (x : Master → ℝ) : Integer.Sparse.eval numericRow661 x =
    (1 : ℝ) * reducedSource661 x := by
  norm_num [numericRow661, reducedSource661, Integer.Sparse.eval, Sparse.eval, nodeValue3532, nodeValue3534, nodeValue3546, nodeValue3622, nodeValue3628, nodeValue4083]

theorem reindexCheck662 : Integer.Sparse.reindex keyMap MixedData.row662 = numericRow662 := by decide +kernel

theorem numericCheck662 (x : Master → ℝ) : Integer.Sparse.eval numericRow662 x =
    (1 : ℝ) * reducedSource662 x := by
  norm_num [numericRow662, reducedSource662, Integer.Sparse.eval, Sparse.eval, nodeValue2243, nodeValue3571, nodeValue3618, nodeValue3622, nodeValue4083]

theorem reindexCheck665 : Integer.Sparse.reindex keyMap MixedData.row665 = numericRow665 := by decide +kernel

theorem numericCheck665 (x : Master → ℝ) : Integer.Sparse.eval numericRow665 x =
    (1 : ℝ) * reducedSource665 x := by
  norm_num [numericRow665, reducedSource665, Integer.Sparse.eval, Sparse.eval, nodeValue1276, nodeValue1277, nodeValue1278, nodeValue1280, nodeValue1291, nodeValue2773, nodeValue4092]

theorem reindexCheck669 : Integer.Sparse.reindex keyMap MixedData.row669 = numericRow669 := by decide +kernel

theorem numericCheck669 (x : Master → ℝ) : Integer.Sparse.eval numericRow669 x =
    (1 : ℝ) * reducedSource669 x := by
  norm_num [numericRow669, reducedSource669, Integer.Sparse.eval, Sparse.eval, nodeValue3051, nodeValue3848, nodeValue3850, nodeValue3857, nodeValue3913, nodeValue3961, nodeValue4092]

theorem reindexCheck670 : Integer.Sparse.reindex keyMap MixedData.row670 = numericRow670 := by decide +kernel

theorem numericCheck670 (x : Master → ℝ) : Integer.Sparse.eval numericRow670 x =
    (1 : ℝ) * reducedSource670 x := by
  norm_num [numericRow670, reducedSource670, Integer.Sparse.eval, Sparse.eval, nodeValue1364, nodeValue1367, nodeValue1368, nodeValue1371, nodeValue1433, nodeValue3051, nodeValue4092]

theorem reindexCheck671 : Integer.Sparse.reindex keyMap MixedData.row671 = numericRow671 := by decide +kernel

theorem numericCheck671 (x : Master → ℝ) : Integer.Sparse.eval numericRow671 x =
    (1 : ℝ) * reducedSource671 x := by
  norm_num [numericRow671, reducedSource671, Integer.Sparse.eval, Sparse.eval, nodeValue1364, nodeValue2878, nodeValue3036, nodeValue3043, nodeValue3051, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero660 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource660 (mixedVector B) = 0 := by
  have h4887 : mixedVector B (Sum.inr 4887) = Sparse.eval nodeValue4887 (mixedVector B) := by
    change mixedMoment B node4887 node4887Labels = _
    exact sound4887 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4893 : mixedVector B (Sum.inr 4893) = Sparse.eval nodeValue4893 (mixedVector B) := by
    change mixedMoment B node4893 node4893Labels = _
    exact sound4893 B hB hF
  have h5256 : mixedVector B (Sum.inr 5256) = Sparse.eval nodeValue5256 (mixedVector B) := by
    change mixedMoment B node5256 node5256Labels = _
    exact sound5256 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5273 : mixedVector B (Sum.inr 5273) = Sparse.eval nodeValue5273 (mixedVector B) := by
    change mixedMoment B node5273 node5273Labels = _
    exact sound5273 B hB hF
  have h5281 : mixedVector B (Sum.inr 5281) = Sparse.eval nodeValue5281 (mixedVector B) := by
    change mixedMoment B node5281 node5281Labels = _
    exact sound5281 B hB hF
  have h5283 : mixedVector B (Sum.inr 5283) = Sparse.eval nodeValue5283 (mixedVector B) := by
    change mixedMoment B node5283 node5283Labels = _
    exact sound5283 B hB hF
  have h5289 : mixedVector B (Sum.inr 5289) = Sparse.eval nodeValue5289 (mixedVector B) := by
    change mixedMoment B node5289 node5289Labels = _
    exact sound5289 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  have h5299 : mixedVector B (Sum.inr 5299) = Sparse.eval nodeValue5299 (mixedVector B) := by
    change mixedMoment B node5299 node5299Labels = _
    exact sound5299 B hB hF
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  have h5307 : mixedVector B (Sum.inr 5307) = Sparse.eval nodeValue5307 (mixedVector B) := by
    change mixedMoment B node5307 node5307Labels = _
    exact sound5307 B hB hF
  simpa only [sourceForm761, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4887, h4888, h4889, h4893, h5256, h5257, h5265, h5271, h5273, h5281, h5283, h5289, h5290, h5292, h5299, h5301, h5306, h5307, reducedSource660] using sourceEq761 B hB

theorem rowSound660 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row660 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck660, numericCheck660, reducedZero660 B hB hF, mul_zero]

theorem reducedZero661 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource661 (mixedVector B) = 0 := by
  have h3532 : mixedVector B (Sum.inr 3532) = Sparse.eval nodeValue3532 (mixedVector B) := by
    change mixedMoment B node3532 node3532Labels = _
    exact sound3532 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3546 : mixedVector B (Sum.inr 3546) = Sparse.eval nodeValue3546 (mixedVector B) := by
    change mixedMoment B node3546 node3546Labels = _
    exact sound3546 B hB hF
  have h3622 : mixedVector B (Sum.inr 3622) = Sparse.eval nodeValue3622 (mixedVector B) := by
    change mixedMoment B node3622 node3622Labels = _
    exact sound3622 B hB hF
  have h3628 : mixedVector B (Sum.inr 3628) = Sparse.eval nodeValue3628 (mixedVector B) := by
    change mixedMoment B node3628 node3628Labels = _
    exact sound3628 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm762, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3532, h3534, h3546, h3622, h3628, h4083, reducedSource661] using sourceEq762 B hB

theorem rowSound661 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row661 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck661, numericCheck661, reducedZero661 B hB hF, mul_zero]

theorem reducedZero662 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource662 (mixedVector B) = 0 := by
  have h2243 : mixedVector B (Sum.inr 2243) = Sparse.eval nodeValue2243 (mixedVector B) := by
    change mixedMoment B node2243 node2243Labels = _
    exact sound2243 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h3618 : mixedVector B (Sum.inr 3618) = Sparse.eval nodeValue3618 (mixedVector B) := by
    change mixedMoment B node3618 node3618Labels = _
    exact sound3618 B hB hF
  have h3622 : mixedVector B (Sum.inr 3622) = Sparse.eval nodeValue3622 (mixedVector B) := by
    change mixedMoment B node3622 node3622Labels = _
    exact sound3622 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm763, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2243, h3571, h3618, h3622, h4083, reducedSource662] using sourceEq763 B hB

theorem rowSound662 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row662 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck662, numericCheck662, reducedZero662 B hB hF, mul_zero]

theorem reducedZero665 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource665 (mixedVector B) = 0 := by
  have h1276 : mixedVector B (Sum.inr 1276) = Sparse.eval nodeValue1276 (mixedVector B) := by
    change mixedMoment B node1276 node1276Labels = _
    exact sound1276 B hB hF
  have h1277 : mixedVector B (Sum.inr 1277) = Sparse.eval nodeValue1277 (mixedVector B) := by
    change mixedMoment B node1277 node1277Labels = _
    exact sound1277 B hB hF
  have h1278 : mixedVector B (Sum.inr 1278) = Sparse.eval nodeValue1278 (mixedVector B) := by
    change mixedMoment B node1278 node1278Labels = _
    exact sound1278 B hB hF
  have h1280 : mixedVector B (Sum.inr 1280) = Sparse.eval nodeValue1280 (mixedVector B) := by
    change mixedMoment B node1280 node1280Labels = _
    exact sound1280 B hB hF
  have h1291 : mixedVector B (Sum.inr 1291) = Sparse.eval nodeValue1291 (mixedVector B) := by
    change mixedMoment B node1291 node1291Labels = _
    exact sound1291 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm767, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1276, h1277, h1278, h1280, h1291, h2773, h4092, reducedSource665] using sourceEq767 B hB

theorem rowSound665 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row665 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck665, numericCheck665, reducedZero665 B hB hF, mul_zero]

theorem reducedZero669 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource669 (mixedVector B) = 0 := by
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h3913 : mixedVector B (Sum.inr 3913) = Sparse.eval nodeValue3913 (mixedVector B) := by
    change mixedMoment B node3913 node3913Labels = _
    exact sound3913 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm771, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3051, h3848, h3850, h3857, h3913, h3961, h4092, reducedSource669] using sourceEq771 B hB

theorem rowSound669 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row669 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck669, numericCheck669, reducedZero669 B hB hF, mul_zero]

theorem reducedZero670 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource670 (mixedVector B) = 0 := by
  have h1364 : mixedVector B (Sum.inr 1364) = Sparse.eval nodeValue1364 (mixedVector B) := by
    change mixedMoment B node1364 node1364Labels = _
    exact sound1364 B hB hF
  have h1367 : mixedVector B (Sum.inr 1367) = Sparse.eval nodeValue1367 (mixedVector B) := by
    change mixedMoment B node1367 node1367Labels = _
    exact sound1367 B hB hF
  have h1368 : mixedVector B (Sum.inr 1368) = Sparse.eval nodeValue1368 (mixedVector B) := by
    change mixedMoment B node1368 node1368Labels = _
    exact sound1368 B hB hF
  have h1371 : mixedVector B (Sum.inr 1371) = Sparse.eval nodeValue1371 (mixedVector B) := by
    change mixedMoment B node1371 node1371Labels = _
    exact sound1371 B hB hF
  have h1433 : mixedVector B (Sum.inr 1433) = Sparse.eval nodeValue1433 (mixedVector B) := by
    change mixedMoment B node1433 node1433Labels = _
    exact sound1433 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm772, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1364, h1367, h1368, h1371, h1433, h3051, h4092, reducedSource670] using sourceEq772 B hB

theorem rowSound670 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row670 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck670, numericCheck670, reducedZero670 B hB hF, mul_zero]

theorem reducedZero671 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource671 (mixedVector B) = 0 := by
  have h1364 : mixedVector B (Sum.inr 1364) = Sparse.eval nodeValue1364 (mixedVector B) := by
    change mixedMoment B node1364 node1364Labels = _
    exact sound1364 B hB hF
  have h2878 : mixedVector B (Sum.inr 2878) = Sparse.eval nodeValue2878 (mixedVector B) := by
    change mixedMoment B node2878 node2878Labels = _
    exact sound2878 B hB hF
  have h3036 : mixedVector B (Sum.inr 3036) = Sparse.eval nodeValue3036 (mixedVector B) := by
    change mixedMoment B node3036 node3036Labels = _
    exact sound3036 B hB hF
  have h3043 : mixedVector B (Sum.inr 3043) = Sparse.eval nodeValue3043 (mixedVector B) := by
    change mixedMoment B node3043 node3043Labels = _
    exact sound3043 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm773, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1364, h2878, h3036, h3043, h3051, h4092, reducedSource671] using sourceEq773 B hB

theorem rowSound671 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row671 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck671, numericCheck671, reducedZero671 B hB hF, mul_zero]

theorem sourceRowsAt656 : MixedData.sourceRows (656 : Fin 2425) =
    MixedData.row656 := by decide +kernel

theorem sourceRowsAt657 : MixedData.sourceRows (657 : Fin 2425) =
    MixedData.row657 := by decide +kernel

theorem sourceRowsAt658 : MixedData.sourceRows (658 : Fin 2425) =
    MixedData.row658 := by decide +kernel

theorem sourceRowsAt659 : MixedData.sourceRows (659 : Fin 2425) =
    MixedData.row659 := by decide +kernel

theorem sourceRowsAt660 : MixedData.sourceRows (660 : Fin 2425) =
    MixedData.row660 := by decide +kernel

theorem sourceRowsAt661 : MixedData.sourceRows (661 : Fin 2425) =
    MixedData.row661 := by decide +kernel

theorem sourceRowsAt662 : MixedData.sourceRows (662 : Fin 2425) =
    MixedData.row662 := by decide +kernel

theorem sourceRowsAt663 : MixedData.sourceRows (663 : Fin 2425) =
    MixedData.row663 := by decide +kernel

theorem sourceRowsAt664 : MixedData.sourceRows (664 : Fin 2425) =
    MixedData.row664 := by decide +kernel

theorem sourceRowsAt665 : MixedData.sourceRows (665 : Fin 2425) =
    MixedData.row665 := by decide +kernel

theorem sourceRowsAt666 : MixedData.sourceRows (666 : Fin 2425) =
    MixedData.row666 := by decide +kernel

theorem sourceRowsAt667 : MixedData.sourceRows (667 : Fin 2425) =
    MixedData.row667 := by decide +kernel

theorem sourceRowsAt668 : MixedData.sourceRows (668 : Fin 2425) =
    MixedData.row668 := by decide +kernel

theorem sourceRowsAt669 : MixedData.sourceRows (669 : Fin 2425) =
    MixedData.row669 := by decide +kernel

theorem sourceRowsAt670 : MixedData.sourceRows (670 : Fin 2425) =
    MixedData.row670 := by decide +kernel

theorem sourceRowsAt671 : MixedData.sourceRows (671 : Fin 2425) =
    MixedData.row671 := by decide +kernel

theorem chunkSound41_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 41) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 656 ∨ k.val = 657 ∨ k.val = 658 ∨ k.val = 659 ∨ k.val = 660 ∨ k.val = 661 ∨ k.val = 662 ∨ k.val = 663 ∨ k.val = 664 ∨ k.val = 665 ∨ k.val = 666 ∨ k.val = 667 ∨ k.val = 668 ∨ k.val = 669 ∨ k.val = 670 ∨ k.val = 671 := by omega
  rcases heq with h656 | h657 | h658 | h659 | h660 | h661 | h662 | h663 | h664 | h665 | h666 | h667 | h668 | h669 | h670 | h671
  · have he : k = (656 : Fin 2425) := Fin.ext h656
    subst k
    rw [sourceRowsAt656]
    exact rowSound656_e B hB hF
  · have he : k = (657 : Fin 2425) := Fin.ext h657
    subst k
    rw [sourceRowsAt657]
    exact rowSound657_e B hB hF
  · have he : k = (658 : Fin 2425) := Fin.ext h658
    subst k
    rw [sourceRowsAt658]
    exact rowSound658_e B hB hF
  · have he : k = (659 : Fin 2425) := Fin.ext h659
    subst k
    rw [sourceRowsAt659]
    exact rowSound659_e B hB hF
  · have he : k = (660 : Fin 2425) := Fin.ext h660
    subst k
    rw [sourceRowsAt660]
    exact rowSound660 B hB hF
  · have he : k = (661 : Fin 2425) := Fin.ext h661
    subst k
    rw [sourceRowsAt661]
    exact rowSound661 B hB hF
  · have he : k = (662 : Fin 2425) := Fin.ext h662
    subst k
    rw [sourceRowsAt662]
    exact rowSound662 B hB hF
  · have he : k = (663 : Fin 2425) := Fin.ext h663
    subst k
    rw [sourceRowsAt663]
    exact rowSound663_e B hB hF
  · have he : k = (664 : Fin 2425) := Fin.ext h664
    subst k
    rw [sourceRowsAt664]
    exact rowSound664_e B hB hF
  · have he : k = (665 : Fin 2425) := Fin.ext h665
    subst k
    rw [sourceRowsAt665]
    exact rowSound665 B hB hF
  · have he : k = (666 : Fin 2425) := Fin.ext h666
    subst k
    rw [sourceRowsAt666]
    exact rowSound666_e B hB hF
  · have he : k = (667 : Fin 2425) := Fin.ext h667
    subst k
    rw [sourceRowsAt667]
    exact rowSound667_e B hB hF
  · have he : k = (668 : Fin 2425) := Fin.ext h668
    subst k
    rw [sourceRowsAt668]
    exact rowSound668_e B hB hF
  · have he : k = (669 : Fin 2425) := Fin.ext h669
    subst k
    rw [sourceRowsAt669]
    exact rowSound669 B hB hF
  · have he : k = (670 : Fin 2425) := Fin.ext h670
    subst k
    rw [sourceRowsAt670]
    exact rowSound670 B hB hF
  · have he : k = (671 : Fin 2425) := Fin.ext h671
    subst k
    rw [sourceRowsAt671]
    exact rowSound671 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e_oai
