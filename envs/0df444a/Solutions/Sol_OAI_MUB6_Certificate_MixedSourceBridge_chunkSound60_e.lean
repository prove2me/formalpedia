-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:26:14.43321+00:00
-- url     : https://prove2.me/submissions/2621b02a-bfca-4d8f-ae23-b6aa5c93e3cc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E129
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5292_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5416_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5433_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5450_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5476_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5482_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5483_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5485_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5490_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5500_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound962_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound963_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound964_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound965_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound966_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound967_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound968_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound970_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound971_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound972_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound973_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound974_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound975_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical137
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17585 raw17585Labels = mixedMoment B node5500 node5500Labels := by
  calc
    mixedMoment B raw17585 raw17585Labels = mixedMoment B raw17585step0 raw17585step0Labels := by
      have ha : raw17585step0 = (fun i j => raw17585 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17585step0 raw17585; decide +kernel
      have hl : raw17585step0Labels = raw17585Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17585 raw17585Labels permutation153 permutation2
    _ = mixedMoment B node5500 node5500Labels := by rfl

theorem canonical17593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17593 raw17593Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw17593 raw17593Labels = mixedMoment B raw17593step0 raw17593step0Labels := by
      have ha : raw17593step0 = (fun i j => raw17593 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17593step0 raw17593; decide +kernel
      have hl : raw17593step0Labels = raw17593Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17593 raw17593Labels permutation161 permutation3
    mixedMoment B raw17593step0 raw17593step0Labels = mixedMoment B raw17593step1 raw17593step1Labels := by
      have ha : raw17593step1 = raw17593step0 := by apply Matrix.ext; unfold raw17593step1 raw17593step0; decide +kernel
      have hl : raw17593step0Labels = labelEmbedding6 ∘ raw17593step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17593step0 raw17593step0Labels raw17593step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical17594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17594 raw17594Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw17594 raw17594Labels = mixedMoment B raw17594step0 raw17594step0Labels := by
      have ha : raw17594step0 = (fun i j => raw17594 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17594step0 raw17594; decide +kernel
      have hl : raw17594step0Labels = raw17594Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17594 raw17594Labels permutation265 permutation3
    mixedMoment B raw17594step0 raw17594step0Labels = mixedMoment B raw17594step1 raw17594step1Labels := by
      have ha : raw17594step1 = raw17594step0 := by apply Matrix.ext; unfold raw17594step1 raw17594step0; decide +kernel
      have hl : raw17594step0Labels = labelEmbedding6 ∘ raw17594step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17594step0 raw17594step0Labels raw17594step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

theorem canonical17595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17595 raw17595Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw17595 raw17595Labels = mixedMoment B raw17595step0 raw17595step0Labels := by
      have ha : raw17595step0 = (fun i j => raw17595 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17595step0 raw17595; decide +kernel
      have hl : raw17595step0Labels = raw17595Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17595 raw17595Labels permutation664 permutation3
    mixedMoment B raw17595step0 raw17595step0Labels = mixedMoment B raw17595step1 raw17595step1Labels := by
      have ha : raw17595step1 = -raw17595step0 := by apply Matrix.ext; change ∀ i j, raw17595step1 i j = -(raw17595step0 i j); unfold raw17595step1 raw17595step0; decide +kernel
      have hl : raw17595step1Labels = raw17595step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17595step1 raw17595step1Labels = mixedMoment B raw17595step2 raw17595step2Labels := by
      have ha : raw17595step2 = raw17595step1 := by apply Matrix.ext; unfold raw17595step2 raw17595step1; decide +kernel
      have hl : raw17595step1Labels = labelEmbedding6 ∘ raw17595step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17595step1 raw17595step1Labels raw17595step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

theorem canonical17596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17596 raw17596Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17596 raw17596Labels = mixedMoment B raw17596step0 raw17596step0Labels := by
      have ha : raw17596step0 = (fun i j => raw17596 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17596step0 raw17596; decide +kernel
      have hl : raw17596step0Labels = raw17596Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17596 raw17596Labels permutation658 permutation3
    mixedMoment B raw17596step0 raw17596step0Labels = mixedMoment B raw17596step1 raw17596step1Labels := by
      have ha : raw17596step1 = -raw17596step0 := by apply Matrix.ext; change ∀ i j, raw17596step1 i j = -(raw17596step0 i j); unfold raw17596step1 raw17596step0; decide +kernel
      have hl : raw17596step1Labels = raw17596step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17596step1 raw17596step1Labels = mixedMoment B raw17596step2 raw17596step2Labels := by
      have ha : raw17596step2 = raw17596step1 := by apply Matrix.ext; unfold raw17596step2 raw17596step1; decide +kernel
      have hl : raw17596step1Labels = labelEmbedding6 ∘ raw17596step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17596step1 raw17596step1Labels raw17596step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical17601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17601 raw17601Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw17601 raw17601Labels = mixedMoment B raw17601step0 raw17601step0Labels := by
      have ha : raw17601step0 = (fun i j => raw17601 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17601step0 raw17601; decide +kernel
      have hl : raw17601step0Labels = raw17601Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17601 raw17601Labels permutation159 permutation3
    mixedMoment B raw17601step0 raw17601step0Labels = mixedMoment B raw17601step1 raw17601step1Labels := by
      have ha : raw17601step1 = raw17601step0 := by apply Matrix.ext; unfold raw17601step1 raw17601step0; decide +kernel
      have hl : raw17601step0Labels = labelEmbedding6 ∘ raw17601step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17601step0 raw17601step0Labels raw17601step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18407 raw18407Labels = mixedMoment B node5479 node5479Labels := by
  calc
    mixedMoment B raw18407 raw18407Labels = mixedMoment B raw18407step0 raw18407step0Labels := by
      have ha : raw18407step0 = (fun i j => raw18407 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18407step0 raw18407; decide +kernel
      have hl : raw18407step0Labels = raw18407Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18407 raw18407Labels permutation152 permutation7
    mixedMoment B raw18407step0 raw18407step0Labels = mixedMoment B raw18407step1 raw18407step1Labels := by
      have ha : raw18407step1 = raw18407step0 := by apply Matrix.ext; unfold raw18407step1 raw18407step0; decide +kernel
      have hl : raw18407step0Labels = labelEmbedding10 ∘ raw18407step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18407step0 raw18407step0Labels raw18407step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5479 node5479Labels := by rfl

theorem canonical18408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18408 raw18408Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw18408 raw18408Labels = mixedMoment B raw18408step0 raw18408step0Labels := by
      have ha : raw18408step0 = (fun i j => raw18408 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18408step0 raw18408; decide +kernel
      have hl : raw18408step0Labels = raw18408Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18408 raw18408Labels permutation212 permutation4
    mixedMoment B raw18408step0 raw18408step0Labels = mixedMoment B raw18408step1 raw18408step1Labels := by
      have ha : raw18408step1 = -raw18408step0 := by apply Matrix.ext; change ∀ i j, raw18408step1 i j = -(raw18408step0 i j); unfold raw18408step1 raw18408step0; decide +kernel
      have hl : raw18408step1Labels = raw18408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18408step1 raw18408step1Labels = mixedMoment B raw18408step2 raw18408step2Labels := by
      have ha : raw18408step2 = raw18408step1 := by apply Matrix.ext; unfold raw18408step2 raw18408step1; decide +kernel
      have hl : raw18408step1Labels = labelEmbedding7 ∘ raw18408step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18408step1 raw18408step1Labels raw18408step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical18409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18409 raw18409Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18409 raw18409Labels = mixedMoment B raw18409step0 raw18409step0Labels := by
      have hz : ∀ j, raw18409 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18409step0 = (fun i j => raw18409 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18409step0 raw18409; decide +kernel
      have hl : raw18409step0Labels = raw18409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18409 raw18409Labels permutation346 hz
    mixedMoment B raw18409step0 raw18409step0Labels = mixedMoment B raw18409step1 raw18409step1Labels := by
      have ha : raw18409step1 = (fun i j => raw18409step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18409step1 raw18409step0; decide +kernel
      have hl : raw18409step1Labels = raw18409step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18409step0 raw18409step0Labels permutation32 permutation6
    mixedMoment B raw18409step1 raw18409step1Labels = mixedMoment B raw18409step2 raw18409step2Labels := by
      have ha : raw18409step2 = raw18409step1 := by apply Matrix.ext; unfold raw18409step2 raw18409step1; decide +kernel
      have hl : raw18409step1Labels = labelEmbedding9 ∘ raw18409step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18409step1 raw18409step1Labels raw18409step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical18410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18410 raw18410Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw18410 raw18410Labels = mixedMoment B raw18410step0 raw18410step0Labels := by
      have ha : raw18410step0 = (fun i j => raw18410 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18410step0 raw18410; decide +kernel
      have hl : raw18410step0Labels = raw18410Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18410 raw18410Labels permutation212 permutation4
    mixedMoment B raw18410step0 raw18410step0Labels = mixedMoment B raw18410step1 raw18410step1Labels := by
      have ha : raw18410step1 = -raw18410step0 := by apply Matrix.ext; change ∀ i j, raw18410step1 i j = -(raw18410step0 i j); unfold raw18410step1 raw18410step0; decide +kernel
      have hl : raw18410step1Labels = raw18410step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18410step1 raw18410step1Labels = mixedMoment B raw18410step2 raw18410step2Labels := by
      have ha : raw18410step2 = raw18410step1 := by apply Matrix.ext; unfold raw18410step2 raw18410step1; decide +kernel
      have hl : raw18410step1Labels = labelEmbedding7 ∘ raw18410step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18410step1 raw18410step1Labels raw18410step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical18411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18411 raw18411Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw18411 raw18411Labels = mixedMoment B raw18411step0 raw18411step0Labels := by
      have ha : raw18411step0 = (fun i j => raw18411 (permutation234 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18411step0 raw18411; decide +kernel
      have hl : raw18411step0Labels = raw18411Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18411 raw18411Labels permutation234 permutation4
    mixedMoment B raw18411step0 raw18411step0Labels = mixedMoment B raw18411step1 raw18411step1Labels := by
      have ha : raw18411step1 = -raw18411step0 := by apply Matrix.ext; change ∀ i j, raw18411step1 i j = -(raw18411step0 i j); unfold raw18411step1 raw18411step0; decide +kernel
      have hl : raw18411step1Labels = raw18411step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18411step1 raw18411step1Labels = mixedMoment B raw18411step2 raw18411step2Labels := by
      have ha : raw18411step2 = raw18411step1 := by apply Matrix.ext; unfold raw18411step2 raw18411step1; decide +kernel
      have hl : raw18411step1Labels = labelEmbedding7 ∘ raw18411step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18411step1 raw18411step1Labels raw18411step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical18417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18417 raw18417Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw18417 raw18417Labels = mixedMoment B raw18417step0 raw18417step0Labels := by
      have ha : raw18417step0 = (fun i j => raw18417 (permutation367 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18417step0 raw18417; decide +kernel
      have hl : raw18417step0Labels = raw18417Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18417 raw18417Labels permutation367 permutation3
    mixedMoment B raw18417step0 raw18417step0Labels = mixedMoment B raw18417step1 raw18417step1Labels := by
      have ha : raw18417step1 = -raw18417step0 := by apply Matrix.ext; change ∀ i j, raw18417step1 i j = -(raw18417step0 i j); unfold raw18417step1 raw18417step0; decide +kernel
      have hl : raw18417step1Labels = raw18417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18417step1 raw18417step1Labels = mixedMoment B raw18417step2 raw18417step2Labels := by
      have ha : raw18417step2 = raw18417step1 := by apply Matrix.ext; unfold raw18417step2 raw18417step1; decide +kernel
      have hl : raw18417step1Labels = labelEmbedding6 ∘ raw18417step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18417step1 raw18417step1Labels raw18417step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5437 node5437Labels := by rfl

theorem canonical18422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18422 raw18422Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18422 raw18422Labels = mixedMoment B raw18422step0 raw18422step0Labels := by
      have ha : raw18422step0 = (fun i j => raw18422 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18422step0 raw18422; decide +kernel
      have hl : raw18422step0Labels = raw18422Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18422 raw18422Labels permutation155 permutation6
    mixedMoment B raw18422step0 raw18422step0Labels = mixedMoment B raw18422step1 raw18422step1Labels := by
      have ha : raw18422step1 = raw18422step0 := by apply Matrix.ext; unfold raw18422step1 raw18422step0; decide +kernel
      have hl : raw18422step0Labels = labelEmbedding9 ∘ raw18422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18422step0 raw18422step0Labels raw18422step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical18427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18427 raw18427Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18427 raw18427Labels = mixedMoment B raw18427step0 raw18427step0Labels := by
      have ha : raw18427step0 = (fun i j => raw18427 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18427step0 raw18427; decide +kernel
      have hl : raw18427step0Labels = raw18427Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18427 raw18427Labels permutation153 permutation6
    mixedMoment B raw18427step0 raw18427step0Labels = mixedMoment B raw18427step1 raw18427step1Labels := by
      have ha : raw18427step1 = raw18427step0 := by apply Matrix.ext; unfold raw18427step1 raw18427step0; decide +kernel
      have hl : raw18427step0Labels = labelEmbedding9 ∘ raw18427step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18427step0 raw18427step0Labels raw18427step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical144
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18510 raw18510Labels = mixedMoment B node5474 node5474Labels := by
  calc
    mixedMoment B raw18510 raw18510Labels = mixedMoment B raw18510step0 raw18510step0Labels := by
      have hz : ∀ j, raw18510 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18510step0 = (fun i j => raw18510 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18510step0 raw18510; decide +kernel
      have hl : raw18510step0Labels = raw18510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18510 raw18510Labels permutation346 hz
    mixedMoment B raw18510step0 raw18510step0Labels = mixedMoment B raw18510step1 raw18510step1Labels := by
      have ha : raw18510step1 = (fun i j => raw18510step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18510step1 raw18510step0; decide +kernel
      have hl : raw18510step1Labels = raw18510step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18510step0 raw18510step0Labels permutation56 permutation2
    mixedMoment B raw18510step1 raw18510step1Labels = mixedMoment B raw18510step2 raw18510step2Labels := by
      have ha : raw18510step2 = -raw18510step1 := by apply Matrix.ext; change ∀ i j, raw18510step2 i j = -(raw18510step1 i j); unfold raw18510step2 raw18510step1; decide +kernel
      have hl : raw18510step2Labels = raw18510step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5474 node5474Labels := by rfl

theorem canonical18515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18515 raw18515Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw18515 raw18515Labels = mixedMoment B raw18515step0 raw18515step0Labels := by
      have hz : ∀ j, raw18515 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18515step0 = (fun i j => raw18515 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18515step0 raw18515; decide +kernel
      have hl : raw18515step0Labels = raw18515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18515 raw18515Labels permutation346 hz
    mixedMoment B raw18515step0 raw18515step0Labels = mixedMoment B raw18515step1 raw18515step1Labels := by
      have ha : raw18515step1 = (fun i j => raw18515step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18515step1 raw18515step0; decide +kernel
      have hl : raw18515step1Labels = raw18515step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18515step0 raw18515step0Labels permutation56 permutation3
    mixedMoment B raw18515step1 raw18515step1Labels = mixedMoment B raw18515step2 raw18515step2Labels := by
      have ha : raw18515step2 = -raw18515step1 := by apply Matrix.ext; change ∀ i j, raw18515step2 i j = -(raw18515step1 i j); unfold raw18515step2 raw18515step1; decide +kernel
      have hl : raw18515step2Labels = raw18515step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18515step2 raw18515step2Labels = mixedMoment B raw18515step3 raw18515step3Labels := by
      have ha : raw18515step3 = raw18515step2 := by apply Matrix.ext; unfold raw18515step3 raw18515step2; decide +kernel
      have hl : raw18515step2Labels = labelEmbedding6 ∘ raw18515step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18515step2 raw18515step2Labels raw18515step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical18516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18516 raw18516Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18516 raw18516Labels = mixedMoment B raw18516step0 raw18516step0Labels := by
      have ha : raw18516step0 = (fun i j => raw18516 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18516step0 raw18516; decide +kernel
      have hl : raw18516step0Labels = raw18516Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18516 raw18516Labels permutation152 permutation6
    mixedMoment B raw18516step0 raw18516step0Labels = mixedMoment B raw18516step1 raw18516step1Labels := by
      have ha : raw18516step1 = raw18516step0 := by apply Matrix.ext; unfold raw18516step1 raw18516step0; decide +kernel
      have hl : raw18516step0Labels = labelEmbedding9 ∘ raw18516step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18516step0 raw18516step0Labels raw18516step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical18520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18520 raw18520Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18520 raw18520Labels = mixedMoment B raw18520step0 raw18520step0Labels := by
      have hz : ∀ j, raw18520 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18520step0 = (fun i j => raw18520 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18520step0 raw18520; decide +kernel
      have hl : raw18520step0Labels = raw18520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18520 raw18520Labels permutation346 hz
    mixedMoment B raw18520step0 raw18520step0Labels = mixedMoment B raw18520step1 raw18520step1Labels := by
      have ha : raw18520step1 = (fun i j => raw18520step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18520step1 raw18520step0; decide +kernel
      have hl : raw18520step1Labels = raw18520step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18520step0 raw18520step0Labels permutation35 permutation6
    mixedMoment B raw18520step1 raw18520step1Labels = mixedMoment B raw18520step2 raw18520step2Labels := by
      have ha : raw18520step2 = raw18520step1 := by apply Matrix.ext; unfold raw18520step2 raw18520step1; decide +kernel
      have hl : raw18520step1Labels = labelEmbedding9 ∘ raw18520step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18520step1 raw18520step1Labels raw18520step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical18524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18524 raw18524Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18524 raw18524Labels = mixedMoment B raw18524step0 raw18524step0Labels := by
      have hz : ∀ j, raw18524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18524step0 = (fun i j => raw18524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18524step0 raw18524; decide +kernel
      have hl : raw18524step0Labels = raw18524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18524 raw18524Labels permutation346 hz
    mixedMoment B raw18524step0 raw18524step0Labels = mixedMoment B raw18524step1 raw18524step1Labels := by
      have ha : raw18524step1 = (fun i j => raw18524step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18524step1 raw18524step0; decide +kernel
      have hl : raw18524step1Labels = raw18524step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18524step0 raw18524step0Labels permutation33 permutation6
    mixedMoment B raw18524step1 raw18524step1Labels = mixedMoment B raw18524step2 raw18524step2Labels := by
      have ha : raw18524step2 = raw18524step1 := by apply Matrix.ext; unfold raw18524step2 raw18524step1; decide +kernel
      have hl : raw18524step1Labels = labelEmbedding9 ∘ raw18524step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18524step1 raw18524step1Labels raw18524step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical145
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18573 raw18573Labels = mixedMoment B node5427 node5427Labels := by
  calc
    mixedMoment B raw18573 raw18573Labels = mixedMoment B raw18573step0 raw18573step0Labels := by
      have ha : raw18573step0 = (fun i j => raw18573 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18573step0 raw18573; decide +kernel
      have hl : raw18573step0Labels = raw18573Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18573 raw18573Labels permutation265 permutation2
    _ = mixedMoment B node5427 node5427Labels := by rfl

theorem canonical18574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18574 raw18574Labels = mixedMoment B node5479 node5479Labels := by
  calc
    mixedMoment B raw18574 raw18574Labels = mixedMoment B raw18574step0 raw18574step0Labels := by
      have ha : raw18574step0 = (fun i j => raw18574 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18574step0 raw18574; decide +kernel
      have hl : raw18574step0Labels = raw18574Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18574 raw18574Labels permutation289 permutation7
    mixedMoment B raw18574step0 raw18574step0Labels = mixedMoment B raw18574step1 raw18574step1Labels := by
      have ha : raw18574step1 = -raw18574step0 := by apply Matrix.ext; change ∀ i j, raw18574step1 i j = -(raw18574step0 i j); unfold raw18574step1 raw18574step0; decide +kernel
      have hl : raw18574step1Labels = raw18574step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18574step1 raw18574step1Labels = mixedMoment B raw18574step2 raw18574step2Labels := by
      have ha : raw18574step2 = raw18574step1 := by apply Matrix.ext; unfold raw18574step2 raw18574step1; decide +kernel
      have hl : raw18574step1Labels = labelEmbedding10 ∘ raw18574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18574step1 raw18574step1Labels raw18574step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5479 node5479Labels := by rfl

theorem canonical18575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18575 raw18575Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw18575 raw18575Labels = mixedMoment B raw18575step0 raw18575step0Labels := by
      have ha : raw18575step0 = (fun i j => raw18575 (permutation292 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18575step0 raw18575; decide +kernel
      have hl : raw18575step0Labels = raw18575Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18575 raw18575Labels permutation292 permutation6
    mixedMoment B raw18575step0 raw18575step0Labels = mixedMoment B raw18575step1 raw18575step1Labels := by
      have ha : raw18575step1 = -raw18575step0 := by apply Matrix.ext; change ∀ i j, raw18575step1 i j = -(raw18575step0 i j); unfold raw18575step1 raw18575step0; decide +kernel
      have hl : raw18575step1Labels = raw18575step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18575step1 raw18575step1Labels = mixedMoment B raw18575step2 raw18575step2Labels := by
      have ha : raw18575step2 = raw18575step1 := by apply Matrix.ext; unfold raw18575step2 raw18575step1; decide +kernel
      have hl : raw18575step1Labels = labelEmbedding9 ∘ raw18575step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18575step1 raw18575step1Labels raw18575step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical18576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18576 raw18576Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw18576 raw18576Labels = mixedMoment B raw18576step0 raw18576step0Labels := by
      have ha : raw18576step0 = (fun i j => raw18576 (permutation290 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18576step0 raw18576; decide +kernel
      have hl : raw18576step0Labels = raw18576Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18576 raw18576Labels permutation290 permutation6
    mixedMoment B raw18576step0 raw18576step0Labels = mixedMoment B raw18576step1 raw18576step1Labels := by
      have ha : raw18576step1 = -raw18576step0 := by apply Matrix.ext; change ∀ i j, raw18576step1 i j = -(raw18576step0 i j); unfold raw18576step1 raw18576step0; decide +kernel
      have hl : raw18576step1Labels = raw18576step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18576step1 raw18576step1Labels = mixedMoment B raw18576step2 raw18576step2Labels := by
      have ha : raw18576step2 = raw18576step1 := by apply Matrix.ext; unfold raw18576step2 raw18576step1; decide +kernel
      have hl : raw18576step1Labels = labelEmbedding9 ∘ raw18576step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18576step1 raw18576step1Labels raw18576step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical18577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18577 raw18577Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw18577 raw18577Labels = mixedMoment B raw18577step0 raw18577step0Labels := by
      have ha : raw18577step0 = (fun i j => raw18577 (permutation289 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18577step0 raw18577; decide +kernel
      have hl : raw18577step0Labels = raw18577Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18577 raw18577Labels permutation289 permutation6
    mixedMoment B raw18577step0 raw18577step0Labels = mixedMoment B raw18577step1 raw18577step1Labels := by
      have ha : raw18577step1 = -raw18577step0 := by apply Matrix.ext; change ∀ i j, raw18577step1 i j = -(raw18577step0 i j); unfold raw18577step1 raw18577step0; decide +kernel
      have hl : raw18577step1Labels = raw18577step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18577step1 raw18577step1Labels = mixedMoment B raw18577step2 raw18577step2Labels := by
      have ha : raw18577step2 = raw18577step1 := by apply Matrix.ext; unfold raw18577step2 raw18577step1; decide +kernel
      have hl : raw18577step1Labels = labelEmbedding9 ∘ raw18577step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18577step1 raw18577step1Labels raw18577step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical18578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18578 raw18578Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw18578 raw18578Labels = mixedMoment B raw18578step0 raw18578step0Labels := by
      have ha : raw18578step0 = (fun i j => raw18578 (permutation217 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18578step0 raw18578; decide +kernel
      have hl : raw18578step0Labels = raw18578Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18578 raw18578Labels permutation217 permutation5
    mixedMoment B raw18578step0 raw18578step0Labels = mixedMoment B raw18578step1 raw18578step1Labels := by
      have ha : raw18578step1 = -raw18578step0 := by apply Matrix.ext; change ∀ i j, raw18578step1 i j = -(raw18578step0 i j); unfold raw18578step1 raw18578step0; decide +kernel
      have hl : raw18578step1Labels = raw18578step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18578step1 raw18578step1Labels = mixedMoment B raw18578step2 raw18578step2Labels := by
      have ha : raw18578step2 = raw18578step1 := by apply Matrix.ext; unfold raw18578step2 raw18578step1; decide +kernel
      have hl : raw18578step1Labels = labelEmbedding8 ∘ raw18578step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18578step1 raw18578step1Labels raw18578step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

theorem canonical18579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18579 raw18579Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw18579 raw18579Labels = mixedMoment B raw18579step0 raw18579step0Labels := by
      have ha : raw18579step0 = (fun i j => raw18579 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18579step0 raw18579; decide +kernel
      have hl : raw18579step0Labels = raw18579Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18579 raw18579Labels permutation176 permutation3
    mixedMoment B raw18579step0 raw18579step0Labels = mixedMoment B raw18579step1 raw18579step1Labels := by
      have ha : raw18579step1 = raw18579step0 := by apply Matrix.ext; unfold raw18579step1 raw18579step0; decide +kernel
      have hl : raw18579step0Labels = labelEmbedding6 ∘ raw18579step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18579step0 raw18579step0Labels raw18579step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5437 node5437Labels := by rfl

theorem canonical18580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18580 raw18580Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18580 raw18580Labels = mixedMoment B raw18580step0 raw18580step0Labels := by
      have ha : raw18580step0 = (fun i j => raw18580 (permutation302 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18580step0 raw18580; decide +kernel
      have hl : raw18580step0Labels = raw18580Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18580 raw18580Labels permutation302 permutation4
    mixedMoment B raw18580step0 raw18580step0Labels = mixedMoment B raw18580step1 raw18580step1Labels := by
      have ha : raw18580step1 = raw18580step0 := by apply Matrix.ext; unfold raw18580step1 raw18580step0; decide +kernel
      have hl : raw18580step0Labels = labelEmbedding7 ∘ raw18580step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18580step0 raw18580step0Labels raw18580step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical18581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18581 raw18581Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18581 raw18581Labels = mixedMoment B raw18581step0 raw18581step0Labels := by
      have ha : raw18581step0 = (fun i j => raw18581 (permutation298 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18581step0 raw18581; decide +kernel
      have hl : raw18581step0Labels = raw18581Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18581 raw18581Labels permutation298 permutation4
    mixedMoment B raw18581step0 raw18581step0Labels = mixedMoment B raw18581step1 raw18581step1Labels := by
      have ha : raw18581step1 = raw18581step0 := by apply Matrix.ext; unfold raw18581step1 raw18581step0; decide +kernel
      have hl : raw18581step0Labels = labelEmbedding7 ∘ raw18581step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18581step0 raw18581step0Labels raw18581step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical18582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18582 raw18582Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18582 raw18582Labels = mixedMoment B raw18582step0 raw18582step0Labels := by
      have ha : raw18582step0 = (fun i j => raw18582 (permutation297 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18582step0 raw18582; decide +kernel
      have hl : raw18582step0Labels = raw18582Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18582 raw18582Labels permutation297 permutation4
    mixedMoment B raw18582step0 raw18582step0Labels = mixedMoment B raw18582step1 raw18582step1Labels := by
      have ha : raw18582step1 = raw18582step0 := by apply Matrix.ext; unfold raw18582step1 raw18582step0; decide +kernel
      have hl : raw18582step0Labels = labelEmbedding7 ∘ raw18582step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18582step0 raw18582step0Labels raw18582step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical18583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18583 raw18583Labels = mixedMoment B node4863 node4863Labels := by
  calc
    mixedMoment B raw18583 raw18583Labels = mixedMoment B raw18583step0 raw18583step0Labels := by
      have ha : raw18583step0 = (fun i j => raw18583 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18583step0 raw18583; decide +kernel
      have hl : raw18583step0Labels = raw18583Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18583 raw18583Labels permutation161 permutation3
    mixedMoment B raw18583step0 raw18583step0Labels = mixedMoment B raw18583step1 raw18583step1Labels := by
      have ha : raw18583step1 = raw18583step0 := by apply Matrix.ext; unfold raw18583step1 raw18583step0; decide +kernel
      have hl : raw18583step0Labels = labelEmbedding6 ∘ raw18583step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18583step0 raw18583step0Labels raw18583step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4863 node4863Labels := by rfl

theorem canonical18584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18584 raw18584Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw18584 raw18584Labels = mixedMoment B raw18584step0 raw18584step0Labels := by
      have ha : raw18584step0 = (fun i j => raw18584 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18584step0 raw18584; decide +kernel
      have hl : raw18584step0Labels = raw18584Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18584 raw18584Labels permutation265 permutation2
    _ = mixedMoment B node5383 node5383Labels := by rfl

theorem canonical18585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18585 raw18585Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw18585 raw18585Labels = mixedMoment B raw18585step0 raw18585step0Labels := by
      have ha : raw18585step0 = (fun i j => raw18585 (permutation216 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18585step0 raw18585; decide +kernel
      have hl : raw18585step0Labels = raw18585Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18585 raw18585Labels permutation216 permutation5
    mixedMoment B raw18585step0 raw18585step0Labels = mixedMoment B raw18585step1 raw18585step1Labels := by
      have ha : raw18585step1 = -raw18585step0 := by apply Matrix.ext; change ∀ i j, raw18585step1 i j = -(raw18585step0 i j); unfold raw18585step1 raw18585step0; decide +kernel
      have hl : raw18585step1Labels = raw18585step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18585step1 raw18585step1Labels = mixedMoment B raw18585step2 raw18585step2Labels := by
      have ha : raw18585step2 = raw18585step1 := by apply Matrix.ext; unfold raw18585step2 raw18585step1; decide +kernel
      have hl : raw18585step1Labels = labelEmbedding8 ∘ raw18585step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18585step1 raw18585step1Labels raw18585step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical18586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18586 raw18586Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw18586 raw18586Labels = mixedMoment B raw18586step0 raw18586step0Labels := by
      have ha : raw18586step0 = (fun i j => raw18586 (permutation238 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18586step0 raw18586; decide +kernel
      have hl : raw18586step0Labels = raw18586Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18586 raw18586Labels permutation238 permutation5
    mixedMoment B raw18586step0 raw18586step0Labels = mixedMoment B raw18586step1 raw18586step1Labels := by
      have ha : raw18586step1 = -raw18586step0 := by apply Matrix.ext; change ∀ i j, raw18586step1 i j = -(raw18586step0 i j); unfold raw18586step1 raw18586step0; decide +kernel
      have hl : raw18586step1Labels = raw18586step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18586step1 raw18586step1Labels = mixedMoment B raw18586step2 raw18586step2Labels := by
      have ha : raw18586step2 = raw18586step1 := by apply Matrix.ext; unfold raw18586step2 raw18586step1; decide +kernel
      have hl : raw18586step1Labels = labelEmbedding8 ∘ raw18586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18586step1 raw18586step1Labels raw18586step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical18587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18587 raw18587Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw18587 raw18587Labels = mixedMoment B raw18587step0 raw18587step0Labels := by
      have ha : raw18587step0 = (fun i j => raw18587 (permutation258 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18587step0 raw18587; decide +kernel
      have hl : raw18587step0Labels = raw18587Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18587 raw18587Labels permutation258 permutation5
    mixedMoment B raw18587step0 raw18587step0Labels = mixedMoment B raw18587step1 raw18587step1Labels := by
      have ha : raw18587step1 = -raw18587step0 := by apply Matrix.ext; change ∀ i j, raw18587step1 i j = -(raw18587step0 i j); unfold raw18587step1 raw18587step0; decide +kernel
      have hl : raw18587step1Labels = raw18587step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18587step1 raw18587step1Labels = mixedMoment B raw18587step2 raw18587step2Labels := by
      have ha : raw18587step2 = raw18587step1 := by apply Matrix.ext; unfold raw18587step2 raw18587step1; decide +kernel
      have hl : raw18587step1Labels = labelEmbedding8 ∘ raw18587step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18587step1 raw18587step1Labels raw18587step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical18588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18588 raw18588Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw18588 raw18588Labels = mixedMoment B raw18588step0 raw18588step0Labels := by
      have ha : raw18588step0 = (fun i j => raw18588 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18588step0 raw18588; decide +kernel
      have hl : raw18588step0Labels = raw18588Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18588 raw18588Labels permutation155 permutation3
    mixedMoment B raw18588step0 raw18588step0Labels = mixedMoment B raw18588step1 raw18588step1Labels := by
      have ha : raw18588step1 = raw18588step0 := by apply Matrix.ext; unfold raw18588step1 raw18588step0; decide +kernel
      have hl : raw18588step0Labels = labelEmbedding6 ∘ raw18588step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18588step0 raw18588step0Labels raw18588step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

theorem canonical18589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18589 raw18589Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw18589 raw18589Labels = mixedMoment B raw18589step0 raw18589step0Labels := by
      have ha : raw18589step0 = (fun i j => raw18589 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18589step0 raw18589; decide +kernel
      have hl : raw18589step0Labels = raw18589Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18589 raw18589Labels permutation268 permutation2
    _ = mixedMoment B node5380 node5380Labels := by rfl

theorem canonical18590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18590 raw18590Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw18590 raw18590Labels = mixedMoment B raw18590step0 raw18590step0Labels := by
      have ha : raw18590step0 = (fun i j => raw18590 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18590step0 raw18590; decide +kernel
      have hl : raw18590step0Labels = raw18590Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18590 raw18590Labels permutation179 permutation3
    mixedMoment B raw18590step0 raw18590step0Labels = mixedMoment B raw18590step1 raw18590step1Labels := by
      have ha : raw18590step1 = raw18590step0 := by apply Matrix.ext; unfold raw18590step1 raw18590step0; decide +kernel
      have hl : raw18590step0Labels = labelEmbedding6 ∘ raw18590step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18590step0 raw18590step0Labels raw18590step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical18591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18591 raw18591Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18591 raw18591Labels = mixedMoment B raw18591step0 raw18591step0Labels := by
      have ha : raw18591step0 = (fun i j => raw18591 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18591step0 raw18591; decide +kernel
      have hl : raw18591step0Labels = raw18591Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18591 raw18591Labels permutation240 permutation5
    mixedMoment B raw18591step0 raw18591step0Labels = mixedMoment B raw18591step1 raw18591step1Labels := by
      have ha : raw18591step1 = -raw18591step0 := by apply Matrix.ext; change ∀ i j, raw18591step1 i j = -(raw18591step0 i j); unfold raw18591step1 raw18591step0; decide +kernel
      have hl : raw18591step1Labels = raw18591step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18591step1 raw18591step1Labels = mixedMoment B raw18591step2 raw18591step2Labels := by
      have ha : raw18591step2 = raw18591step1 := by apply Matrix.ext; unfold raw18591step2 raw18591step1; decide +kernel
      have hl : raw18591step1Labels = labelEmbedding8 ∘ raw18591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18591step1 raw18591step1Labels raw18591step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical18592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18592 raw18592Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18592 raw18592Labels = mixedMoment B raw18592step0 raw18592step0Labels := by
      have ha : raw18592step0 = (fun i j => raw18592 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18592step0 raw18592; decide +kernel
      have hl : raw18592step0Labels = raw18592Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18592 raw18592Labels permutation260 permutation5
    mixedMoment B raw18592step0 raw18592step0Labels = mixedMoment B raw18592step1 raw18592step1Labels := by
      have ha : raw18592step1 = -raw18592step0 := by apply Matrix.ext; change ∀ i j, raw18592step1 i j = -(raw18592step0 i j); unfold raw18592step1 raw18592step0; decide +kernel
      have hl : raw18592step1Labels = raw18592step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18592step1 raw18592step1Labels = mixedMoment B raw18592step2 raw18592step2Labels := by
      have ha : raw18592step2 = raw18592step1 := by apply Matrix.ext; unfold raw18592step2 raw18592step1; decide +kernel
      have hl : raw18592step1Labels = labelEmbedding8 ∘ raw18592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18592step1 raw18592step1Labels raw18592step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical18593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18593 raw18593Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw18593 raw18593Labels = mixedMoment B raw18593step0 raw18593step0Labels := by
      have ha : raw18593step0 = (fun i j => raw18593 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18593step0 raw18593; decide +kernel
      have hl : raw18593step0Labels = raw18593Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18593 raw18593Labels permutation153 permutation3
    mixedMoment B raw18593step0 raw18593step0Labels = mixedMoment B raw18593step1 raw18593step1Labels := by
      have ha : raw18593step1 = raw18593step0 := by apply Matrix.ext; unfold raw18593step1 raw18593step0; decide +kernel
      have hl : raw18593step0Labels = labelEmbedding6 ∘ raw18593step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18593step0 raw18593step0Labels raw18593step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

theorem canonical18594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18594 raw18594Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw18594 raw18594Labels = mixedMoment B raw18594step0 raw18594step0Labels := by
      have ha : raw18594step0 = (fun i j => raw18594 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18594step0 raw18594; decide +kernel
      have hl : raw18594step0Labels = raw18594Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18594 raw18594Labels permutation266 permutation2
    _ = mixedMoment B node5380 node5380Labels := by rfl

theorem canonical18595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18595 raw18595Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw18595 raw18595Labels = mixedMoment B raw18595step0 raw18595step0Labels := by
      have ha : raw18595step0 = (fun i j => raw18595 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18595step0 raw18595; decide +kernel
      have hl : raw18595step0Labels = raw18595Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18595 raw18595Labels permutation177 permutation3
    mixedMoment B raw18595step0 raw18595step0Labels = mixedMoment B raw18595step1 raw18595step1Labels := by
      have ha : raw18595step1 = raw18595step0 := by apply Matrix.ext; unfold raw18595step1 raw18595step0; decide +kernel
      have hl : raw18595step0Labels = labelEmbedding6 ∘ raw18595step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18595step0 raw18595step0Labels raw18595step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical18596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18596 raw18596Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18596 raw18596Labels = mixedMoment B raw18596step0 raw18596step0Labels := by
      have ha : raw18596step0 = (fun i j => raw18596 (permutation218 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18596step0 raw18596; decide +kernel
      have hl : raw18596step0Labels = raw18596Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18596 raw18596Labels permutation218 permutation5
    mixedMoment B raw18596step0 raw18596step0Labels = mixedMoment B raw18596step1 raw18596step1Labels := by
      have ha : raw18596step1 = -raw18596step0 := by apply Matrix.ext; change ∀ i j, raw18596step1 i j = -(raw18596step0 i j); unfold raw18596step1 raw18596step0; decide +kernel
      have hl : raw18596step1Labels = raw18596step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18596step1 raw18596step1Labels = mixedMoment B raw18596step2 raw18596step2Labels := by
      have ha : raw18596step2 = raw18596step1 := by apply Matrix.ext; unfold raw18596step2 raw18596step1; decide +kernel
      have hl : raw18596step1Labels = labelEmbedding8 ∘ raw18596step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18596step1 raw18596step1Labels raw18596step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical18597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18597 raw18597Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18597 raw18597Labels = mixedMoment B raw18597step0 raw18597step0Labels := by
      have ha : raw18597step0 = (fun i j => raw18597 (permutation257 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18597step0 raw18597; decide +kernel
      have hl : raw18597step0Labels = raw18597Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18597 raw18597Labels permutation257 permutation5
    mixedMoment B raw18597step0 raw18597step0Labels = mixedMoment B raw18597step1 raw18597step1Labels := by
      have ha : raw18597step1 = -raw18597step0 := by apply Matrix.ext; change ∀ i j, raw18597step1 i j = -(raw18597step0 i j); unfold raw18597step1 raw18597step0; decide +kernel
      have hl : raw18597step1Labels = raw18597step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18597step1 raw18597step1Labels = mixedMoment B raw18597step2 raw18597step2Labels := by
      have ha : raw18597step2 = raw18597step1 := by apply Matrix.ext; unfold raw18597step2 raw18597step1; decide +kernel
      have hl : raw18597step1Labels = labelEmbedding8 ∘ raw18597step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18597step1 raw18597step1Labels raw18597step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical18598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18598 raw18598Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw18598 raw18598Labels = mixedMoment B raw18598step0 raw18598step0Labels := by
      have ha : raw18598step0 = (fun i j => raw18598 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18598step0 raw18598; decide +kernel
      have hl : raw18598step0Labels = raw18598Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18598 raw18598Labels permutation152 permutation3
    mixedMoment B raw18598step0 raw18598step0Labels = mixedMoment B raw18598step1 raw18598step1Labels := by
      have ha : raw18598step1 = raw18598step0 := by apply Matrix.ext; unfold raw18598step1 raw18598step0; decide +kernel
      have hl : raw18598step0Labels = labelEmbedding6 ∘ raw18598step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18598step0 raw18598step0Labels raw18598step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

theorem canonical18599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18599 raw18599Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw18599 raw18599Labels = mixedMoment B raw18599step0 raw18599step0Labels := by
      have ha : raw18599step0 = (fun i j => raw18599 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18599step0 raw18599; decide +kernel
      have hl : raw18599step0Labels = raw18599Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18599 raw18599Labels permutation265 permutation2
    _ = mixedMoment B node5380 node5380Labels := by rfl

theorem canonical18600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18600 raw18600Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw18600 raw18600Labels = mixedMoment B raw18600step0 raw18600step0Labels := by
      have ha : raw18600step0 = (fun i j => raw18600 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18600step0 raw18600; decide +kernel
      have hl : raw18600step0Labels = raw18600Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18600 raw18600Labels permutation176 permutation3
    mixedMoment B raw18600step0 raw18600step0Labels = mixedMoment B raw18600step1 raw18600step1Labels := by
      have ha : raw18600step1 = raw18600step0 := by apply Matrix.ext; unfold raw18600step1 raw18600step0; decide +kernel
      have hl : raw18600step0Labels = labelEmbedding6 ∘ raw18600step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18600step0 raw18600step0Labels raw18600step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical18601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18601 raw18601Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18601 raw18601Labels = mixedMoment B raw18601step0 raw18601step0Labels := by
      have ha : raw18601step0 = (fun i j => raw18601 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18601step0 raw18601; decide +kernel
      have hl : raw18601step0Labels = raw18601Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18601 raw18601Labels permutation212 permutation5
    mixedMoment B raw18601step0 raw18601step0Labels = mixedMoment B raw18601step1 raw18601step1Labels := by
      have ha : raw18601step1 = -raw18601step0 := by apply Matrix.ext; change ∀ i j, raw18601step1 i j = -(raw18601step0 i j); unfold raw18601step1 raw18601step0; decide +kernel
      have hl : raw18601step1Labels = raw18601step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18601step1 raw18601step1Labels = mixedMoment B raw18601step2 raw18601step2Labels := by
      have ha : raw18601step2 = raw18601step1 := by apply Matrix.ext; unfold raw18601step2 raw18601step1; decide +kernel
      have hl : raw18601step1Labels = labelEmbedding8 ∘ raw18601step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18601step1 raw18601step1Labels raw18601step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical18602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18602 raw18602Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18602 raw18602Labels = mixedMoment B raw18602step0 raw18602step0Labels := by
      have ha : raw18602step0 = (fun i j => raw18602 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18602step0 raw18602; decide +kernel
      have hl : raw18602step0Labels = raw18602Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18602 raw18602Labels permutation234 permutation5
    mixedMoment B raw18602step0 raw18602step0Labels = mixedMoment B raw18602step1 raw18602step1Labels := by
      have ha : raw18602step1 = -raw18602step0 := by apply Matrix.ext; change ∀ i j, raw18602step1 i j = -(raw18602step0 i j); unfold raw18602step1 raw18602step0; decide +kernel
      have hl : raw18602step1Labels = raw18602step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18602step1 raw18602step1Labels = mixedMoment B raw18602step2 raw18602step2Labels := by
      have ha : raw18602step2 = raw18602step1 := by apply Matrix.ext; unfold raw18602step2 raw18602step1; decide +kernel
      have hl : raw18602step1Labels = labelEmbedding8 ∘ raw18602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18602step1 raw18602step1Labels raw18602step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical18603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18603 raw18603Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw18603 raw18603Labels = mixedMoment B raw18603step0 raw18603step0Labels := by
      have ha : raw18603step0 = (fun i j => raw18603 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18603step0 raw18603; decide +kernel
      have hl : raw18603step0Labels = raw18603Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18603 raw18603Labels permutation268 permutation2
    mixedMoment B raw18603step0 raw18603step0Labels = mixedMoment B raw18603step1 raw18603step1Labels := by
      have ha : raw18603step1 = -raw18603step0 := by apply Matrix.ext; change ∀ i j, raw18603step1 i j = -(raw18603step0 i j); unfold raw18603step1 raw18603step0; decide +kernel
      have hl : raw18603step1Labels = raw18603step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5469 node5469Labels := by rfl

theorem canonical18604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18604 raw18604Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw18604 raw18604Labels = mixedMoment B raw18604step0 raw18604step0Labels := by
      have ha : raw18604step0 = (fun i j => raw18604 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18604step0 raw18604; decide +kernel
      have hl : raw18604step0Labels = raw18604Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18604 raw18604Labels permutation266 permutation2
    mixedMoment B raw18604step0 raw18604step0Labels = mixedMoment B raw18604step1 raw18604step1Labels := by
      have ha : raw18604step1 = -raw18604step0 := by apply Matrix.ext; change ∀ i j, raw18604step1 i j = -(raw18604step0 i j); unfold raw18604step1 raw18604step0; decide +kernel
      have hl : raw18604step1Labels = raw18604step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5469 node5469Labels := by rfl

theorem canonical18605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18605 raw18605Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw18605 raw18605Labels = mixedMoment B raw18605step0 raw18605step0Labels := by
      have ha : raw18605step0 = (fun i j => raw18605 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18605step0 raw18605; decide +kernel
      have hl : raw18605step0Labels = raw18605Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18605 raw18605Labels permutation265 permutation2
    mixedMoment B raw18605step0 raw18605step0Labels = mixedMoment B raw18605step1 raw18605step1Labels := by
      have ha : raw18605step1 = -raw18605step0 := by apply Matrix.ext; change ∀ i j, raw18605step1 i j = -(raw18605step0 i j); unfold raw18605step1 raw18605step0; decide +kernel
      have hl : raw18605step1Labels = raw18605step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5469 node5469Labels := by rfl

theorem canonical18606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18606 raw18606Labels = mixedMoment B node5097 node5097Labels := by
  calc
    mixedMoment B raw18606 raw18606Labels = mixedMoment B raw18606step0 raw18606step0Labels := by
      have ha : raw18606step0 = (fun i j => raw18606 (permutation297 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18606step0 raw18606; decide +kernel
      have hl : raw18606step0Labels = raw18606Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18606 raw18606Labels permutation297 permutation3
    mixedMoment B raw18606step0 raw18606step0Labels = mixedMoment B raw18606step1 raw18606step1Labels := by
      have ha : raw18606step1 = -raw18606step0 := by apply Matrix.ext; change ∀ i j, raw18606step1 i j = -(raw18606step0 i j); unfold raw18606step1 raw18606step0; decide +kernel
      have hl : raw18606step1Labels = raw18606step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18606step1 raw18606step1Labels = mixedMoment B raw18606step2 raw18606step2Labels := by
      have ha : raw18606step2 = raw18606step1 := by apply Matrix.ext; unfold raw18606step2 raw18606step1; decide +kernel
      have hl : raw18606step1Labels = labelEmbedding6 ∘ raw18606step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18606step1 raw18606step1Labels raw18606step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5097 node5097Labels := by rfl

theorem canonical18607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18607 raw18607Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw18607 raw18607Labels = mixedMoment B raw18607step0 raw18607step0Labels := by
      have ha : raw18607step0 = (fun i j => raw18607 (permutation292 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18607step0 raw18607; decide +kernel
      have hl : raw18607step0Labels = raw18607Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18607 raw18607Labels permutation292 permutation3
    mixedMoment B raw18607step0 raw18607step0Labels = mixedMoment B raw18607step1 raw18607step1Labels := by
      have ha : raw18607step1 = -raw18607step0 := by apply Matrix.ext; change ∀ i j, raw18607step1 i j = -(raw18607step0 i j); unfold raw18607step1 raw18607step0; decide +kernel
      have hl : raw18607step1Labels = raw18607step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18607step1 raw18607step1Labels = mixedMoment B raw18607step2 raw18607step2Labels := by
      have ha : raw18607step2 = raw18607step1 := by apply Matrix.ext; unfold raw18607step2 raw18607step1; decide +kernel
      have hl : raw18607step1Labels = labelEmbedding6 ∘ raw18607step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18607step1 raw18607step1Labels raw18607step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

theorem canonical18608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18608 raw18608Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw18608 raw18608Labels = mixedMoment B raw18608step0 raw18608step0Labels := by
      have ha : raw18608step0 = (fun i j => raw18608 (permutation290 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18608step0 raw18608; decide +kernel
      have hl : raw18608step0Labels = raw18608Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18608 raw18608Labels permutation290 permutation3
    mixedMoment B raw18608step0 raw18608step0Labels = mixedMoment B raw18608step1 raw18608step1Labels := by
      have ha : raw18608step1 = -raw18608step0 := by apply Matrix.ext; change ∀ i j, raw18608step1 i j = -(raw18608step0 i j); unfold raw18608step1 raw18608step0; decide +kernel
      have hl : raw18608step1Labels = raw18608step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18608step1 raw18608step1Labels = mixedMoment B raw18608step2 raw18608step2Labels := by
      have ha : raw18608step2 = raw18608step1 := by apply Matrix.ext; unfold raw18608step2 raw18608step1; decide +kernel
      have hl : raw18608step1Labels = labelEmbedding6 ∘ raw18608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18608step1 raw18608step1Labels raw18608step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

theorem canonical18609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18609 raw18609Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw18609 raw18609Labels = mixedMoment B raw18609step0 raw18609step0Labels := by
      have ha : raw18609step0 = (fun i j => raw18609 (permutation289 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18609step0 raw18609; decide +kernel
      have hl : raw18609step0Labels = raw18609Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18609 raw18609Labels permutation289 permutation3
    mixedMoment B raw18609step0 raw18609step0Labels = mixedMoment B raw18609step1 raw18609step1Labels := by
      have ha : raw18609step1 = -raw18609step0 := by apply Matrix.ext; change ∀ i j, raw18609step1 i j = -(raw18609step0 i j); unfold raw18609step1 raw18609step0; decide +kernel
      have hl : raw18609step1Labels = raw18609step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18609step1 raw18609step1Labels = mixedMoment B raw18609step2 raw18609step2Labels := by
      have ha : raw18609step2 = raw18609step1 := by apply Matrix.ext; unfold raw18609step2 raw18609step1; decide +kernel
      have hl : raw18609step1Labels = labelEmbedding6 ∘ raw18609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18609step1 raw18609step1Labels raw18609step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

theorem canonical18610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18610 raw18610Labels = mixedMoment B node5277 node5277Labels := by
  calc
    mixedMoment B raw18610 raw18610Labels = mixedMoment B raw18610step0 raw18610step0Labels := by
      have ha : raw18610step0 = (fun i j => raw18610 (permutation216 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18610step0 raw18610; decide +kernel
      have hl : raw18610step0Labels = raw18610Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18610 raw18610Labels permutation216 permutation4
    mixedMoment B raw18610step0 raw18610step0Labels = mixedMoment B raw18610step1 raw18610step1Labels := by
      have ha : raw18610step1 = -raw18610step0 := by apply Matrix.ext; change ∀ i j, raw18610step1 i j = -(raw18610step0 i j); unfold raw18610step1 raw18610step0; decide +kernel
      have hl : raw18610step1Labels = raw18610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18610step1 raw18610step1Labels = mixedMoment B raw18610step2 raw18610step2Labels := by
      have ha : raw18610step2 = raw18610step1 := by apply Matrix.ext; unfold raw18610step2 raw18610step1; decide +kernel
      have hl : raw18610step1Labels = labelEmbedding7 ∘ raw18610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18610step1 raw18610step1Labels raw18610step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5277 node5277Labels := by rfl

theorem canonical18611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18611 raw18611Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw18611 raw18611Labels = mixedMoment B raw18611step0 raw18611step0Labels := by
      have ha : raw18611step0 = (fun i j => raw18611 (permutation369 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18611step0 raw18611; decide +kernel
      have hl : raw18611step0Labels = raw18611Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18611 raw18611Labels permutation369 permutation3
    mixedMoment B raw18611step0 raw18611step0Labels = mixedMoment B raw18611step1 raw18611step1Labels := by
      have ha : raw18611step1 = -raw18611step0 := by apply Matrix.ext; change ∀ i j, raw18611step1 i j = -(raw18611step0 i j); unfold raw18611step1 raw18611step0; decide +kernel
      have hl : raw18611step1Labels = raw18611step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18611step1 raw18611step1Labels = mixedMoment B raw18611step2 raw18611step2Labels := by
      have ha : raw18611step2 = raw18611step1 := by apply Matrix.ext; unfold raw18611step2 raw18611step1; decide +kernel
      have hl : raw18611step1Labels = labelEmbedding6 ∘ raw18611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18611step1 raw18611step1Labels raw18611step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

theorem canonical18612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18612 raw18612Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw18612 raw18612Labels = mixedMoment B raw18612step0 raw18612step0Labels := by
      have ha : raw18612step0 = (fun i j => raw18612 (permutation368 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18612step0 raw18612; decide +kernel
      have hl : raw18612step0Labels = raw18612Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18612 raw18612Labels permutation368 permutation3
    mixedMoment B raw18612step0 raw18612step0Labels = mixedMoment B raw18612step1 raw18612step1Labels := by
      have ha : raw18612step1 = -raw18612step0 := by apply Matrix.ext; change ∀ i j, raw18612step1 i j = -(raw18612step0 i j); unfold raw18612step1 raw18612step0; decide +kernel
      have hl : raw18612step1Labels = raw18612step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18612step1 raw18612step1Labels = mixedMoment B raw18612step2 raw18612step2Labels := by
      have ha : raw18612step2 = raw18612step1 := by apply Matrix.ext; unfold raw18612step2 raw18612step1; decide +kernel
      have hl : raw18612step1Labels = labelEmbedding6 ∘ raw18612step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18612step1 raw18612step1Labels raw18612step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

theorem canonical18613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18613 raw18613Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw18613 raw18613Labels = mixedMoment B raw18613step0 raw18613step0Labels := by
      have ha : raw18613step0 = (fun i j => raw18613 (permutation367 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18613step0 raw18613; decide +kernel
      have hl : raw18613step0Labels = raw18613Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18613 raw18613Labels permutation367 permutation3
    mixedMoment B raw18613step0 raw18613step0Labels = mixedMoment B raw18613step1 raw18613step1Labels := by
      have ha : raw18613step1 = -raw18613step0 := by apply Matrix.ext; change ∀ i j, raw18613step1 i j = -(raw18613step0 i j); unfold raw18613step1 raw18613step0; decide +kernel
      have hl : raw18613step1Labels = raw18613step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18613step1 raw18613step1Labels = mixedMoment B raw18613step2 raw18613step2Labels := by
      have ha : raw18613step2 = raw18613step1 := by apply Matrix.ext; unfold raw18613step2 raw18613step1; decide +kernel
      have hl : raw18613step1Labels = labelEmbedding6 ∘ raw18613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18613step1 raw18613step1Labels raw18613step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

theorem canonical18614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18614 raw18614Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw18614 raw18614Labels = mixedMoment B raw18614step0 raw18614step0Labels := by
      have ha : raw18614step0 = (fun i j => raw18614 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18614step0 raw18614; decide +kernel
      have hl : raw18614step0Labels = raw18614Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18614 raw18614Labels permutation240 permutation4
    mixedMoment B raw18614step0 raw18614step0Labels = mixedMoment B raw18614step1 raw18614step1Labels := by
      have ha : raw18614step1 = -raw18614step0 := by apply Matrix.ext; change ∀ i j, raw18614step1 i j = -(raw18614step0 i j); unfold raw18614step1 raw18614step0; decide +kernel
      have hl : raw18614step1Labels = raw18614step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18614step1 raw18614step1Labels = mixedMoment B raw18614step2 raw18614step2Labels := by
      have ha : raw18614step2 = raw18614step1 := by apply Matrix.ext; unfold raw18614step2 raw18614step1; decide +kernel
      have hl : raw18614step1Labels = labelEmbedding7 ∘ raw18614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18614step1 raw18614step1Labels raw18614step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical18615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18615 raw18615Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw18615 raw18615Labels = mixedMoment B raw18615step0 raw18615step0Labels := by
      have ha : raw18615step0 = (fun i j => raw18615 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18615step0 raw18615; decide +kernel
      have hl : raw18615step0Labels = raw18615Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18615 raw18615Labels permutation240 permutation4
    mixedMoment B raw18615step0 raw18615step0Labels = mixedMoment B raw18615step1 raw18615step1Labels := by
      have ha : raw18615step1 = -raw18615step0 := by apply Matrix.ext; change ∀ i j, raw18615step1 i j = -(raw18615step0 i j); unfold raw18615step1 raw18615step0; decide +kernel
      have hl : raw18615step1Labels = raw18615step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18615step1 raw18615step1Labels = mixedMoment B raw18615step2 raw18615step2Labels := by
      have ha : raw18615step2 = raw18615step1 := by apply Matrix.ext; unfold raw18615step2 raw18615step1; decide +kernel
      have hl : raw18615step1Labels = labelEmbedding7 ∘ raw18615step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18615step1 raw18615step1Labels raw18615step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical18616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18616 raw18616Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw18616 raw18616Labels = mixedMoment B raw18616step0 raw18616step0Labels := by
      have ha : raw18616step0 = (fun i j => raw18616 (permutation260 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18616step0 raw18616; decide +kernel
      have hl : raw18616step0Labels = raw18616Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18616 raw18616Labels permutation260 permutation4
    mixedMoment B raw18616step0 raw18616step0Labels = mixedMoment B raw18616step1 raw18616step1Labels := by
      have ha : raw18616step1 = -raw18616step0 := by apply Matrix.ext; change ∀ i j, raw18616step1 i j = -(raw18616step0 i j); unfold raw18616step1 raw18616step0; decide +kernel
      have hl : raw18616step1Labels = raw18616step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18616step1 raw18616step1Labels = mixedMoment B raw18616step2 raw18616step2Labels := by
      have ha : raw18616step2 = raw18616step1 := by apply Matrix.ext; unfold raw18616step2 raw18616step1; decide +kernel
      have hl : raw18616step1Labels = labelEmbedding7 ∘ raw18616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18616step1 raw18616step1Labels raw18616step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical18617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18617 raw18617Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw18617 raw18617Labels = mixedMoment B raw18617step0 raw18617step0Labels := by
      have ha : raw18617step0 = (fun i j => raw18617 (permutation218 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18617step0 raw18617; decide +kernel
      have hl : raw18617step0Labels = raw18617Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18617 raw18617Labels permutation218 permutation4
    mixedMoment B raw18617step0 raw18617step0Labels = mixedMoment B raw18617step1 raw18617step1Labels := by
      have ha : raw18617step1 = -raw18617step0 := by apply Matrix.ext; change ∀ i j, raw18617step1 i j = -(raw18617step0 i j); unfold raw18617step1 raw18617step0; decide +kernel
      have hl : raw18617step1Labels = raw18617step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18617step1 raw18617step1Labels = mixedMoment B raw18617step2 raw18617step2Labels := by
      have ha : raw18617step2 = raw18617step1 := by apply Matrix.ext; unfold raw18617step2 raw18617step1; decide +kernel
      have hl : raw18617step1Labels = labelEmbedding7 ∘ raw18617step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18617step1 raw18617step1Labels raw18617step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical18618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18618 raw18618Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw18618 raw18618Labels = mixedMoment B raw18618step0 raw18618step0Labels := by
      have ha : raw18618step0 = (fun i j => raw18618 (permutation218 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18618step0 raw18618; decide +kernel
      have hl : raw18618step0Labels = raw18618Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18618 raw18618Labels permutation218 permutation4
    mixedMoment B raw18618step0 raw18618step0Labels = mixedMoment B raw18618step1 raw18618step1Labels := by
      have ha : raw18618step1 = -raw18618step0 := by apply Matrix.ext; change ∀ i j, raw18618step1 i j = -(raw18618step0 i j); unfold raw18618step1 raw18618step0; decide +kernel
      have hl : raw18618step1Labels = raw18618step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18618step1 raw18618step1Labels = mixedMoment B raw18618step2 raw18618step2Labels := by
      have ha : raw18618step2 = raw18618step1 := by apply Matrix.ext; unfold raw18618step2 raw18618step1; decide +kernel
      have hl : raw18618step1Labels = labelEmbedding7 ∘ raw18618step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18618step1 raw18618step1Labels raw18618step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical18619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18619 raw18619Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw18619 raw18619Labels = mixedMoment B raw18619step0 raw18619step0Labels := by
      have ha : raw18619step0 = (fun i j => raw18619 (permutation257 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18619step0 raw18619; decide +kernel
      have hl : raw18619step0Labels = raw18619Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18619 raw18619Labels permutation257 permutation4
    mixedMoment B raw18619step0 raw18619step0Labels = mixedMoment B raw18619step1 raw18619step1Labels := by
      have ha : raw18619step1 = -raw18619step0 := by apply Matrix.ext; change ∀ i j, raw18619step1 i j = -(raw18619step0 i j); unfold raw18619step1 raw18619step0; decide +kernel
      have hl : raw18619step1Labels = raw18619step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18619step1 raw18619step1Labels = mixedMoment B raw18619step2 raw18619step2Labels := by
      have ha : raw18619step2 = raw18619step1 := by apply Matrix.ext; unfold raw18619step2 raw18619step1; decide +kernel
      have hl : raw18619step1Labels = labelEmbedding7 ∘ raw18619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18619step1 raw18619step1Labels raw18619step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical146
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18787 raw18787Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18787 raw18787Labels = mixedMoment B raw18787step0 raw18787step0Labels := by
      have ha : raw18787step0 = (fun i j => raw18787 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18787step0 raw18787; decide +kernel
      have hl : raw18787step0Labels = raw18787Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18787 raw18787Labels permutation265 permutation3
    mixedMoment B raw18787step0 raw18787step0Labels = mixedMoment B raw18787step1 raw18787step1Labels := by
      have ha : raw18787step1 = raw18787step0 := by apply Matrix.ext; unfold raw18787step1 raw18787step0; decide +kernel
      have hl : raw18787step0Labels = labelEmbedding6 ∘ raw18787step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18787step0 raw18787step0Labels raw18787step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical18788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18788 raw18788Labels = mixedMoment B node5497 node5497Labels := by
  calc
    mixedMoment B raw18788 raw18788Labels = mixedMoment B raw18788step0 raw18788step0Labels := by
      have ha : raw18788step0 = (fun i j => raw18788 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18788step0 raw18788; decide +kernel
      have hl : raw18788step0Labels = raw18788Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18788 raw18788Labels permutation180 permutation2
    _ = mixedMoment B node5497 node5497Labels := by rfl

theorem canonical18789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18789 raw18789Labels = mixedMoment B node5500 node5500Labels := by
  calc
    mixedMoment B raw18789 raw18789Labels = mixedMoment B raw18789step0 raw18789step0Labels := by
      have ha : raw18789step0 = (fun i j => raw18789 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18789step0 raw18789; decide +kernel
      have hl : raw18789step0Labels = raw18789Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18789 raw18789Labels permutation155 permutation2
    _ = mixedMoment B node5500 node5500Labels := by rfl

theorem canonical18790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18790 raw18790Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw18790 raw18790Labels = mixedMoment B raw18790step0 raw18790step0Labels := by
      have hz : ∀ j, raw18790 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18790step0 = (fun i j => raw18790 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18790step0 raw18790; decide +kernel
      have hl : raw18790step0Labels = raw18790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18790 raw18790Labels permutation590 hz
    mixedMoment B raw18790step0 raw18790step0Labels = mixedMoment B raw18790step1 raw18790step1Labels := by
      have ha : raw18790step1 = (fun i j => raw18790step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18790step1 raw18790step0; decide +kernel
      have hl : raw18790step1Labels = raw18790step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18790step0 raw18790step0Labels permutation127 permutation2
    mixedMoment B raw18790step1 raw18790step1Labels = mixedMoment B raw18790step2 raw18790step2Labels := by
      have ha : raw18790step2 = -raw18790step1 := by apply Matrix.ext; change ∀ i j, raw18790step2 i j = -(raw18790step1 i j); unfold raw18790step2 raw18790step1; decide +kernel
      have hl : raw18790step2Labels = raw18790step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5499 node5499Labels := by rfl

theorem canonical18791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18791 raw18791Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw18791 raw18791Labels = mixedMoment B raw18791step0 raw18791step0Labels := by
      have hz : ∀ j, raw18791 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18791step0 = (fun i j => raw18791 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18791step0 raw18791; decide +kernel
      have hl : raw18791step0Labels = raw18791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18791 raw18791Labels permutation265 hz
    mixedMoment B raw18791step0 raw18791step0Labels = mixedMoment B raw18791step1 raw18791step1Labels := by
      have ha : raw18791step1 = (fun i j => raw18791step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18791step1 raw18791step0; decide +kernel
      have hl : raw18791step1Labels = raw18791step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18791step0 raw18791step0Labels permutation32 permutation3
    mixedMoment B raw18791step1 raw18791step1Labels = mixedMoment B raw18791step2 raw18791step2Labels := by
      have ha : raw18791step2 = raw18791step1 := by apply Matrix.ext; unfold raw18791step2 raw18791step1; decide +kernel
      have hl : raw18791step1Labels = labelEmbedding6 ∘ raw18791step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18791step1 raw18791step1Labels raw18791step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical18792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18792 raw18792Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw18792 raw18792Labels = mixedMoment B raw18792step0 raw18792step0Labels := by
      have ha : raw18792step0 = (fun i j => raw18792 (permutation274 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18792step0 raw18792; decide +kernel
      have hl : raw18792step0Labels = raw18792Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18792 raw18792Labels permutation274 permutation3
    mixedMoment B raw18792step0 raw18792step0Labels = mixedMoment B raw18792step1 raw18792step1Labels := by
      have ha : raw18792step1 = raw18792step0 := by apply Matrix.ext; unfold raw18792step1 raw18792step0; decide +kernel
      have hl : raw18792step0Labels = labelEmbedding6 ∘ raw18792step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18792step0 raw18792step0Labels raw18792step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

theorem canonical18793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18793 raw18793Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw18793 raw18793Labels = mixedMoment B raw18793step0 raw18793step0Labels := by
      have ha : raw18793step0 = (fun i j => raw18793 (permutation167 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18793step0 raw18793; decide +kernel
      have hl : raw18793step0Labels = raw18793Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18793 raw18793Labels permutation167 permutation3
    mixedMoment B raw18793step0 raw18793step0Labels = mixedMoment B raw18793step1 raw18793step1Labels := by
      have ha : raw18793step1 = raw18793step0 := by apply Matrix.ext; unfold raw18793step1 raw18793step0; decide +kernel
      have hl : raw18793step0Labels = labelEmbedding6 ∘ raw18793step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18793step0 raw18793step0Labels raw18793step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical18794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18794 raw18794Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18794 raw18794Labels = mixedMoment B raw18794step0 raw18794step0Labels := by
      have hz : ∀ j, raw18794 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18794step0 = (fun i j => raw18794 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18794step0 raw18794; decide +kernel
      have hl : raw18794step0Labels = raw18794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18794 raw18794Labels permutation590 hz
    mixedMoment B raw18794step0 raw18794step0Labels = mixedMoment B raw18794step1 raw18794step1Labels := by
      have ha : raw18794step1 = (fun i j => raw18794step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18794step1 raw18794step0; decide +kernel
      have hl : raw18794step1Labels = raw18794step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18794step0 raw18794step0Labels permutation35 permutation3
    mixedMoment B raw18794step1 raw18794step1Labels = mixedMoment B raw18794step2 raw18794step2Labels := by
      have ha : raw18794step2 = raw18794step1 := by apply Matrix.ext; unfold raw18794step2 raw18794step1; decide +kernel
      have hl : raw18794step1Labels = labelEmbedding6 ∘ raw18794step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18794step1 raw18794step1Labels raw18794step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

theorem canonical18795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18795 raw18795Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw18795 raw18795Labels = mixedMoment B raw18795step0 raw18795step0Labels := by
      have ha : raw18795step0 = (fun i j => raw18795 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18795step0 raw18795; decide +kernel
      have hl : raw18795step0Labels = raw18795Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18795 raw18795Labels permutation268 permutation3
    mixedMoment B raw18795step0 raw18795step0Labels = mixedMoment B raw18795step1 raw18795step1Labels := by
      have ha : raw18795step1 = raw18795step0 := by apply Matrix.ext; unfold raw18795step1 raw18795step0; decide +kernel
      have hl : raw18795step0Labels = labelEmbedding6 ∘ raw18795step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18795step0 raw18795step0Labels raw18795step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

theorem canonical18796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18796 raw18796Labels = mixedMoment B node5476 node5476Labels := by
  calc
    mixedMoment B raw18796 raw18796Labels = mixedMoment B raw18796step0 raw18796step0Labels := by
      have ha : raw18796step0 = (fun i j => raw18796 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18796step0 raw18796; decide +kernel
      have hl : raw18796step0Labels = raw18796Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18796 raw18796Labels permutation181 permutation2
    _ = mixedMoment B node5476 node5476Labels := by rfl

theorem canonical18797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18797 raw18797Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw18797 raw18797Labels = mixedMoment B raw18797step0 raw18797step0Labels := by
      have ha : raw18797step0 = (fun i j => raw18797 (permutation165 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18797step0 raw18797; decide +kernel
      have hl : raw18797step0Labels = raw18797Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18797 raw18797Labels permutation165 permutation3
    mixedMoment B raw18797step0 raw18797step0Labels = mixedMoment B raw18797step1 raw18797step1Labels := by
      have ha : raw18797step1 = raw18797step0 := by apply Matrix.ext; unfold raw18797step1 raw18797step0; decide +kernel
      have hl : raw18797step0Labels = labelEmbedding6 ∘ raw18797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18797step0 raw18797step0Labels raw18797step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

theorem canonical18798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18798 raw18798Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw18798 raw18798Labels = mixedMoment B raw18798step0 raw18798step0Labels := by
      have hz : ∀ j, raw18798 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18798step0 = (fun i j => raw18798 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18798step0 raw18798; decide +kernel
      have hl : raw18798step0Labels = raw18798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18798 raw18798Labels permutation590 hz
    mixedMoment B raw18798step0 raw18798step0Labels = mixedMoment B raw18798step1 raw18798step1Labels := by
      have ha : raw18798step1 = (fun i j => raw18798step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18798step1 raw18798step0; decide +kernel
      have hl : raw18798step1Labels = raw18798step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18798step0 raw18798step0Labels permutation127 permutation2
    mixedMoment B raw18798step1 raw18798step1Labels = mixedMoment B raw18798step2 raw18798step2Labels := by
      have ha : raw18798step2 = -raw18798step1 := by apply Matrix.ext; change ∀ i j, raw18798step2 i j = -(raw18798step1 i j); unfold raw18798step2 raw18798step1; decide +kernel
      have hl : raw18798step2Labels = raw18798step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

theorem canonical18799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18799 raw18799Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw18799 raw18799Labels = mixedMoment B raw18799step0 raw18799step0Labels := by
      have ha : raw18799step0 = (fun i j => raw18799 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18799step0 raw18799; decide +kernel
      have hl : raw18799step0Labels = raw18799Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18799 raw18799Labels permutation266 permutation3
    mixedMoment B raw18799step0 raw18799step0Labels = mixedMoment B raw18799step1 raw18799step1Labels := by
      have ha : raw18799step1 = raw18799step0 := by apply Matrix.ext; unfold raw18799step1 raw18799step0; decide +kernel
      have hl : raw18799step0Labels = labelEmbedding6 ∘ raw18799step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18799step0 raw18799step0Labels raw18799step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

theorem canonical18800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18800 raw18800Labels = mixedMoment B node5476 node5476Labels := by
  calc
    mixedMoment B raw18800 raw18800Labels = mixedMoment B raw18800step0 raw18800step0Labels := by
      have ha : raw18800step0 = (fun i j => raw18800 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18800step0 raw18800; decide +kernel
      have hl : raw18800step0Labels = raw18800Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18800 raw18800Labels permutation180 permutation2
    _ = mixedMoment B node5476 node5476Labels := by rfl

theorem canonical18801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18801 raw18801Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw18801 raw18801Labels = mixedMoment B raw18801step0 raw18801step0Labels := by
      have hz : ∀ j, raw18801 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18801step0 = (fun i j => raw18801 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18801step0 raw18801; decide +kernel
      have hl : raw18801step0Labels = raw18801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18801 raw18801Labels permutation590 hz
    mixedMoment B raw18801step0 raw18801step0Labels = mixedMoment B raw18801step1 raw18801step1Labels := by
      have ha : raw18801step1 = (fun i j => raw18801step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18801step1 raw18801step0; decide +kernel
      have hl : raw18801step1Labels = raw18801step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18801step0 raw18801step0Labels permutation151 permutation2
    mixedMoment B raw18801step1 raw18801step1Labels = mixedMoment B raw18801step2 raw18801step2Labels := by
      have ha : raw18801step2 = -raw18801step1 := by apply Matrix.ext; change ∀ i j, raw18801step2 i j = -(raw18801step1 i j); unfold raw18801step2 raw18801step1; decide +kernel
      have hl : raw18801step2Labels = raw18801step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

theorem canonical18802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18802 raw18802Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18802 raw18802Labels = mixedMoment B raw18802step0 raw18802step0Labels := by
      have ha : raw18802step0 = (fun i j => raw18802 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18802step0 raw18802; decide +kernel
      have hl : raw18802step0Labels = raw18802Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18802 raw18802Labels permutation682 permutation3
    mixedMoment B raw18802step0 raw18802step0Labels = mixedMoment B raw18802step1 raw18802step1Labels := by
      have ha : raw18802step1 = -raw18802step0 := by apply Matrix.ext; change ∀ i j, raw18802step1 i j = -(raw18802step0 i j); unfold raw18802step1 raw18802step0; decide +kernel
      have hl : raw18802step1Labels = raw18802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18802step1 raw18802step1Labels = mixedMoment B raw18802step2 raw18802step2Labels := by
      have ha : raw18802step2 = raw18802step1 := by apply Matrix.ext; unfold raw18802step2 raw18802step1; decide +kernel
      have hl : raw18802step1Labels = labelEmbedding6 ∘ raw18802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18802step1 raw18802step1Labels raw18802step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

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

theorem canonical2091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2091 raw2091Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw2091 raw2091Labels = mixedMoment B raw2091step0 raw2091step0Labels := by
      have ha : raw2091step0 = (fun i j => raw2091 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2091step0 raw2091; decide +kernel
      have hl : raw2091step0Labels = raw2091Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2091 raw2091Labels permutation152 permutation4
    mixedMoment B raw2091step0 raw2091step0Labels = mixedMoment B raw2091step1 raw2091step1Labels := by
      have ha : raw2091step1 = raw2091step0 := by apply Matrix.ext; unfold raw2091step1 raw2091step0; decide +kernel
      have hl : raw2091step0Labels = labelEmbedding7 ∘ raw2091step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2091step0 raw2091step0Labels raw2091step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5072 node5072Labels := by rfl

theorem canonical2092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2092 raw2092Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw2092 raw2092Labels = mixedMoment B raw2092step0 raw2092step0Labels := by
      have ha : raw2092step0 = (fun i j => raw2092 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2092step0 raw2092; decide +kernel
      have hl : raw2092step0Labels = raw2092Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2092 raw2092Labels permutation152 permutation4
    _ = mixedMoment B node2479 node2479Labels := by rfl

theorem canonical2093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2093 raw2093Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw2093 raw2093Labels = mixedMoment B raw2093step0 raw2093step0Labels := by
      have ha : raw2093step0 = (fun i j => raw2093 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2093step0 raw2093; decide +kernel
      have hl : raw2093step0Labels = raw2093Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2093 raw2093Labels permutation160 permutation6
    mixedMoment B raw2093step0 raw2093step0Labels = mixedMoment B raw2093step1 raw2093step1Labels := by
      have ha : raw2093step1 = -raw2093step0 := by apply Matrix.ext; change ∀ i j, raw2093step1 i j = -(raw2093step0 i j); unfold raw2093step1 raw2093step0; decide +kernel
      have hl : raw2093step1Labels = raw2093step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2093step1 raw2093step1Labels = mixedMoment B raw2093step2 raw2093step2Labels := by
      have ha : raw2093step2 = raw2093step1 := by apply Matrix.ext; unfold raw2093step2 raw2093step1; decide +kernel
      have hl : raw2093step1Labels = labelEmbedding1 ∘ raw2093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2093step1 raw2093step1Labels raw2093step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

theorem canonical2094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2094 raw2094Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw2094 raw2094Labels = mixedMoment B raw2094step0 raw2094step0Labels := by
      have ha : raw2094step0 = (fun i j => raw2094 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2094step0 raw2094; decide +kernel
      have hl : raw2094step0Labels = raw2094Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2094 raw2094Labels permutation152 permutation4
    mixedMoment B raw2094step0 raw2094step0Labels = mixedMoment B raw2094step1 raw2094step1Labels := by
      have ha : raw2094step1 = raw2094step0 := by apply Matrix.ext; unfold raw2094step1 raw2094step0; decide +kernel
      have hl : raw2094step0Labels = labelEmbedding7 ∘ raw2094step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2094step0 raw2094step0Labels raw2094step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

theorem canonical2095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2095 raw2095Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw2095 raw2095Labels = mixedMoment B raw2095step0 raw2095step0Labels := by
      have ha : raw2095step0 = (fun i j => raw2095 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2095step0 raw2095; decide +kernel
      have hl : raw2095step0Labels = raw2095Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2095 raw2095Labels permutation152 permutation4
    _ = mixedMoment B node2480 node2480Labels := by rfl

theorem canonical2096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2096 raw2096Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw2096 raw2096Labels = mixedMoment B raw2096step0 raw2096step0Labels := by
      have ha : raw2096step0 = (fun i j => raw2096 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2096step0 raw2096; decide +kernel
      have hl : raw2096step0Labels = raw2096Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2096 raw2096Labels permutation158 permutation6
    mixedMoment B raw2096step0 raw2096step0Labels = mixedMoment B raw2096step1 raw2096step1Labels := by
      have ha : raw2096step1 = -raw2096step0 := by apply Matrix.ext; change ∀ i j, raw2096step1 i j = -(raw2096step0 i j); unfold raw2096step1 raw2096step0; decide +kernel
      have hl : raw2096step1Labels = raw2096step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2096step1 raw2096step1Labels = mixedMoment B raw2096step2 raw2096step2Labels := by
      have ha : raw2096step2 = raw2096step1 := by apply Matrix.ext; unfold raw2096step2 raw2096step1; decide +kernel
      have hl : raw2096step1Labels = labelEmbedding1 ∘ raw2096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2096step1 raw2096step1Labels raw2096step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

theorem canonical2121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2121 raw2121Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw2121 raw2121Labels = mixedMoment B raw2121step0 raw2121step0Labels := by
      have ha : raw2121step0 = (fun i j => raw2121 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2121step0 raw2121; decide +kernel
      have hl : raw2121step0Labels = raw2121Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2121 raw2121Labels permutation152 permutation4
    mixedMoment B raw2121step0 raw2121step0Labels = mixedMoment B raw2121step1 raw2121step1Labels := by
      have ha : raw2121step1 = raw2121step0 := by apply Matrix.ext; unfold raw2121step1 raw2121step0; decide +kernel
      have hl : raw2121step0Labels = labelEmbedding7 ∘ raw2121step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2121step0 raw2121step0Labels raw2121step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5098 node5098Labels := by rfl

theorem canonical2122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2122 raw2122Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw2122 raw2122Labels = mixedMoment B raw2122step0 raw2122step0Labels := by
      have ha : raw2122step0 = (fun i j => raw2122 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2122step0 raw2122; decide +kernel
      have hl : raw2122step0Labels = raw2122Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2122 raw2122Labels permutation152 permutation4
    _ = mixedMoment B node2508 node2508Labels := by rfl

theorem canonical2123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2123 raw2123Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw2123 raw2123Labels = mixedMoment B raw2123step0 raw2123step0Labels := by
      have ha : raw2123step0 = (fun i j => raw2123 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2123step0 raw2123; decide +kernel
      have hl : raw2123step0Labels = raw2123Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2123 raw2123Labels permutation152 permutation6
    mixedMoment B raw2123step0 raw2123step0Labels = mixedMoment B raw2123step1 raw2123step1Labels := by
      have ha : raw2123step1 = -raw2123step0 := by apply Matrix.ext; change ∀ i j, raw2123step1 i j = -(raw2123step0 i j); unfold raw2123step1 raw2123step0; decide +kernel
      have hl : raw2123step1Labels = raw2123step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2123step1 raw2123step1Labels = mixedMoment B raw2123step2 raw2123step2Labels := by
      have ha : raw2123step2 = raw2123step1 := by apply Matrix.ext; unfold raw2123step2 raw2123step1; decide +kernel
      have hl : raw2123step1Labels = labelEmbedding1 ∘ raw2123step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2123step1 raw2123step1Labels raw2123step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3460 node3460Labels := by rfl

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

theorem canonical2391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2391 raw2391Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw2391 raw2391Labels = mixedMoment B raw2391step0 raw2391step0Labels := by
      have ha : raw2391step0 = (fun i j => raw2391 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2391step0 raw2391; decide +kernel
      have hl : raw2391step0Labels = raw2391Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2391 raw2391Labels permutation152 permutation4
    mixedMoment B raw2391step0 raw2391step0Labels = mixedMoment B raw2391step1 raw2391step1Labels := by
      have ha : raw2391step1 = raw2391step0 := by apply Matrix.ext; unfold raw2391step1 raw2391step0; decide +kernel
      have hl : raw2391step0Labels = labelEmbedding7 ∘ raw2391step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2391step0 raw2391step0Labels raw2391step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

theorem canonical2392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2392 raw2392Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw2392 raw2392Labels = mixedMoment B raw2392step0 raw2392step0Labels := by
      have ha : raw2392step0 = (fun i j => raw2392 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2392step0 raw2392; decide +kernel
      have hl : raw2392step0Labels = raw2392Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2392 raw2392Labels permutation152 permutation4
    _ = mixedMoment B node3689 node3689Labels := by rfl

theorem canonical2393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2393 raw2393Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw2393 raw2393Labels = mixedMoment B raw2393step0 raw2393step0Labels := by
      have ha : raw2393step0 = (fun i j => raw2393 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2393step0 raw2393; decide +kernel
      have hl : raw2393step0Labels = raw2393Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2393 raw2393Labels permutation160 permutation6
    mixedMoment B raw2393step0 raw2393step0Labels = mixedMoment B raw2393step1 raw2393step1Labels := by
      have ha : raw2393step1 = -raw2393step0 := by apply Matrix.ext; change ∀ i j, raw2393step1 i j = -(raw2393step0 i j); unfold raw2393step1 raw2393step0; decide +kernel
      have hl : raw2393step1Labels = raw2393step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2393step1 raw2393step1Labels = mixedMoment B raw2393step2 raw2393step2Labels := by
      have ha : raw2393step2 = raw2393step1 := by apply Matrix.ext; unfold raw2393step2 raw2393step1; decide +kernel
      have hl : raw2393step1Labels = labelEmbedding1 ∘ raw2393step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2393step1 raw2393step1Labels raw2393step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3757 node3757Labels := by rfl

theorem canonical2394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2394 raw2394Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw2394 raw2394Labels = mixedMoment B raw2394step0 raw2394step0Labels := by
      have ha : raw2394step0 = (fun i j => raw2394 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2394step0 raw2394; decide +kernel
      have hl : raw2394step0Labels = raw2394Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2394 raw2394Labels permutation152 permutation4
    mixedMoment B raw2394step0 raw2394step0Labels = mixedMoment B raw2394step1 raw2394step1Labels := by
      have ha : raw2394step1 = raw2394step0 := by apply Matrix.ext; unfold raw2394step1 raw2394step0; decide +kernel
      have hl : raw2394step0Labels = labelEmbedding7 ∘ raw2394step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2394step0 raw2394step0Labels raw2394step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

theorem canonical2395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2395 raw2395Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw2395 raw2395Labels = mixedMoment B raw2395step0 raw2395step0Labels := by
      have ha : raw2395step0 = (fun i j => raw2395 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2395step0 raw2395; decide +kernel
      have hl : raw2395step0Labels = raw2395Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2395 raw2395Labels permutation152 permutation4
    _ = mixedMoment B node3690 node3690Labels := by rfl

theorem canonical2396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2396 raw2396Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw2396 raw2396Labels = mixedMoment B raw2396step0 raw2396step0Labels := by
      have ha : raw2396step0 = (fun i j => raw2396 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2396step0 raw2396; decide +kernel
      have hl : raw2396step0Labels = raw2396Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2396 raw2396Labels permutation158 permutation6
    mixedMoment B raw2396step0 raw2396step0Labels = mixedMoment B raw2396step1 raw2396step1Labels := by
      have ha : raw2396step1 = -raw2396step0 := by apply Matrix.ext; change ∀ i j, raw2396step1 i j = -(raw2396step0 i j); unfold raw2396step1 raw2396step0; decide +kernel
      have hl : raw2396step1Labels = raw2396step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2396step1 raw2396step1Labels = mixedMoment B raw2396step2 raw2396step2Labels := by
      have ha : raw2396step2 = raw2396step1 := by apply Matrix.ext; unfold raw2396step2 raw2396step1; decide +kernel
      have hl : raw2396step1Labels = labelEmbedding1 ∘ raw2396step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2396step1 raw2396step1Labels raw2396step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

theorem canonical2412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2412 raw2412Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw2412 raw2412Labels = mixedMoment B raw2412step0 raw2412step0Labels := by
      have ha : raw2412step0 = (fun i j => raw2412 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2412step0 raw2412; decide +kernel
      have hl : raw2412step0Labels = raw2412Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2412 raw2412Labels permutation152 permutation4
    mixedMoment B raw2412step0 raw2412step0Labels = mixedMoment B raw2412step1 raw2412step1Labels := by
      have ha : raw2412step1 = raw2412step0 := by apply Matrix.ext; unfold raw2412step1 raw2412step0; decide +kernel
      have hl : raw2412step0Labels = labelEmbedding7 ∘ raw2412step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2412step0 raw2412step0Labels raw2412step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

theorem canonical2413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2413 raw2413Labels = mixedMoment B node3703 node3703Labels := by
  calc
    mixedMoment B raw2413 raw2413Labels = mixedMoment B raw2413step0 raw2413step0Labels := by
      have ha : raw2413step0 = (fun i j => raw2413 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2413step0 raw2413; decide +kernel
      have hl : raw2413step0Labels = raw2413Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2413 raw2413Labels permutation152 permutation4
    _ = mixedMoment B node3703 node3703Labels := by rfl

theorem canonical2414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2414 raw2414Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw2414 raw2414Labels = mixedMoment B raw2414step0 raw2414step0Labels := by
      have ha : raw2414step0 = (fun i j => raw2414 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2414step0 raw2414; decide +kernel
      have hl : raw2414step0Labels = raw2414Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2414 raw2414Labels permutation152 permutation6
    mixedMoment B raw2414step0 raw2414step0Labels = mixedMoment B raw2414step1 raw2414step1Labels := by
      have ha : raw2414step1 = -raw2414step0 := by apply Matrix.ext; change ∀ i j, raw2414step1 i j = -(raw2414step0 i j); unfold raw2414step1 raw2414step0; decide +kernel
      have hl : raw2414step1Labels = raw2414step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2414step1 raw2414step1Labels = mixedMoment B raw2414step2 raw2414step2Labels := by
      have ha : raw2414step2 = raw2414step1 := by apply Matrix.ext; unfold raw2414step2 raw2414step1; decide +kernel
      have hl : raw2414step1Labels = labelEmbedding1 ∘ raw2414step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2414step1 raw2414step1Labels raw2414step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3758 node3758Labels := by rfl

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

theorem canonical2433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2433 raw2433Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw2433 raw2433Labels = mixedMoment B raw2433step0 raw2433step0Labels := by
      have ha : raw2433step0 = (fun i j => raw2433 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2433step0 raw2433; decide +kernel
      have hl : raw2433step0Labels = raw2433Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2433 raw2433Labels permutation152 permutation4
    mixedMoment B raw2433step0 raw2433step0Labels = mixedMoment B raw2433step1 raw2433step1Labels := by
      have ha : raw2433step1 = raw2433step0 := by apply Matrix.ext; unfold raw2433step1 raw2433step0; decide +kernel
      have hl : raw2433step0Labels = labelEmbedding7 ∘ raw2433step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2433step0 raw2433step0Labels raw2433step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

theorem canonical2434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2434 raw2434Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw2434 raw2434Labels = mixedMoment B raw2434step0 raw2434step0Labels := by
      have ha : raw2434step0 = (fun i j => raw2434 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2434step0 raw2434; decide +kernel
      have hl : raw2434step0Labels = raw2434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2434 raw2434Labels permutation152 permutation4
    _ = mixedMoment B node3721 node3721Labels := by rfl

theorem canonical2435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2435 raw2435Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw2435 raw2435Labels = mixedMoment B raw2435step0 raw2435step0Labels := by
      have ha : raw2435step0 = (fun i j => raw2435 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2435step0 raw2435; decide +kernel
      have hl : raw2435step0Labels = raw2435Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2435 raw2435Labels permutation176 permutation6
    mixedMoment B raw2435step0 raw2435step0Labels = mixedMoment B raw2435step1 raw2435step1Labels := by
      have ha : raw2435step1 = -raw2435step0 := by apply Matrix.ext; change ∀ i j, raw2435step1 i j = -(raw2435step0 i j); unfold raw2435step1 raw2435step0; decide +kernel
      have hl : raw2435step1Labels = raw2435step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2435step1 raw2435step1Labels = mixedMoment B raw2435step2 raw2435step2Labels := by
      have ha : raw2435step2 = raw2435step1 := by apply Matrix.ext; unfold raw2435step2 raw2435step1; decide +kernel
      have hl : raw2435step1Labels = labelEmbedding1 ∘ raw2435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2435step1 raw2435step1Labels raw2435step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

theorem canonical2436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2436 raw2436Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw2436 raw2436Labels = mixedMoment B raw2436step0 raw2436step0Labels := by
      have ha : raw2436step0 = (fun i j => raw2436 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2436step0 raw2436; decide +kernel
      have hl : raw2436step0Labels = raw2436Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2436 raw2436Labels permutation152 permutation4
    mixedMoment B raw2436step0 raw2436step0Labels = mixedMoment B raw2436step1 raw2436step1Labels := by
      have ha : raw2436step1 = raw2436step0 := by apply Matrix.ext; unfold raw2436step1 raw2436step0; decide +kernel
      have hl : raw2436step0Labels = labelEmbedding7 ∘ raw2436step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2436step0 raw2436step0Labels raw2436step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

theorem canonical2437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2437 raw2437Labels = mixedMoment B node3731 node3731Labels := by
  calc
    mixedMoment B raw2437 raw2437Labels = mixedMoment B raw2437step0 raw2437step0Labels := by
      have ha : raw2437step0 = (fun i j => raw2437 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2437step0 raw2437; decide +kernel
      have hl : raw2437step0Labels = raw2437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2437 raw2437Labels permutation152 permutation4
    _ = mixedMoment B node3731 node3731Labels := by rfl

theorem canonical2438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2438 raw2438Labels = mixedMoment B node3867 node3867Labels := by
  calc
    mixedMoment B raw2438 raw2438Labels = mixedMoment B raw2438step0 raw2438step0Labels := by
      have ha : raw2438step0 = (fun i j => raw2438 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2438step0 raw2438; decide +kernel
      have hl : raw2438step0Labels = raw2438Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2438 raw2438Labels permutation176 permutation6
    mixedMoment B raw2438step0 raw2438step0Labels = mixedMoment B raw2438step1 raw2438step1Labels := by
      have ha : raw2438step1 = -raw2438step0 := by apply Matrix.ext; change ∀ i j, raw2438step1 i j = -(raw2438step0 i j); unfold raw2438step1 raw2438step0; decide +kernel
      have hl : raw2438step1Labels = raw2438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2438step1 raw2438step1Labels = mixedMoment B raw2438step2 raw2438step2Labels := by
      have ha : raw2438step2 = raw2438step1 := by apply Matrix.ext; unfold raw2438step2 raw2438step1; decide +kernel
      have hl : raw2438step1Labels = labelEmbedding1 ∘ raw2438step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2438step1 raw2438step1Labels raw2438step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3867 node3867Labels := by rfl

theorem canonical2487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2487 raw2487Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw2487 raw2487Labels = mixedMoment B raw2487step0 raw2487step0Labels := by
      have ha : raw2487step0 = (fun i j => raw2487 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2487step0 raw2487; decide +kernel
      have hl : raw2487step0Labels = raw2487Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2487 raw2487Labels permutation152 permutation4
    mixedMoment B raw2487step0 raw2487step0Labels = mixedMoment B raw2487step1 raw2487step1Labels := by
      have ha : raw2487step1 = raw2487step0 := by apply Matrix.ext; unfold raw2487step1 raw2487step0; decide +kernel
      have hl : raw2487step0Labels = labelEmbedding7 ∘ raw2487step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2487step0 raw2487step0Labels raw2487step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2488 raw2488Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw2488 raw2488Labels = mixedMoment B raw2488step0 raw2488step0Labels := by
      have ha : raw2488step0 = (fun i j => raw2488 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2488step0 raw2488; decide +kernel
      have hl : raw2488step0Labels = raw2488Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2488 raw2488Labels permutation152 permutation4
    _ = mixedMoment B node3801 node3801Labels := by rfl

theorem canonical2489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2489 raw2489Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw2489 raw2489Labels = mixedMoment B raw2489step0 raw2489step0Labels := by
      have ha : raw2489step0 = (fun i j => raw2489 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2489step0 raw2489; decide +kernel
      have hl : raw2489step0Labels = raw2489Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2489 raw2489Labels permutation170 permutation6
    mixedMoment B raw2489step0 raw2489step0Labels = mixedMoment B raw2489step1 raw2489step1Labels := by
      have ha : raw2489step1 = -raw2489step0 := by apply Matrix.ext; change ∀ i j, raw2489step1 i j = -(raw2489step0 i j); unfold raw2489step1 raw2489step0; decide +kernel
      have hl : raw2489step1Labels = raw2489step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2489step1 raw2489step1Labels = mixedMoment B raw2489step2 raw2489step2Labels := by
      have ha : raw2489step2 = raw2489step1 := by apply Matrix.ext; unfold raw2489step2 raw2489step1; decide +kernel
      have hl : raw2489step1Labels = labelEmbedding1 ∘ raw2489step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2489step1 raw2489step1Labels raw2489step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

theorem canonical2508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2508 raw2508Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw2508 raw2508Labels = mixedMoment B raw2508step0 raw2508step0Labels := by
      have ha : raw2508step0 = (fun i j => raw2508 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2508step0 raw2508; decide +kernel
      have hl : raw2508step0Labels = raw2508Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2508 raw2508Labels permutation152 permutation5
    mixedMoment B raw2508step0 raw2508step0Labels = mixedMoment B raw2508step1 raw2508step1Labels := by
      have ha : raw2508step1 = raw2508step0 := by apply Matrix.ext; unfold raw2508step1 raw2508step0; decide +kernel
      have hl : raw2508step0Labels = labelEmbedding8 ∘ raw2508step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2508step0 raw2508step0Labels raw2508step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical2509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2509 raw2509Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw2509 raw2509Labels = mixedMoment B raw2509step0 raw2509step0Labels := by
      have ha : raw2509step0 = (fun i j => raw2509 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2509step0 raw2509; decide +kernel
      have hl : raw2509step0Labels = raw2509Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2509 raw2509Labels permutation662 permutation4
    mixedMoment B raw2509step0 raw2509step0Labels = mixedMoment B raw2509step1 raw2509step1Labels := by
      have ha : raw2509step1 = -raw2509step0 := by apply Matrix.ext; change ∀ i j, raw2509step1 i j = -(raw2509step0 i j); unfold raw2509step1 raw2509step0; decide +kernel
      have hl : raw2509step1Labels = raw2509step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3964 node3964Labels := by rfl

theorem canonical2510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2510 raw2510Labels = mixedMoment B node3900 node3900Labels := by
  calc
    mixedMoment B raw2510 raw2510Labels = mixedMoment B raw2510step0 raw2510step0Labels := by
      have ha : raw2510step0 = (fun i j => raw2510 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2510step0 raw2510; decide +kernel
      have hl : raw2510step0Labels = raw2510Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2510 raw2510Labels permutation160 permutation3
    mixedMoment B raw2510step0 raw2510step0Labels = mixedMoment B raw2510step1 raw2510step1Labels := by
      have ha : raw2510step1 = -raw2510step0 := by apply Matrix.ext; change ∀ i j, raw2510step1 i j = -(raw2510step0 i j); unfold raw2510step1 raw2510step0; decide +kernel
      have hl : raw2510step1Labels = raw2510step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2510step1 raw2510step1Labels = mixedMoment B raw2510step2 raw2510step2Labels := by
      have ha : raw2510step2 = raw2510step1 := by apply Matrix.ext; unfold raw2510step2 raw2510step1; decide +kernel
      have hl : raw2510step1Labels = labelEmbedding1 ∘ raw2510step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2510step1 raw2510step1Labels raw2510step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3900 node3900Labels := by rfl

theorem canonical2514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2514 raw2514Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw2514 raw2514Labels = mixedMoment B raw2514step0 raw2514step0Labels := by
      have ha : raw2514step0 = (fun i j => raw2514 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2514step0 raw2514; decide +kernel
      have hl : raw2514step0Labels = raw2514Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2514 raw2514Labels permutation152 permutation4
    mixedMoment B raw2514step0 raw2514step0Labels = mixedMoment B raw2514step1 raw2514step1Labels := by
      have ha : raw2514step1 = raw2514step0 := by apply Matrix.ext; unfold raw2514step1 raw2514step0; decide +kernel
      have hl : raw2514step0Labels = labelEmbedding7 ∘ raw2514step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2514step0 raw2514step0Labels raw2514step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2515 raw2515Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw2515 raw2515Labels = mixedMoment B raw2515step0 raw2515step0Labels := by
      have ha : raw2515step0 = (fun i j => raw2515 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2515step0 raw2515; decide +kernel
      have hl : raw2515step0Labels = raw2515Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2515 raw2515Labels permutation152 permutation4
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical2516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2516 raw2516Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw2516 raw2516Labels = mixedMoment B raw2516step0 raw2516step0Labels := by
      have ha : raw2516step0 = (fun i j => raw2516 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2516step0 raw2516; decide +kernel
      have hl : raw2516step0Labels = raw2516Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2516 raw2516Labels permutation176 permutation6
    mixedMoment B raw2516step0 raw2516step0Labels = mixedMoment B raw2516step1 raw2516step1Labels := by
      have ha : raw2516step1 = -raw2516step0 := by apply Matrix.ext; change ∀ i j, raw2516step1 i j = -(raw2516step0 i j); unfold raw2516step1 raw2516step0; decide +kernel
      have hl : raw2516step1Labels = raw2516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2516step1 raw2516step1Labels = mixedMoment B raw2516step2 raw2516step2Labels := by
      have ha : raw2516step2 = raw2516step1 := by apply Matrix.ext; unfold raw2516step2 raw2516step1; decide +kernel
      have hl : raw2516step1Labels = labelEmbedding1 ∘ raw2516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2516step1 raw2516step1Labels raw2516step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical2535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2535 raw2535Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw2535 raw2535Labels = mixedMoment B raw2535step0 raw2535step0Labels := by
      have ha : raw2535step0 = (fun i j => raw2535 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2535step0 raw2535; decide +kernel
      have hl : raw2535step0Labels = raw2535Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2535 raw2535Labels permutation152 permutation5
    mixedMoment B raw2535step0 raw2535step0Labels = mixedMoment B raw2535step1 raw2535step1Labels := by
      have ha : raw2535step1 = raw2535step0 := by apply Matrix.ext; unfold raw2535step1 raw2535step0; decide +kernel
      have hl : raw2535step0Labels = labelEmbedding8 ∘ raw2535step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2535step0 raw2535step0Labels raw2535step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5437 node5437Labels := by rfl

theorem canonical2536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2536 raw2536Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw2536 raw2536Labels = mixedMoment B raw2536step0 raw2536step0Labels := by
      have ha : raw2536step0 = (fun i j => raw2536 (permutation373 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2536step0 raw2536; decide +kernel
      have hl : raw2536step0Labels = raw2536Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2536 raw2536Labels permutation373 permutation2
    _ = mixedMoment B node3899 node3899Labels := by rfl

theorem canonical2537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2537 raw2537Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw2537 raw2537Labels = mixedMoment B raw2537step0 raw2537step0Labels := by
      have ha : raw2537step0 = (fun i j => raw2537 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2537step0 raw2537; decide +kernel
      have hl : raw2537step0Labels = raw2537Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2537 raw2537Labels permutation161 permutation3
    mixedMoment B raw2537step0 raw2537step0Labels = mixedMoment B raw2537step1 raw2537step1Labels := by
      have ha : raw2537step1 = -raw2537step0 := by apply Matrix.ext; change ∀ i j, raw2537step1 i j = -(raw2537step0 i j); unfold raw2537step1 raw2537step0; decide +kernel
      have hl : raw2537step1Labels = raw2537step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2537step1 raw2537step1Labels = mixedMoment B raw2537step2 raw2537step2Labels := by
      have ha : raw2537step2 = raw2537step1 := by apply Matrix.ext; unfold raw2537step2 raw2537step1; decide +kernel
      have hl : raw2537step1Labels = labelEmbedding1 ∘ raw2537step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2537step1 raw2537step1Labels raw2537step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3899 node3899Labels := by rfl

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

theorem canonical2583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2583 raw2583Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw2583 raw2583Labels = mixedMoment B raw2583step0 raw2583step0Labels := by
      have ha : raw2583step0 = (fun i j => raw2583 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2583step0 raw2583; decide +kernel
      have hl : raw2583step0Labels = raw2583Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2583 raw2583Labels permutation152 permutation4
    mixedMoment B raw2583step0 raw2583step0Labels = mixedMoment B raw2583step1 raw2583step1Labels := by
      have ha : raw2583step1 = raw2583step0 := by apply Matrix.ext; unfold raw2583step1 raw2583step0; decide +kernel
      have hl : raw2583step0Labels = labelEmbedding7 ∘ raw2583step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2583step0 raw2583step0Labels raw2583step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

theorem canonical2584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2584 raw2584Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw2584 raw2584Labels = mixedMoment B raw2584step0 raw2584step0Labels := by
      have ha : raw2584step0 = (fun i j => raw2584 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2584step0 raw2584; decide +kernel
      have hl : raw2584step0Labels = raw2584Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2584 raw2584Labels permutation152 permutation4
    _ = mixedMoment B node3945 node3945Labels := by rfl

theorem canonical2585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2585 raw2585Labels = mixedMoment B node3952 node3952Labels := by
  calc
    mixedMoment B raw2585 raw2585Labels = mixedMoment B raw2585step0 raw2585step0Labels := by
      have ha : raw2585step0 = (fun i j => raw2585 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2585step0 raw2585; decide +kernel
      have hl : raw2585step0Labels = raw2585Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2585 raw2585Labels permutation265 permutation6
    mixedMoment B raw2585step0 raw2585step0Labels = mixedMoment B raw2585step1 raw2585step1Labels := by
      have ha : raw2585step1 = -raw2585step0 := by apply Matrix.ext; change ∀ i j, raw2585step1 i j = -(raw2585step0 i j); unfold raw2585step1 raw2585step0; decide +kernel
      have hl : raw2585step1Labels = raw2585step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2585step1 raw2585step1Labels = mixedMoment B raw2585step2 raw2585step2Labels := by
      have ha : raw2585step2 = raw2585step1 := by apply Matrix.ext; unfold raw2585step2 raw2585step1; decide +kernel
      have hl : raw2585step1Labels = labelEmbedding1 ∘ raw2585step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2585step1 raw2585step1Labels raw2585step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3952 node3952Labels := by rfl

theorem canonical2598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2598 raw2598Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw2598 raw2598Labels = mixedMoment B raw2598step0 raw2598step0Labels := by
      have ha : raw2598step0 = (fun i j => raw2598 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2598step0 raw2598; decide +kernel
      have hl : raw2598step0Labels = raw2598Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2598 raw2598Labels permutation152 permutation4
    mixedMoment B raw2598step0 raw2598step0Labels = mixedMoment B raw2598step1 raw2598step1Labels := by
      have ha : raw2598step1 = raw2598step0 := by apply Matrix.ext; unfold raw2598step1 raw2598step0; decide +kernel
      have hl : raw2598step0Labels = labelEmbedding7 ∘ raw2598step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2598step0 raw2598step0Labels raw2598step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical2599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2599 raw2599Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw2599 raw2599Labels = mixedMoment B raw2599step0 raw2599step0Labels := by
      have ha : raw2599step0 = (fun i j => raw2599 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2599step0 raw2599; decide +kernel
      have hl : raw2599step0Labels = raw2599Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2599 raw2599Labels permutation152 permutation4
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical2600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2600 raw2600Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw2600 raw2600Labels = mixedMoment B raw2600step0 raw2600step0Labels := by
      have ha : raw2600step0 = (fun i j => raw2600 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2600step0 raw2600; decide +kernel
      have hl : raw2600step0Labels = raw2600Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2600 raw2600Labels permutation688 permutation6
    mixedMoment B raw2600step0 raw2600step0Labels = mixedMoment B raw2600step1 raw2600step1Labels := by
      have ha : raw2600step1 = raw2600step0 := by apply Matrix.ext; unfold raw2600step1 raw2600step0; decide +kernel
      have hl : raw2600step0Labels = labelEmbedding1 ∘ raw2600step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2600step0 raw2600step0Labels raw2600step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

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

theorem canonical12592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12592 raw12592Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw12592 raw12592Labels = mixedMoment B raw12592step0 raw12592step0Labels := by
      have hz : ∀ j, raw12592 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12592step0 = (fun i j => raw12592 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12592step0 raw12592; decide +kernel
      have hl : raw12592step0Labels = raw12592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12592 raw12592Labels permutation265 hz
    mixedMoment B raw12592step0 raw12592step0Labels = mixedMoment B raw12592step1 raw12592step1Labels := by
      have ha : raw12592step1 = (fun i j => raw12592step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12592step1 raw12592step0; decide +kernel
      have hl : raw12592step1Labels = raw12592step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12592step0 raw12592step0Labels permutation36 permutation2
    _ = mixedMoment B node5486 node5486Labels := by rfl

theorem canonical12593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12593 raw12593Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw12593 raw12593Labels = mixedMoment B raw12593step0 raw12593step0Labels := by
      have hz : ∀ j, raw12593 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12593step0 = (fun i j => raw12593 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12593step0 raw12593; decide +kernel
      have hl : raw12593step0Labels = raw12593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12593 raw12593Labels permutation265 hz
    mixedMoment B raw12593step0 raw12593step0Labels = mixedMoment B raw12593step1 raw12593step1Labels := by
      have ha : raw12593step1 = (fun i j => raw12593step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12593step1 raw12593step0; decide +kernel
      have hl : raw12593step1Labels = raw12593step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12593step0 raw12593step0Labels permutation33 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical12594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12594 raw12594Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw12594 raw12594Labels = mixedMoment B raw12594step0 raw12594step0Labels := by
      have hz : ∀ j, raw12594 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12594step0 = (fun i j => raw12594 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12594step0 raw12594; decide +kernel
      have hl : raw12594step0Labels = raw12594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12594 raw12594Labels permutation265 hz
    mixedMoment B raw12594step0 raw12594step0Labels = mixedMoment B raw12594step1 raw12594step1Labels := by
      have ha : raw12594step1 = (fun i j => raw12594step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12594step1 raw12594step0; decide +kernel
      have hl : raw12594step1Labels = raw12594step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12594step0 raw12594step0Labels permutation35 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical12595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12595 raw12595Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw12595 raw12595Labels = mixedMoment B raw12595step0 raw12595step0Labels := by
      have hz : ∀ j, raw12595 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12595step0 = (fun i j => raw12595 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12595step0 raw12595; decide +kernel
      have hl : raw12595step0Labels = raw12595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12595 raw12595Labels permutation590 hz
    mixedMoment B raw12595step0 raw12595step0Labels = mixedMoment B raw12595step1 raw12595step1Labels := by
      have hz : ∀ j, raw12595step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12595step1 = (fun i j => raw12595step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12595step1 raw12595step0; decide +kernel
      have hl : raw12595step1Labels = raw12595step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12595step0 raw12595step0Labels permutation56 hz
    _ = mixedMoment B node5493 node5493Labels := by rfl

theorem canonical12602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12602 raw12602Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw12602 raw12602Labels = mixedMoment B raw12602step0 raw12602step0Labels := by
      have ha : raw12602step0 = (fun i j => raw12602 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12602step0 raw12602; decide +kernel
      have hl : raw12602step0Labels = raw12602Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12602 raw12602Labels permutation161 permutation3
    mixedMoment B raw12602step0 raw12602step0Labels = mixedMoment B raw12602step1 raw12602step1Labels := by
      have ha : raw12602step1 = raw12602step0 := by apply Matrix.ext; unfold raw12602step1 raw12602step0; decide +kernel
      have hl : raw12602step0Labels = labelEmbedding6 ∘ raw12602step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12602step0 raw12602step0Labels raw12602step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5098 node5098Labels := by rfl

theorem canonical12607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12607 raw12607Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw12607 raw12607Labels = mixedMoment B raw12607step0 raw12607step0Labels := by
      have ha : raw12607step0 = (fun i j => raw12607 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12607step0 raw12607; decide +kernel
      have hl : raw12607step0Labels = raw12607Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12607 raw12607Labels permutation155 permutation3
    mixedMoment B raw12607step0 raw12607step0Labels = mixedMoment B raw12607step1 raw12607step1Labels := by
      have ha : raw12607step1 = raw12607step0 := by apply Matrix.ext; unfold raw12607step1 raw12607step0; decide +kernel
      have hl : raw12607step0Labels = labelEmbedding6 ∘ raw12607step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12607step0 raw12607step0Labels raw12607step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

theorem canonical12612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12612 raw12612Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw12612 raw12612Labels = mixedMoment B raw12612step0 raw12612step0Labels := by
      have ha : raw12612step0 = (fun i j => raw12612 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12612step0 raw12612; decide +kernel
      have hl : raw12612step0Labels = raw12612Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12612 raw12612Labels permutation153 permutation3
    mixedMoment B raw12612step0 raw12612step0Labels = mixedMoment B raw12612step1 raw12612step1Labels := by
      have ha : raw12612step1 = raw12612step0 := by apply Matrix.ext; unfold raw12612step1 raw12612step0; decide +kernel
      have hl : raw12612step0Labels = labelEmbedding6 ∘ raw12612step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12612step0 raw12612step0Labels raw12612step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

theorem canonical12617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12617 raw12617Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw12617 raw12617Labels = mixedMoment B raw12617step0 raw12617step0Labels := by
      have ha : raw12617step0 = (fun i j => raw12617 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12617step0 raw12617; decide +kernel
      have hl : raw12617step0Labels = raw12617Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12617 raw12617Labels permutation152 permutation3
    mixedMoment B raw12617step0 raw12617step0Labels = mixedMoment B raw12617step1 raw12617step1Labels := by
      have ha : raw12617step1 = raw12617step0 := by apply Matrix.ext; unfold raw12617step1 raw12617step0; decide +kernel
      have hl : raw12617step0Labels = labelEmbedding6 ∘ raw12617step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12617step0 raw12617step0Labels raw12617step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5072 node5072Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5072 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5072 node5072Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2479 node2479Labels + mixedMoment B node3459 node3459Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2091 singletonSmall5072
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5072) = raw2091Labels := by decide +kernel
  rw [hl, canonical2091 B hB] at h
  have hc0 : mixedMoment B raw2091 (Fin.cases (0 : Fin 2) singletonSmall5072) =
      mixedMoment B node2479 node2479Labels := by
    have ha : raw2091 = raw2092 := by apply Matrix.ext; unfold raw2091 raw2092; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5072 = raw2092Labels := by decide +kernel
    rw [ha, hj, canonical2092 B hB]
  have hc1 : mixedMoment B raw2091 (Fin.cases (1 : Fin 2) singletonSmall5072) =
      mixedMoment B node3459 node3459Labels := by
    have ha : raw2091 = raw2093 := by apply Matrix.ext; unfold raw2091 raw2093; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5072 = raw2093Labels := by decide +kernel
    rw [ha, hj, canonical2093 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5073 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5073 node5073Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2480 node2480Labels + mixedMoment B node3467 node3467Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2094 singletonSmall5073
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5073) = raw2094Labels := by decide +kernel
  rw [hl, canonical2094 B hB] at h
  have hc0 : mixedMoment B raw2094 (Fin.cases (0 : Fin 2) singletonSmall5073) =
      mixedMoment B node2480 node2480Labels := by
    have ha : raw2094 = raw2095 := by apply Matrix.ext; unfold raw2094 raw2095; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5073 = raw2095Labels := by decide +kernel
    rw [ha, hj, canonical2095 B hB]
  have hc1 : mixedMoment B raw2094 (Fin.cases (1 : Fin 2) singletonSmall5073) =
      mixedMoment B node3467 node3467Labels := by
    have ha : raw2094 = raw2096 := by apply Matrix.ext; unfold raw2094 raw2096; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5073 = raw2096Labels := by decide +kernel
    rw [ha, hj, canonical2096 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5098 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5098 node5098Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2508 node2508Labels + mixedMoment B node3460 node3460Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2121 singletonSmall5098
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5098) = raw2121Labels := by decide +kernel
  rw [hl, canonical2121 B hB] at h
  have hc0 : mixedMoment B raw2121 (Fin.cases (0 : Fin 2) singletonSmall5098) =
      mixedMoment B node2508 node2508Labels := by
    have ha : raw2121 = raw2122 := by apply Matrix.ext; unfold raw2121 raw2122; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5098 = raw2122Labels := by decide +kernel
    rw [ha, hj, canonical2122 B hB]
  have hc1 : mixedMoment B raw2121 (Fin.cases (1 : Fin 2) singletonSmall5098) =
      mixedMoment B node3460 node3460Labels := by
    have ha : raw2121 = raw2123 := by apply Matrix.ext; unfold raw2121 raw2123; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5098 = raw2123Labels := by decide +kernel
    rw [ha, hj, canonical2123 B hB]
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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5351 node5351Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3689 node3689Labels + mixedMoment B node3757 node3757Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2391 singletonSmall5351
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5351) = raw2391Labels := by decide +kernel
  rw [hl, canonical2391 B hB] at h
  have hc0 : mixedMoment B raw2391 (Fin.cases (0 : Fin 2) singletonSmall5351) =
      mixedMoment B node3689 node3689Labels := by
    have ha : raw2391 = raw2392 := by apply Matrix.ext; unfold raw2391 raw2392; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5351 = raw2392Labels := by decide +kernel
    rw [ha, hj, canonical2392 B hB]
  have hc1 : mixedMoment B raw2391 (Fin.cases (1 : Fin 2) singletonSmall5351) =
      mixedMoment B node3757 node3757Labels := by
    have ha : raw2391 = raw2393 := by apply Matrix.ext; unfold raw2391 raw2393; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5351 = raw2393Labels := by decide +kernel
    rw [ha, hj, canonical2393 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5352 node5352Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3690 node3690Labels + mixedMoment B node3764 node3764Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2394 singletonSmall5352
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5352) = raw2394Labels := by decide +kernel
  rw [hl, canonical2394 B hB] at h
  have hc0 : mixedMoment B raw2394 (Fin.cases (0 : Fin 2) singletonSmall5352) =
      mixedMoment B node3690 node3690Labels := by
    have ha : raw2394 = raw2395 := by apply Matrix.ext; unfold raw2394 raw2395; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5352 = raw2395Labels := by decide +kernel
    rw [ha, hj, canonical2395 B hB]
  have hc1 : mixedMoment B raw2394 (Fin.cases (1 : Fin 2) singletonSmall5352) =
      mixedMoment B node3764 node3764Labels := by
    have ha : raw2394 = raw2396 := by apply Matrix.ext; unfold raw2394 raw2396; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5352 = raw2396Labels := by decide +kernel
    rw [ha, hj, canonical2396 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5365 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5365 node5365Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3703 node3703Labels + mixedMoment B node3758 node3758Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2412 singletonSmall5365
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5365) = raw2412Labels := by decide +kernel
  rw [hl, canonical2412 B hB] at h
  have hc0 : mixedMoment B raw2412 (Fin.cases (0 : Fin 2) singletonSmall5365) =
      mixedMoment B node3703 node3703Labels := by
    have ha : raw2412 = raw2413 := by apply Matrix.ext; unfold raw2412 raw2413; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5365 = raw2413Labels := by decide +kernel
    rw [ha, hj, canonical2413 B hB]
  have hc1 : mixedMoment B raw2412 (Fin.cases (1 : Fin 2) singletonSmall5365) =
      mixedMoment B node3758 node3758Labels := by
    have ha : raw2412 = raw2414 := by apply Matrix.ext; unfold raw2412 raw2414; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5365 = raw2414Labels := by decide +kernel
    rw [ha, hj, canonical2414 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5380 node5380Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3721 node3721Labels + mixedMoment B node3836 node3836Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2433 singletonSmall5380
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5380) = raw2433Labels := by decide +kernel
  rw [hl, canonical2433 B hB] at h
  have hc0 : mixedMoment B raw2433 (Fin.cases (0 : Fin 2) singletonSmall5380) =
      mixedMoment B node3721 node3721Labels := by
    have ha : raw2433 = raw2434 := by apply Matrix.ext; unfold raw2433 raw2434; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5380 = raw2434Labels := by decide +kernel
    rw [ha, hj, canonical2434 B hB]
  have hc1 : mixedMoment B raw2433 (Fin.cases (1 : Fin 2) singletonSmall5380) =
      mixedMoment B node3836 node3836Labels := by
    have ha : raw2433 = raw2435 := by apply Matrix.ext; unfold raw2433 raw2435; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5380 = raw2435Labels := by decide +kernel
    rw [ha, hj, canonical2435 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5383 node5383Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3731 node3731Labels + mixedMoment B node3867 node3867Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2436 singletonSmall5383
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5383) = raw2436Labels := by decide +kernel
  rw [hl, canonical2436 B hB] at h
  have hc0 : mixedMoment B raw2436 (Fin.cases (0 : Fin 2) singletonSmall5383) =
      mixedMoment B node3731 node3731Labels := by
    have ha : raw2436 = raw2437 := by apply Matrix.ext; unfold raw2436 raw2437; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5383 = raw2437Labels := by decide +kernel
    rw [ha, hj, canonical2437 B hB]
  have hc1 : mixedMoment B raw2436 (Fin.cases (1 : Fin 2) singletonSmall5383) =
      mixedMoment B node3867 node3867Labels := by
    have ha : raw2436 = raw2438 := by apply Matrix.ext; unfold raw2436 raw2438; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5383 = raw2438Labels := by decide +kernel
    rw [ha, hj, canonical2438 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5406 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5406 node5406Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3801 node3801Labels + mixedMoment B node3812 node3812Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2487 singletonSmall5406
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5406) = raw2487Labels := by decide +kernel
  rw [hl, canonical2487 B hB] at h
  have hc0 : mixedMoment B raw2487 (Fin.cases (0 : Fin 2) singletonSmall5406) =
      mixedMoment B node3801 node3801Labels := by
    have ha : raw2487 = raw2488 := by apply Matrix.ext; unfold raw2487 raw2488; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5406 = raw2488Labels := by decide +kernel
    rw [ha, hj, canonical2488 B hB]
  have hc1 : mixedMoment B raw2487 (Fin.cases (1 : Fin 2) singletonSmall5406) =
      mixedMoment B node3812 node3812Labels := by
    have ha : raw2487 = raw2489 := by apply Matrix.ext; unfold raw2487 raw2489; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5406 = raw2489Labels := by decide +kernel
    rw [ha, hj, canonical2489 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5422 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5422 node5422Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3964 node3964Labels + mixedMoment B node3900 node3900Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2508 singletonSmall5422
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5422) = raw2508Labels := by decide +kernel
  rw [hl, canonical2508 B hB] at h
  have hc0 : mixedMoment B raw2508 (Fin.cases (0 : Fin 2) singletonSmall5422) =
      mixedMoment B node3964 node3964Labels := by
    have ha : raw2508 = raw2509 := by apply Matrix.ext; unfold raw2508 raw2509; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5422 = raw2509Labels := by decide +kernel
    rw [ha, hj, canonical2509 B hB]
  have hc1 : mixedMoment B raw2508 (Fin.cases (1 : Fin 2) singletonSmall5422) =
      mixedMoment B node3900 node3900Labels := by
    have ha : raw2508 = raw2510 := by apply Matrix.ext; unfold raw2508 raw2510; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5422 = raw2510Labels := by decide +kernel
    rw [ha, hj, canonical2510 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5424 node5424Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3838 node3838Labels + mixedMoment B node3843 node3843Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2514 singletonSmall5424
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5424) = raw2514Labels := by decide +kernel
  rw [hl, canonical2514 B hB] at h
  have hc0 : mixedMoment B raw2514 (Fin.cases (0 : Fin 2) singletonSmall5424) =
      mixedMoment B node3838 node3838Labels := by
    have ha : raw2514 = raw2515 := by apply Matrix.ext; unfold raw2514 raw2515; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5424 = raw2515Labels := by decide +kernel
    rw [ha, hj, canonical2515 B hB]
  have hc1 : mixedMoment B raw2514 (Fin.cases (1 : Fin 2) singletonSmall5424) =
      mixedMoment B node3843 node3843Labels := by
    have ha : raw2514 = raw2516 := by apply Matrix.ext; unfold raw2514 raw2516; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5424 = raw2516Labels := by decide +kernel
    rw [ha, hj, canonical2516 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5437 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5437 node5437Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3899 node3899Labels + mixedMoment B node3899 node3899Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2535 singletonSmall5437
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5437) = raw2535Labels := by decide +kernel
  rw [hl, canonical2535 B hB] at h
  have hc0 : mixedMoment B raw2535 (Fin.cases (0 : Fin 2) singletonSmall5437) =
      mixedMoment B node3899 node3899Labels := by
    have ha : raw2535 = raw2536 := by apply Matrix.ext; unfold raw2535 raw2536; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5437 = raw2536Labels := by decide +kernel
    rw [ha, hj, canonical2536 B hB]
  have hc1 : mixedMoment B raw2535 (Fin.cases (1 : Fin 2) singletonSmall5437) =
      mixedMoment B node3899 node3899Labels := by
    have ha : raw2535 = raw2537 := by apply Matrix.ext; unfold raw2535 raw2537; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5437 = raw2537Labels := by decide +kernel
    rw [ha, hj, canonical2537 B hB]
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

theorem singleton5469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5469 node5469Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3945 node3945Labels + mixedMoment B node3952 node3952Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2583 singletonSmall5469
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5469) = raw2583Labels := by decide +kernel
  rw [hl, canonical2583 B hB] at h
  have hc0 : mixedMoment B raw2583 (Fin.cases (0 : Fin 2) singletonSmall5469) =
      mixedMoment B node3945 node3945Labels := by
    have ha : raw2583 = raw2584 := by apply Matrix.ext; unfold raw2583 raw2584; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5469 = raw2584Labels := by decide +kernel
    rw [ha, hj, canonical2584 B hB]
  have hc1 : mixedMoment B raw2583 (Fin.cases (1 : Fin 2) singletonSmall5469) =
      mixedMoment B node3952 node3952Labels := by
    have ha : raw2583 = raw2585 := by apply Matrix.ext; unfold raw2583 raw2585; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5469 = raw2585Labels := by decide +kernel
    rw [ha, hj, canonical2585 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5478 node5478Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3974 node3974Labels + mixedMoment B node3974 node3974Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2598 singletonSmall5478
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5478) = raw2598Labels := by decide +kernel
  rw [hl, canonical2598 B hB] at h
  have hc0 : mixedMoment B raw2598 (Fin.cases (0 : Fin 2) singletonSmall5478) =
      mixedMoment B node3974 node3974Labels := by
    have ha : raw2598 = raw2599 := by apply Matrix.ext; unfold raw2598 raw2599; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5478 = raw2599Labels := by decide +kernel
    rw [ha, hj, canonical2599 B hB]
  have hc1 : mixedMoment B raw2598 (Fin.cases (1 : Fin 2) singletonSmall5478) =
      mixedMoment B node3974 node3974Labels := by
    have ha : raw2598 = raw2600 := by apply Matrix.ext; unfold raw2598 raw2600; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5478 = raw2600Labels := by decide +kernel
    rw [ha, hj, canonical2600 B hB]
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

theorem zero5474 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5474 node5474Labels = 0 := by
  exact mixedMoment_order_one B hB node5474 node5474Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5477 node5477Labels = 0 := by
  exact mixedMoment_alpha B hF node5477 node5477Labels 2 permutation152
    (by decide +kernel)

theorem zero5479 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5479 node5479Labels = 0 := by
  exact mixedMoment_order_one B hB node5479 node5479Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5486 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5486 node5486Labels = 0 := by
  exact mixedMoment_order_one B hB node5486 node5486Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5493 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5493 node5493Labels = 0 := by
  exact mixedMoment_order_one B hB node5493 node5493Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5497 node5497Labels = 0 := by
  exact mixedMoment_alpha B hF node5497 node5497Labels 0 permutation499
    (by decide +kernel)

theorem zero5499 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5499 node5499Labels = 0 := by
  exact mixedMoment_order_one B hB node5499 node5499Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2479 node2479Labels = Sparse.eval nodeValue2479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2479) = mixedMoment B node2479 node2479Labels := rfl
  simpa [nodeValue2479, Sparse.eval] using hc.symm

theorem sound2480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2480 node2480Labels = Sparse.eval nodeValue2480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2480) = mixedMoment B node2480 node2480Labels := rfl
  simpa [nodeValue2480, Sparse.eval] using hc.symm

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

theorem sound2508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2508 node2508Labels = Sparse.eval nodeValue2508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2508) = mixedMoment B node2508 node2508Labels := rfl
  simpa [nodeValue2508, Sparse.eval] using hc.symm

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

theorem sound3053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3053 node3053Labels = Sparse.eval nodeValue3053 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3053) = mixedMoment B node3053 node3053Labels := rfl
  simpa [nodeValue3053, Sparse.eval] using hc.symm

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

theorem sound3459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3459 node3459Labels = Sparse.eval nodeValue3459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3459) = mixedMoment B node3459 node3459Labels := rfl
  simpa [nodeValue3459, Sparse.eval] using hc.symm

theorem sound3460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3460 node3460Labels = Sparse.eval nodeValue3460 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3460) = mixedMoment B node3460 node3460Labels := rfl
  simpa [nodeValue3460, Sparse.eval] using hc.symm

theorem sound3467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3467 node3467Labels = Sparse.eval nodeValue3467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3467) = mixedMoment B node3467 node3467Labels := rfl
  simpa [nodeValue3467, Sparse.eval] using hc.symm

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

theorem sound3619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3619 node3619Labels = Sparse.eval nodeValue3619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3619) = mixedMoment B node3619 node3619Labels := rfl
  simpa [nodeValue3619, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3689 node3689Labels = Sparse.eval nodeValue3689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3689) = mixedMoment B node3689 node3689Labels := rfl
  simpa [nodeValue3689, Sparse.eval] using hc.symm

theorem sound3690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3690 node3690Labels = Sparse.eval nodeValue3690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3690) = mixedMoment B node3690 node3690Labels := rfl
  simpa [nodeValue3690, Sparse.eval] using hc.symm

theorem sound3703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3703 node3703Labels = Sparse.eval nodeValue3703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3703) = mixedMoment B node3703 node3703Labels := rfl
  simpa [nodeValue3703, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3721 node3721Labels = Sparse.eval nodeValue3721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3721) = mixedMoment B node3721 node3721Labels := rfl
  simpa [nodeValue3721, Sparse.eval] using hc.symm

theorem sound3731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3731 node3731Labels = Sparse.eval nodeValue3731 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3731) = mixedMoment B node3731 node3731Labels := rfl
  simpa [nodeValue3731, Sparse.eval] using hc.symm

theorem sound3757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3757 node3757Labels = Sparse.eval nodeValue3757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3757) = mixedMoment B node3757 node3757Labels := rfl
  simpa [nodeValue3757, Sparse.eval] using hc.symm

theorem sound3758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3758 node3758Labels = Sparse.eval nodeValue3758 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3758) = mixedMoment B node3758 node3758Labels := rfl
  simpa [nodeValue3758, Sparse.eval] using hc.symm

theorem sound3764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3764 node3764Labels = Sparse.eval nodeValue3764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3764) = mixedMoment B node3764 node3764Labels := rfl
  simpa [nodeValue3764, Sparse.eval] using hc.symm

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

theorem sound3801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3801 node3801Labels = Sparse.eval nodeValue3801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3801) = mixedMoment B node3801 node3801Labels := rfl
  simpa [nodeValue3801, Sparse.eval] using hc.symm

theorem sound3812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3812 node3812Labels = Sparse.eval nodeValue3812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3812) = mixedMoment B node3812 node3812Labels := rfl
  simpa [nodeValue3812, Sparse.eval] using hc.symm

theorem sound3836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3836 node3836Labels = Sparse.eval nodeValue3836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3836) = mixedMoment B node3836 node3836Labels := rfl
  simpa [nodeValue3836, Sparse.eval] using hc.symm

theorem sound3838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3838 node3838Labels = Sparse.eval nodeValue3838 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3838) = mixedMoment B node3838 node3838Labels := rfl
  simpa [nodeValue3838, Sparse.eval] using hc.symm

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

theorem sound3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3843 node3843Labels = Sparse.eval nodeValue3843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3843) = mixedMoment B node3843 node3843Labels := rfl
  simpa [nodeValue3843, Sparse.eval] using hc.symm

theorem sound3867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3867 node3867Labels = Sparse.eval nodeValue3867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3867) = mixedMoment B node3867 node3867Labels := rfl
  simpa [nodeValue3867, Sparse.eval] using hc.symm

theorem sound3899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3899 node3899Labels = Sparse.eval nodeValue3899 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3899) = mixedMoment B node3899 node3899Labels := rfl
  simpa [nodeValue3899, Sparse.eval] using hc.symm

theorem sound3900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3900 node3900Labels = Sparse.eval nodeValue3900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3900) = mixedMoment B node3900 node3900Labels := rfl
  simpa [nodeValue3900, Sparse.eval] using hc.symm

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

theorem sound3945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3945 node3945Labels = Sparse.eval nodeValue3945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3945) = mixedMoment B node3945 node3945Labels := rfl
  simpa [nodeValue3945, Sparse.eval] using hc.symm

theorem sound3952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3952 node3952Labels = Sparse.eval nodeValue3952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3952) = mixedMoment B node3952 node3952Labels := rfl
  simpa [nodeValue3952, Sparse.eval] using hc.symm

theorem sound3964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3964 node3964Labels = Sparse.eval nodeValue3964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3964) = mixedMoment B node3964 node3964Labels := rfl
  simpa [nodeValue3964, Sparse.eval] using hc.symm

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

theorem sound3974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3974 node3974Labels = Sparse.eval nodeValue3974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3974) = mixedMoment B node3974 node3974Labels := rfl
  simpa [nodeValue3974, Sparse.eval] using hc.symm

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

theorem sound4851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4851 node4851Labels = Sparse.eval nodeValue4851 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4851) = mixedMoment B node4851 node4851Labels := rfl
  simpa [nodeValue4851, Sparse.eval] using hc.symm

theorem sound4863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4863 node4863Labels = Sparse.eval nodeValue4863 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4863) = mixedMoment B node4863 node4863Labels := rfl
  simpa [nodeValue4863, Sparse.eval] using hc.symm

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

theorem sound4885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4885 node4885Labels = Sparse.eval nodeValue4885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4885) = mixedMoment B node4885 node4885Labels := rfl
  simpa [nodeValue4885, Sparse.eval] using hc.symm

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

theorem sound5072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5072 node5072Labels = Sparse.eval nodeValue5072 (mixedVector B) := by
  have h := singleton5072 B _hB
  rw [sound2479 B _hB _hF, sound3459 B _hB _hF] at h
  norm_num [nodeValue5072, nodeValue2479, nodeValue3459, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5073 node5073Labels = Sparse.eval nodeValue5073 (mixedVector B) := by
  have h := singleton5073 B _hB
  rw [sound2480 B _hB _hF, sound3467 B _hB _hF] at h
  norm_num [nodeValue5073, nodeValue2480, nodeValue3467, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5085 node5085Labels = Sparse.eval nodeValue5085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5085) = mixedMoment B node5085 node5085Labels := rfl
  simpa [nodeValue5085, Sparse.eval] using hc.symm

theorem sound5097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5097 node5097Labels = Sparse.eval nodeValue5097 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5097) = mixedMoment B node5097 node5097Labels := rfl
  simpa [nodeValue5097, Sparse.eval] using hc.symm

theorem sound5098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5098 node5098Labels = Sparse.eval nodeValue5098 (mixedVector B) := by
  have h := singleton5098 B _hB
  rw [sound2508 B _hB _hF, sound3460 B _hB _hF] at h
  norm_num [nodeValue5098, nodeValue2508, nodeValue3460, Sparse.eval] at h ⊢
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

theorem sound5277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5277 node5277Labels = Sparse.eval nodeValue5277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5277) = mixedMoment B node5277 node5277Labels := rfl
  simpa [nodeValue5277, Sparse.eval] using hc.symm

theorem sound5281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5281 node5281Labels = Sparse.eval nodeValue5281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5281) = mixedMoment B node5281 node5281Labels := rfl
  simpa [nodeValue5281, Sparse.eval] using hc.symm

theorem sound5301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5301 node5301Labels = Sparse.eval nodeValue5301 (mixedVector B) := by
  have h := singleton5301 B _hB
  rw [sound3053 B _hB _hF, sound3619 B _hB _hF] at h
  norm_num [nodeValue5301, nodeValue3053, nodeValue3619, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5351 node5351Labels = Sparse.eval nodeValue5351 (mixedVector B) := by
  have h := singleton5351 B _hB
  rw [sound3689 B _hB _hF, sound3757 B _hB _hF] at h
  norm_num [nodeValue5351, nodeValue3689, nodeValue3757, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5352 node5352Labels = Sparse.eval nodeValue5352 (mixedVector B) := by
  have h := singleton5352 B _hB
  rw [sound3690 B _hB _hF, sound3764 B _hB _hF] at h
  norm_num [nodeValue5352, nodeValue3690, nodeValue3764, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5359 node5359Labels = Sparse.eval nodeValue5359 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5359) = mixedMoment B node5359 node5359Labels := rfl
  simpa [nodeValue5359, Sparse.eval] using hc.symm

theorem sound5365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5365 node5365Labels = Sparse.eval nodeValue5365 (mixedVector B) := by
  have h := singleton5365 B _hB
  rw [sound3703 B _hB _hF, sound3758 B _hB _hF] at h
  norm_num [nodeValue5365, nodeValue3703, nodeValue3758, Sparse.eval] at h ⊢
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

theorem zero5427 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5427 node5427Labels = 0 := by
  exact mixedMoment_order_one B hB node5427 node5427Labels 1
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

theorem sound5380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5380 node5380Labels = Sparse.eval nodeValue5380 (mixedVector B) := by
  have h := singleton5380 B _hB
  rw [sound3721 B _hB _hF, sound3836 B _hB _hF] at h
  norm_num [nodeValue5380, nodeValue3721, nodeValue3836, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5383 node5383Labels = Sparse.eval nodeValue5383 (mixedVector B) := by
  have h := singleton5383 B _hB
  rw [sound3731 B _hB _hF, sound3867 B _hB _hF] at h
  norm_num [nodeValue5383, nodeValue3731, nodeValue3867, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5406 node5406Labels = Sparse.eval nodeValue5406 (mixedVector B) := by
  have h := singleton5406 B _hB
  rw [sound3801 B _hB _hF, sound3812 B _hB _hF] at h
  norm_num [nodeValue5406, nodeValue3801, nodeValue3812, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5422 node5422Labels = Sparse.eval nodeValue5422 (mixedVector B) := by
  have h := singleton5422 B _hB
  rw [sound3900 B _hB _hF, sound3964 B _hB _hF] at h
  norm_num [nodeValue5422, nodeValue3900, nodeValue3964, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5424 node5424Labels = Sparse.eval nodeValue5424 (mixedVector B) := by
  have h := singleton5424 B _hB
  rw [sound3838 B _hB _hF, sound3843 B _hB _hF] at h
  norm_num [nodeValue5424, nodeValue3838, nodeValue3843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5427 node5427Labels = Sparse.eval nodeValue5427 (mixedVector B) := by
  simpa only [nodeValue5427, Sparse.eval_nil] using zero5427 B _hB _hF

theorem sound5429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5429 node5429Labels = Sparse.eval nodeValue5429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5429) = mixedMoment B node5429 node5429Labels := rfl
  simpa [nodeValue5429, Sparse.eval] using hc.symm

theorem sound5430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5430 node5430Labels = Sparse.eval nodeValue5430 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5430) = mixedMoment B node5430 node5430Labels := rfl
  simpa [nodeValue5430, Sparse.eval] using hc.symm

theorem sound5437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5437 node5437Labels = Sparse.eval nodeValue5437 (mixedVector B) := by
  have h := singleton5437 B _hB
  rw [sound3899 B _hB _hF] at h
  norm_num [nodeValue5437, nodeValue3899, Sparse.eval] at h ⊢
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

theorem sound5445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5445 node5445Labels = Sparse.eval nodeValue5445 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5445) = mixedMoment B node5445 node5445Labels := rfl
  simpa [nodeValue5445, Sparse.eval] using hc.symm

theorem sound5469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5469 node5469Labels = Sparse.eval nodeValue5469 (mixedVector B) := by
  have h := singleton5469 B _hB
  rw [sound3945 B _hB _hF, sound3952 B _hB _hF] at h
  norm_num [nodeValue5469, nodeValue3945, nodeValue3952, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5474 node5474Labels = Sparse.eval nodeValue5474 (mixedVector B) := by
  simpa only [nodeValue5474, Sparse.eval_nil] using zero5474 B _hB _hF

theorem sound5477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5477 node5477Labels = Sparse.eval nodeValue5477 (mixedVector B) := by
  simpa only [nodeValue5477, Sparse.eval_nil] using zero5477 B _hB _hF

theorem sound5478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5478 node5478Labels = Sparse.eval nodeValue5478 (mixedVector B) := by
  have h := singleton5478 B _hB
  rw [sound3974 B _hB _hF] at h
  norm_num [nodeValue5478, nodeValue3974, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5479 node5479Labels = Sparse.eval nodeValue5479 (mixedVector B) := by
  simpa only [nodeValue5479, Sparse.eval_nil] using zero5479 B _hB _hF

theorem sound5486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5486 node5486Labels = Sparse.eval nodeValue5486 (mixedVector B) := by
  simpa only [nodeValue5486, Sparse.eval_nil] using zero5486 B _hB _hF

theorem sound5493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5493 node5493Labels = Sparse.eval nodeValue5493 (mixedVector B) := by
  simpa only [nodeValue5493, Sparse.eval_nil] using zero5493 B _hB _hF

theorem sound5497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5497 node5497Labels = Sparse.eval nodeValue5497 (mixedVector B) := by
  simpa only [nodeValue5497, Sparse.eval_nil] using zero5497 B _hB _hF

theorem sound5499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5499 node5499Labels = Sparse.eval nodeValue5499 (mixedVector B) := by
  simpa only [nodeValue5499, Sparse.eval_nil] using zero5499 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources34
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1107 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1107 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1107 + difference 0 1) (sourceB1107 + difference 1 0) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5427) := by
    have ha : (tripleCharges (sourceA1107 + difference 0 1) (sourceB1107 + difference 1 0) sourceC1107) = raw18573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18573; decide +kernel
    rw [ha]
    exact (canonical18573 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1107 + difference 0 2) (sourceB1107 + difference 2 0) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5479) := by
    have ha : (tripleCharges (sourceA1107 + difference 0 2) (sourceB1107 + difference 2 0) sourceC1107) = raw18574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18574; decide +kernel
    rw [ha]
    exact (canonical18574 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1107 + difference 0 3) (sourceB1107 + difference 3 0) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1107 + difference 0 3) (sourceB1107 + difference 3 0) sourceC1107) = raw18575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18575; decide +kernel
    rw [ha]
    exact (canonical18575 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1107 + difference 0 4) (sourceB1107 + difference 4 0) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1107 + difference 0 4) (sourceB1107 + difference 4 0) sourceC1107) = raw18576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18576; decide +kernel
    rw [ha]
    exact (canonical18576 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1107 + difference 0 5) (sourceB1107 + difference 5 0) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1107 + difference 0 5) (sourceB1107 + difference 5 0) sourceC1107) = raw18577 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18577; decide +kernel
    rw [ha]
    exact (canonical18577 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1107 + difference 1 0) (sourceB1107 + difference 0 1) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA1107 + difference 1 0) (sourceB1107 + difference 0 1) sourceC1107) = raw18578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18578; decide +kernel
    rw [ha]
    exact (canonical18578 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1107 + difference 1 2) (sourceB1107 + difference 2 1) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA1107 + difference 1 2) (sourceB1107 + difference 2 1) sourceC1107) = raw18579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18579; decide +kernel
    rw [ha]
    exact (canonical18579 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1107 + difference 1 3) (sourceB1107 + difference 3 1) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1107 + difference 1 3) (sourceB1107 + difference 3 1) sourceC1107) = raw18580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18580; decide +kernel
    rw [ha]
    exact (canonical18580 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1107 + difference 1 4) (sourceB1107 + difference 4 1) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1107 + difference 1 4) (sourceB1107 + difference 4 1) sourceC1107) = raw18581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18581; decide +kernel
    rw [ha]
    exact (canonical18581 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1107 + difference 1 5) (sourceB1107 + difference 5 1) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1107 + difference 1 5) (sourceB1107 + difference 5 1) sourceC1107) = raw18582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18582; decide +kernel
    rw [ha]
    exact (canonical18582 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1107 + difference 2 0) (sourceB1107 + difference 0 2) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4863) := by
    have ha : (tripleCharges (sourceA1107 + difference 2 0) (sourceB1107 + difference 0 2) sourceC1107) = raw18583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18583; decide +kernel
    rw [ha]
    exact (canonical18583 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1107 + difference 2 1) (sourceB1107 + difference 1 2) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA1107 + difference 2 1) (sourceB1107 + difference 1 2) sourceC1107) = raw18584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18584; decide +kernel
    rw [ha]
    exact (canonical18584 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1107 + difference 2 3) (sourceB1107 + difference 3 2) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1107 + difference 2 3) (sourceB1107 + difference 3 2) sourceC1107) = raw18585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18585; decide +kernel
    rw [ha]
    exact (canonical18585 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1107 + difference 2 4) (sourceB1107 + difference 4 2) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1107 + difference 2 4) (sourceB1107 + difference 4 2) sourceC1107) = raw18586 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18586; decide +kernel
    rw [ha]
    exact (canonical18586 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1107 + difference 2 5) (sourceB1107 + difference 5 2) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1107 + difference 2 5) (sourceB1107 + difference 5 2) sourceC1107) = raw18587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18587; decide +kernel
    rw [ha]
    exact (canonical18587 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1107 + difference 3 0) (sourceB1107 + difference 0 3) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA1107 + difference 3 0) (sourceB1107 + difference 0 3) sourceC1107) = raw18588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18588; decide +kernel
    rw [ha]
    exact (canonical18588 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1107 + difference 3 1) (sourceB1107 + difference 1 3) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA1107 + difference 3 1) (sourceB1107 + difference 1 3) sourceC1107) = raw18589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18589; decide +kernel
    rw [ha]
    exact (canonical18589 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1107 + difference 3 2) (sourceB1107 + difference 2 3) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1107 + difference 3 2) (sourceB1107 + difference 2 3) sourceC1107) = raw18590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18590; decide +kernel
    rw [ha]
    exact (canonical18590 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1107 + difference 3 4) (sourceB1107 + difference 4 3) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1107 + difference 3 4) (sourceB1107 + difference 4 3) sourceC1107) = raw18591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18591; decide +kernel
    rw [ha]
    exact (canonical18591 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1107 + difference 3 5) (sourceB1107 + difference 5 3) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1107 + difference 3 5) (sourceB1107 + difference 5 3) sourceC1107) = raw18592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18592; decide +kernel
    rw [ha]
    exact (canonical18592 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1107 + difference 4 0) (sourceB1107 + difference 0 4) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA1107 + difference 4 0) (sourceB1107 + difference 0 4) sourceC1107) = raw18593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18593; decide +kernel
    rw [ha]
    exact (canonical18593 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1107 + difference 4 1) (sourceB1107 + difference 1 4) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA1107 + difference 4 1) (sourceB1107 + difference 1 4) sourceC1107) = raw18594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18594; decide +kernel
    rw [ha]
    exact (canonical18594 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1107 + difference 4 2) (sourceB1107 + difference 2 4) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1107 + difference 4 2) (sourceB1107 + difference 2 4) sourceC1107) = raw18595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18595; decide +kernel
    rw [ha]
    exact (canonical18595 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1107 + difference 4 3) (sourceB1107 + difference 3 4) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1107 + difference 4 3) (sourceB1107 + difference 3 4) sourceC1107) = raw18596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18596; decide +kernel
    rw [ha]
    exact (canonical18596 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1107 + difference 4 5) (sourceB1107 + difference 5 4) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1107 + difference 4 5) (sourceB1107 + difference 5 4) sourceC1107) = raw18597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18597; decide +kernel
    rw [ha]
    exact (canonical18597 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1107 + difference 5 0) (sourceB1107 + difference 0 5) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA1107 + difference 5 0) (sourceB1107 + difference 0 5) sourceC1107) = raw18598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18598; decide +kernel
    rw [ha]
    exact (canonical18598 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1107 + difference 5 1) (sourceB1107 + difference 1 5) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA1107 + difference 5 1) (sourceB1107 + difference 1 5) sourceC1107) = raw18599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18599; decide +kernel
    rw [ha]
    exact (canonical18599 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1107 + difference 5 2) (sourceB1107 + difference 2 5) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1107 + difference 5 2) (sourceB1107 + difference 2 5) sourceC1107) = raw18600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18600; decide +kernel
    rw [ha]
    exact (canonical18600 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1107 + difference 5 3) (sourceB1107 + difference 3 5) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1107 + difference 5 3) (sourceB1107 + difference 3 5) sourceC1107) = raw18601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18601; decide +kernel
    rw [ha]
    exact (canonical18601 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1107 + difference 5 4) (sourceB1107 + difference 4 5) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1107 + difference 5 4) (sourceB1107 + difference 4 5) sourceC1107) = raw18602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18602; decide +kernel
    rw [ha]
    exact (canonical18602 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1107 sourceB1107 sourceC1107
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1107, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1108 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1108 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1108 + difference 0 1) (sourceB1108 + difference 1 0) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5479) := by
    have ha : (tripleCharges (sourceA1108 + difference 0 1) (sourceB1108 + difference 1 0) sourceC1108) = raw18407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18407; decide +kernel
    rw [ha]
    exact (canonical18407 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1108 + difference 0 2) (sourceB1108 + difference 2 0) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5474) := by
    have ha : (tripleCharges (sourceA1108 + difference 0 2) (sourceB1108 + difference 2 0) sourceC1108) = raw18510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18510; decide +kernel
    rw [ha]
    exact (canonical18510 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1108 + difference 0 3) (sourceB1108 + difference 3 0) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1108 + difference 0 3) (sourceB1108 + difference 3 0) sourceC1108) = raw18603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18603; decide +kernel
    rw [ha]
    exact (canonical18603 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1108 + difference 0 4) (sourceB1108 + difference 4 0) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1108 + difference 0 4) (sourceB1108 + difference 4 0) sourceC1108) = raw18604 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18604; decide +kernel
    rw [ha]
    exact (canonical18604 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1108 + difference 0 5) (sourceB1108 + difference 5 0) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1108 + difference 0 5) (sourceB1108 + difference 5 0) sourceC1108) = raw18605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18605; decide +kernel
    rw [ha]
    exact (canonical18605 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1108 + difference 1 0) (sourceB1108 + difference 0 1) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5097) := by
    have ha : (tripleCharges (sourceA1108 + difference 1 0) (sourceB1108 + difference 0 1) sourceC1108) = raw18606 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18606; decide +kernel
    rw [ha]
    exact (canonical18606 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1108 + difference 1 2) (sourceB1108 + difference 2 1) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA1108 + difference 1 2) (sourceB1108 + difference 2 1) sourceC1108) = raw18515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18515; decide +kernel
    rw [ha]
    exact (canonical18515 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1108 + difference 1 3) (sourceB1108 + difference 3 1) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA1108 + difference 1 3) (sourceB1108 + difference 3 1) sourceC1108) = raw18607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18607; decide +kernel
    rw [ha]
    exact (canonical18607 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1108 + difference 1 4) (sourceB1108 + difference 4 1) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA1108 + difference 1 4) (sourceB1108 + difference 4 1) sourceC1108) = raw18608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18608; decide +kernel
    rw [ha]
    exact (canonical18608 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1108 + difference 1 5) (sourceB1108 + difference 5 1) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA1108 + difference 1 5) (sourceB1108 + difference 5 1) sourceC1108) = raw18609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18609; decide +kernel
    rw [ha]
    exact (canonical18609 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1108 + difference 2 0) (sourceB1108 + difference 0 2) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5277) := by
    have ha : (tripleCharges (sourceA1108 + difference 2 0) (sourceB1108 + difference 0 2) sourceC1108) = raw18610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18610; decide +kernel
    rw [ha]
    exact (canonical18610 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1108 + difference 2 1) (sourceB1108 + difference 1 2) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA1108 + difference 2 1) (sourceB1108 + difference 1 2) sourceC1108) = raw18417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18417; decide +kernel
    rw [ha]
    exact (canonical18417 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1108 + difference 2 3) (sourceB1108 + difference 3 2) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA1108 + difference 2 3) (sourceB1108 + difference 3 2) sourceC1108) = raw18611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18611; decide +kernel
    rw [ha]
    exact (canonical18611 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1108 + difference 2 4) (sourceB1108 + difference 4 2) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA1108 + difference 2 4) (sourceB1108 + difference 4 2) sourceC1108) = raw18612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18612; decide +kernel
    rw [ha]
    exact (canonical18612 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1108 + difference 2 5) (sourceB1108 + difference 5 2) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA1108 + difference 2 5) (sourceB1108 + difference 5 2) sourceC1108) = raw18613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18613; decide +kernel
    rw [ha]
    exact (canonical18613 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1108 + difference 3 0) (sourceB1108 + difference 0 3) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA1108 + difference 3 0) (sourceB1108 + difference 0 3) sourceC1108) = raw18614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18614; decide +kernel
    rw [ha]
    exact (canonical18614 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1108 + difference 3 1) (sourceB1108 + difference 1 3) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1108 + difference 3 1) (sourceB1108 + difference 1 3) sourceC1108) = raw18422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18422; decide +kernel
    rw [ha]
    exact (canonical18422 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1108 + difference 3 2) (sourceB1108 + difference 2 3) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1108 + difference 3 2) (sourceB1108 + difference 2 3) sourceC1108) = raw18520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18520; decide +kernel
    rw [ha]
    exact (canonical18520 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1108 + difference 3 4) (sourceB1108 + difference 4 3) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1108 + difference 3 4) (sourceB1108 + difference 4 3) sourceC1108) = raw18615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18615; decide +kernel
    rw [ha]
    exact (canonical18615 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1108 + difference 3 5) (sourceB1108 + difference 5 3) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1108 + difference 3 5) (sourceB1108 + difference 5 3) sourceC1108) = raw18616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18616; decide +kernel
    rw [ha]
    exact (canonical18616 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1108 + difference 4 0) (sourceB1108 + difference 0 4) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA1108 + difference 4 0) (sourceB1108 + difference 0 4) sourceC1108) = raw18617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18617; decide +kernel
    rw [ha]
    exact (canonical18617 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1108 + difference 4 1) (sourceB1108 + difference 1 4) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1108 + difference 4 1) (sourceB1108 + difference 1 4) sourceC1108) = raw18427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18427; decide +kernel
    rw [ha]
    exact (canonical18427 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1108 + difference 4 2) (sourceB1108 + difference 2 4) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1108 + difference 4 2) (sourceB1108 + difference 2 4) sourceC1108) = raw18524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18524; decide +kernel
    rw [ha]
    exact (canonical18524 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1108 + difference 4 3) (sourceB1108 + difference 3 4) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1108 + difference 4 3) (sourceB1108 + difference 3 4) sourceC1108) = raw18618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18618; decide +kernel
    rw [ha]
    exact (canonical18618 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1108 + difference 4 5) (sourceB1108 + difference 5 4) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1108 + difference 4 5) (sourceB1108 + difference 5 4) sourceC1108) = raw18619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18619; decide +kernel
    rw [ha]
    exact (canonical18619 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1108 + difference 5 0) (sourceB1108 + difference 0 5) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA1108 + difference 5 0) (sourceB1108 + difference 0 5) sourceC1108) = raw18408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18408; decide +kernel
    rw [ha]
    exact (canonical18408 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1108 + difference 5 1) (sourceB1108 + difference 1 5) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1108 + difference 5 1) (sourceB1108 + difference 1 5) sourceC1108) = raw18516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18516; decide +kernel
    rw [ha]
    exact (canonical18516 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1108 + difference 5 2) (sourceB1108 + difference 2 5) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1108 + difference 5 2) (sourceB1108 + difference 2 5) sourceC1108) = raw18409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18409; decide +kernel
    rw [ha]
    exact (canonical18409 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1108 + difference 5 3) (sourceB1108 + difference 3 5) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1108 + difference 5 3) (sourceB1108 + difference 3 5) sourceC1108) = raw18410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18410; decide +kernel
    rw [ha]
    exact (canonical18410 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1108 + difference 5 4) (sourceB1108 + difference 4 5) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1108 + difference 5 4) (sourceB1108 + difference 4 5) sourceC1108) = raw18411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18411; decide +kernel
    rw [ha]
    exact (canonical18411 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1108 sourceB1108 sourceC1108
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1108, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1117 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1117 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1117 + difference 0 1) (sourceB1117 + difference 1 0) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1117 + difference 0 1) (sourceB1117 + difference 1 0) sourceC1117) = raw18787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18787; decide +kernel
    rw [ha]
    exact (canonical18787 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1117 + difference 0 2) (sourceB1117 + difference 2 0) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5497) := by
    have ha : (tripleCharges (sourceA1117 + difference 0 2) (sourceB1117 + difference 2 0) sourceC1117) = raw18788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18788; decide +kernel
    rw [ha]
    exact (canonical18788 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1117 + difference 0 3) (sourceB1117 + difference 3 0) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA1117 + difference 0 3) (sourceB1117 + difference 3 0) sourceC1117) = raw17585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw17585; decide +kernel
    rw [ha]
    exact (canonical17585 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1117 + difference 0 4) (sourceB1117 + difference 4 0) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA1117 + difference 0 4) (sourceB1117 + difference 4 0) sourceC1117) = raw18789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18789; decide +kernel
    rw [ha]
    exact (canonical18789 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1117 + difference 0 5) (sourceB1117 + difference 5 0) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA1117 + difference 0 5) (sourceB1117 + difference 5 0) sourceC1117) = raw18790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18790; decide +kernel
    rw [ha]
    exact (canonical18790 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1117 + difference 1 0) (sourceB1117 + difference 0 1) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1117 + difference 1 0) (sourceB1117 + difference 0 1) sourceC1117) = raw18791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18791; decide +kernel
    rw [ha]
    exact (canonical18791 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1117 + difference 1 2) (sourceB1117 + difference 2 1) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1117 + difference 1 2) (sourceB1117 + difference 2 1) sourceC1117) = raw12592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw12592; decide +kernel
    rw [ha]
    exact (canonical12592 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1117 + difference 1 3) (sourceB1117 + difference 3 1) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1117 + difference 1 3) (sourceB1117 + difference 3 1) sourceC1117) = raw12593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw12593; decide +kernel
    rw [ha]
    exact (canonical12593 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1117 + difference 1 4) (sourceB1117 + difference 4 1) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1117 + difference 1 4) (sourceB1117 + difference 4 1) sourceC1117) = raw12594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw12594; decide +kernel
    rw [ha]
    exact (canonical12594 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1117 + difference 1 5) (sourceB1117 + difference 5 1) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA1117 + difference 1 5) (sourceB1117 + difference 5 1) sourceC1117) = raw12595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw12595; decide +kernel
    rw [ha]
    exact (canonical12595 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1117 + difference 2 0) (sourceB1117 + difference 0 2) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA1117 + difference 2 0) (sourceB1117 + difference 0 2) sourceC1117) = raw12602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw12602; decide +kernel
    rw [ha]
    exact (canonical12602 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1117 + difference 2 1) (sourceB1117 + difference 1 2) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA1117 + difference 2 1) (sourceB1117 + difference 1 2) sourceC1117) = raw18792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18792; decide +kernel
    rw [ha]
    exact (canonical18792 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1117 + difference 2 3) (sourceB1117 + difference 3 2) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1117 + difference 2 3) (sourceB1117 + difference 3 2) sourceC1117) = raw17593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw17593; decide +kernel
    rw [ha]
    exact (canonical17593 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1117 + difference 2 4) (sourceB1117 + difference 4 2) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1117 + difference 2 4) (sourceB1117 + difference 4 2) sourceC1117) = raw18793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18793; decide +kernel
    rw [ha]
    exact (canonical18793 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1117 + difference 2 5) (sourceB1117 + difference 5 2) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1117 + difference 2 5) (sourceB1117 + difference 5 2) sourceC1117) = raw18794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18794; decide +kernel
    rw [ha]
    exact (canonical18794 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1117 + difference 3 0) (sourceB1117 + difference 0 3) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA1117 + difference 3 0) (sourceB1117 + difference 0 3) sourceC1117) = raw12607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw12607; decide +kernel
    rw [ha]
    exact (canonical12607 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1117 + difference 3 1) (sourceB1117 + difference 1 3) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1117 + difference 3 1) (sourceB1117 + difference 1 3) sourceC1117) = raw18795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18795; decide +kernel
    rw [ha]
    exact (canonical18795 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1117 + difference 3 2) (sourceB1117 + difference 2 3) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5476) := by
    have ha : (tripleCharges (sourceA1117 + difference 3 2) (sourceB1117 + difference 2 3) sourceC1117) = raw18796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18796; decide +kernel
    rw [ha]
    exact (canonical18796 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1117 + difference 3 4) (sourceB1117 + difference 4 3) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1117 + difference 3 4) (sourceB1117 + difference 4 3) sourceC1117) = raw18797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18797; decide +kernel
    rw [ha]
    exact (canonical18797 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1117 + difference 3 5) (sourceB1117 + difference 5 3) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1117 + difference 3 5) (sourceB1117 + difference 5 3) sourceC1117) = raw18798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18798; decide +kernel
    rw [ha]
    exact (canonical18798 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1117 + difference 4 0) (sourceB1117 + difference 0 4) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA1117 + difference 4 0) (sourceB1117 + difference 0 4) sourceC1117) = raw12612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw12612; decide +kernel
    rw [ha]
    exact (canonical12612 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1117 + difference 4 1) (sourceB1117 + difference 1 4) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1117 + difference 4 1) (sourceB1117 + difference 1 4) sourceC1117) = raw18799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18799; decide +kernel
    rw [ha]
    exact (canonical18799 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1117 + difference 4 2) (sourceB1117 + difference 2 4) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5476) := by
    have ha : (tripleCharges (sourceA1117 + difference 4 2) (sourceB1117 + difference 2 4) sourceC1117) = raw18800 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18800; decide +kernel
    rw [ha]
    exact (canonical18800 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1117 + difference 4 3) (sourceB1117 + difference 3 4) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1117 + difference 4 3) (sourceB1117 + difference 3 4) sourceC1117) = raw17601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw17601; decide +kernel
    rw [ha]
    exact (canonical17601 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1117 + difference 4 5) (sourceB1117 + difference 5 4) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1117 + difference 4 5) (sourceB1117 + difference 5 4) sourceC1117) = raw18801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18801; decide +kernel
    rw [ha]
    exact (canonical18801 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1117 + difference 5 0) (sourceB1117 + difference 0 5) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA1117 + difference 5 0) (sourceB1117 + difference 0 5) sourceC1117) = raw12617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw12617; decide +kernel
    rw [ha]
    exact (canonical12617 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1117 + difference 5 1) (sourceB1117 + difference 1 5) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA1117 + difference 5 1) (sourceB1117 + difference 1 5) sourceC1117) = raw17594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw17594; decide +kernel
    rw [ha]
    exact (canonical17594 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1117 + difference 5 2) (sourceB1117 + difference 2 5) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA1117 + difference 5 2) (sourceB1117 + difference 2 5) sourceC1117) = raw17595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw17595; decide +kernel
    rw [ha]
    exact (canonical17595 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1117 + difference 5 3) (sourceB1117 + difference 3 5) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1117 + difference 5 3) (sourceB1117 + difference 3 5) sourceC1117) = raw18802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18802; decide +kernel
    rw [ha]
    exact (canonical18802 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1117 + difference 5 4) (sourceB1117 + difference 4 5) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1117 + difference 5 4) (sourceB1117 + difference 4 5) sourceC1117) = raw17596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw17596; decide +kernel
    rw [ha]
    exact (canonical17596 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1117 sourceB1117 sourceC1117
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1117, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck960 : Integer.Sparse.reindex keyMap MixedData.row960 = numericRow960 := by decide +kernel

theorem numericCheck960 (x : Master → ℝ) : Integer.Sparse.eval numericRow960 x =
    (5760 : ℝ) * reducedSource960 x := by
  norm_num [numericRow960, reducedSource960, Integer.Sparse.eval, Sparse.eval, nodeValue4851, nodeValue4863, nodeValue4885, nodeValue5380, nodeValue5383, nodeValue5406, nodeValue5422, nodeValue5427, nodeValue5429, nodeValue5430, nodeValue5437, nodeValue5479, nodeValue5482]
  ring

theorem reindexCheck961 : Integer.Sparse.reindex keyMap MixedData.row961 = numericRow961 := by decide +kernel

theorem numericCheck961 (x : Master → ℝ) : Integer.Sparse.eval numericRow961 x =
    (5760 : ℝ) * reducedSource961 x := by
  norm_num [numericRow961, reducedSource961, Integer.Sparse.eval, Sparse.eval, nodeValue5085, nodeValue5097, nodeValue5277, nodeValue5281, nodeValue5301, nodeValue5359, nodeValue5433, nodeValue5437, nodeValue5445, nodeValue5450, nodeValue5469, nodeValue5474, nodeValue5479]
  ring

theorem reindexCheck969 : Integer.Sparse.reindex keyMap MixedData.row969 = numericRow969 := by decide +kernel

theorem numericCheck969 (x : Master → ℝ) : Integer.Sparse.eval numericRow969 x =
    (17280 : ℝ) * reducedSource969 x := by
  norm_num [numericRow969, reducedSource969, Integer.Sparse.eval, Sparse.eval, nodeValue5072, nodeValue5073, nodeValue5098, nodeValue5292, nodeValue5351, nodeValue5352, nodeValue5365, nodeValue5416, nodeValue5424, nodeValue5433, nodeValue5476, nodeValue5477, nodeValue5478, nodeValue5483, nodeValue5485, nodeValue5486, nodeValue5490, nodeValue5493, nodeValue5497, nodeValue5499, nodeValue5500]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero960 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource960 (mixedVector B) = 0 := by
  have h4851 : mixedVector B (Sum.inr 4851) = Sparse.eval nodeValue4851 (mixedVector B) := by
    change mixedMoment B node4851 node4851Labels = _
    exact sound4851 B hB hF
  have h4863 : mixedVector B (Sum.inr 4863) = Sparse.eval nodeValue4863 (mixedVector B) := by
    change mixedMoment B node4863 node4863Labels = _
    exact sound4863 B hB hF
  have h4885 : mixedVector B (Sum.inr 4885) = Sparse.eval nodeValue4885 (mixedVector B) := by
    change mixedMoment B node4885 node4885Labels = _
    exact sound4885 B hB hF
  have h5380 : mixedVector B (Sum.inr 5380) = Sparse.eval nodeValue5380 (mixedVector B) := by
    change mixedMoment B node5380 node5380Labels = _
    exact sound5380 B hB hF
  have h5383 : mixedVector B (Sum.inr 5383) = Sparse.eval nodeValue5383 (mixedVector B) := by
    change mixedMoment B node5383 node5383Labels = _
    exact sound5383 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5422 : mixedVector B (Sum.inr 5422) = Sparse.eval nodeValue5422 (mixedVector B) := by
    change mixedMoment B node5422 node5422Labels = _
    exact sound5422 B hB hF
  have h5427 : mixedVector B (Sum.inr 5427) = Sparse.eval nodeValue5427 (mixedVector B) := by
    change mixedMoment B node5427 node5427Labels = _
    exact sound5427 B hB hF
  have h5429 : mixedVector B (Sum.inr 5429) = Sparse.eval nodeValue5429 (mixedVector B) := by
    change mixedMoment B node5429 node5429Labels = _
    exact sound5429 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5437 : mixedVector B (Sum.inr 5437) = Sparse.eval nodeValue5437 (mixedVector B) := by
    change mixedMoment B node5437 node5437Labels = _
    exact sound5437 B hB hF
  have h5479 : mixedVector B (Sum.inr 5479) = Sparse.eval nodeValue5479 (mixedVector B) := by
    change mixedMoment B node5479 node5479Labels = _
    exact sound5479 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482_e B hB hF
  simpa only [sourceForm1107, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4851, h4863, h4885, h5380, h5383, h5406, h5422, h5427, h5429, h5430, h5437, h5479, h5482, reducedSource960] using sourceEq1107 B hB

theorem rowSound960 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row960 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck960, numericCheck960, reducedZero960 B hB hF, mul_zero]

theorem reducedZero961 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource961 (mixedVector B) = 0 := by
  have h5085 : mixedVector B (Sum.inr 5085) = Sparse.eval nodeValue5085 (mixedVector B) := by
    change mixedMoment B node5085 node5085Labels = _
    exact sound5085 B hB hF
  have h5097 : mixedVector B (Sum.inr 5097) = Sparse.eval nodeValue5097 (mixedVector B) := by
    change mixedMoment B node5097 node5097Labels = _
    exact sound5097 B hB hF
  have h5277 : mixedVector B (Sum.inr 5277) = Sparse.eval nodeValue5277 (mixedVector B) := by
    change mixedMoment B node5277 node5277Labels = _
    exact sound5277 B hB hF
  have h5281 : mixedVector B (Sum.inr 5281) = Sparse.eval nodeValue5281 (mixedVector B) := by
    change mixedMoment B node5281 node5281Labels = _
    exact sound5281 B hB hF
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  have h5359 : mixedVector B (Sum.inr 5359) = Sparse.eval nodeValue5359 (mixedVector B) := by
    change mixedMoment B node5359 node5359Labels = _
    exact sound5359 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5437 : mixedVector B (Sum.inr 5437) = Sparse.eval nodeValue5437 (mixedVector B) := by
    change mixedMoment B node5437 node5437Labels = _
    exact sound5437 B hB hF
  have h5445 : mixedVector B (Sum.inr 5445) = Sparse.eval nodeValue5445 (mixedVector B) := by
    change mixedMoment B node5445 node5445Labels = _
    exact sound5445 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450_e B hB hF
  have h5469 : mixedVector B (Sum.inr 5469) = Sparse.eval nodeValue5469 (mixedVector B) := by
    change mixedMoment B node5469 node5469Labels = _
    exact sound5469 B hB hF
  have h5474 : mixedVector B (Sum.inr 5474) = Sparse.eval nodeValue5474 (mixedVector B) := by
    change mixedMoment B node5474 node5474Labels = _
    exact sound5474 B hB hF
  have h5479 : mixedVector B (Sum.inr 5479) = Sparse.eval nodeValue5479 (mixedVector B) := by
    change mixedMoment B node5479 node5479Labels = _
    exact sound5479 B hB hF
  simpa only [sourceForm1108, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5085, h5097, h5277, h5281, h5301, h5359, h5433, h5437, h5445, h5450, h5469, h5474, h5479, reducedSource961] using sourceEq1108 B hB

theorem rowSound961 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row961 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck961, numericCheck961, reducedZero961 B hB hF, mul_zero]

theorem reducedZero969 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource969 (mixedVector B) = 0 := by
  have h5072 : mixedVector B (Sum.inr 5072) = Sparse.eval nodeValue5072 (mixedVector B) := by
    change mixedMoment B node5072 node5072Labels = _
    exact sound5072 B hB hF
  have h5073 : mixedVector B (Sum.inr 5073) = Sparse.eval nodeValue5073 (mixedVector B) := by
    change mixedMoment B node5073 node5073Labels = _
    exact sound5073 B hB hF
  have h5098 : mixedVector B (Sum.inr 5098) = Sparse.eval nodeValue5098 (mixedVector B) := by
    change mixedMoment B node5098 node5098Labels = _
    exact sound5098 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  have h5351 : mixedVector B (Sum.inr 5351) = Sparse.eval nodeValue5351 (mixedVector B) := by
    change mixedMoment B node5351 node5351Labels = _
    exact sound5351 B hB hF
  have h5352 : mixedVector B (Sum.inr 5352) = Sparse.eval nodeValue5352 (mixedVector B) := by
    change mixedMoment B node5352 node5352Labels = _
    exact sound5352 B hB hF
  have h5365 : mixedVector B (Sum.inr 5365) = Sparse.eval nodeValue5365 (mixedVector B) := by
    change mixedMoment B node5365 node5365Labels = _
    exact sound5365 B hB hF
  have h5416 : mixedVector B (Sum.inr 5416) = Sparse.eval nodeValue5416 (mixedVector B) := by
    change mixedMoment B node5416 node5416Labels = _
    exact sound5416_e B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5476 : mixedVector B (Sum.inr 5476) = Sparse.eval nodeValue5476 (mixedVector B) := by
    change mixedMoment B node5476 node5476Labels = _
    exact sound5476_e B hB hF
  have h5477 : mixedVector B (Sum.inr 5477) = Sparse.eval nodeValue5477 (mixedVector B) := by
    change mixedMoment B node5477 node5477Labels = _
    exact sound5477 B hB hF
  have h5478 : mixedVector B (Sum.inr 5478) = Sparse.eval nodeValue5478 (mixedVector B) := by
    change mixedMoment B node5478 node5478Labels = _
    exact sound5478 B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483_e B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485_e B hB hF
  have h5486 : mixedVector B (Sum.inr 5486) = Sparse.eval nodeValue5486 (mixedVector B) := by
    change mixedMoment B node5486 node5486Labels = _
    exact sound5486 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490_e B hB hF
  have h5493 : mixedVector B (Sum.inr 5493) = Sparse.eval nodeValue5493 (mixedVector B) := by
    change mixedMoment B node5493 node5493Labels = _
    exact sound5493 B hB hF
  have h5497 : mixedVector B (Sum.inr 5497) = Sparse.eval nodeValue5497 (mixedVector B) := by
    change mixedMoment B node5497 node5497Labels = _
    exact sound5497 B hB hF
  have h5499 : mixedVector B (Sum.inr 5499) = Sparse.eval nodeValue5499 (mixedVector B) := by
    change mixedMoment B node5499 node5499Labels = _
    exact sound5499 B hB hF
  have h5500 : mixedVector B (Sum.inr 5500) = Sparse.eval nodeValue5500 (mixedVector B) := by
    change mixedMoment B node5500 node5500Labels = _
    exact sound5500_e B hB hF
  simpa only [sourceForm1117, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5072, h5073, h5098, h5292, h5351, h5352, h5365, h5416, h5424, h5433, h5476, h5477, h5478, h5483, h5485, h5486, h5490, h5493, h5497, h5499, h5500, reducedSource969] using sourceEq1117 B hB

theorem rowSound969 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row969 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck969, numericCheck969, reducedZero969 B hB hF, mul_zero]

theorem sourceRowsAt960 : MixedData.sourceRows (960 : Fin 2425) =
    MixedData.row960 := by decide +kernel

theorem sourceRowsAt961 : MixedData.sourceRows (961 : Fin 2425) =
    MixedData.row961 := by decide +kernel

theorem sourceRowsAt962 : MixedData.sourceRows (962 : Fin 2425) =
    MixedData.row962 := by decide +kernel

theorem sourceRowsAt963 : MixedData.sourceRows (963 : Fin 2425) =
    MixedData.row963 := by decide +kernel

theorem sourceRowsAt964 : MixedData.sourceRows (964 : Fin 2425) =
    MixedData.row964 := by decide +kernel

theorem sourceRowsAt965 : MixedData.sourceRows (965 : Fin 2425) =
    MixedData.row965 := by decide +kernel

theorem sourceRowsAt966 : MixedData.sourceRows (966 : Fin 2425) =
    MixedData.row966 := by decide +kernel

theorem sourceRowsAt967 : MixedData.sourceRows (967 : Fin 2425) =
    MixedData.row967 := by decide +kernel

theorem sourceRowsAt968 : MixedData.sourceRows (968 : Fin 2425) =
    MixedData.row968 := by decide +kernel

theorem sourceRowsAt969 : MixedData.sourceRows (969 : Fin 2425) =
    MixedData.row969 := by decide +kernel

theorem sourceRowsAt970 : MixedData.sourceRows (970 : Fin 2425) =
    MixedData.row970 := by decide +kernel

theorem sourceRowsAt971 : MixedData.sourceRows (971 : Fin 2425) =
    MixedData.row971 := by decide +kernel

theorem sourceRowsAt972 : MixedData.sourceRows (972 : Fin 2425) =
    MixedData.row972 := by decide +kernel

theorem sourceRowsAt973 : MixedData.sourceRows (973 : Fin 2425) =
    MixedData.row973 := by decide +kernel

theorem sourceRowsAt974 : MixedData.sourceRows (974 : Fin 2425) =
    MixedData.row974 := by decide +kernel

theorem sourceRowsAt975 : MixedData.sourceRows (975 : Fin 2425) =
    MixedData.row975 := by decide +kernel

theorem chunkSound60_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 60) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 960 ∨ k.val = 961 ∨ k.val = 962 ∨ k.val = 963 ∨ k.val = 964 ∨ k.val = 965 ∨ k.val = 966 ∨ k.val = 967 ∨ k.val = 968 ∨ k.val = 969 ∨ k.val = 970 ∨ k.val = 971 ∨ k.val = 972 ∨ k.val = 973 ∨ k.val = 974 ∨ k.val = 975 := by omega
  rcases heq with h960 | h961 | h962 | h963 | h964 | h965 | h966 | h967 | h968 | h969 | h970 | h971 | h972 | h973 | h974 | h975
  · have he : k = (960 : Fin 2425) := Fin.ext h960
    subst k
    rw [sourceRowsAt960]
    exact rowSound960 B hB hF
  · have he : k = (961 : Fin 2425) := Fin.ext h961
    subst k
    rw [sourceRowsAt961]
    exact rowSound961 B hB hF
  · have he : k = (962 : Fin 2425) := Fin.ext h962
    subst k
    rw [sourceRowsAt962]
    exact rowSound962_e B hB hF
  · have he : k = (963 : Fin 2425) := Fin.ext h963
    subst k
    rw [sourceRowsAt963]
    exact rowSound963_e B hB hF
  · have he : k = (964 : Fin 2425) := Fin.ext h964
    subst k
    rw [sourceRowsAt964]
    exact rowSound964_e B hB hF
  · have he : k = (965 : Fin 2425) := Fin.ext h965
    subst k
    rw [sourceRowsAt965]
    exact rowSound965_e B hB hF
  · have he : k = (966 : Fin 2425) := Fin.ext h966
    subst k
    rw [sourceRowsAt966]
    exact rowSound966_e B hB hF
  · have he : k = (967 : Fin 2425) := Fin.ext h967
    subst k
    rw [sourceRowsAt967]
    exact rowSound967_e B hB hF
  · have he : k = (968 : Fin 2425) := Fin.ext h968
    subst k
    rw [sourceRowsAt968]
    exact rowSound968_e B hB hF
  · have he : k = (969 : Fin 2425) := Fin.ext h969
    subst k
    rw [sourceRowsAt969]
    exact rowSound969 B hB hF
  · have he : k = (970 : Fin 2425) := Fin.ext h970
    subst k
    rw [sourceRowsAt970]
    exact rowSound970_e B hB hF
  · have he : k = (971 : Fin 2425) := Fin.ext h971
    subst k
    rw [sourceRowsAt971]
    exact rowSound971_e B hB hF
  · have he : k = (972 : Fin 2425) := Fin.ext h972
    subst k
    rw [sourceRowsAt972]
    exact rowSound972_e B hB hF
  · have he : k = (973 : Fin 2425) := Fin.ext h973
    subst k
    rw [sourceRowsAt973]
    exact rowSound973_e B hB hF
  · have he : k = (974 : Fin 2425) := Fin.ext h974
    subst k
    rw [sourceRowsAt974]
    exact rowSound974_e B hB hF
  · have he : k = (975 : Fin 2425) := Fin.ext h975
    subst k
    rw [sourceRowsAt975]
    exact rowSound975_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e_oai
