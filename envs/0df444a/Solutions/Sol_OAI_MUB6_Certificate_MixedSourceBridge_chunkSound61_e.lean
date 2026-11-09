-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:26:41.506817+00:00
-- url     : https://prove2.me/submissions/a5661c56-f0ee-4be4-823b-6636dd6c134b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E129
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E150
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3851_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3994_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3998_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5167_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5169_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5172_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5386_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5387_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5388_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5416_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5417_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5433_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5435_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5450_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5482_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5490_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound976_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound977_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound978_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound980_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound981_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound982_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound983_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound984_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound986_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound987_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound988_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound990_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound991_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13734 raw13734Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw13734 raw13734Labels = mixedMoment B raw13734step0 raw13734step0Labels := by
      have ha : raw13734step0 = (fun i j => raw13734 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13734step0 raw13734; decide +kernel
      have hl : raw13734step0Labels = raw13734Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13734 raw13734Labels permutation194 permutation7
    mixedMoment B raw13734step0 raw13734step0Labels = mixedMoment B raw13734step1 raw13734step1Labels := by
      have ha : raw13734step1 = -raw13734step0 := by apply Matrix.ext; change ∀ i j, raw13734step1 i j = -(raw13734step0 i j); unfold raw13734step1 raw13734step0; decide +kernel
      have hl : raw13734step1Labels = raw13734step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13734step1 raw13734step1Labels = mixedMoment B raw13734step2 raw13734step2Labels := by
      have ha : raw13734step2 = raw13734step1 := by apply Matrix.ext; unfold raw13734step2 raw13734step1; decide +kernel
      have hl : raw13734step1Labels = labelEmbedding1 ∘ raw13734step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13734step1 raw13734step1Labels raw13734step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3806 node3806Labels := by rfl

theorem canonical13735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13735 raw13735Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw13735 raw13735Labels = mixedMoment B raw13735step0 raw13735step0Labels := by
      have ha : raw13735step0 = (fun i j => raw13735 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13735step0 raw13735; decide +kernel
      have hl : raw13735step0Labels = raw13735Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13735 raw13735Labels permutation194 permutation7
    mixedMoment B raw13735step0 raw13735step0Labels = mixedMoment B raw13735step1 raw13735step1Labels := by
      have ha : raw13735step1 = -raw13735step0 := by apply Matrix.ext; change ∀ i j, raw13735step1 i j = -(raw13735step0 i j); unfold raw13735step1 raw13735step0; decide +kernel
      have hl : raw13735step1Labels = raw13735step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13735step1 raw13735step1Labels = mixedMoment B raw13735step2 raw13735step2Labels := by
      have ha : raw13735step2 = raw13735step1 := by apply Matrix.ext; unfold raw13735step2 raw13735step1; decide +kernel
      have hl : raw13735step1Labels = labelEmbedding1 ∘ raw13735step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13735step1 raw13735step1Labels raw13735step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3851 node3851Labels := by rfl

theorem canonical13736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13736 raw13736Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw13736 raw13736Labels = mixedMoment B raw13736step0 raw13736step0Labels := by
      have ha : raw13736step0 = (fun i j => raw13736 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13736step0 raw13736; decide +kernel
      have hl : raw13736step0Labels = raw13736Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13736 raw13736Labels permutation195 permutation7
    mixedMoment B raw13736step0 raw13736step0Labels = mixedMoment B raw13736step1 raw13736step1Labels := by
      have ha : raw13736step1 = -raw13736step0 := by apply Matrix.ext; change ∀ i j, raw13736step1 i j = -(raw13736step0 i j); unfold raw13736step1 raw13736step0; decide +kernel
      have hl : raw13736step1Labels = raw13736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13736step1 raw13736step1Labels = mixedMoment B raw13736step2 raw13736step2Labels := by
      have ha : raw13736step2 = raw13736step1 := by apply Matrix.ext; unfold raw13736step2 raw13736step1; decide +kernel
      have hl : raw13736step1Labels = labelEmbedding1 ∘ raw13736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13736step1 raw13736step1Labels raw13736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3851 node3851Labels := by rfl

theorem canonical13737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13737 raw13737Labels = mixedMoment B node3859 node3859Labels := by
  calc
    mixedMoment B raw13737 raw13737Labels = mixedMoment B raw13737step0 raw13737step0Labels := by
      have hz : ∀ j, raw13737 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13737step0 = (fun i j => raw13737 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13737step0 raw13737; decide +kernel
      have hl : raw13737step0Labels = raw13737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13737 raw13737Labels permutation590 hz
    mixedMoment B raw13737step0 raw13737step0Labels = mixedMoment B raw13737step1 raw13737step1Labels := by
      have ha : raw13737step1 = (fun i j => raw13737step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13737step1 raw13737step0; decide +kernel
      have hl : raw13737step1Labels = raw13737step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13737step0 raw13737step0Labels permutation38 permutation7
    mixedMoment B raw13737step1 raw13737step1Labels = mixedMoment B raw13737step2 raw13737step2Labels := by
      have ha : raw13737step2 = -raw13737step1 := by apply Matrix.ext; change ∀ i j, raw13737step2 i j = -(raw13737step1 i j); unfold raw13737step2 raw13737step1; decide +kernel
      have hl : raw13737step2Labels = raw13737step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13737step2 raw13737step2Labels = mixedMoment B raw13737step3 raw13737step3Labels := by
      have ha : raw13737step3 = raw13737step2 := by apply Matrix.ext; unfold raw13737step3 raw13737step2; decide +kernel
      have hl : raw13737step2Labels = labelEmbedding1 ∘ raw13737step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13737step2 raw13737step2Labels raw13737step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3859 node3859Labels := by rfl

theorem canonical13744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13744 raw13744Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw13744 raw13744Labels = mixedMoment B raw13744step0 raw13744step0Labels := by
      have ha : raw13744step0 = (fun i j => raw13744 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13744step0 raw13744; decide +kernel
      have hl : raw13744step0Labels = raw13744Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13744 raw13744Labels permutation194 permutation7
    mixedMoment B raw13744step0 raw13744step0Labels = mixedMoment B raw13744step1 raw13744step1Labels := by
      have ha : raw13744step1 = -raw13744step0 := by apply Matrix.ext; change ∀ i j, raw13744step1 i j = -(raw13744step0 i j); unfold raw13744step1 raw13744step0; decide +kernel
      have hl : raw13744step1Labels = raw13744step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13744step1 raw13744step1Labels = mixedMoment B raw13744step2 raw13744step2Labels := by
      have ha : raw13744step2 = raw13744step1 := by apply Matrix.ext; unfold raw13744step2 raw13744step1; decide +kernel
      have hl : raw13744step1Labels = labelEmbedding1 ∘ raw13744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13744step1 raw13744step1Labels raw13744step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3569 node3569Labels := by rfl

theorem canonical13749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13749 raw13749Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw13749 raw13749Labels = mixedMoment B raw13749step0 raw13749step0Labels := by
      have ha : raw13749step0 = (fun i j => raw13749 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13749step0 raw13749; decide +kernel
      have hl : raw13749step0Labels = raw13749Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13749 raw13749Labels permutation195 permutation7
    mixedMoment B raw13749step0 raw13749step0Labels = mixedMoment B raw13749step1 raw13749step1Labels := by
      have ha : raw13749step1 = -raw13749step0 := by apply Matrix.ext; change ∀ i j, raw13749step1 i j = -(raw13749step0 i j); unfold raw13749step1 raw13749step0; decide +kernel
      have hl : raw13749step1Labels = raw13749step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13749step1 raw13749step1Labels = mixedMoment B raw13749step2 raw13749step2Labels := by
      have ha : raw13749step2 = raw13749step1 := by apply Matrix.ext; unfold raw13749step2 raw13749step1; decide +kernel
      have hl : raw13749step1Labels = labelEmbedding1 ∘ raw13749step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13749step1 raw13749step1Labels raw13749step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

theorem canonical13754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13754 raw13754Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw13754 raw13754Labels = mixedMoment B raw13754step0 raw13754step0Labels := by
      have ha : raw13754step0 = (fun i j => raw13754 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13754step0 raw13754; decide +kernel
      have hl : raw13754step0Labels = raw13754Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13754 raw13754Labels permutation194 permutation7
    mixedMoment B raw13754step0 raw13754step0Labels = mixedMoment B raw13754step1 raw13754step1Labels := by
      have ha : raw13754step1 = -raw13754step0 := by apply Matrix.ext; change ∀ i j, raw13754step1 i j = -(raw13754step0 i j); unfold raw13754step1 raw13754step0; decide +kernel
      have hl : raw13754step1Labels = raw13754step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13754step1 raw13754step1Labels = mixedMoment B raw13754step2 raw13754step2Labels := by
      have ha : raw13754step2 = raw13754step1 := by apply Matrix.ext; unfold raw13754step2 raw13754step1; decide +kernel
      have hl : raw13754step1Labels = labelEmbedding1 ∘ raw13754step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13754step1 raw13754step1Labels raw13754step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

theorem canonical13759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13759 raw13759Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw13759 raw13759Labels = mixedMoment B raw13759step0 raw13759step0Labels := by
      have ha : raw13759step0 = (fun i j => raw13759 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13759step0 raw13759; decide +kernel
      have hl : raw13759step0Labels = raw13759Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13759 raw13759Labels permutation194 permutation7
    mixedMoment B raw13759step0 raw13759step0Labels = mixedMoment B raw13759step1 raw13759step1Labels := by
      have ha : raw13759step1 = -raw13759step0 := by apply Matrix.ext; change ∀ i j, raw13759step1 i j = -(raw13759step0 i j); unfold raw13759step1 raw13759step0; decide +kernel
      have hl : raw13759step1Labels = raw13759step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13759step1 raw13759step1Labels = mixedMoment B raw13759step2 raw13759step2Labels := by
      have ha : raw13759step2 = raw13759step1 := by apply Matrix.ext; unfold raw13759step2 raw13759step1; decide +kernel
      have hl : raw13759step1Labels = labelEmbedding1 ∘ raw13759step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13759step1 raw13759step1Labels raw13759step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14054 raw14054Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw14054 raw14054Labels = mixedMoment B raw14054step0 raw14054step0Labels := by
      have hz : ∀ j, raw14054 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14054step0 = (fun i j => raw14054 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14054step0 raw14054; decide +kernel
      have hl : raw14054step0Labels = raw14054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14054 raw14054Labels permutation265 hz
    mixedMoment B raw14054step0 raw14054step0Labels = mixedMoment B raw14054step1 raw14054step1Labels := by
      have ha : raw14054step1 = (fun i j => raw14054step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14054step1 raw14054step0; decide +kernel
      have hl : raw14054step1Labels = raw14054step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14054step0 raw14054step0Labels permutation36 permutation2
    _ = mixedMoment B node5440 node5440Labels := by rfl

theorem canonical14055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14055 raw14055Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw14055 raw14055Labels = mixedMoment B raw14055step0 raw14055step0Labels := by
      have hz : ∀ j, raw14055 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14055step0 = (fun i j => raw14055 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14055step0 raw14055; decide +kernel
      have hl : raw14055step0Labels = raw14055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14055 raw14055Labels permutation590 hz
    mixedMoment B raw14055step0 raw14055step0Labels = mixedMoment B raw14055step1 raw14055step1Labels := by
      have hz : ∀ j, raw14055step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14055step1 = (fun i j => raw14055step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14055step1 raw14055step0; decide +kernel
      have hl : raw14055step1Labels = raw14055step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14055step0 raw14055step0Labels permutation80 hz
    mixedMoment B raw14055step1 raw14055step1Labels = mixedMoment B raw14055step2 raw14055step2Labels := by
      have hz : ∀ j, raw14055step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw14055step2 = (fun i j => raw14055step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw14055step2 raw14055step1; decide +kernel
      have hl : raw14055step2Labels = raw14055step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14055step1 raw14055step1Labels permutation14 hz
    mixedMoment B raw14055step2 raw14055step2Labels = mixedMoment B raw14055step3 raw14055step3Labels := by
      have hz : ∀ i, raw14055step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw14055step3 = (fun i j => raw14055step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw14055step3 raw14055step2; decide +kernel
      have hl : raw14055step3Labels = (fun j => raw14055step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14055step2 raw14055step2Labels permutation4 hz
    mixedMoment B raw14055step3 raw14055step3Labels = mixedMoment B raw14055step4 raw14055step4Labels := by
      have ha : raw14055step4 = raw14055step3 := by apply Matrix.ext; unfold raw14055step4 raw14055step3; decide +kernel
      have hl : raw14055step3Labels = labelEmbedding2 ∘ raw14055step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14055step3 raw14055step3Labels raw14055step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical14061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14061 raw14061Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw14061 raw14061Labels = mixedMoment B raw14061step0 raw14061step0Labels := by
      have ha : raw14061step0 = (fun i j => raw14061 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14061step0 raw14061; decide +kernel
      have hl : raw14061step0Labels = raw14061Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14061 raw14061Labels permutation156 permutation2
    _ = mixedMoment B node5167 node5167Labels := by rfl

theorem canonical14065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14065 raw14065Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw14065 raw14065Labels = mixedMoment B raw14065step0 raw14065step0Labels := by
      have hz : ∀ j, raw14065 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14065step0 = (fun i j => raw14065 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14065step0 raw14065; decide +kernel
      have hl : raw14065step0Labels = raw14065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14065 raw14065Labels permutation346 hz
    mixedMoment B raw14065step0 raw14065step0Labels = mixedMoment B raw14065step1 raw14065step1Labels := by
      have ha : raw14065step1 = (fun i j => raw14065step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14065step1 raw14065step0; decide +kernel
      have hl : raw14065step1Labels = raw14065step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14065step0 raw14065step0Labels permutation37 permutation2
    _ = mixedMoment B node5169 node5169Labels := by rfl

theorem canonical14070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14070 raw14070Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw14070 raw14070Labels = mixedMoment B raw14070step0 raw14070step0Labels := by
      have hz : ∀ j, raw14070 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14070step0 = (fun i j => raw14070 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14070step0 raw14070; decide +kernel
      have hl : raw14070step0Labels = raw14070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14070 raw14070Labels permutation346 hz
    mixedMoment B raw14070step0 raw14070step0Labels = mixedMoment B raw14070step1 raw14070step1Labels := by
      have ha : raw14070step1 = (fun i j => raw14070step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14070step1 raw14070step0; decide +kernel
      have hl : raw14070step1Labels = raw14070step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14070step0 raw14070step0Labels permutation36 permutation2
    _ = mixedMoment B node5169 node5169Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15170 raw15170Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw15170 raw15170Labels = mixedMoment B raw15170step0 raw15170step0Labels := by
      have hz : ∀ j, raw15170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15170step0 = (fun i j => raw15170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15170step0 raw15170; decide +kernel
      have hl : raw15170step0Labels = raw15170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15170 raw15170Labels permutation346 hz
    mixedMoment B raw15170step0 raw15170step0Labels = mixedMoment B raw15170step1 raw15170step1Labels := by
      have ha : raw15170step1 = (fun i j => raw15170step0 (permutation51 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15170step1 raw15170step0; decide +kernel
      have hl : raw15170step1Labels = raw15170step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15170step0 raw15170step0Labels permutation51 permutation6
    mixedMoment B raw15170step1 raw15170step1Labels = mixedMoment B raw15170step2 raw15170step2Labels := by
      have ha : raw15170step2 = -raw15170step1 := by apply Matrix.ext; change ∀ i j, raw15170step2 i j = -(raw15170step1 i j); unfold raw15170step2 raw15170step1; decide +kernel
      have hl : raw15170step2Labels = raw15170step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15170step2 raw15170step2Labels = mixedMoment B raw15170step3 raw15170step3Labels := by
      have ha : raw15170step3 = raw15170step2 := by apply Matrix.ext; unfold raw15170step3 raw15170step2; decide +kernel
      have hl : raw15170step2Labels = labelEmbedding9 ∘ raw15170step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15170step2 raw15170step2Labels raw15170step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical15173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15173 raw15173Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw15173 raw15173Labels = mixedMoment B raw15173step0 raw15173step0Labels := by
      have ha : raw15173step0 = (fun i j => raw15173 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15173step0 raw15173; decide +kernel
      have hl : raw15173step0Labels = raw15173Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15173 raw15173Labels permutation159 permutation2
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical15174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15174 raw15174Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw15174 raw15174Labels = mixedMoment B raw15174step0 raw15174step0Labels := by
      have hz : ∀ j, raw15174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15174step0 = (fun i j => raw15174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15174step0 raw15174; decide +kernel
      have hl : raw15174step0Labels = raw15174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15174 raw15174Labels permutation346 hz
    mixedMoment B raw15174step0 raw15174step0Labels = mixedMoment B raw15174step1 raw15174step1Labels := by
      have ha : raw15174step1 = (fun i j => raw15174step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15174step1 raw15174step0; decide +kernel
      have hl : raw15174step1Labels = raw15174step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15174step0 raw15174step0Labels permutation56 permutation3
    mixedMoment B raw15174step1 raw15174step1Labels = mixedMoment B raw15174step2 raw15174step2Labels := by
      have ha : raw15174step2 = raw15174step1 := by apply Matrix.ext; unfold raw15174step2 raw15174step1; decide +kernel
      have hl : raw15174step1Labels = labelEmbedding6 ∘ raw15174step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15174step1 raw15174step1Labels raw15174step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5387 node5387Labels := by rfl

theorem canonical15175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15175 raw15175Labels = mixedMoment B node5417 node5417Labels := by
  calc
    _ = mixedMoment B node5417 node5417Labels := by rfl

theorem canonical15179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15179 raw15179Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw15179 raw15179Labels = mixedMoment B raw15179step0 raw15179step0Labels := by
      have hz : ∀ j, raw15179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15179step0 = (fun i j => raw15179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15179step0 raw15179; decide +kernel
      have hl : raw15179step0Labels = raw15179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15179 raw15179Labels permutation346 hz
    mixedMoment B raw15179step0 raw15179step0Labels = mixedMoment B raw15179step1 raw15179step1Labels := by
      have ha : raw15179step1 = (fun i j => raw15179step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15179step1 raw15179step0; decide +kernel
      have hl : raw15179step1Labels = raw15179step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15179step0 raw15179step0Labels permutation33 permutation2
    _ = mixedMoment B node5434 node5434Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical147
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18890 raw18890Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw18890 raw18890Labels = mixedMoment B raw18890step0 raw18890step0Labels := by
      have hz : ∀ j, raw18890 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18890step0 = (fun i j => raw18890 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18890step0 raw18890; decide +kernel
      have hl : raw18890step0Labels = raw18890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18890 raw18890Labels permutation346 hz
    mixedMoment B raw18890step0 raw18890step0Labels = mixedMoment B raw18890step1 raw18890step1Labels := by
      have ha : raw18890step1 = (fun i j => raw18890step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18890step1 raw18890step0; decide +kernel
      have hl : raw18890step1Labels = raw18890step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18890step0 raw18890step0Labels permutation36 permutation6
    mixedMoment B raw18890step1 raw18890step1Labels = mixedMoment B raw18890step2 raw18890step2Labels := by
      have ha : raw18890step2 = raw18890step1 := by apply Matrix.ext; unfold raw18890step2 raw18890step1; decide +kernel
      have hl : raw18890step1Labels = labelEmbedding9 ∘ raw18890step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18890step1 raw18890step1Labels raw18890step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5486 node5486Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical148
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19051 raw19051Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw19051 raw19051Labels = mixedMoment B raw19051step0 raw19051step0Labels := by
      have ha : raw19051step0 = (fun i j => raw19051 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19051step0 raw19051; decide +kernel
      have hl : raw19051step0Labels = raw19051Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19051 raw19051Labels permutation152 permutation7
    mixedMoment B raw19051step0 raw19051step0Labels = mixedMoment B raw19051step1 raw19051step1Labels := by
      have ha : raw19051step1 = raw19051step0 := by apply Matrix.ext; unfold raw19051step1 raw19051step0; decide +kernel
      have hl : raw19051step0Labels = labelEmbedding10 ∘ raw19051step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19051step0 raw19051step0Labels raw19051step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical19052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19052 raw19052Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw19052 raw19052Labels = mixedMoment B raw19052step0 raw19052step0Labels := by
      have ha : raw19052step0 = (fun i j => raw19052 (permutation367 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19052step0 raw19052; decide +kernel
      have hl : raw19052step0Labels = raw19052Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19052 raw19052Labels permutation367 permutation5
    mixedMoment B raw19052step0 raw19052step0Labels = mixedMoment B raw19052step1 raw19052step1Labels := by
      have ha : raw19052step1 = -raw19052step0 := by apply Matrix.ext; change ∀ i j, raw19052step1 i j = -(raw19052step0 i j); unfold raw19052step1 raw19052step0; decide +kernel
      have hl : raw19052step1Labels = raw19052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19052step1 raw19052step1Labels = mixedMoment B raw19052step2 raw19052step2Labels := by
      have ha : raw19052step2 = raw19052step1 := by apply Matrix.ext; unfold raw19052step2 raw19052step1; decide +kernel
      have hl : raw19052step1Labels = labelEmbedding8 ∘ raw19052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19052step1 raw19052step1Labels raw19052step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5437 node5437Labels := by rfl

theorem canonical19053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19053 raw19053Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw19053 raw19053Labels = mixedMoment B raw19053step0 raw19053step0Labels := by
      have ha : raw19053step0 = (fun i j => raw19053 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19053step0 raw19053; decide +kernel
      have hl : raw19053step0Labels = raw19053Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19053 raw19053Labels permutation155 permutation7
    mixedMoment B raw19053step0 raw19053step0Labels = mixedMoment B raw19053step1 raw19053step1Labels := by
      have ha : raw19053step1 = raw19053step0 := by apply Matrix.ext; unfold raw19053step1 raw19053step0; decide +kernel
      have hl : raw19053step0Labels = labelEmbedding10 ∘ raw19053step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19053step0 raw19053step0Labels raw19053step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical19054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19054 raw19054Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw19054 raw19054Labels = mixedMoment B raw19054step0 raw19054step0Labels := by
      have ha : raw19054step0 = (fun i j => raw19054 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19054step0 raw19054; decide +kernel
      have hl : raw19054step0Labels = raw19054Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19054 raw19054Labels permutation153 permutation7
    mixedMoment B raw19054step0 raw19054step0Labels = mixedMoment B raw19054step1 raw19054step1Labels := by
      have ha : raw19054step1 = raw19054step0 := by apply Matrix.ext; unfold raw19054step1 raw19054step0; decide +kernel
      have hl : raw19054step0Labels = labelEmbedding10 ∘ raw19054step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19054step0 raw19054step0Labels raw19054step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical19055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19055 raw19055Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw19055 raw19055Labels = mixedMoment B raw19055step0 raw19055step0Labels := by
      have ha : raw19055step0 = (fun i j => raw19055 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19055step0 raw19055; decide +kernel
      have hl : raw19055step0Labels = raw19055Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19055 raw19055Labels permutation152 permutation7
    mixedMoment B raw19055step0 raw19055step0Labels = mixedMoment B raw19055step1 raw19055step1Labels := by
      have ha : raw19055step1 = raw19055step0 := by apply Matrix.ext; unfold raw19055step1 raw19055step0; decide +kernel
      have hl : raw19055step0Labels = labelEmbedding10 ∘ raw19055step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19055step0 raw19055step0Labels raw19055step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical19056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19056 raw19056Labels = mixedMoment B node5427 node5427Labels := by
  calc
    mixedMoment B raw19056 raw19056Labels = mixedMoment B raw19056step0 raw19056step0Labels := by
      have ha : raw19056step0 = (fun i j => raw19056 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19056step0 raw19056; decide +kernel
      have hl : raw19056step0Labels = raw19056Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19056 raw19056Labels permutation176 permutation4
    mixedMoment B raw19056step0 raw19056step0Labels = mixedMoment B raw19056step1 raw19056step1Labels := by
      have ha : raw19056step1 = -raw19056step0 := by apply Matrix.ext; change ∀ i j, raw19056step1 i j = -(raw19056step0 i j); unfold raw19056step1 raw19056step0; decide +kernel
      have hl : raw19056step1Labels = raw19056step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19056step1 raw19056step1Labels = mixedMoment B raw19056step2 raw19056step2Labels := by
      have ha : raw19056step2 = raw19056step1 := by apply Matrix.ext; unfold raw19056step2 raw19056step1; decide +kernel
      have hl : raw19056step1Labels = labelEmbedding7 ∘ raw19056step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19056step1 raw19056step1Labels raw19056step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5427 node5427Labels := by rfl

theorem canonical19057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19057 raw19057Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw19057 raw19057Labels = mixedMoment B raw19057step0 raw19057step0Labels := by
      have ha : raw19057step0 = (fun i j => raw19057 (permutation346 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19057step0 raw19057; decide +kernel
      have hl : raw19057step0Labels = raw19057Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19057 raw19057Labels permutation346 permutation5
    mixedMoment B raw19057step0 raw19057step0Labels = mixedMoment B raw19057step1 raw19057step1Labels := by
      have ha : raw19057step1 = -raw19057step0 := by apply Matrix.ext; change ∀ i j, raw19057step1 i j = -(raw19057step0 i j); unfold raw19057step1 raw19057step0; decide +kernel
      have hl : raw19057step1Labels = raw19057step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19057step1 raw19057step1Labels = mixedMoment B raw19057step2 raw19057step2Labels := by
      have ha : raw19057step2 = raw19057step1 := by apply Matrix.ext; unfold raw19057step2 raw19057step1; decide +kernel
      have hl : raw19057step1Labels = labelEmbedding8 ∘ raw19057step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19057step1 raw19057step1Labels raw19057step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical19058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19058 raw19058Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19058 raw19058Labels = mixedMoment B raw19058step0 raw19058step0Labels := by
      have ha : raw19058step0 = (fun i j => raw19058 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19058step0 raw19058; decide +kernel
      have hl : raw19058step0Labels = raw19058Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19058 raw19058Labels permutation155 permutation7
    mixedMoment B raw19058step0 raw19058step0Labels = mixedMoment B raw19058step1 raw19058step1Labels := by
      have ha : raw19058step1 = raw19058step0 := by apply Matrix.ext; unfold raw19058step1 raw19058step0; decide +kernel
      have hl : raw19058step0Labels = labelEmbedding10 ∘ raw19058step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19058step0 raw19058step0Labels raw19058step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical19059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19059 raw19059Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19059 raw19059Labels = mixedMoment B raw19059step0 raw19059step0Labels := by
      have ha : raw19059step0 = (fun i j => raw19059 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19059step0 raw19059; decide +kernel
      have hl : raw19059step0Labels = raw19059Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19059 raw19059Labels permutation153 permutation7
    mixedMoment B raw19059step0 raw19059step0Labels = mixedMoment B raw19059step1 raw19059step1Labels := by
      have ha : raw19059step1 = raw19059step0 := by apply Matrix.ext; unfold raw19059step1 raw19059step0; decide +kernel
      have hl : raw19059step0Labels = labelEmbedding10 ∘ raw19059step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19059step0 raw19059step0Labels raw19059step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical19060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19060 raw19060Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19060 raw19060Labels = mixedMoment B raw19060step0 raw19060step0Labels := by
      have ha : raw19060step0 = (fun i j => raw19060 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19060step0 raw19060; decide +kernel
      have hl : raw19060step0Labels = raw19060Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19060 raw19060Labels permutation152 permutation7
    mixedMoment B raw19060step0 raw19060step0Labels = mixedMoment B raw19060step1 raw19060step1Labels := by
      have ha : raw19060step1 = raw19060step0 := by apply Matrix.ext; unfold raw19060step1 raw19060step0; decide +kernel
      have hl : raw19060step0Labels = labelEmbedding10 ∘ raw19060step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19060step0 raw19060step0Labels raw19060step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical19061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19061 raw19061Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19061 raw19061Labels = mixedMoment B raw19061step0 raw19061step0Labels := by
      have hz : ∀ j, raw19061 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19061step0 = (fun i j => raw19061 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19061step0 raw19061; decide +kernel
      have hl : raw19061step0Labels = raw19061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19061 raw19061Labels permutation346 hz
    mixedMoment B raw19061step0 raw19061step0Labels = mixedMoment B raw19061step1 raw19061step1Labels := by
      have hz : ∀ i, raw19061step0 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw19061step1 = (fun i j => raw19061step0 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw19061step1 raw19061step0; decide +kernel
      have hl : raw19061step1Labels = (fun j => raw19061step0Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19061step0 raw19061step0Labels permutation2 hz
    mixedMoment B raw19061step1 raw19061step1Labels = mixedMoment B raw19061step2 raw19061step2Labels := by
      have ha : raw19061step2 = -raw19061step1 := by apply Matrix.ext; change ∀ i j, raw19061step2 i j = -(raw19061step1 i j); unfold raw19061step2 raw19061step1; decide +kernel
      have hl : raw19061step2Labels = raw19061step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19061step2 raw19061step2Labels = mixedMoment B raw19061step3 raw19061step3Labels := by
      have ha : raw19061step3 = raw19061step2 := by apply Matrix.ext; unfold raw19061step3 raw19061step2; decide +kernel
      have hl : raw19061step2Labels = labelEmbedding3 ∘ raw19061step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19061step2 raw19061step2Labels raw19061step3Labels labelEmbedding3 hl
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical19062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19062 raw19062Labels = mixedMoment B node5474 node5474Labels := by
  calc
    mixedMoment B raw19062 raw19062Labels = mixedMoment B raw19062step0 raw19062step0Labels := by
      have hz : ∀ j, raw19062 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19062step0 = (fun i j => raw19062 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19062step0 raw19062; decide +kernel
      have hl : raw19062step0Labels = raw19062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19062 raw19062Labels permutation346 hz
    mixedMoment B raw19062step0 raw19062step0Labels = mixedMoment B raw19062step1 raw19062step1Labels := by
      have ha : raw19062step1 = (fun i j => raw19062step0 (permutation56 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19062step1 raw19062step0; decide +kernel
      have hl : raw19062step1Labels = raw19062step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19062step0 raw19062step0Labels permutation56 permutation4
    mixedMoment B raw19062step1 raw19062step1Labels = mixedMoment B raw19062step2 raw19062step2Labels := by
      have ha : raw19062step2 = -raw19062step1 := by apply Matrix.ext; change ∀ i j, raw19062step2 i j = -(raw19062step1 i j); unfold raw19062step2 raw19062step1; decide +kernel
      have hl : raw19062step2Labels = raw19062step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19062step2 raw19062step2Labels = mixedMoment B raw19062step3 raw19062step3Labels := by
      have ha : raw19062step3 = raw19062step2 := by apply Matrix.ext; unfold raw19062step3 raw19062step2; decide +kernel
      have hl : raw19062step2Labels = labelEmbedding7 ∘ raw19062step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19062step2 raw19062step2Labels raw19062step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5474 node5474Labels := by rfl

theorem canonical19063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19063 raw19063Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw19063 raw19063Labels = mixedMoment B raw19063step0 raw19063step0Labels := by
      have hz : ∀ j, raw19063 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19063step0 = (fun i j => raw19063 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19063step0 raw19063; decide +kernel
      have hl : raw19063step0Labels = raw19063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19063 raw19063Labels permutation346 hz
    mixedMoment B raw19063step0 raw19063step0Labels = mixedMoment B raw19063step1 raw19063step1Labels := by
      have ha : raw19063step1 = (fun i j => raw19063step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19063step1 raw19063step0; decide +kernel
      have hl : raw19063step1Labels = raw19063step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19063step0 raw19063step0Labels permutation32 permutation6
    mixedMoment B raw19063step1 raw19063step1Labels = mixedMoment B raw19063step2 raw19063step2Labels := by
      have ha : raw19063step2 = raw19063step1 := by apply Matrix.ext; unfold raw19063step2 raw19063step1; decide +kernel
      have hl : raw19063step1Labels = labelEmbedding9 ∘ raw19063step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19063step1 raw19063step1Labels raw19063step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5486 node5486Labels := by rfl

theorem canonical19064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19064 raw19064Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw19064 raw19064Labels = mixedMoment B raw19064step0 raw19064step0Labels := by
      have hz : ∀ j, raw19064 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19064step0 = (fun i j => raw19064 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19064step0 raw19064; decide +kernel
      have hl : raw19064step0Labels = raw19064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19064 raw19064Labels permutation346 hz
    mixedMoment B raw19064step0 raw19064step0Labels = mixedMoment B raw19064step1 raw19064step1Labels := by
      have ha : raw19064step1 = (fun i j => raw19064step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19064step1 raw19064step0; decide +kernel
      have hl : raw19064step1Labels = raw19064step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19064step0 raw19064step0Labels permutation34 permutation6
    mixedMoment B raw19064step1 raw19064step1Labels = mixedMoment B raw19064step2 raw19064step2Labels := by
      have ha : raw19064step2 = raw19064step1 := by apply Matrix.ext; unfold raw19064step2 raw19064step1; decide +kernel
      have hl : raw19064step1Labels = labelEmbedding9 ∘ raw19064step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19064step1 raw19064step1Labels raw19064step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5486 node5486Labels := by rfl

theorem canonical19065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19065 raw19065Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw19065 raw19065Labels = mixedMoment B raw19065step0 raw19065step0Labels := by
      have ha : raw19065step0 = (fun i j => raw19065 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19065step0 raw19065; decide +kernel
      have hl : raw19065step0Labels = raw19065Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19065 raw19065Labels permutation155 permutation4
    mixedMoment B raw19065step0 raw19065step0Labels = mixedMoment B raw19065step1 raw19065step1Labels := by
      have ha : raw19065step1 = -raw19065step0 := by apply Matrix.ext; change ∀ i j, raw19065step1 i j = -(raw19065step0 i j); unfold raw19065step1 raw19065step0; decide +kernel
      have hl : raw19065step1Labels = raw19065step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19065step1 raw19065step1Labels = mixedMoment B raw19065step2 raw19065step2Labels := by
      have ha : raw19065step2 = raw19065step1 := by apply Matrix.ext; unfold raw19065step2 raw19065step1; decide +kernel
      have hl : raw19065step1Labels = labelEmbedding7 ∘ raw19065step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19065step1 raw19065step1Labels raw19065step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5396 node5396Labels := by rfl

theorem canonical19066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19066 raw19066Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw19066 raw19066Labels = mixedMoment B raw19066step0 raw19066step0Labels := by
      have ha : raw19066step0 = (fun i j => raw19066 (permutation268 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19066step0 raw19066; decide +kernel
      have hl : raw19066step0Labels = raw19066Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19066 raw19066Labels permutation268 permutation4
    mixedMoment B raw19066step0 raw19066step0Labels = mixedMoment B raw19066step1 raw19066step1Labels := by
      have ha : raw19066step1 = -raw19066step0 := by apply Matrix.ext; change ∀ i j, raw19066step1 i j = -(raw19066step0 i j); unfold raw19066step1 raw19066step0; decide +kernel
      have hl : raw19066step1Labels = raw19066step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19066step1 raw19066step1Labels = mixedMoment B raw19066step2 raw19066step2Labels := by
      have ha : raw19066step2 = raw19066step1 := by apply Matrix.ext; unfold raw19066step2 raw19066step1; decide +kernel
      have hl : raw19066step1Labels = labelEmbedding7 ∘ raw19066step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19066step1 raw19066step1Labels raw19066step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

theorem canonical19067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19067 raw19067Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw19067 raw19067Labels = mixedMoment B raw19067step0 raw19067step0Labels := by
      have ha : raw19067step0 = (fun i j => raw19067 (permutation369 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19067step0 raw19067; decide +kernel
      have hl : raw19067step0Labels = raw19067Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19067 raw19067Labels permutation369 permutation5
    mixedMoment B raw19067step0 raw19067step0Labels = mixedMoment B raw19067step1 raw19067step1Labels := by
      have ha : raw19067step1 = -raw19067step0 := by apply Matrix.ext; change ∀ i j, raw19067step1 i j = -(raw19067step0 i j); unfold raw19067step1 raw19067step0; decide +kernel
      have hl : raw19067step1Labels = raw19067step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19067step1 raw19067step1Labels = mixedMoment B raw19067step2 raw19067step2Labels := by
      have ha : raw19067step2 = raw19067step1 := by apply Matrix.ext; unfold raw19067step2 raw19067step1; decide +kernel
      have hl : raw19067step1Labels = labelEmbedding8 ∘ raw19067step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19067step1 raw19067step1Labels raw19067step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical19068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19068 raw19068Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw19068 raw19068Labels = mixedMoment B raw19068step0 raw19068step0Labels := by
      have ha : raw19068step0 = (fun i j => raw19068 (permutation519 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19068step0 raw19068; decide +kernel
      have hl : raw19068step0Labels = raw19068Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19068 raw19068Labels permutation519 permutation4
    mixedMoment B raw19068step0 raw19068step0Labels = mixedMoment B raw19068step1 raw19068step1Labels := by
      have ha : raw19068step1 = raw19068step0 := by apply Matrix.ext; unfold raw19068step1 raw19068step0; decide +kernel
      have hl : raw19068step0Labels = labelEmbedding7 ∘ raw19068step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19068step0 raw19068step0Labels raw19068step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical19069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19069 raw19069Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw19069 raw19069Labels = mixedMoment B raw19069step0 raw19069step0Labels := by
      have ha : raw19069step0 = (fun i j => raw19069 (permutation504 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19069step0 raw19069; decide +kernel
      have hl : raw19069step0Labels = raw19069Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19069 raw19069Labels permutation504 permutation4
    mixedMoment B raw19069step0 raw19069step0Labels = mixedMoment B raw19069step1 raw19069step1Labels := by
      have ha : raw19069step1 = raw19069step0 := by apply Matrix.ext; unfold raw19069step1 raw19069step0; decide +kernel
      have hl : raw19069step0Labels = labelEmbedding7 ∘ raw19069step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19069step0 raw19069step0Labels raw19069step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical19070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19070 raw19070Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw19070 raw19070Labels = mixedMoment B raw19070step0 raw19070step0Labels := by
      have ha : raw19070step0 = (fun i j => raw19070 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19070step0 raw19070; decide +kernel
      have hl : raw19070step0Labels = raw19070Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19070 raw19070Labels permutation153 permutation4
    mixedMoment B raw19070step0 raw19070step0Labels = mixedMoment B raw19070step1 raw19070step1Labels := by
      have ha : raw19070step1 = -raw19070step0 := by apply Matrix.ext; change ∀ i j, raw19070step1 i j = -(raw19070step0 i j); unfold raw19070step1 raw19070step0; decide +kernel
      have hl : raw19070step1Labels = raw19070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19070step1 raw19070step1Labels = mixedMoment B raw19070step2 raw19070step2Labels := by
      have ha : raw19070step2 = raw19070step1 := by apply Matrix.ext; unfold raw19070step2 raw19070step1; decide +kernel
      have hl : raw19070step1Labels = labelEmbedding7 ∘ raw19070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19070step1 raw19070step1Labels raw19070step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5396 node5396Labels := by rfl

theorem canonical19071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19071 raw19071Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw19071 raw19071Labels = mixedMoment B raw19071step0 raw19071step0Labels := by
      have ha : raw19071step0 = (fun i j => raw19071 (permutation266 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19071step0 raw19071; decide +kernel
      have hl : raw19071step0Labels = raw19071Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19071 raw19071Labels permutation266 permutation4
    mixedMoment B raw19071step0 raw19071step0Labels = mixedMoment B raw19071step1 raw19071step1Labels := by
      have ha : raw19071step1 = -raw19071step0 := by apply Matrix.ext; change ∀ i j, raw19071step1 i j = -(raw19071step0 i j); unfold raw19071step1 raw19071step0; decide +kernel
      have hl : raw19071step1Labels = raw19071step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19071step1 raw19071step1Labels = mixedMoment B raw19071step2 raw19071step2Labels := by
      have ha : raw19071step2 = raw19071step1 := by apply Matrix.ext; unfold raw19071step2 raw19071step1; decide +kernel
      have hl : raw19071step1Labels = labelEmbedding7 ∘ raw19071step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19071step1 raw19071step1Labels raw19071step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical149
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19072 raw19072Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw19072 raw19072Labels = mixedMoment B raw19072step0 raw19072step0Labels := by
      have ha : raw19072step0 = (fun i j => raw19072 (permutation368 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19072step0 raw19072; decide +kernel
      have hl : raw19072step0Labels = raw19072Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19072 raw19072Labels permutation368 permutation5
    mixedMoment B raw19072step0 raw19072step0Labels = mixedMoment B raw19072step1 raw19072step1Labels := by
      have ha : raw19072step1 = -raw19072step0 := by apply Matrix.ext; change ∀ i j, raw19072step1 i j = -(raw19072step0 i j); unfold raw19072step1 raw19072step0; decide +kernel
      have hl : raw19072step1Labels = raw19072step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19072step1 raw19072step1Labels = mixedMoment B raw19072step2 raw19072step2Labels := by
      have ha : raw19072step2 = raw19072step1 := by apply Matrix.ext; unfold raw19072step2 raw19072step1; decide +kernel
      have hl : raw19072step1Labels = labelEmbedding8 ∘ raw19072step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19072step1 raw19072step1Labels raw19072step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical19073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19073 raw19073Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw19073 raw19073Labels = mixedMoment B raw19073step0 raw19073step0Labels := by
      have ha : raw19073step0 = (fun i j => raw19073 (permutation589 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19073step0 raw19073; decide +kernel
      have hl : raw19073step0Labels = raw19073Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19073 raw19073Labels permutation589 permutation4
    mixedMoment B raw19073step0 raw19073step0Labels = mixedMoment B raw19073step1 raw19073step1Labels := by
      have ha : raw19073step1 = raw19073step0 := by apply Matrix.ext; unfold raw19073step1 raw19073step0; decide +kernel
      have hl : raw19073step0Labels = labelEmbedding7 ∘ raw19073step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19073step0 raw19073step0Labels raw19073step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical19074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19074 raw19074Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw19074 raw19074Labels = mixedMoment B raw19074step0 raw19074step0Labels := by
      have ha : raw19074step0 = (fun i j => raw19074 (permutation568 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19074step0 raw19074; decide +kernel
      have hl : raw19074step0Labels = raw19074Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19074 raw19074Labels permutation568 permutation4
    mixedMoment B raw19074step0 raw19074step0Labels = mixedMoment B raw19074step1 raw19074step1Labels := by
      have ha : raw19074step1 = raw19074step0 := by apply Matrix.ext; unfold raw19074step1 raw19074step0; decide +kernel
      have hl : raw19074step0Labels = labelEmbedding7 ∘ raw19074step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19074step0 raw19074step0Labels raw19074step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical19075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19075 raw19075Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw19075 raw19075Labels = mixedMoment B raw19075step0 raw19075step0Labels := by
      have ha : raw19075step0 = (fun i j => raw19075 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19075step0 raw19075; decide +kernel
      have hl : raw19075step0Labels = raw19075Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19075 raw19075Labels permutation152 permutation4
    mixedMoment B raw19075step0 raw19075step0Labels = mixedMoment B raw19075step1 raw19075step1Labels := by
      have ha : raw19075step1 = -raw19075step0 := by apply Matrix.ext; change ∀ i j, raw19075step1 i j = -(raw19075step0 i j); unfold raw19075step1 raw19075step0; decide +kernel
      have hl : raw19075step1Labels = raw19075step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19075step1 raw19075step1Labels = mixedMoment B raw19075step2 raw19075step2Labels := by
      have ha : raw19075step2 = raw19075step1 := by apply Matrix.ext; unfold raw19075step2 raw19075step1; decide +kernel
      have hl : raw19075step1Labels = labelEmbedding7 ∘ raw19075step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19075step1 raw19075step1Labels raw19075step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5396 node5396Labels := by rfl

theorem canonical19076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19076 raw19076Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw19076 raw19076Labels = mixedMoment B raw19076step0 raw19076step0Labels := by
      have ha : raw19076step0 = (fun i j => raw19076 (permutation265 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19076step0 raw19076; decide +kernel
      have hl : raw19076step0Labels = raw19076Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19076 raw19076Labels permutation265 permutation4
    mixedMoment B raw19076step0 raw19076step0Labels = mixedMoment B raw19076step1 raw19076step1Labels := by
      have ha : raw19076step1 = -raw19076step0 := by apply Matrix.ext; change ∀ i j, raw19076step1 i j = -(raw19076step0 i j); unfold raw19076step1 raw19076step0; decide +kernel
      have hl : raw19076step1Labels = raw19076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19076step1 raw19076step1Labels = mixedMoment B raw19076step2 raw19076step2Labels := by
      have ha : raw19076step2 = raw19076step1 := by apply Matrix.ext; unfold raw19076step2 raw19076step1; decide +kernel
      have hl : raw19076step1Labels = labelEmbedding7 ∘ raw19076step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19076step1 raw19076step1Labels raw19076step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

theorem canonical19077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19077 raw19077Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw19077 raw19077Labels = mixedMoment B raw19077step0 raw19077step0Labels := by
      have ha : raw19077step0 = (fun i j => raw19077 (permutation367 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19077step0 raw19077; decide +kernel
      have hl : raw19077step0Labels = raw19077Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19077 raw19077Labels permutation367 permutation5
    mixedMoment B raw19077step0 raw19077step0Labels = mixedMoment B raw19077step1 raw19077step1Labels := by
      have ha : raw19077step1 = -raw19077step0 := by apply Matrix.ext; change ∀ i j, raw19077step1 i j = -(raw19077step0 i j); unfold raw19077step1 raw19077step0; decide +kernel
      have hl : raw19077step1Labels = raw19077step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19077step1 raw19077step1Labels = mixedMoment B raw19077step2 raw19077step2Labels := by
      have ha : raw19077step2 = raw19077step1 := by apply Matrix.ext; unfold raw19077step2 raw19077step1; decide +kernel
      have hl : raw19077step1Labels = labelEmbedding8 ∘ raw19077step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19077step1 raw19077step1Labels raw19077step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical19078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19078 raw19078Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw19078 raw19078Labels = mixedMoment B raw19078step0 raw19078step0Labels := by
      have ha : raw19078step0 = (fun i j => raw19078 (permutation688 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19078step0 raw19078; decide +kernel
      have hl : raw19078step0Labels = raw19078Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19078 raw19078Labels permutation688 permutation4
    mixedMoment B raw19078step0 raw19078step0Labels = mixedMoment B raw19078step1 raw19078step1Labels := by
      have ha : raw19078step1 = raw19078step0 := by apply Matrix.ext; unfold raw19078step1 raw19078step0; decide +kernel
      have hl : raw19078step0Labels = labelEmbedding7 ∘ raw19078step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19078step0 raw19078step0Labels raw19078step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical19079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19079 raw19079Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw19079 raw19079Labels = mixedMoment B raw19079step0 raw19079step0Labels := by
      have ha : raw19079step0 = (fun i j => raw19079 (permutation664 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19079step0 raw19079; decide +kernel
      have hl : raw19079step0Labels = raw19079Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19079 raw19079Labels permutation664 permutation4
    mixedMoment B raw19079step0 raw19079step0Labels = mixedMoment B raw19079step1 raw19079step1Labels := by
      have ha : raw19079step1 = raw19079step0 := by apply Matrix.ext; unfold raw19079step1 raw19079step0; decide +kernel
      have hl : raw19079step0Labels = labelEmbedding7 ∘ raw19079step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19079step0 raw19079step0Labels raw19079step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical150
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19218 raw19218Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw19218 raw19218Labels = mixedMoment B raw19218step0 raw19218step0Labels := by
      have ha : raw19218step0 = (fun i j => raw19218 (permutation313 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19218step0 raw19218; decide +kernel
      have hl : raw19218step0Labels = raw19218Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19218 raw19218Labels permutation313 permutation5
    mixedMoment B raw19218step0 raw19218step0Labels = mixedMoment B raw19218step1 raw19218step1Labels := by
      have ha : raw19218step1 = -raw19218step0 := by apply Matrix.ext; change ∀ i j, raw19218step1 i j = -(raw19218step0 i j); unfold raw19218step1 raw19218step0; decide +kernel
      have hl : raw19218step1Labels = raw19218step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19218step1 raw19218step1Labels = mixedMoment B raw19218step2 raw19218step2Labels := by
      have ha : raw19218step2 = raw19218step1 := by apply Matrix.ext; unfold raw19218step2 raw19218step1; decide +kernel
      have hl : raw19218step1Labels = labelEmbedding1 ∘ raw19218step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19218step1 raw19218step1Labels raw19218step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2750 node2750Labels := by rfl

theorem canonical19219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19219 raw19219Labels = mixedMoment B node3979 node3979Labels := by
  calc
    mixedMoment B raw19219 raw19219Labels = mixedMoment B raw19219step0 raw19219step0Labels := by
      have ha : raw19219step0 = (fun i j => raw19219 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19219step0 raw19219; decide +kernel
      have hl : raw19219step0Labels = raw19219Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19219 raw19219Labels permutation194 permutation7
    mixedMoment B raw19219step0 raw19219step0Labels = mixedMoment B raw19219step1 raw19219step1Labels := by
      have ha : raw19219step1 = -raw19219step0 := by apply Matrix.ext; change ∀ i j, raw19219step1 i j = -(raw19219step0 i j); unfold raw19219step1 raw19219step0; decide +kernel
      have hl : raw19219step1Labels = raw19219step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19219step1 raw19219step1Labels = mixedMoment B raw19219step2 raw19219step2Labels := by
      have ha : raw19219step2 = raw19219step1 := by apply Matrix.ext; unfold raw19219step2 raw19219step1; decide +kernel
      have hl : raw19219step1Labels = labelEmbedding1 ∘ raw19219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19219step1 raw19219step1Labels raw19219step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3979 node3979Labels := by rfl

theorem canonical19220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19220 raw19220Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw19220 raw19220Labels = mixedMoment B raw19220step0 raw19220step0Labels := by
      have ha : raw19220step0 = (fun i j => raw19220 (permutation313 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19220step0 raw19220; decide +kernel
      have hl : raw19220step0Labels = raw19220Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19220 raw19220Labels permutation313 permutation5
    mixedMoment B raw19220step0 raw19220step0Labels = mixedMoment B raw19220step1 raw19220step1Labels := by
      have ha : raw19220step1 = -raw19220step0 := by apply Matrix.ext; change ∀ i j, raw19220step1 i j = -(raw19220step0 i j); unfold raw19220step1 raw19220step0; decide +kernel
      have hl : raw19220step1Labels = raw19220step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19220step1 raw19220step1Labels = mixedMoment B raw19220step2 raw19220step2Labels := by
      have ha : raw19220step2 = raw19220step1 := by apply Matrix.ext; unfold raw19220step2 raw19220step1; decide +kernel
      have hl : raw19220step1Labels = labelEmbedding1 ∘ raw19220step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19220step1 raw19220step1Labels raw19220step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3994 node3994Labels := by rfl

theorem canonical19221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19221 raw19221Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw19221 raw19221Labels = mixedMoment B raw19221step0 raw19221step0Labels := by
      have ha : raw19221step0 = (fun i j => raw19221 (permutation327 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19221step0 raw19221; decide +kernel
      have hl : raw19221step0Labels = raw19221Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19221 raw19221Labels permutation327 permutation5
    mixedMoment B raw19221step0 raw19221step0Labels = mixedMoment B raw19221step1 raw19221step1Labels := by
      have ha : raw19221step1 = -raw19221step0 := by apply Matrix.ext; change ∀ i j, raw19221step1 i j = -(raw19221step0 i j); unfold raw19221step1 raw19221step0; decide +kernel
      have hl : raw19221step1Labels = raw19221step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19221step1 raw19221step1Labels = mixedMoment B raw19221step2 raw19221step2Labels := by
      have ha : raw19221step2 = raw19221step1 := by apply Matrix.ext; unfold raw19221step2 raw19221step1; decide +kernel
      have hl : raw19221step1Labels = labelEmbedding1 ∘ raw19221step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19221step1 raw19221step1Labels raw19221step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3994 node3994Labels := by rfl

theorem canonical19222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19222 raw19222Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw19222 raw19222Labels = mixedMoment B raw19222step0 raw19222step0Labels := by
      have hz : ∀ j, raw19222 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19222step0 = (fun i j => raw19222 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19222step0 raw19222; decide +kernel
      have hl : raw19222step0Labels = raw19222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19222 raw19222Labels permutation590 hz
    mixedMoment B raw19222step0 raw19222step0Labels = mixedMoment B raw19222step1 raw19222step1Labels := by
      have ha : raw19222step1 = (fun i j => raw19222step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19222step1 raw19222step0; decide +kernel
      have hl : raw19222step1Labels = raw19222step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19222step0 raw19222step0Labels permutation38 permutation7
    mixedMoment B raw19222step1 raw19222step1Labels = mixedMoment B raw19222step2 raw19222step2Labels := by
      have ha : raw19222step2 = -raw19222step1 := by apply Matrix.ext; change ∀ i j, raw19222step2 i j = -(raw19222step1 i j); unfold raw19222step2 raw19222step1; decide +kernel
      have hl : raw19222step2Labels = raw19222step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19222step2 raw19222step2Labels = mixedMoment B raw19222step3 raw19222step3Labels := by
      have ha : raw19222step3 = raw19222step2 := by apply Matrix.ext; unfold raw19222step3 raw19222step2; decide +kernel
      have hl : raw19222step2Labels = labelEmbedding1 ∘ raw19222step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19222step2 raw19222step2Labels raw19222step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3998 node3998Labels := by rfl

theorem canonical19223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19223 raw19223Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw19223 raw19223Labels = mixedMoment B raw19223step0 raw19223step0Labels := by
      have ha : raw19223step0 = (fun i j => raw19223 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19223step0 raw19223; decide +kernel
      have hl : raw19223step0Labels = raw19223Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19223 raw19223Labels permutation194 permutation7
    mixedMoment B raw19223step0 raw19223step0Labels = mixedMoment B raw19223step1 raw19223step1Labels := by
      have ha : raw19223step1 = -raw19223step0 := by apply Matrix.ext; change ∀ i j, raw19223step1 i j = -(raw19223step0 i j); unfold raw19223step1 raw19223step0; decide +kernel
      have hl : raw19223step1Labels = raw19223step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19223step1 raw19223step1Labels = mixedMoment B raw19223step2 raw19223step2Labels := by
      have ha : raw19223step2 = raw19223step1 := by apply Matrix.ext; unfold raw19223step2 raw19223step1; decide +kernel
      have hl : raw19223step1Labels = labelEmbedding1 ∘ raw19223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19223step1 raw19223step1Labels raw19223step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

theorem canonical19224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19224 raw19224Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw19224 raw19224Labels = mixedMoment B raw19224step0 raw19224step0Labels := by
      have ha : raw19224step0 = (fun i j => raw19224 (permutation274 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19224step0 raw19224; decide +kernel
      have hl : raw19224step0Labels = raw19224Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19224 raw19224Labels permutation274 permutation5
    mixedMoment B raw19224step0 raw19224step0Labels = mixedMoment B raw19224step1 raw19224step1Labels := by
      have ha : raw19224step1 = -raw19224step0 := by apply Matrix.ext; change ∀ i j, raw19224step1 i j = -(raw19224step0 i j); unfold raw19224step1 raw19224step0; decide +kernel
      have hl : raw19224step1Labels = raw19224step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19224step1 raw19224step1Labels = mixedMoment B raw19224step2 raw19224step2Labels := by
      have ha : raw19224step2 = raw19224step1 := by apply Matrix.ext; unfold raw19224step2 raw19224step1; decide +kernel
      have hl : raw19224step1Labels = labelEmbedding1 ∘ raw19224step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19224step1 raw19224step1Labels raw19224step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2662 node2662Labels := by rfl

theorem canonical19225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19225 raw19225Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw19225 raw19225Labels = mixedMoment B raw19225step0 raw19225step0Labels := by
      have ha : raw19225step0 = (fun i j => raw19225 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19225step0 raw19225; decide +kernel
      have hl : raw19225step0Labels = raw19225Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19225 raw19225Labels permutation194 permutation7
    mixedMoment B raw19225step0 raw19225step0Labels = mixedMoment B raw19225step1 raw19225step1Labels := by
      have ha : raw19225step1 = -raw19225step0 := by apply Matrix.ext; change ∀ i j, raw19225step1 i j = -(raw19225step0 i j); unfold raw19225step1 raw19225step0; decide +kernel
      have hl : raw19225step1Labels = raw19225step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19225step1 raw19225step1Labels = mixedMoment B raw19225step2 raw19225step2Labels := by
      have ha : raw19225step2 = raw19225step1 := by apply Matrix.ext; unfold raw19225step2 raw19225step1; decide +kernel
      have hl : raw19225step1Labels = labelEmbedding1 ∘ raw19225step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19225step1 raw19225step1Labels raw19225step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

theorem canonical19226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19226 raw19226Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw19226 raw19226Labels = mixedMoment B raw19226step0 raw19226step0Labels := by
      have ha : raw19226step0 = (fun i j => raw19226 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19226step0 raw19226; decide +kernel
      have hl : raw19226step0Labels = raw19226Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19226 raw19226Labels permutation195 permutation7
    mixedMoment B raw19226step0 raw19226step0Labels = mixedMoment B raw19226step1 raw19226step1Labels := by
      have ha : raw19226step1 = -raw19226step0 := by apply Matrix.ext; change ∀ i j, raw19226step1 i j = -(raw19226step0 i j); unfold raw19226step1 raw19226step0; decide +kernel
      have hl : raw19226step1Labels = raw19226step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19226step1 raw19226step1Labels = mixedMoment B raw19226step2 raw19226step2Labels := by
      have ha : raw19226step2 = raw19226step1 := by apply Matrix.ext; unfold raw19226step2 raw19226step1; decide +kernel
      have hl : raw19226step1Labels = labelEmbedding1 ∘ raw19226step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19226step1 raw19226step1Labels raw19226step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

theorem canonical19227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19227 raw19227Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw19227 raw19227Labels = mixedMoment B raw19227step0 raw19227step0Labels := by
      have hz : ∀ j, raw19227 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19227step0 = (fun i j => raw19227 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19227step0 raw19227; decide +kernel
      have hl : raw19227step0Labels = raw19227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19227 raw19227Labels permutation590 hz
    mixedMoment B raw19227step0 raw19227step0Labels = mixedMoment B raw19227step1 raw19227step1Labels := by
      have ha : raw19227step1 = (fun i j => raw19227step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19227step1 raw19227step0; decide +kernel
      have hl : raw19227step1Labels = raw19227step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19227step0 raw19227step0Labels permutation38 permutation7
    mixedMoment B raw19227step1 raw19227step1Labels = mixedMoment B raw19227step2 raw19227step2Labels := by
      have ha : raw19227step2 = -raw19227step1 := by apply Matrix.ext; change ∀ i j, raw19227step2 i j = -(raw19227step1 i j); unfold raw19227step2 raw19227step1; decide +kernel
      have hl : raw19227step2Labels = raw19227step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19227step2 raw19227step2Labels = mixedMoment B raw19227step3 raw19227step3Labels := by
      have ha : raw19227step3 = raw19227step2 := by apply Matrix.ext; unfold raw19227step3 raw19227step2; decide +kernel
      have hl : raw19227step2Labels = labelEmbedding1 ∘ raw19227step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19227step2 raw19227step2Labels raw19227step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3885 node3885Labels := by rfl

theorem canonical19228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19228 raw19228Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw19228 raw19228Labels = mixedMoment B raw19228step0 raw19228step0Labels := by
      have ha : raw19228step0 = (fun i j => raw19228 (permutation278 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19228step0 raw19228; decide +kernel
      have hl : raw19228step0Labels = raw19228Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19228 raw19228Labels permutation278 permutation5
    mixedMoment B raw19228step0 raw19228step0Labels = mixedMoment B raw19228step1 raw19228step1Labels := by
      have ha : raw19228step1 = -raw19228step0 := by apply Matrix.ext; change ∀ i j, raw19228step1 i j = -(raw19228step0 i j); unfold raw19228step1 raw19228step0; decide +kernel
      have hl : raw19228step1Labels = raw19228step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19228step1 raw19228step1Labels = mixedMoment B raw19228step2 raw19228step2Labels := by
      have ha : raw19228step2 = raw19228step1 := by apply Matrix.ext; unfold raw19228step2 raw19228step1; decide +kernel
      have hl : raw19228step1Labels = labelEmbedding1 ∘ raw19228step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19228step1 raw19228step1Labels raw19228step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical19229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19229 raw19229Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw19229 raw19229Labels = mixedMoment B raw19229step0 raw19229step0Labels := by
      have ha : raw19229step0 = (fun i j => raw19229 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19229step0 raw19229; decide +kernel
      have hl : raw19229step0Labels = raw19229Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19229 raw19229Labels permutation195 permutation7
    mixedMoment B raw19229step0 raw19229step0Labels = mixedMoment B raw19229step1 raw19229step1Labels := by
      have ha : raw19229step1 = -raw19229step0 := by apply Matrix.ext; change ∀ i j, raw19229step1 i j = -(raw19229step0 i j); unfold raw19229step1 raw19229step0; decide +kernel
      have hl : raw19229step1Labels = raw19229step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19229step1 raw19229step1Labels = mixedMoment B raw19229step2 raw19229step2Labels := by
      have ha : raw19229step2 = raw19229step1 := by apply Matrix.ext; unfold raw19229step2 raw19229step1; decide +kernel
      have hl : raw19229step1Labels = labelEmbedding1 ∘ raw19229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19229step1 raw19229step1Labels raw19229step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

theorem canonical19230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19230 raw19230Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw19230 raw19230Labels = mixedMoment B raw19230step0 raw19230step0Labels := by
      have ha : raw19230step0 = (fun i j => raw19230 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19230step0 raw19230; decide +kernel
      have hl : raw19230step0Labels = raw19230Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19230 raw19230Labels permutation195 permutation7
    mixedMoment B raw19230step0 raw19230step0Labels = mixedMoment B raw19230step1 raw19230step1Labels := by
      have ha : raw19230step1 = -raw19230step0 := by apply Matrix.ext; change ∀ i j, raw19230step1 i j = -(raw19230step0 i j); unfold raw19230step1 raw19230step0; decide +kernel
      have hl : raw19230step1Labels = raw19230step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19230step1 raw19230step1Labels = mixedMoment B raw19230step2 raw19230step2Labels := by
      have ha : raw19230step2 = raw19230step1 := by apply Matrix.ext; unfold raw19230step2 raw19230step1; decide +kernel
      have hl : raw19230step1Labels = labelEmbedding1 ∘ raw19230step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19230step1 raw19230step1Labels raw19230step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

theorem canonical19231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19231 raw19231Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw19231 raw19231Labels = mixedMoment B raw19231step0 raw19231step0Labels := by
      have hz : ∀ j, raw19231 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19231step0 = (fun i j => raw19231 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19231step0 raw19231; decide +kernel
      have hl : raw19231step0Labels = raw19231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19231 raw19231Labels permutation590 hz
    mixedMoment B raw19231step0 raw19231step0Labels = mixedMoment B raw19231step1 raw19231step1Labels := by
      have ha : raw19231step1 = (fun i j => raw19231step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19231step1 raw19231step0; decide +kernel
      have hl : raw19231step1Labels = raw19231step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19231step0 raw19231step0Labels permutation39 permutation7
    mixedMoment B raw19231step1 raw19231step1Labels = mixedMoment B raw19231step2 raw19231step2Labels := by
      have ha : raw19231step2 = -raw19231step1 := by apply Matrix.ext; change ∀ i j, raw19231step2 i j = -(raw19231step1 i j); unfold raw19231step2 raw19231step1; decide +kernel
      have hl : raw19231step2Labels = raw19231step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19231step2 raw19231step2Labels = mixedMoment B raw19231step3 raw19231step3Labels := by
      have ha : raw19231step3 = raw19231step2 := by apply Matrix.ext; unfold raw19231step3 raw19231step2; decide +kernel
      have hl : raw19231step2Labels = labelEmbedding1 ∘ raw19231step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19231step2 raw19231step2Labels raw19231step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical19232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19232 raw19232Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw19232 raw19232Labels = mixedMoment B raw19232step0 raw19232step0Labels := by
      have ha : raw19232step0 = (fun i j => raw19232 (permutation272 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19232step0 raw19232; decide +kernel
      have hl : raw19232step0Labels = raw19232Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19232 raw19232Labels permutation272 permutation5
    mixedMoment B raw19232step0 raw19232step0Labels = mixedMoment B raw19232step1 raw19232step1Labels := by
      have ha : raw19232step1 = -raw19232step0 := by apply Matrix.ext; change ∀ i j, raw19232step1 i j = -(raw19232step0 i j); unfold raw19232step1 raw19232step0; decide +kernel
      have hl : raw19232step1Labels = raw19232step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19232step1 raw19232step1Labels = mixedMoment B raw19232step2 raw19232step2Labels := by
      have ha : raw19232step2 = raw19232step1 := by apply Matrix.ext; unfold raw19232step2 raw19232step1; decide +kernel
      have hl : raw19232step1Labels = labelEmbedding1 ∘ raw19232step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19232step1 raw19232step1Labels raw19232step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical19233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19233 raw19233Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw19233 raw19233Labels = mixedMoment B raw19233step0 raw19233step0Labels := by
      have ha : raw19233step0 = (fun i j => raw19233 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19233step0 raw19233; decide +kernel
      have hl : raw19233step0Labels = raw19233Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19233 raw19233Labels permutation194 permutation7
    mixedMoment B raw19233step0 raw19233step0Labels = mixedMoment B raw19233step1 raw19233step1Labels := by
      have ha : raw19233step1 = -raw19233step0 := by apply Matrix.ext; change ∀ i j, raw19233step1 i j = -(raw19233step0 i j); unfold raw19233step1 raw19233step0; decide +kernel
      have hl : raw19233step1Labels = raw19233step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19233step1 raw19233step1Labels = mixedMoment B raw19233step2 raw19233step2Labels := by
      have ha : raw19233step2 = raw19233step1 := by apply Matrix.ext; unfold raw19233step2 raw19233step1; decide +kernel
      have hl : raw19233step1Labels = labelEmbedding1 ∘ raw19233step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19233step1 raw19233step1Labels raw19233step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

theorem canonical19234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19234 raw19234Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw19234 raw19234Labels = mixedMoment B raw19234step0 raw19234step0Labels := by
      have ha : raw19234step0 = (fun i j => raw19234 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19234step0 raw19234; decide +kernel
      have hl : raw19234step0Labels = raw19234Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19234 raw19234Labels permutation194 permutation7
    mixedMoment B raw19234step0 raw19234step0Labels = mixedMoment B raw19234step1 raw19234step1Labels := by
      have ha : raw19234step1 = -raw19234step0 := by apply Matrix.ext; change ∀ i j, raw19234step1 i j = -(raw19234step0 i j); unfold raw19234step1 raw19234step0; decide +kernel
      have hl : raw19234step1Labels = raw19234step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19234step1 raw19234step1Labels = mixedMoment B raw19234step2 raw19234step2Labels := by
      have ha : raw19234step2 = raw19234step1 := by apply Matrix.ext; unfold raw19234step2 raw19234step1; decide +kernel
      have hl : raw19234step1Labels = labelEmbedding1 ∘ raw19234step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19234step1 raw19234step1Labels raw19234step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

theorem canonical19235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19235 raw19235Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw19235 raw19235Labels = mixedMoment B raw19235step0 raw19235step0Labels := by
      have hz : ∀ j, raw19235 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19235step0 = (fun i j => raw19235 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19235step0 raw19235; decide +kernel
      have hl : raw19235step0Labels = raw19235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19235 raw19235Labels permutation590 hz
    mixedMoment B raw19235step0 raw19235step0Labels = mixedMoment B raw19235step1 raw19235step1Labels := by
      have ha : raw19235step1 = (fun i j => raw19235step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19235step1 raw19235step0; decide +kernel
      have hl : raw19235step1Labels = raw19235step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19235step0 raw19235step0Labels permutation38 permutation7
    mixedMoment B raw19235step1 raw19235step1Labels = mixedMoment B raw19235step2 raw19235step2Labels := by
      have ha : raw19235step2 = -raw19235step1 := by apply Matrix.ext; change ∀ i j, raw19235step2 i j = -(raw19235step1 i j); unfold raw19235step2 raw19235step1; decide +kernel
      have hl : raw19235step2Labels = raw19235step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19235step2 raw19235step2Labels = mixedMoment B raw19235step3 raw19235step3Labels := by
      have ha : raw19235step3 = raw19235step2 := by apply Matrix.ext; unfold raw19235step3 raw19235step2; decide +kernel
      have hl : raw19235step2Labels = labelEmbedding1 ∘ raw19235step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19235step2 raw19235step2Labels raw19235step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical19236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19236 raw19236Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw19236 raw19236Labels = mixedMoment B raw19236step0 raw19236step0Labels := by
      have ha : raw19236step0 = (fun i j => raw19236 (permutation273 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19236step0 raw19236; decide +kernel
      have hl : raw19236step0Labels = raw19236Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19236 raw19236Labels permutation273 permutation5
    mixedMoment B raw19236step0 raw19236step0Labels = mixedMoment B raw19236step1 raw19236step1Labels := by
      have ha : raw19236step1 = -raw19236step0 := by apply Matrix.ext; change ∀ i j, raw19236step1 i j = -(raw19236step0 i j); unfold raw19236step1 raw19236step0; decide +kernel
      have hl : raw19236step1Labels = raw19236step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19236step1 raw19236step1Labels = mixedMoment B raw19236step2 raw19236step2Labels := by
      have ha : raw19236step2 = raw19236step1 := by apply Matrix.ext; unfold raw19236step2 raw19236step1; decide +kernel
      have hl : raw19236step1Labels = labelEmbedding1 ∘ raw19236step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19236step1 raw19236step1Labels raw19236step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2661 node2661Labels := by rfl

theorem canonical19237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19237 raw19237Labels = mixedMoment B node3810 node3810Labels := by
  calc
    mixedMoment B raw19237 raw19237Labels = mixedMoment B raw19237step0 raw19237step0Labels := by
      have ha : raw19237step0 = (fun i j => raw19237 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19237step0 raw19237; decide +kernel
      have hl : raw19237step0Labels = raw19237Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19237 raw19237Labels permutation194 permutation7
    mixedMoment B raw19237step0 raw19237step0Labels = mixedMoment B raw19237step1 raw19237step1Labels := by
      have ha : raw19237step1 = -raw19237step0 := by apply Matrix.ext; change ∀ i j, raw19237step1 i j = -(raw19237step0 i j); unfold raw19237step1 raw19237step0; decide +kernel
      have hl : raw19237step1Labels = raw19237step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19237step1 raw19237step1Labels = mixedMoment B raw19237step2 raw19237step2Labels := by
      have ha : raw19237step2 = raw19237step1 := by apply Matrix.ext; unfold raw19237step2 raw19237step1; decide +kernel
      have hl : raw19237step1Labels = labelEmbedding1 ∘ raw19237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19237step1 raw19237step1Labels raw19237step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3810 node3810Labels := by rfl

theorem canonical19238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19238 raw19238Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw19238 raw19238Labels = mixedMoment B raw19238step0 raw19238step0Labels := by
      have ha : raw19238step0 = (fun i j => raw19238 (permutation642 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19238step0 raw19238; decide +kernel
      have hl : raw19238step0Labels = raw19238Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19238 raw19238Labels permutation642 permutation5
    mixedMoment B raw19238step0 raw19238step0Labels = mixedMoment B raw19238step1 raw19238step1Labels := by
      have ha : raw19238step1 = raw19238step0 := by apply Matrix.ext; unfold raw19238step1 raw19238step0; decide +kernel
      have hl : raw19238step0Labels = labelEmbedding1 ∘ raw19238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19238step0 raw19238step0Labels raw19238step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical19239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19239 raw19239Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw19239 raw19239Labels = mixedMoment B raw19239step0 raw19239step0Labels := by
      have ha : raw19239step0 = (fun i j => raw19239 (permutation636 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19239step0 raw19239; decide +kernel
      have hl : raw19239step0Labels = raw19239Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19239 raw19239Labels permutation636 permutation5
    mixedMoment B raw19239step0 raw19239step0Labels = mixedMoment B raw19239step1 raw19239step1Labels := by
      have ha : raw19239step1 = raw19239step0 := by apply Matrix.ext; unfold raw19239step1 raw19239step0; decide +kernel
      have hl : raw19239step0Labels = labelEmbedding1 ∘ raw19239step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19239step0 raw19239step0Labels raw19239step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical19324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19324 raw19324Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw19324 raw19324Labels = mixedMoment B raw19324step0 raw19324step0Labels := by
      have hz : ∀ j, raw19324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19324step0 = (fun i j => raw19324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19324step0 raw19324; decide +kernel
      have hl : raw19324step0Labels = raw19324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19324 raw19324Labels permutation346 hz
    mixedMoment B raw19324step0 raw19324step0Labels = mixedMoment B raw19324step1 raw19324step1Labels := by
      have ha : raw19324step1 = (fun i j => raw19324step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19324step1 raw19324step0; decide +kernel
      have hl : raw19324step1Labels = raw19324step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19324step0 raw19324step0Labels permutation56 permutation3
    mixedMoment B raw19324step1 raw19324step1Labels = mixedMoment B raw19324step2 raw19324step2Labels := by
      have ha : raw19324step2 = raw19324step1 := by apply Matrix.ext; unfold raw19324step2 raw19324step1; decide +kernel
      have hl : raw19324step1Labels = labelEmbedding6 ∘ raw19324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19324step1 raw19324step1Labels raw19324step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical19325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19325 raw19325Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw19325 raw19325Labels = mixedMoment B raw19325step0 raw19325step0Labels := by
      have ha : raw19325step0 = (fun i j => raw19325 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19325step0 raw19325; decide +kernel
      have hl : raw19325step0Labels = raw19325Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19325 raw19325Labels permutation156 permutation7
    mixedMoment B raw19325step0 raw19325step0Labels = mixedMoment B raw19325step1 raw19325step1Labels := by
      have ha : raw19325step1 = -raw19325step0 := by apply Matrix.ext; change ∀ i j, raw19325step1 i j = -(raw19325step0 i j); unfold raw19325step1 raw19325step0; decide +kernel
      have hl : raw19325step1Labels = raw19325step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19325step1 raw19325step1Labels = mixedMoment B raw19325step2 raw19325step2Labels := by
      have ha : raw19325step2 = raw19325step1 := by apply Matrix.ext; unfold raw19325step2 raw19325step1; decide +kernel
      have hl : raw19325step1Labels = labelEmbedding10 ∘ raw19325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19325step1 raw19325step1Labels raw19325step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

theorem canonical19326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19326 raw19326Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw19326 raw19326Labels = mixedMoment B raw19326step0 raw19326step0Labels := by
      have hz : ∀ j, raw19326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19326step0 = (fun i j => raw19326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19326step0 raw19326; decide +kernel
      have hl : raw19326step0Labels = raw19326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19326 raw19326Labels permutation346 hz
    mixedMoment B raw19326step0 raw19326step0Labels = mixedMoment B raw19326step1 raw19326step1Labels := by
      have ha : raw19326step1 = (fun i j => raw19326step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19326step1 raw19326step0; decide +kernel
      have hl : raw19326step1Labels = raw19326step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19326step0 raw19326step0Labels permutation50 permutation6
    mixedMoment B raw19326step1 raw19326step1Labels = mixedMoment B raw19326step2 raw19326step2Labels := by
      have ha : raw19326step2 = -raw19326step1 := by apply Matrix.ext; change ∀ i j, raw19326step2 i j = -(raw19326step1 i j); unfold raw19326step2 raw19326step1; decide +kernel
      have hl : raw19326step2Labels = raw19326step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19326step2 raw19326step2Labels = mixedMoment B raw19326step3 raw19326step3Labels := by
      have ha : raw19326step3 = raw19326step2 := by apply Matrix.ext; unfold raw19326step3 raw19326step2; decide +kernel
      have hl : raw19326step2Labels = labelEmbedding9 ∘ raw19326step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19326step2 raw19326step2Labels raw19326step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical19327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19327 raw19327Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw19327 raw19327Labels = mixedMoment B raw19327step0 raw19327step0Labels := by
      have hz : ∀ j, raw19327 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19327step0 = (fun i j => raw19327 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19327step0 raw19327; decide +kernel
      have hl : raw19327step0Labels = raw19327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19327 raw19327Labels permutation590 hz
    mixedMoment B raw19327step0 raw19327step0Labels = mixedMoment B raw19327step1 raw19327step1Labels := by
      have hz : ∀ j, raw19327step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19327step1 = (fun i j => raw19327step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19327step1 raw19327step0; decide +kernel
      have hl : raw19327step1Labels = raw19327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19327step0 raw19327step0Labels permutation80 hz
    mixedMoment B raw19327step1 raw19327step1Labels = mixedMoment B raw19327step2 raw19327step2Labels := by
      have ha : raw19327step2 = (fun i j => raw19327step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19327step2 raw19327step1; decide +kernel
      have hl : raw19327step2Labels = raw19327step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19327step1 raw19327step1Labels permutation8 permutation7
    mixedMoment B raw19327step2 raw19327step2Labels = mixedMoment B raw19327step3 raw19327step3Labels := by
      have ha : raw19327step3 = -raw19327step2 := by apply Matrix.ext; change ∀ i j, raw19327step3 i j = -(raw19327step2 i j); unfold raw19327step3 raw19327step2; decide +kernel
      have hl : raw19327step3Labels = raw19327step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19327step3 raw19327step3Labels = mixedMoment B raw19327step4 raw19327step4Labels := by
      have ha : raw19327step4 = raw19327step3 := by apply Matrix.ext; unfold raw19327step4 raw19327step3; decide +kernel
      have hl : raw19327step3Labels = labelEmbedding10 ∘ raw19327step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19327step3 raw19327step3Labels raw19327step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5493 node5493Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19328 raw19328Labels = mixedMoment B node5386 node5386Labels := by
  calc
    mixedMoment B raw19328 raw19328Labels = mixedMoment B raw19328step0 raw19328step0Labels := by
      have ha : raw19328step0 = (fun i j => raw19328 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19328step0 raw19328; decide +kernel
      have hl : raw19328step0Labels = raw19328Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19328 raw19328Labels permutation156 permutation2
    _ = mixedMoment B node5386 node5386Labels := by rfl

theorem canonical19329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19329 raw19329Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw19329 raw19329Labels = mixedMoment B raw19329step0 raw19329step0Labels := by
      have ha : raw19329step0 = (fun i j => raw19329 (permutation165 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19329step0 raw19329; decide +kernel
      have hl : raw19329step0Labels = raw19329Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19329 raw19329Labels permutation165 permutation2
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical19330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19330 raw19330Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw19330 raw19330Labels = mixedMoment B raw19330step0 raw19330step0Labels := by
      have hz : ∀ j, raw19330 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19330step0 = (fun i j => raw19330 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19330step0 raw19330; decide +kernel
      have hl : raw19330step0Labels = raw19330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19330 raw19330Labels permutation590 hz
    _ = mixedMoment B node5440 node5440Labels := by rfl

theorem canonical19331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19331 raw19331Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw19331 raw19331Labels = mixedMoment B raw19331step0 raw19331step0Labels := by
      have hz : ∀ j, raw19331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19331step0 = (fun i j => raw19331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19331step0 raw19331; decide +kernel
      have hl : raw19331step0Labels = raw19331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19331 raw19331Labels permutation346 hz
    mixedMoment B raw19331step0 raw19331step0Labels = mixedMoment B raw19331step1 raw19331step1Labels := by
      have ha : raw19331step1 = (fun i j => raw19331step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19331step1 raw19331step0; decide +kernel
      have hl : raw19331step1Labels = raw19331step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19331step0 raw19331step0Labels permutation37 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

theorem canonical19332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19332 raw19332Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw19332 raw19332Labels = mixedMoment B raw19332step0 raw19332step0Labels := by
      have ha : raw19332step0 = (fun i j => raw19332 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19332step0 raw19332; decide +kernel
      have hl : raw19332step0Labels = raw19332Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19332 raw19332Labels permutation157 permutation2
    _ = mixedMoment B node5416 node5416Labels := by rfl

theorem canonical19333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19333 raw19333Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw19333 raw19333Labels = mixedMoment B raw19333step0 raw19333step0Labels := by
      have hz : ∀ j, raw19333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19333step0 = (fun i j => raw19333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19333step0 raw19333; decide +kernel
      have hl : raw19333step0Labels = raw19333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19333 raw19333Labels permutation346 hz
    mixedMoment B raw19333step0 raw19333step0Labels = mixedMoment B raw19333step1 raw19333step1Labels := by
      have ha : raw19333step1 = (fun i j => raw19333step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19333step1 raw19333step0; decide +kernel
      have hl : raw19333step1Labels = raw19333step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19333step0 raw19333step0Labels permutation35 permutation2
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical19334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19334 raw19334Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw19334 raw19334Labels = mixedMoment B raw19334step0 raw19334step0Labels := by
      have hz : ∀ j, raw19334 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19334step0 = (fun i j => raw19334 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19334step0 raw19334; decide +kernel
      have hl : raw19334step0Labels = raw19334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19334 raw19334Labels permutation590 hz
    mixedMoment B raw19334step0 raw19334step0Labels = mixedMoment B raw19334step1 raw19334step1Labels := by
      have hz : ∀ j, raw19334step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19334step1 = (fun i j => raw19334step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19334step1 raw19334step0; decide +kernel
      have hl : raw19334step1Labels = raw19334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19334step0 raw19334step0Labels permutation80 hz
    mixedMoment B raw19334step1 raw19334step1Labels = mixedMoment B raw19334step2 raw19334step2Labels := by
      have ha : raw19334step2 = (fun i j => raw19334step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19334step2 raw19334step1; decide +kernel
      have hl : raw19334step2Labels = raw19334step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19334step1 raw19334step1Labels permutation9 permutation2
    _ = mixedMoment B node5442 node5442Labels := by rfl

theorem canonical19335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19335 raw19335Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw19335 raw19335Labels = mixedMoment B raw19335step0 raw19335step0Labels := by
      have hz : ∀ j, raw19335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19335step0 = (fun i j => raw19335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19335step0 raw19335; decide +kernel
      have hl : raw19335step0Labels = raw19335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19335 raw19335Labels permutation346 hz
    mixedMoment B raw19335step0 raw19335step0Labels = mixedMoment B raw19335step1 raw19335step1Labels := by
      have ha : raw19335step1 = (fun i j => raw19335step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19335step1 raw19335step0; decide +kernel
      have hl : raw19335step1Labels = raw19335step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19335step0 raw19335step0Labels permutation36 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

theorem canonical19336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19336 raw19336Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw19336 raw19336Labels = mixedMoment B raw19336step0 raw19336step0Labels := by
      have ha : raw19336step0 = (fun i j => raw19336 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19336step0 raw19336; decide +kernel
      have hl : raw19336step0Labels = raw19336Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19336 raw19336Labels permutation156 permutation2
    _ = mixedMoment B node5416 node5416Labels := by rfl

theorem canonical19337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19337 raw19337Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw19337 raw19337Labels = mixedMoment B raw19337step0 raw19337step0Labels := by
      have hz : ∀ j, raw19337 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19337step0 = (fun i j => raw19337 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19337step0 raw19337; decide +kernel
      have hl : raw19337step0Labels = raw19337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19337 raw19337Labels permutation590 hz
    mixedMoment B raw19337step0 raw19337step0Labels = mixedMoment B raw19337step1 raw19337step1Labels := by
      have hz : ∀ j, raw19337step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19337step1 = (fun i j => raw19337step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19337step1 raw19337step0; decide +kernel
      have hl : raw19337step1Labels = raw19337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19337step0 raw19337step0Labels permutation80 hz
    _ = mixedMoment B node5442 node5442Labels := by rfl

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

theorem canonical2547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2547 raw2547Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw2547 raw2547Labels = mixedMoment B raw2547step0 raw2547step0Labels := by
      have ha : raw2547step0 = (fun i j => raw2547 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2547step0 raw2547; decide +kernel
      have hl : raw2547step0Labels = raw2547Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2547 raw2547Labels permutation152 permutation5
    mixedMoment B raw2547step0 raw2547step0Labels = mixedMoment B raw2547step1 raw2547step1Labels := by
      have ha : raw2547step1 = raw2547step0 := by apply Matrix.ext; unfold raw2547step1 raw2547step0; decide +kernel
      have hl : raw2547step0Labels = labelEmbedding8 ∘ raw2547step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2547step0 raw2547step0Labels raw2547step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical2548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2548 raw2548Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw2548 raw2548Labels = mixedMoment B raw2548step0 raw2548step0Labels := by
      have ha : raw2548step0 = (fun i j => raw2548 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2548step0 raw2548; decide +kernel
      have hl : raw2548step0Labels = raw2548Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2548 raw2548Labels permutation152 permutation4
    _ = mixedMoment B node4025 node4025Labels := by rfl

theorem canonical2549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2549 raw2549Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw2549 raw2549Labels = mixedMoment B raw2549step0 raw2549step0Labels := by
      have ha : raw2549step0 = (fun i j => raw2549 (permutation216 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2549step0 raw2549; decide +kernel
      have hl : raw2549step0Labels = raw2549Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2549 raw2549Labels permutation216 permutation3
    mixedMoment B raw2549step0 raw2549step0Labels = mixedMoment B raw2549step1 raw2549step1Labels := by
      have ha : raw2549step1 = -raw2549step0 := by apply Matrix.ext; change ∀ i j, raw2549step1 i j = -(raw2549step0 i j); unfold raw2549step1 raw2549step0; decide +kernel
      have hl : raw2549step1Labels = raw2549step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2549step1 raw2549step1Labels = mixedMoment B raw2549step2 raw2549step2Labels := by
      have ha : raw2549step2 = raw2549step1 := by apply Matrix.ext; unfold raw2549step2 raw2549step1; decide +kernel
      have hl : raw2549step1Labels = labelEmbedding1 ∘ raw2549step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2549step1 raw2549step1Labels raw2549step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3909 node3909Labels := by rfl

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

theorem canonical2677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2677 raw2677Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw2677 raw2677Labels = mixedMoment B raw2677step0 raw2677step0Labels := by
      have hz : ∀ j, raw2677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2677step0 = (fun i j => raw2677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2677step0 raw2677; decide +kernel
      have hl : raw2677step0Labels = raw2677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2677 raw2677Labels permutation346 hz
    mixedMoment B raw2677step0 raw2677step0Labels = mixedMoment B raw2677step1 raw2677step1Labels := by
      have ha : raw2677step1 = (fun i j => raw2677step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2677step1 raw2677step0; decide +kernel
      have hl : raw2677step1Labels = raw2677step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2677step0 raw2677step0Labels permutation34 permutation2
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical2680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2680 raw2680Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw2680 raw2680Labels = mixedMoment B raw2680step0 raw2680step0Labels := by
      have hz : ∀ j, raw2680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2680step0 = (fun i j => raw2680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2680step0 raw2680; decide +kernel
      have hl : raw2680step0Labels = raw2680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2680 raw2680Labels permutation346 hz
    mixedMoment B raw2680step0 raw2680step0Labels = mixedMoment B raw2680step1 raw2680step1Labels := by
      have hz : ∀ j, raw2680step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2680step1 = (fun i j => raw2680step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2680step1 raw2680step0; decide +kernel
      have hl : raw2680step1Labels = raw2680step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2680step0 raw2680step0Labels permutation56 hz
    mixedMoment B raw2680step1 raw2680step1Labels = mixedMoment B raw2680step2 raw2680step2Labels := by
      have ha : raw2680step2 = (fun i j => raw2680step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2680step2 raw2680step1; decide +kernel
      have hl : raw2680step2Labels = raw2680step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2680step1 raw2680step1Labels permutation11 permutation2
    _ = mixedMoment B node5454 node5454Labels := by rfl

theorem canonical2682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2682 raw2682Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw2682 raw2682Labels = mixedMoment B raw2682step0 raw2682step0Labels := by
      have hz : ∀ j, raw2682 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2682step0 = (fun i j => raw2682 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2682step0 raw2682; decide +kernel
      have hl : raw2682step0Labels = raw2682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2682 raw2682Labels permutation346 hz
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical2685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2685 raw2685Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw2685 raw2685Labels = mixedMoment B raw2685step0 raw2685step0Labels := by
      have hz : ∀ j, raw2685 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2685step0 = (fun i j => raw2685 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2685step0 raw2685; decide +kernel
      have hl : raw2685step0Labels = raw2685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2685 raw2685Labels permutation346 hz
    mixedMoment B raw2685step0 raw2685step0Labels = mixedMoment B raw2685step1 raw2685step1Labels := by
      have hz : ∀ j, raw2685step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2685step1 = (fun i j => raw2685step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2685step1 raw2685step0; decide +kernel
      have hl : raw2685step1Labels = raw2685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2685step0 raw2685step0Labels permutation56 hz
    mixedMoment B raw2685step1 raw2685step1Labels = mixedMoment B raw2685step2 raw2685step2Labels := by
      have ha : raw2685step2 = (fun i j => raw2685step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2685step2 raw2685step1; decide +kernel
      have hl : raw2685step2Labels = raw2685step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2685step1 raw2685step1Labels permutation9 permutation2
    _ = mixedMoment B node5454 node5454Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7977 raw7977Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw7977 raw7977Labels = mixedMoment B raw7977step0 raw7977step0Labels := by
      have hz : ∀ j, raw7977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7977step0 = (fun i j => raw7977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7977step0 raw7977; decide +kernel
      have hl : raw7977step0Labels = raw7977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7977 raw7977Labels permutation346 hz
    _ = mixedMoment B node5172 node5172Labels := by rfl

theorem canonical7979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7979 raw7979Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw7979 raw7979Labels = mixedMoment B raw7979step0 raw7979step0Labels := by
      have hz : ∀ j, raw7979 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7979step0 = (fun i j => raw7979 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7979step0 raw7979; decide +kernel
      have hl : raw7979step0Labels = raw7979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7979 raw7979Labels permutation346 hz
    mixedMoment B raw7979step0 raw7979step0Labels = mixedMoment B raw7979step1 raw7979step1Labels := by
      have hz : ∀ j, raw7979step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7979step1 = (fun i j => raw7979step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7979step1 raw7979step0; decide +kernel
      have hl : raw7979step1Labels = raw7979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7979step0 raw7979step0Labels permutation56 hz
    mixedMoment B raw7979step1 raw7979step1Labels = mixedMoment B raw7979step2 raw7979step2Labels := by
      have ha : raw7979step2 = (fun i j => raw7979step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7979step2 raw7979step1; decide +kernel
      have hl : raw7979step2Labels = raw7979step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7979step1 raw7979step1Labels permutation12 permutation2
    _ = mixedMoment B node5307 node5307Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem singleton5447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5447 node5447Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node4025 node4025Labels + mixedMoment B node3909 node3909Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2547 singletonSmall5447
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5447) = raw2547Labels := by decide +kernel
  rw [hl, canonical2547 B hB] at h
  have hc0 : mixedMoment B raw2547 (Fin.cases (0 : Fin 2) singletonSmall5447) =
      mixedMoment B node4025 node4025Labels := by
    have ha : raw2547 = raw2548 := by apply Matrix.ext; unfold raw2547 raw2548; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5447 = raw2548Labels := by decide +kernel
    rw [ha, hj, canonical2548 B hB]
  have hc1 : mixedMoment B raw2547 (Fin.cases (1 : Fin 2) singletonSmall5447) =
      mixedMoment B node3909 node3909Labels := by
    have ha : raw2547 = raw2549 := by apply Matrix.ext; unfold raw2547 raw2549; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5447 = raw2549Labels := by decide +kernel
    rw [ha, hj, canonical2549 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem zero5440 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5440 node5440Labels = 0 := by
  exact mixedMoment_order_one B hB node5440 node5440Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5442 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5442 node5442Labels = 0 := by
  exact mixedMoment_order_one B hB node5442 node5442Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5454 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5454 node5454Labels = 0 := by
  exact mixedMoment_order_one B hB node5454 node5454Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5474 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5474 node5474Labels = 0 := by
  exact mixedMoment_order_one B hB node5474 node5474Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5486 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5486 node5486Labels = 0 := by
  exact mixedMoment_order_one B hB node5486 node5486Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5489 node5489Labels = 0 := by
  exact mixedMoment_alpha B hF node5489 node5489Labels 2 permutation152
    (by decide +kernel)

theorem zero5493 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5493 node5493Labels = 0 := by
  exact mixedMoment_order_one B hB node5493 node5493Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2661 node2661Labels = Sparse.eval nodeValue2661 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2661) = mixedMoment B node2661 node2661Labels := rfl
  simpa [nodeValue2661, Sparse.eval] using hc.symm

theorem sound2662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2662 node2662Labels = Sparse.eval nodeValue2662 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2662) = mixedMoment B node2662 node2662Labels := rfl
  simpa [nodeValue2662, Sparse.eval] using hc.symm

theorem sound2669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2669 node2669Labels = Sparse.eval nodeValue2669 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2669) = mixedMoment B node2669 node2669Labels := rfl
  simpa [nodeValue2669, Sparse.eval] using hc.symm

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

theorem sound2750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2750 node2750Labels = Sparse.eval nodeValue2750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2750) = mixedMoment B node2750 node2750Labels := rfl
  simpa [nodeValue2750, Sparse.eval] using hc.symm

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

theorem sound3529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3529 node3529Labels = Sparse.eval nodeValue3529 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3529) = mixedMoment B node3529 node3529Labels := rfl
  simpa [nodeValue3529, Sparse.eval] using hc.symm

theorem sound3532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3532 node3532Labels = Sparse.eval nodeValue3532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3532) = mixedMoment B node3532 node3532Labels := rfl
  simpa [nodeValue3532, Sparse.eval] using hc.symm

theorem sound3537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3537 node3537Labels = Sparse.eval nodeValue3537 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3537) = mixedMoment B node3537 node3537Labels := rfl
  simpa [nodeValue3537, Sparse.eval] using hc.symm

theorem sound3569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3569 node3569Labels = Sparse.eval nodeValue3569 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3569) = mixedMoment B node3569 node3569Labels := rfl
  simpa [nodeValue3569, Sparse.eval] using hc.symm

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

theorem zero3806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3806 node3806Labels = 0 := by
  exact mixedMoment_order_one B hB node3806 node3806Labels 1
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

theorem sound3804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3804 node3804Labels = Sparse.eval nodeValue3804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3804) = mixedMoment B node3804 node3804Labels := rfl
  simpa [nodeValue3804, Sparse.eval] using hc.symm

theorem sound3806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3806 node3806Labels = Sparse.eval nodeValue3806 (mixedVector B) := by
  simpa only [nodeValue3806, Sparse.eval_nil] using zero3806 B _hB _hF

theorem sound3810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3810 node3810Labels = Sparse.eval nodeValue3810 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3810) = mixedMoment B node3810 node3810Labels := rfl
  simpa [nodeValue3810, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3859 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3859 node3859Labels = 0 := by
  exact mixedMoment_order_one B hB node3859 node3859Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3840 node3840Labels = Sparse.eval nodeValue3840 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3840) = mixedMoment B node3840 node3840Labels := rfl
  simpa [nodeValue3840, Sparse.eval] using hc.symm

theorem sound3848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3848 node3848Labels = Sparse.eval nodeValue3848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3848) = mixedMoment B node3848 node3848Labels := rfl
  simpa [nodeValue3848, Sparse.eval] using hc.symm

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

theorem sound3859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3859 node3859Labels = Sparse.eval nodeValue3859 (mixedVector B) := by
  simpa only [nodeValue3859, Sparse.eval_nil] using zero3859 B _hB _hF

theorem sound3880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3880 node3880Labels = Sparse.eval nodeValue3880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3880) = mixedMoment B node3880 node3880Labels := rfl
  simpa [nodeValue3880, Sparse.eval] using hc.symm

theorem sound3885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3885 node3885Labels = Sparse.eval nodeValue3885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3885) = mixedMoment B node3885 node3885Labels := rfl
  simpa [nodeValue3885, Sparse.eval] using hc.symm

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

theorem sound3909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3909 node3909Labels = Sparse.eval nodeValue3909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3909) = mixedMoment B node3909 node3909Labels := rfl
  simpa [nodeValue3909, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3979 node3979Labels = 0 := by
  exact mixedMoment_alpha B hF node3979 node3979Labels 2 permutation158
    (by decide +kernel)

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

theorem sound3979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3979 node3979Labels = Sparse.eval nodeValue3979 (mixedVector B) := by
  simpa only [nodeValue3979, Sparse.eval_nil] using zero3979 B _hB _hF

theorem sound4025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4025 node4025Labels = Sparse.eval nodeValue4025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4025) = mixedMoment B node4025 node4025Labels := rfl
  simpa [nodeValue4025, Sparse.eval] using hc.symm

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

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem sound5307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5307 node5307Labels = Sparse.eval nodeValue5307 (mixedVector B) := by
  simpa only [nodeValue5307, Sparse.eval_nil] using zero5307 B _hB _hF

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

theorem zero5396 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5396 node5396Labels = 0 := by
  exact mixedMoment_order_one B hB node5396 node5396Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5396 node5396Labels = Sparse.eval nodeValue5396 (mixedVector B) := by
  simpa only [nodeValue5396, Sparse.eval_nil] using zero5396 B _hB _hF

theorem sound5422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5422 node5422Labels = Sparse.eval nodeValue5422 (mixedVector B) := by
  have h := singleton5422 B _hB
  rw [sound3900 B _hB _hF, sound3964 B _hB _hF] at h
  norm_num [nodeValue5422, nodeValue3900, nodeValue3964, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5427 node5427Labels = Sparse.eval nodeValue5427 (mixedVector B) := by
  simpa only [nodeValue5427, Sparse.eval_nil] using zero5427 B _hB _hF

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

theorem sound5440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5440 node5440Labels = Sparse.eval nodeValue5440 (mixedVector B) := by
  simpa only [nodeValue5440, Sparse.eval_nil] using zero5440 B _hB _hF

theorem sound5442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5442 node5442Labels = Sparse.eval nodeValue5442 (mixedVector B) := by
  simpa only [nodeValue5442, Sparse.eval_nil] using zero5442 B _hB _hF

theorem sound5447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5447 node5447Labels = Sparse.eval nodeValue5447 (mixedVector B) := by
  have h := singleton5447 B _hB
  rw [sound3909 B _hB _hF, sound4025 B _hB _hF] at h
  norm_num [nodeValue5447, nodeValue3909, nodeValue4025, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5454 node5454Labels = Sparse.eval nodeValue5454 (mixedVector B) := by
  simpa only [nodeValue5454, Sparse.eval_nil] using zero5454 B _hB _hF

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

theorem sound5478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5478 node5478Labels = Sparse.eval nodeValue5478 (mixedVector B) := by
  have h := singleton5478 B _hB
  rw [sound3974 B _hB _hF] at h
  norm_num [nodeValue5478, nodeValue3974, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5486 node5486Labels = Sparse.eval nodeValue5486 (mixedVector B) := by
  simpa only [nodeValue5486, Sparse.eval_nil] using zero5486 B _hB _hF

theorem sound5489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5489 node5489Labels = Sparse.eval nodeValue5489 (mixedVector B) := by
  simpa only [nodeValue5489, Sparse.eval_nil] using zero5489 B _hB _hF

theorem sound5493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5493 node5493Labels = Sparse.eval nodeValue5493 (mixedVector B) := by
  simpa only [nodeValue5493, Sparse.eval_nil] using zero5493 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources35
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1127 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1127 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1127 + difference 0 1) (sourceB1127 + difference 1 0) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA1127 + difference 0 1) (sourceB1127 + difference 1 0) sourceC1127) = raw19051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19051; decide +kernel
    rw [ha]
    exact (canonical19051 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1127 + difference 0 2) (sourceB1127 + difference 2 0) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA1127 + difference 0 2) (sourceB1127 + difference 2 0) sourceC1127) = raw19052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19052; decide +kernel
    rw [ha]
    exact (canonical19052 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1127 + difference 0 3) (sourceB1127 + difference 3 0) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1127 + difference 0 3) (sourceB1127 + difference 3 0) sourceC1127) = raw19053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19053; decide +kernel
    rw [ha]
    exact (canonical19053 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1127 + difference 0 4) (sourceB1127 + difference 4 0) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1127 + difference 0 4) (sourceB1127 + difference 4 0) sourceC1127) = raw19054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19054; decide +kernel
    rw [ha]
    exact (canonical19054 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1127 + difference 0 5) (sourceB1127 + difference 5 0) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1127 + difference 0 5) (sourceB1127 + difference 5 0) sourceC1127) = raw19055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19055; decide +kernel
    rw [ha]
    exact (canonical19055 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1127 + difference 1 0) (sourceB1127 + difference 0 1) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5427) := by
    have ha : (tripleCharges (sourceA1127 + difference 1 0) (sourceB1127 + difference 0 1) sourceC1127) = raw19056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19056; decide +kernel
    rw [ha]
    exact (canonical19056 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1127 + difference 1 2) (sourceB1127 + difference 2 1) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA1127 + difference 1 2) (sourceB1127 + difference 2 1) sourceC1127) = raw19057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19057; decide +kernel
    rw [ha]
    exact (canonical19057 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1127 + difference 1 3) (sourceB1127 + difference 3 1) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1127 + difference 1 3) (sourceB1127 + difference 3 1) sourceC1127) = raw19058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19058; decide +kernel
    rw [ha]
    exact (canonical19058 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1127 + difference 1 4) (sourceB1127 + difference 4 1) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1127 + difference 1 4) (sourceB1127 + difference 4 1) sourceC1127) = raw19059 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19059; decide +kernel
    rw [ha]
    exact (canonical19059 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1127 + difference 1 5) (sourceB1127 + difference 5 1) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1127 + difference 1 5) (sourceB1127 + difference 5 1) sourceC1127) = raw19060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19060; decide +kernel
    rw [ha]
    exact (canonical19060 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1127 + difference 2 0) (sourceB1127 + difference 0 2) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1127 + difference 2 0) (sourceB1127 + difference 0 2) sourceC1127) = raw19061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19061; decide +kernel
    rw [ha]
    exact (canonical19061 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1127 + difference 2 1) (sourceB1127 + difference 1 2) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5474) := by
    have ha : (tripleCharges (sourceA1127 + difference 2 1) (sourceB1127 + difference 1 2) sourceC1127) = raw19062 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19062; decide +kernel
    rw [ha]
    exact (canonical19062 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1127 + difference 2 3) (sourceB1127 + difference 3 2) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1127 + difference 2 3) (sourceB1127 + difference 3 2) sourceC1127) = raw19063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19063; decide +kernel
    rw [ha]
    exact (canonical19063 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1127 + difference 2 4) (sourceB1127 + difference 4 2) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1127 + difference 2 4) (sourceB1127 + difference 4 2) sourceC1127) = raw19064 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19064; decide +kernel
    rw [ha]
    exact (canonical19064 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1127 + difference 2 5) (sourceB1127 + difference 5 2) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1127 + difference 2 5) (sourceB1127 + difference 5 2) sourceC1127) = raw18890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw18890; decide +kernel
    rw [ha]
    exact (canonical18890 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1127 + difference 3 0) (sourceB1127 + difference 0 3) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA1127 + difference 3 0) (sourceB1127 + difference 0 3) sourceC1127) = raw19065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19065; decide +kernel
    rw [ha]
    exact (canonical19065 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1127 + difference 3 1) (sourceB1127 + difference 1 3) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1127 + difference 3 1) (sourceB1127 + difference 1 3) sourceC1127) = raw19066 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19066; decide +kernel
    rw [ha]
    exact (canonical19066 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1127 + difference 3 2) (sourceB1127 + difference 2 3) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1127 + difference 3 2) (sourceB1127 + difference 2 3) sourceC1127) = raw19067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19067; decide +kernel
    rw [ha]
    exact (canonical19067 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1127 + difference 3 4) (sourceB1127 + difference 4 3) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1127 + difference 3 4) (sourceB1127 + difference 4 3) sourceC1127) = raw19068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19068; decide +kernel
    rw [ha]
    exact (canonical19068 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1127 + difference 3 5) (sourceB1127 + difference 5 3) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1127 + difference 3 5) (sourceB1127 + difference 5 3) sourceC1127) = raw19069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19069; decide +kernel
    rw [ha]
    exact (canonical19069 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1127 + difference 4 0) (sourceB1127 + difference 0 4) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA1127 + difference 4 0) (sourceB1127 + difference 0 4) sourceC1127) = raw19070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19070; decide +kernel
    rw [ha]
    exact (canonical19070 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1127 + difference 4 1) (sourceB1127 + difference 1 4) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1127 + difference 4 1) (sourceB1127 + difference 1 4) sourceC1127) = raw19071 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19071; decide +kernel
    rw [ha]
    exact (canonical19071 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1127 + difference 4 2) (sourceB1127 + difference 2 4) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1127 + difference 4 2) (sourceB1127 + difference 2 4) sourceC1127) = raw19072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19072; decide +kernel
    rw [ha]
    exact (canonical19072 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1127 + difference 4 3) (sourceB1127 + difference 3 4) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1127 + difference 4 3) (sourceB1127 + difference 3 4) sourceC1127) = raw19073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19073; decide +kernel
    rw [ha]
    exact (canonical19073 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1127 + difference 4 5) (sourceB1127 + difference 5 4) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1127 + difference 4 5) (sourceB1127 + difference 5 4) sourceC1127) = raw19074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19074; decide +kernel
    rw [ha]
    exact (canonical19074 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1127 + difference 5 0) (sourceB1127 + difference 0 5) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA1127 + difference 5 0) (sourceB1127 + difference 0 5) sourceC1127) = raw19075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19075; decide +kernel
    rw [ha]
    exact (canonical19075 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1127 + difference 5 1) (sourceB1127 + difference 1 5) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1127 + difference 5 1) (sourceB1127 + difference 1 5) sourceC1127) = raw19076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19076; decide +kernel
    rw [ha]
    exact (canonical19076 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1127 + difference 5 2) (sourceB1127 + difference 2 5) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1127 + difference 5 2) (sourceB1127 + difference 2 5) sourceC1127) = raw19077 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19077; decide +kernel
    rw [ha]
    exact (canonical19077 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1127 + difference 5 3) (sourceB1127 + difference 3 5) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1127 + difference 5 3) (sourceB1127 + difference 3 5) sourceC1127) = raw19078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19078; decide +kernel
    rw [ha]
    exact (canonical19078 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1127 + difference 5 4) (sourceB1127 + difference 4 5) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1127 + difference 5 4) (sourceB1127 + difference 4 5) sourceC1127) = raw19079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19079; decide +kernel
    rw [ha]
    exact (canonical19079 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1127 sourceB1127 sourceC1127
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1127, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1133 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1133 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1133 + difference 0 1) (sourceB1133 + difference 1 0) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA1133 + difference 0 1) (sourceB1133 + difference 1 0) sourceC1133) = raw19218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19218; decide +kernel
    rw [ha]
    exact (canonical19218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1133 + difference 0 2) (sourceB1133 + difference 2 0) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA1133 + difference 0 2) (sourceB1133 + difference 2 0) sourceC1133) = raw19219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19219; decide +kernel
    rw [ha]
    exact (canonical19219 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1133 + difference 0 3) (sourceB1133 + difference 3 0) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3994) := by
    have ha : (tripleCharges (sourceA1133 + difference 0 3) (sourceB1133 + difference 3 0) sourceC1133) = raw19220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19220; decide +kernel
    rw [ha]
    exact (canonical19220 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1133 + difference 0 4) (sourceB1133 + difference 4 0) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3994) := by
    have ha : (tripleCharges (sourceA1133 + difference 0 4) (sourceB1133 + difference 4 0) sourceC1133) = raw19221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19221; decide +kernel
    rw [ha]
    exact (canonical19221 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1133 + difference 0 5) (sourceB1133 + difference 5 0) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA1133 + difference 0 5) (sourceB1133 + difference 5 0) sourceC1133) = raw19222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19222; decide +kernel
    rw [ha]
    exact (canonical19222 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1133 + difference 1 0) (sourceB1133 + difference 0 1) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA1133 + difference 1 0) (sourceB1133 + difference 0 1) sourceC1133) = raw19223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19223; decide +kernel
    rw [ha]
    exact (canonical19223 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1133 + difference 1 2) (sourceB1133 + difference 2 1) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA1133 + difference 1 2) (sourceB1133 + difference 2 1) sourceC1133) = raw13734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw13734; decide +kernel
    rw [ha]
    exact (canonical13734 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1133 + difference 1 3) (sourceB1133 + difference 3 1) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA1133 + difference 1 3) (sourceB1133 + difference 3 1) sourceC1133) = raw13735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw13735; decide +kernel
    rw [ha]
    exact (canonical13735 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1133 + difference 1 4) (sourceB1133 + difference 4 1) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA1133 + difference 1 4) (sourceB1133 + difference 4 1) sourceC1133) = raw13736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw13736; decide +kernel
    rw [ha]
    exact (canonical13736 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1133 + difference 1 5) (sourceB1133 + difference 5 1) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3859) := by
    have ha : (tripleCharges (sourceA1133 + difference 1 5) (sourceB1133 + difference 5 1) sourceC1133) = raw13737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw13737; decide +kernel
    rw [ha]
    exact (canonical13737 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1133 + difference 2 0) (sourceB1133 + difference 0 2) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3569) := by
    have ha : (tripleCharges (sourceA1133 + difference 2 0) (sourceB1133 + difference 0 2) sourceC1133) = raw13744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw13744; decide +kernel
    rw [ha]
    exact (canonical13744 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1133 + difference 2 1) (sourceB1133 + difference 1 2) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2662) := by
    have ha : (tripleCharges (sourceA1133 + difference 2 1) (sourceB1133 + difference 1 2) sourceC1133) = raw19224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19224; decide +kernel
    rw [ha]
    exact (canonical19224 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1133 + difference 2 3) (sourceB1133 + difference 3 2) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1133 + difference 2 3) (sourceB1133 + difference 3 2) sourceC1133) = raw19225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19225; decide +kernel
    rw [ha]
    exact (canonical19225 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1133 + difference 2 4) (sourceB1133 + difference 4 2) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1133 + difference 2 4) (sourceB1133 + difference 4 2) sourceC1133) = raw19226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19226; decide +kernel
    rw [ha]
    exact (canonical19226 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1133 + difference 2 5) (sourceB1133 + difference 5 2) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA1133 + difference 2 5) (sourceB1133 + difference 5 2) sourceC1133) = raw19227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19227; decide +kernel
    rw [ha]
    exact (canonical19227 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1133 + difference 3 0) (sourceB1133 + difference 0 3) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA1133 + difference 3 0) (sourceB1133 + difference 0 3) sourceC1133) = raw13749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw13749; decide +kernel
    rw [ha]
    exact (canonical13749 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1133 + difference 3 1) (sourceB1133 + difference 1 3) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA1133 + difference 3 1) (sourceB1133 + difference 1 3) sourceC1133) = raw19228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19228; decide +kernel
    rw [ha]
    exact (canonical19228 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1133 + difference 3 2) (sourceB1133 + difference 2 3) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA1133 + difference 3 2) (sourceB1133 + difference 2 3) sourceC1133) = raw19229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19229; decide +kernel
    rw [ha]
    exact (canonical19229 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1133 + difference 3 4) (sourceB1133 + difference 4 3) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA1133 + difference 3 4) (sourceB1133 + difference 4 3) sourceC1133) = raw19230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19230; decide +kernel
    rw [ha]
    exact (canonical19230 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1133 + difference 3 5) (sourceB1133 + difference 5 3) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA1133 + difference 3 5) (sourceB1133 + difference 5 3) sourceC1133) = raw19231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19231; decide +kernel
    rw [ha]
    exact (canonical19231 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1133 + difference 4 0) (sourceB1133 + difference 0 4) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA1133 + difference 4 0) (sourceB1133 + difference 0 4) sourceC1133) = raw13754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw13754; decide +kernel
    rw [ha]
    exact (canonical13754 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1133 + difference 4 1) (sourceB1133 + difference 1 4) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA1133 + difference 4 1) (sourceB1133 + difference 1 4) sourceC1133) = raw19232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19232; decide +kernel
    rw [ha]
    exact (canonical19232 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1133 + difference 4 2) (sourceB1133 + difference 2 4) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA1133 + difference 4 2) (sourceB1133 + difference 2 4) sourceC1133) = raw19233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19233; decide +kernel
    rw [ha]
    exact (canonical19233 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1133 + difference 4 3) (sourceB1133 + difference 3 4) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA1133 + difference 4 3) (sourceB1133 + difference 3 4) sourceC1133) = raw19234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19234; decide +kernel
    rw [ha]
    exact (canonical19234 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1133 + difference 4 5) (sourceB1133 + difference 5 4) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA1133 + difference 4 5) (sourceB1133 + difference 5 4) sourceC1133) = raw19235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19235; decide +kernel
    rw [ha]
    exact (canonical19235 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1133 + difference 5 0) (sourceB1133 + difference 0 5) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA1133 + difference 5 0) (sourceB1133 + difference 0 5) sourceC1133) = raw13759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw13759; decide +kernel
    rw [ha]
    exact (canonical13759 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1133 + difference 5 1) (sourceB1133 + difference 1 5) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2661) := by
    have ha : (tripleCharges (sourceA1133 + difference 5 1) (sourceB1133 + difference 1 5) sourceC1133) = raw19236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19236; decide +kernel
    rw [ha]
    exact (canonical19236 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1133 + difference 5 2) (sourceB1133 + difference 2 5) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3810) := by
    have ha : (tripleCharges (sourceA1133 + difference 5 2) (sourceB1133 + difference 2 5) sourceC1133) = raw19237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19237; decide +kernel
    rw [ha]
    exact (canonical19237 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1133 + difference 5 3) (sourceB1133 + difference 3 5) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA1133 + difference 5 3) (sourceB1133 + difference 3 5) sourceC1133) = raw19238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19238; decide +kernel
    rw [ha]
    exact (canonical19238 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1133 + difference 5 4) (sourceB1133 + difference 4 5) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA1133 + difference 5 4) (sourceB1133 + difference 4 5) sourceC1133) = raw19239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19239; decide +kernel
    rw [ha]
    exact (canonical19239 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1133 sourceB1133 sourceC1133
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1133, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1137 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1137 + difference 0 1) (sourceB1137 + difference 1 0) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1137 + difference 0 1) (sourceB1137 + difference 1 0) sourceC1137) = raw19324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19324; decide +kernel
    rw [ha]
    exact (canonical19324 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1137 + difference 0 2) (sourceB1137 + difference 2 0) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1137 + difference 0 2) (sourceB1137 + difference 2 0) sourceC1137) = raw19325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19325; decide +kernel
    rw [ha]
    exact (canonical19325 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1137 + difference 0 3) (sourceB1137 + difference 3 0) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1137 + difference 0 3) (sourceB1137 + difference 3 0) sourceC1137) = raw15170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw15170; decide +kernel
    rw [ha]
    exact (canonical15170 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1137 + difference 0 4) (sourceB1137 + difference 4 0) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1137 + difference 0 4) (sourceB1137 + difference 4 0) sourceC1137) = raw19326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19326; decide +kernel
    rw [ha]
    exact (canonical19326 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1137 + difference 0 5) (sourceB1137 + difference 5 0) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA1137 + difference 0 5) (sourceB1137 + difference 5 0) sourceC1137) = raw19327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19327; decide +kernel
    rw [ha]
    exact (canonical19327 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1137 + difference 1 0) (sourceB1137 + difference 0 1) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA1137 + difference 1 0) (sourceB1137 + difference 0 1) sourceC1137) = raw7979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw7979; decide +kernel
    rw [ha]
    exact (canonical7979 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1137 + difference 1 2) (sourceB1137 + difference 2 1) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1137 + difference 1 2) (sourceB1137 + difference 2 1) sourceC1137) = raw14054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw14054; decide +kernel
    rw [ha]
    exact (canonical14054 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1137 + difference 1 3) (sourceB1137 + difference 3 1) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA1137 + difference 1 3) (sourceB1137 + difference 3 1) sourceC1137) = raw2685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw2685; decide +kernel
    rw [ha]
    exact (canonical2685 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1137 + difference 1 4) (sourceB1137 + difference 4 1) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA1137 + difference 1 4) (sourceB1137 + difference 4 1) sourceC1137) = raw2680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw2680; decide +kernel
    rw [ha]
    exact (canonical2680 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1137 + difference 1 5) (sourceB1137 + difference 5 1) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA1137 + difference 1 5) (sourceB1137 + difference 5 1) sourceC1137) = raw14055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw14055; decide +kernel
    rw [ha]
    exact (canonical14055 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1137 + difference 2 0) (sourceB1137 + difference 0 2) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA1137 + difference 2 0) (sourceB1137 + difference 0 2) sourceC1137) = raw14061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw14061; decide +kernel
    rw [ha]
    exact (canonical14061 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1137 + difference 2 1) (sourceB1137 + difference 1 2) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5386) := by
    have ha : (tripleCharges (sourceA1137 + difference 2 1) (sourceB1137 + difference 1 2) sourceC1137) = raw19328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19328; decide +kernel
    rw [ha]
    exact (canonical19328 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1137 + difference 2 3) (sourceB1137 + difference 3 2) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1137 + difference 2 3) (sourceB1137 + difference 3 2) sourceC1137) = raw15173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw15173; decide +kernel
    rw [ha]
    exact (canonical15173 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1137 + difference 2 4) (sourceB1137 + difference 4 2) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1137 + difference 2 4) (sourceB1137 + difference 4 2) sourceC1137) = raw19329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19329; decide +kernel
    rw [ha]
    exact (canonical19329 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1137 + difference 2 5) (sourceB1137 + difference 5 2) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1137 + difference 2 5) (sourceB1137 + difference 5 2) sourceC1137) = raw19330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19330; decide +kernel
    rw [ha]
    exact (canonical19330 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1137 + difference 3 0) (sourceB1137 + difference 0 3) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1137 + difference 3 0) (sourceB1137 + difference 0 3) sourceC1137) = raw14065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw14065; decide +kernel
    rw [ha]
    exact (canonical14065 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1137 + difference 3 1) (sourceB1137 + difference 1 3) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA1137 + difference 3 1) (sourceB1137 + difference 1 3) sourceC1137) = raw19331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19331; decide +kernel
    rw [ha]
    exact (canonical19331 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1137 + difference 3 2) (sourceB1137 + difference 2 3) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA1137 + difference 3 2) (sourceB1137 + difference 2 3) sourceC1137) = raw19332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19332; decide +kernel
    rw [ha]
    exact (canonical19332 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1137 + difference 3 4) (sourceB1137 + difference 4 3) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1137 + difference 3 4) (sourceB1137 + difference 4 3) sourceC1137) = raw19333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19333; decide +kernel
    rw [ha]
    exact (canonical19333 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1137 + difference 3 5) (sourceB1137 + difference 5 3) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1137 + difference 3 5) (sourceB1137 + difference 5 3) sourceC1137) = raw19334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19334; decide +kernel
    rw [ha]
    exact (canonical19334 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1137 + difference 4 0) (sourceB1137 + difference 0 4) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1137 + difference 4 0) (sourceB1137 + difference 0 4) sourceC1137) = raw14070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw14070; decide +kernel
    rw [ha]
    exact (canonical14070 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1137 + difference 4 1) (sourceB1137 + difference 1 4) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA1137 + difference 4 1) (sourceB1137 + difference 1 4) sourceC1137) = raw19335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19335; decide +kernel
    rw [ha]
    exact (canonical19335 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1137 + difference 4 2) (sourceB1137 + difference 2 4) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA1137 + difference 4 2) (sourceB1137 + difference 2 4) sourceC1137) = raw19336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19336; decide +kernel
    rw [ha]
    exact (canonical19336 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1137 + difference 4 3) (sourceB1137 + difference 3 4) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1137 + difference 4 3) (sourceB1137 + difference 3 4) sourceC1137) = raw15179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw15179; decide +kernel
    rw [ha]
    exact (canonical15179 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1137 + difference 4 5) (sourceB1137 + difference 5 4) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1137 + difference 4 5) (sourceB1137 + difference 5 4) sourceC1137) = raw19337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19337; decide +kernel
    rw [ha]
    exact (canonical19337 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1137 + difference 5 0) (sourceB1137 + difference 0 5) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA1137 + difference 5 0) (sourceB1137 + difference 0 5) sourceC1137) = raw7977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw7977; decide +kernel
    rw [ha]
    exact (canonical7977 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1137 + difference 5 1) (sourceB1137 + difference 1 5) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA1137 + difference 5 1) (sourceB1137 + difference 1 5) sourceC1137) = raw15174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw15174; decide +kernel
    rw [ha]
    exact (canonical15174 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1137 + difference 5 2) (sourceB1137 + difference 2 5) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5417) := by
    have ha : (tripleCharges (sourceA1137 + difference 5 2) (sourceB1137 + difference 2 5) sourceC1137) = raw15175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw15175; decide +kernel
    rw [ha]
    exact (canonical15175 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1137 + difference 5 3) (sourceB1137 + difference 3 5) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1137 + difference 5 3) (sourceB1137 + difference 3 5) sourceC1137) = raw2682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw2682; decide +kernel
    rw [ha]
    exact (canonical2682 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1137 + difference 5 4) (sourceB1137 + difference 4 5) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1137 + difference 5 4) (sourceB1137 + difference 4 5) sourceC1137) = raw2677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw2677; decide +kernel
    rw [ha]
    exact (canonical2677 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1137 sourceB1137 sourceC1137
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1137, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck979 : Integer.Sparse.reindex keyMap MixedData.row979 = numericRow979 := by decide +kernel

theorem numericCheck979 (x : Master → ℝ) : Integer.Sparse.eval numericRow979 x =
    (1440 : ℝ) * reducedSource979 x := by
  norm_num [numericRow979, reducedSource979, Integer.Sparse.eval, Sparse.eval, nodeValue4091, nodeValue5396, nodeValue5422, nodeValue5427, nodeValue5433, nodeValue5437, nodeValue5447, nodeValue5469, nodeValue5474, nodeValue5478, nodeValue5482, nodeValue5486]
  ring

theorem reindexCheck985 : Integer.Sparse.reindex keyMap MixedData.row985 = numericRow985 := by decide +kernel

theorem numericCheck985 (x : Master → ℝ) : Integer.Sparse.eval numericRow985 x =
    (4320 : ℝ) * reducedSource985 x := by
  norm_num [numericRow985, reducedSource985, Integer.Sparse.eval, Sparse.eval, nodeValue2661, nodeValue2662, nodeValue2669, nodeValue2750, nodeValue3529, nodeValue3532, nodeValue3537, nodeValue3569, nodeValue3804, nodeValue3806, nodeValue3810, nodeValue3840, nodeValue3848, nodeValue3851, nodeValue3857, nodeValue3859, nodeValue3880, nodeValue3885, nodeValue3979, nodeValue3994, nodeValue3998]
  ring

theorem reindexCheck989 : Integer.Sparse.reindex keyMap MixedData.row989 = numericRow989 := by decide +kernel

theorem numericCheck989 (x : Master → ℝ) : Integer.Sparse.eval numericRow989 x =
    (17280 : ℝ) * reducedSource989 x := by
  norm_num [numericRow989, reducedSource989, Integer.Sparse.eval, Sparse.eval, nodeValue4093, nodeValue5167, nodeValue5169, nodeValue5172, nodeValue5307, nodeValue5386, nodeValue5387, nodeValue5388, nodeValue5416, nodeValue5417, nodeValue5433, nodeValue5434, nodeValue5435, nodeValue5440, nodeValue5442, nodeValue5450, nodeValue5454, nodeValue5489, nodeValue5490, nodeValue5493]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero979 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource979 (mixedVector B) = 0 := by
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  have h5396 : mixedVector B (Sum.inr 5396) = Sparse.eval nodeValue5396 (mixedVector B) := by
    change mixedMoment B node5396 node5396Labels = _
    exact sound5396 B hB hF
  have h5422 : mixedVector B (Sum.inr 5422) = Sparse.eval nodeValue5422 (mixedVector B) := by
    change mixedMoment B node5422 node5422Labels = _
    exact sound5422 B hB hF
  have h5427 : mixedVector B (Sum.inr 5427) = Sparse.eval nodeValue5427 (mixedVector B) := by
    change mixedMoment B node5427 node5427Labels = _
    exact sound5427 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5437 : mixedVector B (Sum.inr 5437) = Sparse.eval nodeValue5437 (mixedVector B) := by
    change mixedMoment B node5437 node5437Labels = _
    exact sound5437 B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  have h5469 : mixedVector B (Sum.inr 5469) = Sparse.eval nodeValue5469 (mixedVector B) := by
    change mixedMoment B node5469 node5469Labels = _
    exact sound5469 B hB hF
  have h5474 : mixedVector B (Sum.inr 5474) = Sparse.eval nodeValue5474 (mixedVector B) := by
    change mixedMoment B node5474 node5474Labels = _
    exact sound5474 B hB hF
  have h5478 : mixedVector B (Sum.inr 5478) = Sparse.eval nodeValue5478 (mixedVector B) := by
    change mixedMoment B node5478 node5478Labels = _
    exact sound5478 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482_e B hB hF
  have h5486 : mixedVector B (Sum.inr 5486) = Sparse.eval nodeValue5486 (mixedVector B) := by
    change mixedMoment B node5486 node5486Labels = _
    exact sound5486 B hB hF
  simpa only [sourceForm1127, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4091, h5396, h5422, h5427, h5433, h5437, h5447, h5469, h5474, h5478, h5482, h5486, reducedSource979] using sourceEq1127 B hB

theorem rowSound979 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row979 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck979, numericCheck979, reducedZero979 B hB hF, mul_zero]

theorem reducedZero985 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource985 (mixedVector B) = 0 := by
  have h2661 : mixedVector B (Sum.inr 2661) = Sparse.eval nodeValue2661 (mixedVector B) := by
    change mixedMoment B node2661 node2661Labels = _
    exact sound2661 B hB hF
  have h2662 : mixedVector B (Sum.inr 2662) = Sparse.eval nodeValue2662 (mixedVector B) := by
    change mixedMoment B node2662 node2662Labels = _
    exact sound2662 B hB hF
  have h2669 : mixedVector B (Sum.inr 2669) = Sparse.eval nodeValue2669 (mixedVector B) := by
    change mixedMoment B node2669 node2669Labels = _
    exact sound2669 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h3529 : mixedVector B (Sum.inr 3529) = Sparse.eval nodeValue3529 (mixedVector B) := by
    change mixedMoment B node3529 node3529Labels = _
    exact sound3529 B hB hF
  have h3532 : mixedVector B (Sum.inr 3532) = Sparse.eval nodeValue3532 (mixedVector B) := by
    change mixedMoment B node3532 node3532Labels = _
    exact sound3532 B hB hF
  have h3537 : mixedVector B (Sum.inr 3537) = Sparse.eval nodeValue3537 (mixedVector B) := by
    change mixedMoment B node3537 node3537Labels = _
    exact sound3537 B hB hF
  have h3569 : mixedVector B (Sum.inr 3569) = Sparse.eval nodeValue3569 (mixedVector B) := by
    change mixedMoment B node3569 node3569Labels = _
    exact sound3569 B hB hF
  have h3804 : mixedVector B (Sum.inr 3804) = Sparse.eval nodeValue3804 (mixedVector B) := by
    change mixedMoment B node3804 node3804Labels = _
    exact sound3804 B hB hF
  have h3806 : mixedVector B (Sum.inr 3806) = Sparse.eval nodeValue3806 (mixedVector B) := by
    change mixedMoment B node3806 node3806Labels = _
    exact sound3806 B hB hF
  have h3810 : mixedVector B (Sum.inr 3810) = Sparse.eval nodeValue3810 (mixedVector B) := by
    change mixedMoment B node3810 node3810Labels = _
    exact sound3810 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3851 : mixedVector B (Sum.inr 3851) = Sparse.eval nodeValue3851 (mixedVector B) := by
    change mixedMoment B node3851 node3851Labels = _
    exact sound3851_e B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h3859 : mixedVector B (Sum.inr 3859) = Sparse.eval nodeValue3859 (mixedVector B) := by
    change mixedMoment B node3859 node3859Labels = _
    exact sound3859 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h3885 : mixedVector B (Sum.inr 3885) = Sparse.eval nodeValue3885 (mixedVector B) := by
    change mixedMoment B node3885 node3885Labels = _
    exact sound3885 B hB hF
  have h3979 : mixedVector B (Sum.inr 3979) = Sparse.eval nodeValue3979 (mixedVector B) := by
    change mixedMoment B node3979 node3979Labels = _
    exact sound3979 B hB hF
  have h3994 : mixedVector B (Sum.inr 3994) = Sparse.eval nodeValue3994 (mixedVector B) := by
    change mixedMoment B node3994 node3994Labels = _
    exact sound3994_e B hB hF
  have h3998 : mixedVector B (Sum.inr 3998) = Sparse.eval nodeValue3998 (mixedVector B) := by
    change mixedMoment B node3998 node3998Labels = _
    exact sound3998_e B hB hF
  simpa only [sourceForm1133, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2661, h2662, h2669, h2750, h3529, h3532, h3537, h3569, h3804, h3806, h3810, h3840, h3848, h3851, h3857, h3859, h3880, h3885, h3979, h3994, h3998, reducedSource985] using sourceEq1133 B hB

theorem rowSound985 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row985 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck985, numericCheck985, reducedZero985 B hB hF, mul_zero]

theorem reducedZero989 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource989 (mixedVector B) = 0 := by
  have h4093 : mixedVector B (Sum.inr 4093) = Sparse.eval nodeValue4093 (mixedVector B) := by
    change mixedMoment B node4093 node4093Labels = _
    exact sound4093 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167_e B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169_e B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172_e B hB hF
  have h5307 : mixedVector B (Sum.inr 5307) = Sparse.eval nodeValue5307 (mixedVector B) := by
    change mixedMoment B node5307 node5307Labels = _
    exact sound5307 B hB hF
  have h5386 : mixedVector B (Sum.inr 5386) = Sparse.eval nodeValue5386 (mixedVector B) := by
    change mixedMoment B node5386 node5386Labels = _
    exact sound5386_e B hB hF
  have h5387 : mixedVector B (Sum.inr 5387) = Sparse.eval nodeValue5387 (mixedVector B) := by
    change mixedMoment B node5387 node5387Labels = _
    exact sound5387_e B hB hF
  have h5388 : mixedVector B (Sum.inr 5388) = Sparse.eval nodeValue5388 (mixedVector B) := by
    change mixedMoment B node5388 node5388Labels = _
    exact sound5388_e B hB hF
  have h5416 : mixedVector B (Sum.inr 5416) = Sparse.eval nodeValue5416 (mixedVector B) := by
    change mixedMoment B node5416 node5416Labels = _
    exact sound5416_e B hB hF
  have h5417 : mixedVector B (Sum.inr 5417) = Sparse.eval nodeValue5417 (mixedVector B) := by
    change mixedMoment B node5417 node5417Labels = _
    exact sound5417_e B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435_e B hB hF
  have h5440 : mixedVector B (Sum.inr 5440) = Sparse.eval nodeValue5440 (mixedVector B) := by
    change mixedMoment B node5440 node5440Labels = _
    exact sound5440 B hB hF
  have h5442 : mixedVector B (Sum.inr 5442) = Sparse.eval nodeValue5442 (mixedVector B) := by
    change mixedMoment B node5442 node5442Labels = _
    exact sound5442 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450_e B hB hF
  have h5454 : mixedVector B (Sum.inr 5454) = Sparse.eval nodeValue5454 (mixedVector B) := by
    change mixedMoment B node5454 node5454Labels = _
    exact sound5454 B hB hF
  have h5489 : mixedVector B (Sum.inr 5489) = Sparse.eval nodeValue5489 (mixedVector B) := by
    change mixedMoment B node5489 node5489Labels = _
    exact sound5489 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490_e B hB hF
  have h5493 : mixedVector B (Sum.inr 5493) = Sparse.eval nodeValue5493 (mixedVector B) := by
    change mixedMoment B node5493 node5493Labels = _
    exact sound5493 B hB hF
  simpa only [sourceForm1137, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4093, h5167, h5169, h5172, h5307, h5386, h5387, h5388, h5416, h5417, h5433, h5434, h5435, h5440, h5442, h5450, h5454, h5489, h5490, h5493, reducedSource989] using sourceEq1137 B hB

theorem rowSound989 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row989 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck989, numericCheck989, reducedZero989 B hB hF, mul_zero]

theorem sourceRowsAt976 : MixedData.sourceRows (976 : Fin 2425) =
    MixedData.row976 := by decide +kernel

theorem sourceRowsAt977 : MixedData.sourceRows (977 : Fin 2425) =
    MixedData.row977 := by decide +kernel

theorem sourceRowsAt978 : MixedData.sourceRows (978 : Fin 2425) =
    MixedData.row978 := by decide +kernel

theorem sourceRowsAt979 : MixedData.sourceRows (979 : Fin 2425) =
    MixedData.row979 := by decide +kernel

theorem sourceRowsAt980 : MixedData.sourceRows (980 : Fin 2425) =
    MixedData.row980 := by decide +kernel

theorem sourceRowsAt981 : MixedData.sourceRows (981 : Fin 2425) =
    MixedData.row981 := by decide +kernel

theorem sourceRowsAt982 : MixedData.sourceRows (982 : Fin 2425) =
    MixedData.row982 := by decide +kernel

theorem sourceRowsAt983 : MixedData.sourceRows (983 : Fin 2425) =
    MixedData.row983 := by decide +kernel

theorem sourceRowsAt984 : MixedData.sourceRows (984 : Fin 2425) =
    MixedData.row984 := by decide +kernel

theorem sourceRowsAt985 : MixedData.sourceRows (985 : Fin 2425) =
    MixedData.row985 := by decide +kernel

theorem sourceRowsAt986 : MixedData.sourceRows (986 : Fin 2425) =
    MixedData.row986 := by decide +kernel

theorem sourceRowsAt987 : MixedData.sourceRows (987 : Fin 2425) =
    MixedData.row987 := by decide +kernel

theorem sourceRowsAt988 : MixedData.sourceRows (988 : Fin 2425) =
    MixedData.row988 := by decide +kernel

theorem sourceRowsAt989 : MixedData.sourceRows (989 : Fin 2425) =
    MixedData.row989 := by decide +kernel

theorem sourceRowsAt990 : MixedData.sourceRows (990 : Fin 2425) =
    MixedData.row990 := by decide +kernel

theorem sourceRowsAt991 : MixedData.sourceRows (991 : Fin 2425) =
    MixedData.row991 := by decide +kernel

theorem chunkSound61_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 61) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 976 ∨ k.val = 977 ∨ k.val = 978 ∨ k.val = 979 ∨ k.val = 980 ∨ k.val = 981 ∨ k.val = 982 ∨ k.val = 983 ∨ k.val = 984 ∨ k.val = 985 ∨ k.val = 986 ∨ k.val = 987 ∨ k.val = 988 ∨ k.val = 989 ∨ k.val = 990 ∨ k.val = 991 := by omega
  rcases heq with h976 | h977 | h978 | h979 | h980 | h981 | h982 | h983 | h984 | h985 | h986 | h987 | h988 | h989 | h990 | h991
  · have he : k = (976 : Fin 2425) := Fin.ext h976
    subst k
    rw [sourceRowsAt976]
    exact rowSound976_e B hB hF
  · have he : k = (977 : Fin 2425) := Fin.ext h977
    subst k
    rw [sourceRowsAt977]
    exact rowSound977_e B hB hF
  · have he : k = (978 : Fin 2425) := Fin.ext h978
    subst k
    rw [sourceRowsAt978]
    exact rowSound978_e B hB hF
  · have he : k = (979 : Fin 2425) := Fin.ext h979
    subst k
    rw [sourceRowsAt979]
    exact rowSound979 B hB hF
  · have he : k = (980 : Fin 2425) := Fin.ext h980
    subst k
    rw [sourceRowsAt980]
    exact rowSound980_e B hB hF
  · have he : k = (981 : Fin 2425) := Fin.ext h981
    subst k
    rw [sourceRowsAt981]
    exact rowSound981_e B hB hF
  · have he : k = (982 : Fin 2425) := Fin.ext h982
    subst k
    rw [sourceRowsAt982]
    exact rowSound982_e B hB hF
  · have he : k = (983 : Fin 2425) := Fin.ext h983
    subst k
    rw [sourceRowsAt983]
    exact rowSound983_e B hB hF
  · have he : k = (984 : Fin 2425) := Fin.ext h984
    subst k
    rw [sourceRowsAt984]
    exact rowSound984_e B hB hF
  · have he : k = (985 : Fin 2425) := Fin.ext h985
    subst k
    rw [sourceRowsAt985]
    exact rowSound985 B hB hF
  · have he : k = (986 : Fin 2425) := Fin.ext h986
    subst k
    rw [sourceRowsAt986]
    exact rowSound986_e B hB hF
  · have he : k = (987 : Fin 2425) := Fin.ext h987
    subst k
    rw [sourceRowsAt987]
    exact rowSound987_e B hB hF
  · have he : k = (988 : Fin 2425) := Fin.ext h988
    subst k
    rw [sourceRowsAt988]
    exact rowSound988_e B hB hF
  · have he : k = (989 : Fin 2425) := Fin.ext h989
    subst k
    rw [sourceRowsAt989]
    exact rowSound989 B hB hF
  · have he : k = (990 : Fin 2425) := Fin.ext h990
    subst k
    rw [sourceRowsAt990]
    exact rowSound990_e B hB hF
  · have he : k = (991 : Fin 2425) := Fin.ext h991
    subst k
    rw [sourceRowsAt991]
    exact rowSound991_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e_oai
