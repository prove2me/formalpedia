-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:23:46.572706+00:00
-- url     : https://prove2.me/submissions/4e53b83d-8c21-4218-907c-cef0b2064299

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3852_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3853_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3981_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3982_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3990_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound4032_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5483_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound912_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound913_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound916_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound917_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound918_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound919_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound920_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound922_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound923_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound924_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound925_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound926_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound927_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16843 raw16843Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw16843 raw16843Labels = mixedMoment B raw16843step0 raw16843step0Labels := by
      have hz : ∀ j, raw16843 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16843step0 = (fun i j => raw16843 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16843step0 raw16843; decide +kernel
      have hl : raw16843step0Labels = raw16843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16843 raw16843Labels permutation434 hz
    mixedMoment B raw16843step0 raw16843step0Labels = mixedMoment B raw16843step1 raw16843step1Labels := by
      have ha : raw16843step1 = (fun i j => raw16843step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16843step1 raw16843step0; decide +kernel
      have hl : raw16843step1Labels = raw16843step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16843step0 raw16843step0Labels permutation32 permutation6
    mixedMoment B raw16843step1 raw16843step1Labels = mixedMoment B raw16843step2 raw16843step2Labels := by
      have ha : raw16843step2 = raw16843step1 := by apply Matrix.ext; unfold raw16843step2 raw16843step1; decide +kernel
      have hl : raw16843step1Labels = labelEmbedding9 ∘ raw16843step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16843step1 raw16843step1Labels raw16843step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5483 node5483Labels := by rfl

theorem canonical16857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16857 raw16857Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw16857 raw16857Labels = mixedMoment B raw16857step0 raw16857step0Labels := by
      have hz : ∀ j, raw16857 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16857step0 = (fun i j => raw16857 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16857step0 raw16857; decide +kernel
      have hl : raw16857step0Labels = raw16857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16857 raw16857Labels permutation434 hz
    mixedMoment B raw16857step0 raw16857step0Labels = mixedMoment B raw16857step1 raw16857step1Labels := by
      have ha : raw16857step1 = (fun i j => raw16857step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16857step1 raw16857step0; decide +kernel
      have hl : raw16857step1Labels = raw16857step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16857step0 raw16857step0Labels permutation32 permutation6
    mixedMoment B raw16857step1 raw16857step1Labels = mixedMoment B raw16857step2 raw16857step2Labels := by
      have ha : raw16857step2 = raw16857step1 := by apply Matrix.ext; unfold raw16857step2 raw16857step1; decide +kernel
      have hl : raw16857step1Labels = labelEmbedding9 ∘ raw16857step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16857step1 raw16857step1Labels raw16857step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical16870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16870 raw16870Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw16870 raw16870Labels = mixedMoment B raw16870step0 raw16870step0Labels := by
      have hz : ∀ j, raw16870 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16870step0 = (fun i j => raw16870 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16870step0 raw16870; decide +kernel
      have hl : raw16870step0Labels = raw16870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16870 raw16870Labels permutation434 hz
    mixedMoment B raw16870step0 raw16870step0Labels = mixedMoment B raw16870step1 raw16870step1Labels := by
      have ha : raw16870step1 = (fun i j => raw16870step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16870step1 raw16870step0; decide +kernel
      have hl : raw16870step1Labels = raw16870step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16870step0 raw16870step0Labels permutation32 permutation6
    _ = mixedMoment B node3981 node3981Labels := by rfl

theorem canonical16884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16884 raw16884Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw16884 raw16884Labels = mixedMoment B raw16884step0 raw16884step0Labels := by
      have hz : ∀ j, raw16884 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16884step0 = (fun i j => raw16884 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16884step0 raw16884; decide +kernel
      have hl : raw16884step0Labels = raw16884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16884 raw16884Labels permutation434 hz
    mixedMoment B raw16884step0 raw16884step0Labels = mixedMoment B raw16884step1 raw16884step1Labels := by
      have ha : raw16884step1 = (fun i j => raw16884step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16884step1 raw16884step0; decide +kernel
      have hl : raw16884step1Labels = raw16884step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16884step0 raw16884step0Labels permutation32 permutation6
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical16889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16889 raw16889Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw16889 raw16889Labels = mixedMoment B raw16889step0 raw16889step0Labels := by
      have hz : ∀ j, raw16889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16889step0 = (fun i j => raw16889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16889step0 raw16889; decide +kernel
      have hl : raw16889step0Labels = raw16889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16889 raw16889Labels permutation434 hz
    mixedMoment B raw16889step0 raw16889step0Labels = mixedMoment B raw16889step1 raw16889step1Labels := by
      have ha : raw16889step1 = (fun i j => raw16889step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16889step1 raw16889step0; decide +kernel
      have hl : raw16889step1Labels = raw16889step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16889step0 raw16889step0Labels permutation151 permutation6
    mixedMoment B raw16889step1 raw16889step1Labels = mixedMoment B raw16889step2 raw16889step2Labels := by
      have ha : raw16889step2 = -raw16889step1 := by apply Matrix.ext; change ∀ i j, raw16889step2 i j = -(raw16889step1 i j); unfold raw16889step2 raw16889step1; decide +kernel
      have hl : raw16889step2Labels = raw16889step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3845 node3845Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17125 raw17125Labels = mixedMoment B node5487 node5487Labels := by
  calc
    mixedMoment B raw17125 raw17125Labels = mixedMoment B raw17125step0 raw17125step0Labels := by
      have hz : ∀ j, raw17125 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17125step0 = (fun i j => raw17125 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17125step0 raw17125; decide +kernel
      have hl : raw17125step0Labels = raw17125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17125 raw17125Labels permutation434 hz
    mixedMoment B raw17125step0 raw17125step0Labels = mixedMoment B raw17125step1 raw17125step1Labels := by
      have hz : ∀ j, raw17125step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17125step1 = (fun i j => raw17125step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17125step1 raw17125step0; decide +kernel
      have hl : raw17125step1Labels = raw17125step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17125step0 raw17125step0Labels permutation80 hz
    mixedMoment B raw17125step1 raw17125step1Labels = mixedMoment B raw17125step2 raw17125step2Labels := by
      have ha : raw17125step2 = (fun i j => raw17125step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17125step2 raw17125step1; decide +kernel
      have hl : raw17125step2Labels = raw17125step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17125step1 raw17125step1Labels permutation8 permutation6
    mixedMoment B raw17125step2 raw17125step2Labels = mixedMoment B raw17125step3 raw17125step3Labels := by
      have ha : raw17125step3 = raw17125step2 := by apply Matrix.ext; unfold raw17125step3 raw17125step2; decide +kernel
      have hl : raw17125step2Labels = labelEmbedding9 ∘ raw17125step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17125step2 raw17125step2Labels raw17125step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5487 node5487Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17231 raw17231Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw17231 raw17231Labels = mixedMoment B raw17231step0 raw17231step0Labels := by
      have hz : ∀ j, raw17231 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17231step0 = (fun i j => raw17231 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17231step0 raw17231; decide +kernel
      have hl : raw17231step0Labels = raw17231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17231 raw17231Labels permutation434 hz
    mixedMoment B raw17231step0 raw17231step0Labels = mixedMoment B raw17231step1 raw17231step1Labels := by
      have ha : raw17231step1 = (fun i j => raw17231step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17231step1 raw17231step0; decide +kernel
      have hl : raw17231step1Labels = raw17231step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17231step0 raw17231step0Labels permutation151 permutation7
    mixedMoment B raw17231step1 raw17231step1Labels = mixedMoment B raw17231step2 raw17231step2Labels := by
      have ha : raw17231step2 = -raw17231step1 := by apply Matrix.ext; change ∀ i j, raw17231step2 i j = -(raw17231step1 i j); unfold raw17231step2 raw17231step1; decide +kernel
      have hl : raw17231step2Labels = raw17231step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17231step2 raw17231step2Labels = mixedMoment B raw17231step3 raw17231step3Labels := by
      have ha : raw17231step3 = raw17231step2 := by apply Matrix.ext; unfold raw17231step3 raw17231step2; decide +kernel
      have hl : raw17231step2Labels = labelEmbedding10 ∘ raw17231step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17231step2 raw17231step2Labels raw17231step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17389 raw17389Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17389 raw17389Labels = mixedMoment B raw17389step0 raw17389step0Labels := by
      have ha : raw17389step0 = (fun i j => raw17389 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17389step0 raw17389; decide +kernel
      have hl : raw17389step0Labels = raw17389Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17389 raw17389Labels permutation682 permutation6
    mixedMoment B raw17389step0 raw17389step0Labels = mixedMoment B raw17389step1 raw17389step1Labels := by
      have ha : raw17389step1 = -raw17389step0 := by apply Matrix.ext; change ∀ i j, raw17389step1 i j = -(raw17389step0 i j); unfold raw17389step1 raw17389step0; decide +kernel
      have hl : raw17389step1Labels = raw17389step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17389step1 raw17389step1Labels = mixedMoment B raw17389step2 raw17389step2Labels := by
      have ha : raw17389step2 = raw17389step1 := by apply Matrix.ext; unfold raw17389step2 raw17389step1; decide +kernel
      have hl : raw17389step1Labels = labelEmbedding9 ∘ raw17389step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17389step1 raw17389step1Labels raw17389step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical17397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17397 raw17397Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw17397 raw17397Labels = mixedMoment B raw17397step0 raw17397step0Labels := by
      have ha : raw17397step0 = (fun i j => raw17397 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17397step0 raw17397; decide +kernel
      have hl : raw17397step0Labels = raw17397Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17397 raw17397Labels permutation682 permutation6
    mixedMoment B raw17397step0 raw17397step0Labels = mixedMoment B raw17397step1 raw17397step1Labels := by
      have ha : raw17397step1 = -raw17397step0 := by apply Matrix.ext; change ∀ i j, raw17397step1 i j = -(raw17397step0 i j); unfold raw17397step1 raw17397step0; decide +kernel
      have hl : raw17397step1Labels = raw17397step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3872 node3872Labels := by rfl

theorem canonical17401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17401 raw17401Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw17401 raw17401Labels = mixedMoment B raw17401step0 raw17401step0Labels := by
      have ha : raw17401step0 = (fun i j => raw17401 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17401step0 raw17401; decide +kernel
      have hl : raw17401step0Labels = raw17401Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17401 raw17401Labels permutation682 permutation6
    mixedMoment B raw17401step0 raw17401step0Labels = mixedMoment B raw17401step1 raw17401step1Labels := by
      have ha : raw17401step1 = -raw17401step0 := by apply Matrix.ext; change ∀ i j, raw17401step1 i j = -(raw17401step0 i j); unfold raw17401step1 raw17401step0; decide +kernel
      have hl : raw17401step1Labels = raw17401step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3871 node3871Labels := by rfl

theorem canonical17405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17405 raw17405Labels = mixedMoment B node3866 node3866Labels := by
  calc
    mixedMoment B raw17405 raw17405Labels = mixedMoment B raw17405step0 raw17405step0Labels := by
      have ha : raw17405step0 = (fun i j => raw17405 (permutation361 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17405step0 raw17405; decide +kernel
      have hl : raw17405step0Labels = raw17405Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17405 raw17405Labels permutation361 permutation3
    mixedMoment B raw17405step0 raw17405step0Labels = mixedMoment B raw17405step1 raw17405step1Labels := by
      have ha : raw17405step1 = -raw17405step0 := by apply Matrix.ext; change ∀ i j, raw17405step1 i j = -(raw17405step0 i j); unfold raw17405step1 raw17405step0; decide +kernel
      have hl : raw17405step1Labels = raw17405step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3866 node3866Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical136
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17410 raw17410Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw17410 raw17410Labels = mixedMoment B raw17410step0 raw17410step0Labels := by
      have hz : ∀ j, raw17410 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17410step0 = (fun i j => raw17410 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17410step0 raw17410; decide +kernel
      have hl : raw17410step0Labels = raw17410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17410 raw17410Labels permutation434 hz
    mixedMoment B raw17410step0 raw17410step0Labels = mixedMoment B raw17410step1 raw17410step1Labels := by
      have ha : raw17410step1 = (fun i j => raw17410step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17410step1 raw17410step0; decide +kernel
      have hl : raw17410step1Labels = raw17410step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17410step0 raw17410step0Labels permutation32 permutation6
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical17411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17411 raw17411Labels = mixedMoment B node3861 node3861Labels := by
  calc
    mixedMoment B raw17411 raw17411Labels = mixedMoment B raw17411step0 raw17411step0Labels := by
      have hz : ∀ j, raw17411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17411step0 = (fun i j => raw17411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17411step0 raw17411; decide +kernel
      have hl : raw17411step0Labels = raw17411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17411 raw17411Labels permutation434 hz
    mixedMoment B raw17411step0 raw17411step0Labels = mixedMoment B raw17411step1 raw17411step1Labels := by
      have hz : ∀ j, raw17411step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17411step1 = (fun i j => raw17411step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17411step1 raw17411step0; decide +kernel
      have hl : raw17411step1Labels = raw17411step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17411step0 raw17411step0Labels permutation80 hz
    mixedMoment B raw17411step1 raw17411step1Labels = mixedMoment B raw17411step2 raw17411step2Labels := by
      have ha : raw17411step2 = (fun i j => raw17411step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17411step2 raw17411step1; decide +kernel
      have hl : raw17411step2Labels = raw17411step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17411step1 raw17411step1Labels permutation31 permutation6
    mixedMoment B raw17411step2 raw17411step2Labels = mixedMoment B raw17411step3 raw17411step3Labels := by
      have ha : raw17411step3 = -raw17411step2 := by apply Matrix.ext; change ∀ i j, raw17411step3 i j = -(raw17411step2 i j); unfold raw17411step3 raw17411step2; decide +kernel
      have hl : raw17411step3Labels = raw17411step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3861 node3861Labels := by rfl

theorem canonical17412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17412 raw17412Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw17412 raw17412Labels = mixedMoment B raw17412step0 raw17412step0Labels := by
      have ha : raw17412step0 = (fun i j => raw17412 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17412step0 raw17412; decide +kernel
      have hl : raw17412step0Labels = raw17412Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17412 raw17412Labels permutation682 permutation6
    mixedMoment B raw17412step0 raw17412step0Labels = mixedMoment B raw17412step1 raw17412step1Labels := by
      have ha : raw17412step1 = -raw17412step0 := by apply Matrix.ext; change ∀ i j, raw17412step1 i j = -(raw17412step0 i j); unfold raw17412step1 raw17412step0; decide +kernel
      have hl : raw17412step1Labels = raw17412step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical17416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17416 raw17416Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw17416 raw17416Labels = mixedMoment B raw17416step0 raw17416step0Labels := by
      have ha : raw17416step0 = (fun i j => raw17416 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17416step0 raw17416; decide +kernel
      have hl : raw17416step0Labels = raw17416Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17416 raw17416Labels permutation682 permutation6
    mixedMoment B raw17416step0 raw17416step0Labels = mixedMoment B raw17416step1 raw17416step1Labels := by
      have ha : raw17416step1 = -raw17416step0 := by apply Matrix.ext; change ∀ i j, raw17416step1 i j = -(raw17416step0 i j); unfold raw17416step1 raw17416step0; decide +kernel
      have hl : raw17416step1Labels = raw17416step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3558 node3558Labels := by rfl

theorem canonical17469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17469 raw17469Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw17469 raw17469Labels = mixedMoment B raw17469step0 raw17469step0Labels := by
      have ha : raw17469step0 = (fun i j => raw17469 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17469step0 raw17469; decide +kernel
      have hl : raw17469step0Labels = raw17469Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17469 raw17469Labels permutation188 permutation2
    mixedMoment B raw17469step0 raw17469step0Labels = mixedMoment B raw17469step1 raw17469step1Labels := by
      have ha : raw17469step1 = -raw17469step0 := by apply Matrix.ext; change ∀ i j, raw17469step1 i j = -(raw17469step0 i j); unfold raw17469step1 raw17469step0; decide +kernel
      have hl : raw17469step1Labels = raw17469step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical17470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17470 raw17470Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw17470 raw17470Labels = mixedMoment B raw17470step0 raw17470step0Labels := by
      have hz : ∀ j, raw17470 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17470step0 = (fun i j => raw17470 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17470step0 raw17470; decide +kernel
      have hl : raw17470step0Labels = raw17470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17470 raw17470Labels permutation346 hz
    mixedMoment B raw17470step0 raw17470step0Labels = mixedMoment B raw17470step1 raw17470step1Labels := by
      have ha : raw17470step1 = (fun i j => raw17470step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17470step1 raw17470step0; decide +kernel
      have hl : raw17470step1Labels = raw17470step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17470step0 raw17470step0Labels permutation32 permutation7
    mixedMoment B raw17470step1 raw17470step1Labels = mixedMoment B raw17470step2 raw17470step2Labels := by
      have ha : raw17470step2 = raw17470step1 := by apply Matrix.ext; unfold raw17470step2 raw17470step1; decide +kernel
      have hl : raw17470step1Labels = labelEmbedding10 ∘ raw17470step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17470step1 raw17470step1Labels raw17470step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical17471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17471 raw17471Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw17471 raw17471Labels = mixedMoment B raw17471step0 raw17471step0Labels := by
      have ha : raw17471step0 = (fun i j => raw17471 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17471step0 raw17471; decide +kernel
      have hl : raw17471step0Labels = raw17471Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17471 raw17471Labels permutation179 permutation2
    mixedMoment B raw17471step0 raw17471step0Labels = mixedMoment B raw17471step1 raw17471step1Labels := by
      have ha : raw17471step1 = -raw17471step0 := by apply Matrix.ext; change ∀ i j, raw17471step1 i j = -(raw17471step0 i j); unfold raw17471step1 raw17471step0; decide +kernel
      have hl : raw17471step1Labels = raw17471step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical17472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17472 raw17472Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17472 raw17472Labels = mixedMoment B raw17472step0 raw17472step0Labels := by
      have ha : raw17472step0 = (fun i j => raw17472 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17472step0 raw17472; decide +kernel
      have hl : raw17472step0Labels = raw17472Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17472 raw17472Labels permutation152 permutation7
    mixedMoment B raw17472step0 raw17472step0Labels = mixedMoment B raw17472step1 raw17472step1Labels := by
      have ha : raw17472step1 = raw17472step0 := by apply Matrix.ext; unfold raw17472step1 raw17472step0; decide +kernel
      have hl : raw17472step0Labels = labelEmbedding10 ∘ raw17472step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17472step0 raw17472step0Labels raw17472step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical17473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17473 raw17473Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw17473 raw17473Labels = mixedMoment B raw17473step0 raw17473step0Labels := by
      have ha : raw17473step0 = (fun i j => raw17473 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17473step0 raw17473; decide +kernel
      have hl : raw17473step0Labels = raw17473Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17473 raw17473Labels permutation662 permutation2
    _ = mixedMoment B node5423 node5423Labels := by rfl

theorem canonical17474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17474 raw17474Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17474 raw17474Labels = mixedMoment B raw17474step0 raw17474step0Labels := by
      have ha : raw17474step0 = (fun i j => raw17474 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17474step0 raw17474; decide +kernel
      have hl : raw17474step0Labels = raw17474Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17474 raw17474Labels permutation158 permutation6
    mixedMoment B raw17474step0 raw17474step0Labels = mixedMoment B raw17474step1 raw17474step1Labels := by
      have ha : raw17474step1 = raw17474step0 := by apply Matrix.ext; unfold raw17474step1 raw17474step0; decide +kernel
      have hl : raw17474step0Labels = labelEmbedding9 ∘ raw17474step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17474step0 raw17474step0Labels raw17474step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical17475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17475 raw17475Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw17475 raw17475Labels = mixedMoment B raw17475step0 raw17475step0Labels := by
      have hz : ∀ j, raw17475 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17475step0 = (fun i j => raw17475 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17475step0 raw17475; decide +kernel
      have hl : raw17475step0Labels = raw17475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17475 raw17475Labels permutation346 hz
    mixedMoment B raw17475step0 raw17475step0Labels = mixedMoment B raw17475step1 raw17475step1Labels := by
      have ha : raw17475step1 = (fun i j => raw17475step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17475step1 raw17475step0; decide +kernel
      have hl : raw17475step1Labels = raw17475step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17475step0 raw17475step0Labels permutation151 permutation6
    mixedMoment B raw17475step1 raw17475step1Labels = mixedMoment B raw17475step2 raw17475step2Labels := by
      have ha : raw17475step2 = -raw17475step1 := by apply Matrix.ext; change ∀ i j, raw17475step2 i j = -(raw17475step1 i j); unfold raw17475step2 raw17475step1; decide +kernel
      have hl : raw17475step2Labels = raw17475step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17475step2 raw17475step2Labels = mixedMoment B raw17475step3 raw17475step3Labels := by
      have ha : raw17475step3 = raw17475step2 := by apply Matrix.ext; unfold raw17475step3 raw17475step2; decide +kernel
      have hl : raw17475step2Labels = labelEmbedding9 ∘ raw17475step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17475step2 raw17475step2Labels raw17475step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5483 node5483Labels := by rfl

theorem canonical17476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17476 raw17476Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw17476 raw17476Labels = mixedMoment B raw17476step0 raw17476step0Labels := by
      have ha : raw17476step0 = (fun i j => raw17476 (permutation514 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17476step0 raw17476; decide +kernel
      have hl : raw17476step0Labels = raw17476Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17476 raw17476Labels permutation514 permutation3
    mixedMoment B raw17476step0 raw17476step0Labels = mixedMoment B raw17476step1 raw17476step1Labels := by
      have ha : raw17476step1 = raw17476step0 := by apply Matrix.ext; unfold raw17476step1 raw17476step0; decide +kernel
      have hl : raw17476step0Labels = labelEmbedding6 ∘ raw17476step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17476step0 raw17476step0Labels raw17476step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical17477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17477 raw17477Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw17477 raw17477Labels = mixedMoment B raw17477step0 raw17477step0Labels := by
      have ha : raw17477step0 = (fun i j => raw17477 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17477step0 raw17477; decide +kernel
      have hl : raw17477step0Labels = raw17477Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17477 raw17477Labels permutation152 permutation7
    mixedMoment B raw17477step0 raw17477step0Labels = mixedMoment B raw17477step1 raw17477step1Labels := by
      have ha : raw17477step1 = raw17477step0 := by apply Matrix.ext; unfold raw17477step1 raw17477step0; decide +kernel
      have hl : raw17477step0Labels = labelEmbedding10 ∘ raw17477step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17477step0 raw17477step0Labels raw17477step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

theorem canonical17478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17478 raw17478Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17478 raw17478Labels = mixedMoment B raw17478step0 raw17478step0Labels := by
      have ha : raw17478step0 = (fun i j => raw17478 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17478step0 raw17478; decide +kernel
      have hl : raw17478step0Labels = raw17478Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17478 raw17478Labels permutation688 permutation7
    mixedMoment B raw17478step0 raw17478step0Labels = mixedMoment B raw17478step1 raw17478step1Labels := by
      have ha : raw17478step1 = -raw17478step0 := by apply Matrix.ext; change ∀ i j, raw17478step1 i j = -(raw17478step0 i j); unfold raw17478step1 raw17478step0; decide +kernel
      have hl : raw17478step1Labels = raw17478step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17478step1 raw17478step1Labels = mixedMoment B raw17478step2 raw17478step2Labels := by
      have ha : raw17478step2 = raw17478step1 := by apply Matrix.ext; unfold raw17478step2 raw17478step1; decide +kernel
      have hl : raw17478step1Labels = labelEmbedding10 ∘ raw17478step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17478step1 raw17478step1Labels raw17478step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical17479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17479 raw17479Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw17479 raw17479Labels = mixedMoment B raw17479step0 raw17479step0Labels := by
      have ha : raw17479step0 = (fun i j => raw17479 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17479step0 raw17479; decide +kernel
      have hl : raw17479step0Labels = raw17479Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17479 raw17479Labels permutation161 permutation4
    mixedMoment B raw17479step0 raw17479step0Labels = mixedMoment B raw17479step1 raw17479step1Labels := by
      have ha : raw17479step1 = -raw17479step0 := by apply Matrix.ext; change ∀ i j, raw17479step1 i j = -(raw17479step0 i j); unfold raw17479step1 raw17479step0; decide +kernel
      have hl : raw17479step1Labels = raw17479step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17479step1 raw17479step1Labels = mixedMoment B raw17479step2 raw17479step2Labels := by
      have ha : raw17479step2 = raw17479step1 := by apply Matrix.ext; unfold raw17479step2 raw17479step1; decide +kernel
      have hl : raw17479step1Labels = labelEmbedding7 ∘ raw17479step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17479step1 raw17479step1Labels raw17479step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

theorem canonical17480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17480 raw17480Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw17480 raw17480Labels = mixedMoment B raw17480step0 raw17480step0Labels := by
      have ha : raw17480step0 = (fun i j => raw17480 (permutation410 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17480step0 raw17480; decide +kernel
      have hl : raw17480step0Labels = raw17480Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17480 raw17480Labels permutation410 permutation5
    mixedMoment B raw17480step0 raw17480step0Labels = mixedMoment B raw17480step1 raw17480step1Labels := by
      have ha : raw17480step1 = raw17480step0 := by apply Matrix.ext; unfold raw17480step1 raw17480step0; decide +kernel
      have hl : raw17480step0Labels = labelEmbedding8 ∘ raw17480step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17480step0 raw17480step0Labels raw17480step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

theorem canonical17481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17481 raw17481Labels = mixedMoment B node5420 node5420Labels := by
  calc
    mixedMoment B raw17481 raw17481Labels = mixedMoment B raw17481step0 raw17481step0Labels := by
      have ha : raw17481step0 = (fun i j => raw17481 (permutation409 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17481step0 raw17481; decide +kernel
      have hl : raw17481step0Labels = raw17481Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17481 raw17481Labels permutation409 permutation5
    mixedMoment B raw17481step0 raw17481step0Labels = mixedMoment B raw17481step1 raw17481step1Labels := by
      have ha : raw17481step1 = raw17481step0 := by apply Matrix.ext; unfold raw17481step1 raw17481step0; decide +kernel
      have hl : raw17481step0Labels = labelEmbedding8 ∘ raw17481step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17481step0 raw17481step0Labels raw17481step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5420 node5420Labels := by rfl

theorem canonical17482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17482 raw17482Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw17482 raw17482Labels = mixedMoment B raw17482step0 raw17482step0Labels := by
      have ha : raw17482step0 = (fun i j => raw17482 (permutation351 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17482step0 raw17482; decide +kernel
      have hl : raw17482step0Labels = raw17482Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17482 raw17482Labels permutation351 permutation3
    mixedMoment B raw17482step0 raw17482step0Labels = mixedMoment B raw17482step1 raw17482step1Labels := by
      have ha : raw17482step1 = -raw17482step0 := by apply Matrix.ext; change ∀ i j, raw17482step1 i j = -(raw17482step0 i j); unfold raw17482step1 raw17482step0; decide +kernel
      have hl : raw17482step1Labels = raw17482step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17482step1 raw17482step1Labels = mixedMoment B raw17482step2 raw17482step2Labels := by
      have ha : raw17482step2 = raw17482step1 := by apply Matrix.ext; unfold raw17482step2 raw17482step1; decide +kernel
      have hl : raw17482step1Labels = labelEmbedding6 ∘ raw17482step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17482step1 raw17482step1Labels raw17482step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical17483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17483 raw17483Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw17483 raw17483Labels = mixedMoment B raw17483step0 raw17483step0Labels := by
      have ha : raw17483step0 = (fun i j => raw17483 (permutation661 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17483step0 raw17483; decide +kernel
      have hl : raw17483step0Labels = raw17483Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17483 raw17483Labels permutation661 permutation2
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical17484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17484 raw17484Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw17484 raw17484Labels = mixedMoment B raw17484step0 raw17484step0Labels := by
      have hz : ∀ j, raw17484 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17484step0 = (fun i j => raw17484 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17484step0 raw17484; decide +kernel
      have hl : raw17484step0Labels = raw17484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17484 raw17484Labels permutation434 hz
    mixedMoment B raw17484step0 raw17484step0Labels = mixedMoment B raw17484step1 raw17484step1Labels := by
      have ha : raw17484step1 = (fun i j => raw17484step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17484step1 raw17484step0; decide +kernel
      have hl : raw17484step1Labels = raw17484step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17484step0 raw17484step0Labels permutation32 permutation6
    mixedMoment B raw17484step1 raw17484step1Labels = mixedMoment B raw17484step2 raw17484step2Labels := by
      have ha : raw17484step2 = raw17484step1 := by apply Matrix.ext; unfold raw17484step2 raw17484step1; decide +kernel
      have hl : raw17484step1Labels = labelEmbedding9 ∘ raw17484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17484step1 raw17484step1Labels raw17484step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical17485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17485 raw17485Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw17485 raw17485Labels = mixedMoment B raw17485step0 raw17485step0Labels := by
      have ha : raw17485step0 = (fun i j => raw17485 (permutation159 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17485step0 raw17485; decide +kernel
      have hl : raw17485step0Labels = raw17485Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17485 raw17485Labels permutation159 permutation4
    mixedMoment B raw17485step0 raw17485step0Labels = mixedMoment B raw17485step1 raw17485step1Labels := by
      have ha : raw17485step1 = -raw17485step0 := by apply Matrix.ext; change ∀ i j, raw17485step1 i j = -(raw17485step0 i j); unfold raw17485step1 raw17485step0; decide +kernel
      have hl : raw17485step1Labels = raw17485step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17485step1 raw17485step1Labels = mixedMoment B raw17485step2 raw17485step2Labels := by
      have ha : raw17485step2 = raw17485step1 := by apply Matrix.ext; unfold raw17485step2 raw17485step1; decide +kernel
      have hl : raw17485step1Labels = labelEmbedding7 ∘ raw17485step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17485step1 raw17485step1Labels raw17485step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical17486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17486 raw17486Labels = mixedMoment B node5468 node5468Labels := by
  calc
    mixedMoment B raw17486 raw17486Labels = mixedMoment B raw17486step0 raw17486step0Labels := by
      have ha : raw17486step0 = (fun i j => raw17486 (permutation583 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17486step0 raw17486; decide +kernel
      have hl : raw17486step0Labels = raw17486Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17486 raw17486Labels permutation583 permutation4
    mixedMoment B raw17486step0 raw17486step0Labels = mixedMoment B raw17486step1 raw17486step1Labels := by
      have ha : raw17486step1 = raw17486step0 := by apply Matrix.ext; unfold raw17486step1 raw17486step0; decide +kernel
      have hl : raw17486step0Labels = labelEmbedding7 ∘ raw17486step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17486step0 raw17486step0Labels raw17486step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5468 node5468Labels := by rfl

theorem canonical17487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17487 raw17487Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17487 raw17487Labels = mixedMoment B raw17487step0 raw17487step0Labels := by
      have hz : ∀ j, raw17487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17487step0 = (fun i j => raw17487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17487step0 raw17487; decide +kernel
      have hl : raw17487step0Labels = raw17487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17487 raw17487Labels permutation346 hz
    mixedMoment B raw17487step0 raw17487step0Labels = mixedMoment B raw17487step1 raw17487step1Labels := by
      have ha : raw17487step1 = (fun i j => raw17487step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17487step1 raw17487step0; decide +kernel
      have hl : raw17487step1Labels = raw17487step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17487step0 raw17487step0Labels permutation151 permutation6
    mixedMoment B raw17487step1 raw17487step1Labels = mixedMoment B raw17487step2 raw17487step2Labels := by
      have ha : raw17487step2 = -raw17487step1 := by apply Matrix.ext; change ∀ i j, raw17487step2 i j = -(raw17487step1 i j); unfold raw17487step2 raw17487step1; decide +kernel
      have hl : raw17487step2Labels = raw17487step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17487step2 raw17487step2Labels = mixedMoment B raw17487step3 raw17487step3Labels := by
      have ha : raw17487step3 = raw17487step2 := by apply Matrix.ext; unfold raw17487step3 raw17487step2; decide +kernel
      have hl : raw17487step2Labels = labelEmbedding9 ∘ raw17487step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17487step2 raw17487step2Labels raw17487step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical17488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17488 raw17488Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw17488 raw17488Labels = mixedMoment B raw17488step0 raw17488step0Labels := by
      have ha : raw17488step0 = (fun i j => raw17488 (permutation455 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17488step0 raw17488; decide +kernel
      have hl : raw17488step0Labels = raw17488Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17488 raw17488Labels permutation455 permutation5
    mixedMoment B raw17488step0 raw17488step0Labels = mixedMoment B raw17488step1 raw17488step1Labels := by
      have ha : raw17488step1 = -raw17488step0 := by apply Matrix.ext; change ∀ i j, raw17488step1 i j = -(raw17488step0 i j); unfold raw17488step1 raw17488step0; decide +kernel
      have hl : raw17488step1Labels = raw17488step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17488step1 raw17488step1Labels = mixedMoment B raw17488step2 raw17488step2Labels := by
      have ha : raw17488step2 = raw17488step1 := by apply Matrix.ext; unfold raw17488step2 raw17488step1; decide +kernel
      have hl : raw17488step1Labels = labelEmbedding8 ∘ raw17488step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17488step1 raw17488step1Labels raw17488step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

theorem canonical17489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17489 raw17489Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw17489 raw17489Labels = mixedMoment B raw17489step0 raw17489step0Labels := by
      have ha : raw17489step0 = (fun i j => raw17489 (permutation654 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17489step0 raw17489; decide +kernel
      have hl : raw17489step0Labels = raw17489Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17489 raw17489Labels permutation654 permutation2
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical17490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17490 raw17490Labels = mixedMoment B node5394 node5394Labels := by
  calc
    mixedMoment B raw17490 raw17490Labels = mixedMoment B raw17490step0 raw17490step0Labels := by
      have ha : raw17490step0 = (fun i j => raw17490 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17490step0 raw17490; decide +kernel
      have hl : raw17490step0Labels = raw17490Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17490 raw17490Labels permutation682 permutation4
    mixedMoment B raw17490step0 raw17490step0Labels = mixedMoment B raw17490step1 raw17490step1Labels := by
      have ha : raw17490step1 = raw17490step0 := by apply Matrix.ext; unfold raw17490step1 raw17490step0; decide +kernel
      have hl : raw17490step0Labels = labelEmbedding7 ∘ raw17490step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17490step0 raw17490step0Labels raw17490step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5394 node5394Labels := by rfl

theorem canonical17491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17491 raw17491Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw17491 raw17491Labels = mixedMoment B raw17491step0 raw17491step0Labels := by
      have ha : raw17491step0 = (fun i j => raw17491 (permutation681 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17491step0 raw17491; decide +kernel
      have hl : raw17491step0Labels = raw17491Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17491 raw17491Labels permutation681 permutation4
    mixedMoment B raw17491step0 raw17491step0Labels = mixedMoment B raw17491step1 raw17491step1Labels := by
      have ha : raw17491step1 = raw17491step0 := by apply Matrix.ext; unfold raw17491step1 raw17491step0; decide +kernel
      have hl : raw17491step0Labels = labelEmbedding7 ∘ raw17491step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17491step0 raw17491step0Labels raw17491step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical17492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17492 raw17492Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw17492 raw17492Labels = mixedMoment B raw17492step0 raw17492step0Labels := by
      have hz : ∀ j, raw17492 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17492step0 = (fun i j => raw17492 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17492step0 raw17492; decide +kernel
      have hl : raw17492step0Labels = raw17492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17492 raw17492Labels permutation346 hz
    mixedMoment B raw17492step0 raw17492step0Labels = mixedMoment B raw17492step1 raw17492step1Labels := by
      have ha : raw17492step1 = (fun i j => raw17492step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17492step1 raw17492step0; decide +kernel
      have hl : raw17492step1Labels = raw17492step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17492step0 raw17492step0Labels permutation151 permutation6
    mixedMoment B raw17492step1 raw17492step1Labels = mixedMoment B raw17492step2 raw17492step2Labels := by
      have ha : raw17492step2 = -raw17492step1 := by apply Matrix.ext; change ∀ i j, raw17492step2 i j = -(raw17492step1 i j); unfold raw17492step2 raw17492step1; decide +kernel
      have hl : raw17492step2Labels = raw17492step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17492step2 raw17492step2Labels = mixedMoment B raw17492step3 raw17492step3Labels := by
      have ha : raw17492step3 = raw17492step2 := by apply Matrix.ext; unfold raw17492step3 raw17492step2; decide +kernel
      have hl : raw17492step2Labels = labelEmbedding9 ∘ raw17492step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17492step2 raw17492step2Labels raw17492step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical17493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17493 raw17493Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw17493 raw17493Labels = mixedMoment B raw17493step0 raw17493step0Labels := by
      have ha : raw17493step0 = (fun i j => raw17493 (permutation679 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17493step0 raw17493; decide +kernel
      have hl : raw17493step0Labels = raw17493Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17493 raw17493Labels permutation679 permutation4
    mixedMoment B raw17493step0 raw17493step0Labels = mixedMoment B raw17493step1 raw17493step1Labels := by
      have ha : raw17493step1 = raw17493step0 := by apply Matrix.ext; unfold raw17493step1 raw17493step0; decide +kernel
      have hl : raw17493step0Labels = labelEmbedding7 ∘ raw17493step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17493step0 raw17493step0Labels raw17493step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

theorem canonical17494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17494 raw17494Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw17494 raw17494Labels = mixedMoment B raw17494step0 raw17494step0Labels := by
      have ha : raw17494step0 = (fun i j => raw17494 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17494step0 raw17494; decide +kernel
      have hl : raw17494step0Labels = raw17494Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17494 raw17494Labels permutation682 permutation6
    mixedMoment B raw17494step0 raw17494step0Labels = mixedMoment B raw17494step1 raw17494step1Labels := by
      have ha : raw17494step1 = -raw17494step0 := by apply Matrix.ext; change ∀ i j, raw17494step1 i j = -(raw17494step0 i j); unfold raw17494step1 raw17494step0; decide +kernel
      have hl : raw17494step1Labels = raw17494step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3972 node3972Labels := by rfl

theorem canonical17495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17495 raw17495Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw17495 raw17495Labels = mixedMoment B raw17495step0 raw17495step0Labels := by
      have hz : ∀ j, raw17495 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17495step0 = (fun i j => raw17495 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17495step0 raw17495; decide +kernel
      have hl : raw17495step0Labels = raw17495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17495 raw17495Labels permutation346 hz
    mixedMoment B raw17495step0 raw17495step0Labels = mixedMoment B raw17495step1 raw17495step1Labels := by
      have ha : raw17495step1 = (fun i j => raw17495step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17495step1 raw17495step0; decide +kernel
      have hl : raw17495step1Labels = raw17495step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17495step0 raw17495step0Labels permutation151 permutation6
    mixedMoment B raw17495step1 raw17495step1Labels = mixedMoment B raw17495step2 raw17495step2Labels := by
      have ha : raw17495step2 = -raw17495step1 := by apply Matrix.ext; change ∀ i j, raw17495step2 i j = -(raw17495step1 i j); unfold raw17495step2 raw17495step1; decide +kernel
      have hl : raw17495step2Labels = raw17495step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3982 node3982Labels := by rfl

theorem canonical17496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17496 raw17496Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw17496 raw17496Labels = mixedMoment B raw17496step0 raw17496step0Labels := by
      have ha : raw17496step0 = (fun i j => raw17496 (permutation511 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17496step0 raw17496; decide +kernel
      have hl : raw17496step0Labels = raw17496Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17496 raw17496Labels permutation511 permutation3
    _ = mixedMoment B node3872 node3872Labels := by rfl

theorem canonical17497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17497 raw17497Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw17497 raw17497Labels = mixedMoment B raw17497step0 raw17497step0Labels := by
      have ha : raw17497step0 = (fun i j => raw17497 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17497step0 raw17497; decide +kernel
      have hl : raw17497step0Labels = raw17497Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17497 raw17497Labels permutation682 permutation6
    mixedMoment B raw17497step0 raw17497step0Labels = mixedMoment B raw17497step1 raw17497step1Labels := by
      have ha : raw17497step1 = -raw17497step0 := by apply Matrix.ext; change ∀ i j, raw17497step1 i j = -(raw17497step0 i j); unfold raw17497step1 raw17497step0; decide +kernel
      have hl : raw17497step1Labels = raw17497step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3990 node3990Labels := by rfl

theorem canonical17498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17498 raw17498Labels = mixedMoment B node4032 node4032Labels := by
  calc
    mixedMoment B raw17498 raw17498Labels = mixedMoment B raw17498step0 raw17498step0Labels := by
      have ha : raw17498step0 = (fun i j => raw17498 (permutation654 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17498step0 raw17498; decide +kernel
      have hl : raw17498step0Labels = raw17498Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17498 raw17498Labels permutation654 permutation3
    _ = mixedMoment B node4032 node4032Labels := by rfl

theorem canonical17499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17499 raw17499Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw17499 raw17499Labels = mixedMoment B raw17499step0 raw17499step0Labels := by
      have ha : raw17499step0 = (fun i j => raw17499 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17499step0 raw17499; decide +kernel
      have hl : raw17499step0Labels = raw17499Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17499 raw17499Labels permutation158 permutation6
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical17500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17500 raw17500Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw17500 raw17500Labels = mixedMoment B raw17500step0 raw17500step0Labels := by
      have hz : ∀ j, raw17500 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17500step0 = (fun i j => raw17500 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17500step0 raw17500; decide +kernel
      have hl : raw17500step0Labels = raw17500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17500 raw17500Labels permutation346 hz
    mixedMoment B raw17500step0 raw17500step0Labels = mixedMoment B raw17500step1 raw17500step1Labels := by
      have ha : raw17500step1 = (fun i j => raw17500step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17500step1 raw17500step0; decide +kernel
      have hl : raw17500step1Labels = raw17500step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17500step0 raw17500step0Labels permutation151 permutation6
    mixedMoment B raw17500step1 raw17500step1Labels = mixedMoment B raw17500step2 raw17500step2Labels := by
      have ha : raw17500step2 = -raw17500step1 := by apply Matrix.ext; change ∀ i j, raw17500step2 i j = -(raw17500step1 i j); unfold raw17500step2 raw17500step1; decide +kernel
      have hl : raw17500step2Labels = raw17500step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3981 node3981Labels := by rfl

theorem canonical17501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17501 raw17501Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw17501 raw17501Labels = mixedMoment B raw17501step0 raw17501step0Labels := by
      have ha : raw17501step0 = (fun i j => raw17501 (permutation514 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17501step0 raw17501; decide +kernel
      have hl : raw17501step0Labels = raw17501Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17501 raw17501Labels permutation514 permutation3
    _ = mixedMoment B node3880 node3880Labels := by rfl

theorem canonical17502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17502 raw17502Labels = mixedMoment B node3989 node3989Labels := by
  calc
    mixedMoment B raw17502 raw17502Labels = mixedMoment B raw17502step0 raw17502step0Labels := by
      have ha : raw17502step0 = (fun i j => raw17502 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17502step0 raw17502; decide +kernel
      have hl : raw17502step0Labels = raw17502Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17502 raw17502Labels permutation158 permutation6
    _ = mixedMoment B node3989 node3989Labels := by rfl

theorem canonical17503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17503 raw17503Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw17503 raw17503Labels = mixedMoment B raw17503step0 raw17503step0Labels := by
      have ha : raw17503step0 = (fun i j => raw17503 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17503step0 raw17503; decide +kernel
      have hl : raw17503step0Labels = raw17503Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17503 raw17503Labels permutation158 permutation6
    _ = mixedMoment B node3990 node3990Labels := by rfl

theorem canonical17504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17504 raw17504Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw17504 raw17504Labels = mixedMoment B raw17504step0 raw17504step0Labels := by
      have ha : raw17504step0 = (fun i j => raw17504 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17504step0 raw17504; decide +kernel
      have hl : raw17504step0Labels = raw17504Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17504 raw17504Labels permutation158 permutation6
    _ = mixedMoment B node3796 node3796Labels := by rfl

theorem canonical17505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17505 raw17505Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw17505 raw17505Labels = mixedMoment B raw17505step0 raw17505step0Labels := by
      have ha : raw17505step0 = (fun i j => raw17505 (permutation360 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17505step0 raw17505; decide +kernel
      have hl : raw17505step0Labels = raw17505Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17505 raw17505Labels permutation360 permutation3
    mixedMoment B raw17505step0 raw17505step0Labels = mixedMoment B raw17505step1 raw17505step1Labels := by
      have ha : raw17505step1 = -raw17505step0 := by apply Matrix.ext; change ∀ i j, raw17505step1 i j = -(raw17505step0 i j); unfold raw17505step1 raw17505step0; decide +kernel
      have hl : raw17505step1Labels = raw17505step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3873 node3873Labels := by rfl

theorem canonical17506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17506 raw17506Labels = mixedMoment B node3870 node3870Labels := by
  calc
    mixedMoment B raw17506 raw17506Labels = mixedMoment B raw17506step0 raw17506step0Labels := by
      have ha : raw17506step0 = (fun i j => raw17506 (permutation510 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17506step0 raw17506; decide +kernel
      have hl : raw17506step0Labels = raw17506Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17506 raw17506Labels permutation510 permutation3
    _ = mixedMoment B node3870 node3870Labels := by rfl

theorem canonical17507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17507 raw17507Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw17507 raw17507Labels = mixedMoment B raw17507step0 raw17507step0Labels := by
      have ha : raw17507step0 = (fun i j => raw17507 (permutation351 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17507step0 raw17507; decide +kernel
      have hl : raw17507step0Labels = raw17507Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17507 raw17507Labels permutation351 permutation3
    mixedMoment B raw17507step0 raw17507step0Labels = mixedMoment B raw17507step1 raw17507step1Labels := by
      have ha : raw17507step1 = -raw17507step0 := by apply Matrix.ext; change ∀ i j, raw17507step1 i j = -(raw17507step0 i j); unfold raw17507step1 raw17507step0; decide +kernel
      have hl : raw17507step1Labels = raw17507step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3880 node3880Labels := by rfl

theorem canonical17508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17508 raw17508Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw17508 raw17508Labels = mixedMoment B raw17508step0 raw17508step0Labels := by
      have ha : raw17508step0 = (fun i j => raw17508 (permutation356 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17508step0 raw17508; decide +kernel
      have hl : raw17508step0Labels = raw17508Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17508 raw17508Labels permutation356 permutation3
    mixedMoment B raw17508step0 raw17508step0Labels = mixedMoment B raw17508step1 raw17508step1Labels := by
      have ha : raw17508step1 = -raw17508step0 := by apply Matrix.ext; change ∀ i j, raw17508step1 i j = -(raw17508step0 i j); unfold raw17508step1 raw17508step0; decide +kernel
      have hl : raw17508step1Labels = raw17508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3872 node3872Labels := by rfl

theorem canonical17509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17509 raw17509Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw17509 raw17509Labels = mixedMoment B raw17509step0 raw17509step0Labels := by
      have hz : ∀ j, raw17509 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17509step0 = (fun i j => raw17509 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17509step0 raw17509; decide +kernel
      have hl : raw17509step0Labels = raw17509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17509 raw17509Labels permutation434 hz
    mixedMoment B raw17509step0 raw17509step0Labels = mixedMoment B raw17509step1 raw17509step1Labels := by
      have ha : raw17509step1 = (fun i j => raw17509step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17509step1 raw17509step0; decide +kernel
      have hl : raw17509step1Labels = raw17509step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17509step0 raw17509step0Labels permutation32 permutation6
    _ = mixedMoment B node3808 node3808Labels := by rfl

theorem canonical17510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17510 raw17510Labels = mixedMoment B node3986 node3986Labels := by
  calc
    mixedMoment B raw17510 raw17510Labels = mixedMoment B raw17510step0 raw17510step0Labels := by
      have hz : ∀ j, raw17510 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17510step0 = (fun i j => raw17510 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17510step0 raw17510; decide +kernel
      have hl : raw17510step0Labels = raw17510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17510 raw17510Labels permutation434 hz
    mixedMoment B raw17510step0 raw17510step0Labels = mixedMoment B raw17510step1 raw17510step1Labels := by
      have hz : ∀ j, raw17510step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17510step1 = (fun i j => raw17510step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17510step1 raw17510step0; decide +kernel
      have hl : raw17510step1Labels = raw17510step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17510step0 raw17510step0Labels permutation80 hz
    mixedMoment B raw17510step1 raw17510step1Labels = mixedMoment B raw17510step2 raw17510step2Labels := by
      have ha : raw17510step2 = (fun i j => raw17510step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17510step2 raw17510step1; decide +kernel
      have hl : raw17510step2Labels = raw17510step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17510step1 raw17510step1Labels permutation8 permutation6
    _ = mixedMoment B node3986 node3986Labels := by rfl

theorem canonical17511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17511 raw17511Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw17511 raw17511Labels = mixedMoment B raw17511step0 raw17511step0Labels := by
      have hz : ∀ j, raw17511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17511step0 = (fun i j => raw17511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17511step0 raw17511; decide +kernel
      have hl : raw17511step0Labels = raw17511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17511 raw17511Labels permutation434 hz
    mixedMoment B raw17511step0 raw17511step0Labels = mixedMoment B raw17511step1 raw17511step1Labels := by
      have ha : raw17511step1 = (fun i j => raw17511step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17511step1 raw17511step0; decide +kernel
      have hl : raw17511step1Labels = raw17511step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17511step0 raw17511step0Labels permutation32 permutation6
    _ = mixedMoment B node3982 node3982Labels := by rfl

theorem canonical17512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17512 raw17512Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw17512 raw17512Labels = mixedMoment B raw17512step0 raw17512step0Labels := by
      have ha : raw17512step0 = (fun i j => raw17512 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17512step0 raw17512; decide +kernel
      have hl : raw17512step0Labels = raw17512Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17512 raw17512Labels permutation158 permutation6
    _ = mixedMoment B node3794 node3794Labels := by rfl

theorem canonical17513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17513 raw17513Labels = mixedMoment B node3950 node3950Labels := by
  calc
    mixedMoment B raw17513 raw17513Labels = mixedMoment B raw17513step0 raw17513step0Labels := by
      have ha : raw17513step0 = (fun i j => raw17513 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17513step0 raw17513; decide +kernel
      have hl : raw17513step0Labels = raw17513Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17513 raw17513Labels permutation158 permutation6
    _ = mixedMoment B node3950 node3950Labels := by rfl

theorem canonical17514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17514 raw17514Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw17514 raw17514Labels = mixedMoment B raw17514step0 raw17514step0Labels := by
      have hz : ∀ j, raw17514 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17514step0 = (fun i j => raw17514 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17514step0 raw17514; decide +kernel
      have hl : raw17514step0Labels = raw17514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17514 raw17514Labels permutation346 hz
    mixedMoment B raw17514step0 raw17514step0Labels = mixedMoment B raw17514step1 raw17514step1Labels := by
      have ha : raw17514step1 = (fun i j => raw17514step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17514step1 raw17514step0; decide +kernel
      have hl : raw17514step1Labels = raw17514step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17514step0 raw17514step0Labels permutation151 permutation6
    mixedMoment B raw17514step1 raw17514step1Labels = mixedMoment B raw17514step2 raw17514step2Labels := by
      have ha : raw17514step2 = -raw17514step1 := by apply Matrix.ext; change ∀ i j, raw17514step2 i j = -(raw17514step1 i j); unfold raw17514step2 raw17514step1; decide +kernel
      have hl : raw17514step2Labels = raw17514step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical17515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17515 raw17515Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw17515 raw17515Labels = mixedMoment B raw17515step0 raw17515step0Labels := by
      have ha : raw17515step0 = (fun i j => raw17515 (permutation508 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17515step0 raw17515; decide +kernel
      have hl : raw17515step0Labels = raw17515Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17515 raw17515Labels permutation508 permutation3
    _ = mixedMoment B node3873 node3873Labels := by rfl

theorem canonical17516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17516 raw17516Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw17516 raw17516Labels = mixedMoment B raw17516step0 raw17516step0Labels := by
      have ha : raw17516step0 = (fun i j => raw17516 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17516step0 raw17516; decide +kernel
      have hl : raw17516step0Labels = raw17516Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17516 raw17516Labels permutation158 permutation6
    _ = mixedMoment B node3972 node3972Labels := by rfl

theorem canonical17517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17517 raw17517Labels = mixedMoment B node3793 node3793Labels := by
  calc
    mixedMoment B raw17517 raw17517Labels = mixedMoment B raw17517step0 raw17517step0Labels := by
      have ha : raw17517step0 = (fun i j => raw17517 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17517step0 raw17517; decide +kernel
      have hl : raw17517step0Labels = raw17517Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17517 raw17517Labels permutation158 permutation6
    _ = mixedMoment B node3793 node3793Labels := by rfl

theorem canonical17518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17518 raw17518Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw17518 raw17518Labels = mixedMoment B raw17518step0 raw17518step0Labels := by
      have ha : raw17518step0 = (fun i j => raw17518 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17518step0 raw17518; decide +kernel
      have hl : raw17518step0Labels = raw17518Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17518 raw17518Labels permutation682 permutation6
    mixedMoment B raw17518step0 raw17518step0Labels = mixedMoment B raw17518step1 raw17518step1Labels := by
      have ha : raw17518step1 = -raw17518step0 := by apply Matrix.ext; change ∀ i j, raw17518step1 i j = -(raw17518step0 i j); unfold raw17518step1 raw17518step0; decide +kernel
      have hl : raw17518step1Labels = raw17518step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3794 node3794Labels := by rfl

theorem canonical17519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17519 raw17519Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw17519 raw17519Labels = mixedMoment B raw17519step0 raw17519step0Labels := by
      have hz : ∀ j, raw17519 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17519step0 = (fun i j => raw17519 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17519step0 raw17519; decide +kernel
      have hl : raw17519step0Labels = raw17519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17519 raw17519Labels permutation346 hz
    mixedMoment B raw17519step0 raw17519step0Labels = mixedMoment B raw17519step1 raw17519step1Labels := by
      have ha : raw17519step1 = (fun i j => raw17519step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17519step1 raw17519step0; decide +kernel
      have hl : raw17519step1Labels = raw17519step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17519step0 raw17519step0Labels permutation151 permutation6
    mixedMoment B raw17519step1 raw17519step1Labels = mixedMoment B raw17519step2 raw17519step2Labels := by
      have ha : raw17519step2 = -raw17519step1 := by apply Matrix.ext; change ∀ i j, raw17519step2 i j = -(raw17519step1 i j); unfold raw17519step2 raw17519step1; decide +kernel
      have hl : raw17519step2Labels = raw17519step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3808 node3808Labels := by rfl

theorem canonical17520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17520 raw17520Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw17520 raw17520Labels = mixedMoment B raw17520step0 raw17520step0Labels := by
      have ha : raw17520step0 = (fun i j => raw17520 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17520step0 raw17520; decide +kernel
      have hl : raw17520step0Labels = raw17520Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17520 raw17520Labels permutation682 permutation6
    mixedMoment B raw17520step0 raw17520step0Labels = mixedMoment B raw17520step1 raw17520step1Labels := by
      have ha : raw17520step1 = -raw17520step0 := by apply Matrix.ext; change ∀ i j, raw17520step1 i j = -(raw17520step0 i j); unfold raw17520step1 raw17520step0; decide +kernel
      have hl : raw17520step1Labels = raw17520step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3796 node3796Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical17648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17648 raw17648Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw17648 raw17648Labels = mixedMoment B raw17648step0 raw17648step0Labels := by
      have ha : raw17648step0 = (fun i j => raw17648 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17648step0 raw17648; decide +kernel
      have hl : raw17648step0Labels = raw17648Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17648 raw17648Labels permutation682 permutation6
    mixedMoment B raw17648step0 raw17648step0Labels = mixedMoment B raw17648step1 raw17648step1Labels := by
      have ha : raw17648step1 = -raw17648step0 := by apply Matrix.ext; change ∀ i j, raw17648step1 i j = -(raw17648step0 i j); unfold raw17648step1 raw17648step0; decide +kernel
      have hl : raw17648step1Labels = raw17648step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3839 node3839Labels := by rfl

theorem canonical17649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17649 raw17649Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw17649 raw17649Labels = mixedMoment B raw17649step0 raw17649step0Labels := by
      have hz : ∀ j, raw17649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17649step0 = (fun i j => raw17649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17649step0 raw17649; decide +kernel
      have hl : raw17649step0Labels = raw17649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17649 raw17649Labels permutation346 hz
    mixedMoment B raw17649step0 raw17649step0Labels = mixedMoment B raw17649step1 raw17649step1Labels := by
      have ha : raw17649step1 = (fun i j => raw17649step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17649step1 raw17649step0; decide +kernel
      have hl : raw17649step1Labels = raw17649step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17649step0 raw17649step0Labels permutation151 permutation6
    mixedMoment B raw17649step1 raw17649step1Labels = mixedMoment B raw17649step2 raw17649step2Labels := by
      have ha : raw17649step2 = -raw17649step1 := by apply Matrix.ext; change ∀ i j, raw17649step2 i j = -(raw17649step1 i j); unfold raw17649step2 raw17649step1; decide +kernel
      have hl : raw17649step2Labels = raw17649step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3853 node3853Labels := by rfl

theorem canonical17650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17650 raw17650Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw17650 raw17650Labels = mixedMoment B raw17650step0 raw17650step0Labels := by
      have ha : raw17650step0 = (fun i j => raw17650 (permutation494 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17650step0 raw17650; decide +kernel
      have hl : raw17650step0Labels = raw17650Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17650 raw17650Labels permutation494 permutation3
    _ = mixedMoment B node3841 node3841Labels := by rfl

theorem canonical17651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17651 raw17651Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw17651 raw17651Labels = mixedMoment B raw17651step0 raw17651step0Labels := by
      have ha : raw17651step0 = (fun i j => raw17651 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17651step0 raw17651; decide +kernel
      have hl : raw17651step0Labels = raw17651Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17651 raw17651Labels permutation158 permutation6
    _ = mixedMoment B node3837 node3837Labels := by rfl

theorem canonical17652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17652 raw17652Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw17652 raw17652Labels = mixedMoment B raw17652step0 raw17652step0Labels := by
      have hz : ∀ j, raw17652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17652step0 = (fun i j => raw17652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17652step0 raw17652; decide +kernel
      have hl : raw17652step0Labels = raw17652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17652 raw17652Labels permutation346 hz
    mixedMoment B raw17652step0 raw17652step0Labels = mixedMoment B raw17652step1 raw17652step1Labels := by
      have ha : raw17652step1 = (fun i j => raw17652step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17652step1 raw17652step0; decide +kernel
      have hl : raw17652step1Labels = raw17652step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17652step0 raw17652step0Labels permutation151 permutation6
    mixedMoment B raw17652step1 raw17652step1Labels = mixedMoment B raw17652step2 raw17652step2Labels := by
      have ha : raw17652step2 = -raw17652step1 := by apply Matrix.ext; change ∀ i j, raw17652step2 i j = -(raw17652step1 i j); unfold raw17652step2 raw17652step1; decide +kernel
      have hl : raw17652step2Labels = raw17652step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3852 node3852Labels := by rfl

theorem canonical17653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17653 raw17653Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw17653 raw17653Labels = mixedMoment B raw17653step0 raw17653step0Labels := by
      have ha : raw17653step0 = (fun i j => raw17653 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17653step0 raw17653; decide +kernel
      have hl : raw17653step0Labels = raw17653Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17653 raw17653Labels permutation682 permutation6
    mixedMoment B raw17653step0 raw17653step0Labels = mixedMoment B raw17653step1 raw17653step1Labels := by
      have ha : raw17653step1 = -raw17653step0 := by apply Matrix.ext; change ∀ i j, raw17653step1 i j = -(raw17653step0 i j); unfold raw17653step1 raw17653step0; decide +kernel
      have hl : raw17653step1Labels = raw17653step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical17654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17654 raw17654Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw17654 raw17654Labels = mixedMoment B raw17654step0 raw17654step0Labels := by
      have ha : raw17654step0 = (fun i j => raw17654 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17654step0 raw17654; decide +kernel
      have hl : raw17654step0Labels = raw17654Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17654 raw17654Labels permutation158 permutation6
    _ = mixedMoment B node3795 node3795Labels := by rfl

theorem canonical17655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17655 raw17655Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw17655 raw17655Labels = mixedMoment B raw17655step0 raw17655step0Labels := by
      have ha : raw17655step0 = (fun i j => raw17655 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17655step0 raw17655; decide +kernel
      have hl : raw17655step0Labels = raw17655Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17655 raw17655Labels permutation682 permutation6
    mixedMoment B raw17655step0 raw17655step0Labels = mixedMoment B raw17655step1 raw17655step1Labels := by
      have ha : raw17655step1 = -raw17655step0 := by apply Matrix.ext; change ∀ i j, raw17655step1 i j = -(raw17655step0 i j); unfold raw17655step1 raw17655step0; decide +kernel
      have hl : raw17655step1Labels = raw17655step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3832 node3832Labels := by rfl

theorem canonical17656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17656 raw17656Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw17656 raw17656Labels = mixedMoment B raw17656step0 raw17656step0Labels := by
      have ha : raw17656step0 = (fun i j => raw17656 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17656step0 raw17656; decide +kernel
      have hl : raw17656step0Labels = raw17656Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17656 raw17656Labels permutation682 permutation6
    mixedMoment B raw17656step0 raw17656step0Labels = mixedMoment B raw17656step1 raw17656step1Labels := by
      have ha : raw17656step1 = -raw17656step0 := by apply Matrix.ext; change ∀ i j, raw17656step1 i j = -(raw17656step0 i j); unfold raw17656step1 raw17656step0; decide +kernel
      have hl : raw17656step1Labels = raw17656step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3834 node3834Labels := by rfl

theorem canonical17657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17657 raw17657Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw17657 raw17657Labels = mixedMoment B raw17657step0 raw17657step0Labels := by
      have hz : ∀ j, raw17657 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17657step0 = (fun i j => raw17657 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17657step0 raw17657; decide +kernel
      have hl : raw17657step0Labels = raw17657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17657 raw17657Labels permutation434 hz
    mixedMoment B raw17657step0 raw17657step0Labels = mixedMoment B raw17657step1 raw17657step1Labels := by
      have ha : raw17657step1 = (fun i j => raw17657step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17657step1 raw17657step0; decide +kernel
      have hl : raw17657step1Labels = raw17657step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17657step0 raw17657step0Labels permutation151 permutation6
    mixedMoment B raw17657step1 raw17657step1Labels = mixedMoment B raw17657step2 raw17657step2Labels := by
      have ha : raw17657step2 = -raw17657step1 := by apply Matrix.ext; change ∀ i j, raw17657step2 i j = -(raw17657step1 i j); unfold raw17657step2 raw17657step1; decide +kernel
      have hl : raw17657step2Labels = raw17657step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

theorem canonical17658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17658 raw17658Labels = mixedMoment B node3971 node3971Labels := by
  calc
    mixedMoment B raw17658 raw17658Labels = mixedMoment B raw17658step0 raw17658step0Labels := by
      have ha : raw17658step0 = (fun i j => raw17658 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17658step0 raw17658; decide +kernel
      have hl : raw17658step0Labels = raw17658Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17658 raw17658Labels permutation158 permutation6
    _ = mixedMoment B node3971 node3971Labels := by rfl

theorem canonical17659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17659 raw17659Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw17659 raw17659Labels = mixedMoment B raw17659step0 raw17659step0Labels := by
      have ha : raw17659step0 = (fun i j => raw17659 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17659step0 raw17659; decide +kernel
      have hl : raw17659step0Labels = raw17659Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17659 raw17659Labels permutation682 permutation6
    mixedMoment B raw17659step0 raw17659step0Labels = mixedMoment B raw17659step1 raw17659step1Labels := by
      have ha : raw17659step1 = -raw17659step0 := by apply Matrix.ext; change ∀ i j, raw17659step1 i j = -(raw17659step0 i j); unfold raw17659step1 raw17659step0; decide +kernel
      have hl : raw17659step1Labels = raw17659step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3514 node3514Labels := by rfl

theorem canonical17660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17660 raw17660Labels = mixedMoment B node3515 node3515Labels := by
  calc
    mixedMoment B raw17660 raw17660Labels = mixedMoment B raw17660step0 raw17660step0Labels := by
      have ha : raw17660step0 = (fun i j => raw17660 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17660step0 raw17660; decide +kernel
      have hl : raw17660step0Labels = raw17660Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17660 raw17660Labels permutation682 permutation6
    mixedMoment B raw17660step0 raw17660step0Labels = mixedMoment B raw17660step1 raw17660step1Labels := by
      have ha : raw17660step1 = -raw17660step0 := by apply Matrix.ext; change ∀ i j, raw17660step1 i j = -(raw17660step0 i j); unfold raw17660step1 raw17660step0; decide +kernel
      have hl : raw17660step1Labels = raw17660step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3515 node3515Labels := by rfl

theorem canonical17661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17661 raw17661Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw17661 raw17661Labels = mixedMoment B raw17661step0 raw17661step0Labels := by
      have hz : ∀ j, raw17661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17661step0 = (fun i j => raw17661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17661step0 raw17661; decide +kernel
      have hl : raw17661step0Labels = raw17661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17661 raw17661Labels permutation346 hz
    mixedMoment B raw17661step0 raw17661step0Labels = mixedMoment B raw17661step1 raw17661step1Labels := by
      have ha : raw17661step1 = (fun i j => raw17661step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17661step1 raw17661step0; decide +kernel
      have hl : raw17661step1Labels = raw17661step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17661step0 raw17661step0Labels permutation151 permutation6
    mixedMoment B raw17661step1 raw17661step1Labels = mixedMoment B raw17661step2 raw17661step2Labels := by
      have ha : raw17661step2 = -raw17661step1 := by apply Matrix.ext; change ∀ i j, raw17661step2 i j = -(raw17661step1 i j); unfold raw17661step2 raw17661step1; decide +kernel
      have hl : raw17661step2Labels = raw17661step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical17662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17662 raw17662Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw17662 raw17662Labels = mixedMoment B raw17662step0 raw17662step0Labels := by
      have ha : raw17662step0 = (fun i j => raw17662 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17662step0 raw17662; decide +kernel
      have hl : raw17662step0Labels = raw17662Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17662 raw17662Labels permutation682 permutation6
    mixedMoment B raw17662step0 raw17662step0Labels = mixedMoment B raw17662step1 raw17662step1Labels := by
      have ha : raw17662step1 = -raw17662step0 := by apply Matrix.ext; change ∀ i j, raw17662step1 i j = -(raw17662step0 i j); unfold raw17662step1 raw17662step0; decide +kernel
      have hl : raw17662step1Labels = raw17662step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3517 node3517Labels := by rfl

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

theorem canonical2463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2463 raw2463Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw2463 raw2463Labels = mixedMoment B raw2463step0 raw2463step0Labels := by
      have ha : raw2463step0 = (fun i j => raw2463 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2463step0 raw2463; decide +kernel
      have hl : raw2463step0Labels = raw2463Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2463 raw2463Labels permutation152 permutation4
    mixedMoment B raw2463step0 raw2463step0Labels = mixedMoment B raw2463step1 raw2463step1Labels := by
      have ha : raw2463step1 = raw2463step0 := by apply Matrix.ext; unfold raw2463step1 raw2463step0; decide +kernel
      have hl : raw2463step0Labels = labelEmbedding7 ∘ raw2463step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2463step0 raw2463step0Labels raw2463step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical2464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2464 raw2464Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw2464 raw2464Labels = mixedMoment B raw2464step0 raw2464step0Labels := by
      have ha : raw2464step0 = (fun i j => raw2464 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2464step0 raw2464; decide +kernel
      have hl : raw2464step0Labels = raw2464Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2464 raw2464Labels permutation152 permutation4
    _ = mixedMoment B node3781 node3781Labels := by rfl

theorem canonical2465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2465 raw2465Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw2465 raw2465Labels = mixedMoment B raw2465step0 raw2465step0Labels := by
      have ha : raw2465step0 = (fun i j => raw2465 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2465step0 raw2465; decide +kernel
      have hl : raw2465step0Labels = raw2465Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2465 raw2465Labels permutation153 permutation6
    mixedMoment B raw2465step0 raw2465step0Labels = mixedMoment B raw2465step1 raw2465step1Labels := by
      have ha : raw2465step1 = -raw2465step0 := by apply Matrix.ext; change ∀ i j, raw2465step1 i j = -(raw2465step0 i j); unfold raw2465step1 raw2465step0; decide +kernel
      have hl : raw2465step1Labels = raw2465step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2465step1 raw2465step1Labels = mixedMoment B raw2465step2 raw2465step2Labels := by
      have ha : raw2465step2 = raw2465step1 := by apply Matrix.ext; unfold raw2465step2 raw2465step1; decide +kernel
      have hl : raw2465step1Labels = labelEmbedding1 ∘ raw2465step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2465step1 raw2465step1Labels raw2465step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3794 node3794Labels := by rfl

theorem canonical2466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2466 raw2466Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw2466 raw2466Labels = mixedMoment B raw2466step0 raw2466step0Labels := by
      have ha : raw2466step0 = (fun i j => raw2466 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2466step0 raw2466; decide +kernel
      have hl : raw2466step0Labels = raw2466Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2466 raw2466Labels permutation152 permutation4
    mixedMoment B raw2466step0 raw2466step0Labels = mixedMoment B raw2466step1 raw2466step1Labels := by
      have ha : raw2466step1 = raw2466step0 := by apply Matrix.ext; unfold raw2466step1 raw2466step0; decide +kernel
      have hl : raw2466step0Labels = labelEmbedding7 ∘ raw2466step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2466step0 raw2466step0Labels raw2466step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

theorem canonical2467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2467 raw2467Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw2467 raw2467Labels = mixedMoment B raw2467step0 raw2467step0Labels := by
      have ha : raw2467step0 = (fun i j => raw2467 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2467step0 raw2467; decide +kernel
      have hl : raw2467step0Labels = raw2467Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2467 raw2467Labels permutation152 permutation4
    _ = mixedMoment B node3782 node3782Labels := by rfl

theorem canonical2468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2468 raw2468Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw2468 raw2468Labels = mixedMoment B raw2468step0 raw2468step0Labels := by
      have ha : raw2468step0 = (fun i j => raw2468 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2468step0 raw2468; decide +kernel
      have hl : raw2468step0Labels = raw2468Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2468 raw2468Labels permutation156 permutation6
    mixedMoment B raw2468step0 raw2468step0Labels = mixedMoment B raw2468step1 raw2468step1Labels := by
      have ha : raw2468step1 = -raw2468step0 := by apply Matrix.ext; change ∀ i j, raw2468step1 i j = -(raw2468step0 i j); unfold raw2468step1 raw2468step0; decide +kernel
      have hl : raw2468step1Labels = raw2468step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2468step1 raw2468step1Labels = mixedMoment B raw2468step2 raw2468step2Labels := by
      have ha : raw2468step2 = raw2468step1 := by apply Matrix.ext; unfold raw2468step2 raw2468step1; decide +kernel
      have hl : raw2468step1Labels = labelEmbedding1 ∘ raw2468step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2468step1 raw2468step1Labels raw2468step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3796 node3796Labels := by rfl

theorem canonical2511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2511 raw2511Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw2511 raw2511Labels = mixedMoment B raw2511step0 raw2511step0Labels := by
      have ha : raw2511step0 = (fun i j => raw2511 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2511step0 raw2511; decide +kernel
      have hl : raw2511step0Labels = raw2511Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2511 raw2511Labels permutation152 permutation4
    mixedMoment B raw2511step0 raw2511step0Labels = mixedMoment B raw2511step1 raw2511step1Labels := by
      have ha : raw2511step1 = raw2511step0 := by apply Matrix.ext; unfold raw2511step1 raw2511step0; decide +kernel
      have hl : raw2511step0Labels = labelEmbedding7 ∘ raw2511step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2511step0 raw2511step0Labels raw2511step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

theorem canonical2512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2512 raw2512Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw2512 raw2512Labels = mixedMoment B raw2512step0 raw2512step0Labels := by
      have ha : raw2512step0 = (fun i j => raw2512 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2512step0 raw2512; decide +kernel
      have hl : raw2512step0Labels = raw2512Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2512 raw2512Labels permutation152 permutation4
    _ = mixedMoment B node3837 node3837Labels := by rfl

theorem canonical2513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2513 raw2513Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw2513 raw2513Labels = mixedMoment B raw2513step0 raw2513step0Labels := by
      have ha : raw2513step0 = (fun i j => raw2513 (permutation662 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2513step0 raw2513; decide +kernel
      have hl : raw2513step0Labels = raw2513Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2513 raw2513Labels permutation662 permutation6
    mixedMoment B raw2513step0 raw2513step0Labels = mixedMoment B raw2513step1 raw2513step1Labels := by
      have ha : raw2513step1 = raw2513step0 := by apply Matrix.ext; unfold raw2513step1 raw2513step0; decide +kernel
      have hl : raw2513step0Labels = labelEmbedding1 ∘ raw2513step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2513step0 raw2513step0Labels raw2513step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3837 node3837Labels := by rfl

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

theorem canonical2589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2589 raw2589Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw2589 raw2589Labels = mixedMoment B raw2589step0 raw2589step0Labels := by
      have ha : raw2589step0 = (fun i j => raw2589 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2589step0 raw2589; decide +kernel
      have hl : raw2589step0Labels = raw2589Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2589 raw2589Labels permutation32 permutation4
    mixedMoment B raw2589step0 raw2589step0Labels = mixedMoment B raw2589step1 raw2589step1Labels := by
      have ha : raw2589step1 = raw2589step0 := by apply Matrix.ext; unfold raw2589step1 raw2589step0; decide +kernel
      have hl : raw2589step0Labels = labelEmbedding7 ∘ raw2589step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2589step0 raw2589step0Labels raw2589step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2590 raw2590Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw2590 raw2590Labels = mixedMoment B raw2590step0 raw2590step0Labels := by
      have ha : raw2590step0 = (fun i j => raw2590 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2590step0 raw2590; decide +kernel
      have hl : raw2590step0Labels = raw2590Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2590 raw2590Labels permutation32 permutation4
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical2591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2591 raw2591Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw2591 raw2591Labels = mixedMoment B raw2591step0 raw2591step0Labels := by
      have ha : raw2591step0 = (fun i j => raw2591 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2591step0 raw2591; decide +kernel
      have hl : raw2591step0Labels = raw2591Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2591 raw2591Labels permutation56 permutation6
    mixedMoment B raw2591step0 raw2591step0Labels = mixedMoment B raw2591step1 raw2591step1Labels := by
      have ha : raw2591step1 = -raw2591step0 := by apply Matrix.ext; change ∀ i j, raw2591step1 i j = -(raw2591step0 i j); unfold raw2591step1 raw2591step0; decide +kernel
      have hl : raw2591step1Labels = raw2591step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2591step1 raw2591step1Labels = mixedMoment B raw2591step2 raw2591step2Labels := by
      have ha : raw2591step2 = raw2591step1 := by apply Matrix.ext; unfold raw2591step2 raw2591step1; decide +kernel
      have hl : raw2591step1Labels = labelEmbedding1 ∘ raw2591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2591step1 raw2591step1Labels raw2591step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5395 node5395Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3781 node3781Labels + mixedMoment B node3794 node3794Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2463 singletonSmall5395
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5395) = raw2463Labels := by decide +kernel
  rw [hl, canonical2463 B hB] at h
  have hc0 : mixedMoment B raw2463 (Fin.cases (0 : Fin 2) singletonSmall5395) =
      mixedMoment B node3781 node3781Labels := by
    have ha : raw2463 = raw2464 := by apply Matrix.ext; unfold raw2463 raw2464; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5395 = raw2464Labels := by decide +kernel
    rw [ha, hj, canonical2464 B hB]
  have hc1 : mixedMoment B raw2463 (Fin.cases (1 : Fin 2) singletonSmall5395) =
      mixedMoment B node3794 node3794Labels := by
    have ha : raw2463 = raw2465 := by apply Matrix.ext; unfold raw2463 raw2465; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5395 = raw2465Labels := by decide +kernel
    rw [ha, hj, canonical2465 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5397 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5397 node5397Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3782 node3782Labels + mixedMoment B node3796 node3796Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2466 singletonSmall5397
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5397) = raw2466Labels := by decide +kernel
  rw [hl, canonical2466 B hB] at h
  have hc0 : mixedMoment B raw2466 (Fin.cases (0 : Fin 2) singletonSmall5397) =
      mixedMoment B node3782 node3782Labels := by
    have ha : raw2466 = raw2467 := by apply Matrix.ext; unfold raw2466 raw2467; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5397 = raw2467Labels := by decide +kernel
    rw [ha, hj, canonical2467 B hB]
  have hc1 : mixedMoment B raw2466 (Fin.cases (1 : Fin 2) singletonSmall5397) =
      mixedMoment B node3796 node3796Labels := by
    have ha : raw2466 = raw2468 := by apply Matrix.ext; unfold raw2466 raw2468; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5397 = raw2468Labels := by decide +kernel
    rw [ha, hj, canonical2468 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5423 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5423 node5423Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3837 node3837Labels + mixedMoment B node3837 node3837Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2511 singletonSmall5423
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5423) = raw2511Labels := by decide +kernel
  rw [hl, canonical2511 B hB] at h
  have hc0 : mixedMoment B raw2511 (Fin.cases (0 : Fin 2) singletonSmall5423) =
      mixedMoment B node3837 node3837Labels := by
    have ha : raw2511 = raw2512 := by apply Matrix.ext; unfold raw2511 raw2512; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5423 = raw2512Labels := by decide +kernel
    rw [ha, hj, canonical2512 B hB]
  have hc1 : mixedMoment B raw2511 (Fin.cases (1 : Fin 2) singletonSmall5423) =
      mixedMoment B node3837 node3837Labels := by
    have ha : raw2511 = raw2513 := by apply Matrix.ext; unfold raw2511 raw2513; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5423 = raw2513Labels := by decide +kernel
    rw [ha, hj, canonical2513 B hB]
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

theorem singleton5473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5473 node5473Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3958 node3958Labels + mixedMoment B node3961 node3961Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2589 singletonSmall5473
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5473) = raw2589Labels := by decide +kernel
  rw [hl, canonical2589 B hB] at h
  have hc0 : mixedMoment B raw2589 (Fin.cases (0 : Fin 2) singletonSmall5473) =
      mixedMoment B node3958 node3958Labels := by
    have ha : raw2589 = raw2590 := by apply Matrix.ext; unfold raw2589 raw2590; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5473 = raw2590Labels := by decide +kernel
    rw [ha, hj, canonical2590 B hB]
  have hc1 : mixedMoment B raw2589 (Fin.cases (1 : Fin 2) singletonSmall5473) =
      mixedMoment B node3961 node3961Labels := by
    have ha : raw2589 = raw2591 := by apply Matrix.ext; unfold raw2589 raw2591; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5473 = raw2591Labels := by decide +kernel
    rw [ha, hj, canonical2591 B hB]
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

theorem zero5468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5468 node5468Labels = 0 := by
  exact mixedMoment_alpha B hF node5468 node5468Labels 1 permutation202
    (by decide +kernel)

theorem zero5477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5477 node5477Labels = 0 := by
  exact mixedMoment_alpha B hF node5477 node5477Labels 2 permutation152
    (by decide +kernel)

theorem zero5487 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5487 node5487Labels = 0 := by
  exact mixedMoment_order_one B hB node5487 node5487Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3515 node3515Labels = 0 := by
  exact mixedMoment_alpha B hF node3515 node3515Labels 1 permutation443
    (by decide +kernel)

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

theorem sound3514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3514 node3514Labels = Sparse.eval nodeValue3514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3514) = mixedMoment B node3514 node3514Labels := rfl
  simpa [nodeValue3514, Sparse.eval] using hc.symm

theorem sound3515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3515 node3515Labels = Sparse.eval nodeValue3515 (mixedVector B) := by
  simpa only [nodeValue3515, Sparse.eval_nil] using zero3515 B _hB _hF

theorem sound3517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3517 node3517Labels = Sparse.eval nodeValue3517 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3517) = mixedMoment B node3517 node3517Labels := rfl
  simpa [nodeValue3517, Sparse.eval] using hc.symm

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

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

theorem sound3558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3558 node3558Labels = Sparse.eval nodeValue3558 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3558) = mixedMoment B node3558 node3558Labels := rfl
  simpa [nodeValue3558, Sparse.eval] using hc.symm

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

theorem zero3793 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3793 node3793Labels = 0 := by
  exact mixedMoment_order_one B hB node3793 node3793Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = 0 := by
  exact mixedMoment_order_one B hB node3807 node3807Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3808 node3808Labels = 0 := by
  exact mixedMoment_order_one B hB node3808 node3808Labels 1
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

theorem sound3781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3781 node3781Labels = Sparse.eval nodeValue3781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3781) = mixedMoment B node3781 node3781Labels := rfl
  simpa [nodeValue3781, Sparse.eval] using hc.symm

theorem sound3782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3782 node3782Labels = Sparse.eval nodeValue3782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3782) = mixedMoment B node3782 node3782Labels := rfl
  simpa [nodeValue3782, Sparse.eval] using hc.symm

theorem sound3793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3793 node3793Labels = Sparse.eval nodeValue3793 (mixedVector B) := by
  simpa only [nodeValue3793, Sparse.eval_nil] using zero3793 B _hB _hF

theorem sound3794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3794 node3794Labels = Sparse.eval nodeValue3794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3794) = mixedMoment B node3794 node3794Labels := rfl
  simpa [nodeValue3794, Sparse.eval] using hc.symm

theorem sound3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3795 node3795Labels = Sparse.eval nodeValue3795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3795) = mixedMoment B node3795 node3795Labels := rfl
  simpa [nodeValue3795, Sparse.eval] using hc.symm

theorem sound3796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3796 node3796Labels = Sparse.eval nodeValue3796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3796) = mixedMoment B node3796 node3796Labels := rfl
  simpa [nodeValue3796, Sparse.eval] using hc.symm

theorem sound3807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = Sparse.eval nodeValue3807 (mixedVector B) := by
  simpa only [nodeValue3807, Sparse.eval_nil] using zero3807 B _hB _hF

theorem sound3808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3808 node3808Labels = Sparse.eval nodeValue3808 (mixedVector B) := by
  simpa only [nodeValue3808, Sparse.eval_nil] using zero3808 B _hB _hF

theorem sound3832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3832 node3832Labels = Sparse.eval nodeValue3832 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3832) = mixedMoment B node3832 node3832Labels := rfl
  simpa [nodeValue3832, Sparse.eval] using hc.symm

theorem sound3834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3834 node3834Labels = Sparse.eval nodeValue3834 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3834) = mixedMoment B node3834 node3834Labels := rfl
  simpa [nodeValue3834, Sparse.eval] using hc.symm

theorem sound3837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3837 node3837Labels = Sparse.eval nodeValue3837 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3837) = mixedMoment B node3837 node3837Labels := rfl
  simpa [nodeValue3837, Sparse.eval] using hc.symm

theorem sound3838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3838 node3838Labels = Sparse.eval nodeValue3838 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3838) = mixedMoment B node3838 node3838Labels := rfl
  simpa [nodeValue3838, Sparse.eval] using hc.symm

theorem sound3839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3839 node3839Labels = Sparse.eval nodeValue3839 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3839) = mixedMoment B node3839 node3839Labels := rfl
  simpa [nodeValue3839, Sparse.eval] using hc.symm

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

theorem zero3861 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3861 node3861Labels = 0 := by
  exact mixedMoment_order_one B hB node3861 node3861Labels 1
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

theorem sound3841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3841 node3841Labels = Sparse.eval nodeValue3841 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3841) = mixedMoment B node3841 node3841Labels := rfl
  simpa [nodeValue3841, Sparse.eval] using hc.symm

theorem sound3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3843 node3843Labels = Sparse.eval nodeValue3843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3843) = mixedMoment B node3843 node3843Labels := rfl
  simpa [nodeValue3843, Sparse.eval] using hc.symm

theorem sound3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3845 node3845Labels = Sparse.eval nodeValue3845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3845) = mixedMoment B node3845 node3845Labels := rfl
  simpa [nodeValue3845, Sparse.eval] using hc.symm

theorem sound3861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3861 node3861Labels = Sparse.eval nodeValue3861 (mixedVector B) := by
  simpa only [nodeValue3861, Sparse.eval_nil] using zero3861 B _hB _hF

theorem sound3866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3866 node3866Labels = Sparse.eval nodeValue3866 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3866) = mixedMoment B node3866 node3866Labels := rfl
  simpa [nodeValue3866, Sparse.eval] using hc.symm

theorem sound3870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3870 node3870Labels = Sparse.eval nodeValue3870 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3870) = mixedMoment B node3870 node3870Labels := rfl
  simpa [nodeValue3870, Sparse.eval] using hc.symm

theorem sound3871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3871 node3871Labels = Sparse.eval nodeValue3871 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3871) = mixedMoment B node3871 node3871Labels := rfl
  simpa [nodeValue3871, Sparse.eval] using hc.symm

theorem sound3872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3872 node3872Labels = Sparse.eval nodeValue3872 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3872) = mixedMoment B node3872 node3872Labels := rfl
  simpa [nodeValue3872, Sparse.eval] using hc.symm

theorem sound3873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3873 node3873Labels = Sparse.eval nodeValue3873 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3873) = mixedMoment B node3873 node3873Labels := rfl
  simpa [nodeValue3873, Sparse.eval] using hc.symm

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

theorem sound3880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3880 node3880Labels = Sparse.eval nodeValue3880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3880) = mixedMoment B node3880 node3880Labels := rfl
  simpa [nodeValue3880, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3950 node3950Labels = 0 := by
  exact mixedMoment_alpha B hF node3950 node3950Labels 1 permutation212
    (by decide +kernel)

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

theorem sound3950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3950 node3950Labels = Sparse.eval nodeValue3950 (mixedVector B) := by
  simpa only [nodeValue3950, Sparse.eval_nil] using zero3950 B _hB _hF

theorem sound3958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3958 node3958Labels = Sparse.eval nodeValue3958 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3958) = mixedMoment B node3958 node3958Labels := rfl
  simpa [nodeValue3958, Sparse.eval] using hc.symm

theorem sound3961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3961 node3961Labels = Sparse.eval nodeValue3961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3961) = mixedMoment B node3961 node3961Labels := rfl
  simpa [nodeValue3961, Sparse.eval] using hc.symm

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

theorem zero3971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3971 node3971Labels = 0 := by
  exact mixedMoment_alpha B hF node3971 node3971Labels 2 permutation152
    (by decide +kernel)

theorem zero3986 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3986 node3986Labels = 0 := by
  exact mixedMoment_order_one B hB node3986 node3986Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3989 node3989Labels = 0 := by
  exact mixedMoment_alpha B hF node3989 node3989Labels 1 permutation158
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

theorem sound3971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3971 node3971Labels = Sparse.eval nodeValue3971 (mixedVector B) := by
  simpa only [nodeValue3971, Sparse.eval_nil] using zero3971 B _hB _hF

theorem sound3972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3972 node3972Labels = Sparse.eval nodeValue3972 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3972) = mixedMoment B node3972 node3972Labels := rfl
  simpa [nodeValue3972, Sparse.eval] using hc.symm

theorem sound3986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3986 node3986Labels = Sparse.eval nodeValue3986 (mixedVector B) := by
  simpa only [nodeValue3986, Sparse.eval_nil] using zero3986 B _hB _hF

theorem sound3989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3989 node3989Labels = Sparse.eval nodeValue3989 (mixedVector B) := by
  simpa only [nodeValue3989, Sparse.eval_nil] using zero3989 B _hB _hF

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

theorem zero5394 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5394 node5394Labels = 0 := by
  exact mixedMoment_order_one B hB node5394 node5394Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5410 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = 0 := by
  exact mixedMoment_order_one B hB node5410 node5410Labels 1
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

theorem sound5394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5394 node5394Labels = Sparse.eval nodeValue5394 (mixedVector B) := by
  simpa only [nodeValue5394, Sparse.eval_nil] using zero5394 B _hB _hF

theorem sound5395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5395 node5395Labels = Sparse.eval nodeValue5395 (mixedVector B) := by
  have h := singleton5395 B _hB
  rw [sound3781 B _hB _hF, sound3794 B _hB _hF] at h
  norm_num [nodeValue5395, nodeValue3781, nodeValue3794, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5397 node5397Labels = Sparse.eval nodeValue5397 (mixedVector B) := by
  have h := singleton5397 B _hB
  rw [sound3782 B _hB _hF, sound3796 B _hB _hF] at h
  norm_num [nodeValue5397, nodeValue3782, nodeValue3796, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = Sparse.eval nodeValue5410 (mixedVector B) := by
  simpa only [nodeValue5410, Sparse.eval_nil] using zero5410 B _hB _hF

theorem sound5420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5420 node5420Labels = Sparse.eval nodeValue5420 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5420) = mixedMoment B node5420 node5420Labels := rfl
  simpa [nodeValue5420, Sparse.eval] using hc.symm

theorem sound5421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5421 node5421Labels = Sparse.eval nodeValue5421 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5421) = mixedMoment B node5421 node5421Labels := rfl
  simpa [nodeValue5421, Sparse.eval] using hc.symm

theorem sound5423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5423 node5423Labels = Sparse.eval nodeValue5423 (mixedVector B) := by
  have h := singleton5423 B _hB
  rw [sound3837 B _hB _hF] at h
  norm_num [nodeValue5423, nodeValue3837, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5424 node5424Labels = Sparse.eval nodeValue5424 (mixedVector B) := by
  have h := singleton5424 B _hB
  rw [sound3838 B _hB _hF, sound3843 B _hB _hF] at h
  norm_num [nodeValue5424, nodeValue3838, nodeValue3843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5425 node5425Labels = Sparse.eval nodeValue5425 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5425) = mixedMoment B node5425 node5425Labels := rfl
  simpa [nodeValue5425, Sparse.eval] using hc.symm

theorem sound5430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5430 node5430Labels = Sparse.eval nodeValue5430 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5430) = mixedMoment B node5430 node5430Labels := rfl
  simpa [nodeValue5430, Sparse.eval] using hc.symm

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

theorem sound5468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5468 node5468Labels = Sparse.eval nodeValue5468 (mixedVector B) := by
  simpa only [nodeValue5468, Sparse.eval_nil] using zero5468 B _hB _hF

theorem sound5473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5473 node5473Labels = Sparse.eval nodeValue5473 (mixedVector B) := by
  have h := singleton5473 B _hB
  rw [sound3958 B _hB _hF, sound3961 B _hB _hF] at h
  norm_num [nodeValue5473, nodeValue3958, nodeValue3961, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5477 node5477Labels = Sparse.eval nodeValue5477 (mixedVector B) := by
  simpa only [nodeValue5477, Sparse.eval_nil] using zero5477 B _hB _hF

theorem sound5487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5487 node5487Labels = Sparse.eval nodeValue5487 (mixedVector B) := by
  simpa only [nodeValue5487, Sparse.eval_nil] using zero5487 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources33
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1061 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1061 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1061 + difference 0 1) (sourceB1061 + difference 1 0) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1061 + difference 0 1) (sourceB1061 + difference 1 0) sourceC1061) = raw17469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17469; decide +kernel
    rw [ha]
    exact (canonical17469 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1061 + difference 0 2) (sourceB1061 + difference 2 0) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1061 + difference 0 2) (sourceB1061 + difference 2 0) sourceC1061) = raw17470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17470; decide +kernel
    rw [ha]
    exact (canonical17470 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1061 + difference 0 3) (sourceB1061 + difference 3 0) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1061 + difference 0 3) (sourceB1061 + difference 3 0) sourceC1061) = raw17471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17471; decide +kernel
    rw [ha]
    exact (canonical17471 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1061 + difference 0 4) (sourceB1061 + difference 4 0) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1061 + difference 0 4) (sourceB1061 + difference 4 0) sourceC1061) = raw17472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17472; decide +kernel
    rw [ha]
    exact (canonical17472 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1061 + difference 0 5) (sourceB1061 + difference 5 0) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA1061 + difference 0 5) (sourceB1061 + difference 5 0) sourceC1061) = raw17473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17473; decide +kernel
    rw [ha]
    exact (canonical17473 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1061 + difference 1 0) (sourceB1061 + difference 0 1) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1061 + difference 1 0) (sourceB1061 + difference 0 1) sourceC1061) = raw17474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17474; decide +kernel
    rw [ha]
    exact (canonical17474 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1061 + difference 1 2) (sourceB1061 + difference 2 1) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1061 + difference 1 2) (sourceB1061 + difference 2 1) sourceC1061) = raw17475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17475; decide +kernel
    rw [ha]
    exact (canonical17475 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1061 + difference 1 3) (sourceB1061 + difference 3 1) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1061 + difference 1 3) (sourceB1061 + difference 3 1) sourceC1061) = raw17476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17476; decide +kernel
    rw [ha]
    exact (canonical17476 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1061 + difference 1 4) (sourceB1061 + difference 4 1) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1061 + difference 1 4) (sourceB1061 + difference 4 1) sourceC1061) = raw17477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17477; decide +kernel
    rw [ha]
    exact (canonical17477 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1061 + difference 1 5) (sourceB1061 + difference 5 1) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1061 + difference 1 5) (sourceB1061 + difference 5 1) sourceC1061) = raw17478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17478; decide +kernel
    rw [ha]
    exact (canonical17478 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1061 + difference 2 0) (sourceB1061 + difference 0 2) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1061 + difference 2 0) (sourceB1061 + difference 0 2) sourceC1061) = raw17479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17479; decide +kernel
    rw [ha]
    exact (canonical17479 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1061 + difference 2 1) (sourceB1061 + difference 1 2) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1061 + difference 2 1) (sourceB1061 + difference 1 2) sourceC1061) = raw17480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17480; decide +kernel
    rw [ha]
    exact (canonical17480 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1061 + difference 2 3) (sourceB1061 + difference 3 2) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5420) := by
    have ha : (tripleCharges (sourceA1061 + difference 2 3) (sourceB1061 + difference 3 2) sourceC1061) = raw17481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17481; decide +kernel
    rw [ha]
    exact (canonical17481 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1061 + difference 2 4) (sourceB1061 + difference 4 2) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1061 + difference 2 4) (sourceB1061 + difference 4 2) sourceC1061) = raw17482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17482; decide +kernel
    rw [ha]
    exact (canonical17482 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1061 + difference 2 5) (sourceB1061 + difference 5 2) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1061 + difference 2 5) (sourceB1061 + difference 5 2) sourceC1061) = raw17483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17483; decide +kernel
    rw [ha]
    exact (canonical17483 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1061 + difference 3 0) (sourceB1061 + difference 0 3) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1061 + difference 3 0) (sourceB1061 + difference 0 3) sourceC1061) = raw17484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17484; decide +kernel
    rw [ha]
    exact (canonical17484 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1061 + difference 3 1) (sourceB1061 + difference 1 3) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1061 + difference 3 1) (sourceB1061 + difference 1 3) sourceC1061) = raw16857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw16857; decide +kernel
    rw [ha]
    exact (canonical16857 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1061 + difference 3 2) (sourceB1061 + difference 2 3) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA1061 + difference 3 2) (sourceB1061 + difference 2 3) sourceC1061) = raw17125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17125; decide +kernel
    rw [ha]
    exact (canonical17125 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1061 + difference 3 4) (sourceB1061 + difference 4 3) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1061 + difference 3 4) (sourceB1061 + difference 4 3) sourceC1061) = raw16843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw16843; decide +kernel
    rw [ha]
    exact (canonical16843 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1061 + difference 3 5) (sourceB1061 + difference 5 3) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1061 + difference 3 5) (sourceB1061 + difference 5 3) sourceC1061) = raw17231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17231; decide +kernel
    rw [ha]
    exact (canonical17231 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1061 + difference 4 0) (sourceB1061 + difference 0 4) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1061 + difference 4 0) (sourceB1061 + difference 0 4) sourceC1061) = raw17485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17485; decide +kernel
    rw [ha]
    exact (canonical17485 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1061 + difference 4 1) (sourceB1061 + difference 1 4) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5468) := by
    have ha : (tripleCharges (sourceA1061 + difference 4 1) (sourceB1061 + difference 1 4) sourceC1061) = raw17486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17486; decide +kernel
    rw [ha]
    exact (canonical17486 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1061 + difference 4 2) (sourceB1061 + difference 2 4) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1061 + difference 4 2) (sourceB1061 + difference 2 4) sourceC1061) = raw17487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17487; decide +kernel
    rw [ha]
    exact (canonical17487 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1061 + difference 4 3) (sourceB1061 + difference 3 4) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1061 + difference 4 3) (sourceB1061 + difference 3 4) sourceC1061) = raw17488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17488; decide +kernel
    rw [ha]
    exact (canonical17488 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1061 + difference 4 5) (sourceB1061 + difference 5 4) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1061 + difference 4 5) (sourceB1061 + difference 5 4) sourceC1061) = raw17489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17489; decide +kernel
    rw [ha]
    exact (canonical17489 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1061 + difference 5 0) (sourceB1061 + difference 0 5) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5394) := by
    have ha : (tripleCharges (sourceA1061 + difference 5 0) (sourceB1061 + difference 0 5) sourceC1061) = raw17490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17490; decide +kernel
    rw [ha]
    exact (canonical17490 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1061 + difference 5 1) (sourceB1061 + difference 1 5) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1061 + difference 5 1) (sourceB1061 + difference 1 5) sourceC1061) = raw17491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17491; decide +kernel
    rw [ha]
    exact (canonical17491 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1061 + difference 5 2) (sourceB1061 + difference 2 5) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1061 + difference 5 2) (sourceB1061 + difference 2 5) sourceC1061) = raw17492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17492; decide +kernel
    rw [ha]
    exact (canonical17492 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1061 + difference 5 3) (sourceB1061 + difference 3 5) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1061 + difference 5 3) (sourceB1061 + difference 3 5) sourceC1061) = raw17493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17493; decide +kernel
    rw [ha]
    exact (canonical17493 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1061 + difference 5 4) (sourceB1061 + difference 4 5) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1061 + difference 5 4) (sourceB1061 + difference 4 5) sourceC1061) = raw17389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17389; decide +kernel
    rw [ha]
    exact (canonical17389 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1061 sourceB1061 sourceC1061
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1061, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1062 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1062 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1062 + difference 0 1) (sourceB1062 + difference 1 0) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA1062 + difference 0 1) (sourceB1062 + difference 1 0) sourceC1062) = raw17494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17494; decide +kernel
    rw [ha]
    exact (canonical17494 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1062 + difference 0 2) (sourceB1062 + difference 2 0) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA1062 + difference 0 2) (sourceB1062 + difference 2 0) sourceC1062) = raw17495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17495; decide +kernel
    rw [ha]
    exact (canonical17495 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1062 + difference 0 3) (sourceB1062 + difference 3 0) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA1062 + difference 0 3) (sourceB1062 + difference 3 0) sourceC1062) = raw17496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17496; decide +kernel
    rw [ha]
    exact (canonical17496 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1062 + difference 0 4) (sourceB1062 + difference 4 0) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA1062 + difference 0 4) (sourceB1062 + difference 4 0) sourceC1062) = raw17497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17497; decide +kernel
    rw [ha]
    exact (canonical17497 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1062 + difference 0 5) (sourceB1062 + difference 5 0) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4032) := by
    have ha : (tripleCharges (sourceA1062 + difference 0 5) (sourceB1062 + difference 5 0) sourceC1062) = raw17498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17498; decide +kernel
    rw [ha]
    exact (canonical17498 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1062 + difference 1 0) (sourceB1062 + difference 0 1) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA1062 + difference 1 0) (sourceB1062 + difference 0 1) sourceC1062) = raw17499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17499; decide +kernel
    rw [ha]
    exact (canonical17499 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1062 + difference 1 2) (sourceB1062 + difference 2 1) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1062 + difference 1 2) (sourceB1062 + difference 2 1) sourceC1062) = raw17500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17500; decide +kernel
    rw [ha]
    exact (canonical17500 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1062 + difference 1 3) (sourceB1062 + difference 3 1) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1062 + difference 1 3) (sourceB1062 + difference 3 1) sourceC1062) = raw17501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17501; decide +kernel
    rw [ha]
    exact (canonical17501 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1062 + difference 1 4) (sourceB1062 + difference 4 1) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3989) := by
    have ha : (tripleCharges (sourceA1062 + difference 1 4) (sourceB1062 + difference 4 1) sourceC1062) = raw17502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17502; decide +kernel
    rw [ha]
    exact (canonical17502 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1062 + difference 1 5) (sourceB1062 + difference 5 1) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA1062 + difference 1 5) (sourceB1062 + difference 5 1) sourceC1062) = raw17503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17503; decide +kernel
    rw [ha]
    exact (canonical17503 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1062 + difference 2 0) (sourceB1062 + difference 0 2) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA1062 + difference 2 0) (sourceB1062 + difference 0 2) sourceC1062) = raw17504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17504; decide +kernel
    rw [ha]
    exact (canonical17504 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1062 + difference 2 1) (sourceB1062 + difference 1 2) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA1062 + difference 2 1) (sourceB1062 + difference 1 2) sourceC1062) = raw17505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17505; decide +kernel
    rw [ha]
    exact (canonical17505 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1062 + difference 2 3) (sourceB1062 + difference 3 2) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3870) := by
    have ha : (tripleCharges (sourceA1062 + difference 2 3) (sourceB1062 + difference 3 2) sourceC1062) = raw17506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17506; decide +kernel
    rw [ha]
    exact (canonical17506 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1062 + difference 2 4) (sourceB1062 + difference 4 2) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1062 + difference 2 4) (sourceB1062 + difference 4 2) sourceC1062) = raw17507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17507; decide +kernel
    rw [ha]
    exact (canonical17507 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1062 + difference 2 5) (sourceB1062 + difference 5 2) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA1062 + difference 2 5) (sourceB1062 + difference 5 2) sourceC1062) = raw17508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17508; decide +kernel
    rw [ha]
    exact (canonical17508 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1062 + difference 3 0) (sourceB1062 + difference 0 3) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA1062 + difference 3 0) (sourceB1062 + difference 0 3) sourceC1062) = raw17509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17509; decide +kernel
    rw [ha]
    exact (canonical17509 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1062 + difference 3 1) (sourceB1062 + difference 1 3) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1062 + difference 3 1) (sourceB1062 + difference 1 3) sourceC1062) = raw16884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw16884; decide +kernel
    rw [ha]
    exact (canonical16884 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1062 + difference 3 2) (sourceB1062 + difference 2 3) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3986) := by
    have ha : (tripleCharges (sourceA1062 + difference 3 2) (sourceB1062 + difference 2 3) sourceC1062) = raw17510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17510; decide +kernel
    rw [ha]
    exact (canonical17510 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1062 + difference 3 4) (sourceB1062 + difference 4 3) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1062 + difference 3 4) (sourceB1062 + difference 4 3) sourceC1062) = raw16870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw16870; decide +kernel
    rw [ha]
    exact (canonical16870 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1062 + difference 3 5) (sourceB1062 + difference 5 3) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA1062 + difference 3 5) (sourceB1062 + difference 5 3) sourceC1062) = raw17511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17511; decide +kernel
    rw [ha]
    exact (canonical17511 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1062 + difference 4 0) (sourceB1062 + difference 0 4) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA1062 + difference 4 0) (sourceB1062 + difference 0 4) sourceC1062) = raw17512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17512; decide +kernel
    rw [ha]
    exact (canonical17512 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1062 + difference 4 1) (sourceB1062 + difference 1 4) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3950) := by
    have ha : (tripleCharges (sourceA1062 + difference 4 1) (sourceB1062 + difference 1 4) sourceC1062) = raw17513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17513; decide +kernel
    rw [ha]
    exact (canonical17513 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1062 + difference 4 2) (sourceB1062 + difference 2 4) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1062 + difference 4 2) (sourceB1062 + difference 2 4) sourceC1062) = raw17514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17514; decide +kernel
    rw [ha]
    exact (canonical17514 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1062 + difference 4 3) (sourceB1062 + difference 3 4) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA1062 + difference 4 3) (sourceB1062 + difference 3 4) sourceC1062) = raw17515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17515; decide +kernel
    rw [ha]
    exact (canonical17515 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1062 + difference 4 5) (sourceB1062 + difference 5 4) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA1062 + difference 4 5) (sourceB1062 + difference 5 4) sourceC1062) = raw17516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17516; decide +kernel
    rw [ha]
    exact (canonical17516 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1062 + difference 5 0) (sourceB1062 + difference 0 5) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3793) := by
    have ha : (tripleCharges (sourceA1062 + difference 5 0) (sourceB1062 + difference 0 5) sourceC1062) = raw17517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17517; decide +kernel
    rw [ha]
    exact (canonical17517 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1062 + difference 5 1) (sourceB1062 + difference 1 5) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA1062 + difference 5 1) (sourceB1062 + difference 1 5) sourceC1062) = raw17518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17518; decide +kernel
    rw [ha]
    exact (canonical17518 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1062 + difference 5 2) (sourceB1062 + difference 2 5) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA1062 + difference 5 2) (sourceB1062 + difference 2 5) sourceC1062) = raw17519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17519; decide +kernel
    rw [ha]
    exact (canonical17519 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1062 + difference 5 3) (sourceB1062 + difference 3 5) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA1062 + difference 5 3) (sourceB1062 + difference 3 5) sourceC1062) = raw17520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17520; decide +kernel
    rw [ha]
    exact (canonical17520 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1062 + difference 5 4) (sourceB1062 + difference 4 5) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA1062 + difference 5 4) (sourceB1062 + difference 4 5) sourceC1062) = raw17412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17412; decide +kernel
    rw [ha]
    exact (canonical17412 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1062 sourceB1062 sourceC1062
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1062, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1068 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1068 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1068 + difference 0 1) (sourceB1068 + difference 1 0) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA1068 + difference 0 1) (sourceB1068 + difference 1 0) sourceC1068) = raw17648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17648; decide +kernel
    rw [ha]
    exact (canonical17648 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1068 + difference 0 2) (sourceB1068 + difference 2 0) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA1068 + difference 0 2) (sourceB1068 + difference 2 0) sourceC1068) = raw17649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17649; decide +kernel
    rw [ha]
    exact (canonical17649 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1068 + difference 0 3) (sourceB1068 + difference 3 0) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA1068 + difference 0 3) (sourceB1068 + difference 3 0) sourceC1068) = raw17650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17650; decide +kernel
    rw [ha]
    exact (canonical17650 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1068 + difference 0 4) (sourceB1068 + difference 4 0) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA1068 + difference 0 4) (sourceB1068 + difference 4 0) sourceC1068) = raw17397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17397; decide +kernel
    rw [ha]
    exact (canonical17397 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1068 + difference 0 5) (sourceB1068 + difference 5 0) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA1068 + difference 0 5) (sourceB1068 + difference 5 0) sourceC1068) = raw17497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17497; decide +kernel
    rw [ha]
    exact (canonical17497 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1068 + difference 1 0) (sourceB1068 + difference 0 1) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA1068 + difference 1 0) (sourceB1068 + difference 0 1) sourceC1068) = raw17651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17651; decide +kernel
    rw [ha]
    exact (canonical17651 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1068 + difference 1 2) (sourceB1068 + difference 2 1) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA1068 + difference 1 2) (sourceB1068 + difference 2 1) sourceC1068) = raw17652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17652; decide +kernel
    rw [ha]
    exact (canonical17652 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1068 + difference 1 3) (sourceB1068 + difference 3 1) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA1068 + difference 1 3) (sourceB1068 + difference 3 1) sourceC1068) = raw17653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17653; decide +kernel
    rw [ha]
    exact (canonical17653 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1068 + difference 1 4) (sourceB1068 + difference 4 1) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA1068 + difference 1 4) (sourceB1068 + difference 4 1) sourceC1068) = raw17401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17401; decide +kernel
    rw [ha]
    exact (canonical17401 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1068 + difference 1 5) (sourceB1068 + difference 5 1) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3989) := by
    have ha : (tripleCharges (sourceA1068 + difference 1 5) (sourceB1068 + difference 5 1) sourceC1068) = raw17502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17502; decide +kernel
    rw [ha]
    exact (canonical17502 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1068 + difference 2 0) (sourceB1068 + difference 0 2) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA1068 + difference 2 0) (sourceB1068 + difference 0 2) sourceC1068) = raw17654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17654; decide +kernel
    rw [ha]
    exact (canonical17654 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1068 + difference 2 1) (sourceB1068 + difference 1 2) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA1068 + difference 2 1) (sourceB1068 + difference 1 2) sourceC1068) = raw17655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17655; decide +kernel
    rw [ha]
    exact (canonical17655 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1068 + difference 2 3) (sourceB1068 + difference 3 2) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA1068 + difference 2 3) (sourceB1068 + difference 3 2) sourceC1068) = raw17656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17656; decide +kernel
    rw [ha]
    exact (canonical17656 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1068 + difference 2 4) (sourceB1068 + difference 4 2) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3866) := by
    have ha : (tripleCharges (sourceA1068 + difference 2 4) (sourceB1068 + difference 4 2) sourceC1068) = raw17405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17405; decide +kernel
    rw [ha]
    exact (canonical17405 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1068 + difference 2 5) (sourceB1068 + difference 5 2) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1068 + difference 2 5) (sourceB1068 + difference 5 2) sourceC1068) = raw17507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17507; decide +kernel
    rw [ha]
    exact (canonical17507 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1068 + difference 3 0) (sourceB1068 + difference 0 3) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA1068 + difference 3 0) (sourceB1068 + difference 0 3) sourceC1068) = raw17410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17410; decide +kernel
    rw [ha]
    exact (canonical17410 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1068 + difference 3 1) (sourceB1068 + difference 1 3) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA1068 + difference 3 1) (sourceB1068 + difference 1 3) sourceC1068) = raw16889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw16889; decide +kernel
    rw [ha]
    exact (canonical16889 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1068 + difference 3 2) (sourceB1068 + difference 2 3) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3861) := by
    have ha : (tripleCharges (sourceA1068 + difference 3 2) (sourceB1068 + difference 2 3) sourceC1068) = raw17411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17411; decide +kernel
    rw [ha]
    exact (canonical17411 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1068 + difference 3 4) (sourceB1068 + difference 4 3) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1068 + difference 3 4) (sourceB1068 + difference 4 3) sourceC1068) = raw17657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17657; decide +kernel
    rw [ha]
    exact (canonical17657 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1068 + difference 3 5) (sourceB1068 + difference 5 3) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1068 + difference 3 5) (sourceB1068 + difference 5 3) sourceC1068) = raw16870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw16870; decide +kernel
    rw [ha]
    exact (canonical16870 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1068 + difference 4 0) (sourceB1068 + difference 0 4) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3793) := by
    have ha : (tripleCharges (sourceA1068 + difference 4 0) (sourceB1068 + difference 0 4) sourceC1068) = raw17517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17517; decide +kernel
    rw [ha]
    exact (canonical17517 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1068 + difference 4 1) (sourceB1068 + difference 1 4) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA1068 + difference 4 1) (sourceB1068 + difference 1 4) sourceC1068) = raw17518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17518; decide +kernel
    rw [ha]
    exact (canonical17518 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1068 + difference 4 2) (sourceB1068 + difference 2 4) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA1068 + difference 4 2) (sourceB1068 + difference 2 4) sourceC1068) = raw17519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17519; decide +kernel
    rw [ha]
    exact (canonical17519 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1068 + difference 4 3) (sourceB1068 + difference 3 4) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA1068 + difference 4 3) (sourceB1068 + difference 3 4) sourceC1068) = raw17520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17520; decide +kernel
    rw [ha]
    exact (canonical17520 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1068 + difference 4 5) (sourceB1068 + difference 5 4) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3971) := by
    have ha : (tripleCharges (sourceA1068 + difference 4 5) (sourceB1068 + difference 5 4) sourceC1068) = raw17658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17658; decide +kernel
    rw [ha]
    exact (canonical17658 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1068 + difference 5 0) (sourceB1068 + difference 0 5) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA1068 + difference 5 0) (sourceB1068 + difference 0 5) sourceC1068) = raw17659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17659; decide +kernel
    rw [ha]
    exact (canonical17659 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1068 + difference 5 1) (sourceB1068 + difference 1 5) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3515) := by
    have ha : (tripleCharges (sourceA1068 + difference 5 1) (sourceB1068 + difference 1 5) sourceC1068) = raw17660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17660; decide +kernel
    rw [ha]
    exact (canonical17660 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1068 + difference 5 2) (sourceB1068 + difference 2 5) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA1068 + difference 5 2) (sourceB1068 + difference 2 5) sourceC1068) = raw17661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17661; decide +kernel
    rw [ha]
    exact (canonical17661 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1068 + difference 5 3) (sourceB1068 + difference 3 5) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA1068 + difference 5 3) (sourceB1068 + difference 3 5) sourceC1068) = raw17662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17662; decide +kernel
    rw [ha]
    exact (canonical17662 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1068 + difference 5 4) (sourceB1068 + difference 4 5) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA1068 + difference 5 4) (sourceB1068 + difference 4 5) sourceC1068) = raw17416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17416; decide +kernel
    rw [ha]
    exact (canonical17416 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1068 sourceB1068 sourceC1068
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1068, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck914 : Integer.Sparse.reindex keyMap MixedData.row914 = numericRow914 := by decide +kernel

theorem numericCheck914 (x : Master → ℝ) : Integer.Sparse.eval numericRow914 x =
    (8640 : ℝ) * reducedSource914 x := by
  norm_num [numericRow914, reducedSource914, Integer.Sparse.eval, Sparse.eval, nodeValue5394, nodeValue5395, nodeValue5397, nodeValue5410, nodeValue5420, nodeValue5421, nodeValue5423, nodeValue5424, nodeValue5425, nodeValue5430, nodeValue5434, nodeValue5445, nodeValue5468, nodeValue5473, nodeValue5477, nodeValue5483, nodeValue5487]
  ring

theorem reindexCheck915 : Integer.Sparse.reindex keyMap MixedData.row915 = numericRow915 := by decide +kernel

theorem numericCheck915 (x : Master → ℝ) : Integer.Sparse.eval numericRow915 x =
    (2160 : ℝ) * reducedSource915 x := by
  norm_num [numericRow915, reducedSource915, Integer.Sparse.eval, Sparse.eval, nodeValue3793, nodeValue3794, nodeValue3796, nodeValue3808, nodeValue3838, nodeValue3870, nodeValue3872, nodeValue3873, nodeValue3880, nodeValue3950, nodeValue3958, nodeValue3972, nodeValue3981, nodeValue3982, nodeValue3986, nodeValue3989, nodeValue3990, nodeValue4032]
  ring

theorem reindexCheck921 : Integer.Sparse.reindex keyMap MixedData.row921 = numericRow921 := by decide +kernel

theorem numericCheck921 (x : Master → ℝ) : Integer.Sparse.eval numericRow921 x =
    (8640 : ℝ) * reducedSource921 x := by
  norm_num [numericRow921, reducedSource921, Integer.Sparse.eval, Sparse.eval, nodeValue3514, nodeValue3515, nodeValue3517, nodeValue3534, nodeValue3558, nodeValue3793, nodeValue3794, nodeValue3795, nodeValue3796, nodeValue3807, nodeValue3808, nodeValue3832, nodeValue3834, nodeValue3837, nodeValue3839, nodeValue3840, nodeValue3841, nodeValue3845, nodeValue3852, nodeValue3853, nodeValue3861, nodeValue3866, nodeValue3871, nodeValue3872, nodeValue3876, nodeValue3880, nodeValue3971, nodeValue3981, nodeValue3989, nodeValue3990]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero914 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource914 (mixedVector B) = 0 := by
  have h5394 : mixedVector B (Sum.inr 5394) = Sparse.eval nodeValue5394 (mixedVector B) := by
    change mixedMoment B node5394 node5394Labels = _
    exact sound5394 B hB hF
  have h5395 : mixedVector B (Sum.inr 5395) = Sparse.eval nodeValue5395 (mixedVector B) := by
    change mixedMoment B node5395 node5395Labels = _
    exact sound5395 B hB hF
  have h5397 : mixedVector B (Sum.inr 5397) = Sparse.eval nodeValue5397 (mixedVector B) := by
    change mixedMoment B node5397 node5397Labels = _
    exact sound5397 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5420 : mixedVector B (Sum.inr 5420) = Sparse.eval nodeValue5420 (mixedVector B) := by
    change mixedMoment B node5420 node5420Labels = _
    exact sound5420 B hB hF
  have h5421 : mixedVector B (Sum.inr 5421) = Sparse.eval nodeValue5421 (mixedVector B) := by
    change mixedMoment B node5421 node5421Labels = _
    exact sound5421 B hB hF
  have h5423 : mixedVector B (Sum.inr 5423) = Sparse.eval nodeValue5423 (mixedVector B) := by
    change mixedMoment B node5423 node5423Labels = _
    exact sound5423 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5425 : mixedVector B (Sum.inr 5425) = Sparse.eval nodeValue5425 (mixedVector B) := by
    change mixedMoment B node5425 node5425Labels = _
    exact sound5425 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5445 : mixedVector B (Sum.inr 5445) = Sparse.eval nodeValue5445 (mixedVector B) := by
    change mixedMoment B node5445 node5445Labels = _
    exact sound5445 B hB hF
  have h5468 : mixedVector B (Sum.inr 5468) = Sparse.eval nodeValue5468 (mixedVector B) := by
    change mixedMoment B node5468 node5468Labels = _
    exact sound5468 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5477 : mixedVector B (Sum.inr 5477) = Sparse.eval nodeValue5477 (mixedVector B) := by
    change mixedMoment B node5477 node5477Labels = _
    exact sound5477 B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483_e B hB hF
  have h5487 : mixedVector B (Sum.inr 5487) = Sparse.eval nodeValue5487 (mixedVector B) := by
    change mixedMoment B node5487 node5487Labels = _
    exact sound5487 B hB hF
  simpa only [sourceForm1061, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5394, h5395, h5397, h5410, h5420, h5421, h5423, h5424, h5425, h5430, h5434, h5445, h5468, h5473, h5477, h5483, h5487, reducedSource914] using sourceEq1061 B hB

theorem rowSound914 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row914 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck914, numericCheck914, reducedZero914 B hB hF, mul_zero]

theorem reducedZero915 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource915 (mixedVector B) = 0 := by
  have h3793 : mixedVector B (Sum.inr 3793) = Sparse.eval nodeValue3793 (mixedVector B) := by
    change mixedMoment B node3793 node3793Labels = _
    exact sound3793 B hB hF
  have h3794 : mixedVector B (Sum.inr 3794) = Sparse.eval nodeValue3794 (mixedVector B) := by
    change mixedMoment B node3794 node3794Labels = _
    exact sound3794 B hB hF
  have h3796 : mixedVector B (Sum.inr 3796) = Sparse.eval nodeValue3796 (mixedVector B) := by
    change mixedMoment B node3796 node3796Labels = _
    exact sound3796 B hB hF
  have h3808 : mixedVector B (Sum.inr 3808) = Sparse.eval nodeValue3808 (mixedVector B) := by
    change mixedMoment B node3808 node3808Labels = _
    exact sound3808 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h3870 : mixedVector B (Sum.inr 3870) = Sparse.eval nodeValue3870 (mixedVector B) := by
    change mixedMoment B node3870 node3870Labels = _
    exact sound3870 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3873 : mixedVector B (Sum.inr 3873) = Sparse.eval nodeValue3873 (mixedVector B) := by
    change mixedMoment B node3873 node3873Labels = _
    exact sound3873 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h3950 : mixedVector B (Sum.inr 3950) = Sparse.eval nodeValue3950 (mixedVector B) := by
    change mixedMoment B node3950 node3950Labels = _
    exact sound3950 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h3972 : mixedVector B (Sum.inr 3972) = Sparse.eval nodeValue3972 (mixedVector B) := by
    change mixedMoment B node3972 node3972Labels = _
    exact sound3972 B hB hF
  have h3981 : mixedVector B (Sum.inr 3981) = Sparse.eval nodeValue3981 (mixedVector B) := by
    change mixedMoment B node3981 node3981Labels = _
    exact sound3981_e B hB hF
  have h3982 : mixedVector B (Sum.inr 3982) = Sparse.eval nodeValue3982 (mixedVector B) := by
    change mixedMoment B node3982 node3982Labels = _
    exact sound3982_e B hB hF
  have h3986 : mixedVector B (Sum.inr 3986) = Sparse.eval nodeValue3986 (mixedVector B) := by
    change mixedMoment B node3986 node3986Labels = _
    exact sound3986 B hB hF
  have h3989 : mixedVector B (Sum.inr 3989) = Sparse.eval nodeValue3989 (mixedVector B) := by
    change mixedMoment B node3989 node3989Labels = _
    exact sound3989 B hB hF
  have h3990 : mixedVector B (Sum.inr 3990) = Sparse.eval nodeValue3990 (mixedVector B) := by
    change mixedMoment B node3990 node3990Labels = _
    exact sound3990_e B hB hF
  have h4032 : mixedVector B (Sum.inr 4032) = Sparse.eval nodeValue4032 (mixedVector B) := by
    change mixedMoment B node4032 node4032Labels = _
    exact sound4032_e B hB hF
  simpa only [sourceForm1062, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3793, h3794, h3796, h3808, h3838, h3870, h3872, h3873, h3880, h3950, h3958, h3972, h3981, h3982, h3986, h3989, h3990, h4032, reducedSource915] using sourceEq1062 B hB

theorem rowSound915 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row915 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck915, numericCheck915, reducedZero915 B hB hF, mul_zero]

theorem reducedZero921 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource921 (mixedVector B) = 0 := by
  have h3514 : mixedVector B (Sum.inr 3514) = Sparse.eval nodeValue3514 (mixedVector B) := by
    change mixedMoment B node3514 node3514Labels = _
    exact sound3514 B hB hF
  have h3515 : mixedVector B (Sum.inr 3515) = Sparse.eval nodeValue3515 (mixedVector B) := by
    change mixedMoment B node3515 node3515Labels = _
    exact sound3515 B hB hF
  have h3517 : mixedVector B (Sum.inr 3517) = Sparse.eval nodeValue3517 (mixedVector B) := by
    change mixedMoment B node3517 node3517Labels = _
    exact sound3517 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3558 : mixedVector B (Sum.inr 3558) = Sparse.eval nodeValue3558 (mixedVector B) := by
    change mixedMoment B node3558 node3558Labels = _
    exact sound3558 B hB hF
  have h3793 : mixedVector B (Sum.inr 3793) = Sparse.eval nodeValue3793 (mixedVector B) := by
    change mixedMoment B node3793 node3793Labels = _
    exact sound3793 B hB hF
  have h3794 : mixedVector B (Sum.inr 3794) = Sparse.eval nodeValue3794 (mixedVector B) := by
    change mixedMoment B node3794 node3794Labels = _
    exact sound3794 B hB hF
  have h3795 : mixedVector B (Sum.inr 3795) = Sparse.eval nodeValue3795 (mixedVector B) := by
    change mixedMoment B node3795 node3795Labels = _
    exact sound3795 B hB hF
  have h3796 : mixedVector B (Sum.inr 3796) = Sparse.eval nodeValue3796 (mixedVector B) := by
    change mixedMoment B node3796 node3796Labels = _
    exact sound3796 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3808 : mixedVector B (Sum.inr 3808) = Sparse.eval nodeValue3808 (mixedVector B) := by
    change mixedMoment B node3808 node3808Labels = _
    exact sound3808 B hB hF
  have h3832 : mixedVector B (Sum.inr 3832) = Sparse.eval nodeValue3832 (mixedVector B) := by
    change mixedMoment B node3832 node3832Labels = _
    exact sound3832 B hB hF
  have h3834 : mixedVector B (Sum.inr 3834) = Sparse.eval nodeValue3834 (mixedVector B) := by
    change mixedMoment B node3834 node3834Labels = _
    exact sound3834 B hB hF
  have h3837 : mixedVector B (Sum.inr 3837) = Sparse.eval nodeValue3837 (mixedVector B) := by
    change mixedMoment B node3837 node3837Labels = _
    exact sound3837 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3841 : mixedVector B (Sum.inr 3841) = Sparse.eval nodeValue3841 (mixedVector B) := by
    change mixedMoment B node3841 node3841Labels = _
    exact sound3841 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h3852 : mixedVector B (Sum.inr 3852) = Sparse.eval nodeValue3852 (mixedVector B) := by
    change mixedMoment B node3852 node3852Labels = _
    exact sound3852_e B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853_e B hB hF
  have h3861 : mixedVector B (Sum.inr 3861) = Sparse.eval nodeValue3861 (mixedVector B) := by
    change mixedMoment B node3861 node3861Labels = _
    exact sound3861 B hB hF
  have h3866 : mixedVector B (Sum.inr 3866) = Sparse.eval nodeValue3866 (mixedVector B) := by
    change mixedMoment B node3866 node3866Labels = _
    exact sound3866 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h3971 : mixedVector B (Sum.inr 3971) = Sparse.eval nodeValue3971 (mixedVector B) := by
    change mixedMoment B node3971 node3971Labels = _
    exact sound3971 B hB hF
  have h3981 : mixedVector B (Sum.inr 3981) = Sparse.eval nodeValue3981 (mixedVector B) := by
    change mixedMoment B node3981 node3981Labels = _
    exact sound3981_e B hB hF
  have h3989 : mixedVector B (Sum.inr 3989) = Sparse.eval nodeValue3989 (mixedVector B) := by
    change mixedMoment B node3989 node3989Labels = _
    exact sound3989 B hB hF
  have h3990 : mixedVector B (Sum.inr 3990) = Sparse.eval nodeValue3990 (mixedVector B) := by
    change mixedMoment B node3990 node3990Labels = _
    exact sound3990_e B hB hF
  simpa only [sourceForm1068, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3514, h3515, h3517, h3534, h3558, h3793, h3794, h3795, h3796, h3807, h3808, h3832, h3834, h3837, h3839, h3840, h3841, h3845, h3852, h3853, h3861, h3866, h3871, h3872, h3876, h3880, h3971, h3981, h3989, h3990, reducedSource921] using sourceEq1068 B hB

theorem rowSound921 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row921 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck921, numericCheck921, reducedZero921 B hB hF, mul_zero]

theorem sourceRowsAt912 : MixedData.sourceRows (912 : Fin 2425) =
    MixedData.row912 := by decide +kernel

theorem sourceRowsAt913 : MixedData.sourceRows (913 : Fin 2425) =
    MixedData.row913 := by decide +kernel

theorem sourceRowsAt914 : MixedData.sourceRows (914 : Fin 2425) =
    MixedData.row914 := by decide +kernel

theorem sourceRowsAt915 : MixedData.sourceRows (915 : Fin 2425) =
    MixedData.row915 := by decide +kernel

theorem sourceRowsAt916 : MixedData.sourceRows (916 : Fin 2425) =
    MixedData.row916 := by decide +kernel

theorem sourceRowsAt917 : MixedData.sourceRows (917 : Fin 2425) =
    MixedData.row917 := by decide +kernel

theorem sourceRowsAt918 : MixedData.sourceRows (918 : Fin 2425) =
    MixedData.row918 := by decide +kernel

theorem sourceRowsAt919 : MixedData.sourceRows (919 : Fin 2425) =
    MixedData.row919 := by decide +kernel

theorem sourceRowsAt920 : MixedData.sourceRows (920 : Fin 2425) =
    MixedData.row920 := by decide +kernel

theorem sourceRowsAt921 : MixedData.sourceRows (921 : Fin 2425) =
    MixedData.row921 := by decide +kernel

theorem sourceRowsAt922 : MixedData.sourceRows (922 : Fin 2425) =
    MixedData.row922 := by decide +kernel

theorem sourceRowsAt923 : MixedData.sourceRows (923 : Fin 2425) =
    MixedData.row923 := by decide +kernel

theorem sourceRowsAt924 : MixedData.sourceRows (924 : Fin 2425) =
    MixedData.row924 := by decide +kernel

theorem sourceRowsAt925 : MixedData.sourceRows (925 : Fin 2425) =
    MixedData.row925 := by decide +kernel

theorem sourceRowsAt926 : MixedData.sourceRows (926 : Fin 2425) =
    MixedData.row926 := by decide +kernel

theorem sourceRowsAt927 : MixedData.sourceRows (927 : Fin 2425) =
    MixedData.row927 := by decide +kernel

theorem chunkSound57_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 57) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 912 ∨ k.val = 913 ∨ k.val = 914 ∨ k.val = 915 ∨ k.val = 916 ∨ k.val = 917 ∨ k.val = 918 ∨ k.val = 919 ∨ k.val = 920 ∨ k.val = 921 ∨ k.val = 922 ∨ k.val = 923 ∨ k.val = 924 ∨ k.val = 925 ∨ k.val = 926 ∨ k.val = 927 := by omega
  rcases heq with h912 | h913 | h914 | h915 | h916 | h917 | h918 | h919 | h920 | h921 | h922 | h923 | h924 | h925 | h926 | h927
  · have he : k = (912 : Fin 2425) := Fin.ext h912
    subst k
    rw [sourceRowsAt912]
    exact rowSound912_e B hB hF
  · have he : k = (913 : Fin 2425) := Fin.ext h913
    subst k
    rw [sourceRowsAt913]
    exact rowSound913_e B hB hF
  · have he : k = (914 : Fin 2425) := Fin.ext h914
    subst k
    rw [sourceRowsAt914]
    exact rowSound914 B hB hF
  · have he : k = (915 : Fin 2425) := Fin.ext h915
    subst k
    rw [sourceRowsAt915]
    exact rowSound915 B hB hF
  · have he : k = (916 : Fin 2425) := Fin.ext h916
    subst k
    rw [sourceRowsAt916]
    exact rowSound916_e B hB hF
  · have he : k = (917 : Fin 2425) := Fin.ext h917
    subst k
    rw [sourceRowsAt917]
    exact rowSound917_e B hB hF
  · have he : k = (918 : Fin 2425) := Fin.ext h918
    subst k
    rw [sourceRowsAt918]
    exact rowSound918_e B hB hF
  · have he : k = (919 : Fin 2425) := Fin.ext h919
    subst k
    rw [sourceRowsAt919]
    exact rowSound919_e B hB hF
  · have he : k = (920 : Fin 2425) := Fin.ext h920
    subst k
    rw [sourceRowsAt920]
    exact rowSound920_e B hB hF
  · have he : k = (921 : Fin 2425) := Fin.ext h921
    subst k
    rw [sourceRowsAt921]
    exact rowSound921 B hB hF
  · have he : k = (922 : Fin 2425) := Fin.ext h922
    subst k
    rw [sourceRowsAt922]
    exact rowSound922_e B hB hF
  · have he : k = (923 : Fin 2425) := Fin.ext h923
    subst k
    rw [sourceRowsAt923]
    exact rowSound923_e B hB hF
  · have he : k = (924 : Fin 2425) := Fin.ext h924
    subst k
    rw [sourceRowsAt924]
    exact rowSound924_e B hB hF
  · have he : k = (925 : Fin 2425) := Fin.ext h925
    subst k
    rw [sourceRowsAt925]
    exact rowSound925_e B hB hF
  · have he : k = (926 : Fin 2425) := Fin.ext h926
    subst k
    rw [sourceRowsAt926]
    exact rowSound926_e B hB hF
  · have he : k = (927 : Fin 2425) := Fin.ext h927
    subst k
    rw [sourceRowsAt927]
    exact rowSound927_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57_e_oai
