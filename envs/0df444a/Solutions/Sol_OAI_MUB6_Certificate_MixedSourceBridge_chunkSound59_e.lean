-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:24:48.362913+00:00
-- url     : https://prove2.me/submissions/4e23c093-4c68-4464-a460-d90fcc99438e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E129
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3852_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5415_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5433_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5500_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound947_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound948_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound949_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound950_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound951_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound952_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound953_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound954_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound956_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound957_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound958_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound959_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1710 raw1710Labels = mixedMoment B node4778 node4778Labels := by
  calc
    mixedMoment B raw1710 raw1710Labels = mixedMoment B raw1710step0 raw1710step0Labels := by
      have ha : raw1710step0 = (fun i j => raw1710 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1710step0 raw1710; decide +kernel
      have hl : raw1710step0Labels = raw1710Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1710 raw1710Labels permutation152 permutation4
    mixedMoment B raw1710step0 raw1710step0Labels = mixedMoment B raw1710step1 raw1710step1Labels := by
      have ha : raw1710step1 = raw1710step0 := by apply Matrix.ext; unfold raw1710step1 raw1710step0; decide +kernel
      have hl : raw1710step0Labels = labelEmbedding7 ∘ raw1710step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1710step0 raw1710step0Labels raw1710step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4778 node4778Labels := by rfl

theorem canonical1711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1711 raw1711Labels = mixedMoment B node1986 node1986Labels := by
  calc
    mixedMoment B raw1711 raw1711Labels = mixedMoment B raw1711step0 raw1711step0Labels := by
      have ha : raw1711step0 = (fun i j => raw1711 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1711step0 raw1711; decide +kernel
      have hl : raw1711step0Labels = raw1711Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1711 raw1711Labels permutation152 permutation4
    _ = mixedMoment B node1986 node1986Labels := by rfl

theorem canonical1712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1712 raw1712Labels = mixedMoment B node1986 node1986Labels := by
  calc
    mixedMoment B raw1712 raw1712Labels = mixedMoment B raw1712step0 raw1712step0Labels := by
      have ha : raw1712step0 = (fun i j => raw1712 (permutation662 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1712step0 raw1712; decide +kernel
      have hl : raw1712step0Labels = raw1712Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1712 raw1712Labels permutation662 permutation6
    mixedMoment B raw1712step0 raw1712step0Labels = mixedMoment B raw1712step1 raw1712step1Labels := by
      have ha : raw1712step1 = raw1712step0 := by apply Matrix.ext; unfold raw1712step1 raw1712step0; decide +kernel
      have hl : raw1712step0Labels = labelEmbedding1 ∘ raw1712step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1712step0 raw1712step0Labels raw1712step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1986 node1986Labels := by rfl

theorem canonical1716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1716 raw1716Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw1716 raw1716Labels = mixedMoment B raw1716step0 raw1716step0Labels := by
      have ha : raw1716step0 = (fun i j => raw1716 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1716step0 raw1716; decide +kernel
      have hl : raw1716step0Labels = raw1716Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1716 raw1716Labels permutation152 permutation4
    mixedMoment B raw1716step0 raw1716step0Labels = mixedMoment B raw1716step1 raw1716step1Labels := by
      have ha : raw1716step1 = raw1716step0 := by apply Matrix.ext; unfold raw1716step1 raw1716step0; decide +kernel
      have hl : raw1716step0Labels = labelEmbedding7 ∘ raw1716step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1716step0 raw1716step0Labels raw1716step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

theorem canonical1717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1717 raw1717Labels = mixedMoment B node1990 node1990Labels := by
  calc
    mixedMoment B raw1717 raw1717Labels = mixedMoment B raw1717step0 raw1717step0Labels := by
      have ha : raw1717step0 = (fun i j => raw1717 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1717step0 raw1717; decide +kernel
      have hl : raw1717step0Labels = raw1717Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1717 raw1717Labels permutation152 permutation4
    _ = mixedMoment B node1990 node1990Labels := by rfl

theorem canonical1718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1718 raw1718Labels = mixedMoment B node1997 node1997Labels := by
  calc
    mixedMoment B raw1718 raw1718Labels = mixedMoment B raw1718step0 raw1718step0Labels := by
      have ha : raw1718step0 = (fun i j => raw1718 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1718step0 raw1718; decide +kernel
      have hl : raw1718step0Labels = raw1718Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1718 raw1718Labels permutation176 permutation6
    mixedMoment B raw1718step0 raw1718step0Labels = mixedMoment B raw1718step1 raw1718step1Labels := by
      have ha : raw1718step1 = -raw1718step0 := by apply Matrix.ext; change ∀ i j, raw1718step1 i j = -(raw1718step0 i j); unfold raw1718step1 raw1718step0; decide +kernel
      have hl : raw1718step1Labels = raw1718step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1718step1 raw1718step1Labels = mixedMoment B raw1718step2 raw1718step2Labels := by
      have ha : raw1718step2 = raw1718step1 := by apply Matrix.ext; unfold raw1718step2 raw1718step1; decide +kernel
      have hl : raw1718step1Labels = labelEmbedding1 ∘ raw1718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1718step1 raw1718step1Labels raw1718step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1997 node1997Labels := by rfl

theorem canonical1731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1731 raw1731Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw1731 raw1731Labels = mixedMoment B raw1731step0 raw1731step0Labels := by
      have ha : raw1731step0 = (fun i j => raw1731 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1731step0 raw1731; decide +kernel
      have hl : raw1731step0Labels = raw1731Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1731 raw1731Labels permutation152 permutation4
    mixedMoment B raw1731step0 raw1731step0Labels = mixedMoment B raw1731step1 raw1731step1Labels := by
      have ha : raw1731step1 = raw1731step0 := by apply Matrix.ext; unfold raw1731step1 raw1731step0; decide +kernel
      have hl : raw1731step0Labels = labelEmbedding7 ∘ raw1731step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1731step0 raw1731step0Labels raw1731step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

theorem canonical1732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1732 raw1732Labels = mixedMoment B node2019 node2019Labels := by
  calc
    mixedMoment B raw1732 raw1732Labels = mixedMoment B raw1732step0 raw1732step0Labels := by
      have ha : raw1732step0 = (fun i j => raw1732 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1732step0 raw1732; decide +kernel
      have hl : raw1732step0Labels = raw1732Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1732 raw1732Labels permutation152 permutation4
    _ = mixedMoment B node2019 node2019Labels := by rfl

theorem canonical1733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1733 raw1733Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw1733 raw1733Labels = mixedMoment B raw1733step0 raw1733step0Labels := by
      have ha : raw1733step0 = (fun i j => raw1733 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1733step0 raw1733; decide +kernel
      have hl : raw1733step0Labels = raw1733Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1733 raw1733Labels permutation160 permutation6
    mixedMoment B raw1733step0 raw1733step0Labels = mixedMoment B raw1733step1 raw1733step1Labels := by
      have ha : raw1733step1 = -raw1733step0 := by apply Matrix.ext; change ∀ i j, raw1733step1 i j = -(raw1733step0 i j); unfold raw1733step1 raw1733step0; decide +kernel
      have hl : raw1733step1Labels = raw1733step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1733step1 raw1733step1Labels = mixedMoment B raw1733step2 raw1733step2Labels := by
      have ha : raw1733step2 = raw1733step1 := by apply Matrix.ext; unfold raw1733step2 raw1733step1; decide +kernel
      have hl : raw1733step1Labels = labelEmbedding1 ∘ raw1733step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1733step1 raw1733step1Labels raw1733step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2190 node2190Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical142
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18212 raw18212Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18212 raw18212Labels = mixedMoment B raw18212step0 raw18212step0Labels := by
      have ha : raw18212step0 = (fun i j => raw18212 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18212step0 raw18212; decide +kernel
      have hl : raw18212step0Labels = raw18212Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18212 raw18212Labels permutation681 permutation2
    mixedMoment B raw18212step0 raw18212step0Labels = mixedMoment B raw18212step1 raw18212step1Labels := by
      have ha : raw18212step1 = -raw18212step0 := by apply Matrix.ext; change ∀ i j, raw18212step1 i j = -(raw18212step0 i j); unfold raw18212step1 raw18212step0; decide +kernel
      have hl : raw18212step1Labels = raw18212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical18213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18213 raw18213Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18213 raw18213Labels = mixedMoment B raw18213step0 raw18213step0Labels := by
      have ha : raw18213step0 = (fun i j => raw18213 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18213step0 raw18213; decide +kernel
      have hl : raw18213step0Labels = raw18213Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18213 raw18213Labels permutation688 permutation2
    mixedMoment B raw18213step0 raw18213step0Labels = mixedMoment B raw18213step1 raw18213step1Labels := by
      have ha : raw18213step1 = -raw18213step0 := by apply Matrix.ext; change ∀ i j, raw18213step1 i j = -(raw18213step0 i j); unfold raw18213step1 raw18213step0; decide +kernel
      have hl : raw18213step1Labels = raw18213step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical18214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18214 raw18214Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18214 raw18214Labels = mixedMoment B raw18214step0 raw18214step0Labels := by
      have ha : raw18214step0 = (fun i j => raw18214 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18214step0 raw18214; decide +kernel
      have hl : raw18214step0Labels = raw18214Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18214 raw18214Labels permutation644 permutation7
    mixedMoment B raw18214step0 raw18214step0Labels = mixedMoment B raw18214step1 raw18214step1Labels := by
      have ha : raw18214step1 = raw18214step0 := by apply Matrix.ext; unfold raw18214step1 raw18214step0; decide +kernel
      have hl : raw18214step0Labels = labelEmbedding10 ∘ raw18214step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18214step0 raw18214step0Labels raw18214step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical18215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18215 raw18215Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18215 raw18215Labels = mixedMoment B raw18215step0 raw18215step0Labels := by
      have hz : ∀ j, raw18215 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18215step0 = (fun i j => raw18215 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18215step0 raw18215; decide +kernel
      have hl : raw18215step0Labels = raw18215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18215 raw18215Labels permutation520 hz
    mixedMoment B raw18215step0 raw18215step0Labels = mixedMoment B raw18215step1 raw18215step1Labels := by
      have ha : raw18215step1 = (fun i j => raw18215step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18215step1 raw18215step0; decide +kernel
      have hl : raw18215step1Labels = raw18215step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18215step0 raw18215step0Labels permutation143 permutation7
    mixedMoment B raw18215step1 raw18215step1Labels = mixedMoment B raw18215step2 raw18215step2Labels := by
      have ha : raw18215step2 = raw18215step1 := by apply Matrix.ext; unfold raw18215step2 raw18215step1; decide +kernel
      have hl : raw18215step1Labels = labelEmbedding10 ∘ raw18215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18215step1 raw18215step1Labels raw18215step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical18216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18216 raw18216Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw18216 raw18216Labels = mixedMoment B raw18216step0 raw18216step0Labels := by
      have ha : raw18216step0 = (fun i j => raw18216 (permutation634 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18216step0 raw18216; decide +kernel
      have hl : raw18216step0Labels = raw18216Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18216 raw18216Labels permutation634 permutation6
    mixedMoment B raw18216step0 raw18216step0Labels = mixedMoment B raw18216step1 raw18216step1Labels := by
      have ha : raw18216step1 = raw18216step0 := by apply Matrix.ext; unfold raw18216step1 raw18216step0; decide +kernel
      have hl : raw18216step0Labels = labelEmbedding9 ∘ raw18216step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18216step0 raw18216step0Labels raw18216step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

theorem canonical18217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18217 raw18217Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw18217 raw18217Labels = mixedMoment B raw18217step0 raw18217step0Labels := by
      have hz : ∀ j, raw18217 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18217step0 = (fun i j => raw18217 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18217step0 raw18217; decide +kernel
      have hl : raw18217step0Labels = raw18217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18217 raw18217Labels permutation265 hz
    mixedMoment B raw18217step0 raw18217step0Labels = mixedMoment B raw18217step1 raw18217step1Labels := by
      have ha : raw18217step1 = (fun i j => raw18217step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18217step1 raw18217step0; decide +kernel
      have hl : raw18217step1Labels = raw18217step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18217step0 raw18217step0Labels permutation151 permutation2
    mixedMoment B raw18217step1 raw18217step1Labels = mixedMoment B raw18217step2 raw18217step2Labels := by
      have ha : raw18217step2 = -raw18217step1 := by apply Matrix.ext; change ∀ i j, raw18217step2 i j = -(raw18217step1 i j); unfold raw18217step2 raw18217step1; decide +kernel
      have hl : raw18217step2Labels = raw18217step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5432 node5432Labels := by rfl

theorem canonical18218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18218 raw18218Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw18218 raw18218Labels = mixedMoment B raw18218step0 raw18218step0Labels := by
      have hz : ∀ j, raw18218 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18218step0 = (fun i j => raw18218 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18218step0 raw18218; decide +kernel
      have hl : raw18218step0Labels = raw18218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18218 raw18218Labels permutation265 hz
    mixedMoment B raw18218step0 raw18218step0Labels = mixedMoment B raw18218step1 raw18218step1Labels := by
      have ha : raw18218step1 = (fun i j => raw18218step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18218step1 raw18218step0; decide +kernel
      have hl : raw18218step1Labels = raw18218step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18218step0 raw18218step0Labels permutation38 permutation2
    _ = mixedMoment B node5409 node5409Labels := by rfl

theorem canonical18219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18219 raw18219Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw18219 raw18219Labels = mixedMoment B raw18219step0 raw18219step0Labels := by
      have hz : ∀ j, raw18219 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18219step0 = (fun i j => raw18219 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18219step0 raw18219; decide +kernel
      have hl : raw18219step0Labels = raw18219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18219 raw18219Labels permutation520 hz
    mixedMoment B raw18219step0 raw18219step0Labels = mixedMoment B raw18219step1 raw18219step1Labels := by
      have hz : ∀ j, raw18219step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw18219step1 = (fun i j => raw18219step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw18219step1 raw18219step0; decide +kernel
      have hl : raw18219step1Labels = raw18219step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18219step0 raw18219step0Labels permutation56 hz
    mixedMoment B raw18219step1 raw18219step1Labels = mixedMoment B raw18219step2 raw18219step2Labels := by
      have ha : raw18219step2 = (fun i j => raw18219step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18219step2 raw18219step1; decide +kernel
      have hl : raw18219step2Labels = raw18219step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18219step1 raw18219step1Labels permutation29 permutation7
    mixedMoment B raw18219step2 raw18219step2Labels = mixedMoment B raw18219step3 raw18219step3Labels := by
      have ha : raw18219step3 = raw18219step2 := by apply Matrix.ext; unfold raw18219step3 raw18219step2; decide +kernel
      have hl : raw18219step2Labels = labelEmbedding10 ∘ raw18219step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18219step2 raw18219step2Labels raw18219step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5441 node5441Labels := by rfl

theorem canonical18220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18220 raw18220Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw18220 raw18220Labels = mixedMoment B raw18220step0 raw18220step0Labels := by
      have ha : raw18220step0 = (fun i j => raw18220 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18220step0 raw18220; decide +kernel
      have hl : raw18220step0Labels = raw18220Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18220 raw18220Labels permutation160 permutation2
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical18221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18221 raw18221Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw18221 raw18221Labels = mixedMoment B raw18221step0 raw18221step0Labels := by
      have ha : raw18221step0 = (fun i j => raw18221 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18221step0 raw18221; decide +kernel
      have hl : raw18221step0Labels = raw18221Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18221 raw18221Labels permutation160 permutation2
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical18222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18222 raw18222Labels = mixedMoment B node5394 node5394Labels := by
  calc
    mixedMoment B raw18222 raw18222Labels = mixedMoment B raw18222step0 raw18222step0Labels := by
      have ha : raw18222step0 = (fun i j => raw18222 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18222step0 raw18222; decide +kernel
      have hl : raw18222step0Labels = raw18222Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18222 raw18222Labels permutation202 permutation2
    _ = mixedMoment B node5394 node5394Labels := by rfl

theorem canonical18223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18223 raw18223Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw18223 raw18223Labels = mixedMoment B raw18223step0 raw18223step0Labels := by
      have hz : ∀ j, raw18223 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18223step0 = (fun i j => raw18223 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18223step0 raw18223; decide +kernel
      have hl : raw18223step0Labels = raw18223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18223 raw18223Labels permutation520 hz
    mixedMoment B raw18223step0 raw18223step0Labels = mixedMoment B raw18223step1 raw18223step1Labels := by
      have ha : raw18223step1 = (fun i j => raw18223step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18223step1 raw18223step0; decide +kernel
      have hl : raw18223step1Labels = raw18223step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18223step0 raw18223step0Labels permutation145 permutation2
    mixedMoment B raw18223step1 raw18223step1Labels = mixedMoment B raw18223step2 raw18223step2Labels := by
      have ha : raw18223step2 = -raw18223step1 := by apply Matrix.ext; change ∀ i j, raw18223step2 i j = -(raw18223step1 i j); unfold raw18223step2 raw18223step1; decide +kernel
      have hl : raw18223step2Labels = raw18223step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5409 node5409Labels := by rfl

theorem canonical18224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18224 raw18224Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18224 raw18224Labels = mixedMoment B raw18224step0 raw18224step0Labels := by
      have ha : raw18224step0 = (fun i j => raw18224 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18224step0 raw18224; decide +kernel
      have hl : raw18224step0Labels = raw18224Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18224 raw18224Labels permutation202 permutation7
    mixedMoment B raw18224step0 raw18224step0Labels = mixedMoment B raw18224step1 raw18224step1Labels := by
      have ha : raw18224step1 = -raw18224step0 := by apply Matrix.ext; change ∀ i j, raw18224step1 i j = -(raw18224step0 i j); unfold raw18224step1 raw18224step0; decide +kernel
      have hl : raw18224step1Labels = raw18224step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18224step1 raw18224step1Labels = mixedMoment B raw18224step2 raw18224step2Labels := by
      have ha : raw18224step2 = raw18224step1 := by apply Matrix.ext; unfold raw18224step2 raw18224step1; decide +kernel
      have hl : raw18224step1Labels = labelEmbedding10 ∘ raw18224step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18224step1 raw18224step1Labels raw18224step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical18225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18225 raw18225Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw18225 raw18225Labels = mixedMoment B raw18225step0 raw18225step0Labels := by
      have ha : raw18225step0 = (fun i j => raw18225 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18225step0 raw18225; decide +kernel
      have hl : raw18225step0Labels = raw18225Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18225 raw18225Labels permutation267 permutation3
    mixedMoment B raw18225step0 raw18225step0Labels = mixedMoment B raw18225step1 raw18225step1Labels := by
      have ha : raw18225step1 = raw18225step0 := by apply Matrix.ext; unfold raw18225step1 raw18225step0; decide +kernel
      have hl : raw18225step0Labels = labelEmbedding6 ∘ raw18225step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18225step0 raw18225step0Labels raw18225step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

theorem canonical18226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18226 raw18226Labels = mixedMoment B node5420 node5420Labels := by
  calc
    _ = mixedMoment B node5420 node5420Labels := by rfl

theorem canonical18227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18227 raw18227Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw18227 raw18227Labels = mixedMoment B raw18227step0 raw18227step0Labels := by
      have hz : ∀ j, raw18227 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18227step0 = (fun i j => raw18227 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18227step0 raw18227; decide +kernel
      have hl : raw18227step0Labels = raw18227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18227 raw18227Labels permutation520 hz
    _ = mixedMoment B node5432 node5432Labels := by rfl

theorem canonical18228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18228 raw18228Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw18228 raw18228Labels = mixedMoment B raw18228step0 raw18228step0Labels := by
      have ha : raw18228step0 = (fun i j => raw18228 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18228step0 raw18228; decide +kernel
      have hl : raw18228step0Labels = raw18228Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18228 raw18228Labels permutation158 permutation2
    _ = mixedMoment B node5129 node5129Labels := by rfl

theorem canonical18229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18229 raw18229Labels = mixedMoment B node5376 node5376Labels := by
  calc
    mixedMoment B raw18229 raw18229Labels = mixedMoment B raw18229step0 raw18229step0Labels := by
      have ha : raw18229step0 = (fun i j => raw18229 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18229step0 raw18229; decide +kernel
      have hl : raw18229step0Labels = raw18229Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18229 raw18229Labels permutation158 permutation2
    _ = mixedMoment B node5376 node5376Labels := by rfl

theorem canonical18230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18230 raw18230Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw18230 raw18230Labels = mixedMoment B raw18230step0 raw18230step0Labels := by
      have ha : raw18230step0 = (fun i j => raw18230 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18230step0 raw18230; decide +kernel
      have hl : raw18230step0Labels = raw18230Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18230 raw18230Labels permutation587 permutation3
    mixedMoment B raw18230step0 raw18230step0Labels = mixedMoment B raw18230step1 raw18230step1Labels := by
      have ha : raw18230step1 = -raw18230step0 := by apply Matrix.ext; change ∀ i j, raw18230step1 i j = -(raw18230step0 i j); unfold raw18230step1 raw18230step0; decide +kernel
      have hl : raw18230step1Labels = raw18230step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18230step1 raw18230step1Labels = mixedMoment B raw18230step2 raw18230step2Labels := by
      have ha : raw18230step2 = raw18230step1 := by apply Matrix.ext; unfold raw18230step2 raw18230step1; decide +kernel
      have hl : raw18230step1Labels = labelEmbedding6 ∘ raw18230step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18230step1 raw18230step1Labels raw18230step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

theorem canonical18231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18231 raw18231Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw18231 raw18231Labels = mixedMoment B raw18231step0 raw18231step0Labels := by
      have ha : raw18231step0 = (fun i j => raw18231 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18231step0 raw18231; decide +kernel
      have hl : raw18231step0Labels = raw18231Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18231 raw18231Labels permutation680 permutation2
    mixedMoment B raw18231step0 raw18231step0Labels = mixedMoment B raw18231step1 raw18231step1Labels := by
      have ha : raw18231step1 = -raw18231step0 := by apply Matrix.ext; change ∀ i j, raw18231step1 i j = -(raw18231step0 i j); unfold raw18231step1 raw18231step0; decide +kernel
      have hl : raw18231step1Labels = raw18231step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical18232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18232 raw18232Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18232 raw18232Labels = mixedMoment B raw18232step0 raw18232step0Labels := by
      have ha : raw18232step0 = (fun i j => raw18232 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18232step0 raw18232; decide +kernel
      have hl : raw18232step0Labels = raw18232Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18232 raw18232Labels permutation159 permutation2
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical18233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18233 raw18233Labels = mixedMoment B node5127 node5127Labels := by
  calc
    mixedMoment B raw18233 raw18233Labels = mixedMoment B raw18233step0 raw18233step0Labels := by
      have ha : raw18233step0 = (fun i j => raw18233 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18233step0 raw18233; decide +kernel
      have hl : raw18233step0Labels = raw18233Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18233 raw18233Labels permutation158 permutation2
    _ = mixedMoment B node5127 node5127Labels := by rfl

theorem canonical18234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18234 raw18234Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw18234 raw18234Labels = mixedMoment B raw18234step0 raw18234step0Labels := by
      have ha : raw18234step0 = (fun i j => raw18234 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18234step0 raw18234; decide +kernel
      have hl : raw18234step0Labels = raw18234Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18234 raw18234Labels permutation682 permutation2
    mixedMoment B raw18234step0 raw18234step0Labels = mixedMoment B raw18234step1 raw18234step1Labels := by
      have ha : raw18234step1 = -raw18234step0 := by apply Matrix.ext; change ∀ i j, raw18234step1 i j = -(raw18234step0 i j); unfold raw18234step1 raw18234step0; decide +kernel
      have hl : raw18234step1Labels = raw18234step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5129 node5129Labels := by rfl

theorem canonical18235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18235 raw18235Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw18235 raw18235Labels = mixedMoment B raw18235step0 raw18235step0Labels := by
      have ha : raw18235step0 = (fun i j => raw18235 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18235step0 raw18235; decide +kernel
      have hl : raw18235step0Labels = raw18235Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18235 raw18235Labels permutation688 permutation2
    mixedMoment B raw18235step0 raw18235step0Labels = mixedMoment B raw18235step1 raw18235step1Labels := by
      have ha : raw18235step1 = -raw18235step0 := by apply Matrix.ext; change ∀ i j, raw18235step1 i j = -(raw18235step0 i j); unfold raw18235step1 raw18235step0; decide +kernel
      have hl : raw18235step1Labels = raw18235step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5144 node5144Labels := by rfl

theorem canonical18236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18236 raw18236Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw18236 raw18236Labels = mixedMoment B raw18236step0 raw18236step0Labels := by
      have ha : raw18236step0 = (fun i j => raw18236 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18236step0 raw18236; decide +kernel
      have hl : raw18236step0Labels = raw18236Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18236 raw18236Labels permutation680 permutation2
    mixedMoment B raw18236step0 raw18236step0Labels = mixedMoment B raw18236step1 raw18236step1Labels := by
      have ha : raw18236step1 = -raw18236step0 := by apply Matrix.ext; change ∀ i j, raw18236step1 i j = -(raw18236step0 i j); unfold raw18236step1 raw18236step0; decide +kernel
      have hl : raw18236step1Labels = raw18236step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical18237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18237 raw18237Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw18237 raw18237Labels = mixedMoment B raw18237step0 raw18237step0Labels := by
      have hz : ∀ j, raw18237 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18237step0 = (fun i j => raw18237 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18237step0 raw18237; decide +kernel
      have hl : raw18237step0Labels = raw18237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18237 raw18237Labels permutation520 hz
    mixedMoment B raw18237step0 raw18237step0Labels = mixedMoment B raw18237step1 raw18237step1Labels := by
      have ha : raw18237step1 = (fun i j => raw18237step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18237step1 raw18237step0; decide +kernel
      have hl : raw18237step1Labels = raw18237step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18237step0 raw18237step0Labels permutation145 permutation2
    mixedMoment B raw18237step1 raw18237step1Labels = mixedMoment B raw18237step2 raw18237step2Labels := by
      have ha : raw18237step2 = -raw18237step1 := by apply Matrix.ext; change ∀ i j, raw18237step2 i j = -(raw18237step1 i j); unfold raw18237step2 raw18237step1; decide +kernel
      have hl : raw18237step2Labels = raw18237step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical18238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18238 raw18238Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw18238 raw18238Labels = mixedMoment B raw18238step0 raw18238step0Labels := by
      have ha : raw18238step0 = (fun i j => raw18238 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18238step0 raw18238; decide +kernel
      have hl : raw18238step0Labels = raw18238Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18238 raw18238Labels permutation644 permutation7
    mixedMoment B raw18238step0 raw18238step0Labels = mixedMoment B raw18238step1 raw18238step1Labels := by
      have ha : raw18238step1 = raw18238step0 := by apply Matrix.ext; unfold raw18238step1 raw18238step0; decide +kernel
      have hl : raw18238step0Labels = labelEmbedding1 ∘ raw18238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18238step0 raw18238step0Labels raw18238step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical18239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18239 raw18239Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw18239 raw18239Labels = mixedMoment B raw18239step0 raw18239step0Labels := by
      have ha : raw18239step0 = (fun i j => raw18239 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18239step0 raw18239; decide +kernel
      have hl : raw18239step0Labels = raw18239Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18239 raw18239Labels permutation644 permutation7
    mixedMoment B raw18239step0 raw18239step0Labels = mixedMoment B raw18239step1 raw18239step1Labels := by
      have ha : raw18239step1 = raw18239step0 := by apply Matrix.ext; unfold raw18239step1 raw18239step0; decide +kernel
      have hl : raw18239step0Labels = labelEmbedding1 ∘ raw18239step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18239step0 raw18239step0Labels raw18239step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

theorem canonical18240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18240 raw18240Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw18240 raw18240Labels = mixedMoment B raw18240step0 raw18240step0Labels := by
      have ha : raw18240step0 = (fun i j => raw18240 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18240step0 raw18240; decide +kernel
      have hl : raw18240step0Labels = raw18240Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18240 raw18240Labels permutation644 permutation7
    mixedMoment B raw18240step0 raw18240step0Labels = mixedMoment B raw18240step1 raw18240step1Labels := by
      have ha : raw18240step1 = raw18240step0 := by apply Matrix.ext; unfold raw18240step1 raw18240step0; decide +kernel
      have hl : raw18240step0Labels = labelEmbedding1 ∘ raw18240step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18240step0 raw18240step0Labels raw18240step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical18241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18241 raw18241Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw18241 raw18241Labels = mixedMoment B raw18241step0 raw18241step0Labels := by
      have hz : ∀ j, raw18241 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18241step0 = (fun i j => raw18241 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18241step0 raw18241; decide +kernel
      have hl : raw18241step0Labels = raw18241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18241 raw18241Labels permutation520 hz
    mixedMoment B raw18241step0 raw18241step0Labels = mixedMoment B raw18241step1 raw18241step1Labels := by
      have ha : raw18241step1 = (fun i j => raw18241step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18241step1 raw18241step0; decide +kernel
      have hl : raw18241step1Labels = raw18241step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18241step0 raw18241step0Labels permutation143 permutation7
    mixedMoment B raw18241step1 raw18241step1Labels = mixedMoment B raw18241step2 raw18241step2Labels := by
      have ha : raw18241step2 = raw18241step1 := by apply Matrix.ext; unfold raw18241step2 raw18241step1; decide +kernel
      have hl : raw18241step1Labels = labelEmbedding1 ∘ raw18241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18241step1 raw18241step1Labels raw18241step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

theorem canonical18242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18242 raw18242Labels = mixedMoment B node3989 node3989Labels := by
  calc
    mixedMoment B raw18242 raw18242Labels = mixedMoment B raw18242step0 raw18242step0Labels := by
      have ha : raw18242step0 = (fun i j => raw18242 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18242step0 raw18242; decide +kernel
      have hl : raw18242step0Labels = raw18242Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18242 raw18242Labels permutation644 permutation7
    mixedMoment B raw18242step0 raw18242step0Labels = mixedMoment B raw18242step1 raw18242step1Labels := by
      have ha : raw18242step1 = raw18242step0 := by apply Matrix.ext; unfold raw18242step1 raw18242step0; decide +kernel
      have hl : raw18242step0Labels = labelEmbedding1 ∘ raw18242step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18242step0 raw18242step0Labels raw18242step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3989 node3989Labels := by rfl

theorem canonical18243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18243 raw18243Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw18243 raw18243Labels = mixedMoment B raw18243step0 raw18243step0Labels := by
      have hz : ∀ j, raw18243 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18243step0 = (fun i j => raw18243 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18243step0 raw18243; decide +kernel
      have hl : raw18243step0Labels = raw18243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18243 raw18243Labels permutation265 hz
    mixedMoment B raw18243step0 raw18243step0Labels = mixedMoment B raw18243step1 raw18243step1Labels := by
      have ha : raw18243step1 = (fun i j => raw18243step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18243step1 raw18243step0; decide +kernel
      have hl : raw18243step1Labels = raw18243step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18243step0 raw18243step0Labels permutation40 permutation7
    mixedMoment B raw18243step1 raw18243step1Labels = mixedMoment B raw18243step2 raw18243step2Labels := by
      have ha : raw18243step2 = -raw18243step1 := by apply Matrix.ext; change ∀ i j, raw18243step2 i j = -(raw18243step1 i j); unfold raw18243step2 raw18243step1; decide +kernel
      have hl : raw18243step2Labels = raw18243step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18243step2 raw18243step2Labels = mixedMoment B raw18243step3 raw18243step3Labels := by
      have ha : raw18243step3 = raw18243step2 := by apply Matrix.ext; unfold raw18243step3 raw18243step2; decide +kernel
      have hl : raw18243step2Labels = labelEmbedding1 ∘ raw18243step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18243step2 raw18243step2Labels raw18243step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical18244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18244 raw18244Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw18244 raw18244Labels = mixedMoment B raw18244step0 raw18244step0Labels := by
      have hz : ∀ j, raw18244 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18244step0 = (fun i j => raw18244 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18244step0 raw18244; decide +kernel
      have hl : raw18244step0Labels = raw18244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18244 raw18244Labels permutation265 hz
    mixedMoment B raw18244step0 raw18244step0Labels = mixedMoment B raw18244step1 raw18244step1Labels := by
      have ha : raw18244step1 = (fun i j => raw18244step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18244step1 raw18244step0; decide +kernel
      have hl : raw18244step1Labels = raw18244step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18244step0 raw18244step0Labels permutation40 permutation7
    mixedMoment B raw18244step1 raw18244step1Labels = mixedMoment B raw18244step2 raw18244step2Labels := by
      have ha : raw18244step2 = -raw18244step1 := by apply Matrix.ext; change ∀ i j, raw18244step2 i j = -(raw18244step1 i j); unfold raw18244step2 raw18244step1; decide +kernel
      have hl : raw18244step2Labels = raw18244step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18244step2 raw18244step2Labels = mixedMoment B raw18244step3 raw18244step3Labels := by
      have ha : raw18244step3 = raw18244step2 := by apply Matrix.ext; unfold raw18244step3 raw18244step2; decide +kernel
      have hl : raw18244step2Labels = labelEmbedding1 ∘ raw18244step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18244step2 raw18244step2Labels raw18244step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical18245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18245 raw18245Labels = mixedMoment B node3860 node3860Labels := by
  calc
    mixedMoment B raw18245 raw18245Labels = mixedMoment B raw18245step0 raw18245step0Labels := by
      have hz : ∀ j, raw18245 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18245step0 = (fun i j => raw18245 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18245step0 raw18245; decide +kernel
      have hl : raw18245step0Labels = raw18245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18245 raw18245Labels permutation520 hz
    mixedMoment B raw18245step0 raw18245step0Labels = mixedMoment B raw18245step1 raw18245step1Labels := by
      have hz : ∀ j, raw18245step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw18245step1 = (fun i j => raw18245step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw18245step1 raw18245step0; decide +kernel
      have hl : raw18245step1Labels = raw18245step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18245step0 raw18245step0Labels permutation56 hz
    mixedMoment B raw18245step1 raw18245step1Labels = mixedMoment B raw18245step2 raw18245step2Labels := by
      have ha : raw18245step2 = (fun i j => raw18245step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18245step2 raw18245step1; decide +kernel
      have hl : raw18245step2Labels = raw18245step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18245step1 raw18245step1Labels permutation29 permutation7
    mixedMoment B raw18245step2 raw18245step2Labels = mixedMoment B raw18245step3 raw18245step3Labels := by
      have ha : raw18245step3 = raw18245step2 := by apply Matrix.ext; unfold raw18245step3 raw18245step2; decide +kernel
      have hl : raw18245step2Labels = labelEmbedding1 ∘ raw18245step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18245step2 raw18245step2Labels raw18245step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3860 node3860Labels := by rfl

theorem canonical18246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18246 raw18246Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw18246 raw18246Labels = mixedMoment B raw18246step0 raw18246step0Labels := by
      have ha : raw18246step0 = (fun i j => raw18246 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18246step0 raw18246; decide +kernel
      have hl : raw18246step0Labels = raw18246Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18246 raw18246Labels permutation202 permutation7
    mixedMoment B raw18246step0 raw18246step0Labels = mixedMoment B raw18246step1 raw18246step1Labels := by
      have ha : raw18246step1 = -raw18246step0 := by apply Matrix.ext; change ∀ i j, raw18246step1 i j = -(raw18246step0 i j); unfold raw18246step1 raw18246step0; decide +kernel
      have hl : raw18246step1Labels = raw18246step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18246step1 raw18246step1Labels = mixedMoment B raw18246step2 raw18246step2Labels := by
      have ha : raw18246step2 = raw18246step1 := by apply Matrix.ext; unfold raw18246step2 raw18246step1; decide +kernel
      have hl : raw18246step1Labels = labelEmbedding1 ∘ raw18246step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18246step1 raw18246step1Labels raw18246step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

theorem canonical18247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18247 raw18247Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw18247 raw18247Labels = mixedMoment B raw18247step0 raw18247step0Labels := by
      have ha : raw18247step0 = (fun i j => raw18247 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18247step0 raw18247; decide +kernel
      have hl : raw18247step0Labels = raw18247Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18247 raw18247Labels permutation644 permutation7
    mixedMoment B raw18247step0 raw18247step0Labels = mixedMoment B raw18247step1 raw18247step1Labels := by
      have ha : raw18247step1 = raw18247step0 := by apply Matrix.ext; unfold raw18247step1 raw18247step0; decide +kernel
      have hl : raw18247step0Labels = labelEmbedding1 ∘ raw18247step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18247step0 raw18247step0Labels raw18247step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

theorem canonical18248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18248 raw18248Labels = mixedMoment B node3793 node3793Labels := by
  calc
    mixedMoment B raw18248 raw18248Labels = mixedMoment B raw18248step0 raw18248step0Labels := by
      have ha : raw18248step0 = (fun i j => raw18248 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18248step0 raw18248; decide +kernel
      have hl : raw18248step0Labels = raw18248Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18248 raw18248Labels permutation644 permutation7
    mixedMoment B raw18248step0 raw18248step0Labels = mixedMoment B raw18248step1 raw18248step1Labels := by
      have ha : raw18248step1 = raw18248step0 := by apply Matrix.ext; unfold raw18248step1 raw18248step0; decide +kernel
      have hl : raw18248step0Labels = labelEmbedding1 ∘ raw18248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18248step0 raw18248step0Labels raw18248step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3793 node3793Labels := by rfl

theorem canonical18249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18249 raw18249Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw18249 raw18249Labels = mixedMoment B raw18249step0 raw18249step0Labels := by
      have hz : ∀ j, raw18249 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18249step0 = (fun i j => raw18249 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18249step0 raw18249; decide +kernel
      have hl : raw18249step0Labels = raw18249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18249 raw18249Labels permutation520 hz
    mixedMoment B raw18249step0 raw18249step0Labels = mixedMoment B raw18249step1 raw18249step1Labels := by
      have ha : raw18249step1 = (fun i j => raw18249step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18249step1 raw18249step0; decide +kernel
      have hl : raw18249step1Labels = raw18249step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18249step0 raw18249step0Labels permutation143 permutation7
    mixedMoment B raw18249step1 raw18249step1Labels = mixedMoment B raw18249step2 raw18249step2Labels := by
      have ha : raw18249step2 = raw18249step1 := by apply Matrix.ext; unfold raw18249step2 raw18249step1; decide +kernel
      have hl : raw18249step1Labels = labelEmbedding1 ∘ raw18249step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18249step1 raw18249step1Labels raw18249step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical18250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18250 raw18250Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw18250 raw18250Labels = mixedMoment B raw18250step0 raw18250step0Labels := by
      have ha : raw18250step0 = (fun i j => raw18250 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18250step0 raw18250; decide +kernel
      have hl : raw18250step0Labels = raw18250Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18250 raw18250Labels permutation202 permutation7
    mixedMoment B raw18250step0 raw18250step0Labels = mixedMoment B raw18250step1 raw18250step1Labels := by
      have ha : raw18250step1 = -raw18250step0 := by apply Matrix.ext; change ∀ i j, raw18250step1 i j = -(raw18250step0 i j); unfold raw18250step1 raw18250step0; decide +kernel
      have hl : raw18250step1Labels = raw18250step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18250step1 raw18250step1Labels = mixedMoment B raw18250step2 raw18250step2Labels := by
      have ha : raw18250step2 = raw18250step1 := by apply Matrix.ext; unfold raw18250step2 raw18250step1; decide +kernel
      have hl : raw18250step1Labels = labelEmbedding1 ∘ raw18250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18250step1 raw18250step1Labels raw18250step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical18251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18251 raw18251Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw18251 raw18251Labels = mixedMoment B raw18251step0 raw18251step0Labels := by
      have ha : raw18251step0 = (fun i j => raw18251 (permutation294 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18251step0 raw18251; decide +kernel
      have hl : raw18251step0Labels = raw18251Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18251 raw18251Labels permutation294 permutation5
    mixedMoment B raw18251step0 raw18251step0Labels = mixedMoment B raw18251step1 raw18251step1Labels := by
      have ha : raw18251step1 = -raw18251step0 := by apply Matrix.ext; change ∀ i j, raw18251step1 i j = -(raw18251step0 i j); unfold raw18251step1 raw18251step0; decide +kernel
      have hl : raw18251step1Labels = raw18251step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18251step1 raw18251step1Labels = mixedMoment B raw18251step2 raw18251step2Labels := by
      have ha : raw18251step2 = raw18251step1 := by apply Matrix.ext; unfold raw18251step2 raw18251step1; decide +kernel
      have hl : raw18251step1Labels = labelEmbedding1 ∘ raw18251step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18251step1 raw18251step1Labels raw18251step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

theorem canonical18252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18252 raw18252Labels = mixedMoment B node3870 node3870Labels := by
  calc
    mixedMoment B raw18252 raw18252Labels = mixedMoment B raw18252step0 raw18252step0Labels := by
      have ha : raw18252step0 = (fun i j => raw18252 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18252step0 raw18252; decide +kernel
      have hl : raw18252step0Labels = raw18252Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18252 raw18252Labels permutation644 permutation7
    mixedMoment B raw18252step0 raw18252step0Labels = mixedMoment B raw18252step1 raw18252step1Labels := by
      have ha : raw18252step1 = raw18252step0 := by apply Matrix.ext; unfold raw18252step1 raw18252step0; decide +kernel
      have hl : raw18252step0Labels = labelEmbedding1 ∘ raw18252step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18252step0 raw18252step0Labels raw18252step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3870 node3870Labels := by rfl

theorem canonical18253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18253 raw18253Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw18253 raw18253Labels = mixedMoment B raw18253step0 raw18253step0Labels := by
      have hz : ∀ j, raw18253 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18253step0 = (fun i j => raw18253 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18253step0 raw18253; decide +kernel
      have hl : raw18253step0Labels = raw18253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18253 raw18253Labels permutation520 hz
    mixedMoment B raw18253step0 raw18253step0Labels = mixedMoment B raw18253step1 raw18253step1Labels := by
      have ha : raw18253step1 = (fun i j => raw18253step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18253step1 raw18253step0; decide +kernel
      have hl : raw18253step1Labels = raw18253step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18253step0 raw18253step0Labels permutation143 permutation7
    mixedMoment B raw18253step1 raw18253step1Labels = mixedMoment B raw18253step2 raw18253step2Labels := by
      have ha : raw18253step2 = raw18253step1 := by apply Matrix.ext; unfold raw18253step2 raw18253step1; decide +kernel
      have hl : raw18253step1Labels = labelEmbedding1 ∘ raw18253step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18253step1 raw18253step1Labels raw18253step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical18254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18254 raw18254Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw18254 raw18254Labels = mixedMoment B raw18254step0 raw18254step0Labels := by
      have ha : raw18254step0 = (fun i j => raw18254 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18254step0 raw18254; decide +kernel
      have hl : raw18254step0Labels = raw18254Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18254 raw18254Labels permutation202 permutation7
    mixedMoment B raw18254step0 raw18254step0Labels = mixedMoment B raw18254step1 raw18254step1Labels := by
      have ha : raw18254step1 = -raw18254step0 := by apply Matrix.ext; change ∀ i j, raw18254step1 i j = -(raw18254step0 i j); unfold raw18254step1 raw18254step0; decide +kernel
      have hl : raw18254step1Labels = raw18254step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18254step1 raw18254step1Labels = mixedMoment B raw18254step2 raw18254step2Labels := by
      have ha : raw18254step2 = raw18254step1 := by apply Matrix.ext; unfold raw18254step2 raw18254step1; decide +kernel
      have hl : raw18254step1Labels = labelEmbedding1 ∘ raw18254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18254step1 raw18254step1Labels raw18254step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical18255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18255 raw18255Labels = mixedMoment B node3833 node3833Labels := by
  calc
    mixedMoment B raw18255 raw18255Labels = mixedMoment B raw18255step0 raw18255step0Labels := by
      have ha : raw18255step0 = (fun i j => raw18255 (permutation564 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18255step0 raw18255; decide +kernel
      have hl : raw18255step0Labels = raw18255Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18255 raw18255Labels permutation564 permutation5
    mixedMoment B raw18255step0 raw18255step0Labels = mixedMoment B raw18255step1 raw18255step1Labels := by
      have ha : raw18255step1 = raw18255step0 := by apply Matrix.ext; unfold raw18255step1 raw18255step0; decide +kernel
      have hl : raw18255step0Labels = labelEmbedding1 ∘ raw18255step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18255step0 raw18255step0Labels raw18255step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3833 node3833Labels := by rfl

theorem canonical18256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18256 raw18256Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw18256 raw18256Labels = mixedMoment B raw18256step0 raw18256step0Labels := by
      have ha : raw18256step0 = (fun i j => raw18256 (permutation563 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18256step0 raw18256; decide +kernel
      have hl : raw18256step0Labels = raw18256Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18256 raw18256Labels permutation563 permutation5
    mixedMoment B raw18256step0 raw18256step0Labels = mixedMoment B raw18256step1 raw18256step1Labels := by
      have ha : raw18256step1 = raw18256step0 := by apply Matrix.ext; unfold raw18256step1 raw18256step0; decide +kernel
      have hl : raw18256step0Labels = labelEmbedding1 ∘ raw18256step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18256step0 raw18256step0Labels raw18256step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

theorem canonical18257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18257 raw18257Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw18257 raw18257Labels = mixedMoment B raw18257step0 raw18257step0Labels := by
      have ha : raw18257step0 = (fun i j => raw18257 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18257step0 raw18257; decide +kernel
      have hl : raw18257step0Labels = raw18257Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18257 raw18257Labels permutation202 permutation7
    mixedMoment B raw18257step0 raw18257step0Labels = mixedMoment B raw18257step1 raw18257step1Labels := by
      have ha : raw18257step1 = -raw18257step0 := by apply Matrix.ext; change ∀ i j, raw18257step1 i j = -(raw18257step0 i j); unfold raw18257step1 raw18257step0; decide +kernel
      have hl : raw18257step1Labels = raw18257step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18257step1 raw18257step1Labels = mixedMoment B raw18257step2 raw18257step2Labels := by
      have ha : raw18257step2 = raw18257step1 := by apply Matrix.ext; unfold raw18257step2 raw18257step1; decide +kernel
      have hl : raw18257step1Labels = labelEmbedding1 ∘ raw18257step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18257step1 raw18257step1Labels raw18257step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

theorem canonical18258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18258 raw18258Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw18258 raw18258Labels = mixedMoment B raw18258step0 raw18258step0Labels := by
      have ha : raw18258step0 = (fun i j => raw18258 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18258step0 raw18258; decide +kernel
      have hl : raw18258step0Labels = raw18258Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18258 raw18258Labels permutation202 permutation7
    mixedMoment B raw18258step0 raw18258step0Labels = mixedMoment B raw18258step1 raw18258step1Labels := by
      have ha : raw18258step1 = -raw18258step0 := by apply Matrix.ext; change ∀ i j, raw18258step1 i j = -(raw18258step0 i j); unfold raw18258step1 raw18258step0; decide +kernel
      have hl : raw18258step1Labels = raw18258step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18258step1 raw18258step1Labels = mixedMoment B raw18258step2 raw18258step2Labels := by
      have ha : raw18258step2 = raw18258step1 := by apply Matrix.ext; unfold raw18258step2 raw18258step1; decide +kernel
      have hl : raw18258step1Labels = labelEmbedding1 ∘ raw18258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18258step1 raw18258step1Labels raw18258step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical18259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18259 raw18259Labels = mixedMoment B node3513 node3513Labels := by
  calc
    mixedMoment B raw18259 raw18259Labels = mixedMoment B raw18259step0 raw18259step0Labels := by
      have ha : raw18259step0 = (fun i j => raw18259 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18259step0 raw18259; decide +kernel
      have hl : raw18259step0Labels = raw18259Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18259 raw18259Labels permutation644 permutation7
    mixedMoment B raw18259step0 raw18259step0Labels = mixedMoment B raw18259step1 raw18259step1Labels := by
      have ha : raw18259step1 = raw18259step0 := by apply Matrix.ext; unfold raw18259step1 raw18259step0; decide +kernel
      have hl : raw18259step0Labels = labelEmbedding1 ∘ raw18259step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18259step0 raw18259step0Labels raw18259step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3513 node3513Labels := by rfl

theorem canonical18260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18260 raw18260Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw18260 raw18260Labels = mixedMoment B raw18260step0 raw18260step0Labels := by
      have ha : raw18260step0 = (fun i j => raw18260 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18260step0 raw18260; decide +kernel
      have hl : raw18260step0Labels = raw18260Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18260 raw18260Labels permutation644 permutation7
    mixedMoment B raw18260step0 raw18260step0Labels = mixedMoment B raw18260step1 raw18260step1Labels := by
      have ha : raw18260step1 = raw18260step0 := by apply Matrix.ext; unfold raw18260step1 raw18260step0; decide +kernel
      have hl : raw18260step0Labels = labelEmbedding1 ∘ raw18260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18260step0 raw18260step0Labels raw18260step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical18261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18261 raw18261Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw18261 raw18261Labels = mixedMoment B raw18261step0 raw18261step0Labels := by
      have ha : raw18261step0 = (fun i j => raw18261 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18261step0 raw18261; decide +kernel
      have hl : raw18261step0Labels = raw18261Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18261 raw18261Labels permutation644 permutation7
    mixedMoment B raw18261step0 raw18261step0Labels = mixedMoment B raw18261step1 raw18261step1Labels := by
      have ha : raw18261step1 = raw18261step0 := by apply Matrix.ext; unfold raw18261step1 raw18261step0; decide +kernel
      have hl : raw18261step0Labels = labelEmbedding1 ∘ raw18261step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18261step0 raw18261step0Labels raw18261step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

theorem canonical18262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18262 raw18262Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw18262 raw18262Labels = mixedMoment B raw18262step0 raw18262step0Labels := by
      have ha : raw18262step0 = (fun i j => raw18262 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18262step0 raw18262; decide +kernel
      have hl : raw18262step0Labels = raw18262Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18262 raw18262Labels permutation644 permutation7
    mixedMoment B raw18262step0 raw18262step0Labels = mixedMoment B raw18262step1 raw18262step1Labels := by
      have ha : raw18262step1 = raw18262step0 := by apply Matrix.ext; unfold raw18262step1 raw18262step0; decide +kernel
      have hl : raw18262step0Labels = labelEmbedding1 ∘ raw18262step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18262step0 raw18262step0Labels raw18262step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

theorem canonical18263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18263 raw18263Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw18263 raw18263Labels = mixedMoment B raw18263step0 raw18263step0Labels := by
      have hz : ∀ j, raw18263 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18263step0 = (fun i j => raw18263 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18263step0 raw18263; decide +kernel
      have hl : raw18263step0Labels = raw18263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18263 raw18263Labels permutation520 hz
    mixedMoment B raw18263step0 raw18263step0Labels = mixedMoment B raw18263step1 raw18263step1Labels := by
      have ha : raw18263step1 = (fun i j => raw18263step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18263step1 raw18263step0; decide +kernel
      have hl : raw18263step1Labels = raw18263step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18263step0 raw18263step0Labels permutation143 permutation7
    mixedMoment B raw18263step1 raw18263step1Labels = mixedMoment B raw18263step2 raw18263step2Labels := by
      have ha : raw18263step2 = raw18263step1 := by apply Matrix.ext; unfold raw18263step2 raw18263step1; decide +kernel
      have hl : raw18263step1Labels = labelEmbedding1 ∘ raw18263step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18263step1 raw18263step1Labels raw18263step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical18264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18264 raw18264Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18264 raw18264Labels = mixedMoment B raw18264step0 raw18264step0Labels := by
      have ha : raw18264step0 = (fun i j => raw18264 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18264step0 raw18264; decide +kernel
      have hl : raw18264step0Labels = raw18264Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18264 raw18264Labels permutation681 permutation3
    mixedMoment B raw18264step0 raw18264step0Labels = mixedMoment B raw18264step1 raw18264step1Labels := by
      have ha : raw18264step1 = -raw18264step0 := by apply Matrix.ext; change ∀ i j, raw18264step1 i j = -(raw18264step0 i j); unfold raw18264step1 raw18264step0; decide +kernel
      have hl : raw18264step1Labels = raw18264step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18264step1 raw18264step1Labels = mixedMoment B raw18264step2 raw18264step2Labels := by
      have ha : raw18264step2 = raw18264step1 := by apply Matrix.ext; unfold raw18264step2 raw18264step1; decide +kernel
      have hl : raw18264step1Labels = labelEmbedding6 ∘ raw18264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18264step1 raw18264step1Labels raw18264step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical18265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18265 raw18265Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18265 raw18265Labels = mixedMoment B raw18265step0 raw18265step0Labels := by
      have ha : raw18265step0 = (fun i j => raw18265 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18265step0 raw18265; decide +kernel
      have hl : raw18265step0Labels = raw18265Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18265 raw18265Labels permutation686 permutation3
    mixedMoment B raw18265step0 raw18265step0Labels = mixedMoment B raw18265step1 raw18265step1Labels := by
      have ha : raw18265step1 = -raw18265step0 := by apply Matrix.ext; change ∀ i j, raw18265step1 i j = -(raw18265step0 i j); unfold raw18265step1 raw18265step0; decide +kernel
      have hl : raw18265step1Labels = raw18265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18265step1 raw18265step1Labels = mixedMoment B raw18265step2 raw18265step2Labels := by
      have ha : raw18265step2 = raw18265step1 := by apply Matrix.ext; unfold raw18265step2 raw18265step1; decide +kernel
      have hl : raw18265step1Labels = labelEmbedding6 ∘ raw18265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18265step1 raw18265step1Labels raw18265step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical18266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18266 raw18266Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18266 raw18266Labels = mixedMoment B raw18266step0 raw18266step0Labels := by
      have ha : raw18266step0 = (fun i j => raw18266 (permutation643 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18266step0 raw18266; decide +kernel
      have hl : raw18266step0Labels = raw18266Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18266 raw18266Labels permutation643 permutation5
    mixedMoment B raw18266step0 raw18266step0Labels = mixedMoment B raw18266step1 raw18266step1Labels := by
      have ha : raw18266step1 = raw18266step0 := by apply Matrix.ext; unfold raw18266step1 raw18266step0; decide +kernel
      have hl : raw18266step0Labels = labelEmbedding8 ∘ raw18266step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18266step0 raw18266step0Labels raw18266step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical18267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18267 raw18267Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18267 raw18267Labels = mixedMoment B raw18267step0 raw18267step0Labels := by
      have ha : raw18267step0 = (fun i j => raw18267 (permutation632 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18267step0 raw18267; decide +kernel
      have hl : raw18267step0Labels = raw18267Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18267 raw18267Labels permutation632 permutation5
    mixedMoment B raw18267step0 raw18267step0Labels = mixedMoment B raw18267step1 raw18267step1Labels := by
      have ha : raw18267step1 = raw18267step0 := by apply Matrix.ext; unfold raw18267step1 raw18267step0; decide +kernel
      have hl : raw18267step0Labels = labelEmbedding8 ∘ raw18267step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18267step0 raw18267step0Labels raw18267step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical18268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18268 raw18268Labels = mixedMoment B node5500 node5500Labels := by
  calc
    mixedMoment B raw18268 raw18268Labels = mixedMoment B raw18268step0 raw18268step0Labels := by
      have ha : raw18268step0 = (fun i j => raw18268 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18268step0 raw18268; decide +kernel
      have hl : raw18268step0Labels = raw18268Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18268 raw18268Labels permutation266 permutation2
    _ = mixedMoment B node5500 node5500Labels := by rfl

theorem canonical18269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18269 raw18269Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw18269 raw18269Labels = mixedMoment B raw18269step0 raw18269step0Labels := by
      have ha : raw18269step0 = (fun i j => raw18269 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18269step0 raw18269; decide +kernel
      have hl : raw18269step0Labels = raw18269Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18269 raw18269Labels permutation212 permutation5
    mixedMoment B raw18269step0 raw18269step0Labels = mixedMoment B raw18269step1 raw18269step1Labels := by
      have ha : raw18269step1 = -raw18269step0 := by apply Matrix.ext; change ∀ i j, raw18269step1 i j = -(raw18269step0 i j); unfold raw18269step1 raw18269step0; decide +kernel
      have hl : raw18269step1Labels = raw18269step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18269step1 raw18269step1Labels = mixedMoment B raw18269step2 raw18269step2Labels := by
      have ha : raw18269step2 = raw18269step1 := by apply Matrix.ext; unfold raw18269step2 raw18269step1; decide +kernel
      have hl : raw18269step1Labels = labelEmbedding8 ∘ raw18269step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18269step1 raw18269step1Labels raw18269step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

theorem canonical18270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18270 raw18270Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw18270 raw18270Labels = mixedMoment B raw18270step0 raw18270step0Labels := by
      have ha : raw18270step0 = (fun i j => raw18270 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18270step0 raw18270; decide +kernel
      have hl : raw18270step0Labels = raw18270Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18270 raw18270Labels permutation182 permutation3
    mixedMoment B raw18270step0 raw18270step0Labels = mixedMoment B raw18270step1 raw18270step1Labels := by
      have ha : raw18270step1 = raw18270step0 := by apply Matrix.ext; unfold raw18270step1 raw18270step0; decide +kernel
      have hl : raw18270step0Labels = labelEmbedding6 ∘ raw18270step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18270step0 raw18270step0Labels raw18270step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

theorem canonical18271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18271 raw18271Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw18271 raw18271Labels = mixedMoment B raw18271step0 raw18271step0Labels := by
      have ha : raw18271step0 = (fun i j => raw18271 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18271step0 raw18271; decide +kernel
      have hl : raw18271step0Labels = raw18271Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18271 raw18271Labels permutation212 permutation5
    mixedMoment B raw18271step0 raw18271step0Labels = mixedMoment B raw18271step1 raw18271step1Labels := by
      have ha : raw18271step1 = -raw18271step0 := by apply Matrix.ext; change ∀ i j, raw18271step1 i j = -(raw18271step0 i j); unfold raw18271step1 raw18271step0; decide +kernel
      have hl : raw18271step1Labels = raw18271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18271step1 raw18271step1Labels = mixedMoment B raw18271step2 raw18271step2Labels := by
      have ha : raw18271step2 = raw18271step1 := by apply Matrix.ext; unfold raw18271step2 raw18271step1; decide +kernel
      have hl : raw18271step1Labels = labelEmbedding8 ∘ raw18271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18271step1 raw18271step1Labels raw18271step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

theorem canonical18272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18272 raw18272Labels = mixedMoment B node5415 node5415Labels := by
  calc
    mixedMoment B raw18272 raw18272Labels = mixedMoment B raw18272step0 raw18272step0Labels := by
      have ha : raw18272step0 = (fun i j => raw18272 (permutation609 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18272step0 raw18272; decide +kernel
      have hl : raw18272step0Labels = raw18272Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18272 raw18272Labels permutation609 permutation5
    mixedMoment B raw18272step0 raw18272step0Labels = mixedMoment B raw18272step1 raw18272step1Labels := by
      have ha : raw18272step1 = raw18272step0 := by apply Matrix.ext; unfold raw18272step1 raw18272step0; decide +kernel
      have hl : raw18272step0Labels = labelEmbedding8 ∘ raw18272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18272step0 raw18272step0Labels raw18272step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5415 node5415Labels := by rfl

theorem canonical18273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18273 raw18273Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18273 raw18273Labels = mixedMoment B raw18273step0 raw18273step0Labels := by
      have ha : raw18273step0 = (fun i j => raw18273 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18273step0 raw18273; decide +kernel
      have hl : raw18273step0Labels = raw18273Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18273 raw18273Labels permutation212 permutation5
    mixedMoment B raw18273step0 raw18273step0Labels = mixedMoment B raw18273step1 raw18273step1Labels := by
      have ha : raw18273step1 = -raw18273step0 := by apply Matrix.ext; change ∀ i j, raw18273step1 i j = -(raw18273step0 i j); unfold raw18273step1 raw18273step0; decide +kernel
      have hl : raw18273step1Labels = raw18273step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18273step1 raw18273step1Labels = mixedMoment B raw18273step2 raw18273step2Labels := by
      have ha : raw18273step2 = raw18273step1 := by apply Matrix.ext; unfold raw18273step2 raw18273step1; decide +kernel
      have hl : raw18273step1Labels = labelEmbedding8 ∘ raw18273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18273step1 raw18273step1Labels raw18273step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical18274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18274 raw18274Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw18274 raw18274Labels = mixedMoment B raw18274step0 raw18274step0Labels := by
      have ha : raw18274step0 = (fun i j => raw18274 (permutation202 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18274step0 raw18274; decide +kernel
      have hl : raw18274step0Labels = raw18274Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18274 raw18274Labels permutation202 permutation5
    mixedMoment B raw18274step0 raw18274step0Labels = mixedMoment B raw18274step1 raw18274step1Labels := by
      have ha : raw18274step1 = -raw18274step0 := by apply Matrix.ext; change ∀ i j, raw18274step1 i j = -(raw18274step0 i j); unfold raw18274step1 raw18274step0; decide +kernel
      have hl : raw18274step1Labels = raw18274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18274step1 raw18274step1Labels = mixedMoment B raw18274step2 raw18274step2Labels := by
      have ha : raw18274step2 = raw18274step1 := by apply Matrix.ext; unfold raw18274step2 raw18274step1; decide +kernel
      have hl : raw18274step1Labels = labelEmbedding8 ∘ raw18274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18274step1 raw18274step1Labels raw18274step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

theorem canonical18275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18275 raw18275Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw18275 raw18275Labels = mixedMoment B raw18275step0 raw18275step0Labels := by
      have ha : raw18275step0 = (fun i j => raw18275 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18275step0 raw18275; decide +kernel
      have hl : raw18275step0Labels = raw18275Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18275 raw18275Labels permutation160 permutation3
    mixedMoment B raw18275step0 raw18275step0Labels = mixedMoment B raw18275step1 raw18275step1Labels := by
      have ha : raw18275step1 = raw18275step0 := by apply Matrix.ext; unfold raw18275step1 raw18275step0; decide +kernel
      have hl : raw18275step0Labels = labelEmbedding6 ∘ raw18275step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18275step0 raw18275step0Labels raw18275step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5344 node5344Labels := by rfl

theorem canonical18276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18276 raw18276Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw18276 raw18276Labels = mixedMoment B raw18276step0 raw18276step0Labels := by
      have ha : raw18276step0 = (fun i j => raw18276 (permutation644 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18276step0 raw18276; decide +kernel
      have hl : raw18276step0Labels = raw18276Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18276 raw18276Labels permutation644 permutation5
    mixedMoment B raw18276step0 raw18276step0Labels = mixedMoment B raw18276step1 raw18276step1Labels := by
      have ha : raw18276step1 = raw18276step0 := by apply Matrix.ext; unfold raw18276step1 raw18276step0; decide +kernel
      have hl : raw18276step0Labels = labelEmbedding8 ∘ raw18276step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18276step0 raw18276step0Labels raw18276step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5341 node5341Labels := by rfl

theorem canonical18277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18277 raw18277Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw18277 raw18277Labels = mixedMoment B raw18277step0 raw18277step0Labels := by
      have ha : raw18277step0 = (fun i j => raw18277 (permutation632 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18277step0 raw18277; decide +kernel
      have hl : raw18277step0Labels = raw18277Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18277 raw18277Labels permutation632 permutation5
    mixedMoment B raw18277step0 raw18277step0Labels = mixedMoment B raw18277step1 raw18277step1Labels := by
      have ha : raw18277step1 = raw18277step0 := by apply Matrix.ext; unfold raw18277step1 raw18277step0; decide +kernel
      have hl : raw18277step0Labels = labelEmbedding8 ∘ raw18277step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18277step0 raw18277step0Labels raw18277step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

theorem canonical18278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18278 raw18278Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18278 raw18278Labels = mixedMoment B raw18278step0 raw18278step0Labels := by
      have ha : raw18278step0 = (fun i j => raw18278 (permutation203 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18278step0 raw18278; decide +kernel
      have hl : raw18278step0Labels = raw18278Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18278 raw18278Labels permutation203 permutation5
    mixedMoment B raw18278step0 raw18278step0Labels = mixedMoment B raw18278step1 raw18278step1Labels := by
      have ha : raw18278step1 = -raw18278step0 := by apply Matrix.ext; change ∀ i j, raw18278step1 i j = -(raw18278step0 i j); unfold raw18278step1 raw18278step0; decide +kernel
      have hl : raw18278step1Labels = raw18278step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18278step1 raw18278step1Labels = mixedMoment B raw18278step2 raw18278step2Labels := by
      have ha : raw18278step2 = raw18278step1 := by apply Matrix.ext; unfold raw18278step2 raw18278step1; decide +kernel
      have hl : raw18278step1Labels = labelEmbedding8 ∘ raw18278step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18278step1 raw18278step1Labels raw18278step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical18279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18279 raw18279Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw18279 raw18279Labels = mixedMoment B raw18279step0 raw18279step0Labels := by
      have ha : raw18279step0 = (fun i j => raw18279 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18279step0 raw18279; decide +kernel
      have hl : raw18279step0Labels = raw18279Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18279 raw18279Labels permutation152 permutation3
    mixedMoment B raw18279step0 raw18279step0Labels = mixedMoment B raw18279step1 raw18279step1Labels := by
      have ha : raw18279step1 = raw18279step0 := by apply Matrix.ext; unfold raw18279step1 raw18279step0; decide +kernel
      have hl : raw18279step0Labels = labelEmbedding6 ∘ raw18279step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18279step0 raw18279step0Labels raw18279step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

theorem canonical18280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18280 raw18280Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw18280 raw18280Labels = mixedMoment B raw18280step0 raw18280step0Labels := by
      have ha : raw18280step0 = (fun i j => raw18280 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18280step0 raw18280; decide +kernel
      have hl : raw18280step0Labels = raw18280Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18280 raw18280Labels permutation152 permutation3
    mixedMoment B raw18280step0 raw18280step0Labels = mixedMoment B raw18280step1 raw18280step1Labels := by
      have ha : raw18280step1 = raw18280step0 := by apply Matrix.ext; unfold raw18280step1 raw18280step0; decide +kernel
      have hl : raw18280step0Labels = labelEmbedding6 ∘ raw18280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18280step0 raw18280step0Labels raw18280step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

theorem canonical18281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18281 raw18281Labels = mixedMoment B node5415 node5415Labels := by
  calc
    mixedMoment B raw18281 raw18281Labels = mixedMoment B raw18281step0 raw18281step0Labels := by
      have ha : raw18281step0 = (fun i j => raw18281 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18281step0 raw18281; decide +kernel
      have hl : raw18281step0Labels = raw18281Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18281 raw18281Labels permutation152 permutation3
    mixedMoment B raw18281step0 raw18281step0Labels = mixedMoment B raw18281step1 raw18281step1Labels := by
      have ha : raw18281step1 = raw18281step0 := by apply Matrix.ext; unfold raw18281step1 raw18281step0; decide +kernel
      have hl : raw18281step0Labels = labelEmbedding6 ∘ raw18281step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18281step0 raw18281step0Labels raw18281step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5415 node5415Labels := by rfl

theorem canonical18282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18282 raw18282Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw18282 raw18282Labels = mixedMoment B raw18282step0 raw18282step0Labels := by
      have ha : raw18282step0 = (fun i j => raw18282 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18282step0 raw18282; decide +kernel
      have hl : raw18282step0Labels = raw18282Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18282 raw18282Labels permutation164 permutation3
    mixedMoment B raw18282step0 raw18282step0Labels = mixedMoment B raw18282step1 raw18282step1Labels := by
      have ha : raw18282step1 = raw18282step0 := by apply Matrix.ext; unfold raw18282step1 raw18282step0; decide +kernel
      have hl : raw18282step0Labels = labelEmbedding6 ∘ raw18282step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18282step0 raw18282step0Labels raw18282step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

theorem canonical18283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18283 raw18283Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18283 raw18283Labels = mixedMoment B raw18283step0 raw18283step0Labels := by
      have ha : raw18283step0 = (fun i j => raw18283 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18283step0 raw18283; decide +kernel
      have hl : raw18283step0Labels = raw18283Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18283 raw18283Labels permutation152 permutation3
    mixedMoment B raw18283step0 raw18283step0Labels = mixedMoment B raw18283step1 raw18283step1Labels := by
      have ha : raw18283step1 = raw18283step0 := by apply Matrix.ext; unfold raw18283step1 raw18283step0; decide +kernel
      have hl : raw18283step0Labels = labelEmbedding6 ∘ raw18283step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18283step0 raw18283step0Labels raw18283step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical18284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18284 raw18284Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw18284 raw18284Labels = mixedMoment B raw18284step0 raw18284step0Labels := by
      have ha : raw18284step0 = (fun i j => raw18284 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18284step0 raw18284; decide +kernel
      have hl : raw18284step0Labels = raw18284Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18284 raw18284Labels permutation158 permutation3
    mixedMoment B raw18284step0 raw18284step0Labels = mixedMoment B raw18284step1 raw18284step1Labels := by
      have ha : raw18284step1 = raw18284step0 := by apply Matrix.ext; unfold raw18284step1 raw18284step0; decide +kernel
      have hl : raw18284step0Labels = labelEmbedding6 ∘ raw18284step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18284step0 raw18284step0Labels raw18284step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

theorem canonical18285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18285 raw18285Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw18285 raw18285Labels = mixedMoment B raw18285step0 raw18285step0Labels := by
      have ha : raw18285step0 = (fun i j => raw18285 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18285step0 raw18285; decide +kernel
      have hl : raw18285step0Labels = raw18285Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18285 raw18285Labels permutation158 permutation3
    mixedMoment B raw18285step0 raw18285step0Labels = mixedMoment B raw18285step1 raw18285step1Labels := by
      have ha : raw18285step1 = raw18285step0 := by apply Matrix.ext; unfold raw18285step1 raw18285step0; decide +kernel
      have hl : raw18285step0Labels = labelEmbedding6 ∘ raw18285step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18285step0 raw18285step0Labels raw18285step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5341 node5341Labels := by rfl

theorem canonical18286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18286 raw18286Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw18286 raw18286Labels = mixedMoment B raw18286step0 raw18286step0Labels := by
      have ha : raw18286step0 = (fun i j => raw18286 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18286step0 raw18286; decide +kernel
      have hl : raw18286step0Labels = raw18286Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18286 raw18286Labels permutation686 permutation3
    mixedMoment B raw18286step0 raw18286step0Labels = mixedMoment B raw18286step1 raw18286step1Labels := by
      have ha : raw18286step1 = -raw18286step0 := by apply Matrix.ext; change ∀ i j, raw18286step1 i j = -(raw18286step0 i j); unfold raw18286step1 raw18286step0; decide +kernel
      have hl : raw18286step1Labels = raw18286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18286step1 raw18286step1Labels = mixedMoment B raw18286step2 raw18286step2Labels := by
      have ha : raw18286step2 = raw18286step1 := by apply Matrix.ext; unfold raw18286step2 raw18286step1; decide +kernel
      have hl : raw18286step1Labels = labelEmbedding6 ∘ raw18286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18286step1 raw18286step1Labels raw18286step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

theorem canonical18287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18287 raw18287Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw18287 raw18287Labels = mixedMoment B raw18287step0 raw18287step0Labels := by
      have ha : raw18287step0 = (fun i j => raw18287 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18287step0 raw18287; decide +kernel
      have hl : raw18287step0Labels = raw18287Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18287 raw18287Labels permutation680 permutation3
    mixedMoment B raw18287step0 raw18287step0Labels = mixedMoment B raw18287step1 raw18287step1Labels := by
      have ha : raw18287step1 = -raw18287step0 := by apply Matrix.ext; change ∀ i j, raw18287step1 i j = -(raw18287step0 i j); unfold raw18287step1 raw18287step0; decide +kernel
      have hl : raw18287step1Labels = raw18287step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18287step1 raw18287step1Labels = mixedMoment B raw18287step2 raw18287step2Labels := by
      have ha : raw18287step2 = raw18287step1 := by apply Matrix.ext; unfold raw18287step2 raw18287step1; decide +kernel
      have hl : raw18287step1Labels = labelEmbedding6 ∘ raw18287step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18287step1 raw18287step1Labels raw18287step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5344 node5344Labels := by rfl

theorem canonical18288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18288 raw18288Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18288 raw18288Labels = mixedMoment B raw18288step0 raw18288step0Labels := by
      have ha : raw18288step0 = (fun i j => raw18288 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18288step0 raw18288; decide +kernel
      have hl : raw18288step0Labels = raw18288Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18288 raw18288Labels permutation159 permutation3
    mixedMoment B raw18288step0 raw18288step0Labels = mixedMoment B raw18288step1 raw18288step1Labels := by
      have ha : raw18288step1 = raw18288step0 := by apply Matrix.ext; unfold raw18288step1 raw18288step0; decide +kernel
      have hl : raw18288step0Labels = labelEmbedding6 ∘ raw18288step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18288step0 raw18288step0Labels raw18288step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical18289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18289 raw18289Labels = mixedMoment B node4778 node4778Labels := by
  calc
    mixedMoment B raw18289 raw18289Labels = mixedMoment B raw18289step0 raw18289step0Labels := by
      have ha : raw18289step0 = (fun i j => raw18289 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18289step0 raw18289; decide +kernel
      have hl : raw18289step0Labels = raw18289Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18289 raw18289Labels permutation158 permutation3
    mixedMoment B raw18289step0 raw18289step0Labels = mixedMoment B raw18289step1 raw18289step1Labels := by
      have ha : raw18289step1 = raw18289step0 := by apply Matrix.ext; unfold raw18289step1 raw18289step0; decide +kernel
      have hl : raw18289step0Labels = labelEmbedding6 ∘ raw18289step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18289step0 raw18289step0Labels raw18289step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4778 node4778Labels := by rfl

theorem canonical18290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18290 raw18290Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw18290 raw18290Labels = mixedMoment B raw18290step0 raw18290step0Labels := by
      have ha : raw18290step0 = (fun i j => raw18290 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18290step0 raw18290; decide +kernel
      have hl : raw18290step0Labels = raw18290Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18290 raw18290Labels permutation682 permutation3
    mixedMoment B raw18290step0 raw18290step0Labels = mixedMoment B raw18290step1 raw18290step1Labels := by
      have ha : raw18290step1 = -raw18290step0 := by apply Matrix.ext; change ∀ i j, raw18290step1 i j = -(raw18290step0 i j); unfold raw18290step1 raw18290step0; decide +kernel
      have hl : raw18290step1Labels = raw18290step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18290step1 raw18290step1Labels = mixedMoment B raw18290step2 raw18290step2Labels := by
      have ha : raw18290step2 = raw18290step1 := by apply Matrix.ext; unfold raw18290step2 raw18290step1; decide +kernel
      have hl : raw18290step1Labels = labelEmbedding6 ∘ raw18290step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18290step1 raw18290step1Labels raw18290step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

theorem canonical18291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18291 raw18291Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw18291 raw18291Labels = mixedMoment B raw18291step0 raw18291step0Labels := by
      have ha : raw18291step0 = (fun i j => raw18291 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18291step0 raw18291; decide +kernel
      have hl : raw18291step0Labels = raw18291Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18291 raw18291Labels permutation686 permutation3
    mixedMoment B raw18291step0 raw18291step0Labels = mixedMoment B raw18291step1 raw18291step1Labels := by
      have ha : raw18291step1 = -raw18291step0 := by apply Matrix.ext; change ∀ i j, raw18291step1 i j = -(raw18291step0 i j); unfold raw18291step1 raw18291step0; decide +kernel
      have hl : raw18291step1Labels = raw18291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18291step1 raw18291step1Labels = mixedMoment B raw18291step2 raw18291step2Labels := by
      have ha : raw18291step2 = raw18291step1 := by apply Matrix.ext; unfold raw18291step2 raw18291step1; decide +kernel
      have hl : raw18291step1Labels = labelEmbedding6 ∘ raw18291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18291step1 raw18291step1Labels raw18291step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

theorem canonical18292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18292 raw18292Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw18292 raw18292Labels = mixedMoment B raw18292step0 raw18292step0Labels := by
      have ha : raw18292step0 = (fun i j => raw18292 (permutation644 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18292step0 raw18292; decide +kernel
      have hl : raw18292step0Labels = raw18292Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18292 raw18292Labels permutation644 permutation5
    mixedMoment B raw18292step0 raw18292step0Labels = mixedMoment B raw18292step1 raw18292step1Labels := by
      have ha : raw18292step1 = raw18292step0 := by apply Matrix.ext; unfold raw18292step1 raw18292step0; decide +kernel
      have hl : raw18292step0Labels = labelEmbedding8 ∘ raw18292step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18292step0 raw18292step0Labels raw18292step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

theorem canonical18293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18293 raw18293Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw18293 raw18293Labels = mixedMoment B raw18293step0 raw18293step0Labels := by
      have ha : raw18293step0 = (fun i j => raw18293 (permutation632 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18293step0 raw18293; decide +kernel
      have hl : raw18293step0Labels = raw18293Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18293 raw18293Labels permutation632 permutation5
    mixedMoment B raw18293step0 raw18293step0Labels = mixedMoment B raw18293step1 raw18293step1Labels := by
      have ha : raw18293step1 = raw18293step0 := by apply Matrix.ext; unfold raw18293step1 raw18293step0; decide +kernel
      have hl : raw18293step0Labels = labelEmbedding8 ∘ raw18293step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18293step0 raw18293step0Labels raw18293step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

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

theorem canonical18455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18455 raw18455Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw18455 raw18455Labels = mixedMoment B raw18455step0 raw18455step0Labels := by
      have ha : raw18455step0 = (fun i j => raw18455 (permutation367 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18455step0 raw18455; decide +kernel
      have hl : raw18455step0Labels = raw18455Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18455 raw18455Labels permutation367 permutation6
    mixedMoment B raw18455step0 raw18455step0Labels = mixedMoment B raw18455step1 raw18455step1Labels := by
      have ha : raw18455step1 = -raw18455step0 := by apply Matrix.ext; change ∀ i j, raw18455step1 i j = -(raw18455step0 i j); unfold raw18455step1 raw18455step0; decide +kernel
      have hl : raw18455step1Labels = raw18455step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18455step1 raw18455step1Labels = mixedMoment B raw18455step2 raw18455step2Labels := by
      have ha : raw18455step2 = raw18455step1 := by apply Matrix.ext; unfold raw18455step2 raw18455step1; decide +kernel
      have hl : raw18455step1Labels = labelEmbedding9 ∘ raw18455step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18455step1 raw18455step1Labels raw18455step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical18456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18456 raw18456Labels = mixedMoment B node5479 node5479Labels := by
  calc
    mixedMoment B raw18456 raw18456Labels = mixedMoment B raw18456step0 raw18456step0Labels := by
      have ha : raw18456step0 = (fun i j => raw18456 (permutation367 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18456step0 raw18456; decide +kernel
      have hl : raw18456step0Labels = raw18456Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18456 raw18456Labels permutation367 permutation7
    mixedMoment B raw18456step0 raw18456step0Labels = mixedMoment B raw18456step1 raw18456step1Labels := by
      have ha : raw18456step1 = -raw18456step0 := by apply Matrix.ext; change ∀ i j, raw18456step1 i j = -(raw18456step0 i j); unfold raw18456step1 raw18456step0; decide +kernel
      have hl : raw18456step1Labels = raw18456step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18456step1 raw18456step1Labels = mixedMoment B raw18456step2 raw18456step2Labels := by
      have ha : raw18456step2 = raw18456step1 := by apply Matrix.ext; unfold raw18456step2 raw18456step1; decide +kernel
      have hl : raw18456step1Labels = labelEmbedding10 ∘ raw18456step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18456step1 raw18456step1Labels raw18456step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5479 node5479Labels := by rfl

theorem canonical18457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18457 raw18457Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18457 raw18457Labels = mixedMoment B raw18457step0 raw18457step0Labels := by
      have ha : raw18457step0 = (fun i j => raw18457 (permutation369 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18457step0 raw18457; decide +kernel
      have hl : raw18457step0Labels = raw18457Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18457 raw18457Labels permutation369 permutation6
    mixedMoment B raw18457step0 raw18457step0Labels = mixedMoment B raw18457step1 raw18457step1Labels := by
      have ha : raw18457step1 = -raw18457step0 := by apply Matrix.ext; change ∀ i j, raw18457step1 i j = -(raw18457step0 i j); unfold raw18457step1 raw18457step0; decide +kernel
      have hl : raw18457step1Labels = raw18457step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18457step1 raw18457step1Labels = mixedMoment B raw18457step2 raw18457step2Labels := by
      have ha : raw18457step2 = raw18457step1 := by apply Matrix.ext; unfold raw18457step2 raw18457step1; decide +kernel
      have hl : raw18457step1Labels = labelEmbedding9 ∘ raw18457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18457step1 raw18457step1Labels raw18457step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical18458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18458 raw18458Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18458 raw18458Labels = mixedMoment B raw18458step0 raw18458step0Labels := by
      have ha : raw18458step0 = (fun i j => raw18458 (permutation368 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18458step0 raw18458; decide +kernel
      have hl : raw18458step0Labels = raw18458Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18458 raw18458Labels permutation368 permutation6
    mixedMoment B raw18458step0 raw18458step0Labels = mixedMoment B raw18458step1 raw18458step1Labels := by
      have ha : raw18458step1 = -raw18458step0 := by apply Matrix.ext; change ∀ i j, raw18458step1 i j = -(raw18458step0 i j); unfold raw18458step1 raw18458step0; decide +kernel
      have hl : raw18458step1Labels = raw18458step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18458step1 raw18458step1Labels = mixedMoment B raw18458step2 raw18458step2Labels := by
      have ha : raw18458step2 = raw18458step1 := by apply Matrix.ext; unfold raw18458step2 raw18458step1; decide +kernel
      have hl : raw18458step1Labels = labelEmbedding9 ∘ raw18458step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18458step1 raw18458step1Labels raw18458step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical18459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18459 raw18459Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18459 raw18459Labels = mixedMoment B raw18459step0 raw18459step0Labels := by
      have ha : raw18459step0 = (fun i j => raw18459 (permutation367 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18459step0 raw18459; decide +kernel
      have hl : raw18459step0Labels = raw18459Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18459 raw18459Labels permutation367 permutation6
    mixedMoment B raw18459step0 raw18459step0Labels = mixedMoment B raw18459step1 raw18459step1Labels := by
      have ha : raw18459step1 = -raw18459step0 := by apply Matrix.ext; change ∀ i j, raw18459step1 i j = -(raw18459step0 i j); unfold raw18459step1 raw18459step0; decide +kernel
      have hl : raw18459step1Labels = raw18459step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18459step1 raw18459step1Labels = mixedMoment B raw18459step2 raw18459step2Labels := by
      have ha : raw18459step2 = raw18459step1 := by apply Matrix.ext; unfold raw18459step2 raw18459step1; decide +kernel
      have hl : raw18459step1Labels = labelEmbedding9 ∘ raw18459step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18459step1 raw18459step1Labels raw18459step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical18460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18460 raw18460Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw18460 raw18460Labels = mixedMoment B raw18460step0 raw18460step0Labels := by
      have ha : raw18460step0 = (fun i j => raw18460 (permutation216 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18460step0 raw18460; decide +kernel
      have hl : raw18460step0Labels = raw18460Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18460 raw18460Labels permutation216 permutation5
    mixedMoment B raw18460step0 raw18460step0Labels = mixedMoment B raw18460step1 raw18460step1Labels := by
      have ha : raw18460step1 = -raw18460step0 := by apply Matrix.ext; change ∀ i j, raw18460step1 i j = -(raw18460step0 i j); unfold raw18460step1 raw18460step0; decide +kernel
      have hl : raw18460step1Labels = raw18460step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18460step1 raw18460step1Labels = mixedMoment B raw18460step2 raw18460step2Labels := by
      have ha : raw18460step2 = raw18460step1 := by apply Matrix.ext; unfold raw18460step2 raw18460step1; decide +kernel
      have hl : raw18460step1Labels = labelEmbedding8 ∘ raw18460step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18460step1 raw18460step1Labels raw18460step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

theorem canonical18461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18461 raw18461Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw18461 raw18461Labels = mixedMoment B raw18461step0 raw18461step0Labels := by
      have ha : raw18461step0 = (fun i j => raw18461 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18461step0 raw18461; decide +kernel
      have hl : raw18461step0Labels = raw18461Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18461 raw18461Labels permutation176 permutation3
    mixedMoment B raw18461step0 raw18461step0Labels = mixedMoment B raw18461step1 raw18461step1Labels := by
      have ha : raw18461step1 = raw18461step0 := by apply Matrix.ext; unfold raw18461step1 raw18461step0; decide +kernel
      have hl : raw18461step0Labels = labelEmbedding6 ∘ raw18461step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18461step0 raw18461step0Labels raw18461step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical18462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18462 raw18462Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18462 raw18462Labels = mixedMoment B raw18462step0 raw18462step0Labels := by
      have ha : raw18462step0 = (fun i j => raw18462 (permutation378 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18462step0 raw18462; decide +kernel
      have hl : raw18462step0Labels = raw18462Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18462 raw18462Labels permutation378 permutation4
    mixedMoment B raw18462step0 raw18462step0Labels = mixedMoment B raw18462step1 raw18462step1Labels := by
      have ha : raw18462step1 = raw18462step0 := by apply Matrix.ext; unfold raw18462step1 raw18462step0; decide +kernel
      have hl : raw18462step0Labels = labelEmbedding7 ∘ raw18462step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18462step0 raw18462step0Labels raw18462step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical18463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18463 raw18463Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18463 raw18463Labels = mixedMoment B raw18463step0 raw18463step0Labels := by
      have ha : raw18463step0 = (fun i j => raw18463 (permutation374 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18463step0 raw18463; decide +kernel
      have hl : raw18463step0Labels = raw18463Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18463 raw18463Labels permutation374 permutation4
    mixedMoment B raw18463step0 raw18463step0Labels = mixedMoment B raw18463step1 raw18463step1Labels := by
      have ha : raw18463step1 = raw18463step0 := by apply Matrix.ext; unfold raw18463step1 raw18463step0; decide +kernel
      have hl : raw18463step0Labels = labelEmbedding7 ∘ raw18463step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18463step0 raw18463step0Labels raw18463step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical18464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18464 raw18464Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18464 raw18464Labels = mixedMoment B raw18464step0 raw18464step0Labels := by
      have ha : raw18464step0 = (fun i j => raw18464 (permutation373 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18464step0 raw18464; decide +kernel
      have hl : raw18464step0Labels = raw18464Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18464 raw18464Labels permutation373 permutation4
    mixedMoment B raw18464step0 raw18464step0Labels = mixedMoment B raw18464step1 raw18464step1Labels := by
      have ha : raw18464step1 = raw18464step0 := by apply Matrix.ext; unfold raw18464step1 raw18464step0; decide +kernel
      have hl : raw18464step0Labels = labelEmbedding7 ∘ raw18464step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18464step0 raw18464step0Labels raw18464step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical18465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18465 raw18465Labels = mixedMoment B node4830 node4830Labels := by
  calc
    mixedMoment B raw18465 raw18465Labels = mixedMoment B raw18465step0 raw18465step0Labels := by
      have ha : raw18465step0 = (fun i j => raw18465 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18465step0 raw18465; decide +kernel
      have hl : raw18465step0Labels = raw18465Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18465 raw18465Labels permutation161 permutation3
    mixedMoment B raw18465step0 raw18465step0Labels = mixedMoment B raw18465step1 raw18465step1Labels := by
      have ha : raw18465step1 = raw18465step0 := by apply Matrix.ext; unfold raw18465step1 raw18465step0; decide +kernel
      have hl : raw18465step0Labels = labelEmbedding6 ∘ raw18465step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18465step0 raw18465step0Labels raw18465step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4830 node4830Labels := by rfl

theorem canonical18466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18466 raw18466Labels = mixedMoment B node5277 node5277Labels := by
  calc
    mixedMoment B raw18466 raw18466Labels = mixedMoment B raw18466step0 raw18466step0Labels := by
      have ha : raw18466step0 = (fun i j => raw18466 (permutation394 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18466step0 raw18466; decide +kernel
      have hl : raw18466step0Labels = raw18466Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18466 raw18466Labels permutation394 permutation4
    mixedMoment B raw18466step0 raw18466step0Labels = mixedMoment B raw18466step1 raw18466step1Labels := by
      have ha : raw18466step1 = raw18466step0 := by apply Matrix.ext; unfold raw18466step1 raw18466step0; decide +kernel
      have hl : raw18466step0Labels = labelEmbedding7 ∘ raw18466step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18466step0 raw18466step0Labels raw18466step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5277 node5277Labels := by rfl

theorem canonical18467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18467 raw18467Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw18467 raw18467Labels = mixedMoment B raw18467step0 raw18467step0Labels := by
      have ha : raw18467step0 = (fun i j => raw18467 (permutation378 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18467step0 raw18467; decide +kernel
      have hl : raw18467step0Labels = raw18467Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18467 raw18467Labels permutation378 permutation4
    mixedMoment B raw18467step0 raw18467step0Labels = mixedMoment B raw18467step1 raw18467step1Labels := by
      have ha : raw18467step1 = raw18467step0 := by apply Matrix.ext; unfold raw18467step1 raw18467step0; decide +kernel
      have hl : raw18467step0Labels = labelEmbedding7 ∘ raw18467step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18467step0 raw18467step0Labels raw18467step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical18468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18468 raw18468Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw18468 raw18468Labels = mixedMoment B raw18468step0 raw18468step0Labels := by
      have ha : raw18468step0 = (fun i j => raw18468 (permutation374 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18468step0 raw18468; decide +kernel
      have hl : raw18468step0Labels = raw18468Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18468 raw18468Labels permutation374 permutation4
    mixedMoment B raw18468step0 raw18468step0Labels = mixedMoment B raw18468step1 raw18468step1Labels := by
      have ha : raw18468step1 = raw18468step0 := by apply Matrix.ext; unfold raw18468step1 raw18468step0; decide +kernel
      have hl : raw18468step0Labels = labelEmbedding7 ∘ raw18468step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18468step0 raw18468step0Labels raw18468step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical18469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18469 raw18469Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw18469 raw18469Labels = mixedMoment B raw18469step0 raw18469step0Labels := by
      have ha : raw18469step0 = (fun i j => raw18469 (permutation373 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18469step0 raw18469; decide +kernel
      have hl : raw18469step0Labels = raw18469Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18469 raw18469Labels permutation373 permutation4
    mixedMoment B raw18469step0 raw18469step0Labels = mixedMoment B raw18469step1 raw18469step1Labels := by
      have ha : raw18469step1 = raw18469step0 := by apply Matrix.ext; unfold raw18469step1 raw18469step0; decide +kernel
      have hl : raw18469step0Labels = labelEmbedding7 ∘ raw18469step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18469step0 raw18469step0Labels raw18469step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical18470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18470 raw18470Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw18470 raw18470Labels = mixedMoment B raw18470step0 raw18470step0Labels := by
      have ha : raw18470step0 = (fun i j => raw18470 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18470step0 raw18470; decide +kernel
      have hl : raw18470step0Labels = raw18470Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18470 raw18470Labels permutation155 permutation3
    mixedMoment B raw18470step0 raw18470step0Labels = mixedMoment B raw18470step1 raw18470step1Labels := by
      have ha : raw18470step1 = raw18470step0 := by apply Matrix.ext; unfold raw18470step1 raw18470step0; decide +kernel
      have hl : raw18470step0Labels = labelEmbedding6 ∘ raw18470step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18470step0 raw18470step0Labels raw18470step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4815 node4815Labels := by rfl

theorem canonical18471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18471 raw18471Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw18471 raw18471Labels = mixedMoment B raw18471step0 raw18471step0Labels := by
      have ha : raw18471step0 = (fun i j => raw18471 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18471step0 raw18471; decide +kernel
      have hl : raw18471step0Labels = raw18471Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18471 raw18471Labels permutation155 permutation3
    mixedMoment B raw18471step0 raw18471step0Labels = mixedMoment B raw18471step1 raw18471step1Labels := by
      have ha : raw18471step1 = raw18471step0 := by apply Matrix.ext; unfold raw18471step1 raw18471step0; decide +kernel
      have hl : raw18471step0Labels = labelEmbedding6 ∘ raw18471step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18471step0 raw18471step0Labels raw18471step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

theorem canonical18472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18472 raw18472Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw18472 raw18472Labels = mixedMoment B raw18472step0 raw18472step0Labels := by
      have ha : raw18472step0 = (fun i j => raw18472 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18472step0 raw18472; decide +kernel
      have hl : raw18472step0Labels = raw18472Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18472 raw18472Labels permutation155 permutation3
    mixedMoment B raw18472step0 raw18472step0Labels = mixedMoment B raw18472step1 raw18472step1Labels := by
      have ha : raw18472step1 = raw18472step0 := by apply Matrix.ext; unfold raw18472step1 raw18472step0; decide +kernel
      have hl : raw18472step0Labels = labelEmbedding6 ∘ raw18472step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18472step0 raw18472step0Labels raw18472step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical18473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18473 raw18473Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18473 raw18473Labels = mixedMoment B raw18473step0 raw18473step0Labels := by
      have ha : raw18473step0 = (fun i j => raw18473 (permutation229 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18473step0 raw18473; decide +kernel
      have hl : raw18473step0Labels = raw18473Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18473 raw18473Labels permutation229 permutation5
    mixedMoment B raw18473step0 raw18473step0Labels = mixedMoment B raw18473step1 raw18473step1Labels := by
      have ha : raw18473step1 = -raw18473step0 := by apply Matrix.ext; change ∀ i j, raw18473step1 i j = -(raw18473step0 i j); unfold raw18473step1 raw18473step0; decide +kernel
      have hl : raw18473step1Labels = raw18473step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18473step1 raw18473step1Labels = mixedMoment B raw18473step2 raw18473step2Labels := by
      have ha : raw18473step2 = raw18473step1 := by apply Matrix.ext; unfold raw18473step2 raw18473step1; decide +kernel
      have hl : raw18473step1Labels = labelEmbedding8 ∘ raw18473step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18473step1 raw18473step1Labels raw18473step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical18474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18474 raw18474Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18474 raw18474Labels = mixedMoment B raw18474step0 raw18474step0Labels := by
      have ha : raw18474step0 = (fun i j => raw18474 (permutation251 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18474step0 raw18474; decide +kernel
      have hl : raw18474step0Labels = raw18474Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18474 raw18474Labels permutation251 permutation5
    mixedMoment B raw18474step0 raw18474step0Labels = mixedMoment B raw18474step1 raw18474step1Labels := by
      have ha : raw18474step1 = -raw18474step0 := by apply Matrix.ext; change ∀ i j, raw18474step1 i j = -(raw18474step0 i j); unfold raw18474step1 raw18474step0; decide +kernel
      have hl : raw18474step1Labels = raw18474step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18474step1 raw18474step1Labels = mixedMoment B raw18474step2 raw18474step2Labels := by
      have ha : raw18474step2 = raw18474step1 := by apply Matrix.ext; unfold raw18474step2 raw18474step1; decide +kernel
      have hl : raw18474step1Labels = labelEmbedding8 ∘ raw18474step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18474step1 raw18474step1Labels raw18474step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical18475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18475 raw18475Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw18475 raw18475Labels = mixedMoment B raw18475step0 raw18475step0Labels := by
      have ha : raw18475step0 = (fun i j => raw18475 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18475step0 raw18475; decide +kernel
      have hl : raw18475step0Labels = raw18475Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18475 raw18475Labels permutation153 permutation3
    mixedMoment B raw18475step0 raw18475step0Labels = mixedMoment B raw18475step1 raw18475step1Labels := by
      have ha : raw18475step1 = raw18475step0 := by apply Matrix.ext; unfold raw18475step1 raw18475step0; decide +kernel
      have hl : raw18475step0Labels = labelEmbedding6 ∘ raw18475step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18475step0 raw18475step0Labels raw18475step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4815 node4815Labels := by rfl

theorem canonical18476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18476 raw18476Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw18476 raw18476Labels = mixedMoment B raw18476step0 raw18476step0Labels := by
      have ha : raw18476step0 = (fun i j => raw18476 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18476step0 raw18476; decide +kernel
      have hl : raw18476step0Labels = raw18476Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18476 raw18476Labels permutation153 permutation3
    mixedMoment B raw18476step0 raw18476step0Labels = mixedMoment B raw18476step1 raw18476step1Labels := by
      have ha : raw18476step1 = raw18476step0 := by apply Matrix.ext; unfold raw18476step1 raw18476step0; decide +kernel
      have hl : raw18476step0Labels = labelEmbedding6 ∘ raw18476step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18476step0 raw18476step0Labels raw18476step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

theorem canonical18477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18477 raw18477Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw18477 raw18477Labels = mixedMoment B raw18477step0 raw18477step0Labels := by
      have ha : raw18477step0 = (fun i j => raw18477 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18477step0 raw18477; decide +kernel
      have hl : raw18477step0Labels = raw18477Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18477 raw18477Labels permutation153 permutation3
    mixedMoment B raw18477step0 raw18477step0Labels = mixedMoment B raw18477step1 raw18477step1Labels := by
      have ha : raw18477step1 = raw18477step0 := by apply Matrix.ext; unfold raw18477step1 raw18477step0; decide +kernel
      have hl : raw18477step0Labels = labelEmbedding6 ∘ raw18477step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18477step0 raw18477step0Labels raw18477step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical18478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18478 raw18478Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18478 raw18478Labels = mixedMoment B raw18478step0 raw18478step0Labels := by
      have ha : raw18478step0 = (fun i j => raw18478 (permutation205 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18478step0 raw18478; decide +kernel
      have hl : raw18478step0Labels = raw18478Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18478 raw18478Labels permutation205 permutation5
    mixedMoment B raw18478step0 raw18478step0Labels = mixedMoment B raw18478step1 raw18478step1Labels := by
      have ha : raw18478step1 = -raw18478step0 := by apply Matrix.ext; change ∀ i j, raw18478step1 i j = -(raw18478step0 i j); unfold raw18478step1 raw18478step0; decide +kernel
      have hl : raw18478step1Labels = raw18478step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18478step1 raw18478step1Labels = mixedMoment B raw18478step2 raw18478step2Labels := by
      have ha : raw18478step2 = raw18478step1 := by apply Matrix.ext; unfold raw18478step2 raw18478step1; decide +kernel
      have hl : raw18478step1Labels = labelEmbedding8 ∘ raw18478step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18478step1 raw18478step1Labels raw18478step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical18479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18479 raw18479Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18479 raw18479Labels = mixedMoment B raw18479step0 raw18479step0Labels := by
      have ha : raw18479step0 = (fun i j => raw18479 (permutation249 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18479step0 raw18479; decide +kernel
      have hl : raw18479step0Labels = raw18479Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18479 raw18479Labels permutation249 permutation5
    mixedMoment B raw18479step0 raw18479step0Labels = mixedMoment B raw18479step1 raw18479step1Labels := by
      have ha : raw18479step1 = -raw18479step0 := by apply Matrix.ext; change ∀ i j, raw18479step1 i j = -(raw18479step0 i j); unfold raw18479step1 raw18479step0; decide +kernel
      have hl : raw18479step1Labels = raw18479step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18479step1 raw18479step1Labels = mixedMoment B raw18479step2 raw18479step2Labels := by
      have ha : raw18479step2 = raw18479step1 := by apply Matrix.ext; unfold raw18479step2 raw18479step1; decide +kernel
      have hl : raw18479step1Labels = labelEmbedding8 ∘ raw18479step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18479step1 raw18479step1Labels raw18479step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical18480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18480 raw18480Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw18480 raw18480Labels = mixedMoment B raw18480step0 raw18480step0Labels := by
      have ha : raw18480step0 = (fun i j => raw18480 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18480step0 raw18480; decide +kernel
      have hl : raw18480step0Labels = raw18480Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18480 raw18480Labels permutation152 permutation3
    mixedMoment B raw18480step0 raw18480step0Labels = mixedMoment B raw18480step1 raw18480step1Labels := by
      have ha : raw18480step1 = raw18480step0 := by apply Matrix.ext; unfold raw18480step1 raw18480step0; decide +kernel
      have hl : raw18480step0Labels = labelEmbedding6 ∘ raw18480step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18480step0 raw18480step0Labels raw18480step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4815 node4815Labels := by rfl

theorem canonical18481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18481 raw18481Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw18481 raw18481Labels = mixedMoment B raw18481step0 raw18481step0Labels := by
      have ha : raw18481step0 = (fun i j => raw18481 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18481step0 raw18481; decide +kernel
      have hl : raw18481step0Labels = raw18481Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18481 raw18481Labels permutation152 permutation3
    mixedMoment B raw18481step0 raw18481step0Labels = mixedMoment B raw18481step1 raw18481step1Labels := by
      have ha : raw18481step1 = raw18481step0 := by apply Matrix.ext; unfold raw18481step1 raw18481step0; decide +kernel
      have hl : raw18481step0Labels = labelEmbedding6 ∘ raw18481step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18481step0 raw18481step0Labels raw18481step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

theorem canonical18482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18482 raw18482Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw18482 raw18482Labels = mixedMoment B raw18482step0 raw18482step0Labels := by
      have ha : raw18482step0 = (fun i j => raw18482 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18482step0 raw18482; decide +kernel
      have hl : raw18482step0Labels = raw18482Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18482 raw18482Labels permutation152 permutation3
    mixedMoment B raw18482step0 raw18482step0Labels = mixedMoment B raw18482step1 raw18482step1Labels := by
      have ha : raw18482step1 = raw18482step0 := by apply Matrix.ext; unfold raw18482step1 raw18482step0; decide +kernel
      have hl : raw18482step0Labels = labelEmbedding6 ∘ raw18482step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18482step0 raw18482step0Labels raw18482step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical18483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18483 raw18483Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18483 raw18483Labels = mixedMoment B raw18483step0 raw18483step0Labels := by
      have ha : raw18483step0 = (fun i j => raw18483 (permutation203 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18483step0 raw18483; decide +kernel
      have hl : raw18483step0Labels = raw18483Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18483 raw18483Labels permutation203 permutation5
    mixedMoment B raw18483step0 raw18483step0Labels = mixedMoment B raw18483step1 raw18483step1Labels := by
      have ha : raw18483step1 = -raw18483step0 := by apply Matrix.ext; change ∀ i j, raw18483step1 i j = -(raw18483step0 i j); unfold raw18483step1 raw18483step0; decide +kernel
      have hl : raw18483step1Labels = raw18483step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18483step1 raw18483step1Labels = mixedMoment B raw18483step2 raw18483step2Labels := by
      have ha : raw18483step2 = raw18483step1 := by apply Matrix.ext; unfold raw18483step2 raw18483step1; decide +kernel
      have hl : raw18483step1Labels = labelEmbedding8 ∘ raw18483step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18483step1 raw18483step1Labels raw18483step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical18484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18484 raw18484Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18484 raw18484Labels = mixedMoment B raw18484step0 raw18484step0Labels := by
      have ha : raw18484step0 = (fun i j => raw18484 (permutation227 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18484step0 raw18484; decide +kernel
      have hl : raw18484step0Labels = raw18484Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18484 raw18484Labels permutation227 permutation5
    mixedMoment B raw18484step0 raw18484step0Labels = mixedMoment B raw18484step1 raw18484step1Labels := by
      have ha : raw18484step1 = -raw18484step0 := by apply Matrix.ext; change ∀ i j, raw18484step1 i j = -(raw18484step0 i j); unfold raw18484step1 raw18484step0; decide +kernel
      have hl : raw18484step1Labels = raw18484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18484step1 raw18484step1Labels = mixedMoment B raw18484step2 raw18484step2Labels := by
      have ha : raw18484step2 = raw18484step1 := by apply Matrix.ext; unfold raw18484step2 raw18484step1; decide +kernel
      have hl : raw18484step1Labels = labelEmbedding8 ∘ raw18484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18484step1 raw18484step1Labels raw18484step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

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

theorem canonical2379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2379 raw2379Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw2379 raw2379Labels = mixedMoment B raw2379step0 raw2379step0Labels := by
      have ha : raw2379step0 = (fun i j => raw2379 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2379step0 raw2379; decide +kernel
      have hl : raw2379step0Labels = raw2379Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2379 raw2379Labels permutation152 permutation4
    mixedMoment B raw2379step0 raw2379step0Labels = mixedMoment B raw2379step1 raw2379step1Labels := by
      have ha : raw2379step1 = raw2379step0 := by apply Matrix.ext; unfold raw2379step1 raw2379step0; decide +kernel
      have hl : raw2379step0Labels = labelEmbedding7 ∘ raw2379step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2379step0 raw2379step0Labels raw2379step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5341 node5341Labels := by rfl

theorem canonical2380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2380 raw2380Labels = mixedMoment B node3678 node3678Labels := by
  calc
    mixedMoment B raw2380 raw2380Labels = mixedMoment B raw2380step0 raw2380step0Labels := by
      have ha : raw2380step0 = (fun i j => raw2380 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2380step0 raw2380; decide +kernel
      have hl : raw2380step0Labels = raw2380Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2380 raw2380Labels permutation152 permutation4
    _ = mixedMoment B node3678 node3678Labels := by rfl

theorem canonical2381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2381 raw2381Labels = mixedMoment B node3744 node3744Labels := by
  calc
    mixedMoment B raw2381 raw2381Labels = mixedMoment B raw2381step0 raw2381step0Labels := by
      have ha : raw2381step0 = (fun i j => raw2381 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2381step0 raw2381; decide +kernel
      have hl : raw2381step0Labels = raw2381Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2381 raw2381Labels permutation688 permutation6
    mixedMoment B raw2381step0 raw2381step0Labels = mixedMoment B raw2381step1 raw2381step1Labels := by
      have ha : raw2381step1 = raw2381step0 := by apply Matrix.ext; unfold raw2381step1 raw2381step0; decide +kernel
      have hl : raw2381step0Labels = labelEmbedding1 ∘ raw2381step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2381step0 raw2381step0Labels raw2381step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3744 node3744Labels := by rfl

theorem canonical2382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2382 raw2382Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw2382 raw2382Labels = mixedMoment B raw2382step0 raw2382step0Labels := by
      have ha : raw2382step0 = (fun i j => raw2382 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2382step0 raw2382; decide +kernel
      have hl : raw2382step0Labels = raw2382Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2382 raw2382Labels permutation152 permutation4
    mixedMoment B raw2382step0 raw2382step0Labels = mixedMoment B raw2382step1 raw2382step1Labels := by
      have ha : raw2382step1 = raw2382step0 := by apply Matrix.ext; unfold raw2382step1 raw2382step0; decide +kernel
      have hl : raw2382step0Labels = labelEmbedding7 ∘ raw2382step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2382step0 raw2382step0Labels raw2382step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5344 node5344Labels := by rfl

theorem canonical2383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2383 raw2383Labels = mixedMoment B node3681 node3681Labels := by
  calc
    mixedMoment B raw2383 raw2383Labels = mixedMoment B raw2383step0 raw2383step0Labels := by
      have ha : raw2383step0 = (fun i j => raw2383 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2383step0 raw2383; decide +kernel
      have hl : raw2383step0Labels = raw2383Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2383 raw2383Labels permutation152 permutation4
    _ = mixedMoment B node3681 node3681Labels := by rfl

theorem canonical2384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2384 raw2384Labels = mixedMoment B node3681 node3681Labels := by
  calc
    mixedMoment B raw2384 raw2384Labels = mixedMoment B raw2384step0 raw2384step0Labels := by
      have ha : raw2384step0 = (fun i j => raw2384 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2384step0 raw2384; decide +kernel
      have hl : raw2384step0Labels = raw2384Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2384 raw2384Labels permutation688 permutation6
    mixedMoment B raw2384step0 raw2384step0Labels = mixedMoment B raw2384step1 raw2384step1Labels := by
      have ha : raw2384step1 = raw2384step0 := by apply Matrix.ext; unfold raw2384step1 raw2384step0; decide +kernel
      have hl : raw2384step0Labels = labelEmbedding1 ∘ raw2384step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2384step0 raw2384step0Labels raw2384step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3681 node3681Labels := by rfl

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

theorem canonical2430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2430 raw2430Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw2430 raw2430Labels = mixedMoment B raw2430step0 raw2430step0Labels := by
      have ha : raw2430step0 = (fun i j => raw2430 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2430step0 raw2430; decide +kernel
      have hl : raw2430step0Labels = raw2430Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2430 raw2430Labels permutation152 permutation4
    mixedMoment B raw2430step0 raw2430step0Labels = mixedMoment B raw2430step1 raw2430step1Labels := by
      have ha : raw2430step1 = raw2430step0 := by apply Matrix.ext; unfold raw2430step1 raw2430step0; decide +kernel
      have hl : raw2430step0Labels = labelEmbedding7 ∘ raw2430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2430step0 raw2430step0Labels raw2430step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical2431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2431 raw2431Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw2431 raw2431Labels = mixedMoment B raw2431step0 raw2431step0Labels := by
      have ha : raw2431step0 = (fun i j => raw2431 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2431step0 raw2431; decide +kernel
      have hl : raw2431step0Labels = raw2431Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2431 raw2431Labels permutation152 permutation4
    _ = mixedMoment B node3719 node3719Labels := by rfl

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

theorem canonical2432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2432 raw2432Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw2432 raw2432Labels = mixedMoment B raw2432step0 raw2432step0Labels := by
      have ha : raw2432step0 = (fun i j => raw2432 (permutation686 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2432step0 raw2432; decide +kernel
      have hl : raw2432step0Labels = raw2432Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2432 raw2432Labels permutation686 permutation6
    mixedMoment B raw2432step0 raw2432step0Labels = mixedMoment B raw2432step1 raw2432step1Labels := by
      have ha : raw2432step1 = raw2432step0 := by apply Matrix.ext; unfold raw2432step1 raw2432step0; decide +kernel
      have hl : raw2432step0Labels = labelEmbedding1 ∘ raw2432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2432step0 raw2432step0Labels raw2432step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

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

theorem canonical2523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2523 raw2523Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw2523 raw2523Labels = mixedMoment B raw2523step0 raw2523step0Labels := by
      have ha : raw2523step0 = (fun i j => raw2523 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2523step0 raw2523; decide +kernel
      have hl : raw2523step0Labels = raw2523Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2523 raw2523Labels permutation32 permutation4
    mixedMoment B raw2523step0 raw2523step0Labels = mixedMoment B raw2523step1 raw2523step1Labels := by
      have ha : raw2523step1 = raw2523step0 := by apply Matrix.ext; unfold raw2523step1 raw2523step0; decide +kernel
      have hl : raw2523step0Labels = labelEmbedding7 ∘ raw2523step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2523step0 raw2523step0Labels raw2523step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

theorem canonical2524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2524 raw2524Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw2524 raw2524Labels = mixedMoment B raw2524step0 raw2524step0Labels := by
      have ha : raw2524step0 = (fun i j => raw2524 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2524step0 raw2524; decide +kernel
      have hl : raw2524step0Labels = raw2524Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2524 raw2524Labels permutation32 permutation4
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical2525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2525 raw2525Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw2525 raw2525Labels = mixedMoment B raw2525step0 raw2525step0Labels := by
      have ha : raw2525step0 = (fun i j => raw2525 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2525step0 raw2525; decide +kernel
      have hl : raw2525step0Labels = raw2525Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2525 raw2525Labels permutation143 permutation6
    mixedMoment B raw2525step0 raw2525step0Labels = mixedMoment B raw2525step1 raw2525step1Labels := by
      have ha : raw2525step1 = raw2525step0 := by apply Matrix.ext; unfold raw2525step1 raw2525step0; decide +kernel
      have hl : raw2525step0Labels = labelEmbedding1 ∘ raw2525step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2525step0 raw2525step0Labels raw2525step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12230 raw12230Labels = mixedMoment B node5430 node5430Labels := by
  calc
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical12232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12232 raw12232Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw12232 raw12232Labels = mixedMoment B raw12232step0 raw12232step0Labels := by
      have hz : ∀ j, raw12232 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12232step0 = (fun i j => raw12232 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12232step0 raw12232; decide +kernel
      have hl : raw12232step0Labels = raw12232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12232 raw12232Labels permutation265 hz
    mixedMoment B raw12232step0 raw12232step0Labels = mixedMoment B raw12232step1 raw12232step1Labels := by
      have ha : raw12232step1 = (fun i j => raw12232step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12232step1 raw12232step0; decide +kernel
      have hl : raw12232step1Labels = raw12232step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12232step0 raw12232step0Labels permutation40 permutation7
    mixedMoment B raw12232step1 raw12232step1Labels = mixedMoment B raw12232step2 raw12232step2Labels := by
      have ha : raw12232step2 = -raw12232step1 := by apply Matrix.ext; change ∀ i j, raw12232step2 i j = -(raw12232step1 i j); unfold raw12232step2 raw12232step1; decide +kernel
      have hl : raw12232step2Labels = raw12232step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12232step2 raw12232step2Labels = mixedMoment B raw12232step3 raw12232step3Labels := by
      have ha : raw12232step3 = raw12232step2 := by apply Matrix.ext; unfold raw12232step3 raw12232step2; decide +kernel
      have hl : raw12232step2Labels = labelEmbedding10 ∘ raw12232step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12232step2 raw12232step2Labels raw12232step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical12256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12256 raw12256Labels = mixedMoment B node5144 node5144Labels := by
  calc
    _ = mixedMoment B node5144 node5144Labels := by rfl

theorem canonical12258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12258 raw12258Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw12258 raw12258Labels = mixedMoment B raw12258step0 raw12258step0Labels := by
      have hz : ∀ j, raw12258 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12258step0 = (fun i j => raw12258 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12258step0 raw12258; decide +kernel
      have hl : raw12258step0Labels = raw12258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12258 raw12258Labels permutation265 hz
    mixedMoment B raw12258step0 raw12258step0Labels = mixedMoment B raw12258step1 raw12258step1Labels := by
      have ha : raw12258step1 = (fun i j => raw12258step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12258step1 raw12258step0; decide +kernel
      have hl : raw12258step1Labels = raw12258step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12258step0 raw12258step0Labels permutation38 permutation2
    _ = mixedMoment B node5258 node5258Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12290 raw12290Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw12290 raw12290Labels = mixedMoment B raw12290step0 raw12290step0Labels := by
      have ha : raw12290step0 = (fun i j => raw12290 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12290step0 raw12290; decide +kernel
      have hl : raw12290step0Labels = raw12290Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12290 raw12290Labels permutation202 permutation7
    mixedMoment B raw12290step0 raw12290step0Labels = mixedMoment B raw12290step1 raw12290step1Labels := by
      have ha : raw12290step1 = -raw12290step0 := by apply Matrix.ext; change ∀ i j, raw12290step1 i j = -(raw12290step0 i j); unfold raw12290step1 raw12290step0; decide +kernel
      have hl : raw12290step1Labels = raw12290step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12290step1 raw12290step1Labels = mixedMoment B raw12290step2 raw12290step2Labels := by
      have ha : raw12290step2 = raw12290step1 := by apply Matrix.ext; unfold raw12290step2 raw12290step1; decide +kernel
      have hl : raw12290step1Labels = labelEmbedding1 ∘ raw12290step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12290step1 raw12290step1Labels raw12290step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

theorem canonical12292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12292 raw12292Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw12292 raw12292Labels = mixedMoment B raw12292step0 raw12292step0Labels := by
      have hz : ∀ j, raw12292 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12292step0 = (fun i j => raw12292 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12292step0 raw12292; decide +kernel
      have hl : raw12292step0Labels = raw12292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12292 raw12292Labels permutation265 hz
    mixedMoment B raw12292step0 raw12292step0Labels = mixedMoment B raw12292step1 raw12292step1Labels := by
      have ha : raw12292step1 = (fun i j => raw12292step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12292step1 raw12292step0; decide +kernel
      have hl : raw12292step1Labels = raw12292step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12292step0 raw12292step0Labels permutation40 permutation7
    mixedMoment B raw12292step1 raw12292step1Labels = mixedMoment B raw12292step2 raw12292step2Labels := by
      have ha : raw12292step2 = -raw12292step1 := by apply Matrix.ext; change ∀ i j, raw12292step2 i j = -(raw12292step1 i j); unfold raw12292step2 raw12292step1; decide +kernel
      have hl : raw12292step2Labels = raw12292step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12292step2 raw12292step2Labels = mixedMoment B raw12292step3 raw12292step3Labels := by
      have ha : raw12292step3 = raw12292step2 := by apply Matrix.ext; unfold raw12292step3 raw12292step2; decide +kernel
      have hl : raw12292step2Labels = labelEmbedding1 ∘ raw12292step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12292step2 raw12292step2Labels raw12292step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

theorem canonical12316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12316 raw12316Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw12316 raw12316Labels = mixedMoment B raw12316step0 raw12316step0Labels := by
      have ha : raw12316step0 = (fun i j => raw12316 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12316step0 raw12316; decide +kernel
      have hl : raw12316step0Labels = raw12316Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12316 raw12316Labels permutation202 permutation7
    mixedMoment B raw12316step0 raw12316step0Labels = mixedMoment B raw12316step1 raw12316step1Labels := by
      have ha : raw12316step1 = -raw12316step0 := by apply Matrix.ext; change ∀ i j, raw12316step1 i j = -(raw12316step0 i j); unfold raw12316step1 raw12316step0; decide +kernel
      have hl : raw12316step1Labels = raw12316step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12316step1 raw12316step1Labels = mixedMoment B raw12316step2 raw12316step2Labels := by
      have ha : raw12316step2 = raw12316step1 := by apply Matrix.ext; unfold raw12316step2 raw12316step1; decide +kernel
      have hl : raw12316step1Labels = labelEmbedding1 ∘ raw12316step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12316step1 raw12316step1Labels raw12316step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

theorem canonical12318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12318 raw12318Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw12318 raw12318Labels = mixedMoment B raw12318step0 raw12318step0Labels := by
      have hz : ∀ j, raw12318 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12318step0 = (fun i j => raw12318 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12318step0 raw12318; decide +kernel
      have hl : raw12318step0Labels = raw12318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12318 raw12318Labels permutation265 hz
    mixedMoment B raw12318step0 raw12318step0Labels = mixedMoment B raw12318step1 raw12318step1Labels := by
      have ha : raw12318step1 = (fun i j => raw12318step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12318step1 raw12318step0; decide +kernel
      have hl : raw12318step1Labels = raw12318step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12318step0 raw12318step0Labels permutation40 permutation7
    mixedMoment B raw12318step1 raw12318step1Labels = mixedMoment B raw12318step2 raw12318step2Labels := by
      have ha : raw12318step2 = -raw12318step1 := by apply Matrix.ext; change ∀ i j, raw12318step2 i j = -(raw12318step1 i j); unfold raw12318step2 raw12318step1; decide +kernel
      have hl : raw12318step2Labels = raw12318step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12318step2 raw12318step2Labels = mixedMoment B raw12318step3 raw12318step3Labels := by
      have ha : raw12318step3 = raw12318step2 := by apply Matrix.ext; unfold raw12318step3 raw12318step2; decide +kernel
      have hl : raw12318step2Labels = labelEmbedding1 ∘ raw12318step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12318step2 raw12318step2Labels raw12318step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4778 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4778 node4778Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1986 node1986Labels + mixedMoment B node1986 node1986Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1710 singletonSmall4778
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4778) = raw1710Labels := by decide +kernel
  rw [hl, canonical1710 B hB] at h
  have hc0 : mixedMoment B raw1710 (Fin.cases (0 : Fin 2) singletonSmall4778) =
      mixedMoment B node1986 node1986Labels := by
    have ha : raw1710 = raw1711 := by apply Matrix.ext; unfold raw1710 raw1711; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4778 = raw1711Labels := by decide +kernel
    rw [ha, hj, canonical1711 B hB]
  have hc1 : mixedMoment B raw1710 (Fin.cases (1 : Fin 2) singletonSmall4778) =
      mixedMoment B node1986 node1986Labels := by
    have ha : raw1710 = raw1712 := by apply Matrix.ext; unfold raw1710 raw1712; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4778 = raw1712Labels := by decide +kernel
    rw [ha, hj, canonical1712 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4782 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4782 node4782Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1990 node1990Labels + mixedMoment B node1997 node1997Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1716 singletonSmall4782
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4782) = raw1716Labels := by decide +kernel
  rw [hl, canonical1716 B hB] at h
  have hc0 : mixedMoment B raw1716 (Fin.cases (0 : Fin 2) singletonSmall4782) =
      mixedMoment B node1990 node1990Labels := by
    have ha : raw1716 = raw1717 := by apply Matrix.ext; unfold raw1716 raw1717; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4782 = raw1717Labels := by decide +kernel
    rw [ha, hj, canonical1717 B hB]
  have hc1 : mixedMoment B raw1716 (Fin.cases (1 : Fin 2) singletonSmall4782) =
      mixedMoment B node1997 node1997Labels := by
    have ha : raw1716 = raw1718 := by apply Matrix.ext; unfold raw1716 raw1718; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4782 = raw1718Labels := by decide +kernel
    rw [ha, hj, canonical1718 B hB]
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

theorem singleton4801 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4801 node4801Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2019 node2019Labels + mixedMoment B node2190 node2190Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1731 singletonSmall4801
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4801) = raw1731Labels := by decide +kernel
  rw [hl, canonical1731 B hB] at h
  have hc0 : mixedMoment B raw1731 (Fin.cases (0 : Fin 2) singletonSmall4801) =
      mixedMoment B node2019 node2019Labels := by
    have ha : raw1731 = raw1732 := by apply Matrix.ext; unfold raw1731 raw1732; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4801 = raw1732Labels := by decide +kernel
    rw [ha, hj, canonical1732 B hB]
  have hc1 : mixedMoment B raw1731 (Fin.cases (1 : Fin 2) singletonSmall4801) =
      mixedMoment B node2190 node2190Labels := by
    have ha : raw1731 = raw1733 := by apply Matrix.ext; unfold raw1731 raw1733; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4801 = raw1733Labels := by decide +kernel
    rw [ha, hj, canonical1733 B hB]
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

theorem singleton5341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5341 node5341Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3678 node3678Labels + mixedMoment B node3744 node3744Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2379 singletonSmall5341
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5341) = raw2379Labels := by decide +kernel
  rw [hl, canonical2379 B hB] at h
  have hc0 : mixedMoment B raw2379 (Fin.cases (0 : Fin 2) singletonSmall5341) =
      mixedMoment B node3678 node3678Labels := by
    have ha : raw2379 = raw2380 := by apply Matrix.ext; unfold raw2379 raw2380; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5341 = raw2380Labels := by decide +kernel
    rw [ha, hj, canonical2380 B hB]
  have hc1 : mixedMoment B raw2379 (Fin.cases (1 : Fin 2) singletonSmall5341) =
      mixedMoment B node3744 node3744Labels := by
    have ha : raw2379 = raw2381 := by apply Matrix.ext; unfold raw2379 raw2381; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5341 = raw2381Labels := by decide +kernel
    rw [ha, hj, canonical2381 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5344 node5344Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3681 node3681Labels + mixedMoment B node3681 node3681Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2382 singletonSmall5344
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5344) = raw2382Labels := by decide +kernel
  rw [hl, canonical2382 B hB] at h
  have hc0 : mixedMoment B raw2382 (Fin.cases (0 : Fin 2) singletonSmall5344) =
      mixedMoment B node3681 node3681Labels := by
    have ha : raw2382 = raw2383 := by apply Matrix.ext; unfold raw2382 raw2383; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5344 = raw2383Labels := by decide +kernel
    rw [ha, hj, canonical2383 B hB]
  have hc1 : mixedMoment B raw2382 (Fin.cases (1 : Fin 2) singletonSmall5344) =
      mixedMoment B node3681 node3681Labels := by
    have ha : raw2382 = raw2384 := by apply Matrix.ext; unfold raw2382 raw2384; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5344 = raw2384Labels := by decide +kernel
    rw [ha, hj, canonical2384 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5378 node5378Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3719 node3719Labels + mixedMoment B node3795 node3795Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2430 singletonSmall5378
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5378) = raw2430Labels := by decide +kernel
  rw [hl, canonical2430 B hB] at h
  have hc0 : mixedMoment B raw2430 (Fin.cases (0 : Fin 2) singletonSmall5378) =
      mixedMoment B node3719 node3719Labels := by
    have ha : raw2430 = raw2431 := by apply Matrix.ext; unfold raw2430 raw2431; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5378 = raw2431Labels := by decide +kernel
    rw [ha, hj, canonical2431 B hB]
  have hc1 : mixedMoment B raw2430 (Fin.cases (1 : Fin 2) singletonSmall5378) =
      mixedMoment B node3795 node3795Labels := by
    have ha : raw2430 = raw2432 := by apply Matrix.ext; unfold raw2430 raw2432; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5378 = raw2432Labels := by decide +kernel
    rw [ha, hj, canonical2432 B hB]
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

theorem singleton5432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5432 node5432Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3850 node3850Labels + mixedMoment B node3850 node3850Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2523 singletonSmall5432
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5432) = raw2523Labels := by decide +kernel
  rw [hl, canonical2523 B hB] at h
  have hc0 : mixedMoment B raw2523 (Fin.cases (0 : Fin 2) singletonSmall5432) =
      mixedMoment B node3850 node3850Labels := by
    have ha : raw2523 = raw2524 := by apply Matrix.ext; unfold raw2523 raw2524; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5432 = raw2524Labels := by decide +kernel
    rw [ha, hj, canonical2524 B hB]
  have hc1 : mixedMoment B raw2523 (Fin.cases (1 : Fin 2) singletonSmall5432) =
      mixedMoment B node3850 node3850Labels := by
    have ha : raw2523 = raw2525 := by apply Matrix.ext; unfold raw2523 raw2525; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5432 = raw2525Labels := by decide +kernel
    rw [ha, hj, canonical2525 B hB]
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

theorem sound1986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1986 node1986Labels = Sparse.eval nodeValue1986 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1986) = mixedMoment B node1986 node1986Labels := rfl
  simpa [nodeValue1986, Sparse.eval] using hc.symm

theorem sound1990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1990 node1990Labels = Sparse.eval nodeValue1990 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1990) = mixedMoment B node1990 node1990Labels := rfl
  simpa [nodeValue1990, Sparse.eval] using hc.symm

theorem sound1997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1997 node1997Labels = Sparse.eval nodeValue1997 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1997) = mixedMoment B node1997 node1997Labels := rfl
  simpa [nodeValue1997, Sparse.eval] using hc.symm

theorem sound2019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2019 node2019Labels = Sparse.eval nodeValue2019 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2019) = mixedMoment B node2019 node2019Labels := rfl
  simpa [nodeValue2019, Sparse.eval] using hc.symm

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

theorem sound2190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2190 node2190Labels = Sparse.eval nodeValue2190 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2190) = mixedMoment B node2190 node2190Labels := rfl
  simpa [nodeValue2190, Sparse.eval] using hc.symm

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

theorem sound2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2553 node2553Labels = Sparse.eval nodeValue2553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2553) = mixedMoment B node2553 node2553Labels := rfl
  simpa [nodeValue2553, Sparse.eval] using hc.symm

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

theorem zero3513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3513 node3513Labels = 0 := by
  exact mixedMoment_alpha B hF node3513 node3513Labels 1 permutation444
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

theorem sound3513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3513 node3513Labels = Sparse.eval nodeValue3513 (mixedVector B) := by
  simpa only [nodeValue3513, Sparse.eval_nil] using zero3513 B _hB _hF

theorem sound3514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3514 node3514Labels = Sparse.eval nodeValue3514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3514) = mixedMoment B node3514 node3514Labels := rfl
  simpa [nodeValue3514, Sparse.eval] using hc.symm

theorem sound3516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3516 node3516Labels = Sparse.eval nodeValue3516 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3516) = mixedMoment B node3516 node3516Labels := rfl
  simpa [nodeValue3516, Sparse.eval] using hc.symm

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

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3557 node3557Labels = Sparse.eval nodeValue3557 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3557) = mixedMoment B node3557 node3557Labels := rfl
  simpa [nodeValue3557, Sparse.eval] using hc.symm

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

theorem sound3678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3678 node3678Labels = Sparse.eval nodeValue3678 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3678) = mixedMoment B node3678 node3678Labels := rfl
  simpa [nodeValue3678, Sparse.eval] using hc.symm

theorem sound3681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3681 node3681Labels = Sparse.eval nodeValue3681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3681) = mixedMoment B node3681 node3681Labels := rfl
  simpa [nodeValue3681, Sparse.eval] using hc.symm

theorem sound3689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3689 node3689Labels = Sparse.eval nodeValue3689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3689) = mixedMoment B node3689 node3689Labels := rfl
  simpa [nodeValue3689, Sparse.eval] using hc.symm

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

theorem sound3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3719 node3719Labels = Sparse.eval nodeValue3719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3719) = mixedMoment B node3719 node3719Labels := rfl
  simpa [nodeValue3719, Sparse.eval] using hc.symm

theorem sound3744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3744 node3744Labels = Sparse.eval nodeValue3744 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3744) = mixedMoment B node3744 node3744Labels := rfl
  simpa [nodeValue3744, Sparse.eval] using hc.symm

theorem sound3757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3757 node3757Labels = Sparse.eval nodeValue3757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3757) = mixedMoment B node3757 node3757Labels := rfl
  simpa [nodeValue3757, Sparse.eval] using hc.symm

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

theorem sound3793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3793 node3793Labels = Sparse.eval nodeValue3793 (mixedVector B) := by
  simpa only [nodeValue3793, Sparse.eval_nil] using zero3793 B _hB _hF

theorem sound3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3795 node3795Labels = Sparse.eval nodeValue3795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3795) = mixedMoment B node3795 node3795Labels := rfl
  simpa [nodeValue3795, Sparse.eval] using hc.symm

theorem sound3801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3801 node3801Labels = Sparse.eval nodeValue3801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3801) = mixedMoment B node3801 node3801Labels := rfl
  simpa [nodeValue3801, Sparse.eval] using hc.symm

theorem sound3807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = Sparse.eval nodeValue3807 (mixedVector B) := by
  simpa only [nodeValue3807, Sparse.eval_nil] using zero3807 B _hB _hF

theorem sound3812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3812 node3812Labels = Sparse.eval nodeValue3812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3812) = mixedMoment B node3812 node3812Labels := rfl
  simpa [nodeValue3812, Sparse.eval] using hc.symm

theorem sound3833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3833 node3833Labels = Sparse.eval nodeValue3833 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3833) = mixedMoment B node3833 node3833Labels := rfl
  simpa [nodeValue3833, Sparse.eval] using hc.symm

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

theorem zero3860 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3860 node3860Labels = 0 := by
  exact mixedMoment_order_one B hB node3860 node3860Labels 1
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

theorem sound3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3843 node3843Labels = Sparse.eval nodeValue3843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3843) = mixedMoment B node3843 node3843Labels := rfl
  simpa [nodeValue3843, Sparse.eval] using hc.symm

theorem sound3850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3850 node3850Labels = Sparse.eval nodeValue3850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3850) = mixedMoment B node3850 node3850Labels := rfl
  simpa [nodeValue3850, Sparse.eval] using hc.symm

theorem sound3860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3860 node3860Labels = Sparse.eval nodeValue3860 (mixedVector B) := by
  simpa only [nodeValue3860, Sparse.eval_nil] using zero3860 B _hB _hF

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

theorem sound3989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3989 node3989Labels = Sparse.eval nodeValue3989 (mixedVector B) := by
  simpa only [nodeValue3989, Sparse.eval_nil] using zero3989 B _hB _hF

theorem sound4025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4025 node4025Labels = Sparse.eval nodeValue4025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4025) = mixedMoment B node4025 node4025Labels := rfl
  simpa [nodeValue4025, Sparse.eval] using hc.symm

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

theorem sound4778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4778 node4778Labels = Sparse.eval nodeValue4778 (mixedVector B) := by
  have h := singleton4778 B _hB
  rw [sound1986 B _hB _hF] at h
  norm_num [nodeValue4778, nodeValue1986, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4782 node4782Labels = Sparse.eval nodeValue4782 (mixedVector B) := by
  have h := singleton4782 B _hB
  rw [sound1990 B _hB _hF, sound1997 B _hB _hF] at h
  norm_num [nodeValue4782, nodeValue1990, nodeValue1997, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4801 node4801Labels = Sparse.eval nodeValue4801 (mixedVector B) := by
  have h := singleton4801 B _hB
  rw [sound2019 B _hB _hF, sound2190 B _hB _hF] at h
  norm_num [nodeValue4801, nodeValue2019, nodeValue2190, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4815 node4815Labels = Sparse.eval nodeValue4815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4815) = mixedMoment B node4815 node4815Labels := rfl
  simpa [nodeValue4815, Sparse.eval] using hc.symm

theorem sound4830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4830 node4830Labels = Sparse.eval nodeValue4830 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4830) = mixedMoment B node4830 node4830Labels := rfl
  simpa [nodeValue4830, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5127 node5127Labels = 0 := by
  exact mixedMoment_alpha B hF node5127 node5127Labels 1 permutation158
    (by decide +kernel)

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

theorem sound5127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5127 node5127Labels = Sparse.eval nodeValue5127 (mixedVector B) := by
  simpa only [nodeValue5127, Sparse.eval_nil] using zero5127 B _hB _hF

theorem sound5129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5129 node5129Labels = Sparse.eval nodeValue5129 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5129) = mixedMoment B node5129 node5129Labels := rfl
  simpa [nodeValue5129, Sparse.eval] using hc.symm

theorem sound5134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5134 node5134Labels = Sparse.eval nodeValue5134 (mixedVector B) := by
  have h := singleton5134 B _hB
  rw [sound2553 B _hB _hF, sound3514 B _hB _hF] at h
  norm_num [nodeValue5134, nodeValue2553, nodeValue3514, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5144 node5144Labels = Sparse.eval nodeValue5144 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5144) = mixedMoment B node5144 node5144Labels := rfl
  simpa [nodeValue5144, Sparse.eval] using hc.symm

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

theorem sound5251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5251 node5251Labels = Sparse.eval nodeValue5251 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5251) = mixedMoment B node5251 node5251Labels := rfl
  simpa [nodeValue5251, Sparse.eval] using hc.symm

theorem sound5258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5258 node5258Labels = Sparse.eval nodeValue5258 (mixedVector B) := by
  have h := singleton5258 B _hB
  rw [sound2722 B _hB _hF, sound3533 B _hB _hF] at h
  norm_num [nodeValue5258, nodeValue2722, nodeValue3533, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5277 node5277Labels = Sparse.eval nodeValue5277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5277) = mixedMoment B node5277 node5277Labels := rfl
  simpa [nodeValue5277, Sparse.eval] using hc.symm

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

theorem sound5341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5341 node5341Labels = Sparse.eval nodeValue5341 (mixedVector B) := by
  have h := singleton5341 B _hB
  rw [sound3678 B _hB _hF, sound3744 B _hB _hF] at h
  norm_num [nodeValue5341, nodeValue3678, nodeValue3744, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5344 node5344Labels = Sparse.eval nodeValue5344 (mixedVector B) := by
  have h := singleton5344 B _hB
  rw [sound3681 B _hB _hF] at h
  norm_num [nodeValue5344, nodeValue3681, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5351 node5351Labels = Sparse.eval nodeValue5351 (mixedVector B) := by
  have h := singleton5351 B _hB
  rw [sound3689 B _hB _hF, sound3757 B _hB _hF] at h
  norm_num [nodeValue5351, nodeValue3689, nodeValue3757, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5359 node5359Labels = Sparse.eval nodeValue5359 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5359) = mixedMoment B node5359 node5359Labels := rfl
  simpa [nodeValue5359, Sparse.eval] using hc.symm

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

theorem sound5376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5376 node5376Labels = Sparse.eval nodeValue5376 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5376) = mixedMoment B node5376 node5376Labels := rfl
  simpa [nodeValue5376, Sparse.eval] using hc.symm

theorem sound5378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5378 node5378Labels = Sparse.eval nodeValue5378 (mixedVector B) := by
  have h := singleton5378 B _hB
  rw [sound3719 B _hB _hF, sound3795 B _hB _hF] at h
  norm_num [nodeValue5378, nodeValue3719, nodeValue3795, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5381 node5381Labels = Sparse.eval nodeValue5381 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5381) = mixedMoment B node5381 node5381Labels := rfl
  simpa [nodeValue5381, Sparse.eval] using hc.symm

theorem sound5394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5394 node5394Labels = Sparse.eval nodeValue5394 (mixedVector B) := by
  simpa only [nodeValue5394, Sparse.eval_nil] using zero5394 B _hB _hF

theorem sound5406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5406 node5406Labels = Sparse.eval nodeValue5406 (mixedVector B) := by
  have h := singleton5406 B _hB
  rw [sound3801 B _hB _hF, sound3812 B _hB _hF] at h
  norm_num [nodeValue5406, nodeValue3801, nodeValue3812, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5409 node5409Labels = Sparse.eval nodeValue5409 (mixedVector B) := by
  simpa only [nodeValue5409, Sparse.eval_nil] using zero5409 B _hB _hF

theorem sound5420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5420 node5420Labels = Sparse.eval nodeValue5420 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5420) = mixedMoment B node5420 node5420Labels := rfl
  simpa [nodeValue5420, Sparse.eval] using hc.symm

theorem sound5422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5422 node5422Labels = Sparse.eval nodeValue5422 (mixedVector B) := by
  have h := singleton5422 B _hB
  rw [sound3900 B _hB _hF, sound3964 B _hB _hF] at h
  norm_num [nodeValue5422, nodeValue3900, nodeValue3964, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5432 node5432Labels = Sparse.eval nodeValue5432 (mixedVector B) := by
  have h := singleton5432 B _hB
  rw [sound3850 B _hB _hF] at h
  norm_num [nodeValue5432, nodeValue3850, Sparse.eval] at h ⊢
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

theorem sound5441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5441 node5441Labels = Sparse.eval nodeValue5441 (mixedVector B) := by
  simpa only [nodeValue5441, Sparse.eval_nil] using zero5441 B _hB _hF

theorem sound5447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5447 node5447Labels = Sparse.eval nodeValue5447 (mixedVector B) := by
  have h := singleton5447 B _hB
  rw [sound3909 B _hB _hF, sound4025 B _hB _hF] at h
  norm_num [nodeValue5447, nodeValue3909, nodeValue4025, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5477 node5477Labels = Sparse.eval nodeValue5477 (mixedVector B) := by
  simpa only [nodeValue5477, Sparse.eval_nil] using zero5477 B _hB _hF

theorem sound5479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5479 node5479Labels = Sparse.eval nodeValue5479 (mixedVector B) := by
  simpa only [nodeValue5479, Sparse.eval_nil] using zero5479 B _hB _hF

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

theorem sourceEq1091 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1091 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1091 + difference 0 1) (sourceB1091 + difference 1 0) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1091 + difference 0 1) (sourceB1091 + difference 1 0) sourceC1091) = raw18212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18212; decide +kernel
    rw [ha]
    exact (canonical18212 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1091 + difference 0 2) (sourceB1091 + difference 2 0) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1091 + difference 0 2) (sourceB1091 + difference 2 0) sourceC1091) = raw18213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18213; decide +kernel
    rw [ha]
    exact (canonical18213 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1091 + difference 0 3) (sourceB1091 + difference 3 0) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1091 + difference 0 3) (sourceB1091 + difference 3 0) sourceC1091) = raw18214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18214; decide +kernel
    rw [ha]
    exact (canonical18214 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1091 + difference 0 4) (sourceB1091 + difference 4 0) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1091 + difference 0 4) (sourceB1091 + difference 4 0) sourceC1091) = raw18215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18215; decide +kernel
    rw [ha]
    exact (canonical18215 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1091 + difference 0 5) (sourceB1091 + difference 5 0) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1091 + difference 0 5) (sourceB1091 + difference 5 0) sourceC1091) = raw18216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18216; decide +kernel
    rw [ha]
    exact (canonical18216 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1091 + difference 1 0) (sourceB1091 + difference 0 1) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA1091 + difference 1 0) (sourceB1091 + difference 0 1) sourceC1091) = raw12258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw12258; decide +kernel
    rw [ha]
    exact (canonical12258 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1091 + difference 1 2) (sourceB1091 + difference 2 1) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1091 + difference 1 2) (sourceB1091 + difference 2 1) sourceC1091) = raw18217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18217; decide +kernel
    rw [ha]
    exact (canonical18217 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1091 + difference 1 3) (sourceB1091 + difference 3 1) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1091 + difference 1 3) (sourceB1091 + difference 3 1) sourceC1091) = raw18218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18218; decide +kernel
    rw [ha]
    exact (canonical18218 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1091 + difference 1 4) (sourceB1091 + difference 4 1) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA1091 + difference 1 4) (sourceB1091 + difference 4 1) sourceC1091) = raw18219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18219; decide +kernel
    rw [ha]
    exact (canonical18219 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1091 + difference 1 5) (sourceB1091 + difference 5 1) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1091 + difference 1 5) (sourceB1091 + difference 5 1) sourceC1091) = raw12232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw12232; decide +kernel
    rw [ha]
    exact (canonical12232 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1091 + difference 2 0) (sourceB1091 + difference 0 2) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA1091 + difference 2 0) (sourceB1091 + difference 0 2) sourceC1091) = raw18220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18220; decide +kernel
    rw [ha]
    exact (canonical18220 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1091 + difference 2 1) (sourceB1091 + difference 1 2) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1091 + difference 2 1) (sourceB1091 + difference 1 2) sourceC1091) = raw18221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18221; decide +kernel
    rw [ha]
    exact (canonical18221 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1091 + difference 2 3) (sourceB1091 + difference 3 2) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5394) := by
    have ha : (tripleCharges (sourceA1091 + difference 2 3) (sourceB1091 + difference 3 2) sourceC1091) = raw18222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18222; decide +kernel
    rw [ha]
    exact (canonical18222 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1091 + difference 2 4) (sourceB1091 + difference 4 2) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1091 + difference 2 4) (sourceB1091 + difference 4 2) sourceC1091) = raw18223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18223; decide +kernel
    rw [ha]
    exact (canonical18223 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1091 + difference 2 5) (sourceB1091 + difference 5 2) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1091 + difference 2 5) (sourceB1091 + difference 5 2) sourceC1091) = raw18224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18224; decide +kernel
    rw [ha]
    exact (canonical18224 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1091 + difference 3 0) (sourceB1091 + difference 0 3) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA1091 + difference 3 0) (sourceB1091 + difference 0 3) sourceC1091) = raw12256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw12256; decide +kernel
    rw [ha]
    exact (canonical12256 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1091 + difference 3 1) (sourceB1091 + difference 1 3) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA1091 + difference 3 1) (sourceB1091 + difference 1 3) sourceC1091) = raw18225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18225; decide +kernel
    rw [ha]
    exact (canonical18225 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1091 + difference 3 2) (sourceB1091 + difference 2 3) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5420) := by
    have ha : (tripleCharges (sourceA1091 + difference 3 2) (sourceB1091 + difference 2 3) sourceC1091) = raw18226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18226; decide +kernel
    rw [ha]
    exact (canonical18226 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1091 + difference 3 4) (sourceB1091 + difference 4 3) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1091 + difference 3 4) (sourceB1091 + difference 4 3) sourceC1091) = raw18227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18227; decide +kernel
    rw [ha]
    exact (canonical18227 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1091 + difference 3 5) (sourceB1091 + difference 5 3) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1091 + difference 3 5) (sourceB1091 + difference 5 3) sourceC1091) = raw12230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw12230; decide +kernel
    rw [ha]
    exact (canonical12230 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1091 + difference 4 0) (sourceB1091 + difference 0 4) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA1091 + difference 4 0) (sourceB1091 + difference 0 4) sourceC1091) = raw18228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18228; decide +kernel
    rw [ha]
    exact (canonical18228 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1091 + difference 4 1) (sourceB1091 + difference 1 4) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5376) := by
    have ha : (tripleCharges (sourceA1091 + difference 4 1) (sourceB1091 + difference 1 4) sourceC1091) = raw18229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18229; decide +kernel
    rw [ha]
    exact (canonical18229 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1091 + difference 4 2) (sourceB1091 + difference 2 4) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA1091 + difference 4 2) (sourceB1091 + difference 2 4) sourceC1091) = raw18230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18230; decide +kernel
    rw [ha]
    exact (canonical18230 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1091 + difference 4 3) (sourceB1091 + difference 3 4) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1091 + difference 4 3) (sourceB1091 + difference 3 4) sourceC1091) = raw18231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18231; decide +kernel
    rw [ha]
    exact (canonical18231 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1091 + difference 4 5) (sourceB1091 + difference 5 4) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1091 + difference 4 5) (sourceB1091 + difference 5 4) sourceC1091) = raw18232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18232; decide +kernel
    rw [ha]
    exact (canonical18232 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1091 + difference 5 0) (sourceB1091 + difference 0 5) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5127) := by
    have ha : (tripleCharges (sourceA1091 + difference 5 0) (sourceB1091 + difference 0 5) sourceC1091) = raw18233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18233; decide +kernel
    rw [ha]
    exact (canonical18233 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1091 + difference 5 1) (sourceB1091 + difference 1 5) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA1091 + difference 5 1) (sourceB1091 + difference 1 5) sourceC1091) = raw18234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18234; decide +kernel
    rw [ha]
    exact (canonical18234 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1091 + difference 5 2) (sourceB1091 + difference 2 5) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA1091 + difference 5 2) (sourceB1091 + difference 2 5) sourceC1091) = raw18235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18235; decide +kernel
    rw [ha]
    exact (canonical18235 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1091 + difference 5 3) (sourceB1091 + difference 3 5) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA1091 + difference 5 3) (sourceB1091 + difference 3 5) sourceC1091) = raw18236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18236; decide +kernel
    rw [ha]
    exact (canonical18236 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1091 + difference 5 4) (sourceB1091 + difference 4 5) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA1091 + difference 5 4) (sourceB1091 + difference 4 5) sourceC1091) = raw18237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18237; decide +kernel
    rw [ha]
    exact (canonical18237 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1091 sourceB1091 sourceC1091
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1091, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1092 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1092 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1092 + difference 0 1) (sourceB1092 + difference 1 0) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA1092 + difference 0 1) (sourceB1092 + difference 1 0) sourceC1092) = raw18238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18238; decide +kernel
    rw [ha]
    exact (canonical18238 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1092 + difference 0 2) (sourceB1092 + difference 2 0) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA1092 + difference 0 2) (sourceB1092 + difference 2 0) sourceC1092) = raw18239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18239; decide +kernel
    rw [ha]
    exact (canonical18239 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1092 + difference 0 3) (sourceB1092 + difference 3 0) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA1092 + difference 0 3) (sourceB1092 + difference 3 0) sourceC1092) = raw18240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18240; decide +kernel
    rw [ha]
    exact (canonical18240 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1092 + difference 0 4) (sourceB1092 + difference 4 0) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA1092 + difference 0 4) (sourceB1092 + difference 4 0) sourceC1092) = raw18241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18241; decide +kernel
    rw [ha]
    exact (canonical18241 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1092 + difference 0 5) (sourceB1092 + difference 5 0) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3989) := by
    have ha : (tripleCharges (sourceA1092 + difference 0 5) (sourceB1092 + difference 5 0) sourceC1092) = raw18242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18242; decide +kernel
    rw [ha]
    exact (canonical18242 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1092 + difference 1 0) (sourceB1092 + difference 0 1) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA1092 + difference 1 0) (sourceB1092 + difference 0 1) sourceC1092) = raw12318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw12318; decide +kernel
    rw [ha]
    exact (canonical12318 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1092 + difference 1 2) (sourceB1092 + difference 2 1) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA1092 + difference 1 2) (sourceB1092 + difference 2 1) sourceC1092) = raw18243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18243; decide +kernel
    rw [ha]
    exact (canonical18243 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1092 + difference 1 3) (sourceB1092 + difference 3 1) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA1092 + difference 1 3) (sourceB1092 + difference 3 1) sourceC1092) = raw18244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18244; decide +kernel
    rw [ha]
    exact (canonical18244 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1092 + difference 1 4) (sourceB1092 + difference 4 1) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3860) := by
    have ha : (tripleCharges (sourceA1092 + difference 1 4) (sourceB1092 + difference 4 1) sourceC1092) = raw18245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18245; decide +kernel
    rw [ha]
    exact (canonical18245 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1092 + difference 1 5) (sourceB1092 + difference 5 1) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA1092 + difference 1 5) (sourceB1092 + difference 5 1) sourceC1092) = raw12292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw12292; decide +kernel
    rw [ha]
    exact (canonical12292 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1092 + difference 2 0) (sourceB1092 + difference 0 2) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA1092 + difference 2 0) (sourceB1092 + difference 0 2) sourceC1092) = raw18246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18246; decide +kernel
    rw [ha]
    exact (canonical18246 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1092 + difference 2 1) (sourceB1092 + difference 1 2) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA1092 + difference 2 1) (sourceB1092 + difference 1 2) sourceC1092) = raw18247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18247; decide +kernel
    rw [ha]
    exact (canonical18247 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1092 + difference 2 3) (sourceB1092 + difference 3 2) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3793) := by
    have ha : (tripleCharges (sourceA1092 + difference 2 3) (sourceB1092 + difference 3 2) sourceC1092) = raw18248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18248; decide +kernel
    rw [ha]
    exact (canonical18248 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1092 + difference 2 4) (sourceB1092 + difference 4 2) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA1092 + difference 2 4) (sourceB1092 + difference 4 2) sourceC1092) = raw18249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18249; decide +kernel
    rw [ha]
    exact (canonical18249 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1092 + difference 2 5) (sourceB1092 + difference 5 2) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA1092 + difference 2 5) (sourceB1092 + difference 5 2) sourceC1092) = raw18250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18250; decide +kernel
    rw [ha]
    exact (canonical18250 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1092 + difference 3 0) (sourceB1092 + difference 0 3) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA1092 + difference 3 0) (sourceB1092 + difference 0 3) sourceC1092) = raw12316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw12316; decide +kernel
    rw [ha]
    exact (canonical12316 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1092 + difference 3 1) (sourceB1092 + difference 1 3) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA1092 + difference 3 1) (sourceB1092 + difference 1 3) sourceC1092) = raw18251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18251; decide +kernel
    rw [ha]
    exact (canonical18251 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1092 + difference 3 2) (sourceB1092 + difference 2 3) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3870) := by
    have ha : (tripleCharges (sourceA1092 + difference 3 2) (sourceB1092 + difference 2 3) sourceC1092) = raw18252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18252; decide +kernel
    rw [ha]
    exact (canonical18252 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1092 + difference 3 4) (sourceB1092 + difference 4 3) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA1092 + difference 3 4) (sourceB1092 + difference 4 3) sourceC1092) = raw18253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18253; decide +kernel
    rw [ha]
    exact (canonical18253 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1092 + difference 3 5) (sourceB1092 + difference 5 3) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA1092 + difference 3 5) (sourceB1092 + difference 5 3) sourceC1092) = raw12290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw12290; decide +kernel
    rw [ha]
    exact (canonical12290 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1092 + difference 4 0) (sourceB1092 + difference 0 4) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA1092 + difference 4 0) (sourceB1092 + difference 0 4) sourceC1092) = raw18254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18254; decide +kernel
    rw [ha]
    exact (canonical18254 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1092 + difference 4 1) (sourceB1092 + difference 1 4) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3833) := by
    have ha : (tripleCharges (sourceA1092 + difference 4 1) (sourceB1092 + difference 1 4) sourceC1092) = raw18255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18255; decide +kernel
    rw [ha]
    exact (canonical18255 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1092 + difference 4 2) (sourceB1092 + difference 2 4) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA1092 + difference 4 2) (sourceB1092 + difference 2 4) sourceC1092) = raw18256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18256; decide +kernel
    rw [ha]
    exact (canonical18256 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1092 + difference 4 3) (sourceB1092 + difference 3 4) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA1092 + difference 4 3) (sourceB1092 + difference 3 4) sourceC1092) = raw18257 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18257; decide +kernel
    rw [ha]
    exact (canonical18257 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1092 + difference 4 5) (sourceB1092 + difference 5 4) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA1092 + difference 4 5) (sourceB1092 + difference 5 4) sourceC1092) = raw18258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18258; decide +kernel
    rw [ha]
    exact (canonical18258 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1092 + difference 5 0) (sourceB1092 + difference 0 5) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA1092 + difference 5 0) (sourceB1092 + difference 0 5) sourceC1092) = raw18259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18259; decide +kernel
    rw [ha]
    exact (canonical18259 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1092 + difference 5 1) (sourceB1092 + difference 1 5) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA1092 + difference 5 1) (sourceB1092 + difference 1 5) sourceC1092) = raw18260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18260; decide +kernel
    rw [ha]
    exact (canonical18260 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1092 + difference 5 2) (sourceB1092 + difference 2 5) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA1092 + difference 5 2) (sourceB1092 + difference 2 5) sourceC1092) = raw18261 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18261; decide +kernel
    rw [ha]
    exact (canonical18261 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1092 + difference 5 3) (sourceB1092 + difference 3 5) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA1092 + difference 5 3) (sourceB1092 + difference 3 5) sourceC1092) = raw18262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18262; decide +kernel
    rw [ha]
    exact (canonical18262 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1092 + difference 5 4) (sourceB1092 + difference 4 5) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA1092 + difference 5 4) (sourceB1092 + difference 4 5) sourceC1092) = raw18263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18263; decide +kernel
    rw [ha]
    exact (canonical18263 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1092 sourceB1092 sourceC1092
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1092, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1093 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1093 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1093 + difference 0 1) (sourceB1093 + difference 1 0) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1093 + difference 0 1) (sourceB1093 + difference 1 0) sourceC1093) = raw18264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18264; decide +kernel
    rw [ha]
    exact (canonical18264 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1093 + difference 0 2) (sourceB1093 + difference 2 0) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1093 + difference 0 2) (sourceB1093 + difference 2 0) sourceC1093) = raw18265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18265; decide +kernel
    rw [ha]
    exact (canonical18265 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1093 + difference 0 3) (sourceB1093 + difference 3 0) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1093 + difference 0 3) (sourceB1093 + difference 3 0) sourceC1093) = raw18266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18266; decide +kernel
    rw [ha]
    exact (canonical18266 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1093 + difference 0 4) (sourceB1093 + difference 4 0) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1093 + difference 0 4) (sourceB1093 + difference 4 0) sourceC1093) = raw18267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18267; decide +kernel
    rw [ha]
    exact (canonical18267 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1093 + difference 0 5) (sourceB1093 + difference 5 0) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA1093 + difference 0 5) (sourceB1093 + difference 5 0) sourceC1093) = raw18268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18268; decide +kernel
    rw [ha]
    exact (canonical18268 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1093 + difference 1 0) (sourceB1093 + difference 0 1) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA1093 + difference 1 0) (sourceB1093 + difference 0 1) sourceC1093) = raw18269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18269; decide +kernel
    rw [ha]
    exact (canonical18269 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1093 + difference 1 2) (sourceB1093 + difference 2 1) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA1093 + difference 1 2) (sourceB1093 + difference 2 1) sourceC1093) = raw18270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18270; decide +kernel
    rw [ha]
    exact (canonical18270 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1093 + difference 1 3) (sourceB1093 + difference 3 1) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA1093 + difference 1 3) (sourceB1093 + difference 3 1) sourceC1093) = raw18271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18271; decide +kernel
    rw [ha]
    exact (canonical18271 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1093 + difference 1 4) (sourceB1093 + difference 4 1) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5415) := by
    have ha : (tripleCharges (sourceA1093 + difference 1 4) (sourceB1093 + difference 4 1) sourceC1093) = raw18272 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18272; decide +kernel
    rw [ha]
    exact (canonical18272 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1093 + difference 1 5) (sourceB1093 + difference 5 1) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1093 + difference 1 5) (sourceB1093 + difference 5 1) sourceC1093) = raw18273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18273; decide +kernel
    rw [ha]
    exact (canonical18273 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1093 + difference 2 0) (sourceB1093 + difference 0 2) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA1093 + difference 2 0) (sourceB1093 + difference 0 2) sourceC1093) = raw18274 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18274; decide +kernel
    rw [ha]
    exact (canonical18274 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1093 + difference 2 1) (sourceB1093 + difference 1 2) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA1093 + difference 2 1) (sourceB1093 + difference 1 2) sourceC1093) = raw18275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18275; decide +kernel
    rw [ha]
    exact (canonical18275 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1093 + difference 2 3) (sourceB1093 + difference 3 2) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA1093 + difference 2 3) (sourceB1093 + difference 3 2) sourceC1093) = raw18276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18276; decide +kernel
    rw [ha]
    exact (canonical18276 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1093 + difference 2 4) (sourceB1093 + difference 4 2) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA1093 + difference 2 4) (sourceB1093 + difference 4 2) sourceC1093) = raw18277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18277; decide +kernel
    rw [ha]
    exact (canonical18277 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1093 + difference 2 5) (sourceB1093 + difference 5 2) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1093 + difference 2 5) (sourceB1093 + difference 5 2) sourceC1093) = raw18278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18278; decide +kernel
    rw [ha]
    exact (canonical18278 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1093 + difference 3 0) (sourceB1093 + difference 0 3) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA1093 + difference 3 0) (sourceB1093 + difference 0 3) sourceC1093) = raw18279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18279; decide +kernel
    rw [ha]
    exact (canonical18279 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1093 + difference 3 1) (sourceB1093 + difference 1 3) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA1093 + difference 3 1) (sourceB1093 + difference 1 3) sourceC1093) = raw18280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18280; decide +kernel
    rw [ha]
    exact (canonical18280 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1093 + difference 3 2) (sourceB1093 + difference 2 3) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5415) := by
    have ha : (tripleCharges (sourceA1093 + difference 3 2) (sourceB1093 + difference 2 3) sourceC1093) = raw18281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18281; decide +kernel
    rw [ha]
    exact (canonical18281 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1093 + difference 3 4) (sourceB1093 + difference 4 3) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA1093 + difference 3 4) (sourceB1093 + difference 4 3) sourceC1093) = raw18282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18282; decide +kernel
    rw [ha]
    exact (canonical18282 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1093 + difference 3 5) (sourceB1093 + difference 5 3) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1093 + difference 3 5) (sourceB1093 + difference 5 3) sourceC1093) = raw18283 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18283; decide +kernel
    rw [ha]
    exact (canonical18283 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1093 + difference 4 0) (sourceB1093 + difference 0 4) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA1093 + difference 4 0) (sourceB1093 + difference 0 4) sourceC1093) = raw18284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18284; decide +kernel
    rw [ha]
    exact (canonical18284 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1093 + difference 4 1) (sourceB1093 + difference 1 4) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA1093 + difference 4 1) (sourceB1093 + difference 1 4) sourceC1093) = raw18285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18285; decide +kernel
    rw [ha]
    exact (canonical18285 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1093 + difference 4 2) (sourceB1093 + difference 2 4) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA1093 + difference 4 2) (sourceB1093 + difference 2 4) sourceC1093) = raw18286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18286; decide +kernel
    rw [ha]
    exact (canonical18286 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1093 + difference 4 3) (sourceB1093 + difference 3 4) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA1093 + difference 4 3) (sourceB1093 + difference 3 4) sourceC1093) = raw18287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18287; decide +kernel
    rw [ha]
    exact (canonical18287 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1093 + difference 4 5) (sourceB1093 + difference 5 4) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1093 + difference 4 5) (sourceB1093 + difference 5 4) sourceC1093) = raw18288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18288; decide +kernel
    rw [ha]
    exact (canonical18288 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1093 + difference 5 0) (sourceB1093 + difference 0 5) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4778) := by
    have ha : (tripleCharges (sourceA1093 + difference 5 0) (sourceB1093 + difference 0 5) sourceC1093) = raw18289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18289; decide +kernel
    rw [ha]
    exact (canonical18289 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1093 + difference 5 1) (sourceB1093 + difference 1 5) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA1093 + difference 5 1) (sourceB1093 + difference 1 5) sourceC1093) = raw18290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18290; decide +kernel
    rw [ha]
    exact (canonical18290 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1093 + difference 5 2) (sourceB1093 + difference 2 5) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA1093 + difference 5 2) (sourceB1093 + difference 2 5) sourceC1093) = raw18291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18291; decide +kernel
    rw [ha]
    exact (canonical18291 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1093 + difference 5 3) (sourceB1093 + difference 3 5) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA1093 + difference 5 3) (sourceB1093 + difference 3 5) sourceC1093) = raw18292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18292; decide +kernel
    rw [ha]
    exact (canonical18292 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1093 + difference 5 4) (sourceB1093 + difference 4 5) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA1093 + difference 5 4) (sourceB1093 + difference 4 5) sourceC1093) = raw18293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18293; decide +kernel
    rw [ha]
    exact (canonical18293 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1093 sourceB1093 sourceC1093
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1093, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1102 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1102 + difference 0 1) (sourceB1102 + difference 1 0) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA1102 + difference 0 1) (sourceB1102 + difference 1 0) sourceC1102) = raw18455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18455; decide +kernel
    rw [ha]
    exact (canonical18455 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1102 + difference 0 2) (sourceB1102 + difference 2 0) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5479) := by
    have ha : (tripleCharges (sourceA1102 + difference 0 2) (sourceB1102 + difference 2 0) sourceC1102) = raw18456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18456; decide +kernel
    rw [ha]
    exact (canonical18456 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1102 + difference 0 3) (sourceB1102 + difference 3 0) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1102 + difference 0 3) (sourceB1102 + difference 3 0) sourceC1102) = raw18457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18457; decide +kernel
    rw [ha]
    exact (canonical18457 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1102 + difference 0 4) (sourceB1102 + difference 4 0) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1102 + difference 0 4) (sourceB1102 + difference 4 0) sourceC1102) = raw18458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18458; decide +kernel
    rw [ha]
    exact (canonical18458 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1102 + difference 0 5) (sourceB1102 + difference 5 0) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1102 + difference 0 5) (sourceB1102 + difference 5 0) sourceC1102) = raw18459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18459; decide +kernel
    rw [ha]
    exact (canonical18459 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1102 + difference 1 0) (sourceB1102 + difference 0 1) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA1102 + difference 1 0) (sourceB1102 + difference 0 1) sourceC1102) = raw18460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18460; decide +kernel
    rw [ha]
    exact (canonical18460 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1102 + difference 1 2) (sourceB1102 + difference 2 1) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA1102 + difference 1 2) (sourceB1102 + difference 2 1) sourceC1102) = raw18461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18461; decide +kernel
    rw [ha]
    exact (canonical18461 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1102 + difference 1 3) (sourceB1102 + difference 3 1) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1102 + difference 1 3) (sourceB1102 + difference 3 1) sourceC1102) = raw18462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18462; decide +kernel
    rw [ha]
    exact (canonical18462 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1102 + difference 1 4) (sourceB1102 + difference 4 1) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1102 + difference 1 4) (sourceB1102 + difference 4 1) sourceC1102) = raw18463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18463; decide +kernel
    rw [ha]
    exact (canonical18463 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1102 + difference 1 5) (sourceB1102 + difference 5 1) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1102 + difference 1 5) (sourceB1102 + difference 5 1) sourceC1102) = raw18464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18464; decide +kernel
    rw [ha]
    exact (canonical18464 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1102 + difference 2 0) (sourceB1102 + difference 0 2) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4830) := by
    have ha : (tripleCharges (sourceA1102 + difference 2 0) (sourceB1102 + difference 0 2) sourceC1102) = raw18465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18465; decide +kernel
    rw [ha]
    exact (canonical18465 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1102 + difference 2 1) (sourceB1102 + difference 1 2) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5277) := by
    have ha : (tripleCharges (sourceA1102 + difference 2 1) (sourceB1102 + difference 1 2) sourceC1102) = raw18466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18466; decide +kernel
    rw [ha]
    exact (canonical18466 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1102 + difference 2 3) (sourceB1102 + difference 3 2) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA1102 + difference 2 3) (sourceB1102 + difference 3 2) sourceC1102) = raw18467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18467; decide +kernel
    rw [ha]
    exact (canonical18467 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1102 + difference 2 4) (sourceB1102 + difference 4 2) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA1102 + difference 2 4) (sourceB1102 + difference 4 2) sourceC1102) = raw18468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18468; decide +kernel
    rw [ha]
    exact (canonical18468 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1102 + difference 2 5) (sourceB1102 + difference 5 2) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA1102 + difference 2 5) (sourceB1102 + difference 5 2) sourceC1102) = raw18469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18469; decide +kernel
    rw [ha]
    exact (canonical18469 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1102 + difference 3 0) (sourceB1102 + difference 0 3) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA1102 + difference 3 0) (sourceB1102 + difference 0 3) sourceC1102) = raw18470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18470; decide +kernel
    rw [ha]
    exact (canonical18470 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1102 + difference 3 1) (sourceB1102 + difference 1 3) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA1102 + difference 3 1) (sourceB1102 + difference 1 3) sourceC1102) = raw18471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18471; decide +kernel
    rw [ha]
    exact (canonical18471 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1102 + difference 3 2) (sourceB1102 + difference 2 3) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1102 + difference 3 2) (sourceB1102 + difference 2 3) sourceC1102) = raw18472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18472; decide +kernel
    rw [ha]
    exact (canonical18472 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1102 + difference 3 4) (sourceB1102 + difference 4 3) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1102 + difference 3 4) (sourceB1102 + difference 4 3) sourceC1102) = raw18473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18473; decide +kernel
    rw [ha]
    exact (canonical18473 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1102 + difference 3 5) (sourceB1102 + difference 5 3) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1102 + difference 3 5) (sourceB1102 + difference 5 3) sourceC1102) = raw18474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18474; decide +kernel
    rw [ha]
    exact (canonical18474 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1102 + difference 4 0) (sourceB1102 + difference 0 4) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA1102 + difference 4 0) (sourceB1102 + difference 0 4) sourceC1102) = raw18475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18475; decide +kernel
    rw [ha]
    exact (canonical18475 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1102 + difference 4 1) (sourceB1102 + difference 1 4) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA1102 + difference 4 1) (sourceB1102 + difference 1 4) sourceC1102) = raw18476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18476; decide +kernel
    rw [ha]
    exact (canonical18476 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1102 + difference 4 2) (sourceB1102 + difference 2 4) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1102 + difference 4 2) (sourceB1102 + difference 2 4) sourceC1102) = raw18477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18477; decide +kernel
    rw [ha]
    exact (canonical18477 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1102 + difference 4 3) (sourceB1102 + difference 3 4) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1102 + difference 4 3) (sourceB1102 + difference 3 4) sourceC1102) = raw18478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18478; decide +kernel
    rw [ha]
    exact (canonical18478 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1102 + difference 4 5) (sourceB1102 + difference 5 4) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1102 + difference 4 5) (sourceB1102 + difference 5 4) sourceC1102) = raw18479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18479; decide +kernel
    rw [ha]
    exact (canonical18479 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1102 + difference 5 0) (sourceB1102 + difference 0 5) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA1102 + difference 5 0) (sourceB1102 + difference 0 5) sourceC1102) = raw18480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18480; decide +kernel
    rw [ha]
    exact (canonical18480 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1102 + difference 5 1) (sourceB1102 + difference 1 5) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA1102 + difference 5 1) (sourceB1102 + difference 1 5) sourceC1102) = raw18481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18481; decide +kernel
    rw [ha]
    exact (canonical18481 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1102 + difference 5 2) (sourceB1102 + difference 2 5) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1102 + difference 5 2) (sourceB1102 + difference 2 5) sourceC1102) = raw18482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18482; decide +kernel
    rw [ha]
    exact (canonical18482 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1102 + difference 5 3) (sourceB1102 + difference 3 5) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1102 + difference 5 3) (sourceB1102 + difference 3 5) sourceC1102) = raw18483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18483; decide +kernel
    rw [ha]
    exact (canonical18483 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1102 + difference 5 4) (sourceB1102 + difference 4 5) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1102 + difference 5 4) (sourceB1102 + difference 4 5) sourceC1102) = raw18484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18484; decide +kernel
    rw [ha]
    exact (canonical18484 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1102 sourceB1102 sourceC1102
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1102, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck944 : Integer.Sparse.reindex keyMap MixedData.row944 = numericRow944 := by decide +kernel

theorem numericCheck944 (x : Master → ℝ) : Integer.Sparse.eval numericRow944 x =
    (8640 : ℝ) * reducedSource944 x := by
  norm_num [numericRow944, reducedSource944, Integer.Sparse.eval, Sparse.eval, nodeValue5127, nodeValue5129, nodeValue5134, nodeValue5144, nodeValue5258, nodeValue5376, nodeValue5378, nodeValue5381, nodeValue5394, nodeValue5409, nodeValue5420, nodeValue5424, nodeValue5425, nodeValue5430, nodeValue5432, nodeValue5434, nodeValue5441, nodeValue5477] <;> ring

theorem reindexCheck945 : Integer.Sparse.reindex keyMap MixedData.row945 = numericRow945 := by decide +kernel

theorem numericCheck945 (x : Master → ℝ) : Integer.Sparse.eval numericRow945 x =
    (2160 : ℝ) * reducedSource945 x := by
  norm_num [numericRow945, reducedSource945, Integer.Sparse.eval, Sparse.eval, nodeValue3513, nodeValue3514, nodeValue3516, nodeValue3533, nodeValue3557, nodeValue3793, nodeValue3795, nodeValue3807, nodeValue3833, nodeValue3834, nodeValue3838, nodeValue3840, nodeValue3850, nodeValue3852, nodeValue3860, nodeValue3870, nodeValue3871, nodeValue3989] <;> ring

theorem reindexCheck946 : Integer.Sparse.reindex keyMap MixedData.row946 = numericRow946 := by decide +kernel

theorem numericCheck946 (x : Master → ℝ) : Integer.Sparse.eval numericRow946 x =
    (5184 : ℝ) * reducedSource946 x := by
  norm_num [numericRow946, reducedSource946, Integer.Sparse.eval, Sparse.eval, nodeValue4778, nodeValue4782, nodeValue4801, nodeValue5341, nodeValue5344, nodeValue5351, nodeValue5415, nodeValue5423, nodeValue5424, nodeValue5433, nodeValue5500] <;> ring

theorem reindexCheck955 : Integer.Sparse.reindex keyMap MixedData.row955 = numericRow955 := by decide +kernel

theorem numericCheck955 (x : Master → ℝ) : Integer.Sparse.eval numericRow955 x =
    (5760 : ℝ) * reducedSource955 x := by
  norm_num [numericRow955, reducedSource955, Integer.Sparse.eval, Sparse.eval, nodeValue4815, nodeValue4830, nodeValue4885, nodeValue5251, nodeValue5277, nodeValue5359, nodeValue5406, nodeValue5422, nodeValue5425, nodeValue5433, nodeValue5447, nodeValue5479] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero944 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource944 (mixedVector B) = 0 := by
  have h5127 : mixedVector B (Sum.inr 5127) = Sparse.eval nodeValue5127 (mixedVector B) := by
    change mixedMoment B node5127 node5127Labels = _
    exact sound5127 B hB hF
  have h5129 : mixedVector B (Sum.inr 5129) = Sparse.eval nodeValue5129 (mixedVector B) := by
    change mixedMoment B node5129 node5129Labels = _
    exact sound5129 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5144 : mixedVector B (Sum.inr 5144) = Sparse.eval nodeValue5144 (mixedVector B) := by
    change mixedMoment B node5144 node5144Labels = _
    exact sound5144 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5376 : mixedVector B (Sum.inr 5376) = Sparse.eval nodeValue5376 (mixedVector B) := by
    change mixedMoment B node5376 node5376Labels = _
    exact sound5376 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5381 : mixedVector B (Sum.inr 5381) = Sparse.eval nodeValue5381 (mixedVector B) := by
    change mixedMoment B node5381 node5381Labels = _
    exact sound5381 B hB hF
  have h5394 : mixedVector B (Sum.inr 5394) = Sparse.eval nodeValue5394 (mixedVector B) := by
    change mixedMoment B node5394 node5394Labels = _
    exact sound5394 B hB hF
  have h5409 : mixedVector B (Sum.inr 5409) = Sparse.eval nodeValue5409 (mixedVector B) := by
    change mixedMoment B node5409 node5409Labels = _
    exact sound5409 B hB hF
  have h5420 : mixedVector B (Sum.inr 5420) = Sparse.eval nodeValue5420 (mixedVector B) := by
    change mixedMoment B node5420 node5420Labels = _
    exact sound5420 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5425 : mixedVector B (Sum.inr 5425) = Sparse.eval nodeValue5425 (mixedVector B) := by
    change mixedMoment B node5425 node5425Labels = _
    exact sound5425 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5432 : mixedVector B (Sum.inr 5432) = Sparse.eval nodeValue5432 (mixedVector B) := by
    change mixedMoment B node5432 node5432Labels = _
    exact sound5432 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5441 : mixedVector B (Sum.inr 5441) = Sparse.eval nodeValue5441 (mixedVector B) := by
    change mixedMoment B node5441 node5441Labels = _
    exact sound5441 B hB hF
  have h5477 : mixedVector B (Sum.inr 5477) = Sparse.eval nodeValue5477 (mixedVector B) := by
    change mixedMoment B node5477 node5477Labels = _
    exact sound5477 B hB hF
  simpa only [sourceForm1091, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5127, h5129, h5134, h5144, h5258, h5376, h5378, h5381, h5394, h5409, h5420, h5424, h5425, h5430, h5432, h5434, h5441, h5477, reducedSource944] using sourceEq1091 B hB

theorem rowSound944 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row944 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck944, numericCheck944, reducedZero944 B hB hF, mul_zero]

theorem reducedZero945 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource945 (mixedVector B) = 0 := by
  have h3513 : mixedVector B (Sum.inr 3513) = Sparse.eval nodeValue3513 (mixedVector B) := by
    change mixedMoment B node3513 node3513Labels = _
    exact sound3513 B hB hF
  have h3514 : mixedVector B (Sum.inr 3514) = Sparse.eval nodeValue3514 (mixedVector B) := by
    change mixedMoment B node3514 node3514Labels = _
    exact sound3514 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3557 : mixedVector B (Sum.inr 3557) = Sparse.eval nodeValue3557 (mixedVector B) := by
    change mixedMoment B node3557 node3557Labels = _
    exact sound3557 B hB hF
  have h3793 : mixedVector B (Sum.inr 3793) = Sparse.eval nodeValue3793 (mixedVector B) := by
    change mixedMoment B node3793 node3793Labels = _
    exact sound3793 B hB hF
  have h3795 : mixedVector B (Sum.inr 3795) = Sparse.eval nodeValue3795 (mixedVector B) := by
    change mixedMoment B node3795 node3795Labels = _
    exact sound3795 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3833 : mixedVector B (Sum.inr 3833) = Sparse.eval nodeValue3833 (mixedVector B) := by
    change mixedMoment B node3833 node3833Labels = _
    exact sound3833 B hB hF
  have h3834 : mixedVector B (Sum.inr 3834) = Sparse.eval nodeValue3834 (mixedVector B) := by
    change mixedMoment B node3834 node3834Labels = _
    exact sound3834 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3852 : mixedVector B (Sum.inr 3852) = Sparse.eval nodeValue3852 (mixedVector B) := by
    change mixedMoment B node3852 node3852Labels = _
    exact sound3852_e B hB hF
  have h3860 : mixedVector B (Sum.inr 3860) = Sparse.eval nodeValue3860 (mixedVector B) := by
    change mixedMoment B node3860 node3860Labels = _
    exact sound3860 B hB hF
  have h3870 : mixedVector B (Sum.inr 3870) = Sparse.eval nodeValue3870 (mixedVector B) := by
    change mixedMoment B node3870 node3870Labels = _
    exact sound3870 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3989 : mixedVector B (Sum.inr 3989) = Sparse.eval nodeValue3989 (mixedVector B) := by
    change mixedMoment B node3989 node3989Labels = _
    exact sound3989 B hB hF
  simpa only [sourceForm1092, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3513, h3514, h3516, h3533, h3557, h3793, h3795, h3807, h3833, h3834, h3838, h3840, h3850, h3852, h3860, h3870, h3871, h3989, reducedSource945] using sourceEq1092 B hB

theorem rowSound945 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row945 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck945, numericCheck945, reducedZero945 B hB hF, mul_zero]

theorem reducedZero946 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource946 (mixedVector B) = 0 := by
  have h4778 : mixedVector B (Sum.inr 4778) = Sparse.eval nodeValue4778 (mixedVector B) := by
    change mixedMoment B node4778 node4778Labels = _
    exact sound4778 B hB hF
  have h4782 : mixedVector B (Sum.inr 4782) = Sparse.eval nodeValue4782 (mixedVector B) := by
    change mixedMoment B node4782 node4782Labels = _
    exact sound4782 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h5341 : mixedVector B (Sum.inr 5341) = Sparse.eval nodeValue5341 (mixedVector B) := by
    change mixedMoment B node5341 node5341Labels = _
    exact sound5341 B hB hF
  have h5344 : mixedVector B (Sum.inr 5344) = Sparse.eval nodeValue5344 (mixedVector B) := by
    change mixedMoment B node5344 node5344Labels = _
    exact sound5344 B hB hF
  have h5351 : mixedVector B (Sum.inr 5351) = Sparse.eval nodeValue5351 (mixedVector B) := by
    change mixedMoment B node5351 node5351Labels = _
    exact sound5351 B hB hF
  have h5415 : mixedVector B (Sum.inr 5415) = Sparse.eval nodeValue5415 (mixedVector B) := by
    change mixedMoment B node5415 node5415Labels = _
    exact sound5415_e B hB hF
  have h5423 : mixedVector B (Sum.inr 5423) = Sparse.eval nodeValue5423 (mixedVector B) := by
    change mixedMoment B node5423 node5423Labels = _
    exact sound5423 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5500 : mixedVector B (Sum.inr 5500) = Sparse.eval nodeValue5500 (mixedVector B) := by
    change mixedMoment B node5500 node5500Labels = _
    exact sound5500_e B hB hF
  simpa only [sourceForm1093, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4778, h4782, h4801, h5341, h5344, h5351, h5415, h5423, h5424, h5433, h5500, reducedSource946] using sourceEq1093 B hB

theorem rowSound946 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row946 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck946, numericCheck946, reducedZero946 B hB hF, mul_zero]

theorem reducedZero955 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource955 (mixedVector B) = 0 := by
  have h4815 : mixedVector B (Sum.inr 4815) = Sparse.eval nodeValue4815 (mixedVector B) := by
    change mixedMoment B node4815 node4815Labels = _
    exact sound4815 B hB hF
  have h4830 : mixedVector B (Sum.inr 4830) = Sparse.eval nodeValue4830 (mixedVector B) := by
    change mixedMoment B node4830 node4830Labels = _
    exact sound4830 B hB hF
  have h4885 : mixedVector B (Sum.inr 4885) = Sparse.eval nodeValue4885 (mixedVector B) := by
    change mixedMoment B node4885 node4885Labels = _
    exact sound4885 B hB hF
  have h5251 : mixedVector B (Sum.inr 5251) = Sparse.eval nodeValue5251 (mixedVector B) := by
    change mixedMoment B node5251 node5251Labels = _
    exact sound5251 B hB hF
  have h5277 : mixedVector B (Sum.inr 5277) = Sparse.eval nodeValue5277 (mixedVector B) := by
    change mixedMoment B node5277 node5277Labels = _
    exact sound5277 B hB hF
  have h5359 : mixedVector B (Sum.inr 5359) = Sparse.eval nodeValue5359 (mixedVector B) := by
    change mixedMoment B node5359 node5359Labels = _
    exact sound5359 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5422 : mixedVector B (Sum.inr 5422) = Sparse.eval nodeValue5422 (mixedVector B) := by
    change mixedMoment B node5422 node5422Labels = _
    exact sound5422 B hB hF
  have h5425 : mixedVector B (Sum.inr 5425) = Sparse.eval nodeValue5425 (mixedVector B) := by
    change mixedMoment B node5425 node5425Labels = _
    exact sound5425 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  have h5479 : mixedVector B (Sum.inr 5479) = Sparse.eval nodeValue5479 (mixedVector B) := by
    change mixedMoment B node5479 node5479Labels = _
    exact sound5479 B hB hF
  simpa only [sourceForm1102, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4815, h4830, h4885, h5251, h5277, h5359, h5406, h5422, h5425, h5433, h5447, h5479, reducedSource955] using sourceEq1102 B hB

theorem rowSound955 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row955 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck955, numericCheck955, reducedZero955 B hB hF, mul_zero]

theorem sourceRowsAt944 : MixedData.sourceRows (944 : Fin 2425) =
    MixedData.row944 := by decide +kernel

theorem sourceRowsAt945 : MixedData.sourceRows (945 : Fin 2425) =
    MixedData.row945 := by decide +kernel

theorem sourceRowsAt946 : MixedData.sourceRows (946 : Fin 2425) =
    MixedData.row946 := by decide +kernel

theorem sourceRowsAt947 : MixedData.sourceRows (947 : Fin 2425) =
    MixedData.row947 := by decide +kernel

theorem sourceRowsAt948 : MixedData.sourceRows (948 : Fin 2425) =
    MixedData.row948 := by decide +kernel

theorem sourceRowsAt949 : MixedData.sourceRows (949 : Fin 2425) =
    MixedData.row949 := by decide +kernel

theorem sourceRowsAt950 : MixedData.sourceRows (950 : Fin 2425) =
    MixedData.row950 := by decide +kernel

theorem sourceRowsAt951 : MixedData.sourceRows (951 : Fin 2425) =
    MixedData.row951 := by decide +kernel

theorem sourceRowsAt952 : MixedData.sourceRows (952 : Fin 2425) =
    MixedData.row952 := by decide +kernel

theorem sourceRowsAt953 : MixedData.sourceRows (953 : Fin 2425) =
    MixedData.row953 := by decide +kernel

theorem sourceRowsAt954 : MixedData.sourceRows (954 : Fin 2425) =
    MixedData.row954 := by decide +kernel

theorem sourceRowsAt955 : MixedData.sourceRows (955 : Fin 2425) =
    MixedData.row955 := by decide +kernel

theorem sourceRowsAt956 : MixedData.sourceRows (956 : Fin 2425) =
    MixedData.row956 := by decide +kernel

theorem sourceRowsAt957 : MixedData.sourceRows (957 : Fin 2425) =
    MixedData.row957 := by decide +kernel

theorem sourceRowsAt958 : MixedData.sourceRows (958 : Fin 2425) =
    MixedData.row958 := by decide +kernel

theorem sourceRowsAt959 : MixedData.sourceRows (959 : Fin 2425) =
    MixedData.row959 := by decide +kernel

theorem chunkSound59_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 59) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 944 ∨ k.val = 945 ∨ k.val = 946 ∨ k.val = 947 ∨ k.val = 948 ∨ k.val = 949 ∨ k.val = 950 ∨ k.val = 951 ∨ k.val = 952 ∨ k.val = 953 ∨ k.val = 954 ∨ k.val = 955 ∨ k.val = 956 ∨ k.val = 957 ∨ k.val = 958 ∨ k.val = 959 := by omega
  rcases heq with h944 | h945 | h946 | h947 | h948 | h949 | h950 | h951 | h952 | h953 | h954 | h955 | h956 | h957 | h958 | h959
  · have he : k = (944 : Fin 2425) := Fin.ext h944
    subst k
    rw [sourceRowsAt944]
    exact rowSound944 B hB hF
  · have he : k = (945 : Fin 2425) := Fin.ext h945
    subst k
    rw [sourceRowsAt945]
    exact rowSound945 B hB hF
  · have he : k = (946 : Fin 2425) := Fin.ext h946
    subst k
    rw [sourceRowsAt946]
    exact rowSound946 B hB hF
  · have he : k = (947 : Fin 2425) := Fin.ext h947
    subst k
    rw [sourceRowsAt947]
    exact rowSound947_e B hB hF
  · have he : k = (948 : Fin 2425) := Fin.ext h948
    subst k
    rw [sourceRowsAt948]
    exact rowSound948_e B hB hF
  · have he : k = (949 : Fin 2425) := Fin.ext h949
    subst k
    rw [sourceRowsAt949]
    exact rowSound949_e B hB hF
  · have he : k = (950 : Fin 2425) := Fin.ext h950
    subst k
    rw [sourceRowsAt950]
    exact rowSound950_e B hB hF
  · have he : k = (951 : Fin 2425) := Fin.ext h951
    subst k
    rw [sourceRowsAt951]
    exact rowSound951_e B hB hF
  · have he : k = (952 : Fin 2425) := Fin.ext h952
    subst k
    rw [sourceRowsAt952]
    exact rowSound952_e B hB hF
  · have he : k = (953 : Fin 2425) := Fin.ext h953
    subst k
    rw [sourceRowsAt953]
    exact rowSound953_e B hB hF
  · have he : k = (954 : Fin 2425) := Fin.ext h954
    subst k
    rw [sourceRowsAt954]
    exact rowSound954_e B hB hF
  · have he : k = (955 : Fin 2425) := Fin.ext h955
    subst k
    rw [sourceRowsAt955]
    exact rowSound955 B hB hF
  · have he : k = (956 : Fin 2425) := Fin.ext h956
    subst k
    rw [sourceRowsAt956]
    exact rowSound956_e B hB hF
  · have he : k = (957 : Fin 2425) := Fin.ext h957
    subst k
    rw [sourceRowsAt957]
    exact rowSound957_e B hB hF
  · have he : k = (958 : Fin 2425) := Fin.ext h958
    subst k
    rw [sourceRowsAt958]
    exact rowSound958_e B hB hF
  · have he : k = (959 : Fin 2425) := Fin.ext h959
    subst k
    rw [sourceRowsAt959]
    exact rowSound959_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e_oai
