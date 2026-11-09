-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:09:10.603272+00:00
-- url     : https://prove2.me/submissions/3307f734-bcee-48a2-a29b-f2bba6c0c708

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E111
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound512_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound513_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound514_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound515_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound516_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound518_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound519_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound521_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound523_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound524_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound525_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound526_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1446 raw1446Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw1446 raw1446Labels = mixedMoment B raw1446step0 raw1446step0Labels := by
      have ha : raw1446step0 = (fun i j => raw1446 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1446step0 raw1446; decide +kernel
      have hl : raw1446step0Labels = raw1446Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1446 raw1446Labels permutation2 permutation4
    mixedMoment B raw1446step0 raw1446step0Labels = mixedMoment B raw1446step1 raw1446step1Labels := by
      have ha : raw1446step1 = raw1446step0 := by apply Matrix.ext; unfold raw1446step1 raw1446step0; decide +kernel
      have hl : raw1446step0Labels = labelEmbedding7 ∘ raw1446step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1446step0 raw1446step0Labels raw1446step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4621 node4621Labels := by rfl

theorem canonical1447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1447 raw1447Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw1447 raw1447Labels = mixedMoment B raw1447step0 raw1447step0Labels := by
      have ha : raw1447step0 = (fun i j => raw1447 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1447step0 raw1447; decide +kernel
      have hl : raw1447step0Labels = raw1447Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1447 raw1447Labels permutation2 permutation4
    _ = mixedMoment B node1297 node1297Labels := by rfl

theorem canonical1448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1448 raw1448Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw1448 raw1448Labels = mixedMoment B raw1448step0 raw1448step0Labels := by
      have ha : raw1448step0 = (fun i j => raw1448 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1448step0 raw1448; decide +kernel
      have hl : raw1448step0Labels = raw1448Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1448 raw1448Labels permutation7 permutation6
    mixedMoment B raw1448step0 raw1448step0Labels = mixedMoment B raw1448step1 raw1448step1Labels := by
      have ha : raw1448step1 = raw1448step0 := by apply Matrix.ext; unfold raw1448step1 raw1448step0; decide +kernel
      have hl : raw1448step0Labels = labelEmbedding1 ∘ raw1448step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1448step0 raw1448step0Labels raw1448step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2289 node2289Labels := by rfl

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

theorem canonical2283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2283 raw2283Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw2283 raw2283Labels = mixedMoment B raw2283step0 raw2283step0Labels := by
      have ha : raw2283step0 = (fun i j => raw2283 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2283step0 raw2283; decide +kernel
      have hl : raw2283step0Labels = raw2283Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2283 raw2283Labels permutation8 permutation4
    mixedMoment B raw2283step0 raw2283step0Labels = mixedMoment B raw2283step1 raw2283step1Labels := by
      have ha : raw2283step1 = raw2283step0 := by apply Matrix.ext; unfold raw2283step1 raw2283step0; decide +kernel
      have hl : raw2283step0Labels = labelEmbedding7 ∘ raw2283step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2283step0 raw2283step0Labels raw2283step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5272 node5272Labels := by rfl

theorem canonical2284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2284 raw2284Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw2284 raw2284Labels = mixedMoment B raw2284step0 raw2284step0Labels := by
      have ha : raw2284step0 = (fun i j => raw2284 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2284step0 raw2284; decide +kernel
      have hl : raw2284step0Labels = raw2284Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2284 raw2284Labels permutation8 permutation4
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical2285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2285 raw2285Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw2285 raw2285Labels = mixedMoment B raw2285step0 raw2285step0Labels := by
      have ha : raw2285step0 = (fun i j => raw2285 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2285step0 raw2285; decide +kernel
      have hl : raw2285step0Labels = raw2285Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2285 raw2285Labels permutation31 permutation6
    mixedMoment B raw2285step0 raw2285step0Labels = mixedMoment B raw2285step1 raw2285step1Labels := by
      have ha : raw2285step1 = raw2285step0 := by apply Matrix.ext; unfold raw2285step1 raw2285step0; decide +kernel
      have hl : raw2285step0Labels = labelEmbedding1 ∘ raw2285step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2285step0 raw2285step0Labels raw2285step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

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

theorem canonical2325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2325 raw2325Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw2325 raw2325Labels = mixedMoment B raw2325step0 raw2325step0Labels := by
      have ha : raw2325step0 = (fun i j => raw2325 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2325step0 raw2325; decide +kernel
      have hl : raw2325step0Labels = raw2325Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2325 raw2325Labels permutation2 permutation4
    mixedMoment B raw2325step0 raw2325step0Labels = mixedMoment B raw2325step1 raw2325step1Labels := by
      have ha : raw2325step1 = raw2325step0 := by apply Matrix.ext; unfold raw2325step1 raw2325step0; decide +kernel
      have hl : raw2325step0Labels = labelEmbedding7 ∘ raw2325step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2325step0 raw2325step0Labels raw2325step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

theorem canonical2326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2326 raw2326Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw2326 raw2326Labels = mixedMoment B raw2326step0 raw2326step0Labels := by
      have ha : raw2326step0 = (fun i j => raw2326 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2326step0 raw2326; decide +kernel
      have hl : raw2326step0Labels = raw2326Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2326 raw2326Labels permutation2 permutation4
    _ = mixedMoment B node2788 node2788Labels := by rfl

theorem canonical2327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2327 raw2327Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw2327 raw2327Labels = mixedMoment B raw2327step0 raw2327step0Labels := by
      have ha : raw2327step0 = (fun i j => raw2327 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2327step0 raw2327; decide +kernel
      have hl : raw2327step0Labels = raw2327Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2327 raw2327Labels permutation3 permutation6
    mixedMoment B raw2327step0 raw2327step0Labels = mixedMoment B raw2327step1 raw2327step1Labels := by
      have ha : raw2327step1 = -raw2327step0 := by apply Matrix.ext; change ∀ i j, raw2327step1 i j = -(raw2327step0 i j); unfold raw2327step1 raw2327step0; decide +kernel
      have hl : raw2327step1Labels = raw2327step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2327step1 raw2327step1Labels = mixedMoment B raw2327step2 raw2327step2Labels := by
      have ha : raw2327step2 = raw2327step1 := by apply Matrix.ext; unfold raw2327step2 raw2327step1; decide +kernel
      have hl : raw2327step1Labels = labelEmbedding1 ∘ raw2327step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2327step1 raw2327step1Labels raw2327step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3633 node3633Labels := by rfl

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

theorem canonical284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw284 raw284Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw284 raw284Labels = mixedMoment B raw284step0 raw284step0Labels := by
      have ha : raw284step0 = (fun i j => raw284 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw284step0 raw284; decide +kernel
      have hl : raw284step0Labels = raw284Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw284 raw284Labels permutation2 permutation5
    mixedMoment B raw284step0 raw284step0Labels = mixedMoment B raw284step1 raw284step1Labels := by
      have ha : raw284step1 = raw284step0 := by apply Matrix.ext; unfold raw284step1 raw284step0; decide +kernel
      have hl : raw284step0Labels = labelEmbedding1 ∘ raw284step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw284step0 raw284step0Labels raw284step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2788 node2788Labels := by rfl

theorem canonical285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw285 raw285Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw285 raw285Labels = mixedMoment B raw285step0 raw285step0Labels := by
      have ha : raw285step0 = (fun i j => raw285 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw285step0 raw285; decide +kernel
      have hl : raw285step0Labels = raw285Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw285 raw285Labels permutation2 permutation5
    _ = mixedMoment B node420 node420Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw404 raw404Labels = mixedMoment B node3121 node3121Labels := by
  calc
    mixedMoment B raw404 raw404Labels = mixedMoment B raw404step0 raw404step0Labels := by
      have ha : raw404step0 = (fun i j => raw404 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw404step0 raw404; decide +kernel
      have hl : raw404step0Labels = raw404Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw404 raw404Labels permutation2 permutation5
    mixedMoment B raw404step0 raw404step0Labels = mixedMoment B raw404step1 raw404step1Labels := by
      have ha : raw404step1 = raw404step0 := by apply Matrix.ext; unfold raw404step1 raw404step0; decide +kernel
      have hl : raw404step0Labels = labelEmbedding1 ∘ raw404step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw404step0 raw404step0Labels raw404step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3121 node3121Labels := by rfl

theorem canonical405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw405 raw405Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw405 raw405Labels = mixedMoment B raw405step0 raw405step0Labels := by
      have ha : raw405step0 = (fun i j => raw405 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw405step0 raw405; decide +kernel
      have hl : raw405step0Labels = raw405Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw405 raw405Labels permutation2 permutation4
    _ = mixedMoment B node420 node420Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5105 raw5105Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw5105 raw5105Labels = mixedMoment B raw5105step0 raw5105step0Labels := by
      have hz : ∀ j, raw5105 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5105step0 = (fun i j => raw5105 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5105step0 raw5105; decide +kernel
      have hl : raw5105step0Labels = raw5105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5105 raw5105Labels permutation434 hz
    mixedMoment B raw5105step0 raw5105step0Labels = mixedMoment B raw5105step1 raw5105step1Labels := by
      have hz : ∀ j, raw5105step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5105step1 = (fun i j => raw5105step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5105step1 raw5105step0; decide +kernel
      have hl : raw5105step1Labels = raw5105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5105step0 raw5105step0Labels permutation80 hz
    mixedMoment B raw5105step1 raw5105step1Labels = mixedMoment B raw5105step2 raw5105step2Labels := by
      have hz : ∀ j, raw5105step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5105step2 = (fun i j => raw5105step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5105step2 raw5105step1; decide +kernel
      have hl : raw5105step2Labels = raw5105step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5105step1 raw5105step1Labels permutation14 hz
    mixedMoment B raw5105step2 raw5105step2Labels = mixedMoment B raw5105step3 raw5105step3Labels := by
      have ha : raw5105step3 = (fun i j => raw5105step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5105step3 raw5105step2; decide +kernel
      have hl : raw5105step3Labels = raw5105step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5105step2 raw5105step2Labels permutation7 permutation7
    mixedMoment B raw5105step3 raw5105step3Labels = mixedMoment B raw5105step4 raw5105step4Labels := by
      have ha : raw5105step4 = raw5105step3 := by apply Matrix.ext; unfold raw5105step4 raw5105step3; decide +kernel
      have hl : raw5105step3Labels = labelEmbedding10 ∘ raw5105step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5105step3 raw5105step3Labels raw5105step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5308 node5308Labels := by rfl

theorem canonical5110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5110 raw5110Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw5110 raw5110Labels = mixedMoment B raw5110step0 raw5110step0Labels := by
      have hz : ∀ j, raw5110 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5110step0 = (fun i j => raw5110 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5110step0 raw5110; decide +kernel
      have hl : raw5110step0Labels = raw5110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5110 raw5110Labels permutation434 hz
    mixedMoment B raw5110step0 raw5110step0Labels = mixedMoment B raw5110step1 raw5110step1Labels := by
      have hz : ∀ j, raw5110step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5110step1 = (fun i j => raw5110step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5110step1 raw5110step0; decide +kernel
      have hl : raw5110step1Labels = raw5110step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5110step0 raw5110step0Labels permutation80 hz
    mixedMoment B raw5110step1 raw5110step1Labels = mixedMoment B raw5110step2 raw5110step2Labels := by
      have ha : raw5110step2 = (fun i j => raw5110step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5110step2 raw5110step1; decide +kernel
      have hl : raw5110step2Labels = raw5110step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5110step1 raw5110step1Labels permutation10 permutation2
    _ = mixedMoment B node5272 node5272Labels := by rfl

theorem canonical5115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5115 raw5115Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw5115 raw5115Labels = mixedMoment B raw5115step0 raw5115step0Labels := by
      have hz : ∀ j, raw5115 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5115step0 = (fun i j => raw5115 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5115step0 raw5115; decide +kernel
      have hl : raw5115step0Labels = raw5115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5115 raw5115Labels permutation434 hz
    mixedMoment B raw5115step0 raw5115step0Labels = mixedMoment B raw5115step1 raw5115step1Labels := by
      have hz : ∀ j, raw5115step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5115step1 = (fun i j => raw5115step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5115step1 raw5115step0; decide +kernel
      have hl : raw5115step1Labels = raw5115step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5115step0 raw5115step0Labels permutation56 hz
    mixedMoment B raw5115step1 raw5115step1Labels = mixedMoment B raw5115step2 raw5115step2Labels := by
      have ha : raw5115step2 = (fun i j => raw5115step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5115step2 raw5115step1; decide +kernel
      have hl : raw5115step2Labels = raw5115step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5115step1 raw5115step1Labels permutation10 permutation2
    _ = mixedMoment B node5272 node5272Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5120 raw5120Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw5120 raw5120Labels = mixedMoment B raw5120step0 raw5120step0Labels := by
      have hz : ∀ j, raw5120 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5120step0 = (fun i j => raw5120 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5120step0 raw5120; decide +kernel
      have hl : raw5120step0Labels = raw5120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5120 raw5120Labels permutation346 hz
    mixedMoment B raw5120step0 raw5120step0Labels = mixedMoment B raw5120step1 raw5120step1Labels := by
      have hz : ∀ j, raw5120step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5120step1 = (fun i j => raw5120step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5120step1 raw5120step0; decide +kernel
      have hl : raw5120step1Labels = raw5120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5120step0 raw5120step0Labels permutation56 hz
    mixedMoment B raw5120step1 raw5120step1Labels = mixedMoment B raw5120step2 raw5120step2Labels := by
      have ha : raw5120step2 = (fun i j => raw5120step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5120step2 raw5120step1; decide +kernel
      have hl : raw5120step2Labels = raw5120step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5120step1 raw5120step1Labels permutation10 permutation2
    _ = mixedMoment B node5272 node5272Labels := by rfl

theorem canonical5121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5121 raw5121Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw5121 raw5121Labels = mixedMoment B raw5121step0 raw5121step0Labels := by
      have hz : ∀ j, raw5121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5121step0 = (fun i j => raw5121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5121step0 raw5121; decide +kernel
      have hl : raw5121step0Labels = raw5121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5121 raw5121Labels permutation434 hz
    mixedMoment B raw5121step0 raw5121step0Labels = mixedMoment B raw5121step1 raw5121step1Labels := by
      have hz : ∀ j, raw5121step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5121step1 = (fun i j => raw5121step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5121step1 raw5121step0; decide +kernel
      have hl : raw5121step1Labels = raw5121step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5121step0 raw5121step0Labels permutation80 hz
    mixedMoment B raw5121step1 raw5121step1Labels = mixedMoment B raw5121step2 raw5121step2Labels := by
      have hz : ∀ j, raw5121step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5121step2 = (fun i j => raw5121step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5121step2 raw5121step1; decide +kernel
      have hl : raw5121step2Labels = raw5121step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5121step1 raw5121step1Labels permutation14 hz
    _ = mixedMoment B node4621 node4621Labels := by rfl

theorem canonical5122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5122 raw5122Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw5122 raw5122Labels = mixedMoment B raw5122step0 raw5122step0Labels := by
      have hz : ∀ j, raw5122 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5122step0 = (fun i j => raw5122 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5122step0 raw5122; decide +kernel
      have hl : raw5122step0Labels = raw5122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5122 raw5122Labels permutation434 hz
    mixedMoment B raw5122step0 raw5122step0Labels = mixedMoment B raw5122step1 raw5122step1Labels := by
      have hz : ∀ j, raw5122step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5122step1 = (fun i j => raw5122step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5122step1 raw5122step0; decide +kernel
      have hl : raw5122step1Labels = raw5122step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5122step0 raw5122step0Labels permutation80 hz
    mixedMoment B raw5122step1 raw5122step1Labels = mixedMoment B raw5122step2 raw5122step2Labels := by
      have ha : raw5122step2 = (fun i j => raw5122step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5122step2 raw5122step1; decide +kernel
      have hl : raw5122step2Labels = raw5122step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5122step1 raw5122step1Labels permutation31 permutation2
    mixedMoment B raw5122step2 raw5122step2Labels = mixedMoment B raw5122step3 raw5122step3Labels := by
      have ha : raw5122step3 = -raw5122step2 := by apply Matrix.ext; change ∀ i j, raw5122step3 i j = -(raw5122step2 i j); unfold raw5122step3 raw5122step2; decide +kernel
      have hl : raw5122step3Labels = raw5122step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical5123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5123 raw5123Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw5123 raw5123Labels = mixedMoment B raw5123step0 raw5123step0Labels := by
      have hz : ∀ j, raw5123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5123step0 = (fun i j => raw5123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5123step0 raw5123; decide +kernel
      have hl : raw5123step0Labels = raw5123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5123 raw5123Labels permutation434 hz
    mixedMoment B raw5123step0 raw5123step0Labels = mixedMoment B raw5123step1 raw5123step1Labels := by
      have hz : ∀ j, raw5123step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5123step1 = (fun i j => raw5123step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5123step1 raw5123step0; decide +kernel
      have hl : raw5123step1Labels = raw5123step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5123step0 raw5123step0Labels permutation56 hz
    mixedMoment B raw5123step1 raw5123step1Labels = mixedMoment B raw5123step2 raw5123step2Labels := by
      have ha : raw5123step2 = (fun i j => raw5123step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5123step2 raw5123step1; decide +kernel
      have hl : raw5123step2Labels = raw5123step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5123step1 raw5123step1Labels permutation31 permutation2
    mixedMoment B raw5123step2 raw5123step2Labels = mixedMoment B raw5123step3 raw5123step3Labels := by
      have ha : raw5123step3 = -raw5123step2 := by apply Matrix.ext; change ∀ i j, raw5123step3 i j = -(raw5123step2 i j); unfold raw5123step3 raw5123step2; decide +kernel
      have hl : raw5123step3Labels = raw5123step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical5124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5124 raw5124Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw5124 raw5124Labels = mixedMoment B raw5124step0 raw5124step0Labels := by
      have hz : ∀ j, raw5124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5124step0 = (fun i j => raw5124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5124step0 raw5124; decide +kernel
      have hl : raw5124step0Labels = raw5124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5124 raw5124Labels permutation346 hz
    mixedMoment B raw5124step0 raw5124step0Labels = mixedMoment B raw5124step1 raw5124step1Labels := by
      have hz : ∀ j, raw5124step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5124step1 = (fun i j => raw5124step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5124step1 raw5124step0; decide +kernel
      have hl : raw5124step1Labels = raw5124step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5124step0 raw5124step0Labels permutation56 hz
    mixedMoment B raw5124step1 raw5124step1Labels = mixedMoment B raw5124step2 raw5124step2Labels := by
      have ha : raw5124step2 = (fun i j => raw5124step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5124step2 raw5124step1; decide +kernel
      have hl : raw5124step2Labels = raw5124step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5124step1 raw5124step1Labels permutation31 permutation2
    mixedMoment B raw5124step2 raw5124step2Labels = mixedMoment B raw5124step3 raw5124step3Labels := by
      have ha : raw5124step3 = -raw5124step2 := by apply Matrix.ext; change ∀ i j, raw5124step3 i j = -(raw5124step2 i j); unfold raw5124step3 raw5124step2; decide +kernel
      have hl : raw5124step3Labels = raw5124step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical5135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5135 raw5135Labels = mixedMoment B node2786 node2786Labels := by
  calc
    mixedMoment B raw5135 raw5135Labels = mixedMoment B raw5135step0 raw5135step0Labels := by
      have hz : ∀ j, raw5135 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5135step0 = (fun i j => raw5135 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5135step0 raw5135; decide +kernel
      have hl : raw5135step0Labels = raw5135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5135 raw5135Labels permutation434 hz
    mixedMoment B raw5135step0 raw5135step0Labels = mixedMoment B raw5135step1 raw5135step1Labels := by
      have hz : ∀ j, raw5135step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5135step1 = (fun i j => raw5135step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5135step1 raw5135step0; decide +kernel
      have hl : raw5135step1Labels = raw5135step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5135step0 raw5135step0Labels permutation80 hz
    mixedMoment B raw5135step1 raw5135step1Labels = mixedMoment B raw5135step2 raw5135step2Labels := by
      have hz : ∀ j, raw5135step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5135step2 = (fun i j => raw5135step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5135step2 raw5135step1; decide +kernel
      have hl : raw5135step2Labels = raw5135step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5135step1 raw5135step1Labels permutation14 hz
    mixedMoment B raw5135step2 raw5135step2Labels = mixedMoment B raw5135step3 raw5135step3Labels := by
      have ha : raw5135step3 = (fun i j => raw5135step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5135step3 raw5135step2; decide +kernel
      have hl : raw5135step3Labels = raw5135step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5135step2 raw5135step2Labels permutation7 permutation7
    mixedMoment B raw5135step3 raw5135step3Labels = mixedMoment B raw5135step4 raw5135step4Labels := by
      have ha : raw5135step4 = raw5135step3 := by apply Matrix.ext; unfold raw5135step4 raw5135step3; decide +kernel
      have hl : raw5135step3Labels = labelEmbedding1 ∘ raw5135step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5135step3 raw5135step3Labels raw5135step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2786 node2786Labels := by rfl

theorem canonical5140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5140 raw5140Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw5140 raw5140Labels = mixedMoment B raw5140step0 raw5140step0Labels := by
      have hz : ∀ j, raw5140 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5140step0 = (fun i j => raw5140 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5140step0 raw5140; decide +kernel
      have hl : raw5140step0Labels = raw5140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5140 raw5140Labels permutation434 hz
    mixedMoment B raw5140step0 raw5140step0Labels = mixedMoment B raw5140step1 raw5140step1Labels := by
      have hz : ∀ j, raw5140step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5140step1 = (fun i j => raw5140step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5140step1 raw5140step0; decide +kernel
      have hl : raw5140step1Labels = raw5140step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5140step0 raw5140step0Labels permutation80 hz
    mixedMoment B raw5140step1 raw5140step1Labels = mixedMoment B raw5140step2 raw5140step2Labels := by
      have ha : raw5140step2 = (fun i j => raw5140step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5140step2 raw5140step1; decide +kernel
      have hl : raw5140step2Labels = raw5140step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5140step1 raw5140step1Labels permutation29 permutation7
    mixedMoment B raw5140step2 raw5140step2Labels = mixedMoment B raw5140step3 raw5140step3Labels := by
      have ha : raw5140step3 = raw5140step2 := by apply Matrix.ext; unfold raw5140step3 raw5140step2; decide +kernel
      have hl : raw5140step2Labels = labelEmbedding1 ∘ raw5140step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5140step2 raw5140step2Labels raw5140step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical5145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5145 raw5145Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw5145 raw5145Labels = mixedMoment B raw5145step0 raw5145step0Labels := by
      have hz : ∀ j, raw5145 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5145step0 = (fun i j => raw5145 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5145step0 raw5145; decide +kernel
      have hl : raw5145step0Labels = raw5145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5145 raw5145Labels permutation434 hz
    mixedMoment B raw5145step0 raw5145step0Labels = mixedMoment B raw5145step1 raw5145step1Labels := by
      have hz : ∀ j, raw5145step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5145step1 = (fun i j => raw5145step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5145step1 raw5145step0; decide +kernel
      have hl : raw5145step1Labels = raw5145step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5145step0 raw5145step0Labels permutation56 hz
    mixedMoment B raw5145step1 raw5145step1Labels = mixedMoment B raw5145step2 raw5145step2Labels := by
      have ha : raw5145step2 = (fun i j => raw5145step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5145step2 raw5145step1; decide +kernel
      have hl : raw5145step2Labels = raw5145step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5145step1 raw5145step1Labels permutation29 permutation7
    mixedMoment B raw5145step2 raw5145step2Labels = mixedMoment B raw5145step3 raw5145step3Labels := by
      have ha : raw5145step3 = raw5145step2 := by apply Matrix.ext; unfold raw5145step3 raw5145step2; decide +kernel
      have hl : raw5145step2Labels = labelEmbedding1 ∘ raw5145step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5145step2 raw5145step2Labels raw5145step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical5150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5150 raw5150Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw5150 raw5150Labels = mixedMoment B raw5150step0 raw5150step0Labels := by
      have hz : ∀ j, raw5150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5150step0 = (fun i j => raw5150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5150step0 raw5150; decide +kernel
      have hl : raw5150step0Labels = raw5150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5150 raw5150Labels permutation346 hz
    mixedMoment B raw5150step0 raw5150step0Labels = mixedMoment B raw5150step1 raw5150step1Labels := by
      have hz : ∀ j, raw5150step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5150step1 = (fun i j => raw5150step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5150step1 raw5150step0; decide +kernel
      have hl : raw5150step1Labels = raw5150step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5150step0 raw5150step0Labels permutation56 hz
    mixedMoment B raw5150step1 raw5150step1Labels = mixedMoment B raw5150step2 raw5150step2Labels := by
      have ha : raw5150step2 = (fun i j => raw5150step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5150step2 raw5150step1; decide +kernel
      have hl : raw5150step2Labels = raw5150step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5150step1 raw5150step1Labels permutation29 permutation7
    mixedMoment B raw5150step2 raw5150step2Labels = mixedMoment B raw5150step3 raw5150step3Labels := by
      have ha : raw5150step3 = raw5150step2 := by apply Matrix.ext; unfold raw5150step3 raw5150step2; decide +kernel
      have hl : raw5150step2Labels = labelEmbedding1 ∘ raw5150step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5150step2 raw5150step2Labels raw5150step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical5151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5151 raw5151Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw5151 raw5151Labels = mixedMoment B raw5151step0 raw5151step0Labels := by
      have hz : ∀ j, raw5151 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5151step0 = (fun i j => raw5151 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5151step0 raw5151; decide +kernel
      have hl : raw5151step0Labels = raw5151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5151 raw5151Labels permutation434 hz
    mixedMoment B raw5151step0 raw5151step0Labels = mixedMoment B raw5151step1 raw5151step1Labels := by
      have hz : ∀ j, raw5151step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5151step1 = (fun i j => raw5151step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5151step1 raw5151step0; decide +kernel
      have hl : raw5151step1Labels = raw5151step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5151step0 raw5151step0Labels permutation80 hz
    mixedMoment B raw5151step1 raw5151step1Labels = mixedMoment B raw5151step2 raw5151step2Labels := by
      have hz : ∀ j, raw5151step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5151step2 = (fun i j => raw5151step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5151step2 raw5151step1; decide +kernel
      have hl : raw5151step2Labels = raw5151step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5151step1 raw5151step1Labels permutation14 hz
    mixedMoment B raw5151step2 raw5151step2Labels = mixedMoment B raw5151step3 raw5151step3Labels := by
      have ha : raw5151step3 = (fun i j => raw5151step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5151step3 raw5151step2; decide +kernel
      have hl : raw5151step3Labels = raw5151step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5151step2 raw5151step2Labels permutation7 permutation7
    mixedMoment B raw5151step3 raw5151step3Labels = mixedMoment B raw5151step4 raw5151step4Labels := by
      have ha : raw5151step4 = raw5151step3 := by apply Matrix.ext; unfold raw5151step4 raw5151step3; decide +kernel
      have hl : raw5151step3Labels = labelEmbedding1 ∘ raw5151step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5151step3 raw5151step3Labels raw5151step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2289 node2289Labels := by rfl

theorem canonical5152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5152 raw5152Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw5152 raw5152Labels = mixedMoment B raw5152step0 raw5152step0Labels := by
      have hz : ∀ j, raw5152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5152step0 = (fun i j => raw5152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5152step0 raw5152; decide +kernel
      have hl : raw5152step0Labels = raw5152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5152 raw5152Labels permutation434 hz
    mixedMoment B raw5152step0 raw5152step0Labels = mixedMoment B raw5152step1 raw5152step1Labels := by
      have hz : ∀ j, raw5152step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5152step1 = (fun i j => raw5152step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5152step1 raw5152step0; decide +kernel
      have hl : raw5152step1Labels = raw5152step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5152step0 raw5152step0Labels permutation80 hz
    mixedMoment B raw5152step1 raw5152step1Labels = mixedMoment B raw5152step2 raw5152step2Labels := by
      have ha : raw5152step2 = (fun i j => raw5152step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5152step2 raw5152step1; decide +kernel
      have hl : raw5152step2Labels = raw5152step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5152step1 raw5152step1Labels permutation29 permutation7
    mixedMoment B raw5152step2 raw5152step2Labels = mixedMoment B raw5152step3 raw5152step3Labels := by
      have ha : raw5152step3 = raw5152step2 := by apply Matrix.ext; unfold raw5152step3 raw5152step2; decide +kernel
      have hl : raw5152step2Labels = labelEmbedding1 ∘ raw5152step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5152step2 raw5152step2Labels raw5152step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical5153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5153 raw5153Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw5153 raw5153Labels = mixedMoment B raw5153step0 raw5153step0Labels := by
      have hz : ∀ j, raw5153 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5153step0 = (fun i j => raw5153 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5153step0 raw5153; decide +kernel
      have hl : raw5153step0Labels = raw5153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5153 raw5153Labels permutation434 hz
    mixedMoment B raw5153step0 raw5153step0Labels = mixedMoment B raw5153step1 raw5153step1Labels := by
      have hz : ∀ j, raw5153step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5153step1 = (fun i j => raw5153step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5153step1 raw5153step0; decide +kernel
      have hl : raw5153step1Labels = raw5153step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5153step0 raw5153step0Labels permutation56 hz
    mixedMoment B raw5153step1 raw5153step1Labels = mixedMoment B raw5153step2 raw5153step2Labels := by
      have ha : raw5153step2 = (fun i j => raw5153step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5153step2 raw5153step1; decide +kernel
      have hl : raw5153step2Labels = raw5153step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5153step1 raw5153step1Labels permutation29 permutation7
    mixedMoment B raw5153step2 raw5153step2Labels = mixedMoment B raw5153step3 raw5153step3Labels := by
      have ha : raw5153step3 = raw5153step2 := by apply Matrix.ext; unfold raw5153step3 raw5153step2; decide +kernel
      have hl : raw5153step2Labels = labelEmbedding1 ∘ raw5153step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5153step2 raw5153step2Labels raw5153step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical5154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5154 raw5154Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw5154 raw5154Labels = mixedMoment B raw5154step0 raw5154step0Labels := by
      have hz : ∀ j, raw5154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5154step0 = (fun i j => raw5154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5154step0 raw5154; decide +kernel
      have hl : raw5154step0Labels = raw5154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5154 raw5154Labels permutation346 hz
    mixedMoment B raw5154step0 raw5154step0Labels = mixedMoment B raw5154step1 raw5154step1Labels := by
      have hz : ∀ j, raw5154step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5154step1 = (fun i j => raw5154step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5154step1 raw5154step0; decide +kernel
      have hl : raw5154step1Labels = raw5154step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5154step0 raw5154step0Labels permutation56 hz
    mixedMoment B raw5154step1 raw5154step1Labels = mixedMoment B raw5154step2 raw5154step2Labels := by
      have ha : raw5154step2 = (fun i j => raw5154step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5154step2 raw5154step1; decide +kernel
      have hl : raw5154step2Labels = raw5154step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5154step1 raw5154step1Labels permutation29 permutation7
    mixedMoment B raw5154step2 raw5154step2Labels = mixedMoment B raw5154step3 raw5154step3Labels := by
      have ha : raw5154step3 = raw5154step2 := by apply Matrix.ext; unfold raw5154step3 raw5154step2; decide +kernel
      have hl : raw5154step2Labels = labelEmbedding1 ∘ raw5154step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5154step2 raw5154step2Labels raw5154step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9728 raw9728Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw9728 raw9728Labels = mixedMoment B raw9728step0 raw9728step0Labels := by
      have hz : ∀ j, raw9728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9728step0 = (fun i j => raw9728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9728step0 raw9728; decide +kernel
      have hl : raw9728step0Labels = raw9728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9728 raw9728Labels permutation434 hz
    mixedMoment B raw9728step0 raw9728step0Labels = mixedMoment B raw9728step1 raw9728step1Labels := by
      have hz : ∀ j, raw9728step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9728step1 = (fun i j => raw9728step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9728step1 raw9728step0; decide +kernel
      have hl : raw9728step1Labels = raw9728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9728step0 raw9728step0Labels permutation80 hz
    mixedMoment B raw9728step1 raw9728step1Labels = mixedMoment B raw9728step2 raw9728step2Labels := by
      have ha : raw9728step2 = (fun i j => raw9728step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9728step2 raw9728step1; decide +kernel
      have hl : raw9728step2Labels = raw9728step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9728step1 raw9728step1Labels permutation10 permutation4
    mixedMoment B raw9728step2 raw9728step2Labels = mixedMoment B raw9728step3 raw9728step3Labels := by
      have ha : raw9728step3 = -raw9728step2 := by apply Matrix.ext; change ∀ i j, raw9728step3 i j = -(raw9728step2 i j); unfold raw9728step3 raw9728step2; decide +kernel
      have hl : raw9728step3Labels = raw9728step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2264 node2264Labels := by rfl

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

theorem canonical9968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9968 raw9968Labels = mixedMoment B node2053 node2053Labels := by
  calc
    mixedMoment B raw9968 raw9968Labels = mixedMoment B raw9968step0 raw9968step0Labels := by
      have hz : ∀ j, raw9968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9968step0 = (fun i j => raw9968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9968step0 raw9968; decide +kernel
      have hl : raw9968step0Labels = raw9968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9968 raw9968Labels permutation346 hz
    mixedMoment B raw9968step0 raw9968step0Labels = mixedMoment B raw9968step1 raw9968step1Labels := by
      have ha : raw9968step1 = (fun i j => raw9968step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9968step1 raw9968step0; decide +kernel
      have hl : raw9968step1Labels = raw9968step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9968step0 raw9968step0Labels permutation38 permutation4
    mixedMoment B raw9968step1 raw9968step1Labels = mixedMoment B raw9968step2 raw9968step2Labels := by
      have ha : raw9968step2 = -raw9968step1 := by apply Matrix.ext; change ∀ i j, raw9968step2 i j = -(raw9968step1 i j); unfold raw9968step2 raw9968step1; decide +kernel
      have hl : raw9968step2Labels = raw9968step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2053 node2053Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10190 raw10190Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw10190 raw10190Labels = mixedMoment B raw10190step0 raw10190step0Labels := by
      have hz : ∀ j, raw10190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10190step0 = (fun i j => raw10190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10190step0 raw10190; decide +kernel
      have hl : raw10190step0Labels = raw10190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10190 raw10190Labels permutation346 hz
    mixedMoment B raw10190step0 raw10190step0Labels = mixedMoment B raw10190step1 raw10190step1Labels := by
      have ha : raw10190step1 = (fun i j => raw10190step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10190step1 raw10190step0; decide +kernel
      have hl : raw10190step1Labels = raw10190step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10190step0 raw10190step0Labels permutation40 permutation4
    mixedMoment B raw10190step1 raw10190step1Labels = mixedMoment B raw10190step2 raw10190step2Labels := by
      have ha : raw10190step2 = -raw10190step1 := by apply Matrix.ext; change ∀ i j, raw10190step2 i j = -(raw10190step1 i j); unfold raw10190step2 raw10190step1; decide +kernel
      have hl : raw10190step2Labels = raw10190step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical10191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10191 raw10191Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw10191 raw10191Labels = mixedMoment B raw10191step0 raw10191step0Labels := by
      have hz : ∀ j, raw10191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10191step0 = (fun i j => raw10191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10191step0 raw10191; decide +kernel
      have hl : raw10191step0Labels = raw10191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10191 raw10191Labels permutation346 hz
    mixedMoment B raw10191step0 raw10191step0Labels = mixedMoment B raw10191step1 raw10191step1Labels := by
      have ha : raw10191step1 = (fun i j => raw10191step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10191step1 raw10191step0; decide +kernel
      have hl : raw10191step1Labels = raw10191step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10191step0 raw10191step0Labels permutation40 permutation4
    mixedMoment B raw10191step1 raw10191step1Labels = mixedMoment B raw10191step2 raw10191step2Labels := by
      have ha : raw10191step2 = -raw10191step1 := by apply Matrix.ext; change ∀ i j, raw10191step2 i j = -(raw10191step1 i j); unfold raw10191step2 raw10191step1; decide +kernel
      have hl : raw10191step2Labels = raw10191step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2028 node2028Labels := by rfl

theorem canonical10192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10192 raw10192Labels = mixedMoment B node2019 node2019Labels := by
  calc
    mixedMoment B raw10192 raw10192Labels = mixedMoment B raw10192step0 raw10192step0Labels := by
      have ha : raw10192step0 = (fun i j => raw10192 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10192step0 raw10192; decide +kernel
      have hl : raw10192step0Labels = raw10192Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10192 raw10192Labels permutation212 permutation4
    mixedMoment B raw10192step0 raw10192step0Labels = mixedMoment B raw10192step1 raw10192step1Labels := by
      have ha : raw10192step1 = -raw10192step0 := by apply Matrix.ext; change ∀ i j, raw10192step1 i j = -(raw10192step0 i j); unfold raw10192step1 raw10192step0; decide +kernel
      have hl : raw10192step1Labels = raw10192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2019 node2019Labels := by rfl

theorem canonical10193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10193 raw10193Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw10193 raw10193Labels = mixedMoment B raw10193step0 raw10193step0Labels := by
      have hz : ∀ j, raw10193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10193step0 = (fun i j => raw10193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10193step0 raw10193; decide +kernel
      have hl : raw10193step0Labels = raw10193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10193 raw10193Labels permutation346 hz
    mixedMoment B raw10193step0 raw10193step0Labels = mixedMoment B raw10193step1 raw10193step1Labels := by
      have ha : raw10193step1 = (fun i j => raw10193step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10193step1 raw10193step0; decide +kernel
      have hl : raw10193step1Labels = raw10193step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10193step0 raw10193step0Labels permutation40 permutation4
    mixedMoment B raw10193step1 raw10193step1Labels = mixedMoment B raw10193step2 raw10193step2Labels := by
      have ha : raw10193step2 = -raw10193step1 := by apply Matrix.ext; change ∀ i j, raw10193step2 i j = -(raw10193step1 i j); unfold raw10193step2 raw10193step1; decide +kernel
      have hl : raw10193step2Labels = raw10193step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical10238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10238 raw10238Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw10238 raw10238Labels = mixedMoment B raw10238step0 raw10238step0Labels := by
      have hz : ∀ j, raw10238 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10238step0 = (fun i j => raw10238 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10238step0 raw10238; decide +kernel
      have hl : raw10238step0Labels = raw10238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10238 raw10238Labels permutation434 hz
    mixedMoment B raw10238step0 raw10238step0Labels = mixedMoment B raw10238step1 raw10238step1Labels := by
      have hz : ∀ j, raw10238step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10238step1 = (fun i j => raw10238step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10238step1 raw10238step0; decide +kernel
      have hl : raw10238step1Labels = raw10238step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10238step0 raw10238step0Labels permutation80 hz
    mixedMoment B raw10238step1 raw10238step1Labels = mixedMoment B raw10238step2 raw10238step2Labels := by
      have ha : raw10238step2 = (fun i j => raw10238step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10238step2 raw10238step1; decide +kernel
      have hl : raw10238step2Labels = raw10238step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10238step1 raw10238step1Labels permutation29 permutation7
    mixedMoment B raw10238step2 raw10238step2Labels = mixedMoment B raw10238step3 raw10238step3Labels := by
      have ha : raw10238step3 = raw10238step2 := by apply Matrix.ext; unfold raw10238step3 raw10238step2; decide +kernel
      have hl : raw10238step2Labels = labelEmbedding10 ∘ raw10238step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10238step2 raw10238step2Labels raw10238step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical10239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10239 raw10239Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw10239 raw10239Labels = mixedMoment B raw10239step0 raw10239step0Labels := by
      have hz : ∀ j, raw10239 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10239step0 = (fun i j => raw10239 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10239step0 raw10239; decide +kernel
      have hl : raw10239step0Labels = raw10239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10239 raw10239Labels permutation434 hz
    mixedMoment B raw10239step0 raw10239step0Labels = mixedMoment B raw10239step1 raw10239step1Labels := by
      have hz : ∀ j, raw10239step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10239step1 = (fun i j => raw10239step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10239step1 raw10239step0; decide +kernel
      have hl : raw10239step1Labels = raw10239step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10239step0 raw10239step0Labels permutation56 hz
    mixedMoment B raw10239step1 raw10239step1Labels = mixedMoment B raw10239step2 raw10239step2Labels := by
      have ha : raw10239step2 = (fun i j => raw10239step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10239step2 raw10239step1; decide +kernel
      have hl : raw10239step2Labels = raw10239step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10239step1 raw10239step1Labels permutation29 permutation7
    mixedMoment B raw10239step2 raw10239step2Labels = mixedMoment B raw10239step3 raw10239step3Labels := by
      have ha : raw10239step3 = raw10239step2 := by apply Matrix.ext; unfold raw10239step3 raw10239step2; decide +kernel
      have hl : raw10239step2Labels = labelEmbedding10 ∘ raw10239step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10239step2 raw10239step2Labels raw10239step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10240 raw10240Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw10240 raw10240Labels = mixedMoment B raw10240step0 raw10240step0Labels := by
      have hz : ∀ j, raw10240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10240step0 = (fun i j => raw10240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10240step0 raw10240; decide +kernel
      have hl : raw10240step0Labels = raw10240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10240 raw10240Labels permutation346 hz
    mixedMoment B raw10240step0 raw10240step0Labels = mixedMoment B raw10240step1 raw10240step1Labels := by
      have hz : ∀ j, raw10240step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10240step1 = (fun i j => raw10240step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10240step1 raw10240step0; decide +kernel
      have hl : raw10240step1Labels = raw10240step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10240step0 raw10240step0Labels permutation56 hz
    mixedMoment B raw10240step1 raw10240step1Labels = mixedMoment B raw10240step2 raw10240step2Labels := by
      have ha : raw10240step2 = (fun i j => raw10240step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10240step2 raw10240step1; decide +kernel
      have hl : raw10240step2Labels = raw10240step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10240step1 raw10240step1Labels permutation29 permutation7
    mixedMoment B raw10240step2 raw10240step2Labels = mixedMoment B raw10240step3 raw10240step3Labels := by
      have ha : raw10240step3 = raw10240step2 := by apply Matrix.ext; unfold raw10240step3 raw10240step2; decide +kernel
      have hl : raw10240step2Labels = labelEmbedding10 ∘ raw10240step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10240step2 raw10240step2Labels raw10240step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical10241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10241 raw10241Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw10241 raw10241Labels = mixedMoment B raw10241step0 raw10241step0Labels := by
      have hz : ∀ j, raw10241 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10241step0 = (fun i j => raw10241 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10241step0 raw10241; decide +kernel
      have hl : raw10241step0Labels = raw10241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10241 raw10241Labels permutation434 hz
    mixedMoment B raw10241step0 raw10241step0Labels = mixedMoment B raw10241step1 raw10241step1Labels := by
      have hz : ∀ j, raw10241step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10241step1 = (fun i j => raw10241step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10241step1 raw10241step0; decide +kernel
      have hl : raw10241step1Labels = raw10241step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10241step0 raw10241step0Labels permutation80 hz
    mixedMoment B raw10241step1 raw10241step1Labels = mixedMoment B raw10241step2 raw10241step2Labels := by
      have hz : ∀ j, raw10241step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10241step2 = (fun i j => raw10241step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10241step2 raw10241step1; decide +kernel
      have hl : raw10241step2Labels = raw10241step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10241step1 raw10241step1Labels permutation14 hz
    mixedMoment B raw10241step2 raw10241step2Labels = mixedMoment B raw10241step3 raw10241step3Labels := by
      have ha : raw10241step3 = (fun i j => raw10241step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10241step3 raw10241step2; decide +kernel
      have hl : raw10241step3Labels = raw10241step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10241step2 raw10241step2Labels permutation7 permutation6
    mixedMoment B raw10241step3 raw10241step3Labels = mixedMoment B raw10241step4 raw10241step4Labels := by
      have ha : raw10241step4 = raw10241step3 := by apply Matrix.ext; unfold raw10241step4 raw10241step3; decide +kernel
      have hl : raw10241step3Labels = labelEmbedding9 ∘ raw10241step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10241step3 raw10241step3Labels raw10241step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

theorem canonical10242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10242 raw10242Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw10242 raw10242Labels = mixedMoment B raw10242step0 raw10242step0Labels := by
      have hz : ∀ j, raw10242 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10242step0 = (fun i j => raw10242 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10242step0 raw10242; decide +kernel
      have hl : raw10242step0Labels = raw10242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10242 raw10242Labels permutation434 hz
    mixedMoment B raw10242step0 raw10242step0Labels = mixedMoment B raw10242step1 raw10242step1Labels := by
      have hz : ∀ j, raw10242step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10242step1 = (fun i j => raw10242step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10242step1 raw10242step0; decide +kernel
      have hl : raw10242step1Labels = raw10242step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10242step0 raw10242step0Labels permutation80 hz
    mixedMoment B raw10242step1 raw10242step1Labels = mixedMoment B raw10242step2 raw10242step2Labels := by
      have ha : raw10242step2 = (fun i j => raw10242step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10242step2 raw10242step1; decide +kernel
      have hl : raw10242step2Labels = raw10242step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10242step1 raw10242step1Labels permutation10 permutation2
    _ = mixedMoment B node4617 node4617Labels := by rfl

theorem canonical10243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10243 raw10243Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw10243 raw10243Labels = mixedMoment B raw10243step0 raw10243step0Labels := by
      have hz : ∀ j, raw10243 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10243step0 = (fun i j => raw10243 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10243step0 raw10243; decide +kernel
      have hl : raw10243step0Labels = raw10243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10243 raw10243Labels permutation434 hz
    mixedMoment B raw10243step0 raw10243step0Labels = mixedMoment B raw10243step1 raw10243step1Labels := by
      have ha : raw10243step1 = (fun i j => raw10243step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10243step1 raw10243step0; decide +kernel
      have hl : raw10243step1Labels = raw10243step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10243step0 raw10243step0Labels permutation40 permutation2
    _ = mixedMoment B node5161 node5161Labels := by rfl

theorem canonical10244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10244 raw10244Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw10244 raw10244Labels = mixedMoment B raw10244step0 raw10244step0Labels := by
      have hz : ∀ j, raw10244 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10244step0 = (fun i j => raw10244 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10244step0 raw10244; decide +kernel
      have hl : raw10244step0Labels = raw10244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10244 raw10244Labels permutation346 hz
    mixedMoment B raw10244step0 raw10244step0Labels = mixedMoment B raw10244step1 raw10244step1Labels := by
      have ha : raw10244step1 = (fun i j => raw10244step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10244step1 raw10244step0; decide +kernel
      have hl : raw10244step1Labels = raw10244step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10244step0 raw10244step0Labels permutation40 permutation2
    _ = mixedMoment B node5161 node5161Labels := by rfl

theorem canonical10245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10245 raw10245Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw10245 raw10245Labels = mixedMoment B raw10245step0 raw10245step0Labels := by
      have hz : ∀ j, raw10245 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10245step0 = (fun i j => raw10245 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10245step0 raw10245; decide +kernel
      have hl : raw10245step0Labels = raw10245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10245 raw10245Labels permutation434 hz
    mixedMoment B raw10245step0 raw10245step0Labels = mixedMoment B raw10245step1 raw10245step1Labels := by
      have hz : ∀ j, raw10245step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10245step1 = (fun i j => raw10245step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10245step1 raw10245step0; decide +kernel
      have hl : raw10245step1Labels = raw10245step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10245step0 raw10245step0Labels permutation80 hz
    mixedMoment B raw10245step1 raw10245step1Labels = mixedMoment B raw10245step2 raw10245step2Labels := by
      have ha : raw10245step2 = (fun i j => raw10245step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10245step2 raw10245step1; decide +kernel
      have hl : raw10245step2Labels = raw10245step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10245step1 raw10245step1Labels permutation29 permutation6
    mixedMoment B raw10245step2 raw10245step2Labels = mixedMoment B raw10245step3 raw10245step3Labels := by
      have ha : raw10245step3 = raw10245step2 := by apply Matrix.ext; unfold raw10245step3 raw10245step2; decide +kernel
      have hl : raw10245step2Labels = labelEmbedding9 ∘ raw10245step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10245step2 raw10245step2Labels raw10245step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

theorem canonical10246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10246 raw10246Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw10246 raw10246Labels = mixedMoment B raw10246step0 raw10246step0Labels := by
      have hz : ∀ j, raw10246 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10246step0 = (fun i j => raw10246 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10246step0 raw10246; decide +kernel
      have hl : raw10246step0Labels = raw10246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10246 raw10246Labels permutation434 hz
    mixedMoment B raw10246step0 raw10246step0Labels = mixedMoment B raw10246step1 raw10246step1Labels := by
      have hz : ∀ j, raw10246step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10246step1 = (fun i j => raw10246step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10246step1 raw10246step0; decide +kernel
      have hl : raw10246step1Labels = raw10246step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10246step0 raw10246step0Labels permutation56 hz
    mixedMoment B raw10246step1 raw10246step1Labels = mixedMoment B raw10246step2 raw10246step2Labels := by
      have ha : raw10246step2 = (fun i j => raw10246step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10246step2 raw10246step1; decide +kernel
      have hl : raw10246step2Labels = raw10246step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10246step1 raw10246step1Labels permutation10 permutation2
    _ = mixedMoment B node4617 node4617Labels := by rfl

theorem canonical10247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10247 raw10247Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw10247 raw10247Labels = mixedMoment B raw10247step0 raw10247step0Labels := by
      have hz : ∀ j, raw10247 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10247step0 = (fun i j => raw10247 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10247step0 raw10247; decide +kernel
      have hl : raw10247step0Labels = raw10247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10247 raw10247Labels permutation434 hz
    mixedMoment B raw10247step0 raw10247step0Labels = mixedMoment B raw10247step1 raw10247step1Labels := by
      have ha : raw10247step1 = (fun i j => raw10247step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10247step1 raw10247step0; decide +kernel
      have hl : raw10247step1Labels = raw10247step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10247step0 raw10247step0Labels permutation34 permutation2
    _ = mixedMoment B node5161 node5161Labels := by rfl

theorem canonical10248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10248 raw10248Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw10248 raw10248Labels = mixedMoment B raw10248step0 raw10248step0Labels := by
      have hz : ∀ j, raw10248 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10248step0 = (fun i j => raw10248 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10248step0 raw10248; decide +kernel
      have hl : raw10248step0Labels = raw10248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10248 raw10248Labels permutation265 hz
    mixedMoment B raw10248step0 raw10248step0Labels = mixedMoment B raw10248step1 raw10248step1Labels := by
      have ha : raw10248step1 = (fun i j => raw10248step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10248step1 raw10248step0; decide +kernel
      have hl : raw10248step1Labels = raw10248step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10248step0 raw10248step0Labels permutation40 permutation2
    _ = mixedMoment B node5161 node5161Labels := by rfl

theorem canonical10249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10249 raw10249Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw10249 raw10249Labels = mixedMoment B raw10249step0 raw10249step0Labels := by
      have hz : ∀ j, raw10249 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10249step0 = (fun i j => raw10249 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10249step0 raw10249; decide +kernel
      have hl : raw10249step0Labels = raw10249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10249 raw10249Labels permutation434 hz
    mixedMoment B raw10249step0 raw10249step0Labels = mixedMoment B raw10249step1 raw10249step1Labels := by
      have hz : ∀ j, raw10249step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10249step1 = (fun i j => raw10249step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10249step1 raw10249step0; decide +kernel
      have hl : raw10249step1Labels = raw10249step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10249step0 raw10249step0Labels permutation56 hz
    mixedMoment B raw10249step1 raw10249step1Labels = mixedMoment B raw10249step2 raw10249step2Labels := by
      have ha : raw10249step2 = (fun i j => raw10249step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10249step2 raw10249step1; decide +kernel
      have hl : raw10249step2Labels = raw10249step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10249step1 raw10249step1Labels permutation29 permutation6
    mixedMoment B raw10249step2 raw10249step2Labels = mixedMoment B raw10249step3 raw10249step3Labels := by
      have ha : raw10249step3 = raw10249step2 := by apply Matrix.ext; unfold raw10249step3 raw10249step2; decide +kernel
      have hl : raw10249step2Labels = labelEmbedding9 ∘ raw10249step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10249step2 raw10249step2Labels raw10249step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

theorem canonical10250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10250 raw10250Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw10250 raw10250Labels = mixedMoment B raw10250step0 raw10250step0Labels := by
      have hz : ∀ j, raw10250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10250step0 = (fun i j => raw10250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10250step0 raw10250; decide +kernel
      have hl : raw10250step0Labels = raw10250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10250 raw10250Labels permutation346 hz
    mixedMoment B raw10250step0 raw10250step0Labels = mixedMoment B raw10250step1 raw10250step1Labels := by
      have hz : ∀ j, raw10250step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10250step1 = (fun i j => raw10250step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10250step1 raw10250step0; decide +kernel
      have hl : raw10250step1Labels = raw10250step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10250step0 raw10250step0Labels permutation56 hz
    mixedMoment B raw10250step1 raw10250step1Labels = mixedMoment B raw10250step2 raw10250step2Labels := by
      have ha : raw10250step2 = (fun i j => raw10250step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10250step2 raw10250step1; decide +kernel
      have hl : raw10250step2Labels = raw10250step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10250step1 raw10250step1Labels permutation10 permutation2
    _ = mixedMoment B node4617 node4617Labels := by rfl

theorem canonical10251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10251 raw10251Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw10251 raw10251Labels = mixedMoment B raw10251step0 raw10251step0Labels := by
      have hz : ∀ j, raw10251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10251step0 = (fun i j => raw10251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10251step0 raw10251; decide +kernel
      have hl : raw10251step0Labels = raw10251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10251 raw10251Labels permutation346 hz
    mixedMoment B raw10251step0 raw10251step0Labels = mixedMoment B raw10251step1 raw10251step1Labels := by
      have ha : raw10251step1 = (fun i j => raw10251step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10251step1 raw10251step0; decide +kernel
      have hl : raw10251step1Labels = raw10251step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10251step0 raw10251step0Labels permutation34 permutation2
    _ = mixedMoment B node5161 node5161Labels := by rfl

theorem canonical10252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10252 raw10252Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw10252 raw10252Labels = mixedMoment B raw10252step0 raw10252step0Labels := by
      have hz : ∀ j, raw10252 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10252step0 = (fun i j => raw10252 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10252step0 raw10252; decide +kernel
      have hl : raw10252step0Labels = raw10252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10252 raw10252Labels permutation265 hz
    mixedMoment B raw10252step0 raw10252step0Labels = mixedMoment B raw10252step1 raw10252step1Labels := by
      have ha : raw10252step1 = (fun i j => raw10252step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10252step1 raw10252step0; decide +kernel
      have hl : raw10252step1Labels = raw10252step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10252step0 raw10252step0Labels permutation34 permutation2
    _ = mixedMoment B node5161 node5161Labels := by rfl

theorem canonical10253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10253 raw10253Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw10253 raw10253Labels = mixedMoment B raw10253step0 raw10253step0Labels := by
      have hz : ∀ j, raw10253 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10253step0 = (fun i j => raw10253 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10253step0 raw10253; decide +kernel
      have hl : raw10253step0Labels = raw10253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10253 raw10253Labels permutation346 hz
    mixedMoment B raw10253step0 raw10253step0Labels = mixedMoment B raw10253step1 raw10253step1Labels := by
      have hz : ∀ j, raw10253step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10253step1 = (fun i j => raw10253step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10253step1 raw10253step0; decide +kernel
      have hl : raw10253step1Labels = raw10253step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10253step0 raw10253step0Labels permutation56 hz
    mixedMoment B raw10253step1 raw10253step1Labels = mixedMoment B raw10253step2 raw10253step2Labels := by
      have ha : raw10253step2 = (fun i j => raw10253step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10253step2 raw10253step1; decide +kernel
      have hl : raw10253step2Labels = raw10253step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10253step1 raw10253step1Labels permutation29 permutation6
    mixedMoment B raw10253step2 raw10253step2Labels = mixedMoment B raw10253step3 raw10253step3Labels := by
      have ha : raw10253step3 = raw10253step2 := by apply Matrix.ext; unfold raw10253step3 raw10253step2; decide +kernel
      have hl : raw10253step2Labels = labelEmbedding9 ∘ raw10253step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10253step2 raw10253step2Labels raw10253step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

theorem canonical10254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10254 raw10254Labels = mixedMoment B node4626 node4626Labels := by
  calc
    mixedMoment B raw10254 raw10254Labels = mixedMoment B raw10254step0 raw10254step0Labels := by
      have hz : ∀ j, raw10254 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10254step0 = (fun i j => raw10254 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10254step0 raw10254; decide +kernel
      have hl : raw10254step0Labels = raw10254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10254 raw10254Labels permutation434 hz
    mixedMoment B raw10254step0 raw10254step0Labels = mixedMoment B raw10254step1 raw10254step1Labels := by
      have hz : ∀ j, raw10254step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10254step1 = (fun i j => raw10254step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10254step1 raw10254step0; decide +kernel
      have hl : raw10254step1Labels = raw10254step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10254step0 raw10254step0Labels permutation80 hz
    mixedMoment B raw10254step1 raw10254step1Labels = mixedMoment B raw10254step2 raw10254step2Labels := by
      have hz : ∀ j, raw10254step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10254step2 = (fun i j => raw10254step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10254step2 raw10254step1; decide +kernel
      have hl : raw10254step2Labels = raw10254step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10254step1 raw10254step1Labels permutation14 hz
    _ = mixedMoment B node4626 node4626Labels := by rfl

theorem canonical10255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10255 raw10255Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw10255 raw10255Labels = mixedMoment B raw10255step0 raw10255step0Labels := by
      have hz : ∀ j, raw10255 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10255step0 = (fun i j => raw10255 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10255step0 raw10255; decide +kernel
      have hl : raw10255step0Labels = raw10255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10255 raw10255Labels permutation434 hz
    mixedMoment B raw10255step0 raw10255step0Labels = mixedMoment B raw10255step1 raw10255step1Labels := by
      have hz : ∀ j, raw10255step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10255step1 = (fun i j => raw10255step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10255step1 raw10255step0; decide +kernel
      have hl : raw10255step1Labels = raw10255step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10255step0 raw10255step0Labels permutation80 hz
    _ = mixedMoment B node5175 node5175Labels := by rfl

theorem canonical10256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10256 raw10256Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw10256 raw10256Labels = mixedMoment B raw10256step0 raw10256step0Labels := by
      have hz : ∀ j, raw10256 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10256step0 = (fun i j => raw10256 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10256step0 raw10256; decide +kernel
      have hl : raw10256step0Labels = raw10256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10256 raw10256Labels permutation434 hz
    mixedMoment B raw10256step0 raw10256step0Labels = mixedMoment B raw10256step1 raw10256step1Labels := by
      have hz : ∀ j, raw10256step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10256step1 = (fun i j => raw10256step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10256step1 raw10256step0; decide +kernel
      have hl : raw10256step1Labels = raw10256step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10256step0 raw10256step0Labels permutation56 hz
    _ = mixedMoment B node5175 node5175Labels := by rfl

theorem canonical10257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10257 raw10257Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw10257 raw10257Labels = mixedMoment B raw10257step0 raw10257step0Labels := by
      have hz : ∀ j, raw10257 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10257step0 = (fun i j => raw10257 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10257step0 raw10257; decide +kernel
      have hl : raw10257step0Labels = raw10257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10257 raw10257Labels permutation346 hz
    mixedMoment B raw10257step0 raw10257step0Labels = mixedMoment B raw10257step1 raw10257step1Labels := by
      have hz : ∀ j, raw10257step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10257step1 = (fun i j => raw10257step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10257step1 raw10257step0; decide +kernel
      have hl : raw10257step1Labels = raw10257step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10257step0 raw10257step0Labels permutation56 hz
    _ = mixedMoment B node5175 node5175Labels := by rfl

theorem canonical10258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10258 raw10258Labels = mixedMoment B node5311 node5311Labels := by
  calc
    mixedMoment B raw10258 raw10258Labels = mixedMoment B raw10258step0 raw10258step0Labels := by
      have hz : ∀ j, raw10258 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10258step0 = (fun i j => raw10258 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10258step0 raw10258; decide +kernel
      have hl : raw10258step0Labels = raw10258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10258 raw10258Labels permutation434 hz
    mixedMoment B raw10258step0 raw10258step0Labels = mixedMoment B raw10258step1 raw10258step1Labels := by
      have hz : ∀ j, raw10258step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10258step1 = (fun i j => raw10258step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10258step1 raw10258step0; decide +kernel
      have hl : raw10258step1Labels = raw10258step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10258step0 raw10258step0Labels permutation80 hz
    mixedMoment B raw10258step1 raw10258step1Labels = mixedMoment B raw10258step2 raw10258step2Labels := by
      have hz : ∀ j, raw10258step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10258step2 = (fun i j => raw10258step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10258step2 raw10258step1; decide +kernel
      have hl : raw10258step2Labels = raw10258step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10258step1 raw10258step1Labels permutation14 hz
    mixedMoment B raw10258step2 raw10258step2Labels = mixedMoment B raw10258step3 raw10258step3Labels := by
      have ha : raw10258step3 = (fun i j => raw10258step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10258step3 raw10258step2; decide +kernel
      have hl : raw10258step3Labels = raw10258step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10258step2 raw10258step2Labels permutation3 permutation2
    _ = mixedMoment B node5311 node5311Labels := by rfl

theorem canonical10259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10259 raw10259Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw10259 raw10259Labels = mixedMoment B raw10259step0 raw10259step0Labels := by
      have hz : ∀ j, raw10259 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10259step0 = (fun i j => raw10259 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10259step0 raw10259; decide +kernel
      have hl : raw10259step0Labels = raw10259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10259 raw10259Labels permutation434 hz
    mixedMoment B raw10259step0 raw10259step0Labels = mixedMoment B raw10259step1 raw10259step1Labels := by
      have hz : ∀ j, raw10259step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10259step1 = (fun i j => raw10259step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10259step1 raw10259step0; decide +kernel
      have hl : raw10259step1Labels = raw10259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10259step0 raw10259step0Labels permutation80 hz
    mixedMoment B raw10259step1 raw10259step1Labels = mixedMoment B raw10259step2 raw10259step2Labels := by
      have hz : ∀ j, raw10259step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10259step2 = (fun i j => raw10259step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10259step2 raw10259step1; decide +kernel
      have hl : raw10259step2Labels = raw10259step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10259step1 raw10259step1Labels permutation14 hz
    mixedMoment B raw10259step2 raw10259step2Labels = mixedMoment B raw10259step3 raw10259step3Labels := by
      have ha : raw10259step3 = (fun i j => raw10259step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10259step3 raw10259step2; decide +kernel
      have hl : raw10259step3Labels = raw10259step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10259step2 raw10259step2Labels permutation7 permutation2
    mixedMoment B raw10259step3 raw10259step3Labels = mixedMoment B raw10259step4 raw10259step4Labels := by
      have ha : raw10259step4 = -raw10259step3 := by apply Matrix.ext; change ∀ i j, raw10259step4 i j = -(raw10259step3 i j); unfold raw10259step4 raw10259step3; decide +kernel
      have hl : raw10259step4Labels = raw10259step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4897 node4897Labels := by rfl

theorem canonical10290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10290 raw10290Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw10290 raw10290Labels = mixedMoment B raw10290step0 raw10290step0Labels := by
      have hz : ∀ j, raw10290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10290step0 = (fun i j => raw10290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10290step0 raw10290; decide +kernel
      have hl : raw10290step0Labels = raw10290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10290 raw10290Labels permutation434 hz
    mixedMoment B raw10290step0 raw10290step0Labels = mixedMoment B raw10290step1 raw10290step1Labels := by
      have hz : ∀ j, raw10290step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10290step1 = (fun i j => raw10290step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10290step1 raw10290step0; decide +kernel
      have hl : raw10290step1Labels = raw10290step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10290step0 raw10290step0Labels permutation80 hz
    mixedMoment B raw10290step1 raw10290step1Labels = mixedMoment B raw10290step2 raw10290step2Labels := by
      have ha : raw10290step2 = (fun i j => raw10290step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10290step2 raw10290step1; decide +kernel
      have hl : raw10290step2Labels = raw10290step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10290step1 raw10290step1Labels permutation29 permutation7
    mixedMoment B raw10290step2 raw10290step2Labels = mixedMoment B raw10290step3 raw10290step3Labels := by
      have ha : raw10290step3 = raw10290step2 := by apply Matrix.ext; unfold raw10290step3 raw10290step2; decide +kernel
      have hl : raw10290step2Labels = labelEmbedding1 ∘ raw10290step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10290step2 raw10290step2Labels raw10290step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical10291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10291 raw10291Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw10291 raw10291Labels = mixedMoment B raw10291step0 raw10291step0Labels := by
      have hz : ∀ j, raw10291 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10291step0 = (fun i j => raw10291 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10291step0 raw10291; decide +kernel
      have hl : raw10291step0Labels = raw10291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10291 raw10291Labels permutation434 hz
    mixedMoment B raw10291step0 raw10291step0Labels = mixedMoment B raw10291step1 raw10291step1Labels := by
      have hz : ∀ j, raw10291step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10291step1 = (fun i j => raw10291step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10291step1 raw10291step0; decide +kernel
      have hl : raw10291step1Labels = raw10291step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10291step0 raw10291step0Labels permutation56 hz
    mixedMoment B raw10291step1 raw10291step1Labels = mixedMoment B raw10291step2 raw10291step2Labels := by
      have ha : raw10291step2 = (fun i j => raw10291step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10291step2 raw10291step1; decide +kernel
      have hl : raw10291step2Labels = raw10291step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10291step1 raw10291step1Labels permutation29 permutation7
    mixedMoment B raw10291step2 raw10291step2Labels = mixedMoment B raw10291step3 raw10291step3Labels := by
      have ha : raw10291step3 = raw10291step2 := by apply Matrix.ext; unfold raw10291step3 raw10291step2; decide +kernel
      have hl : raw10291step2Labels = labelEmbedding1 ∘ raw10291step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10291step2 raw10291step2Labels raw10291step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical10292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10292 raw10292Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw10292 raw10292Labels = mixedMoment B raw10292step0 raw10292step0Labels := by
      have hz : ∀ j, raw10292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10292step0 = (fun i j => raw10292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10292step0 raw10292; decide +kernel
      have hl : raw10292step0Labels = raw10292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10292 raw10292Labels permutation346 hz
    mixedMoment B raw10292step0 raw10292step0Labels = mixedMoment B raw10292step1 raw10292step1Labels := by
      have hz : ∀ j, raw10292step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10292step1 = (fun i j => raw10292step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10292step1 raw10292step0; decide +kernel
      have hl : raw10292step1Labels = raw10292step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10292step0 raw10292step0Labels permutation56 hz
    mixedMoment B raw10292step1 raw10292step1Labels = mixedMoment B raw10292step2 raw10292step2Labels := by
      have ha : raw10292step2 = (fun i j => raw10292step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10292step2 raw10292step1; decide +kernel
      have hl : raw10292step2Labels = raw10292step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10292step1 raw10292step1Labels permutation29 permutation7
    mixedMoment B raw10292step2 raw10292step2Labels = mixedMoment B raw10292step3 raw10292step3Labels := by
      have ha : raw10292step3 = raw10292step2 := by apply Matrix.ext; unfold raw10292step3 raw10292step2; decide +kernel
      have hl : raw10292step2Labels = labelEmbedding1 ∘ raw10292step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10292step2 raw10292step2Labels raw10292step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical10293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10293 raw10293Labels = mixedMoment B node3121 node3121Labels := by
  calc
    mixedMoment B raw10293 raw10293Labels = mixedMoment B raw10293step0 raw10293step0Labels := by
      have hz : ∀ j, raw10293 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10293step0 = (fun i j => raw10293 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10293step0 raw10293; decide +kernel
      have hl : raw10293step0Labels = raw10293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10293 raw10293Labels permutation434 hz
    mixedMoment B raw10293step0 raw10293step0Labels = mixedMoment B raw10293step1 raw10293step1Labels := by
      have hz : ∀ j, raw10293step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10293step1 = (fun i j => raw10293step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10293step1 raw10293step0; decide +kernel
      have hl : raw10293step1Labels = raw10293step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10293step0 raw10293step0Labels permutation80 hz
    mixedMoment B raw10293step1 raw10293step1Labels = mixedMoment B raw10293step2 raw10293step2Labels := by
      have hz : ∀ j, raw10293step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10293step2 = (fun i j => raw10293step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10293step2 raw10293step1; decide +kernel
      have hl : raw10293step2Labels = raw10293step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10293step1 raw10293step1Labels permutation14 hz
    mixedMoment B raw10293step2 raw10293step2Labels = mixedMoment B raw10293step3 raw10293step3Labels := by
      have ha : raw10293step3 = (fun i j => raw10293step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10293step3 raw10293step2; decide +kernel
      have hl : raw10293step3Labels = raw10293step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10293step2 raw10293step2Labels permutation7 permutation7
    mixedMoment B raw10293step3 raw10293step3Labels = mixedMoment B raw10293step4 raw10293step4Labels := by
      have ha : raw10293step4 = raw10293step3 := by apply Matrix.ext; unfold raw10293step4 raw10293step3; decide +kernel
      have hl : raw10293step3Labels = labelEmbedding1 ∘ raw10293step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10293step3 raw10293step3Labels raw10293step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3121 node3121Labels := by rfl

theorem canonical10294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10294 raw10294Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw10294 raw10294Labels = mixedMoment B raw10294step0 raw10294step0Labels := by
      have hz : ∀ j, raw10294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10294step0 = (fun i j => raw10294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10294step0 raw10294; decide +kernel
      have hl : raw10294step0Labels = raw10294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10294 raw10294Labels permutation434 hz
    mixedMoment B raw10294step0 raw10294step0Labels = mixedMoment B raw10294step1 raw10294step1Labels := by
      have hz : ∀ j, raw10294step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10294step1 = (fun i j => raw10294step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10294step1 raw10294step0; decide +kernel
      have hl : raw10294step1Labels = raw10294step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10294step0 raw10294step0Labels permutation80 hz
    mixedMoment B raw10294step1 raw10294step1Labels = mixedMoment B raw10294step2 raw10294step2Labels := by
      have ha : raw10294step2 = (fun i j => raw10294step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10294step2 raw10294step1; decide +kernel
      have hl : raw10294step2Labels = raw10294step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10294step1 raw10294step1Labels permutation29 permutation7
    mixedMoment B raw10294step2 raw10294step2Labels = mixedMoment B raw10294step3 raw10294step3Labels := by
      have ha : raw10294step3 = raw10294step2 := by apply Matrix.ext; unfold raw10294step3 raw10294step2; decide +kernel
      have hl : raw10294step2Labels = labelEmbedding1 ∘ raw10294step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10294step2 raw10294step2Labels raw10294step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

theorem canonical10295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10295 raw10295Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10295 raw10295Labels = mixedMoment B raw10295step0 raw10295step0Labels := by
      have hz : ∀ j, raw10295 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10295step0 = (fun i j => raw10295 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10295step0 raw10295; decide +kernel
      have hl : raw10295step0Labels = raw10295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10295 raw10295Labels permutation434 hz
    mixedMoment B raw10295step0 raw10295step0Labels = mixedMoment B raw10295step1 raw10295step1Labels := by
      have ha : raw10295step1 = (fun i j => raw10295step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10295step1 raw10295step0; decide +kernel
      have hl : raw10295step1Labels = raw10295step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10295step0 raw10295step0Labels permutation137 permutation7
    mixedMoment B raw10295step1 raw10295step1Labels = mixedMoment B raw10295step2 raw10295step2Labels := by
      have ha : raw10295step2 = raw10295step1 := by apply Matrix.ext; unfold raw10295step2 raw10295step1; decide +kernel
      have hl : raw10295step1Labels = labelEmbedding1 ∘ raw10295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10295step1 raw10295step1Labels raw10295step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

theorem canonical10296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10296 raw10296Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10296 raw10296Labels = mixedMoment B raw10296step0 raw10296step0Labels := by
      have hz : ∀ j, raw10296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10296step0 = (fun i j => raw10296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10296step0 raw10296; decide +kernel
      have hl : raw10296step0Labels = raw10296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10296 raw10296Labels permutation346 hz
    mixedMoment B raw10296step0 raw10296step0Labels = mixedMoment B raw10296step1 raw10296step1Labels := by
      have ha : raw10296step1 = (fun i j => raw10296step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10296step1 raw10296step0; decide +kernel
      have hl : raw10296step1Labels = raw10296step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10296step0 raw10296step0Labels permutation137 permutation7
    mixedMoment B raw10296step1 raw10296step1Labels = mixedMoment B raw10296step2 raw10296step2Labels := by
      have ha : raw10296step2 = raw10296step1 := by apply Matrix.ext; unfold raw10296step2 raw10296step1; decide +kernel
      have hl : raw10296step1Labels = labelEmbedding1 ∘ raw10296step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10296step1 raw10296step1Labels raw10296step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

theorem canonical10297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10297 raw10297Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw10297 raw10297Labels = mixedMoment B raw10297step0 raw10297step0Labels := by
      have hz : ∀ j, raw10297 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10297step0 = (fun i j => raw10297 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10297step0 raw10297; decide +kernel
      have hl : raw10297step0Labels = raw10297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10297 raw10297Labels permutation434 hz
    mixedMoment B raw10297step0 raw10297step0Labels = mixedMoment B raw10297step1 raw10297step1Labels := by
      have hz : ∀ j, raw10297step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10297step1 = (fun i j => raw10297step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10297step1 raw10297step0; decide +kernel
      have hl : raw10297step1Labels = raw10297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10297step0 raw10297step0Labels permutation80 hz
    mixedMoment B raw10297step1 raw10297step1Labels = mixedMoment B raw10297step2 raw10297step2Labels := by
      have ha : raw10297step2 = (fun i j => raw10297step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10297step2 raw10297step1; decide +kernel
      have hl : raw10297step2Labels = raw10297step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10297step1 raw10297step1Labels permutation29 permutation7
    mixedMoment B raw10297step2 raw10297step2Labels = mixedMoment B raw10297step3 raw10297step3Labels := by
      have ha : raw10297step3 = raw10297step2 := by apply Matrix.ext; unfold raw10297step3 raw10297step2; decide +kernel
      have hl : raw10297step2Labels = labelEmbedding1 ∘ raw10297step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10297step2 raw10297step2Labels raw10297step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

theorem canonical10298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10298 raw10298Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw10298 raw10298Labels = mixedMoment B raw10298step0 raw10298step0Labels := by
      have hz : ∀ j, raw10298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10298step0 = (fun i j => raw10298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10298step0 raw10298; decide +kernel
      have hl : raw10298step0Labels = raw10298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10298 raw10298Labels permutation434 hz
    mixedMoment B raw10298step0 raw10298step0Labels = mixedMoment B raw10298step1 raw10298step1Labels := by
      have hz : ∀ j, raw10298step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10298step1 = (fun i j => raw10298step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10298step1 raw10298step0; decide +kernel
      have hl : raw10298step1Labels = raw10298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10298step0 raw10298step0Labels permutation56 hz
    mixedMoment B raw10298step1 raw10298step1Labels = mixedMoment B raw10298step2 raw10298step2Labels := by
      have ha : raw10298step2 = (fun i j => raw10298step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10298step2 raw10298step1; decide +kernel
      have hl : raw10298step2Labels = raw10298step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10298step1 raw10298step1Labels permutation29 permutation7
    mixedMoment B raw10298step2 raw10298step2Labels = mixedMoment B raw10298step3 raw10298step3Labels := by
      have ha : raw10298step3 = raw10298step2 := by apply Matrix.ext; unfold raw10298step3 raw10298step2; decide +kernel
      have hl : raw10298step2Labels = labelEmbedding1 ∘ raw10298step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10298step2 raw10298step2Labels raw10298step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

theorem canonical10299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10299 raw10299Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10299 raw10299Labels = mixedMoment B raw10299step0 raw10299step0Labels := by
      have hz : ∀ j, raw10299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10299step0 = (fun i j => raw10299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10299step0 raw10299; decide +kernel
      have hl : raw10299step0Labels = raw10299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10299 raw10299Labels permutation434 hz
    mixedMoment B raw10299step0 raw10299step0Labels = mixedMoment B raw10299step1 raw10299step1Labels := by
      have ha : raw10299step1 = (fun i j => raw10299step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10299step1 raw10299step0; decide +kernel
      have hl : raw10299step1Labels = raw10299step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10299step0 raw10299step0Labels permutation143 permutation7
    mixedMoment B raw10299step1 raw10299step1Labels = mixedMoment B raw10299step2 raw10299step2Labels := by
      have ha : raw10299step2 = raw10299step1 := by apply Matrix.ext; unfold raw10299step2 raw10299step1; decide +kernel
      have hl : raw10299step1Labels = labelEmbedding1 ∘ raw10299step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10299step1 raw10299step1Labels raw10299step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

theorem canonical10300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10300 raw10300Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10300 raw10300Labels = mixedMoment B raw10300step0 raw10300step0Labels := by
      have hz : ∀ j, raw10300 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10300step0 = (fun i j => raw10300 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10300step0 raw10300; decide +kernel
      have hl : raw10300step0Labels = raw10300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10300 raw10300Labels permutation265 hz
    mixedMoment B raw10300step0 raw10300step0Labels = mixedMoment B raw10300step1 raw10300step1Labels := by
      have ha : raw10300step1 = (fun i j => raw10300step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10300step1 raw10300step0; decide +kernel
      have hl : raw10300step1Labels = raw10300step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10300step0 raw10300step0Labels permutation137 permutation7
    mixedMoment B raw10300step1 raw10300step1Labels = mixedMoment B raw10300step2 raw10300step2Labels := by
      have ha : raw10300step2 = raw10300step1 := by apply Matrix.ext; unfold raw10300step2 raw10300step1; decide +kernel
      have hl : raw10300step1Labels = labelEmbedding1 ∘ raw10300step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10300step1 raw10300step1Labels raw10300step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

theorem canonical10301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10301 raw10301Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw10301 raw10301Labels = mixedMoment B raw10301step0 raw10301step0Labels := by
      have hz : ∀ j, raw10301 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10301step0 = (fun i j => raw10301 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10301step0 raw10301; decide +kernel
      have hl : raw10301step0Labels = raw10301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10301 raw10301Labels permutation434 hz
    mixedMoment B raw10301step0 raw10301step0Labels = mixedMoment B raw10301step1 raw10301step1Labels := by
      have hz : ∀ j, raw10301step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10301step1 = (fun i j => raw10301step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10301step1 raw10301step0; decide +kernel
      have hl : raw10301step1Labels = raw10301step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10301step0 raw10301step0Labels permutation56 hz
    mixedMoment B raw10301step1 raw10301step1Labels = mixedMoment B raw10301step2 raw10301step2Labels := by
      have ha : raw10301step2 = (fun i j => raw10301step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10301step2 raw10301step1; decide +kernel
      have hl : raw10301step2Labels = raw10301step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10301step1 raw10301step1Labels permutation29 permutation7
    mixedMoment B raw10301step2 raw10301step2Labels = mixedMoment B raw10301step3 raw10301step3Labels := by
      have ha : raw10301step3 = raw10301step2 := by apply Matrix.ext; unfold raw10301step3 raw10301step2; decide +kernel
      have hl : raw10301step2Labels = labelEmbedding1 ∘ raw10301step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10301step2 raw10301step2Labels raw10301step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

theorem canonical10302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10302 raw10302Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw10302 raw10302Labels = mixedMoment B raw10302step0 raw10302step0Labels := by
      have hz : ∀ j, raw10302 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10302step0 = (fun i j => raw10302 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10302step0 raw10302; decide +kernel
      have hl : raw10302step0Labels = raw10302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10302 raw10302Labels permutation346 hz
    mixedMoment B raw10302step0 raw10302step0Labels = mixedMoment B raw10302step1 raw10302step1Labels := by
      have hz : ∀ j, raw10302step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10302step1 = (fun i j => raw10302step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10302step1 raw10302step0; decide +kernel
      have hl : raw10302step1Labels = raw10302step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10302step0 raw10302step0Labels permutation56 hz
    mixedMoment B raw10302step1 raw10302step1Labels = mixedMoment B raw10302step2 raw10302step2Labels := by
      have ha : raw10302step2 = (fun i j => raw10302step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10302step2 raw10302step1; decide +kernel
      have hl : raw10302step2Labels = raw10302step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10302step1 raw10302step1Labels permutation29 permutation7
    mixedMoment B raw10302step2 raw10302step2Labels = mixedMoment B raw10302step3 raw10302step3Labels := by
      have ha : raw10302step3 = raw10302step2 := by apply Matrix.ext; unfold raw10302step3 raw10302step2; decide +kernel
      have hl : raw10302step2Labels = labelEmbedding1 ∘ raw10302step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10302step2 raw10302step2Labels raw10302step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

theorem canonical10303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10303 raw10303Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10303 raw10303Labels = mixedMoment B raw10303step0 raw10303step0Labels := by
      have hz : ∀ j, raw10303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10303step0 = (fun i j => raw10303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10303step0 raw10303; decide +kernel
      have hl : raw10303step0Labels = raw10303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10303 raw10303Labels permutation346 hz
    mixedMoment B raw10303step0 raw10303step0Labels = mixedMoment B raw10303step1 raw10303step1Labels := by
      have ha : raw10303step1 = (fun i j => raw10303step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10303step1 raw10303step0; decide +kernel
      have hl : raw10303step1Labels = raw10303step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10303step0 raw10303step0Labels permutation143 permutation7
    mixedMoment B raw10303step1 raw10303step1Labels = mixedMoment B raw10303step2 raw10303step2Labels := by
      have ha : raw10303step2 = raw10303step1 := by apply Matrix.ext; unfold raw10303step2 raw10303step1; decide +kernel
      have hl : raw10303step1Labels = labelEmbedding1 ∘ raw10303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10303step1 raw10303step1Labels raw10303step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

theorem canonical10304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10304 raw10304Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10304 raw10304Labels = mixedMoment B raw10304step0 raw10304step0Labels := by
      have hz : ∀ j, raw10304 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10304step0 = (fun i j => raw10304 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10304step0 raw10304; decide +kernel
      have hl : raw10304step0Labels = raw10304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10304 raw10304Labels permutation265 hz
    mixedMoment B raw10304step0 raw10304step0Labels = mixedMoment B raw10304step1 raw10304step1Labels := by
      have ha : raw10304step1 = (fun i j => raw10304step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10304step1 raw10304step0; decide +kernel
      have hl : raw10304step1Labels = raw10304step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10304step0 raw10304step0Labels permutation143 permutation7
    mixedMoment B raw10304step1 raw10304step1Labels = mixedMoment B raw10304step2 raw10304step2Labels := by
      have ha : raw10304step2 = raw10304step1 := by apply Matrix.ext; unfold raw10304step2 raw10304step1; decide +kernel
      have hl : raw10304step1Labels = labelEmbedding1 ∘ raw10304step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10304step1 raw10304step1Labels raw10304step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

theorem canonical10305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10305 raw10305Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw10305 raw10305Labels = mixedMoment B raw10305step0 raw10305step0Labels := by
      have hz : ∀ j, raw10305 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10305step0 = (fun i j => raw10305 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10305step0 raw10305; decide +kernel
      have hl : raw10305step0Labels = raw10305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10305 raw10305Labels permutation346 hz
    mixedMoment B raw10305step0 raw10305step0Labels = mixedMoment B raw10305step1 raw10305step1Labels := by
      have hz : ∀ j, raw10305step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10305step1 = (fun i j => raw10305step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10305step1 raw10305step0; decide +kernel
      have hl : raw10305step1Labels = raw10305step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10305step0 raw10305step0Labels permutation56 hz
    mixedMoment B raw10305step1 raw10305step1Labels = mixedMoment B raw10305step2 raw10305step2Labels := by
      have ha : raw10305step2 = (fun i j => raw10305step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10305step2 raw10305step1; decide +kernel
      have hl : raw10305step2Labels = raw10305step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10305step1 raw10305step1Labels permutation29 permutation7
    mixedMoment B raw10305step2 raw10305step2Labels = mixedMoment B raw10305step3 raw10305step3Labels := by
      have ha : raw10305step3 = raw10305step2 := by apply Matrix.ext; unfold raw10305step3 raw10305step2; decide +kernel
      have hl : raw10305step2Labels = labelEmbedding1 ∘ raw10305step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10305step2 raw10305step2Labels raw10305step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

theorem canonical10306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10306 raw10306Labels = mixedMoment B node2780 node2780Labels := by
  calc
    mixedMoment B raw10306 raw10306Labels = mixedMoment B raw10306step0 raw10306step0Labels := by
      have hz : ∀ j, raw10306 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10306step0 = (fun i j => raw10306 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10306step0 raw10306; decide +kernel
      have hl : raw10306step0Labels = raw10306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10306 raw10306Labels permutation434 hz
    mixedMoment B raw10306step0 raw10306step0Labels = mixedMoment B raw10306step1 raw10306step1Labels := by
      have hz : ∀ j, raw10306step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10306step1 = (fun i j => raw10306step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10306step1 raw10306step0; decide +kernel
      have hl : raw10306step1Labels = raw10306step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10306step0 raw10306step0Labels permutation80 hz
    mixedMoment B raw10306step1 raw10306step1Labels = mixedMoment B raw10306step2 raw10306step2Labels := by
      have hz : ∀ j, raw10306step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10306step2 = (fun i j => raw10306step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10306step2 raw10306step1; decide +kernel
      have hl : raw10306step2Labels = raw10306step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10306step1 raw10306step1Labels permutation14 hz
    mixedMoment B raw10306step2 raw10306step2Labels = mixedMoment B raw10306step3 raw10306step3Labels := by
      have ha : raw10306step3 = (fun i j => raw10306step2 (permutation5 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10306step3 raw10306step2; decide +kernel
      have hl : raw10306step3Labels = raw10306step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10306step2 raw10306step2Labels permutation5 permutation5
    mixedMoment B raw10306step3 raw10306step3Labels = mixedMoment B raw10306step4 raw10306step4Labels := by
      have ha : raw10306step4 = raw10306step3 := by apply Matrix.ext; unfold raw10306step4 raw10306step3; decide +kernel
      have hl : raw10306step3Labels = labelEmbedding1 ∘ raw10306step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10306step3 raw10306step3Labels raw10306step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2780 node2780Labels := by rfl

theorem canonical10307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10307 raw10307Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw10307 raw10307Labels = mixedMoment B raw10307step0 raw10307step0Labels := by
      have hz : ∀ j, raw10307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10307step0 = (fun i j => raw10307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10307step0 raw10307; decide +kernel
      have hl : raw10307step0Labels = raw10307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10307 raw10307Labels permutation434 hz
    mixedMoment B raw10307step0 raw10307step0Labels = mixedMoment B raw10307step1 raw10307step1Labels := by
      have hz : ∀ j, raw10307step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10307step1 = (fun i j => raw10307step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10307step1 raw10307step0; decide +kernel
      have hl : raw10307step1Labels = raw10307step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10307step0 raw10307step0Labels permutation80 hz
    mixedMoment B raw10307step1 raw10307step1Labels = mixedMoment B raw10307step2 raw10307step2Labels := by
      have ha : raw10307step2 = (fun i j => raw10307step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10307step2 raw10307step1; decide +kernel
      have hl : raw10307step2Labels = raw10307step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10307step1 raw10307step1Labels permutation29 permutation7
    mixedMoment B raw10307step2 raw10307step2Labels = mixedMoment B raw10307step3 raw10307step3Labels := by
      have ha : raw10307step3 = raw10307step2 := by apply Matrix.ext; unfold raw10307step3 raw10307step2; decide +kernel
      have hl : raw10307step2Labels = labelEmbedding1 ∘ raw10307step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10307step2 raw10307step2Labels raw10307step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

theorem canonical10308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10308 raw10308Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw10308 raw10308Labels = mixedMoment B raw10308step0 raw10308step0Labels := by
      have hz : ∀ j, raw10308 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10308step0 = (fun i j => raw10308 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10308step0 raw10308; decide +kernel
      have hl : raw10308step0Labels = raw10308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10308 raw10308Labels permutation434 hz
    mixedMoment B raw10308step0 raw10308step0Labels = mixedMoment B raw10308step1 raw10308step1Labels := by
      have hz : ∀ j, raw10308step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10308step1 = (fun i j => raw10308step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10308step1 raw10308step0; decide +kernel
      have hl : raw10308step1Labels = raw10308step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10308step0 raw10308step0Labels permutation56 hz
    mixedMoment B raw10308step1 raw10308step1Labels = mixedMoment B raw10308step2 raw10308step2Labels := by
      have ha : raw10308step2 = (fun i j => raw10308step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10308step2 raw10308step1; decide +kernel
      have hl : raw10308step2Labels = raw10308step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10308step1 raw10308step1Labels permutation29 permutation7
    mixedMoment B raw10308step2 raw10308step2Labels = mixedMoment B raw10308step3 raw10308step3Labels := by
      have ha : raw10308step3 = raw10308step2 := by apply Matrix.ext; unfold raw10308step3 raw10308step2; decide +kernel
      have hl : raw10308step2Labels = labelEmbedding1 ∘ raw10308step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10308step2 raw10308step2Labels raw10308step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

theorem canonical10309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10309 raw10309Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw10309 raw10309Labels = mixedMoment B raw10309step0 raw10309step0Labels := by
      have hz : ∀ j, raw10309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10309step0 = (fun i j => raw10309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10309step0 raw10309; decide +kernel
      have hl : raw10309step0Labels = raw10309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10309 raw10309Labels permutation346 hz
    mixedMoment B raw10309step0 raw10309step0Labels = mixedMoment B raw10309step1 raw10309step1Labels := by
      have hz : ∀ j, raw10309step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10309step1 = (fun i j => raw10309step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10309step1 raw10309step0; decide +kernel
      have hl : raw10309step1Labels = raw10309step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10309step0 raw10309step0Labels permutation56 hz
    mixedMoment B raw10309step1 raw10309step1Labels = mixedMoment B raw10309step2 raw10309step2Labels := by
      have ha : raw10309step2 = (fun i j => raw10309step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10309step2 raw10309step1; decide +kernel
      have hl : raw10309step2Labels = raw10309step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10309step1 raw10309step1Labels permutation29 permutation7
    mixedMoment B raw10309step2 raw10309step2Labels = mixedMoment B raw10309step3 raw10309step3Labels := by
      have ha : raw10309step3 = raw10309step2 := by apply Matrix.ext; unfold raw10309step3 raw10309step2; decide +kernel
      have hl : raw10309step2Labels = labelEmbedding1 ∘ raw10309step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10309step2 raw10309step2Labels raw10309step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

theorem canonical10310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10310 raw10310Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw10310 raw10310Labels = mixedMoment B raw10310step0 raw10310step0Labels := by
      have hz : ∀ j, raw10310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10310step0 = (fun i j => raw10310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10310step0 raw10310; decide +kernel
      have hl : raw10310step0Labels = raw10310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10310 raw10310Labels permutation434 hz
    mixedMoment B raw10310step0 raw10310step0Labels = mixedMoment B raw10310step1 raw10310step1Labels := by
      have hz : ∀ j, raw10310step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10310step1 = (fun i j => raw10310step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10310step1 raw10310step0; decide +kernel
      have hl : raw10310step1Labels = raw10310step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10310step0 raw10310step0Labels permutation80 hz
    mixedMoment B raw10310step1 raw10310step1Labels = mixedMoment B raw10310step2 raw10310step2Labels := by
      have hz : ∀ j, raw10310step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10310step2 = (fun i j => raw10310step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10310step2 raw10310step1; decide +kernel
      have hl : raw10310step2Labels = raw10310step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10310step1 raw10310step1Labels permutation14 hz
    mixedMoment B raw10310step2 raw10310step2Labels = mixedMoment B raw10310step3 raw10310step3Labels := by
      have ha : raw10310step3 = (fun i j => raw10310step2 (permutation4 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10310step3 raw10310step2; decide +kernel
      have hl : raw10310step3Labels = raw10310step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10310step2 raw10310step2Labels permutation4 permutation5
    mixedMoment B raw10310step3 raw10310step3Labels = mixedMoment B raw10310step4 raw10310step4Labels := by
      have ha : raw10310step4 = raw10310step3 := by apply Matrix.ext; unfold raw10310step4 raw10310step3; decide +kernel
      have hl : raw10310step3Labels = labelEmbedding1 ∘ raw10310step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10310step3 raw10310step3Labels raw10310step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2789 node2789Labels := by rfl

theorem canonical10311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10311 raw10311Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw10311 raw10311Labels = mixedMoment B raw10311step0 raw10311step0Labels := by
      have hz : ∀ j, raw10311 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10311step0 = (fun i j => raw10311 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10311step0 raw10311; decide +kernel
      have hl : raw10311step0Labels = raw10311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10311 raw10311Labels permutation434 hz
    mixedMoment B raw10311step0 raw10311step0Labels = mixedMoment B raw10311step1 raw10311step1Labels := by
      have hz : ∀ j, raw10311step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10311step1 = (fun i j => raw10311step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10311step1 raw10311step0; decide +kernel
      have hl : raw10311step1Labels = raw10311step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10311step0 raw10311step0Labels permutation80 hz
    mixedMoment B raw10311step1 raw10311step1Labels = mixedMoment B raw10311step2 raw10311step2Labels := by
      have hz : ∀ j, raw10311step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10311step2 = (fun i j => raw10311step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10311step2 raw10311step1; decide +kernel
      have hl : raw10311step2Labels = raw10311step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10311step1 raw10311step1Labels permutation14 hz
    mixedMoment B raw10311step2 raw10311step2Labels = mixedMoment B raw10311step3 raw10311step3Labels := by
      have ha : raw10311step3 = (fun i j => raw10311step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10311step3 raw10311step2; decide +kernel
      have hl : raw10311step3Labels = raw10311step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10311step2 raw10311step2Labels permutation7 permutation7
    mixedMoment B raw10311step3 raw10311step3Labels = mixedMoment B raw10311step4 raw10311step4Labels := by
      have ha : raw10311step4 = raw10311step3 := by apply Matrix.ext; unfold raw10311step4 raw10311step3; decide +kernel
      have hl : raw10311step3Labels = labelEmbedding1 ∘ raw10311step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10311step3 raw10311step3Labels raw10311step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2292 node2292Labels := by rfl

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

theorem canonical10434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10434 raw10434Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw10434 raw10434Labels = mixedMoment B raw10434step0 raw10434step0Labels := by
      have hz : ∀ j, raw10434 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10434step0 = (fun i j => raw10434 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10434step0 raw10434; decide +kernel
      have hl : raw10434step0Labels = raw10434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10434 raw10434Labels permutation265 hz
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

theorem canonical10436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10436 raw10436Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw10436 raw10436Labels = mixedMoment B raw10436step0 raw10436step0Labels := by
      have hz : ∀ j, raw10436 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10436step0 = (fun i j => raw10436 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10436step0 raw10436; decide +kernel
      have hl : raw10436step0Labels = raw10436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10436 raw10436Labels permutation346 hz
    mixedMoment B raw10436step0 raw10436step0Labels = mixedMoment B raw10436step1 raw10436step1Labels := by
      have hz : ∀ j, raw10436step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10436step1 = (fun i j => raw10436step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10436step1 raw10436step0; decide +kernel
      have hl : raw10436step1Labels = raw10436step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10436step0 raw10436step0Labels permutation56 hz
    _ = mixedMoment B node3907 node3907Labels := by rfl

theorem canonical10437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10437 raw10437Labels = mixedMoment B node3908 node3908Labels := by
  calc
    mixedMoment B raw10437 raw10437Labels = mixedMoment B raw10437step0 raw10437step0Labels := by
      have hz : ∀ j, raw10437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10437step0 = (fun i j => raw10437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10437step0 raw10437; decide +kernel
      have hl : raw10437step0Labels = raw10437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10437 raw10437Labels permutation346 hz
    mixedMoment B raw10437step0 raw10437step0Labels = mixedMoment B raw10437step1 raw10437step1Labels := by
      have hz : ∀ j, raw10437step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10437step1 = (fun i j => raw10437step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10437step1 raw10437step0; decide +kernel
      have hl : raw10437step1Labels = raw10437step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10437step0 raw10437step0Labels permutation56 hz
    mixedMoment B raw10437step1 raw10437step1Labels = mixedMoment B raw10437step2 raw10437step2Labels := by
      have ha : raw10437step2 = (fun i j => raw10437step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10437step2 raw10437step1; decide +kernel
      have hl : raw10437step2Labels = raw10437step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10437step1 raw10437step1Labels permutation9 permutation2
    _ = mixedMoment B node3908 node3908Labels := by rfl

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

theorem canonical5214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5214 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5214 = injectiveMoment H raw5214step0 := by
      have hz : ∀ j, raw5214 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw5214step0 = (fun i j => raw5214 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5214 permutation7 hz
    _ = injectiveMoment H node4 := by rfl

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

theorem canonical7683 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7683 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7683 = injectiveMoment H raw7683step0 := by
      have heq : raw7683step0 = (fun i j => raw7683 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7683 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical813 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw813 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw813 = injectiveMoment H raw813step0 := by
      have heq : raw813step0 = -raw813 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw813).symm
    injectiveMoment H raw813step0 = injectiveMoment H raw813step1 := by
      have heq : raw813step1 = (fun i j => raw813step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw813step0 permutation4 permutation8
    _ = injectiveMoment H node36 := by rfl

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

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SinglePriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair420 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node420 node420Labels = Sparse.eval singlePairValue420 (familyPairVector B) := by
  have hp := single_label_three B hB node420
  have hl : node420Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node420 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 1) = PairSemantics.raw5214 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node420 PairSemantics.raw5214; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5214 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 2) = PairSemantics.raw7683 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node420 PairSemantics.raw7683; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7683 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 3) = PairSemantics.raw917 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node420 PairSemantics.raw917; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical917 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value36 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 4) = PairSemantics.raw813 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node420 PairSemantics.raw813; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical813 hH).trans (PairSemantics.sound36 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue420, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value11, PairSemantics.value36, Sparse.eval] at hp ⊢
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

theorem singleton2788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2788 node2788Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node420 node420Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw284 singletonSmall2788
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2788) = raw284Labels := by decide +kernel
  rw [hl, canonical284 B hB] at h
  have hc0 : mixedMoment B raw284 (Fin.cases (0 : Fin 1) singletonSmall2788) =
      mixedMoment B node420 node420Labels := by
    have ha : raw284 = raw285 := by apply Matrix.ext; unfold raw284 raw285; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2788 = raw285Labels := by decide +kernel
    rw [ha, hj, canonical285 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3121 node3121Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node420 node420Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw404 singletonSmall3121
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3121) = raw404Labels := by decide +kernel
  rw [hl, canonical404 B hB] at h
  have hc0 : mixedMoment B raw404 (Fin.cases (0 : Fin 1) singletonSmall3121) =
      mixedMoment B node420 node420Labels := by
    have ha : raw404 = raw405 := by apply Matrix.ext; unfold raw404 raw405; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3121 = raw405Labels := by decide +kernel
    rw [ha, hj, canonical405 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem singleton4621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4621 node4621Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1297 node1297Labels + mixedMoment B node2289 node2289Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1446 singletonSmall4621
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4621) = raw1446Labels := by decide +kernel
  rw [hl, canonical1446 B hB] at h
  have hc0 : mixedMoment B raw1446 (Fin.cases (0 : Fin 2) singletonSmall4621) =
      mixedMoment B node1297 node1297Labels := by
    have ha : raw1446 = raw1447 := by apply Matrix.ext; unfold raw1446 raw1447; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4621 = raw1447Labels := by decide +kernel
    rw [ha, hj, canonical1447 B hB]
  have hc1 : mixedMoment B raw1446 (Fin.cases (1 : Fin 2) singletonSmall4621) =
      mixedMoment B node2289 node2289Labels := by
    have ha : raw1446 = raw1448 := by apply Matrix.ext; unfold raw1446 raw1448; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4621 = raw1448Labels := by decide +kernel
    rw [ha, hj, canonical1448 B hB]
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

theorem singleton5272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5272 node5272Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2740 node2740Labels + mixedMoment B node2740 node2740Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2283 singletonSmall5272
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5272) = raw2283Labels := by decide +kernel
  rw [hl, canonical2283 B hB] at h
  have hc0 : mixedMoment B raw2283 (Fin.cases (0 : Fin 2) singletonSmall5272) =
      mixedMoment B node2740 node2740Labels := by
    have ha : raw2283 = raw2284 := by apply Matrix.ext; unfold raw2283 raw2284; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5272 = raw2284Labels := by decide +kernel
    rw [ha, hj, canonical2284 B hB]
  have hc1 : mixedMoment B raw2283 (Fin.cases (1 : Fin 2) singletonSmall5272) =
      mixedMoment B node2740 node2740Labels := by
    have ha : raw2283 = raw2285 := by apply Matrix.ext; unfold raw2283 raw2285; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5272 = raw2285Labels := by decide +kernel
    rw [ha, hj, canonical2285 B hB]
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

theorem singleton5310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5310 node5310Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2788 node2788Labels + mixedMoment B node3633 node3633Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2325 singletonSmall5310
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5310) = raw2325Labels := by decide +kernel
  rw [hl, canonical2325 B hB] at h
  have hc0 : mixedMoment B raw2325 (Fin.cases (0 : Fin 2) singletonSmall5310) =
      mixedMoment B node2788 node2788Labels := by
    have ha : raw2325 = raw2326 := by apply Matrix.ext; unfold raw2325 raw2326; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5310 = raw2326Labels := by decide +kernel
    rw [ha, hj, canonical2326 B hB]
  have hc1 : mixedMoment B raw2325 (Fin.cases (1 : Fin 2) singletonSmall5310) =
      mixedMoment B node3633 node3633Labels := by
    have ha : raw2325 = raw2327 := by apply Matrix.ext; unfold raw2325 raw2327; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5310 = raw2327Labels := by decide +kernel
    rw [ha, hj, canonical2327 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
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

theorem sound420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node420 node420Labels = Sparse.eval nodeValue420 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue420 (familyPairVector B) := singlePair420 B _hB
    _ = _ := by norm_num [singlePairValue420, nodeValue420, Sparse.eval, mixedVector] <;> ring

theorem sound2788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2788 node2788Labels = Sparse.eval nodeValue2788 (mixedVector B) := by
  have h := singleton2788 B _hB
  rw [sound420 B _hB _hF] at h
  norm_num [nodeValue2788, nodeValue420, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3633 node3633Labels = Sparse.eval nodeValue3633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3633) = mixedMoment B node3633 node3633Labels := rfl
  simpa [nodeValue3633, Sparse.eval] using hc.symm

theorem sound3907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3907 node3907Labels = Sparse.eval nodeValue3907 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3907) = mixedMoment B node3907 node3907Labels := rfl
  simpa [nodeValue3907, Sparse.eval] using hc.symm

theorem sound5310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5310 node5310Labels = Sparse.eval nodeValue5310 (mixedVector B) := by
  have h := singleton5310 B _hB
  rw [sound2788 B _hB _hF, sound3633 B _hB _hF] at h
  norm_num [nodeValue5310, nodeValue2788, nodeValue3633, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound1297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1297 node1297Labels = Sparse.eval nodeValue1297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1297) = mixedMoment B node1297 node1297Labels := rfl
  simpa [nodeValue1297, Sparse.eval] using hc.symm

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

theorem sound2019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2019 node2019Labels = Sparse.eval nodeValue2019 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2019) = mixedMoment B node2019 node2019Labels := rfl
  simpa [nodeValue2019, Sparse.eval] using hc.symm

theorem sound2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2022 node2022Labels = Sparse.eval nodeValue2022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2022) = mixedMoment B node2022 node2022Labels := rfl
  simpa [nodeValue2022, Sparse.eval] using hc.symm

theorem sound2028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2028 node2028Labels = Sparse.eval nodeValue2028 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2028) = mixedMoment B node2028 node2028Labels := rfl
  simpa [nodeValue2028, Sparse.eval] using hc.symm

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

theorem zero2053 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2053 node2053Labels = 0 := by
  exact mixedMoment_order_one B hB node2053 node2053Labels 1
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

theorem sound2053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2053 node2053Labels = Sparse.eval nodeValue2053 (mixedVector B) := by
  simpa only [nodeValue2053, Sparse.eval_nil] using zero2053 B _hB _hF

theorem sound2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2109 node2109Labels = Sparse.eval nodeValue2109 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2109) = mixedMoment B node2109 node2109Labels := rfl
  simpa [nodeValue2109, Sparse.eval] using hc.symm

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

theorem zero2264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = 0 := by
  exact mixedMoment_order_one B hB node2264 node2264Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = 0 := by
  exact mixedMoment_order_one B hB node2292 node2292Labels 1
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

theorem sound2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2261 node2261Labels = Sparse.eval nodeValue2261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2261) = mixedMoment B node2261 node2261Labels := rfl
  simpa [nodeValue2261, Sparse.eval] using hc.symm

theorem sound2264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = Sparse.eval nodeValue2264 (mixedVector B) := by
  simpa only [nodeValue2264, Sparse.eval_nil] using zero2264 B _hB _hF

theorem sound2289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2289 node2289Labels = Sparse.eval nodeValue2289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2289) = mixedMoment B node2289 node2289Labels := rfl
  simpa [nodeValue2289, Sparse.eval] using hc.symm

theorem sound2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = Sparse.eval nodeValue2292 (mixedVector B) := by
  simpa only [nodeValue2292, Sparse.eval_nil] using zero2292 B _hB _hF

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

theorem sound2719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2719 node2719Labels = Sparse.eval nodeValue2719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2719) = mixedMoment B node2719 node2719Labels := rfl
  simpa [nodeValue2719, Sparse.eval] using hc.symm

theorem sound2737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2737 node2737Labels = Sparse.eval nodeValue2737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2737) = mixedMoment B node2737 node2737Labels := rfl
  simpa [nodeValue2737, Sparse.eval] using hc.symm

theorem sound2740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2740 node2740Labels = Sparse.eval nodeValue2740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2740) = mixedMoment B node2740 node2740Labels := rfl
  simpa [nodeValue2740, Sparse.eval] using hc.symm

theorem sound2743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2743 node2743Labels = Sparse.eval nodeValue2743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2743) = mixedMoment B node2743 node2743Labels := rfl
  simpa [nodeValue2743, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2786 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2786 node2786Labels = 0 := by
  exact mixedMoment_order_one B hB node2786 node2786Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2765 node2765Labels = Sparse.eval nodeValue2765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2765) = mixedMoment B node2765 node2765Labels := rfl
  simpa [nodeValue2765, Sparse.eval] using hc.symm

theorem sound2780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2780 node2780Labels = Sparse.eval nodeValue2780 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2780) = mixedMoment B node2780 node2780Labels := rfl
  simpa [nodeValue2780, Sparse.eval] using hc.symm

theorem sound2786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2786 node2786Labels = Sparse.eval nodeValue2786 (mixedVector B) := by
  simpa only [nodeValue2786, Sparse.eval_nil] using zero2786 B _hB _hF

theorem sound2789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2789 node2789Labels = Sparse.eval nodeValue2789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2789) = mixedMoment B node2789 node2789Labels := rfl
  simpa [nodeValue2789, Sparse.eval] using hc.symm

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

theorem sound3098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3098 node3098Labels = Sparse.eval nodeValue3098 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3098) = mixedMoment B node3098 node3098Labels := rfl
  simpa [nodeValue3098, Sparse.eval] using hc.symm

theorem sound3121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3121 node3121Labels = Sparse.eval nodeValue3121 (mixedVector B) := by
  have h := singleton3121 B _hB
  rw [sound420 B _hB _hF] at h
  norm_num [nodeValue3121, nodeValue420, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3908 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3908 node3908Labels = 0 := by
  exact mixedMoment_order_one B hB node3908 node3908Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3908 node3908Labels = Sparse.eval nodeValue3908 (mixedVector B) := by
  simpa only [nodeValue3908, Sparse.eval_nil] using zero3908 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4617 node4617Labels = Sparse.eval nodeValue4617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4617) = mixedMoment B node4617 node4617Labels := rfl
  simpa [nodeValue4617, Sparse.eval] using hc.symm

theorem sound4621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4621 node4621Labels = Sparse.eval nodeValue4621 (mixedVector B) := by
  have h := singleton4621 B _hB
  rw [sound1297 B _hB _hF, sound2289 B _hB _hF] at h
  norm_num [nodeValue4621, nodeValue1297, nodeValue2289, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4626 node4626Labels = Sparse.eval nodeValue4626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4626) = mixedMoment B node4626 node4626Labels := rfl
  simpa [nodeValue4626, Sparse.eval] using hc.symm

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

theorem zero4897 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = 0 := by
  exact mixedMoment_order_one B hB node4897 node4897Labels 1
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

theorem sound4868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4868 node4868Labels = Sparse.eval nodeValue4868 (mixedVector B) := by
  have h := singleton4868 B _hB
  rw [sound2109 B _hB _hF, sound2261 B _hB _hF] at h
  norm_num [nodeValue4868, nodeValue2109, nodeValue2261, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = Sparse.eval nodeValue4897 (mixedVector B) := by
  simpa only [nodeValue4897, Sparse.eval_nil] using zero4897 B _hB _hF

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

theorem sound5161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5161 node5161Labels = Sparse.eval nodeValue5161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5161) = mixedMoment B node5161 node5161Labels := rfl
  simpa [nodeValue5161, Sparse.eval] using hc.symm

theorem sound5175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5175 node5175Labels = Sparse.eval nodeValue5175 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5175) = mixedMoment B node5175 node5175Labels := rfl
  simpa [nodeValue5175, Sparse.eval] using hc.symm

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

theorem zero5308 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5308 node5308Labels = 0 := by
  exact mixedMoment_order_one B hB node5308 node5308Labels 1
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

theorem sound5272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5272 node5272Labels = Sparse.eval nodeValue5272 (mixedVector B) := by
  have h := singleton5272 B _hB
  rw [sound2740 B _hB _hF] at h
  norm_num [nodeValue5272, nodeValue2740, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5291 node5291Labels = Sparse.eval nodeValue5291 (mixedVector B) := by
  have h := singleton5291 B _hB
  rw [sound2765 B _hB _hF, sound3582 B _hB _hF] at h
  norm_num [nodeValue5291, nodeValue2765, nodeValue3582, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5295 node5295Labels = Sparse.eval nodeValue5295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5295) = mixedMoment B node5295 node5295Labels := rfl
  simpa [nodeValue5295, Sparse.eval] using hc.symm

theorem sound5308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5308 node5308Labels = Sparse.eval nodeValue5308 (mixedVector B) := by
  simpa only [nodeValue5308, Sparse.eval_nil] using zero5308 B _hB _hF

theorem sound5311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5311 node5311Labels = Sparse.eval nodeValue5311 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5311) = mixedMoment B node5311 node5311Labels := rfl
  simpa [nodeValue5311, Sparse.eval] using hc.symm

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

theorem sourceEq608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm608 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA608 + difference 0 0) (sourceB608 + difference 0 0) sourceC608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA608 + difference 0 0) (sourceB608 + difference 0 0) sourceC608) = raw10190 := by
      apply Matrix.ext; unfold tripleCharges sourceA608 sourceB608 sourceC608 difference raw10190; decide +kernel
    rw [ha]
    exact (canonical10190 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA608 + difference 1 0) (sourceB608 + difference 0 1) sourceC608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA608 + difference 1 0) (sourceB608 + difference 0 1) sourceC608) = raw10191 := by
      apply Matrix.ext; unfold tripleCharges sourceA608 sourceB608 sourceC608 difference raw10191; decide +kernel
    rw [ha]
    exact (canonical10191 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA608 + difference 2 0) (sourceB608 + difference 0 2) sourceC608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2019) := by
    have ha : (tripleCharges (sourceA608 + difference 2 0) (sourceB608 + difference 0 2) sourceC608) = raw10192 := by
      apply Matrix.ext; unfold tripleCharges sourceA608 sourceB608 sourceC608 difference raw10192; decide +kernel
    rw [ha]
    exact (canonical10192 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA608 + difference 3 0) (sourceB608 + difference 0 3) sourceC608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA608 + difference 3 0) (sourceB608 + difference 0 3) sourceC608) = raw9728 := by
      apply Matrix.ext; unfold tripleCharges sourceA608 sourceB608 sourceC608 difference raw9728; decide +kernel
    rw [ha]
    exact (canonical9728 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA608 + difference 4 0) (sourceB608 + difference 0 4) sourceC608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2053) := by
    have ha : (tripleCharges (sourceA608 + difference 4 0) (sourceB608 + difference 0 4) sourceC608) = raw9968 := by
      apply Matrix.ext; unfold tripleCharges sourceA608 sourceB608 sourceC608 difference raw9968; decide +kernel
    rw [ha]
    exact (canonical9968 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA608 + difference 5 0) (sourceB608 + difference 0 5) sourceC608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA608 + difference 5 0) (sourceB608 + difference 0 5) sourceC608) = raw10193 := by
      apply Matrix.ext; unfold tripleCharges sourceA608 sourceB608 sourceC608 difference raw10193; decide +kernel
    rw [ha]
    exact (canonical10193 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA608 + sourceB608) sourceC608) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA608 + sourceB608) sourceC608) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA608 sourceB608 sourceC608 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA608 sourceB608 sourceC608
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm608, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq611 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm611 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA611 + difference 0 1) (sourceB611 + difference 1 0) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA611 + difference 0 1) (sourceB611 + difference 1 0) sourceC611) = raw10238 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10238; decide +kernel
    rw [ha]
    exact (canonical10238 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA611 + difference 0 2) (sourceB611 + difference 2 0) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA611 + difference 0 2) (sourceB611 + difference 2 0) sourceC611) = raw10239 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10239; decide +kernel
    rw [ha]
    exact (canonical10239 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA611 + difference 0 3) (sourceB611 + difference 3 0) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA611 + difference 0 3) (sourceB611 + difference 3 0) sourceC611) = raw10240 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10240; decide +kernel
    rw [ha]
    exact (canonical10240 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA611 + difference 0 4) (sourceB611 + difference 4 0) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA611 + difference 0 4) (sourceB611 + difference 4 0) sourceC611) = raw5105 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw5105; decide +kernel
    rw [ha]
    exact (canonical5105 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA611 + difference 0 5) (sourceB611 + difference 5 0) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA611 + difference 0 5) (sourceB611 + difference 5 0) sourceC611) = raw10241 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10241; decide +kernel
    rw [ha]
    exact (canonical10241 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA611 + difference 1 0) (sourceB611 + difference 0 1) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA611 + difference 1 0) (sourceB611 + difference 0 1) sourceC611) = raw10242 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10242; decide +kernel
    rw [ha]
    exact (canonical10242 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA611 + difference 1 2) (sourceB611 + difference 2 1) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA611 + difference 1 2) (sourceB611 + difference 2 1) sourceC611) = raw10243 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10243; decide +kernel
    rw [ha]
    exact (canonical10243 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA611 + difference 1 3) (sourceB611 + difference 3 1) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA611 + difference 1 3) (sourceB611 + difference 3 1) sourceC611) = raw10244 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10244; decide +kernel
    rw [ha]
    exact (canonical10244 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA611 + difference 1 4) (sourceB611 + difference 4 1) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA611 + difference 1 4) (sourceB611 + difference 4 1) sourceC611) = raw5110 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw5110; decide +kernel
    rw [ha]
    exact (canonical5110 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA611 + difference 1 5) (sourceB611 + difference 5 1) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA611 + difference 1 5) (sourceB611 + difference 5 1) sourceC611) = raw10245 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10245; decide +kernel
    rw [ha]
    exact (canonical10245 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA611 + difference 2 0) (sourceB611 + difference 0 2) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA611 + difference 2 0) (sourceB611 + difference 0 2) sourceC611) = raw10246 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10246; decide +kernel
    rw [ha]
    exact (canonical10246 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA611 + difference 2 1) (sourceB611 + difference 1 2) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA611 + difference 2 1) (sourceB611 + difference 1 2) sourceC611) = raw10247 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10247; decide +kernel
    rw [ha]
    exact (canonical10247 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA611 + difference 2 3) (sourceB611 + difference 3 2) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA611 + difference 2 3) (sourceB611 + difference 3 2) sourceC611) = raw10248 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10248; decide +kernel
    rw [ha]
    exact (canonical10248 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA611 + difference 2 4) (sourceB611 + difference 4 2) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA611 + difference 2 4) (sourceB611 + difference 4 2) sourceC611) = raw5115 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw5115; decide +kernel
    rw [ha]
    exact (canonical5115 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA611 + difference 2 5) (sourceB611 + difference 5 2) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA611 + difference 2 5) (sourceB611 + difference 5 2) sourceC611) = raw10249 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10249; decide +kernel
    rw [ha]
    exact (canonical10249 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA611 + difference 3 0) (sourceB611 + difference 0 3) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA611 + difference 3 0) (sourceB611 + difference 0 3) sourceC611) = raw10250 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10250; decide +kernel
    rw [ha]
    exact (canonical10250 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA611 + difference 3 1) (sourceB611 + difference 1 3) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA611 + difference 3 1) (sourceB611 + difference 1 3) sourceC611) = raw10251 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10251; decide +kernel
    rw [ha]
    exact (canonical10251 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA611 + difference 3 2) (sourceB611 + difference 2 3) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA611 + difference 3 2) (sourceB611 + difference 2 3) sourceC611) = raw10252 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10252; decide +kernel
    rw [ha]
    exact (canonical10252 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA611 + difference 3 4) (sourceB611 + difference 4 3) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA611 + difference 3 4) (sourceB611 + difference 4 3) sourceC611) = raw5120 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw5120; decide +kernel
    rw [ha]
    exact (canonical5120 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA611 + difference 3 5) (sourceB611 + difference 5 3) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA611 + difference 3 5) (sourceB611 + difference 5 3) sourceC611) = raw10253 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10253; decide +kernel
    rw [ha]
    exact (canonical10253 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA611 + difference 4 0) (sourceB611 + difference 0 4) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4626) := by
    have ha : (tripleCharges (sourceA611 + difference 4 0) (sourceB611 + difference 0 4) sourceC611) = raw10254 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10254; decide +kernel
    rw [ha]
    exact (canonical10254 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA611 + difference 4 1) (sourceB611 + difference 1 4) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA611 + difference 4 1) (sourceB611 + difference 1 4) sourceC611) = raw10255 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10255; decide +kernel
    rw [ha]
    exact (canonical10255 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA611 + difference 4 2) (sourceB611 + difference 2 4) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA611 + difference 4 2) (sourceB611 + difference 2 4) sourceC611) = raw10256 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10256; decide +kernel
    rw [ha]
    exact (canonical10256 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA611 + difference 4 3) (sourceB611 + difference 3 4) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA611 + difference 4 3) (sourceB611 + difference 3 4) sourceC611) = raw10257 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10257; decide +kernel
    rw [ha]
    exact (canonical10257 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA611 + difference 4 5) (sourceB611 + difference 5 4) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5311) := by
    have ha : (tripleCharges (sourceA611 + difference 4 5) (sourceB611 + difference 5 4) sourceC611) = raw10258 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10258; decide +kernel
    rw [ha]
    exact (canonical10258 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA611 + difference 5 0) (sourceB611 + difference 0 5) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA611 + difference 5 0) (sourceB611 + difference 0 5) sourceC611) = raw5121 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw5121; decide +kernel
    rw [ha]
    exact (canonical5121 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA611 + difference 5 1) (sourceB611 + difference 1 5) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA611 + difference 5 1) (sourceB611 + difference 1 5) sourceC611) = raw5122 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw5122; decide +kernel
    rw [ha]
    exact (canonical5122 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA611 + difference 5 2) (sourceB611 + difference 2 5) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA611 + difference 5 2) (sourceB611 + difference 2 5) sourceC611) = raw5123 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw5123; decide +kernel
    rw [ha]
    exact (canonical5123 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA611 + difference 5 3) (sourceB611 + difference 3 5) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA611 + difference 5 3) (sourceB611 + difference 3 5) sourceC611) = raw5124 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw5124; decide +kernel
    rw [ha]
    exact (canonical5124 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA611 + difference 5 4) (sourceB611 + difference 4 5) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA611 + difference 5 4) (sourceB611 + difference 4 5) sourceC611) = raw10259 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10259; decide +kernel
    rw [ha]
    exact (canonical10259 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA611 sourceB611 sourceC611
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm611, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq613 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm613 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA613 + difference 0 1) (sourceB613 + difference 1 0) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA613 + difference 0 1) (sourceB613 + difference 1 0) sourceC613) = raw10290 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10290; decide +kernel
    rw [ha]
    exact (canonical10290 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA613 + difference 0 2) (sourceB613 + difference 2 0) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA613 + difference 0 2) (sourceB613 + difference 2 0) sourceC613) = raw10291 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10291; decide +kernel
    rw [ha]
    exact (canonical10291 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA613 + difference 0 3) (sourceB613 + difference 3 0) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA613 + difference 0 3) (sourceB613 + difference 3 0) sourceC613) = raw10292 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10292; decide +kernel
    rw [ha]
    exact (canonical10292 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA613 + difference 0 4) (sourceB613 + difference 4 0) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2786) := by
    have ha : (tripleCharges (sourceA613 + difference 0 4) (sourceB613 + difference 4 0) sourceC613) = raw5135 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw5135; decide +kernel
    rw [ha]
    exact (canonical5135 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA613 + difference 0 5) (sourceB613 + difference 5 0) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA613 + difference 0 5) (sourceB613 + difference 5 0) sourceC613) = raw10293 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10293; decide +kernel
    rw [ha]
    exact (canonical10293 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA613 + difference 1 0) (sourceB613 + difference 0 1) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA613 + difference 1 0) (sourceB613 + difference 0 1) sourceC613) = raw10294 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10294; decide +kernel
    rw [ha]
    exact (canonical10294 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA613 + difference 1 2) (sourceB613 + difference 2 1) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA613 + difference 1 2) (sourceB613 + difference 2 1) sourceC613) = raw10295 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10295; decide +kernel
    rw [ha]
    exact (canonical10295 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA613 + difference 1 3) (sourceB613 + difference 3 1) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA613 + difference 1 3) (sourceB613 + difference 3 1) sourceC613) = raw10296 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10296; decide +kernel
    rw [ha]
    exact (canonical10296 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA613 + difference 1 4) (sourceB613 + difference 4 1) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA613 + difference 1 4) (sourceB613 + difference 4 1) sourceC613) = raw5140 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw5140; decide +kernel
    rw [ha]
    exact (canonical5140 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA613 + difference 1 5) (sourceB613 + difference 5 1) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA613 + difference 1 5) (sourceB613 + difference 5 1) sourceC613) = raw10297 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10297; decide +kernel
    rw [ha]
    exact (canonical10297 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA613 + difference 2 0) (sourceB613 + difference 0 2) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA613 + difference 2 0) (sourceB613 + difference 0 2) sourceC613) = raw10298 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10298; decide +kernel
    rw [ha]
    exact (canonical10298 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA613 + difference 2 1) (sourceB613 + difference 1 2) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA613 + difference 2 1) (sourceB613 + difference 1 2) sourceC613) = raw10299 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10299; decide +kernel
    rw [ha]
    exact (canonical10299 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA613 + difference 2 3) (sourceB613 + difference 3 2) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA613 + difference 2 3) (sourceB613 + difference 3 2) sourceC613) = raw10300 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10300; decide +kernel
    rw [ha]
    exact (canonical10300 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA613 + difference 2 4) (sourceB613 + difference 4 2) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA613 + difference 2 4) (sourceB613 + difference 4 2) sourceC613) = raw5145 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw5145; decide +kernel
    rw [ha]
    exact (canonical5145 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA613 + difference 2 5) (sourceB613 + difference 5 2) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA613 + difference 2 5) (sourceB613 + difference 5 2) sourceC613) = raw10301 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10301; decide +kernel
    rw [ha]
    exact (canonical10301 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA613 + difference 3 0) (sourceB613 + difference 0 3) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA613 + difference 3 0) (sourceB613 + difference 0 3) sourceC613) = raw10302 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10302; decide +kernel
    rw [ha]
    exact (canonical10302 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA613 + difference 3 1) (sourceB613 + difference 1 3) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA613 + difference 3 1) (sourceB613 + difference 1 3) sourceC613) = raw10303 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10303; decide +kernel
    rw [ha]
    exact (canonical10303 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA613 + difference 3 2) (sourceB613 + difference 2 3) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA613 + difference 3 2) (sourceB613 + difference 2 3) sourceC613) = raw10304 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10304; decide +kernel
    rw [ha]
    exact (canonical10304 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA613 + difference 3 4) (sourceB613 + difference 4 3) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA613 + difference 3 4) (sourceB613 + difference 4 3) sourceC613) = raw5150 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw5150; decide +kernel
    rw [ha]
    exact (canonical5150 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA613 + difference 3 5) (sourceB613 + difference 5 3) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA613 + difference 3 5) (sourceB613 + difference 5 3) sourceC613) = raw10305 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10305; decide +kernel
    rw [ha]
    exact (canonical10305 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA613 + difference 4 0) (sourceB613 + difference 0 4) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2780) := by
    have ha : (tripleCharges (sourceA613 + difference 4 0) (sourceB613 + difference 0 4) sourceC613) = raw10306 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10306; decide +kernel
    rw [ha]
    exact (canonical10306 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA613 + difference 4 1) (sourceB613 + difference 1 4) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA613 + difference 4 1) (sourceB613 + difference 1 4) sourceC613) = raw10307 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10307; decide +kernel
    rw [ha]
    exact (canonical10307 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA613 + difference 4 2) (sourceB613 + difference 2 4) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA613 + difference 4 2) (sourceB613 + difference 2 4) sourceC613) = raw10308 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10308; decide +kernel
    rw [ha]
    exact (canonical10308 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA613 + difference 4 3) (sourceB613 + difference 3 4) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA613 + difference 4 3) (sourceB613 + difference 3 4) sourceC613) = raw10309 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10309; decide +kernel
    rw [ha]
    exact (canonical10309 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA613 + difference 4 5) (sourceB613 + difference 5 4) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA613 + difference 4 5) (sourceB613 + difference 5 4) sourceC613) = raw10310 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10310; decide +kernel
    rw [ha]
    exact (canonical10310 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA613 + difference 5 0) (sourceB613 + difference 0 5) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA613 + difference 5 0) (sourceB613 + difference 0 5) sourceC613) = raw5151 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw5151; decide +kernel
    rw [ha]
    exact (canonical5151 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA613 + difference 5 1) (sourceB613 + difference 1 5) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA613 + difference 5 1) (sourceB613 + difference 1 5) sourceC613) = raw5152 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw5152; decide +kernel
    rw [ha]
    exact (canonical5152 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA613 + difference 5 2) (sourceB613 + difference 2 5) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA613 + difference 5 2) (sourceB613 + difference 2 5) sourceC613) = raw5153 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw5153; decide +kernel
    rw [ha]
    exact (canonical5153 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA613 + difference 5 3) (sourceB613 + difference 3 5) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA613 + difference 5 3) (sourceB613 + difference 3 5) sourceC613) = raw5154 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw5154; decide +kernel
    rw [ha]
    exact (canonical5154 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA613 + difference 5 4) (sourceB613 + difference 4 5) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA613 + difference 5 4) (sourceB613 + difference 4 5) sourceC613) = raw10311 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10311; decide +kernel
    rw [ha]
    exact (canonical10311 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA613 sourceB613 sourceC613
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm613, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq618 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm618 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA618 + difference 0 0) (sourceB618 + difference 0 0) sourceC618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA618 + difference 0 0) (sourceB618 + difference 0 0) sourceC618) = raw10432 := by
      apply Matrix.ext; unfold tripleCharges sourceA618 sourceB618 sourceC618 difference raw10432; decide +kernel
    rw [ha]
    exact (canonical10432 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA618 + difference 0 1) (sourceB618 + difference 1 0) sourceC618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA618 + difference 0 1) (sourceB618 + difference 1 0) sourceC618) = raw10433 := by
      apply Matrix.ext; unfold tripleCharges sourceA618 sourceB618 sourceC618 difference raw10433; decide +kernel
    rw [ha]
    exact (canonical10433 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA618 + difference 0 2) (sourceB618 + difference 2 0) sourceC618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA618 + difference 0 2) (sourceB618 + difference 2 0) sourceC618) = raw10434 := by
      apply Matrix.ext; unfold tripleCharges sourceA618 sourceB618 sourceC618 difference raw10434; decide +kernel
    rw [ha]
    exact (canonical10434 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA618 + difference 0 3) (sourceB618 + difference 3 0) sourceC618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA618 + difference 0 3) (sourceB618 + difference 3 0) sourceC618) = raw10435 := by
      apply Matrix.ext; unfold tripleCharges sourceA618 sourceB618 sourceC618 difference raw10435; decide +kernel
    rw [ha]
    exact (canonical10435 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA618 + difference 0 4) (sourceB618 + difference 4 0) sourceC618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA618 + difference 0 4) (sourceB618 + difference 4 0) sourceC618) = raw10436 := by
      apply Matrix.ext; unfold tripleCharges sourceA618 sourceB618 sourceC618 difference raw10436; decide +kernel
    rw [ha]
    exact (canonical10436 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA618 + difference 0 5) (sourceB618 + difference 5 0) sourceC618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3908) := by
    have ha : (tripleCharges (sourceA618 + difference 0 5) (sourceB618 + difference 5 0) sourceC618) = raw10437 := by
      apply Matrix.ext; unfold tripleCharges sourceA618 sourceB618 sourceC618 difference raw10437; decide +kernel
    rw [ha]
    exact (canonical10437 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA618 + sourceB618) sourceC618) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA618 + sourceB618) sourceC618) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA618 sourceB618 sourceC618 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA618 sourceB618 sourceC618
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm618, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck517 : Integer.Sparse.reindex keyMap MixedData.row517 = numericRow517 := by decide +kernel

theorem numericCheck517 (x : Master → ℝ) : Integer.Sparse.eval numericRow517 x =
    (1 : ℝ) * reducedSource517 x := by
  norm_num [numericRow517, reducedSource517, Integer.Sparse.eval, Sparse.eval, nodeValue2019, nodeValue2022, nodeValue2028, nodeValue2053, nodeValue2264, nodeValue3533, nodeValue4084]

theorem reindexCheck520 : Integer.Sparse.reindex keyMap MixedData.row520 = numericRow520 := by decide +kernel

theorem numericCheck520 (x : Master → ℝ) : Integer.Sparse.eval numericRow520 x =
    (576 : ℝ) * reducedSource520 x := by
  norm_num [numericRow520, reducedSource520, Integer.Sparse.eval, Sparse.eval, nodeValue4617, nodeValue4621, nodeValue4626, nodeValue4868, nodeValue4897, nodeValue5161, nodeValue5175, nodeValue5272, nodeValue5291, nodeValue5295, nodeValue5308, nodeValue5310, nodeValue5311]
  ring

theorem reindexCheck522 : Integer.Sparse.reindex keyMap MixedData.row522 = numericRow522 := by decide +kernel

theorem numericCheck522 (x : Master → ℝ) : Integer.Sparse.eval numericRow522 x =
    (144 : ℝ) * reducedSource522 x := by
  norm_num [numericRow522, reducedSource522, Integer.Sparse.eval, Sparse.eval, nodeValue2261, nodeValue2289, nodeValue2292, nodeValue2719, nodeValue2737, nodeValue2740, nodeValue2761, nodeValue2765, nodeValue2780, nodeValue2786, nodeValue2789, nodeValue3098, nodeValue3121]
  ring

theorem reindexCheck527 : Integer.Sparse.reindex keyMap MixedData.row527 = numericRow527 := by decide +kernel

theorem numericCheck527 (x : Master → ℝ) : Integer.Sparse.eval numericRow527 x =
    (1 : ℝ) * reducedSource527 x := by
  norm_num [numericRow527, reducedSource527, Integer.Sparse.eval, Sparse.eval, nodeValue2743, nodeValue3817, nodeValue3845, nodeValue3907, nodeValue3908, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero517 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource517 (mixedVector B) = 0 := by
  have h2019 : mixedVector B (Sum.inr 2019) = Sparse.eval nodeValue2019 (mixedVector B) := by
    change mixedMoment B node2019 node2019Labels = _
    exact sound2019 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h2028 : mixedVector B (Sum.inr 2028) = Sparse.eval nodeValue2028 (mixedVector B) := by
    change mixedMoment B node2028 node2028Labels = _
    exact sound2028 B hB hF
  have h2053 : mixedVector B (Sum.inr 2053) = Sparse.eval nodeValue2053 (mixedVector B) := by
    change mixedMoment B node2053 node2053Labels = _
    exact sound2053 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm608, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2019, h2022, h2028, h2053, h2264, h3533, h4084, reducedSource517] using sourceEq608 B hB

theorem rowSound517 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row517 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck517, numericCheck517, reducedZero517 B hB hF, mul_zero]

theorem reducedZero520 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource520 (mixedVector B) = 0 := by
  have h4617 : mixedVector B (Sum.inr 4617) = Sparse.eval nodeValue4617 (mixedVector B) := by
    change mixedMoment B node4617 node4617Labels = _
    exact sound4617 B hB hF
  have h4621 : mixedVector B (Sum.inr 4621) = Sparse.eval nodeValue4621 (mixedVector B) := by
    change mixedMoment B node4621 node4621Labels = _
    exact sound4621 B hB hF
  have h4626 : mixedVector B (Sum.inr 4626) = Sparse.eval nodeValue4626 (mixedVector B) := by
    change mixedMoment B node4626 node4626Labels = _
    exact sound4626 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h5161 : mixedVector B (Sum.inr 5161) = Sparse.eval nodeValue5161 (mixedVector B) := by
    change mixedMoment B node5161 node5161Labels = _
    exact sound5161 B hB hF
  have h5175 : mixedVector B (Sum.inr 5175) = Sparse.eval nodeValue5175 (mixedVector B) := by
    change mixedMoment B node5175 node5175Labels = _
    exact sound5175 B hB hF
  have h5272 : mixedVector B (Sum.inr 5272) = Sparse.eval nodeValue5272 (mixedVector B) := by
    change mixedMoment B node5272 node5272Labels = _
    exact sound5272 B hB hF
  have h5291 : mixedVector B (Sum.inr 5291) = Sparse.eval nodeValue5291 (mixedVector B) := by
    change mixedMoment B node5291 node5291Labels = _
    exact sound5291 B hB hF
  have h5295 : mixedVector B (Sum.inr 5295) = Sparse.eval nodeValue5295 (mixedVector B) := by
    change mixedMoment B node5295 node5295Labels = _
    exact sound5295 B hB hF
  have h5308 : mixedVector B (Sum.inr 5308) = Sparse.eval nodeValue5308 (mixedVector B) := by
    change mixedMoment B node5308 node5308Labels = _
    exact sound5308 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  have h5311 : mixedVector B (Sum.inr 5311) = Sparse.eval nodeValue5311 (mixedVector B) := by
    change mixedMoment B node5311 node5311Labels = _
    exact sound5311 B hB hF
  simpa only [sourceForm611, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4617, h4621, h4626, h4868, h4897, h5161, h5175, h5272, h5291, h5295, h5308, h5310, h5311, reducedSource520] using sourceEq611 B hB

theorem rowSound520 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row520 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck520, numericCheck520, reducedZero520 B hB hF, mul_zero]

theorem reducedZero522 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource522 (mixedVector B) = 0 := by
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h2719 : mixedVector B (Sum.inr 2719) = Sparse.eval nodeValue2719 (mixedVector B) := by
    change mixedMoment B node2719 node2719Labels = _
    exact sound2719 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h2761 : mixedVector B (Sum.inr 2761) = Sparse.eval nodeValue2761 (mixedVector B) := by
    change mixedMoment B node2761 node2761Labels = _
    exact sound2761 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h2780 : mixedVector B (Sum.inr 2780) = Sparse.eval nodeValue2780 (mixedVector B) := by
    change mixedMoment B node2780 node2780Labels = _
    exact sound2780 B hB hF
  have h2786 : mixedVector B (Sum.inr 2786) = Sparse.eval nodeValue2786 (mixedVector B) := by
    change mixedMoment B node2786 node2786Labels = _
    exact sound2786 B hB hF
  have h2789 : mixedVector B (Sum.inr 2789) = Sparse.eval nodeValue2789 (mixedVector B) := by
    change mixedMoment B node2789 node2789Labels = _
    exact sound2789 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3121 : mixedVector B (Sum.inr 3121) = Sparse.eval nodeValue3121 (mixedVector B) := by
    change mixedMoment B node3121 node3121Labels = _
    exact sound3121 B hB hF
  simpa only [sourceForm613, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2261, h2289, h2292, h2719, h2737, h2740, h2761, h2765, h2780, h2786, h2789, h3098, h3121, reducedSource522] using sourceEq613 B hB

theorem rowSound522 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row522 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck522, numericCheck522, reducedZero522 B hB hF, mul_zero]

theorem reducedZero527 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource527 (mixedVector B) = 0 := by
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h3817 : mixedVector B (Sum.inr 3817) = Sparse.eval nodeValue3817 (mixedVector B) := by
    change mixedMoment B node3817 node3817Labels = _
    exact sound3817 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h3907 : mixedVector B (Sum.inr 3907) = Sparse.eval nodeValue3907 (mixedVector B) := by
    change mixedMoment B node3907 node3907Labels = _
    exact sound3907 B hB hF
  have h3908 : mixedVector B (Sum.inr 3908) = Sparse.eval nodeValue3908 (mixedVector B) := by
    change mixedMoment B node3908 node3908Labels = _
    exact sound3908 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm618, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2743, h3817, h3845, h3907, h3908, h4092, reducedSource527] using sourceEq618 B hB

theorem rowSound527 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row527 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck527, numericCheck527, reducedZero527 B hB hF, mul_zero]

theorem sourceRowsAt512 : MixedData.sourceRows (512 : Fin 2425) =
    MixedData.row512 := by decide +kernel

theorem sourceRowsAt513 : MixedData.sourceRows (513 : Fin 2425) =
    MixedData.row513 := by decide +kernel

theorem sourceRowsAt514 : MixedData.sourceRows (514 : Fin 2425) =
    MixedData.row514 := by decide +kernel

theorem sourceRowsAt515 : MixedData.sourceRows (515 : Fin 2425) =
    MixedData.row515 := by decide +kernel

theorem sourceRowsAt516 : MixedData.sourceRows (516 : Fin 2425) =
    MixedData.row516 := by decide +kernel

theorem sourceRowsAt517 : MixedData.sourceRows (517 : Fin 2425) =
    MixedData.row517 := by decide +kernel

theorem sourceRowsAt518 : MixedData.sourceRows (518 : Fin 2425) =
    MixedData.row518 := by decide +kernel

theorem sourceRowsAt519 : MixedData.sourceRows (519 : Fin 2425) =
    MixedData.row519 := by decide +kernel

theorem sourceRowsAt520 : MixedData.sourceRows (520 : Fin 2425) =
    MixedData.row520 := by decide +kernel

theorem sourceRowsAt521 : MixedData.sourceRows (521 : Fin 2425) =
    MixedData.row521 := by decide +kernel

theorem sourceRowsAt522 : MixedData.sourceRows (522 : Fin 2425) =
    MixedData.row522 := by decide +kernel

theorem sourceRowsAt523 : MixedData.sourceRows (523 : Fin 2425) =
    MixedData.row523 := by decide +kernel

theorem sourceRowsAt524 : MixedData.sourceRows (524 : Fin 2425) =
    MixedData.row524 := by decide +kernel

theorem sourceRowsAt525 : MixedData.sourceRows (525 : Fin 2425) =
    MixedData.row525 := by decide +kernel

theorem sourceRowsAt526 : MixedData.sourceRows (526 : Fin 2425) =
    MixedData.row526 := by decide +kernel

theorem sourceRowsAt527 : MixedData.sourceRows (527 : Fin 2425) =
    MixedData.row527 := by decide +kernel

theorem chunkSound32_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 32) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 512 ∨ k.val = 513 ∨ k.val = 514 ∨ k.val = 515 ∨ k.val = 516 ∨ k.val = 517 ∨ k.val = 518 ∨ k.val = 519 ∨ k.val = 520 ∨ k.val = 521 ∨ k.val = 522 ∨ k.val = 523 ∨ k.val = 524 ∨ k.val = 525 ∨ k.val = 526 ∨ k.val = 527 := by omega
  rcases heq with h512 | h513 | h514 | h515 | h516 | h517 | h518 | h519 | h520 | h521 | h522 | h523 | h524 | h525 | h526 | h527
  · have he : k = (512 : Fin 2425) := Fin.ext h512
    subst k
    rw [sourceRowsAt512]
    exact rowSound512_e B hB hF
  · have he : k = (513 : Fin 2425) := Fin.ext h513
    subst k
    rw [sourceRowsAt513]
    exact rowSound513_e B hB hF
  · have he : k = (514 : Fin 2425) := Fin.ext h514
    subst k
    rw [sourceRowsAt514]
    exact rowSound514_e B hB hF
  · have he : k = (515 : Fin 2425) := Fin.ext h515
    subst k
    rw [sourceRowsAt515]
    exact rowSound515_e B hB hF
  · have he : k = (516 : Fin 2425) := Fin.ext h516
    subst k
    rw [sourceRowsAt516]
    exact rowSound516_e B hB hF
  · have he : k = (517 : Fin 2425) := Fin.ext h517
    subst k
    rw [sourceRowsAt517]
    exact rowSound517 B hB hF
  · have he : k = (518 : Fin 2425) := Fin.ext h518
    subst k
    rw [sourceRowsAt518]
    exact rowSound518_e B hB hF
  · have he : k = (519 : Fin 2425) := Fin.ext h519
    subst k
    rw [sourceRowsAt519]
    exact rowSound519_e B hB hF
  · have he : k = (520 : Fin 2425) := Fin.ext h520
    subst k
    rw [sourceRowsAt520]
    exact rowSound520 B hB hF
  · have he : k = (521 : Fin 2425) := Fin.ext h521
    subst k
    rw [sourceRowsAt521]
    exact rowSound521_e B hB hF
  · have he : k = (522 : Fin 2425) := Fin.ext h522
    subst k
    rw [sourceRowsAt522]
    exact rowSound522 B hB hF
  · have he : k = (523 : Fin 2425) := Fin.ext h523
    subst k
    rw [sourceRowsAt523]
    exact rowSound523_e B hB hF
  · have he : k = (524 : Fin 2425) := Fin.ext h524
    subst k
    rw [sourceRowsAt524]
    exact rowSound524_e B hB hF
  · have he : k = (525 : Fin 2425) := Fin.ext h525
    subst k
    rw [sourceRowsAt525]
    exact rowSound525_e B hB hF
  · have he : k = (526 : Fin 2425) := Fin.ext h526
    subst k
    rw [sourceRowsAt526]
    exact rowSound526_e B hB hF
  · have he : k = (527 : Fin 2425) := Fin.ext h527
    subst k
    rw [sourceRowsAt527]
    exact rowSound527 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e_oai
