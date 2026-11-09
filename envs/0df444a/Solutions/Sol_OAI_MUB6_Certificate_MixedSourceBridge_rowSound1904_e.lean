-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:39:51.999579+00:00
-- url     : https://prove2.me/submissions/1dfde29d-5b7f-434f-bfc4-4323f7fdbf63

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5168_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5387_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5415_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5439_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical76 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw76 raw76Labels = mixedMoment B node1300 node1300Labels := by
  calc
    mixedMoment B raw76 raw76Labels = mixedMoment B raw76step0 raw76step0Labels := by
      have ha : raw76step0 = (fun i j => raw76 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw76step0 raw76; decide +kernel
      have hl : raw76step0Labels = raw76Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw76 raw76Labels permutation8 permutation5
    mixedMoment B raw76step0 raw76step0Labels = mixedMoment B raw76step1 raw76step1Labels := by
      have ha : raw76step1 = raw76step0 := by apply Matrix.ext; unfold raw76step1 raw76step0; decide +kernel
      have hl : raw76step0Labels = labelEmbedding1 ∘ raw76step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw76step0 raw76step0Labels raw76step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1300 node1300Labels := by rfl

theorem canonical77 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw77 raw77Labels = mixedMoment B node156 node156Labels := by
  calc
    mixedMoment B raw77 raw77Labels = mixedMoment B raw77step0 raw77step0Labels := by
      have ha : raw77step0 = (fun i j => raw77 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw77step0 raw77; decide +kernel
      have hl : raw77step0Labels = raw77Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw77 raw77Labels permutation8 permutation5
    _ = mixedMoment B node156 node156Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw238 raw238Labels = mixedMoment B node2598 node2598Labels := by
  calc
    mixedMoment B raw238 raw238Labels = mixedMoment B raw238step0 raw238step0Labels := by
      have ha : raw238step0 = (fun i j => raw238 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw238step0 raw238; decide +kernel
      have hl : raw238step0Labels = raw238Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw238 raw238Labels permutation8 permutation5
    mixedMoment B raw238step0 raw238step0Labels = mixedMoment B raw238step1 raw238step1Labels := by
      have ha : raw238step1 = raw238step0 := by apply Matrix.ext; unfold raw238step1 raw238step0; decide +kernel
      have hl : raw238step0Labels = labelEmbedding1 ∘ raw238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw238step0 raw238step0Labels raw238step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2598 node2598Labels := by rfl

theorem canonical239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw239 raw239Labels = mixedMoment B node338 node338Labels := by
  calc
    mixedMoment B raw239 raw239Labels = mixedMoment B raw239step0 raw239step0Labels := by
      have ha : raw239step0 = (fun i j => raw239 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw239step0 raw239; decide +kernel
      have hl : raw239step0Labels = raw239Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw239 raw239Labels permutation8 permutation5
    _ = mixedMoment B node338 node338Labels := by rfl

theorem canonical246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw246 raw246Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw246 raw246Labels = mixedMoment B raw246step0 raw246step0Labels := by
      have ha : raw246step0 = (fun i j => raw246 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw246step0 raw246; decide +kernel
      have hl : raw246step0Labels = raw246Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw246 raw246Labels permutation8 permutation5
    mixedMoment B raw246step0 raw246step0Labels = mixedMoment B raw246step1 raw246step1Labels := by
      have ha : raw246step1 = raw246step0 := by apply Matrix.ext; unfold raw246step1 raw246step0; decide +kernel
      have hl : raw246step0Labels = labelEmbedding1 ∘ raw246step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw246step0 raw246step0Labels raw246step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2604 node2604Labels := by rfl

theorem canonical247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw247 raw247Labels = mixedMoment B node343 node343Labels := by
  calc
    mixedMoment B raw247 raw247Labels = mixedMoment B raw247step0 raw247step0Labels := by
      have ha : raw247step0 = (fun i j => raw247 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw247step0 raw247; decide +kernel
      have hl : raw247step0Labels = raw247Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw247 raw247Labels permutation8 permutation5
    _ = mixedMoment B node343 node343Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical1377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1377 raw1377Labels = mixedMoment B node4550 node4550Labels := by
  calc
    mixedMoment B raw1377 raw1377Labels = mixedMoment B raw1377step0 raw1377step0Labels := by
      have ha : raw1377step0 = (fun i j => raw1377 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1377step0 raw1377; decide +kernel
      have hl : raw1377step0Labels = raw1377Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1377 raw1377Labels permutation152 permutation4
    mixedMoment B raw1377step0 raw1377step0Labels = mixedMoment B raw1377step1 raw1377step1Labels := by
      have ha : raw1377step1 = raw1377step0 := by apply Matrix.ext; unfold raw1377step1 raw1377step0; decide +kernel
      have hl : raw1377step0Labels = labelEmbedding7 ∘ raw1377step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1377step0 raw1377step0Labels raw1377step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4550 node4550Labels := by rfl

theorem canonical1378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1378 raw1378Labels = mixedMoment B node1135 node1135Labels := by
  calc
    mixedMoment B raw1378 raw1378Labels = mixedMoment B raw1378step0 raw1378step0Labels := by
      have ha : raw1378step0 = (fun i j => raw1378 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1378step0 raw1378; decide +kernel
      have hl : raw1378step0Labels = raw1378Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1378 raw1378Labels permutation152 permutation4
    _ = mixedMoment B node1135 node1135Labels := by rfl

theorem canonical1379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1379 raw1379Labels = mixedMoment B node3269 node3269Labels := by
  calc
    mixedMoment B raw1379 raw1379Labels = mixedMoment B raw1379step0 raw1379step0Labels := by
      have ha : raw1379step0 = (fun i j => raw1379 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1379step0 raw1379; decide +kernel
      have hl : raw1379step0Labels = raw1379Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1379 raw1379Labels permutation170 permutation6
    mixedMoment B raw1379step0 raw1379step0Labels = mixedMoment B raw1379step1 raw1379step1Labels := by
      have ha : raw1379step1 = -raw1379step0 := by apply Matrix.ext; change ∀ i j, raw1379step1 i j = -(raw1379step0 i j); unfold raw1379step1 raw1379step0; decide +kernel
      have hl : raw1379step1Labels = raw1379step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1379step1 raw1379step1Labels = mixedMoment B raw1379step2 raw1379step2Labels := by
      have ha : raw1379step2 = raw1379step1 := by apply Matrix.ext; unfold raw1379step2 raw1379step1; decide +kernel
      have hl : raw1379step1Labels = labelEmbedding1 ∘ raw1379step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1379step1 raw1379step1Labels raw1379step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3269 node3269Labels := by rfl

theorem canonical1380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1380 raw1380Labels = mixedMoment B node4551 node4551Labels := by
  calc
    mixedMoment B raw1380 raw1380Labels = mixedMoment B raw1380step0 raw1380step0Labels := by
      have ha : raw1380step0 = (fun i j => raw1380 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1380step0 raw1380; decide +kernel
      have hl : raw1380step0Labels = raw1380Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1380 raw1380Labels permutation32 permutation4
    mixedMoment B raw1380step0 raw1380step0Labels = mixedMoment B raw1380step1 raw1380step1Labels := by
      have ha : raw1380step1 = raw1380step0 := by apply Matrix.ext; unfold raw1380step1 raw1380step0; decide +kernel
      have hl : raw1380step0Labels = labelEmbedding7 ∘ raw1380step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1380step0 raw1380step0Labels raw1380step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4551 node4551Labels := by rfl

theorem canonical1381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1381 raw1381Labels = mixedMoment B node1136 node1136Labels := by
  calc
    mixedMoment B raw1381 raw1381Labels = mixedMoment B raw1381step0 raw1381step0Labels := by
      have ha : raw1381step0 = (fun i j => raw1381 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1381step0 raw1381; decide +kernel
      have hl : raw1381step0Labels = raw1381Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1381 raw1381Labels permutation32 permutation4
    _ = mixedMoment B node1136 node1136Labels := by rfl

theorem canonical1382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1382 raw1382Labels = mixedMoment B node3273 node3273Labels := by
  calc
    mixedMoment B raw1382 raw1382Labels = mixedMoment B raw1382step0 raw1382step0Labels := by
      have ha : raw1382step0 = (fun i j => raw1382 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1382step0 raw1382; decide +kernel
      have hl : raw1382step0Labels = raw1382Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1382 raw1382Labels permutation32 permutation6
    mixedMoment B raw1382step0 raw1382step0Labels = mixedMoment B raw1382step1 raw1382step1Labels := by
      have ha : raw1382step1 = -raw1382step0 := by apply Matrix.ext; change ∀ i j, raw1382step1 i j = -(raw1382step0 i j); unfold raw1382step1 raw1382step0; decide +kernel
      have hl : raw1382step1Labels = raw1382step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1382step1 raw1382step1Labels = mixedMoment B raw1382step2 raw1382step2Labels := by
      have ha : raw1382step2 = raw1382step1 := by apply Matrix.ext; unfold raw1382step2 raw1382step1; decide +kernel
      have hl : raw1382step1Labels = labelEmbedding1 ∘ raw1382step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1382step1 raw1382step1Labels raw1382step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3273 node3273Labels := by rfl

theorem canonical1383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1383 raw1383Labels = mixedMoment B node4553 node4553Labels := by
  calc
    mixedMoment B raw1383 raw1383Labels = mixedMoment B raw1383step0 raw1383step0Labels := by
      have ha : raw1383step0 = (fun i j => raw1383 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1383step0 raw1383; decide +kernel
      have hl : raw1383step0Labels = raw1383Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1383 raw1383Labels permutation32 permutation4
    mixedMoment B raw1383step0 raw1383step0Labels = mixedMoment B raw1383step1 raw1383step1Labels := by
      have ha : raw1383step1 = raw1383step0 := by apply Matrix.ext; unfold raw1383step1 raw1383step0; decide +kernel
      have hl : raw1383step0Labels = labelEmbedding7 ∘ raw1383step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1383step0 raw1383step0Labels raw1383step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4553 node4553Labels := by rfl

theorem canonical1384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1384 raw1384Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw1384 raw1384Labels = mixedMoment B raw1384step0 raw1384step0Labels := by
      have ha : raw1384step0 = (fun i j => raw1384 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1384step0 raw1384; decide +kernel
      have hl : raw1384step0Labels = raw1384Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1384 raw1384Labels permutation32 permutation4
    _ = mixedMoment B node1138 node1138Labels := by rfl

theorem canonical1385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1385 raw1385Labels = mixedMoment B node3270 node3270Labels := by
  calc
    mixedMoment B raw1385 raw1385Labels = mixedMoment B raw1385step0 raw1385step0Labels := by
      have ha : raw1385step0 = (fun i j => raw1385 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1385step0 raw1385; decide +kernel
      have hl : raw1385step0Labels = raw1385Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1385 raw1385Labels permutation34 permutation6
    mixedMoment B raw1385step0 raw1385step0Labels = mixedMoment B raw1385step1 raw1385step1Labels := by
      have ha : raw1385step1 = -raw1385step0 := by apply Matrix.ext; change ∀ i j, raw1385step1 i j = -(raw1385step0 i j); unfold raw1385step1 raw1385step0; decide +kernel
      have hl : raw1385step1Labels = raw1385step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1385step1 raw1385step1Labels = mixedMoment B raw1385step2 raw1385step2Labels := by
      have ha : raw1385step2 = raw1385step1 := by apply Matrix.ext; unfold raw1385step2 raw1385step1; decide +kernel
      have hl : raw1385step1Labels = labelEmbedding1 ∘ raw1385step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1385step1 raw1385step1Labels raw1385step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3270 node3270Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical1452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1452 raw1452Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw1452 raw1452Labels = mixedMoment B raw1452step0 raw1452step0Labels := by
      have ha : raw1452step0 = (fun i j => raw1452 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1452step0 raw1452; decide +kernel
      have hl : raw1452step0Labels = raw1452Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1452 raw1452Labels permutation8 permutation4
    mixedMoment B raw1452step0 raw1452step0Labels = mixedMoment B raw1452step1 raw1452step1Labels := by
      have ha : raw1452step1 = raw1452step0 := by apply Matrix.ext; unfold raw1452step1 raw1452step0; decide +kernel
      have hl : raw1452step0Labels = labelEmbedding7 ∘ raw1452step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1452step0 raw1452step0Labels raw1452step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4623 node4623Labels := by rfl

theorem canonical1453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1453 raw1453Labels = mixedMoment B node1300 node1300Labels := by
  calc
    mixedMoment B raw1453 raw1453Labels = mixedMoment B raw1453step0 raw1453step0Labels := by
      have ha : raw1453step0 = (fun i j => raw1453 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1453step0 raw1453; decide +kernel
      have hl : raw1453step0Labels = raw1453Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1453 raw1453Labels permutation8 permutation4
    _ = mixedMoment B node1300 node1300Labels := by rfl

theorem canonical1454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1454 raw1454Labels = mixedMoment B node3308 node3308Labels := by
  calc
    mixedMoment B raw1454 raw1454Labels = mixedMoment B raw1454step0 raw1454step0Labels := by
      have ha : raw1454step0 = (fun i j => raw1454 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1454step0 raw1454; decide +kernel
      have hl : raw1454step0Labels = raw1454Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1454 raw1454Labels permutation8 permutation6
    mixedMoment B raw1454step0 raw1454step0Labels = mixedMoment B raw1454step1 raw1454step1Labels := by
      have ha : raw1454step1 = -raw1454step0 := by apply Matrix.ext; change ∀ i j, raw1454step1 i j = -(raw1454step0 i j); unfold raw1454step1 raw1454step0; decide +kernel
      have hl : raw1454step1Labels = raw1454step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1454step1 raw1454step1Labels = mixedMoment B raw1454step2 raw1454step2Labels := by
      have ha : raw1454step2 = raw1454step1 := by apply Matrix.ext; unfold raw1454step2 raw1454step1; decide +kernel
      have hl : raw1454step1Labels = labelEmbedding1 ∘ raw1454step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1454step1 raw1454step1Labels raw1454step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3308 node3308Labels := by rfl

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

theorem canonical18303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18303 raw18303Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw18303 raw18303Labels = mixedMoment B raw18303step0 raw18303step0Labels := by
      have hz : ∀ j, raw18303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18303step0 = (fun i j => raw18303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18303step0 raw18303; decide +kernel
      have hl : raw18303step0Labels = raw18303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18303 raw18303Labels permutation346 hz
    _ = mixedMoment B node5387 node5387Labels := by rfl

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

theorem canonical18304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18304 raw18304Labels = mixedMoment B node5415 node5415Labels := by
  calc
    _ = mixedMoment B node5415 node5415Labels := by rfl

theorem canonical18305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18305 raw18305Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw18305 raw18305Labels = mixedMoment B raw18305step0 raw18305step0Labels := by
      have hz : ∀ j, raw18305 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18305step0 = (fun i j => raw18305 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18305step0 raw18305; decide +kernel
      have hl : raw18305step0Labels = raw18305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18305 raw18305Labels permutation520 hz
    mixedMoment B raw18305step0 raw18305step0Labels = mixedMoment B raw18305step1 raw18305step1Labels := by
      have hz : ∀ j, raw18305step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18305step1 = (fun i j => raw18305step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18305step1 raw18305step0; decide +kernel
      have hl : raw18305step1Labels = raw18305step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18305step0 raw18305step0Labels permutation80 hz
    _ = mixedMoment B node5441 node5441Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1941 raw1941Labels = mixedMoment B node4967 node4967Labels := by
  calc
    mixedMoment B raw1941 raw1941Labels = mixedMoment B raw1941step0 raw1941step0Labels := by
      have ha : raw1941step0 = (fun i j => raw1941 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1941step0 raw1941; decide +kernel
      have hl : raw1941step0Labels = raw1941Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1941 raw1941Labels permutation152 permutation5
    mixedMoment B raw1941step0 raw1941step0Labels = mixedMoment B raw1941step1 raw1941step1Labels := by
      have ha : raw1941step1 = raw1941step0 := by apply Matrix.ext; unfold raw1941step1 raw1941step0; decide +kernel
      have hl : raw1941step0Labels = labelEmbedding8 ∘ raw1941step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1941step0 raw1941step0Labels raw1941step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4967 node4967Labels := by rfl

theorem canonical1942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1942 raw1942Labels = mixedMoment B node2814 node2814Labels := by
  calc
    mixedMoment B raw1942 raw1942Labels = mixedMoment B raw1942step0 raw1942step0Labels := by
      have ha : raw1942step0 = (fun i j => raw1942 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1942step0 raw1942; decide +kernel
      have hl : raw1942step0Labels = raw1942Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1942 raw1942Labels permutation152 permutation4
    _ = mixedMoment B node2814 node2814Labels := by rfl

theorem canonical1943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1943 raw1943Labels = mixedMoment B node3585 node3585Labels := by
  calc
    mixedMoment B raw1943 raw1943Labels = mixedMoment B raw1943step0 raw1943step0Labels := by
      have ha : raw1943step0 = (fun i j => raw1943 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1943step0 raw1943; decide +kernel
      have hl : raw1943step0Labels = raw1943Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1943 raw1943Labels permutation152 permutation3
    mixedMoment B raw1943step0 raw1943step0Labels = mixedMoment B raw1943step1 raw1943step1Labels := by
      have ha : raw1943step1 = -raw1943step0 := by apply Matrix.ext; change ∀ i j, raw1943step1 i j = -(raw1943step0 i j); unfold raw1943step1 raw1943step0; decide +kernel
      have hl : raw1943step1Labels = raw1943step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1943step1 raw1943step1Labels = mixedMoment B raw1943step2 raw1943step2Labels := by
      have ha : raw1943step2 = raw1943step1 := by apply Matrix.ext; unfold raw1943step2 raw1943step1; decide +kernel
      have hl : raw1943step1Labels = labelEmbedding1 ∘ raw1943step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1943step1 raw1943step1Labels raw1943step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3585 node3585Labels := by rfl

theorem canonical1950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1950 raw1950Labels = mixedMoment B node4970 node4970Labels := by
  calc
    mixedMoment B raw1950 raw1950Labels = mixedMoment B raw1950step0 raw1950step0Labels := by
      have ha : raw1950step0 = (fun i j => raw1950 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1950step0 raw1950; decide +kernel
      have hl : raw1950step0Labels = raw1950Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1950 raw1950Labels permutation32 permutation5
    mixedMoment B raw1950step0 raw1950step0Labels = mixedMoment B raw1950step1 raw1950step1Labels := by
      have ha : raw1950step1 = raw1950step0 := by apply Matrix.ext; unfold raw1950step1 raw1950step0; decide +kernel
      have hl : raw1950step0Labels = labelEmbedding8 ∘ raw1950step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1950step0 raw1950step0Labels raw1950step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4970 node4970Labels := by rfl

theorem canonical1951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1951 raw1951Labels = mixedMoment B node2815 node2815Labels := by
  calc
    mixedMoment B raw1951 raw1951Labels = mixedMoment B raw1951step0 raw1951step0Labels := by
      have ha : raw1951step0 = (fun i j => raw1951 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1951step0 raw1951; decide +kernel
      have hl : raw1951step0Labels = raw1951Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1951 raw1951Labels permutation32 permutation4
    _ = mixedMoment B node2815 node2815Labels := by rfl

theorem canonical1952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1952 raw1952Labels = mixedMoment B node3588 node3588Labels := by
  calc
    mixedMoment B raw1952 raw1952Labels = mixedMoment B raw1952step0 raw1952step0Labels := by
      have ha : raw1952step0 = (fun i j => raw1952 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1952step0 raw1952; decide +kernel
      have hl : raw1952step0Labels = raw1952Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1952 raw1952Labels permutation32 permutation3
    mixedMoment B raw1952step0 raw1952step0Labels = mixedMoment B raw1952step1 raw1952step1Labels := by
      have ha : raw1952step1 = -raw1952step0 := by apply Matrix.ext; change ∀ i j, raw1952step1 i j = -(raw1952step0 i j); unfold raw1952step1 raw1952step0; decide +kernel
      have hl : raw1952step1Labels = raw1952step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1952step1 raw1952step1Labels = mixedMoment B raw1952step2 raw1952step2Labels := by
      have ha : raw1952step2 = raw1952step1 := by apply Matrix.ext; unfold raw1952step2 raw1952step1; decide +kernel
      have hl : raw1952step1Labels = labelEmbedding1 ∘ raw1952step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1952step1 raw1952step1Labels raw1952step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3588 node3588Labels := by rfl

theorem canonical1959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1959 raw1959Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw1959 raw1959Labels = mixedMoment B raw1959step0 raw1959step0Labels := by
      have ha : raw1959step0 = (fun i j => raw1959 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1959step0 raw1959; decide +kernel
      have hl : raw1959step0Labels = raw1959Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1959 raw1959Labels permutation32 permutation5
    mixedMoment B raw1959step0 raw1959step0Labels = mixedMoment B raw1959step1 raw1959step1Labels := by
      have ha : raw1959step1 = raw1959step0 := by apply Matrix.ext; unfold raw1959step1 raw1959step0; decide +kernel
      have hl : raw1959step0Labels = labelEmbedding8 ∘ raw1959step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1959step0 raw1959step0Labels raw1959step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4973 node4973Labels := by rfl

theorem canonical1960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1960 raw1960Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw1960 raw1960Labels = mixedMoment B raw1960step0 raw1960step0Labels := by
      have ha : raw1960step0 = (fun i j => raw1960 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1960step0 raw1960; decide +kernel
      have hl : raw1960step0Labels = raw1960Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1960 raw1960Labels permutation33 permutation4
    _ = mixedMoment B node2817 node2817Labels := by rfl

theorem canonical1961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1961 raw1961Labels = mixedMoment B node3591 node3591Labels := by
  calc
    mixedMoment B raw1961 raw1961Labels = mixedMoment B raw1961step0 raw1961step0Labels := by
      have ha : raw1961step0 = (fun i j => raw1961 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1961step0 raw1961; decide +kernel
      have hl : raw1961step0Labels = raw1961Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1961 raw1961Labels permutation32 permutation3
    mixedMoment B raw1961step0 raw1961step0Labels = mixedMoment B raw1961step1 raw1961step1Labels := by
      have ha : raw1961step1 = -raw1961step0 := by apply Matrix.ext; change ∀ i j, raw1961step1 i j = -(raw1961step0 i j); unfold raw1961step1 raw1961step0; decide +kernel
      have hl : raw1961step1Labels = raw1961step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1961step1 raw1961step1Labels = mixedMoment B raw1961step2 raw1961step2Labels := by
      have ha : raw1961step2 = raw1961step1 := by apply Matrix.ext; unfold raw1961step2 raw1961step1; decide +kernel
      have hl : raw1961step1Labels = labelEmbedding1 ∘ raw1961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1961step1 raw1961step1Labels raw1961step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3591 node3591Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20358 raw20358Labels = mixedMoment B node4551 node4551Labels := by
  calc
    mixedMoment B raw20358 raw20358Labels = mixedMoment B raw20358step0 raw20358step0Labels := by
      have hz : ∀ j, raw20358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20358step0 = (fun i j => raw20358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20358step0 raw20358; decide +kernel
      have hl : raw20358step0Labels = raw20358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20358 raw20358Labels permutation346 hz
    mixedMoment B raw20358step0 raw20358step0Labels = mixedMoment B raw20358step1 raw20358step1Labels := by
      have ha : raw20358step1 = (fun i j => raw20358step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20358step1 raw20358step0; decide +kernel
      have hl : raw20358step1Labels = raw20358step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20358step0 raw20358step0Labels permutation32 permutation3
    mixedMoment B raw20358step1 raw20358step1Labels = mixedMoment B raw20358step2 raw20358step2Labels := by
      have ha : raw20358step2 = raw20358step1 := by apply Matrix.ext; unfold raw20358step2 raw20358step1; decide +kernel
      have hl : raw20358step1Labels = labelEmbedding6 ∘ raw20358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20358step1 raw20358step1Labels raw20358step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4551 node4551Labels := by rfl

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

theorem canonical2139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2139 raw2139Labels = mixedMoment B node5114 node5114Labels := by
  calc
    mixedMoment B raw2139 raw2139Labels = mixedMoment B raw2139step0 raw2139step0Labels := by
      have ha : raw2139step0 = (fun i j => raw2139 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2139step0 raw2139; decide +kernel
      have hl : raw2139step0Labels = raw2139Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2139 raw2139Labels permutation152 permutation5
    mixedMoment B raw2139step0 raw2139step0Labels = mixedMoment B raw2139step1 raw2139step1Labels := by
      have ha : raw2139step1 = raw2139step0 := by apply Matrix.ext; unfold raw2139step1 raw2139step0; decide +kernel
      have hl : raw2139step0Labels = labelEmbedding8 ∘ raw2139step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2139step0 raw2139step0Labels raw2139step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5114 node5114Labels := by rfl

theorem canonical2140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2140 raw2140Labels = mixedMoment B node2896 node2896Labels := by
  calc
    mixedMoment B raw2140 raw2140Labels = mixedMoment B raw2140step0 raw2140step0Labels := by
      have ha : raw2140step0 = (fun i j => raw2140 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2140step0 raw2140; decide +kernel
      have hl : raw2140step0Labels = raw2140Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2140 raw2140Labels permutation153 permutation4
    _ = mixedMoment B node2896 node2896Labels := by rfl

theorem canonical2141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2141 raw2141Labels = mixedMoment B node3597 node3597Labels := by
  calc
    mixedMoment B raw2141 raw2141Labels = mixedMoment B raw2141step0 raw2141step0Labels := by
      have ha : raw2141step0 = (fun i j => raw2141 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2141step0 raw2141; decide +kernel
      have hl : raw2141step0Labels = raw2141Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2141 raw2141Labels permutation152 permutation3
    mixedMoment B raw2141step0 raw2141step0Labels = mixedMoment B raw2141step1 raw2141step1Labels := by
      have ha : raw2141step1 = -raw2141step0 := by apply Matrix.ext; change ∀ i j, raw2141step1 i j = -(raw2141step0 i j); unfold raw2141step1 raw2141step0; decide +kernel
      have hl : raw2141step1Labels = raw2141step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2141step1 raw2141step1Labels = mixedMoment B raw2141step2 raw2141step2Labels := by
      have ha : raw2141step2 = raw2141step1 := by apply Matrix.ext; unfold raw2141step2 raw2141step1; decide +kernel
      have hl : raw2141step1Labels = labelEmbedding1 ∘ raw2141step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2141step1 raw2141step1Labels raw2141step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3597 node3597Labels := by rfl

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

theorem canonical2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2202 raw2202Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw2202 raw2202Labels = mixedMoment B raw2202step0 raw2202step0Labels := by
      have ha : raw2202step0 = (fun i j => raw2202 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2202step0 raw2202; decide +kernel
      have hl : raw2202step0Labels = raw2202Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2202 raw2202Labels permutation32 permutation5
    mixedMoment B raw2202step0 raw2202step0Labels = mixedMoment B raw2202step1 raw2202step1Labels := by
      have ha : raw2202step1 = raw2202step0 := by apply Matrix.ext; unfold raw2202step1 raw2202step0; decide +kernel
      have hl : raw2202step0Labels = labelEmbedding8 ∘ raw2202step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2202step0 raw2202step0Labels raw2202step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

theorem canonical2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2203 raw2203Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw2203 raw2203Labels = mixedMoment B raw2203step0 raw2203step0Labels := by
      have ha : raw2203step0 = (fun i j => raw2203 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2203step0 raw2203; decide +kernel
      have hl : raw2203step0Labels = raw2203Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2203 raw2203Labels permutation34 permutation4
    _ = mixedMoment B node2954 node2954Labels := by rfl

theorem canonical2204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2204 raw2204Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw2204 raw2204Labels = mixedMoment B raw2204step0 raw2204step0Labels := by
      have ha : raw2204step0 = (fun i j => raw2204 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2204step0 raw2204; decide +kernel
      have hl : raw2204step0Labels = raw2204Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2204 raw2204Labels permutation33 permutation3
    mixedMoment B raw2204step0 raw2204step0Labels = mixedMoment B raw2204step1 raw2204step1Labels := by
      have ha : raw2204step1 = -raw2204step0 := by apply Matrix.ext; change ∀ i j, raw2204step1 i j = -(raw2204step0 i j); unfold raw2204step1 raw2204step0; decide +kernel
      have hl : raw2204step1Labels = raw2204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2204step1 raw2204step1Labels = mixedMoment B raw2204step2 raw2204step2Labels := by
      have ha : raw2204step2 = raw2204step1 := by apply Matrix.ext; unfold raw2204step2 raw2204step1; decide +kernel
      have hl : raw2204step1Labels = labelEmbedding1 ∘ raw2204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2204step1 raw2204step1Labels raw2204step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

theorem canonical2205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2205 raw2205Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw2205 raw2205Labels = mixedMoment B raw2205step0 raw2205step0Labels := by
      have ha : raw2205step0 = (fun i j => raw2205 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2205step0 raw2205; decide +kernel
      have hl : raw2205step0Labels = raw2205Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2205 raw2205Labels permutation8 permutation4
    mixedMoment B raw2205step0 raw2205step0Labels = mixedMoment B raw2205step1 raw2205step1Labels := by
      have ha : raw2205step1 = raw2205step0 := by apply Matrix.ext; unfold raw2205step1 raw2205step0; decide +kernel
      have hl : raw2205step0Labels = labelEmbedding7 ∘ raw2205step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2205step0 raw2205step0Labels raw2205step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5171 node5171Labels := by rfl

theorem canonical2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2206 raw2206Labels = mixedMoment B node2598 node2598Labels := by
  calc
    mixedMoment B raw2206 raw2206Labels = mixedMoment B raw2206step0 raw2206step0Labels := by
      have ha : raw2206step0 = (fun i j => raw2206 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2206step0 raw2206; decide +kernel
      have hl : raw2206step0Labels = raw2206Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2206 raw2206Labels permutation8 permutation4
    _ = mixedMoment B node2598 node2598Labels := by rfl

theorem canonical2207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2207 raw2207Labels = mixedMoment B node3608 node3608Labels := by
  calc
    mixedMoment B raw2207 raw2207Labels = mixedMoment B raw2207step0 raw2207step0Labels := by
      have ha : raw2207step0 = (fun i j => raw2207 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2207step0 raw2207; decide +kernel
      have hl : raw2207step0Labels = raw2207Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2207 raw2207Labels permutation31 permutation6
    mixedMoment B raw2207step0 raw2207step0Labels = mixedMoment B raw2207step1 raw2207step1Labels := by
      have ha : raw2207step1 = raw2207step0 := by apply Matrix.ext; unfold raw2207step1 raw2207step0; decide +kernel
      have hl : raw2207step0Labels = labelEmbedding1 ∘ raw2207step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2207step0 raw2207step0Labels raw2207step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3608 node3608Labels := by rfl

theorem canonical2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2214 raw2214Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw2214 raw2214Labels = mixedMoment B raw2214step0 raw2214step0Labels := by
      have ha : raw2214step0 = (fun i j => raw2214 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2214step0 raw2214; decide +kernel
      have hl : raw2214step0Labels = raw2214Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2214 raw2214Labels permutation8 permutation4
    mixedMoment B raw2214step0 raw2214step0Labels = mixedMoment B raw2214step1 raw2214step1Labels := by
      have ha : raw2214step1 = raw2214step0 := by apply Matrix.ext; unfold raw2214step1 raw2214step0; decide +kernel
      have hl : raw2214step0Labels = labelEmbedding7 ∘ raw2214step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2214step0 raw2214step0Labels raw2214step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

theorem canonical2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2215 raw2215Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw2215 raw2215Labels = mixedMoment B raw2215step0 raw2215step0Labels := by
      have ha : raw2215step0 = (fun i j => raw2215 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2215step0 raw2215; decide +kernel
      have hl : raw2215step0Labels = raw2215Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2215 raw2215Labels permutation8 permutation4
    _ = mixedMoment B node2604 node2604Labels := by rfl

theorem canonical2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2216 raw2216Labels = mixedMoment B node3614 node3614Labels := by
  calc
    mixedMoment B raw2216 raw2216Labels = mixedMoment B raw2216step0 raw2216step0Labels := by
      have ha : raw2216step0 = (fun i j => raw2216 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2216step0 raw2216; decide +kernel
      have hl : raw2216step0Labels = raw2216Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2216 raw2216Labels permutation8 permutation6
    mixedMoment B raw2216step0 raw2216step0Labels = mixedMoment B raw2216step1 raw2216step1Labels := by
      have ha : raw2216step1 = -raw2216step0 := by apply Matrix.ext; change ∀ i j, raw2216step1 i j = -(raw2216step0 i j); unfold raw2216step1 raw2216step0; decide +kernel
      have hl : raw2216step1Labels = raw2216step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2216step1 raw2216step1Labels = mixedMoment B raw2216step2 raw2216step2Labels := by
      have ha : raw2216step2 = raw2216step1 := by apply Matrix.ext; unfold raw2216step2 raw2216step1; decide +kernel
      have hl : raw2216step1Labels = labelEmbedding1 ∘ raw2216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2216step1 raw2216step1Labels raw2216step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3614 node3614Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22480 raw22480Labels = mixedMoment B node4553 node4553Labels := by
  calc
    mixedMoment B raw22480 raw22480Labels = mixedMoment B raw22480step0 raw22480step0Labels := by
      have hz : ∀ j, raw22480 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22480step0 = (fun i j => raw22480 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22480step0 raw22480; decide +kernel
      have hl : raw22480step0Labels = raw22480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22480 raw22480Labels permutation346 hz
    mixedMoment B raw22480step0 raw22480step0Labels = mixedMoment B raw22480step1 raw22480step1Labels := by
      have ha : raw22480step1 = (fun i j => raw22480step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22480step1 raw22480step0; decide +kernel
      have hl : raw22480step1Labels = raw22480step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22480step0 raw22480step0Labels permutation33 permutation3
    mixedMoment B raw22480step1 raw22480step1Labels = mixedMoment B raw22480step2 raw22480step2Labels := by
      have ha : raw22480step2 = raw22480step1 := by apply Matrix.ext; unfold raw22480step2 raw22480step1; decide +kernel
      have hl : raw22480step1Labels = labelEmbedding6 ∘ raw22480step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22480step1 raw22480step1Labels raw22480step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4553 node4553Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical188
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24105 raw24105Labels = mixedMoment B node4550 node4550Labels := by
  calc
    mixedMoment B raw24105 raw24105Labels = mixedMoment B raw24105step0 raw24105step0Labels := by
      have ha : raw24105step0 = (fun i j => raw24105 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24105step0 raw24105; decide +kernel
      have hl : raw24105step0Labels = raw24105Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24105 raw24105Labels permutation152 permutation3
    mixedMoment B raw24105step0 raw24105step0Labels = mixedMoment B raw24105step1 raw24105step1Labels := by
      have ha : raw24105step1 = raw24105step0 := by apply Matrix.ext; unfold raw24105step1 raw24105step0; decide +kernel
      have hl : raw24105step0Labels = labelEmbedding6 ∘ raw24105step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24105step0 raw24105step0Labels raw24105step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4550 node4550Labels := by rfl

theorem canonical24108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24108 raw24108Labels = mixedMoment B node4553 node4553Labels := by
  calc
    mixedMoment B raw24108 raw24108Labels = mixedMoment B raw24108step0 raw24108step0Labels := by
      have hz : ∀ j, raw24108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24108step0 = (fun i j => raw24108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24108step0 raw24108; decide +kernel
      have hl : raw24108step0Labels = raw24108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24108 raw24108Labels permutation346 hz
    mixedMoment B raw24108step0 raw24108step0Labels = mixedMoment B raw24108step1 raw24108step1Labels := by
      have ha : raw24108step1 = (fun i j => raw24108step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24108step1 raw24108step0; decide +kernel
      have hl : raw24108step1Labels = raw24108step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24108step0 raw24108step0Labels permutation35 permutation3
    mixedMoment B raw24108step1 raw24108step1Labels = mixedMoment B raw24108step2 raw24108step2Labels := by
      have ha : raw24108step2 = raw24108step1 := by apply Matrix.ext; unfold raw24108step2 raw24108step1; decide +kernel
      have hl : raw24108step1Labels = labelEmbedding6 ∘ raw24108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24108step1 raw24108step1Labels raw24108step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4553 node4553Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27560 raw27560Labels = mixedMoment B node4970 node4970Labels := by
  calc
    mixedMoment B raw27560 raw27560Labels = mixedMoment B raw27560step0 raw27560step0Labels := by
      have hz : ∀ j, raw27560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27560step0 = (fun i j => raw27560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27560step0 raw27560; decide +kernel
      have hl : raw27560step0Labels = raw27560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27560 raw27560Labels permutation346 hz
    _ = mixedMoment B node4970 node4970Labels := by rfl

theorem canonical27561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27561 raw27561Labels = mixedMoment B node5113 node5113Labels := by
  calc
    _ = mixedMoment B node5113 node5113Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical230
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29509 raw29509Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw29509 raw29509Labels = mixedMoment B raw29509step0 raw29509step0Labels := by
      have hz : ∀ j, raw29509 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29509step0 = (fun i j => raw29509 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29509step0 raw29509; decide +kernel
      have hl : raw29509step0Labels = raw29509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29509 raw29509Labels permutation346 hz
    _ = mixedMoment B node4973 node4973Labels := by rfl

theorem canonical29510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29510 raw29510Labels = mixedMoment B node5114 node5114Labels := by
  calc
    _ = mixedMoment B node5114 node5114Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical250
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32031 raw32031Labels = mixedMoment B node4967 node4967Labels := by
  calc
    _ = mixedMoment B node4967 node4967Labels := by rfl

theorem canonical32032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32032 raw32032Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw32032 raw32032Labels = mixedMoment B raw32032step0 raw32032step0Labels := by
      have hz : ∀ j, raw32032 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32032step0 = (fun i j => raw32032 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32032step0 raw32032; decide +kernel
      have hl : raw32032step0Labels = raw32032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32032 raw32032Labels permutation520 hz
    _ = mixedMoment B node5168 node5168Labels := by rfl

theorem canonical32033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32033 raw32033Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw32033 raw32033Labels = mixedMoment B raw32033step0 raw32033step0Labels := by
      have hz : ∀ j, raw32033 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32033step0 = (fun i j => raw32033 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32033step0 raw32033; decide +kernel
      have hl : raw32033step0Labels = raw32033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32033 raw32033Labels permutation346 hz
    mixedMoment B raw32033step0 raw32033step0Labels = mixedMoment B raw32033step1 raw32033step1Labels := by
      have ha : raw32033step1 = (fun i j => raw32033step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32033step1 raw32033step0; decide +kernel
      have hl : raw32033step1Labels = raw32033step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32033step0 raw32033step0Labels permutation34 permutation2
    _ = mixedMoment B node4973 node4973Labels := by rfl

theorem canonical32034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32034 raw32034Labels = mixedMoment B node5114 node5114Labels := by
  calc
    mixedMoment B raw32034 raw32034Labels = mixedMoment B raw32034step0 raw32034step0Labels := by
      have ha : raw32034step0 = (fun i j => raw32034 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32034step0 raw32034; decide +kernel
      have hl : raw32034step0Labels = raw32034Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32034 raw32034Labels permutation154 permutation2
    _ = mixedMoment B node5114 node5114Labels := by rfl

theorem canonical32035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32035 raw32035Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw32035 raw32035Labels = mixedMoment B raw32035step0 raw32035step0Labels := by
      have hz : ∀ j, raw32035 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32035step0 = (fun i j => raw32035 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32035step0 raw32035; decide +kernel
      have hl : raw32035step0Labels = raw32035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32035 raw32035Labels permutation520 hz
    mixedMoment B raw32035step0 raw32035step0Labels = mixedMoment B raw32035step1 raw32035step1Labels := by
      have hz : ∀ j, raw32035step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32035step1 = (fun i j => raw32035step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32035step1 raw32035step0; decide +kernel
      have hl : raw32035step1Labels = raw32035step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32035step0 raw32035step0Labels permutation80 hz
    _ = mixedMoment B node5176 node5176Labels := by rfl

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

theorem canonical5074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5074 raw5074Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw5074 raw5074Labels = mixedMoment B raw5074step0 raw5074step0Labels := by
      have hz : ∀ j, raw5074 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5074step0 = (fun i j => raw5074 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5074step0 raw5074; decide +kernel
      have hl : raw5074step0Labels = raw5074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5074 raw5074Labels permutation520 hz
    mixedMoment B raw5074step0 raw5074step0Labels = mixedMoment B raw5074step1 raw5074step1Labels := by
      have hz : ∀ j, raw5074step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5074step1 = (fun i j => raw5074step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5074step1 raw5074step0; decide +kernel
      have hl : raw5074step1Labels = raw5074step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5074step0 raw5074step0Labels permutation80 hz
    _ = mixedMoment B node5171 node5171Labels := by rfl

theorem canonical5077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5077 raw5077Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw5077 raw5077Labels = mixedMoment B raw5077step0 raw5077step0Labels := by
      have hz : ∀ j, raw5077 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5077step0 = (fun i j => raw5077 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5077step0 raw5077; decide +kernel
      have hl : raw5077step0Labels = raw5077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5077 raw5077Labels permutation520 hz
    mixedMoment B raw5077step0 raw5077step0Labels = mixedMoment B raw5077step1 raw5077step1Labels := by
      have hz : ∀ j, raw5077step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5077step1 = (fun i j => raw5077step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5077step1 raw5077step0; decide +kernel
      have hl : raw5077step1Labels = raw5077step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5077step0 raw5077step0Labels permutation80 hz
    mixedMoment B raw5077step1 raw5077step1Labels = mixedMoment B raw5077step2 raw5077step2Labels := by
      have hz : ∀ j, raw5077step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5077step2 = (fun i j => raw5077step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5077step2 raw5077step1; decide +kernel
      have hl : raw5077step2Labels = raw5077step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5077step1 raw5077step1Labels permutation14 hz
    _ = mixedMoment B node5308 node5308Labels := by rfl

theorem canonical5079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5079 raw5079Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw5079 raw5079Labels = mixedMoment B raw5079step0 raw5079step0Labels := by
      have hz : ∀ j, raw5079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5079step0 = (fun i j => raw5079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5079step0 raw5079; decide +kernel
      have hl : raw5079step0Labels = raw5079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5079 raw5079Labels permutation434 hz
    mixedMoment B raw5079step0 raw5079step0Labels = mixedMoment B raw5079step1 raw5079step1Labels := by
      have hz : ∀ j, raw5079step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5079step1 = (fun i j => raw5079step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5079step1 raw5079step0; decide +kernel
      have hl : raw5079step1Labels = raw5079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5079step0 raw5079step0Labels permutation80 hz
    _ = mixedMoment B node5171 node5171Labels := by rfl

theorem canonical5082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5082 raw5082Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw5082 raw5082Labels = mixedMoment B raw5082step0 raw5082step0Labels := by
      have hz : ∀ j, raw5082 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5082step0 = (fun i j => raw5082 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5082step0 raw5082; decide +kernel
      have hl : raw5082step0Labels = raw5082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5082 raw5082Labels permutation434 hz
    mixedMoment B raw5082step0 raw5082step0Labels = mixedMoment B raw5082step1 raw5082step1Labels := by
      have hz : ∀ j, raw5082step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5082step1 = (fun i j => raw5082step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5082step1 raw5082step0; decide +kernel
      have hl : raw5082step1Labels = raw5082step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5082step0 raw5082step0Labels permutation80 hz
    mixedMoment B raw5082step1 raw5082step1Labels = mixedMoment B raw5082step2 raw5082step2Labels := by
      have hz : ∀ j, raw5082step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5082step2 = (fun i j => raw5082step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5082step2 raw5082step1; decide +kernel
      have hl : raw5082step2Labels = raw5082step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5082step1 raw5082step1Labels permutation14 hz
    _ = mixedMoment B node5308 node5308Labels := by rfl

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

theorem canonical10216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10216 raw10216Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw10216 raw10216Labels = mixedMoment B raw10216step0 raw10216step0Labels := by
      have hz : ∀ j, raw10216 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10216step0 = (fun i j => raw10216 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10216step0 raw10216; decide +kernel
      have hl : raw10216step0Labels = raw10216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10216 raw10216Labels permutation434 hz
    mixedMoment B raw10216step0 raw10216step0Labels = mixedMoment B raw10216step1 raw10216step1Labels := by
      have hz : ∀ j, raw10216step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10216step1 = (fun i j => raw10216step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10216step1 raw10216step0; decide +kernel
      have hl : raw10216step1Labels = raw10216step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10216step0 raw10216step0Labels permutation80 hz
    _ = mixedMoment B node5441 node5441Labels := by rfl

theorem canonical10225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10225 raw10225Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw10225 raw10225Labels = mixedMoment B raw10225step0 raw10225step0Labels := by
      have hz : ∀ j, raw10225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10225step0 = (fun i j => raw10225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10225step0 raw10225; decide +kernel
      have hl : raw10225step0Labels = raw10225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10225 raw10225Labels permutation434 hz
    _ = mixedMoment B node5168 node5168Labels := by rfl

theorem canonical10228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10228 raw10228Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw10228 raw10228Labels = mixedMoment B raw10228step0 raw10228step0Labels := by
      have hz : ∀ j, raw10228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10228step0 = (fun i j => raw10228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10228step0 raw10228; decide +kernel
      have hl : raw10228step0Labels = raw10228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10228 raw10228Labels permutation346 hz
    mixedMoment B raw10228step0 raw10228step0Labels = mixedMoment B raw10228step1 raw10228step1Labels := by
      have hz : ∀ j, raw10228step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10228step1 = (fun i j => raw10228step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10228step1 raw10228step0; decide +kernel
      have hl : raw10228step1Labels = raw10228step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10228step0 raw10228step0Labels permutation56 hz
    _ = mixedMoment B node4623 node4623Labels := by rfl

theorem canonical10230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10230 raw10230Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw10230 raw10230Labels = mixedMoment B raw10230step0 raw10230step0Labels := by
      have hz : ∀ j, raw10230 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10230step0 = (fun i j => raw10230 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10230step0 raw10230; decide +kernel
      have hl : raw10230step0Labels = raw10230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10230 raw10230Labels permutation265 hz
    _ = mixedMoment B node5168 node5168Labels := by rfl

theorem canonical10231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10231 raw10231Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw10231 raw10231Labels = mixedMoment B raw10231step0 raw10231step0Labels := by
      have hz : ∀ j, raw10231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10231step0 = (fun i j => raw10231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10231step0 raw10231; decide +kernel
      have hl : raw10231step0Labels = raw10231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10231 raw10231Labels permutation346 hz
    mixedMoment B raw10231step0 raw10231step0Labels = mixedMoment B raw10231step1 raw10231step1Labels := by
      have hz : ∀ j, raw10231step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10231step1 = (fun i j => raw10231step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10231step1 raw10231step0; decide +kernel
      have hl : raw10231step1Labels = raw10231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10231step0 raw10231step0Labels permutation56 hz
    _ = mixedMoment B node5306 node5306Labels := by rfl

theorem canonical10233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10233 raw10233Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw10233 raw10233Labels = mixedMoment B raw10233step0 raw10233step0Labels := by
      have hz : ∀ j, raw10233 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10233step0 = (fun i j => raw10233 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10233step0 raw10233; decide +kernel
      have hl : raw10233step0Labels = raw10233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10233 raw10233Labels permutation434 hz
    mixedMoment B raw10233step0 raw10233step0Labels = mixedMoment B raw10233step1 raw10233step1Labels := by
      have hz : ∀ j, raw10233step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10233step1 = (fun i j => raw10233step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10233step1 raw10233step0; decide +kernel
      have hl : raw10233step1Labels = raw10233step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10233step0 raw10233step0Labels permutation80 hz
    _ = mixedMoment B node5176 node5176Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12080 raw12080Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw12080 raw12080Labels = mixedMoment B raw12080step0 raw12080step0Labels := by
      have hz : ∀ j, raw12080 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12080step0 = (fun i j => raw12080 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12080step0 raw12080; decide +kernel
      have hl : raw12080step0Labels = raw12080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12080 raw12080Labels permutation346 hz
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical12089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12089 raw12089Labels = mixedMoment B node5166 node5166Labels := by
  calc
    _ = mixedMoment B node5166 node5166Labels := by rfl

theorem canonical12093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12093 raw12093Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw12093 raw12093Labels = mixedMoment B raw12093step0 raw12093step0Labels := by
      have hz : ∀ j, raw12093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12093step0 = (fun i j => raw12093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12093step0 raw12093; decide +kernel
      have hl : raw12093step0Labels = raw12093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12093 raw12093Labels permutation346 hz
    mixedMoment B raw12093step0 raw12093step0Labels = mixedMoment B raw12093step1 raw12093step1Labels := by
      have ha : raw12093step1 = (fun i j => raw12093step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12093step1 raw12093step0; decide +kernel
      have hl : raw12093step1Labels = raw12093step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12093step0 raw12093step0Labels permutation35 permutation2
    _ = mixedMoment B node5170 node5170Labels := by rfl

theorem canonical12098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12098 raw12098Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw12098 raw12098Labels = mixedMoment B raw12098step0 raw12098step0Labels := by
      have hz : ∀ j, raw12098 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12098step0 = (fun i j => raw12098 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12098step0 raw12098; decide +kernel
      have hl : raw12098step0Labels = raw12098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12098 raw12098Labels permutation346 hz
    mixedMoment B raw12098step0 raw12098step0Labels = mixedMoment B raw12098step1 raw12098step1Labels := by
      have ha : raw12098step1 = (fun i j => raw12098step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12098step1 raw12098step0; decide +kernel
      have hl : raw12098step1Labels = raw12098step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12098step0 raw12098step0Labels permutation33 permutation2
    _ = mixedMoment B node5170 node5170Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical666 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw666 = injectiveMoment H node168 := by
  calc
    injectiveMoment H raw666 = injectiveMoment H raw666step0 := by
      have heq : raw666step0 = (fun i j => raw666 (permutation32 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw666 permutation32 permutation8
    _ = injectiveMoment H node168 := by rfl

theorem canonical671 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw671 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw671 = injectiveMoment H raw671step0 := by
      have heq : raw671step0 = -raw671 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw671).symm
    injectiveMoment H raw671step0 = injectiveMoment H raw671step1 := by
      have heq : raw671step1 = (fun i j => raw671step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw671step0 permutation9 permutation8
    _ = injectiveMoment H node169 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7685 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7685 = injectiveMoment H raw7685step0 := by
      have hz : ∀ j, raw7685 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7685step0 = (fun i j => raw7685 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7685 permutation27 hz
    injectiveMoment H raw7685step0 = injectiveMoment H raw7685step1 := by
      have heq : raw7685step1 = (fun i j => raw7685step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7685step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw841 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw841 = injectiveMoment H raw841step0 := by
      have heq : raw841step0 = raw841.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw841).symm
    injectiveMoment H raw841step0 = injectiveMoment H raw841step1 := by
      have heq : raw841step1 = (fun i j => raw841step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw841step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

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

theorem canonical869 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw869 = injectiveMoment H node24 := by
  rfl

theorem canonical872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw872 = injectiveMoment H node25 := by
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

theorem canonical900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw900 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw900 = injectiveMoment H raw900step0 := by
      have hz : ∀ j, raw900 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw900step0 = (fun i j => raw900 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw900 permutation5 hz
    _ = injectiveMoment H node3 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical174 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw174 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw174 = injectiveMoment H raw174step0 := by
      have heq : raw174step0 = -raw174 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw174).symm
    injectiveMoment H raw174step0 = injectiveMoment H raw174step1 := by
      have heq : raw174step1 = (fun i j => raw174step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw174step0 permutation9 permutation8
    _ = injectiveMoment H node145 := by rfl

theorem canonical180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw180 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw180 = injectiveMoment H raw180step0 := by
      have heq : raw180step0 = raw180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw180).symm
    _ = injectiveMoment H node9 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw208 = injectiveMoment H node16 := by
  rfl

theorem canonical211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw211 = injectiveMoment H node8 := by
  rfl

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
  rfl

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
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

theorem sound2 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node2 = Sparse.eval value2 (momentVector H) := by
  have hc : momentVector H 6 = injectiveMoment H node2 := rfl
  simp [value2, Sparse.eval, hc]

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

theorem sound8 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node8 = Sparse.eval value8 (momentVector H) := by
  have heq : pivotMatrix8 = (fun u v => node8 (pivotPermutation8 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node8 = injectiveMoment H pivotMatrix8 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix8 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix8 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (0 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (1 : Fin 2) = raw215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical215 hH).trans (sound2 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node8 + (injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value8, value2, value3, Sparse.eval] at hc ⊢
  linarith

theorem sound9 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node9 = Sparse.eval value9 (momentVector H) := by
  have hc : momentVector H 5 = injectiveMoment H node9 := rfl
  simp [value9, Sparse.eval, hc]

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

theorem sound16 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node16 = Sparse.eval value16 (momentVector H) := by
  have heq : pivotMatrix16 = (fun u v => node16 (pivotPermutation16 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node16 = injectiveMoment H pivotMatrix16 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix16 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix16 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (1 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (2 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node16 + (injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value16, value10, value8, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound24 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node24 = Sparse.eval value24 (momentVector H) := by
  have heq : pivotMatrix24 = (fun u v => node24 (pivotPermutation24 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node24 = injectiveMoment H pivotMatrix24 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix24 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix24 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix24 (0 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix24 (0 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix24 (1 : Fin 3)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix24 (1 : Fin 3) = raw900 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical900 hH).trans (sound3 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix24 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix24 (2 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node24 + (injectiveMoment H (mergeFirst pivotMatrix24 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix24 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix24 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value24, value10, value3, value8, Sparse.eval] at hc ⊢
  linarith

theorem sound25 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node25 = Sparse.eval value25 (momentVector H) := by
  have heq : pivotMatrix25 = (fun u v => node25 (pivotPermutation25 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node25 = injectiveMoment H pivotMatrix25 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix25 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix25 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix25 (0 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (0 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix25 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (1 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix25 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (2 : Fin 3) = raw924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical924 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node25 + (injectiveMoment H (mergeFirst pivotMatrix25 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix25 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix25 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value25, value10, value9, Sparse.eval] at hc ⊢
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

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound52 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node52 = Sparse.eval value52 (momentVector H) := by
  have heq : pivotMatrix52 = (fun u v => node52.transpose (pivotPermutation52 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node52 = injectiveMoment H pivotMatrix52 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix52 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix52 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (0 : Fin 2) = raw180 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical180 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (1 : Fin 2) = raw841 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical841 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node52 + (injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value52, value10, value9, Sparse.eval] at hc ⊢
  linarith

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1420 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1420 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1420 = injectiveMoment H raw1420step0 := by
      have heq : raw1420step0 = raw1420.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1420).symm
    injectiveMoment H raw1420step0 = injectiveMoment H raw1420step1 := by
      have heq : raw1420step1 = (fun i j => raw1420step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1420step0 permutation7 permutation6
    _ = injectiveMoment H node52 := by rfl

theorem canonical1435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1435 = injectiveMoment H node31 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2783 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2783 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw2783 = injectiveMoment H raw2783step0 := by
      have heq : raw2783step0 = raw2783.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2783).symm
    injectiveMoment H raw2783step0 = injectiveMoment H raw2783step1 := by
      have hz : ∀ i, raw2783step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw2783step1 = (fun i j => raw2783step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2783step0 permutation5 hz
    injectiveMoment H raw2783step1 = injectiveMoment H raw2783step2 := by
      have heq : raw2783step2 = (fun i j => raw2783step1 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2783step1 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

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

theorem sound145 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node145 = Sparse.eval value145 (momentVector H) := by
  have heq : pivotMatrix145 = (fun u v => node145 (pivotPermutation145 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node145 = injectiveMoment H pivotMatrix145 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix145 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix145 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix145 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (0 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix145 (1 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (1 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix145 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (2 : Fin 3) = raw1420 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1420 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node145 + (injectiveMoment H (mergeFirst pivotMatrix145 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix145 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix145 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value145, value31, value52, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound168 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node168 = Sparse.eval value168 (momentVector H) := by
  have heq : pivotMatrix168 = (fun u v => node168 (pivotPermutation168 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node168 = injectiveMoment H pivotMatrix168 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix168 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix168 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix168 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix168 (0 : Fin 3) = raw1420 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1420 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix168 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix168 (1 : Fin 3) = raw2783 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2783 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix168 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix168 (2 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node168 + (injectiveMoment H (mergeFirst pivotMatrix168 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix168 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix168 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value168, value10, value52, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound169 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node169 = Sparse.eval value169 (momentVector H) := by
  have heq : pivotMatrix169 = (fun u v => node169 (pivotPermutation169 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node169 = injectiveMoment H pivotMatrix169 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix169 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix169 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix169 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (0 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix169 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (1 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix169 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node169 + (injectiveMoment H (mergeFirst pivotMatrix169 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix169 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix169 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value169, value31, value36, value57, Sparse.eval] at hc ⊢
  linarith

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair338 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node338 node338Labels = Sparse.eval singlePairValue338 (familyPairVector B) := by
  have hp := single_label_three B hB node338
  have hl : node338Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node338 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node338 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node338 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node338 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node338 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node338 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node338 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node338 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node338 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node338 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node338 (EqualityPatterns.family3.label 3) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node338 PairSemantics.raw869; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node338 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value168 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node338 (EqualityPatterns.family3.label 4) = PairSemantics.raw666 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node338 PairSemantics.raw666; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical666 hH).trans (PairSemantics.sound168 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue338, PairSemantics.value0, PairSemantics.value4, PairSemantics.value24, PairSemantics.value65, PairSemantics.value168, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node343 node343Labels = Sparse.eval singlePairValue343 (familyPairVector B) := by
  have hp := single_label_three B hB node343
  have hl : node343Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node343 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node343 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 2) = PairSemantics.raw7685 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node343 PairSemantics.raw7685; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7685 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node343 PairSemantics.raw872; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value169 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 4) = PairSemantics.raw671 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node343 PairSemantics.raw671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical671 hH).trans (PairSemantics.sound169 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue343, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value25, PairSemantics.value169, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair156 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node156 node156Labels = Sparse.eval singlePairValue156 (familyPairVector B) := by
  have hp := single_label_three B hB node156
  have hl : node156Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node156 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node156 PairSemantics.raw5169
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 2) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node156 PairSemantics.raw5204
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 3) = PairSemantics.raw208 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node156 PairSemantics.raw208
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical208 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value145 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 4) = PairSemantics.raw174 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node156 PairSemantics.raw174
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical174 hH).trans (PairSemantics.sound145 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue156, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value16, PairSemantics.value145, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1300 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1300 node1300Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node156 node156Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw76 singletonSmall1300
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1300) = raw76Labels := by decide +kernel
  rw [hl, canonical76 B hB] at h
  have hc0 : mixedMoment B raw76 (Fin.cases (0 : Fin 1) singletonSmall1300) =
      mixedMoment B node156 node156Labels := by
    have ha : raw76 = raw77 := by apply Matrix.ext; unfold raw76 raw77; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1300 = raw77Labels := by decide +kernel
    rw [ha, hj, canonical77 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton2598 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2598 node2598Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node338 node338Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw238 singletonSmall2598
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2598) = raw238Labels := by decide +kernel
  rw [hl, canonical238 B hB] at h
  have hc0 : mixedMoment B raw238 (Fin.cases (0 : Fin 1) singletonSmall2598) =
      mixedMoment B node338 node338Labels := by
    have ha : raw238 = raw239 := by apply Matrix.ext; unfold raw238 raw239; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2598 = raw239Labels := by decide +kernel
    rw [ha, hj, canonical239 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton2604 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2604 node2604Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node343 node343Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw246 singletonSmall2604
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2604) = raw246Labels := by decide +kernel
  rw [hl, canonical246 B hB] at h
  have hc0 : mixedMoment B raw246 (Fin.cases (0 : Fin 1) singletonSmall2604) =
      mixedMoment B node343 node343Labels := by
    have ha : raw246 = raw247 := by apply Matrix.ext; unfold raw246 raw247; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2604 = raw247Labels := by decide +kernel
    rw [ha, hj, canonical247 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4550 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4550 node4550Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1135 node1135Labels + mixedMoment B node3269 node3269Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1377 singletonSmall4550
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4550) = raw1377Labels := by decide +kernel
  rw [hl, canonical1377 B hB] at h
  have hc0 : mixedMoment B raw1377 (Fin.cases (0 : Fin 2) singletonSmall4550) =
      mixedMoment B node1135 node1135Labels := by
    have ha : raw1377 = raw1378 := by apply Matrix.ext; unfold raw1377 raw1378; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4550 = raw1378Labels := by decide +kernel
    rw [ha, hj, canonical1378 B hB]
  have hc1 : mixedMoment B raw1377 (Fin.cases (1 : Fin 2) singletonSmall4550) =
      mixedMoment B node3269 node3269Labels := by
    have ha : raw1377 = raw1379 := by apply Matrix.ext; unfold raw1377 raw1379; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4550 = raw1379Labels := by decide +kernel
    rw [ha, hj, canonical1379 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4551 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4551 node4551Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1136 node1136Labels + mixedMoment B node3273 node3273Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1380 singletonSmall4551
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4551) = raw1380Labels := by decide +kernel
  rw [hl, canonical1380 B hB] at h
  have hc0 : mixedMoment B raw1380 (Fin.cases (0 : Fin 2) singletonSmall4551) =
      mixedMoment B node1136 node1136Labels := by
    have ha : raw1380 = raw1381 := by apply Matrix.ext; unfold raw1380 raw1381; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4551 = raw1381Labels := by decide +kernel
    rw [ha, hj, canonical1381 B hB]
  have hc1 : mixedMoment B raw1380 (Fin.cases (1 : Fin 2) singletonSmall4551) =
      mixedMoment B node3273 node3273Labels := by
    have ha : raw1380 = raw1382 := by apply Matrix.ext; unfold raw1380 raw1382; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4551 = raw1382Labels := by decide +kernel
    rw [ha, hj, canonical1382 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4553 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4553 node4553Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1138 node1138Labels + mixedMoment B node3270 node3270Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1383 singletonSmall4553
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4553) = raw1383Labels := by decide +kernel
  rw [hl, canonical1383 B hB] at h
  have hc0 : mixedMoment B raw1383 (Fin.cases (0 : Fin 2) singletonSmall4553) =
      mixedMoment B node1138 node1138Labels := by
    have ha : raw1383 = raw1384 := by apply Matrix.ext; unfold raw1383 raw1384; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4553 = raw1384Labels := by decide +kernel
    rw [ha, hj, canonical1384 B hB]
  have hc1 : mixedMoment B raw1383 (Fin.cases (1 : Fin 2) singletonSmall4553) =
      mixedMoment B node3270 node3270Labels := by
    have ha : raw1383 = raw1385 := by apply Matrix.ext; unfold raw1383 raw1385; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4553 = raw1385Labels := by decide +kernel
    rw [ha, hj, canonical1385 B hB]
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

theorem singleton4623 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4623 node4623Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1300 node1300Labels + mixedMoment B node3308 node3308Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1452 singletonSmall4623
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4623) = raw1452Labels := by decide +kernel
  rw [hl, canonical1452 B hB] at h
  have hc0 : mixedMoment B raw1452 (Fin.cases (0 : Fin 2) singletonSmall4623) =
      mixedMoment B node1300 node1300Labels := by
    have ha : raw1452 = raw1453 := by apply Matrix.ext; unfold raw1452 raw1453; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4623 = raw1453Labels := by decide +kernel
    rw [ha, hj, canonical1453 B hB]
  have hc1 : mixedMoment B raw1452 (Fin.cases (1 : Fin 2) singletonSmall4623) =
      mixedMoment B node3308 node3308Labels := by
    have ha : raw1452 = raw1454 := by apply Matrix.ext; unfold raw1452 raw1454; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4623 = raw1454Labels := by decide +kernel
    rw [ha, hj, canonical1454 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4967 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4967 node4967Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2814 node2814Labels + mixedMoment B node3585 node3585Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1941 singletonSmall4967
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4967) = raw1941Labels := by decide +kernel
  rw [hl, canonical1941 B hB] at h
  have hc0 : mixedMoment B raw1941 (Fin.cases (0 : Fin 2) singletonSmall4967) =
      mixedMoment B node2814 node2814Labels := by
    have ha : raw1941 = raw1942 := by apply Matrix.ext; unfold raw1941 raw1942; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4967 = raw1942Labels := by decide +kernel
    rw [ha, hj, canonical1942 B hB]
  have hc1 : mixedMoment B raw1941 (Fin.cases (1 : Fin 2) singletonSmall4967) =
      mixedMoment B node3585 node3585Labels := by
    have ha : raw1941 = raw1943 := by apply Matrix.ext; unfold raw1941 raw1943; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4967 = raw1943Labels := by decide +kernel
    rw [ha, hj, canonical1943 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4970 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4970 node4970Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2815 node2815Labels + mixedMoment B node3588 node3588Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1950 singletonSmall4970
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4970) = raw1950Labels := by decide +kernel
  rw [hl, canonical1950 B hB] at h
  have hc0 : mixedMoment B raw1950 (Fin.cases (0 : Fin 2) singletonSmall4970) =
      mixedMoment B node2815 node2815Labels := by
    have ha : raw1950 = raw1951 := by apply Matrix.ext; unfold raw1950 raw1951; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4970 = raw1951Labels := by decide +kernel
    rw [ha, hj, canonical1951 B hB]
  have hc1 : mixedMoment B raw1950 (Fin.cases (1 : Fin 2) singletonSmall4970) =
      mixedMoment B node3588 node3588Labels := by
    have ha : raw1950 = raw1952 := by apply Matrix.ext; unfold raw1950 raw1952; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4970 = raw1952Labels := by decide +kernel
    rw [ha, hj, canonical1952 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4973 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4973 node4973Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2817 node2817Labels + mixedMoment B node3591 node3591Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1959 singletonSmall4973
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4973) = raw1959Labels := by decide +kernel
  rw [hl, canonical1959 B hB] at h
  have hc0 : mixedMoment B raw1959 (Fin.cases (0 : Fin 2) singletonSmall4973) =
      mixedMoment B node2817 node2817Labels := by
    have ha : raw1959 = raw1960 := by apply Matrix.ext; unfold raw1959 raw1960; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4973 = raw1960Labels := by decide +kernel
    rw [ha, hj, canonical1960 B hB]
  have hc1 : mixedMoment B raw1959 (Fin.cases (1 : Fin 2) singletonSmall4973) =
      mixedMoment B node3591 node3591Labels := by
    have ha : raw1959 = raw1961 := by apply Matrix.ext; unfold raw1959 raw1961; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4973 = raw1961Labels := by decide +kernel
    rw [ha, hj, canonical1961 B hB]
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

theorem singleton5114 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5114 node5114Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2896 node2896Labels + mixedMoment B node3597 node3597Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2139 singletonSmall5114
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5114) = raw2139Labels := by decide +kernel
  rw [hl, canonical2139 B hB] at h
  have hc0 : mixedMoment B raw2139 (Fin.cases (0 : Fin 2) singletonSmall5114) =
      mixedMoment B node2896 node2896Labels := by
    have ha : raw2139 = raw2140 := by apply Matrix.ext; unfold raw2139 raw2140; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5114 = raw2140Labels := by decide +kernel
    rw [ha, hj, canonical2140 B hB]
  have hc1 : mixedMoment B raw2139 (Fin.cases (1 : Fin 2) singletonSmall5114) =
      mixedMoment B node3597 node3597Labels := by
    have ha : raw2139 = raw2141 := by apply Matrix.ext; unfold raw2139 raw2141; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5114 = raw2141Labels := by decide +kernel
    rw [ha, hj, canonical2141 B hB]
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

theorem singleton5170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5170 node5170Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2954 node2954Labels + mixedMoment B node3606 node3606Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2202 singletonSmall5170
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5170) = raw2202Labels := by decide +kernel
  rw [hl, canonical2202 B hB] at h
  have hc0 : mixedMoment B raw2202 (Fin.cases (0 : Fin 2) singletonSmall5170) =
      mixedMoment B node2954 node2954Labels := by
    have ha : raw2202 = raw2203 := by apply Matrix.ext; unfold raw2202 raw2203; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5170 = raw2203Labels := by decide +kernel
    rw [ha, hj, canonical2203 B hB]
  have hc1 : mixedMoment B raw2202 (Fin.cases (1 : Fin 2) singletonSmall5170) =
      mixedMoment B node3606 node3606Labels := by
    have ha : raw2202 = raw2204 := by apply Matrix.ext; unfold raw2202 raw2204; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5170 = raw2204Labels := by decide +kernel
    rw [ha, hj, canonical2204 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5171 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5171 node5171Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2598 node2598Labels + mixedMoment B node3608 node3608Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2205 singletonSmall5171
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5171) = raw2205Labels := by decide +kernel
  rw [hl, canonical2205 B hB] at h
  have hc0 : mixedMoment B raw2205 (Fin.cases (0 : Fin 2) singletonSmall5171) =
      mixedMoment B node2598 node2598Labels := by
    have ha : raw2205 = raw2206 := by apply Matrix.ext; unfold raw2205 raw2206; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5171 = raw2206Labels := by decide +kernel
    rw [ha, hj, canonical2206 B hB]
  have hc1 : mixedMoment B raw2205 (Fin.cases (1 : Fin 2) singletonSmall5171) =
      mixedMoment B node3608 node3608Labels := by
    have ha : raw2205 = raw2207 := by apply Matrix.ext; unfold raw2205 raw2207; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5171 = raw2207Labels := by decide +kernel
    rw [ha, hj, canonical2207 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5176 node5176Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2604 node2604Labels + mixedMoment B node3614 node3614Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2214 singletonSmall5176
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5176) = raw2214Labels := by decide +kernel
  rw [hl, canonical2214 B hB] at h
  have hc0 : mixedMoment B raw2214 (Fin.cases (0 : Fin 2) singletonSmall5176) =
      mixedMoment B node2604 node2604Labels := by
    have ha : raw2214 = raw2215 := by apply Matrix.ext; unfold raw2214 raw2215; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5176 = raw2215Labels := by decide +kernel
    rw [ha, hj, canonical2215 B hB]
  have hc1 : mixedMoment B raw2214 (Fin.cases (1 : Fin 2) singletonSmall5176) =
      mixedMoment B node3614 node3614Labels := by
    have ha : raw2214 = raw2216 := by apply Matrix.ext; unfold raw2214 raw2216; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5176 = raw2216Labels := by decide +kernel
    rw [ha, hj, canonical2216 B hB]
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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1135 node1135Labels = Sparse.eval nodeValue1135 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1135) = mixedMoment B node1135 node1135Labels := rfl
  simpa [nodeValue1135, Sparse.eval] using hc.symm

theorem sound1136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1136 node1136Labels = Sparse.eval nodeValue1136 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1136) = mixedMoment B node1136 node1136Labels := rfl
  simpa [nodeValue1136, Sparse.eval] using hc.symm

theorem sound1138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1138 node1138Labels = Sparse.eval nodeValue1138 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1138) = mixedMoment B node1138 node1138Labels := rfl
  simpa [nodeValue1138, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node156 node156Labels = Sparse.eval nodeValue156 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue156 (familyPairVector B) := singlePair156 B _hB
    _ = _ := by
      norm_num [singlePairValue156, nodeValue156, Sparse.eval, mixedVector]
      ring

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

theorem sound1300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1300 node1300Labels = Sparse.eval nodeValue1300 (mixedVector B) := by
  have h := singleton1300 B _hB
  rw [sound156 B _hB _hF] at h
  norm_num [nodeValue1300, nodeValue156, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node338 node338Labels = Sparse.eval nodeValue338 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue338 (familyPairVector B) := singlePair338 B _hB
    _ = _ := by norm_num [singlePairValue338, nodeValue338, Sparse.eval, mixedVector] <;> ring

theorem sound343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node343 node343Labels = Sparse.eval nodeValue343 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue343 (familyPairVector B) := singlePair343 B _hB
    _ = _ := by norm_num [singlePairValue343, nodeValue343, Sparse.eval, mixedVector] <;> ring

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

theorem sound2598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2598 node2598Labels = Sparse.eval nodeValue2598 (mixedVector B) := by
  have h := singleton2598 B _hB
  rw [sound338 B _hB _hF] at h
  norm_num [nodeValue2598, nodeValue338, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2604 node2604Labels = Sparse.eval nodeValue2604 (mixedVector B) := by
  have h := singleton2604 B _hB
  rw [sound343 B _hB _hF] at h
  norm_num [nodeValue2604, nodeValue343, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound2784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2784 node2784Labels = Sparse.eval nodeValue2784 (mixedVector B) := by
  have h := singleton2784 B _hB
  rw [sound416 B _hB _hF] at h
  norm_num [nodeValue2784, nodeValue416, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2814 node2814Labels = Sparse.eval nodeValue2814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2814) = mixedMoment B node2814 node2814Labels := rfl
  simpa [nodeValue2814, Sparse.eval] using hc.symm

theorem sound2815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2815 node2815Labels = Sparse.eval nodeValue2815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2815) = mixedMoment B node2815 node2815Labels := rfl
  simpa [nodeValue2815, Sparse.eval] using hc.symm

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

theorem sound2817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2817 node2817Labels = Sparse.eval nodeValue2817 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2817) = mixedMoment B node2817 node2817Labels := rfl
  simpa [nodeValue2817, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2896 node2896Labels = Sparse.eval nodeValue2896 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2896) = mixedMoment B node2896 node2896Labels := rfl
  simpa [nodeValue2896, Sparse.eval] using hc.symm

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

theorem sound2954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2954 node2954Labels = Sparse.eval nodeValue2954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2954) = mixedMoment B node2954 node2954Labels := rfl
  simpa [nodeValue2954, Sparse.eval] using hc.symm

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

theorem sound3269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3269 node3269Labels = Sparse.eval nodeValue3269 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3269) = mixedMoment B node3269 node3269Labels := rfl
  simpa [nodeValue3269, Sparse.eval] using hc.symm

theorem sound3270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3270 node3270Labels = Sparse.eval nodeValue3270 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3270) = mixedMoment B node3270 node3270Labels := rfl
  simpa [nodeValue3270, Sparse.eval] using hc.symm

theorem sound3273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3273 node3273Labels = Sparse.eval nodeValue3273 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3273) = mixedMoment B node3273 node3273Labels := rfl
  simpa [nodeValue3273, Sparse.eval] using hc.symm

theorem sound3308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3308 node3308Labels = Sparse.eval nodeValue3308 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3308) = mixedMoment B node3308 node3308Labels := rfl
  simpa [nodeValue3308, Sparse.eval] using hc.symm

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

theorem sound3585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3585 node3585Labels = Sparse.eval nodeValue3585 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3585) = mixedMoment B node3585 node3585Labels := rfl
  simpa [nodeValue3585, Sparse.eval] using hc.symm

theorem sound3588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3588 node3588Labels = Sparse.eval nodeValue3588 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3588) = mixedMoment B node3588 node3588Labels := rfl
  simpa [nodeValue3588, Sparse.eval] using hc.symm

theorem sound3591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3591 node3591Labels = Sparse.eval nodeValue3591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3591) = mixedMoment B node3591 node3591Labels := rfl
  simpa [nodeValue3591, Sparse.eval] using hc.symm

theorem sound3597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3597 node3597Labels = Sparse.eval nodeValue3597 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3597) = mixedMoment B node3597 node3597Labels := rfl
  simpa [nodeValue3597, Sparse.eval] using hc.symm

theorem sound3606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3606 node3606Labels = Sparse.eval nodeValue3606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3606) = mixedMoment B node3606 node3606Labels := rfl
  simpa [nodeValue3606, Sparse.eval] using hc.symm

theorem sound3608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3608 node3608Labels = Sparse.eval nodeValue3608 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3608) = mixedMoment B node3608 node3608Labels := rfl
  simpa [nodeValue3608, Sparse.eval] using hc.symm

theorem sound3614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3614 node3614Labels = Sparse.eval nodeValue3614 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3614) = mixedMoment B node3614 node3614Labels := rfl
  simpa [nodeValue3614, Sparse.eval] using hc.symm

theorem sound3623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3623 node3623Labels = Sparse.eval nodeValue3623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3623) = mixedMoment B node3623 node3623Labels := rfl
  simpa [nodeValue3623, Sparse.eval] using hc.symm

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

theorem sound4550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4550 node4550Labels = Sparse.eval nodeValue4550 (mixedVector B) := by
  have h := singleton4550 B _hB
  rw [sound1135 B _hB _hF, sound3269 B _hB _hF] at h
  norm_num [nodeValue4550, nodeValue1135, nodeValue3269, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4551 node4551Labels = Sparse.eval nodeValue4551 (mixedVector B) := by
  have h := singleton4551 B _hB
  rw [sound1136 B _hB _hF, sound3273 B _hB _hF] at h
  norm_num [nodeValue4551, nodeValue1136, nodeValue3273, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4553 node4553Labels = Sparse.eval nodeValue4553 (mixedVector B) := by
  have h := singleton4553 B _hB
  rw [sound1138 B _hB _hF, sound3270 B _hB _hF] at h
  norm_num [nodeValue4553, nodeValue1138, nodeValue3270, Sparse.eval] at h ⊢
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

theorem sound4623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4623 node4623Labels = Sparse.eval nodeValue4623 (mixedVector B) := by
  have h := singleton4623 B _hB
  rw [sound1300 B _hB _hF, sound3308 B _hB _hF] at h
  norm_num [nodeValue4623, nodeValue1300, nodeValue3308, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4967 node4967Labels = Sparse.eval nodeValue4967 (mixedVector B) := by
  have h := singleton4967 B _hB
  rw [sound2814 B _hB _hF, sound3585 B _hB _hF] at h
  norm_num [nodeValue4967, nodeValue2814, nodeValue3585, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4970 node4970Labels = Sparse.eval nodeValue4970 (mixedVector B) := by
  have h := singleton4970 B _hB
  rw [sound2815 B _hB _hF, sound3588 B _hB _hF] at h
  norm_num [nodeValue4970, nodeValue2815, nodeValue3588, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4973 node4973Labels = Sparse.eval nodeValue4973 (mixedVector B) := by
  have h := singleton4973 B _hB
  rw [sound2817 B _hB _hF, sound3591 B _hB _hF] at h
  norm_num [nodeValue4973, nodeValue2817, nodeValue3591, Sparse.eval] at h ⊢
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

theorem zero5113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5113 node5113Labels = 0 := by
  exact mixedMoment_alpha B hF node5113 node5113Labels 1 permutation152
    (by decide +kernel)

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

theorem sound5113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5113 node5113Labels = Sparse.eval nodeValue5113 (mixedVector B) := by
  simpa only [nodeValue5113, Sparse.eval_nil] using zero5113 B _hB _hF

theorem sound5114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5114 node5114Labels = Sparse.eval nodeValue5114 (mixedVector B) := by
  have h := singleton5114 B _hB
  rw [sound2896 B _hB _hF, sound3597 B _hB _hF] at h
  norm_num [nodeValue5114, nodeValue2896, nodeValue3597, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem zero5166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5166 node5166Labels = 0 := by
  exact mixedMoment_alpha B hF node5166 node5166Labels 1 permutation161
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

theorem sound5166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5166 node5166Labels = Sparse.eval nodeValue5166 (mixedVector B) := by
  simpa only [nodeValue5166, Sparse.eval_nil] using zero5166 B _hB _hF

theorem sound5170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5170 node5170Labels = Sparse.eval nodeValue5170 (mixedVector B) := by
  have h := singleton5170 B _hB
  rw [sound2954 B _hB _hF, sound3606 B _hB _hF] at h
  norm_num [nodeValue5170, nodeValue2954, nodeValue3606, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5171 node5171Labels = Sparse.eval nodeValue5171 (mixedVector B) := by
  have h := singleton5171 B _hB
  rw [sound2598 B _hB _hF, sound3608 B _hB _hF] at h
  norm_num [nodeValue5171, nodeValue2598, nodeValue3608, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5176 node5176Labels = Sparse.eval nodeValue5176 (mixedVector B) := by
  have h := singleton5176 B _hB
  rw [sound2604 B _hB _hF, sound3614 B _hB _hF] at h
  norm_num [nodeValue5176, nodeValue2604, nodeValue3614, Sparse.eval] at h ⊢
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

theorem sound5306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5306 node5306Labels = Sparse.eval nodeValue5306 (mixedVector B) := by
  have h := singleton5306 B _hB
  rw [sound2784 B _hB _hF, sound3623 B _hB _hF] at h
  norm_num [nodeValue5306, nodeValue2784, nodeValue3623, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5308 node5308Labels = Sparse.eval nodeValue5308 (mixedVector B) := by
  simpa only [nodeValue5308, Sparse.eval_nil] using zero5308 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources73
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2338 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2338 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2338 + difference 0 1) (sourceB2338 + difference 1 0) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2338 + difference 0 1) (sourceB2338 + difference 1 0) sourceC2338) = raw18303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw18303; decide +kernel
    rw [ha]
    exact (canonical18303 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2338 + difference 0 2) (sourceB2338 + difference 2 0) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5415) := by
    have ha : (tripleCharges (sourceA2338 + difference 0 2) (sourceB2338 + difference 2 0) sourceC2338) = raw18304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw18304; decide +kernel
    rw [ha]
    exact (canonical18304 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2338 + difference 0 3) (sourceB2338 + difference 3 0) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA2338 + difference 0 3) (sourceB2338 + difference 3 0) sourceC2338) = raw10216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw10216; decide +kernel
    rw [ha]
    exact (canonical10216 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2338 + difference 0 4) (sourceB2338 + difference 4 0) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA2338 + difference 0 4) (sourceB2338 + difference 4 0) sourceC2338) = raw18305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw18305; decide +kernel
    rw [ha]
    exact (canonical18305 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2338 + difference 0 5) (sourceB2338 + difference 5 0) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2338 + difference 0 5) (sourceB2338 + difference 5 0) sourceC2338) = raw12080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw12080; decide +kernel
    rw [ha]
    exact (canonical12080 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2338 + difference 1 0) (sourceB2338 + difference 0 1) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA2338 + difference 1 0) (sourceB2338 + difference 0 1) sourceC2338) = raw10228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw10228; decide +kernel
    rw [ha]
    exact (canonical10228 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2338 + difference 1 2) (sourceB2338 + difference 2 1) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2338 + difference 1 2) (sourceB2338 + difference 2 1) sourceC2338) = raw10230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw10230; decide +kernel
    rw [ha]
    exact (canonical10230 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2338 + difference 1 3) (sourceB2338 + difference 3 1) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA2338 + difference 1 3) (sourceB2338 + difference 3 1) sourceC2338) = raw5082 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw5082; decide +kernel
    rw [ha]
    exact (canonical5082 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2338 + difference 1 4) (sourceB2338 + difference 4 1) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA2338 + difference 1 4) (sourceB2338 + difference 4 1) sourceC2338) = raw5077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw5077; decide +kernel
    rw [ha]
    exact (canonical5077 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2338 + difference 1 5) (sourceB2338 + difference 5 1) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA2338 + difference 1 5) (sourceB2338 + difference 5 1) sourceC2338) = raw10231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw10231; decide +kernel
    rw [ha]
    exact (canonical10231 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2338 + difference 2 0) (sourceB2338 + difference 0 2) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4550) := by
    have ha : (tripleCharges (sourceA2338 + difference 2 0) (sourceB2338 + difference 0 2) sourceC2338) = raw24105 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw24105; decide +kernel
    rw [ha]
    exact (canonical24105 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2338 + difference 2 1) (sourceB2338 + difference 1 2) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4967) := by
    have ha : (tripleCharges (sourceA2338 + difference 2 1) (sourceB2338 + difference 1 2) sourceC2338) = raw32031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw32031; decide +kernel
    rw [ha]
    exact (canonical32031 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2338 + difference 2 3) (sourceB2338 + difference 3 2) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2338 + difference 2 3) (sourceB2338 + difference 3 2) sourceC2338) = raw10225 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw10225; decide +kernel
    rw [ha]
    exact (canonical10225 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2338 + difference 2 4) (sourceB2338 + difference 4 2) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2338 + difference 2 4) (sourceB2338 + difference 4 2) sourceC2338) = raw32032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw32032; decide +kernel
    rw [ha]
    exact (canonical32032 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2338 + difference 2 5) (sourceB2338 + difference 5 2) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5166) := by
    have ha : (tripleCharges (sourceA2338 + difference 2 5) (sourceB2338 + difference 5 2) sourceC2338) = raw12089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw12089; decide +kernel
    rw [ha]
    exact (canonical12089 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2338 + difference 3 0) (sourceB2338 + difference 0 3) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA2338 + difference 3 0) (sourceB2338 + difference 0 3) sourceC2338) = raw24108 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw24108; decide +kernel
    rw [ha]
    exact (canonical24108 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2338 + difference 3 1) (sourceB2338 + difference 1 3) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4973) := by
    have ha : (tripleCharges (sourceA2338 + difference 3 1) (sourceB2338 + difference 1 3) sourceC2338) = raw32033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw32033; decide +kernel
    rw [ha]
    exact (canonical32033 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2338 + difference 3 2) (sourceB2338 + difference 2 3) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5114) := by
    have ha : (tripleCharges (sourceA2338 + difference 3 2) (sourceB2338 + difference 2 3) sourceC2338) = raw32034 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw32034; decide +kernel
    rw [ha]
    exact (canonical32034 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2338 + difference 3 4) (sourceB2338 + difference 4 3) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2338 + difference 3 4) (sourceB2338 + difference 4 3) sourceC2338) = raw32035 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw32035; decide +kernel
    rw [ha]
    exact (canonical32035 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2338 + difference 3 5) (sourceB2338 + difference 5 3) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2338 + difference 3 5) (sourceB2338 + difference 5 3) sourceC2338) = raw12093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw12093; decide +kernel
    rw [ha]
    exact (canonical12093 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2338 + difference 4 0) (sourceB2338 + difference 0 4) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA2338 + difference 4 0) (sourceB2338 + difference 0 4) sourceC2338) = raw22480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw22480; decide +kernel
    rw [ha]
    exact (canonical22480 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2338 + difference 4 1) (sourceB2338 + difference 1 4) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4973) := by
    have ha : (tripleCharges (sourceA2338 + difference 4 1) (sourceB2338 + difference 1 4) sourceC2338) = raw29509 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw29509; decide +kernel
    rw [ha]
    exact (canonical29509 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2338 + difference 4 2) (sourceB2338 + difference 2 4) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5114) := by
    have ha : (tripleCharges (sourceA2338 + difference 4 2) (sourceB2338 + difference 2 4) sourceC2338) = raw29510 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw29510; decide +kernel
    rw [ha]
    exact (canonical29510 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2338 + difference 4 3) (sourceB2338 + difference 3 4) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2338 + difference 4 3) (sourceB2338 + difference 3 4) sourceC2338) = raw10233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw10233; decide +kernel
    rw [ha]
    exact (canonical10233 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2338 + difference 4 5) (sourceB2338 + difference 5 4) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2338 + difference 4 5) (sourceB2338 + difference 5 4) sourceC2338) = raw12098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw12098; decide +kernel
    rw [ha]
    exact (canonical12098 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2338 + difference 5 0) (sourceB2338 + difference 0 5) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4551) := by
    have ha : (tripleCharges (sourceA2338 + difference 5 0) (sourceB2338 + difference 0 5) sourceC2338) = raw20358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw20358; decide +kernel
    rw [ha]
    exact (canonical20358 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2338 + difference 5 1) (sourceB2338 + difference 1 5) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4970) := by
    have ha : (tripleCharges (sourceA2338 + difference 5 1) (sourceB2338 + difference 1 5) sourceC2338) = raw27560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw27560; decide +kernel
    rw [ha]
    exact (canonical27560 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2338 + difference 5 2) (sourceB2338 + difference 2 5) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5113) := by
    have ha : (tripleCharges (sourceA2338 + difference 5 2) (sourceB2338 + difference 2 5) sourceC2338) = raw27561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw27561; decide +kernel
    rw [ha]
    exact (canonical27561 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2338 + difference 5 3) (sourceB2338 + difference 3 5) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA2338 + difference 5 3) (sourceB2338 + difference 3 5) sourceC2338) = raw5079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw5079; decide +kernel
    rw [ha]
    exact (canonical5079 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2338 + difference 5 4) (sourceB2338 + difference 4 5) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA2338 + difference 5 4) (sourceB2338 + difference 4 5) sourceC2338) = raw5074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw5074; decide +kernel
    rw [ha]
    exact (canonical5074 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2338 sourceB2338 sourceC2338
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2338, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1904 : Integer.Sparse.reindex keyMap MixedData.row1904 = numericRow1904 := by decide +kernel

theorem numericCheck1904 (x : Master → ℝ) : Integer.Sparse.eval numericRow1904 x =
    (4320 : ℝ) * reducedSource1904 x := by
  norm_num [numericRow1904, reducedSource1904, Integer.Sparse.eval, Sparse.eval, nodeValue4550, nodeValue4551, nodeValue4553, nodeValue4623, nodeValue4967, nodeValue4970, nodeValue4973, nodeValue5113, nodeValue5114, nodeValue5166, nodeValue5168, nodeValue5170, nodeValue5171, nodeValue5176, nodeValue5306, nodeValue5308, nodeValue5387, nodeValue5415, nodeValue5439, nodeValue5441]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1904 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1904 (mixedVector B) = 0 := by
  have h4550 : mixedVector B (Sum.inr 4550) = Sparse.eval nodeValue4550 (mixedVector B) := by
    change mixedMoment B node4550 node4550Labels = _
    exact sound4550 B hB hF
  have h4551 : mixedVector B (Sum.inr 4551) = Sparse.eval nodeValue4551 (mixedVector B) := by
    change mixedMoment B node4551 node4551Labels = _
    exact sound4551 B hB hF
  have h4553 : mixedVector B (Sum.inr 4553) = Sparse.eval nodeValue4553 (mixedVector B) := by
    change mixedMoment B node4553 node4553Labels = _
    exact sound4553 B hB hF
  have h4623 : mixedVector B (Sum.inr 4623) = Sparse.eval nodeValue4623 (mixedVector B) := by
    change mixedMoment B node4623 node4623Labels = _
    exact sound4623 B hB hF
  have h4967 : mixedVector B (Sum.inr 4967) = Sparse.eval nodeValue4967 (mixedVector B) := by
    change mixedMoment B node4967 node4967Labels = _
    exact sound4967 B hB hF
  have h4970 : mixedVector B (Sum.inr 4970) = Sparse.eval nodeValue4970 (mixedVector B) := by
    change mixedMoment B node4970 node4970Labels = _
    exact sound4970 B hB hF
  have h4973 : mixedVector B (Sum.inr 4973) = Sparse.eval nodeValue4973 (mixedVector B) := by
    change mixedMoment B node4973 node4973Labels = _
    exact sound4973 B hB hF
  have h5113 : mixedVector B (Sum.inr 5113) = Sparse.eval nodeValue5113 (mixedVector B) := by
    change mixedMoment B node5113 node5113Labels = _
    exact sound5113 B hB hF
  have h5114 : mixedVector B (Sum.inr 5114) = Sparse.eval nodeValue5114 (mixedVector B) := by
    change mixedMoment B node5114 node5114Labels = _
    exact sound5114 B hB hF
  have h5166 : mixedVector B (Sum.inr 5166) = Sparse.eval nodeValue5166 (mixedVector B) := by
    change mixedMoment B node5166 node5166Labels = _
    exact sound5166 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168_e B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5171 : mixedVector B (Sum.inr 5171) = Sparse.eval nodeValue5171 (mixedVector B) := by
    change mixedMoment B node5171 node5171Labels = _
    exact sound5171 B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  have h5308 : mixedVector B (Sum.inr 5308) = Sparse.eval nodeValue5308 (mixedVector B) := by
    change mixedMoment B node5308 node5308Labels = _
    exact sound5308 B hB hF
  have h5387 : mixedVector B (Sum.inr 5387) = Sparse.eval nodeValue5387 (mixedVector B) := by
    change mixedMoment B node5387 node5387Labels = _
    exact sound5387_e B hB hF
  have h5415 : mixedVector B (Sum.inr 5415) = Sparse.eval nodeValue5415 (mixedVector B) := by
    change mixedMoment B node5415 node5415Labels = _
    exact sound5415_e B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439_e B hB hF
  have h5441 : mixedVector B (Sum.inr 5441) = Sparse.eval nodeValue5441 (mixedVector B) := by
    change mixedMoment B node5441 node5441Labels = _
    exact sound5441 B hB hF
  simpa only [sourceForm2338, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4550, h4551, h4553, h4623, h4967, h4970, h4973, h5113, h5114, h5166, h5168, h5170, h5171, h5176, h5306, h5308, h5387, h5415, h5439, h5441, reducedSource1904] using sourceEq2338 B hB

theorem rowSound1904_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1904 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1904, numericCheck1904, reducedZero1904 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e_oai
