-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:06:49.149185+00:00
-- url     : https://prove2.me/submissions/31abbc8a-fb0a-4ad3-b632-401b123d9bb3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E118
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5172_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5485_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1620 raw1620Labels = mixedMoment B node4721 node4721Labels := by
  calc
    mixedMoment B raw1620 raw1620Labels = mixedMoment B raw1620step0 raw1620step0Labels := by
      have ha : raw1620step0 = (fun i j => raw1620 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1620step0 raw1620; decide +kernel
      have hl : raw1620step0Labels = raw1620Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1620 raw1620Labels permutation152 permutation4
    mixedMoment B raw1620step0 raw1620step0Labels = mixedMoment B raw1620step1 raw1620step1Labels := by
      have ha : raw1620step1 = raw1620step0 := by apply Matrix.ext; unfold raw1620step1 raw1620step0; decide +kernel
      have hl : raw1620step0Labels = labelEmbedding7 ∘ raw1620step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1620step0 raw1620step0Labels raw1620step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4721 node4721Labels := by rfl

theorem canonical1621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1621 raw1621Labels = mixedMoment B node1875 node1875Labels := by
  calc
    mixedMoment B raw1621 raw1621Labels = mixedMoment B raw1621step0 raw1621step0Labels := by
      have ha : raw1621step0 = (fun i j => raw1621 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1621step0 raw1621; decide +kernel
      have hl : raw1621step0Labels = raw1621Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1621 raw1621Labels permutation152 permutation4
    _ = mixedMoment B node1875 node1875Labels := by rfl

theorem canonical1622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1622 raw1622Labels = mixedMoment B node1905 node1905Labels := by
  calc
    mixedMoment B raw1622 raw1622Labels = mixedMoment B raw1622step0 raw1622step0Labels := by
      have ha : raw1622step0 = (fun i j => raw1622 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1622step0 raw1622; decide +kernel
      have hl : raw1622step0Labels = raw1622Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1622 raw1622Labels permutation158 permutation6
    mixedMoment B raw1622step0 raw1622step0Labels = mixedMoment B raw1622step1 raw1622step1Labels := by
      have ha : raw1622step1 = -raw1622step0 := by apply Matrix.ext; change ∀ i j, raw1622step1 i j = -(raw1622step0 i j); unfold raw1622step1 raw1622step0; decide +kernel
      have hl : raw1622step1Labels = raw1622step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1622step1 raw1622step1Labels = mixedMoment B raw1622step2 raw1622step2Labels := by
      have ha : raw1622step2 = raw1622step1 := by apply Matrix.ext; unfold raw1622step2 raw1622step1; decide +kernel
      have hl : raw1622step1Labels = labelEmbedding1 ∘ raw1622step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1622step1 raw1622step1Labels raw1622step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1905 node1905Labels := by rfl

theorem canonical1635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1635 raw1635Labels = mixedMoment B node4726 node4726Labels := by
  calc
    mixedMoment B raw1635 raw1635Labels = mixedMoment B raw1635step0 raw1635step0Labels := by
      have ha : raw1635step0 = (fun i j => raw1635 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1635step0 raw1635; decide +kernel
      have hl : raw1635step0Labels = raw1635Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1635 raw1635Labels permutation32 permutation4
    mixedMoment B raw1635step0 raw1635step0Labels = mixedMoment B raw1635step1 raw1635step1Labels := by
      have ha : raw1635step1 = raw1635step0 := by apply Matrix.ext; unfold raw1635step1 raw1635step0; decide +kernel
      have hl : raw1635step0Labels = labelEmbedding7 ∘ raw1635step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1635step0 raw1635step0Labels raw1635step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4726 node4726Labels := by rfl

theorem canonical1636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1636 raw1636Labels = mixedMoment B node1880 node1880Labels := by
  calc
    mixedMoment B raw1636 raw1636Labels = mixedMoment B raw1636step0 raw1636step0Labels := by
      have ha : raw1636step0 = (fun i j => raw1636 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1636step0 raw1636; decide +kernel
      have hl : raw1636step0Labels = raw1636Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1636 raw1636Labels permutation32 permutation4
    _ = mixedMoment B node1880 node1880Labels := by rfl

theorem canonical1637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1637 raw1637Labels = mixedMoment B node1938 node1938Labels := by
  calc
    mixedMoment B raw1637 raw1637Labels = mixedMoment B raw1637step0 raw1637step0Labels := by
      have ha : raw1637step0 = (fun i j => raw1637 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1637step0 raw1637; decide +kernel
      have hl : raw1637step0Labels = raw1637Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1637 raw1637Labels permutation32 permutation6
    mixedMoment B raw1637step0 raw1637step0Labels = mixedMoment B raw1637step1 raw1637step1Labels := by
      have ha : raw1637step1 = -raw1637step0 := by apply Matrix.ext; change ∀ i j, raw1637step1 i j = -(raw1637step0 i j); unfold raw1637step1 raw1637step0; decide +kernel
      have hl : raw1637step1Labels = raw1637step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1637step1 raw1637step1Labels = mixedMoment B raw1637step2 raw1637step2Labels := by
      have ha : raw1637step2 = raw1637step1 := by apply Matrix.ext; unfold raw1637step2 raw1637step1; decide +kernel
      have hl : raw1637step1Labels = labelEmbedding1 ∘ raw1637step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1637step1 raw1637step1Labels raw1637step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1938 node1938Labels := by rfl

theorem canonical1662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1662 raw1662Labels = mixedMoment B node4744 node4744Labels := by
  calc
    mixedMoment B raw1662 raw1662Labels = mixedMoment B raw1662step0 raw1662step0Labels := by
      have ha : raw1662step0 = (fun i j => raw1662 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1662step0 raw1662; decide +kernel
      have hl : raw1662step0Labels = raw1662Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1662 raw1662Labels permutation32 permutation4
    mixedMoment B raw1662step0 raw1662step0Labels = mixedMoment B raw1662step1 raw1662step1Labels := by
      have ha : raw1662step1 = raw1662step0 := by apply Matrix.ext; unfold raw1662step1 raw1662step0; decide +kernel
      have hl : raw1662step0Labels = labelEmbedding7 ∘ raw1662step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1662step0 raw1662step0Labels raw1662step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4744 node4744Labels := by rfl

theorem canonical1663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1663 raw1663Labels = mixedMoment B node1917 node1917Labels := by
  calc
    mixedMoment B raw1663 raw1663Labels = mixedMoment B raw1663step0 raw1663step0Labels := by
      have ha : raw1663step0 = (fun i j => raw1663 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1663step0 raw1663; decide +kernel
      have hl : raw1663step0Labels = raw1663Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1663 raw1663Labels permutation32 permutation4
    _ = mixedMoment B node1917 node1917Labels := by rfl

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

theorem canonical1664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1664 raw1664Labels = mixedMoment B node1924 node1924Labels := by
  calc
    mixedMoment B raw1664 raw1664Labels = mixedMoment B raw1664step0 raw1664step0Labels := by
      have ha : raw1664step0 = (fun i j => raw1664 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1664step0 raw1664; decide +kernel
      have hl : raw1664step0Labels = raw1664Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1664 raw1664Labels permutation34 permutation6
    mixedMoment B raw1664step0 raw1664step0Labels = mixedMoment B raw1664step1 raw1664step1Labels := by
      have ha : raw1664step1 = -raw1664step0 := by apply Matrix.ext; change ∀ i j, raw1664step1 i j = -(raw1664step0 i j); unfold raw1664step1 raw1664step0; decide +kernel
      have hl : raw1664step1Labels = raw1664step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1664step1 raw1664step1Labels = mixedMoment B raw1664step2 raw1664step2Labels := by
      have ha : raw1664step2 = raw1664step1 := by apply Matrix.ext; unfold raw1664step2 raw1664step1; decide +kernel
      have hl : raw1664step1Labels = labelEmbedding1 ∘ raw1664step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1664step1 raw1664step1Labels raw1664step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1924 node1924Labels := by rfl

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

theorem canonical1896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1896 raw1896Labels = mixedMoment B node4936 node4936Labels := by
  calc
    mixedMoment B raw1896 raw1896Labels = mixedMoment B raw1896step0 raw1896step0Labels := by
      have ha : raw1896step0 = (fun i j => raw1896 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1896step0 raw1896; decide +kernel
      have hl : raw1896step0Labels = raw1896Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1896 raw1896Labels permutation152 permutation4
    mixedMoment B raw1896step0 raw1896step0Labels = mixedMoment B raw1896step1 raw1896step1Labels := by
      have ha : raw1896step1 = raw1896step0 := by apply Matrix.ext; unfold raw1896step1 raw1896step0; decide +kernel
      have hl : raw1896step0Labels = labelEmbedding7 ∘ raw1896step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1896step0 raw1896step0Labels raw1896step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4936 node4936Labels := by rfl

theorem canonical1897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1897 raw1897Labels = mixedMoment B node2328 node2328Labels := by
  calc
    mixedMoment B raw1897 raw1897Labels = mixedMoment B raw1897step0 raw1897step0Labels := by
      have ha : raw1897step0 = (fun i j => raw1897 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1897step0 raw1897; decide +kernel
      have hl : raw1897step0Labels = raw1897Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1897 raw1897Labels permutation152 permutation4
    _ = mixedMoment B node2328 node2328Labels := by rfl

theorem canonical1898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1898 raw1898Labels = mixedMoment B node3401 node3401Labels := by
  calc
    mixedMoment B raw1898 raw1898Labels = mixedMoment B raw1898step0 raw1898step0Labels := by
      have ha : raw1898step0 = (fun i j => raw1898 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1898step0 raw1898; decide +kernel
      have hl : raw1898step0Labels = raw1898Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1898 raw1898Labels permutation152 permutation6
    mixedMoment B raw1898step0 raw1898step0Labels = mixedMoment B raw1898step1 raw1898step1Labels := by
      have ha : raw1898step1 = -raw1898step0 := by apply Matrix.ext; change ∀ i j, raw1898step1 i j = -(raw1898step0 i j); unfold raw1898step1 raw1898step0; decide +kernel
      have hl : raw1898step1Labels = raw1898step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1898step1 raw1898step1Labels = mixedMoment B raw1898step2 raw1898step2Labels := by
      have ha : raw1898step2 = raw1898step1 := by apply Matrix.ext; unfold raw1898step2 raw1898step1; decide +kernel
      have hl : raw1898step1Labels = labelEmbedding1 ∘ raw1898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1898step1 raw1898step1Labels raw1898step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3401 node3401Labels := by rfl

theorem canonical1899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1899 raw1899Labels = mixedMoment B node4937 node4937Labels := by
  calc
    mixedMoment B raw1899 raw1899Labels = mixedMoment B raw1899step0 raw1899step0Labels := by
      have ha : raw1899step0 = (fun i j => raw1899 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1899step0 raw1899; decide +kernel
      have hl : raw1899step0Labels = raw1899Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1899 raw1899Labels permutation32 permutation4
    mixedMoment B raw1899step0 raw1899step0Labels = mixedMoment B raw1899step1 raw1899step1Labels := by
      have ha : raw1899step1 = raw1899step0 := by apply Matrix.ext; unfold raw1899step1 raw1899step0; decide +kernel
      have hl : raw1899step0Labels = labelEmbedding7 ∘ raw1899step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1899step0 raw1899step0Labels raw1899step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4937 node4937Labels := by rfl

theorem canonical1900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1900 raw1900Labels = mixedMoment B node2329 node2329Labels := by
  calc
    mixedMoment B raw1900 raw1900Labels = mixedMoment B raw1900step0 raw1900step0Labels := by
      have ha : raw1900step0 = (fun i j => raw1900 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1900step0 raw1900; decide +kernel
      have hl : raw1900step0Labels = raw1900Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1900 raw1900Labels permutation32 permutation4
    _ = mixedMoment B node2329 node2329Labels := by rfl

theorem canonical1901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1901 raw1901Labels = mixedMoment B node3402 node3402Labels := by
  calc
    mixedMoment B raw1901 raw1901Labels = mixedMoment B raw1901step0 raw1901step0Labels := by
      have ha : raw1901step0 = (fun i j => raw1901 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1901step0 raw1901; decide +kernel
      have hl : raw1901step0Labels = raw1901Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1901 raw1901Labels permutation32 permutation6
    mixedMoment B raw1901step0 raw1901step0Labels = mixedMoment B raw1901step1 raw1901step1Labels := by
      have ha : raw1901step1 = -raw1901step0 := by apply Matrix.ext; change ∀ i j, raw1901step1 i j = -(raw1901step0 i j); unfold raw1901step1 raw1901step0; decide +kernel
      have hl : raw1901step1Labels = raw1901step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1901step1 raw1901step1Labels = mixedMoment B raw1901step2 raw1901step2Labels := by
      have ha : raw1901step2 = raw1901step1 := by apply Matrix.ext; unfold raw1901step2 raw1901step1; decide +kernel
      have hl : raw1901step1Labels = labelEmbedding1 ∘ raw1901step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1901step1 raw1901step1Labels raw1901step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3402 node3402Labels := by rfl

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

theorem canonical1920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1920 raw1920Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw1920 raw1920Labels = mixedMoment B raw1920step0 raw1920step0Labels := by
      have ha : raw1920step0 = (fun i j => raw1920 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1920step0 raw1920; decide +kernel
      have hl : raw1920step0Labels = raw1920Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1920 raw1920Labels permutation32 permutation4
    mixedMoment B raw1920step0 raw1920step0Labels = mixedMoment B raw1920step1 raw1920step1Labels := by
      have ha : raw1920step1 = raw1920step0 := by apply Matrix.ext; unfold raw1920step1 raw1920step0; decide +kernel
      have hl : raw1920step0Labels = labelEmbedding7 ∘ raw1920step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1920step0 raw1920step0Labels raw1920step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

theorem canonical1921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1921 raw1921Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw1921 raw1921Labels = mixedMoment B raw1921step0 raw1921step0Labels := by
      have ha : raw1921step0 = (fun i j => raw1921 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1921step0 raw1921; decide +kernel
      have hl : raw1921step0Labels = raw1921Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1921 raw1921Labels permutation32 permutation4
    _ = mixedMoment B node2341 node2341Labels := by rfl

theorem canonical1922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1922 raw1922Labels = mixedMoment B node3417 node3417Labels := by
  calc
    mixedMoment B raw1922 raw1922Labels = mixedMoment B raw1922step0 raw1922step0Labels := by
      have ha : raw1922step0 = (fun i j => raw1922 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1922step0 raw1922; decide +kernel
      have hl : raw1922step0Labels = raw1922Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1922 raw1922Labels permutation34 permutation6
    mixedMoment B raw1922step0 raw1922step0Labels = mixedMoment B raw1922step1 raw1922step1Labels := by
      have ha : raw1922step1 = -raw1922step0 := by apply Matrix.ext; change ∀ i j, raw1922step1 i j = -(raw1922step0 i j); unfold raw1922step1 raw1922step0; decide +kernel
      have hl : raw1922step1Labels = raw1922step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1922step1 raw1922step1Labels = mixedMoment B raw1922step2 raw1922step2Labels := by
      have ha : raw1922step2 = raw1922step1 := by apply Matrix.ext; unfold raw1922step2 raw1922step1; decide +kernel
      have hl : raw1922step1Labels = labelEmbedding1 ∘ raw1922step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1922step1 raw1922step1Labels raw1922step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3417 node3417Labels := by rfl

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

theorem canonical2049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2049 raw2049Labels = mixedMoment B node5032 node5032Labels := by
  calc
    mixedMoment B raw2049 raw2049Labels = mixedMoment B raw2049step0 raw2049step0Labels := by
      have ha : raw2049step0 = (fun i j => raw2049 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2049step0 raw2049; decide +kernel
      have hl : raw2049step0Labels = raw2049Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2049 raw2049Labels permutation152 permutation4
    mixedMoment B raw2049step0 raw2049step0Labels = mixedMoment B raw2049step1 raw2049step1Labels := by
      have ha : raw2049step1 = raw2049step0 := by apply Matrix.ext; unfold raw2049step1 raw2049step0; decide +kernel
      have hl : raw2049step0Labels = labelEmbedding7 ∘ raw2049step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2049step0 raw2049step0Labels raw2049step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5032 node5032Labels := by rfl

theorem canonical2050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2050 raw2050Labels = mixedMoment B node2424 node2424Labels := by
  calc
    mixedMoment B raw2050 raw2050Labels = mixedMoment B raw2050step0 raw2050step0Labels := by
      have ha : raw2050step0 = (fun i j => raw2050 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2050step0 raw2050; decide +kernel
      have hl : raw2050step0Labels = raw2050Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2050 raw2050Labels permutation152 permutation4
    _ = mixedMoment B node2424 node2424Labels := by rfl

theorem canonical2051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2051 raw2051Labels = mixedMoment B node3440 node3440Labels := by
  calc
    mixedMoment B raw2051 raw2051Labels = mixedMoment B raw2051step0 raw2051step0Labels := by
      have ha : raw2051step0 = (fun i j => raw2051 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2051step0 raw2051; decide +kernel
      have hl : raw2051step0Labels = raw2051Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2051 raw2051Labels permutation158 permutation6
    mixedMoment B raw2051step0 raw2051step0Labels = mixedMoment B raw2051step1 raw2051step1Labels := by
      have ha : raw2051step1 = -raw2051step0 := by apply Matrix.ext; change ∀ i j, raw2051step1 i j = -(raw2051step0 i j); unfold raw2051step1 raw2051step0; decide +kernel
      have hl : raw2051step1Labels = raw2051step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2051step1 raw2051step1Labels = mixedMoment B raw2051step2 raw2051step2Labels := by
      have ha : raw2051step2 = raw2051step1 := by apply Matrix.ext; unfold raw2051step2 raw2051step1; decide +kernel
      have hl : raw2051step1Labels = labelEmbedding1 ∘ raw2051step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2051step1 raw2051step1Labels raw2051step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3440 node3440Labels := by rfl

theorem canonical2061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2061 raw2061Labels = mixedMoment B node5038 node5038Labels := by
  calc
    mixedMoment B raw2061 raw2061Labels = mixedMoment B raw2061step0 raw2061step0Labels := by
      have ha : raw2061step0 = (fun i j => raw2061 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2061step0 raw2061; decide +kernel
      have hl : raw2061step0Labels = raw2061Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2061 raw2061Labels permutation152 permutation4
    mixedMoment B raw2061step0 raw2061step0Labels = mixedMoment B raw2061step1 raw2061step1Labels := by
      have ha : raw2061step1 = raw2061step0 := by apply Matrix.ext; unfold raw2061step1 raw2061step0; decide +kernel
      have hl : raw2061step0Labels = labelEmbedding7 ∘ raw2061step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2061step0 raw2061step0Labels raw2061step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5038 node5038Labels := by rfl

theorem canonical2062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2062 raw2062Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw2062 raw2062Labels = mixedMoment B raw2062step0 raw2062step0Labels := by
      have ha : raw2062step0 = (fun i j => raw2062 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2062step0 raw2062; decide +kernel
      have hl : raw2062step0Labels = raw2062Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2062 raw2062Labels permutation152 permutation4
    _ = mixedMoment B node2431 node2431Labels := by rfl

theorem canonical2063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2063 raw2063Labels = mixedMoment B node3453 node3453Labels := by
  calc
    mixedMoment B raw2063 raw2063Labels = mixedMoment B raw2063step0 raw2063step0Labels := by
      have ha : raw2063step0 = (fun i j => raw2063 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2063step0 raw2063; decide +kernel
      have hl : raw2063step0Labels = raw2063Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2063 raw2063Labels permutation154 permutation6
    mixedMoment B raw2063step0 raw2063step0Labels = mixedMoment B raw2063step1 raw2063step1Labels := by
      have ha : raw2063step1 = -raw2063step0 := by apply Matrix.ext; change ∀ i j, raw2063step1 i j = -(raw2063step0 i j); unfold raw2063step1 raw2063step0; decide +kernel
      have hl : raw2063step1Labels = raw2063step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2063step1 raw2063step1Labels = mixedMoment B raw2063step2 raw2063step2Labels := by
      have ha : raw2063step2 = raw2063step1 := by apply Matrix.ext; unfold raw2063step2 raw2063step1; decide +kernel
      have hl : raw2063step1Labels = labelEmbedding1 ∘ raw2063step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2063step1 raw2063step1Labels raw2063step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3453 node3453Labels := by rfl

theorem canonical2088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2088 raw2088Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw2088 raw2088Labels = mixedMoment B raw2088step0 raw2088step0Labels := by
      have ha : raw2088step0 = (fun i j => raw2088 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2088step0 raw2088; decide +kernel
      have hl : raw2088step0Labels = raw2088Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2088 raw2088Labels permutation152 permutation4
    mixedMoment B raw2088step0 raw2088step0Labels = mixedMoment B raw2088step1 raw2088step1Labels := by
      have ha : raw2088step1 = raw2088step0 := by apply Matrix.ext; unfold raw2088step1 raw2088step0; decide +kernel
      have hl : raw2088step0Labels = labelEmbedding7 ∘ raw2088step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2088step0 raw2088step0Labels raw2088step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5070 node5070Labels := by rfl

theorem canonical2089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2089 raw2089Labels = mixedMoment B node2477 node2477Labels := by
  calc
    mixedMoment B raw2089 raw2089Labels = mixedMoment B raw2089step0 raw2089step0Labels := by
      have ha : raw2089step0 = (fun i j => raw2089 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2089step0 raw2089; decide +kernel
      have hl : raw2089step0Labels = raw2089Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2089 raw2089Labels permutation152 permutation4
    _ = mixedMoment B node2477 node2477Labels := by rfl

theorem canonical2090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2090 raw2090Labels = mixedMoment B node3444 node3444Labels := by
  calc
    mixedMoment B raw2090 raw2090Labels = mixedMoment B raw2090step0 raw2090step0Labels := by
      have ha : raw2090step0 = (fun i j => raw2090 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2090step0 raw2090; decide +kernel
      have hl : raw2090step0Labels = raw2090Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2090 raw2090Labels permutation158 permutation6
    mixedMoment B raw2090step0 raw2090step0Labels = mixedMoment B raw2090step1 raw2090step1Labels := by
      have ha : raw2090step1 = -raw2090step0 := by apply Matrix.ext; change ∀ i j, raw2090step1 i j = -(raw2090step0 i j); unfold raw2090step1 raw2090step0; decide +kernel
      have hl : raw2090step1Labels = raw2090step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2090step1 raw2090step1Labels = mixedMoment B raw2090step2 raw2090step2Labels := by
      have ha : raw2090step2 = raw2090step1 := by apply Matrix.ext; unfold raw2090step2 raw2090step1; decide +kernel
      have hl : raw2090step1Labels = labelEmbedding1 ∘ raw2090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2090step1 raw2090step1Labels raw2090step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3444 node3444Labels := by rfl

theorem canonical2154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2154 raw2154Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw2154 raw2154Labels = mixedMoment B raw2154step0 raw2154step0Labels := by
      have ha : raw2154step0 = (fun i j => raw2154 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2154step0 raw2154; decide +kernel
      have hl : raw2154step0Labels = raw2154Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2154 raw2154Labels permutation152 permutation4
    mixedMoment B raw2154step0 raw2154step0Labels = mixedMoment B raw2154step1 raw2154step1Labels := by
      have ha : raw2154step1 = raw2154step0 := by apply Matrix.ext; unfold raw2154step1 raw2154step0; decide +kernel
      have hl : raw2154step0Labels = labelEmbedding7 ∘ raw2154step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2154step0 raw2154step0Labels raw2154step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

theorem canonical2155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2155 raw2155Labels = mixedMoment B node2536 node2536Labels := by
  calc
    mixedMoment B raw2155 raw2155Labels = mixedMoment B raw2155step0 raw2155step0Labels := by
      have ha : raw2155step0 = (fun i j => raw2155 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2155step0 raw2155; decide +kernel
      have hl : raw2155step0Labels = raw2155Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2155 raw2155Labels permutation152 permutation4
    _ = mixedMoment B node2536 node2536Labels := by rfl

theorem canonical2156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2156 raw2156Labels = mixedMoment B node3370 node3370Labels := by
  calc
    mixedMoment B raw2156 raw2156Labels = mixedMoment B raw2156step0 raw2156step0Labels := by
      have ha : raw2156step0 = (fun i j => raw2156 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2156step0 raw2156; decide +kernel
      have hl : raw2156step0Labels = raw2156Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2156 raw2156Labels permutation176 permutation6
    mixedMoment B raw2156step0 raw2156step0Labels = mixedMoment B raw2156step1 raw2156step1Labels := by
      have ha : raw2156step1 = -raw2156step0 := by apply Matrix.ext; change ∀ i j, raw2156step1 i j = -(raw2156step0 i j); unfold raw2156step1 raw2156step0; decide +kernel
      have hl : raw2156step1Labels = raw2156step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2156step1 raw2156step1Labels = mixedMoment B raw2156step2 raw2156step2Labels := by
      have ha : raw2156step2 = raw2156step1 := by apply Matrix.ext; unfold raw2156step2 raw2156step1; decide +kernel
      have hl : raw2156step1Labels = labelEmbedding1 ∘ raw2156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2156step1 raw2156step1Labels raw2156step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3370 node3370Labels := by rfl

theorem canonical2157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2157 raw2157Labels = mixedMoment B node5125 node5125Labels := by
  calc
    mixedMoment B raw2157 raw2157Labels = mixedMoment B raw2157step0 raw2157step0Labels := by
      have ha : raw2157step0 = (fun i j => raw2157 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2157step0 raw2157; decide +kernel
      have hl : raw2157step0Labels = raw2157Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2157 raw2157Labels permutation32 permutation4
    mixedMoment B raw2157step0 raw2157step0Labels = mixedMoment B raw2157step1 raw2157step1Labels := by
      have ha : raw2157step1 = raw2157step0 := by apply Matrix.ext; unfold raw2157step1 raw2157step0; decide +kernel
      have hl : raw2157step0Labels = labelEmbedding7 ∘ raw2157step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2157step0 raw2157step0Labels raw2157step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5125 node5125Labels := by rfl

theorem canonical2158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2158 raw2158Labels = mixedMoment B node2539 node2539Labels := by
  calc
    mixedMoment B raw2158 raw2158Labels = mixedMoment B raw2158step0 raw2158step0Labels := by
      have ha : raw2158step0 = (fun i j => raw2158 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2158step0 raw2158; decide +kernel
      have hl : raw2158step0Labels = raw2158Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2158 raw2158Labels permutation32 permutation4
    _ = mixedMoment B node2539 node2539Labels := by rfl

theorem canonical2159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2159 raw2159Labels = mixedMoment B node3372 node3372Labels := by
  calc
    mixedMoment B raw2159 raw2159Labels = mixedMoment B raw2159step0 raw2159step0Labels := by
      have ha : raw2159step0 = (fun i j => raw2159 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2159step0 raw2159; decide +kernel
      have hl : raw2159step0Labels = raw2159Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2159 raw2159Labels permutation38 permutation6
    mixedMoment B raw2159step0 raw2159step0Labels = mixedMoment B raw2159step1 raw2159step1Labels := by
      have ha : raw2159step1 = -raw2159step0 := by apply Matrix.ext; change ∀ i j, raw2159step1 i j = -(raw2159step0 i j); unfold raw2159step1 raw2159step0; decide +kernel
      have hl : raw2159step1Labels = raw2159step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2159step1 raw2159step1Labels = mixedMoment B raw2159step2 raw2159step2Labels := by
      have ha : raw2159step2 = raw2159step1 := by apply Matrix.ext; unfold raw2159step2 raw2159step1; decide +kernel
      have hl : raw2159step1Labels = labelEmbedding1 ∘ raw2159step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2159step1 raw2159step1Labels raw2159step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3372 node3372Labels := by rfl

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

theorem canonical2187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2187 raw2187Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw2187 raw2187Labels = mixedMoment B raw2187step0 raw2187step0Labels := by
      have ha : raw2187step0 = (fun i j => raw2187 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2187step0 raw2187; decide +kernel
      have hl : raw2187step0Labels = raw2187Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2187 raw2187Labels permutation152 permutation4
    mixedMoment B raw2187step0 raw2187step0Labels = mixedMoment B raw2187step1 raw2187step1Labels := by
      have ha : raw2187step1 = raw2187step0 := by apply Matrix.ext; unfold raw2187step1 raw2187step0; decide +kernel
      have hl : raw2187step0Labels = labelEmbedding7 ∘ raw2187step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2187step0 raw2187step0Labels raw2187step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5162 node5162Labels := by rfl

theorem canonical2188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2188 raw2188Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw2188 raw2188Labels = mixedMoment B raw2188step0 raw2188step0Labels := by
      have ha : raw2188step0 = (fun i j => raw2188 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2188step0 raw2188; decide +kernel
      have hl : raw2188step0Labels = raw2188Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2188 raw2188Labels permutation152 permutation4
    _ = mixedMoment B node2589 node2589Labels := by rfl

theorem canonical2189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2189 raw2189Labels = mixedMoment B node3563 node3563Labels := by
  calc
    mixedMoment B raw2189 raw2189Labels = mixedMoment B raw2189step0 raw2189step0Labels := by
      have ha : raw2189step0 = (fun i j => raw2189 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2189step0 raw2189; decide +kernel
      have hl : raw2189step0Labels = raw2189Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2189 raw2189Labels permutation176 permutation6
    mixedMoment B raw2189step0 raw2189step0Labels = mixedMoment B raw2189step1 raw2189step1Labels := by
      have ha : raw2189step1 = -raw2189step0 := by apply Matrix.ext; change ∀ i j, raw2189step1 i j = -(raw2189step0 i j); unfold raw2189step1 raw2189step0; decide +kernel
      have hl : raw2189step1Labels = raw2189step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2189step1 raw2189step1Labels = mixedMoment B raw2189step2 raw2189step2Labels := by
      have ha : raw2189step2 = raw2189step1 := by apply Matrix.ext; unfold raw2189step2 raw2189step1; decide +kernel
      have hl : raw2189step1Labels = labelEmbedding1 ∘ raw2189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2189step1 raw2189step1Labels raw2189step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3563 node3563Labels := by rfl

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

theorem canonical2250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2250 raw2250Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw2250 raw2250Labels = mixedMoment B raw2250step0 raw2250step0Labels := by
      have ha : raw2250step0 = (fun i j => raw2250 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2250step0 raw2250; decide +kernel
      have hl : raw2250step0Labels = raw2250Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2250 raw2250Labels permutation32 permutation4
    mixedMoment B raw2250step0 raw2250step0Labels = mixedMoment B raw2250step1 raw2250step1Labels := by
      have ha : raw2250step1 = raw2250step0 := by apply Matrix.ext; unfold raw2250step1 raw2250step0; decide +kernel
      have hl : raw2250step0Labels = labelEmbedding7 ∘ raw2250step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2250step0 raw2250step0Labels raw2250step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

theorem canonical2251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2251 raw2251Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw2251 raw2251Labels = mixedMoment B raw2251step0 raw2251step0Labels := by
      have ha : raw2251step0 = (fun i j => raw2251 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2251step0 raw2251; decide +kernel
      have hl : raw2251step0Labels = raw2251Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2251 raw2251Labels permutation32 permutation4
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical2252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2252 raw2252Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw2252 raw2252Labels = mixedMoment B raw2252step0 raw2252step0Labels := by
      have ha : raw2252step0 = (fun i j => raw2252 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2252step0 raw2252; decide +kernel
      have hl : raw2252step0Labels = raw2252Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2252 raw2252Labels permutation32 permutation6
    mixedMoment B raw2252step0 raw2252step0Labels = mixedMoment B raw2252step1 raw2252step1Labels := by
      have ha : raw2252step1 = -raw2252step0 := by apply Matrix.ext; change ∀ i j, raw2252step1 i j = -(raw2252step0 i j); unfold raw2252step1 raw2252step0; decide +kernel
      have hl : raw2252step1Labels = raw2252step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2252step1 raw2252step1Labels = mixedMoment B raw2252step2 raw2252step2Labels := by
      have ha : raw2252step2 = raw2252step1 := by apply Matrix.ext; unfold raw2252step2 raw2252step1; decide +kernel
      have hl : raw2252step1Labels = labelEmbedding1 ∘ raw2252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2252step1 raw2252step1Labels raw2252step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3391 node3391Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2475 raw2475Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw2475 raw2475Labels = mixedMoment B raw2475step0 raw2475step0Labels := by
      have ha : raw2475step0 = (fun i j => raw2475 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2475step0 raw2475; decide +kernel
      have hl : raw2475step0Labels = raw2475Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2475 raw2475Labels permutation152 permutation4
    mixedMoment B raw2475step0 raw2475step0Labels = mixedMoment B raw2475step1 raw2475step1Labels := by
      have ha : raw2475step1 = raw2475step0 := by apply Matrix.ext; unfold raw2475step1 raw2475step0; decide +kernel
      have hl : raw2475step0Labels = labelEmbedding7 ∘ raw2475step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2475step0 raw2475step0Labels raw2475step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical2476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2476 raw2476Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw2476 raw2476Labels = mixedMoment B raw2476step0 raw2476step0Labels := by
      have ha : raw2476step0 = (fun i j => raw2476 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2476step0 raw2476; decide +kernel
      have hl : raw2476step0Labels = raw2476Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2476 raw2476Labels permutation152 permutation4
    _ = mixedMoment B node3787 node3787Labels := by rfl

theorem canonical2477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2477 raw2477Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw2477 raw2477Labels = mixedMoment B raw2477step0 raw2477step0Labels := by
      have ha : raw2477step0 = (fun i j => raw2477 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2477step0 raw2477; decide +kernel
      have hl : raw2477step0Labels = raw2477Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2477 raw2477Labels permutation158 permutation6
    mixedMoment B raw2477step0 raw2477step0Labels = mixedMoment B raw2477step1 raw2477step1Labels := by
      have ha : raw2477step1 = -raw2477step0 := by apply Matrix.ext; change ∀ i j, raw2477step1 i j = -(raw2477step0 i j); unfold raw2477step1 raw2477step0; decide +kernel
      have hl : raw2477step1Labels = raw2477step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2477step1 raw2477step1Labels = mixedMoment B raw2477step2 raw2477step2Labels := by
      have ha : raw2477step2 = raw2477step1 := by apply Matrix.ext; unfold raw2477step2 raw2477step1; decide +kernel
      have hl : raw2477step1Labels = labelEmbedding1 ∘ raw2477step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2477step1 raw2477step1Labels raw2477step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

theorem canonical2481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2481 raw2481Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw2481 raw2481Labels = mixedMoment B raw2481step0 raw2481step0Labels := by
      have ha : raw2481step0 = (fun i j => raw2481 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2481step0 raw2481; decide +kernel
      have hl : raw2481step0Labels = raw2481Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2481 raw2481Labels permutation32 permutation4
    mixedMoment B raw2481step0 raw2481step0Labels = mixedMoment B raw2481step1 raw2481step1Labels := by
      have ha : raw2481step1 = raw2481step0 := by apply Matrix.ext; unfold raw2481step1 raw2481step0; decide +kernel
      have hl : raw2481step0Labels = labelEmbedding7 ∘ raw2481step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2481step0 raw2481step0Labels raw2481step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

theorem canonical2482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2482 raw2482Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw2482 raw2482Labels = mixedMoment B raw2482step0 raw2482step0Labels := by
      have ha : raw2482step0 = (fun i j => raw2482 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2482step0 raw2482; decide +kernel
      have hl : raw2482step0Labels = raw2482Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2482 raw2482Labels permutation32 permutation4
    _ = mixedMoment B node3790 node3790Labels := by rfl

theorem canonical2483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2483 raw2483Labels = mixedMoment B node3815 node3815Labels := by
  calc
    mixedMoment B raw2483 raw2483Labels = mixedMoment B raw2483step0 raw2483step0Labels := by
      have ha : raw2483step0 = (fun i j => raw2483 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2483step0 raw2483; decide +kernel
      have hl : raw2483step0Labels = raw2483Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2483 raw2483Labels permutation32 permutation6
    mixedMoment B raw2483step0 raw2483step0Labels = mixedMoment B raw2483step1 raw2483step1Labels := by
      have ha : raw2483step1 = -raw2483step0 := by apply Matrix.ext; change ∀ i j, raw2483step1 i j = -(raw2483step0 i j); unfold raw2483step1 raw2483step0; decide +kernel
      have hl : raw2483step1Labels = raw2483step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2483step1 raw2483step1Labels = mixedMoment B raw2483step2 raw2483step2Labels := by
      have ha : raw2483step2 = raw2483step1 := by apply Matrix.ext; unfold raw2483step2 raw2483step1; decide +kernel
      have hl : raw2483step1Labels = labelEmbedding1 ∘ raw2483step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2483step1 raw2483step1Labels raw2483step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3815 node3815Labels := by rfl

theorem canonical2490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2490 raw2490Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw2490 raw2490Labels = mixedMoment B raw2490step0 raw2490step0Labels := by
      have ha : raw2490step0 = (fun i j => raw2490 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2490step0 raw2490; decide +kernel
      have hl : raw2490step0Labels = raw2490Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2490 raw2490Labels permutation32 permutation4
    mixedMoment B raw2490step0 raw2490step0Labels = mixedMoment B raw2490step1 raw2490step1Labels := by
      have ha : raw2490step1 = raw2490step0 := by apply Matrix.ext; unfold raw2490step1 raw2490step0; decide +kernel
      have hl : raw2490step0Labels = labelEmbedding7 ∘ raw2490step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2490step0 raw2490step0Labels raw2490step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical2491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2491 raw2491Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw2491 raw2491Labels = mixedMoment B raw2491step0 raw2491step0Labels := by
      have ha : raw2491step0 = (fun i j => raw2491 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2491step0 raw2491; decide +kernel
      have hl : raw2491step0Labels = raw2491Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2491 raw2491Labels permutation32 permutation4
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical2492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2492 raw2492Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw2492 raw2492Labels = mixedMoment B raw2492step0 raw2492step0Labels := by
      have ha : raw2492step0 = (fun i j => raw2492 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2492step0 raw2492; decide +kernel
      have hl : raw2492step0Labels = raw2492Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2492 raw2492Labels permutation36 permutation6
    mixedMoment B raw2492step0 raw2492step0Labels = mixedMoment B raw2492step1 raw2492step1Labels := by
      have ha : raw2492step1 = -raw2492step0 := by apply Matrix.ext; change ∀ i j, raw2492step1 i j = -(raw2492step0 i j); unfold raw2492step1 raw2492step0; decide +kernel
      have hl : raw2492step1Labels = raw2492step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2492step1 raw2492step1Labels = mixedMoment B raw2492step2 raw2492step2Labels := by
      have ha : raw2492step2 = raw2492step1 := by apply Matrix.ext; unfold raw2492step2 raw2492step1; decide +kernel
      have hl : raw2492step1Labels = labelEmbedding1 ∘ raw2492step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2492step1 raw2492step1Labels raw2492step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical2559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2559 raw2559Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw2559 raw2559Labels = mixedMoment B raw2559step0 raw2559step0Labels := by
      have ha : raw2559step0 = (fun i j => raw2559 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2559step0 raw2559; decide +kernel
      have hl : raw2559step0Labels = raw2559Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2559 raw2559Labels permutation8 permutation4
    mixedMoment B raw2559step0 raw2559step0Labels = mixedMoment B raw2559step1 raw2559step1Labels := by
      have ha : raw2559step1 = raw2559step0 := by apply Matrix.ext; unfold raw2559step1 raw2559step0; decide +kernel
      have hl : raw2559step0Labels = labelEmbedding7 ∘ raw2559step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2559step0 raw2559step0Labels raw2559step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

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

theorem canonical2560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2560 raw2560Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw2560 raw2560Labels = mixedMoment B raw2560step0 raw2560step0Labels := by
      have ha : raw2560step0 = (fun i j => raw2560 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2560step0 raw2560; decide +kernel
      have hl : raw2560step0Labels = raw2560Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2560 raw2560Labels permutation8 permutation4
    _ = mixedMoment B node3888 node3888Labels := by rfl

theorem canonical2561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2561 raw2561Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw2561 raw2561Labels = mixedMoment B raw2561step0 raw2561step0Labels := by
      have ha : raw2561step0 = (fun i j => raw2561 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2561step0 raw2561; decide +kernel
      have hl : raw2561step0Labels = raw2561Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2561 raw2561Labels permutation10 permutation6
    mixedMoment B raw2561step0 raw2561step0Labels = mixedMoment B raw2561step1 raw2561step1Labels := by
      have ha : raw2561step1 = -raw2561step0 := by apply Matrix.ext; change ∀ i j, raw2561step1 i j = -(raw2561step0 i j); unfold raw2561step1 raw2561step0; decide +kernel
      have hl : raw2561step1Labels = raw2561step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2561step1 raw2561step1Labels = mixedMoment B raw2561step2 raw2561step2Labels := by
      have ha : raw2561step2 = raw2561step1 := by apply Matrix.ext; unfold raw2561step2 raw2561step1; decide +kernel
      have hl : raw2561step1Labels = labelEmbedding1 ∘ raw2561step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2561step1 raw2561step1Labels raw2561step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3913 node3913Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical223
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28619 raw28619Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw28619 raw28619Labels = mixedMoment B raw28619step0 raw28619step0Labels := by
      have hz : ∀ j, raw28619 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28619step0 = (fun i j => raw28619 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28619step0 raw28619; decide +kernel
      have hl : raw28619step0Labels = raw28619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28619 raw28619Labels permutation434 hz
    mixedMoment B raw28619step0 raw28619step0Labels = mixedMoment B raw28619step1 raw28619step1Labels := by
      have hz : ∀ j, raw28619step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28619step1 = (fun i j => raw28619step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28619step1 raw28619step0; decide +kernel
      have hl : raw28619step1Labels = raw28619step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28619step0 raw28619step0Labels permutation80 hz
    mixedMoment B raw28619step1 raw28619step1Labels = mixedMoment B raw28619step2 raw28619step2Labels := by
      have ha : raw28619step2 = (fun i j => raw28619step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28619step2 raw28619step1; decide +kernel
      have hl : raw28619step2Labels = raw28619step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28619step1 raw28619step1Labels permutation8 permutation3
    mixedMoment B raw28619step2 raw28619step2Labels = mixedMoment B raw28619step3 raw28619step3Labels := by
      have ha : raw28619step3 = raw28619step2 := by apply Matrix.ext; unfold raw28619step3 raw28619step2; decide +kernel
      have hl : raw28619step2Labels = labelEmbedding6 ∘ raw28619step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28619step2 raw28619step2Labels raw28619step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical28624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28624 raw28624Labels = mixedMoment B node4338 node4338Labels := by
  calc
    mixedMoment B raw28624 raw28624Labels = mixedMoment B raw28624step0 raw28624step0Labels := by
      have hz : ∀ j, raw28624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28624step0 = (fun i j => raw28624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28624step0 raw28624; decide +kernel
      have hl : raw28624step0Labels = raw28624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28624 raw28624Labels permutation346 hz
    mixedMoment B raw28624step0 raw28624step0Labels = mixedMoment B raw28624step1 raw28624step1Labels := by
      have ha : raw28624step1 = (fun i j => raw28624step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28624step1 raw28624step0; decide +kernel
      have hl : raw28624step1Labels = raw28624step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28624step0 raw28624step0Labels permutation34 permutation3
    mixedMoment B raw28624step1 raw28624step1Labels = mixedMoment B raw28624step2 raw28624step2Labels := by
      have ha : raw28624step2 = raw28624step1 := by apply Matrix.ext; unfold raw28624step2 raw28624step1; decide +kernel
      have hl : raw28624step1Labels = labelEmbedding6 ∘ raw28624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28624step1 raw28624step1Labels raw28624step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4338 node4338Labels := by rfl

theorem canonical28625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28625 raw28625Labels = mixedMoment B node4726 node4726Labels := by
  calc
    mixedMoment B raw28625 raw28625Labels = mixedMoment B raw28625step0 raw28625step0Labels := by
      have hz : ∀ j, raw28625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28625step0 = (fun i j => raw28625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28625step0 raw28625; decide +kernel
      have hl : raw28625step0Labels = raw28625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28625 raw28625Labels permutation346 hz
    mixedMoment B raw28625step0 raw28625step0Labels = mixedMoment B raw28625step1 raw28625step1Labels := by
      have ha : raw28625step1 = (fun i j => raw28625step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28625step1 raw28625step0; decide +kernel
      have hl : raw28625step1Labels = raw28625step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28625step0 raw28625step0Labels permutation145 permutation3
    mixedMoment B raw28625step1 raw28625step1Labels = mixedMoment B raw28625step2 raw28625step2Labels := by
      have ha : raw28625step2 = -raw28625step1 := by apply Matrix.ext; change ∀ i j, raw28625step2 i j = -(raw28625step1 i j); unfold raw28625step2 raw28625step1; decide +kernel
      have hl : raw28625step2Labels = raw28625step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28625step2 raw28625step2Labels = mixedMoment B raw28625step3 raw28625step3Labels := by
      have ha : raw28625step3 = raw28625step2 := by apply Matrix.ext; unfold raw28625step3 raw28625step2; decide +kernel
      have hl : raw28625step2Labels = labelEmbedding6 ∘ raw28625step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28625step2 raw28625step2Labels raw28625step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4726 node4726Labels := by rfl

theorem canonical28626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28626 raw28626Labels = mixedMoment B node4721 node4721Labels := by
  calc
    mixedMoment B raw28626 raw28626Labels = mixedMoment B raw28626step0 raw28626step0Labels := by
      have ha : raw28626step0 = (fun i j => raw28626 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28626step0 raw28626; decide +kernel
      have hl : raw28626step0Labels = raw28626Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28626 raw28626Labels permutation662 permutation3
    mixedMoment B raw28626step0 raw28626step0Labels = mixedMoment B raw28626step1 raw28626step1Labels := by
      have ha : raw28626step1 = -raw28626step0 := by apply Matrix.ext; change ∀ i j, raw28626step1 i j = -(raw28626step0 i j); unfold raw28626step1 raw28626step0; decide +kernel
      have hl : raw28626step1Labels = raw28626step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28626step1 raw28626step1Labels = mixedMoment B raw28626step2 raw28626step2Labels := by
      have ha : raw28626step2 = raw28626step1 := by apply Matrix.ext; unfold raw28626step2 raw28626step1; decide +kernel
      have hl : raw28626step1Labels = labelEmbedding6 ∘ raw28626step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28626step1 raw28626step1Labels raw28626step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4721 node4721Labels := by rfl

theorem canonical28627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28627 raw28627Labels = mixedMoment B node4744 node4744Labels := by
  calc
    mixedMoment B raw28627 raw28627Labels = mixedMoment B raw28627step0 raw28627step0Labels := by
      have hz : ∀ j, raw28627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28627step0 = (fun i j => raw28627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28627step0 raw28627; decide +kernel
      have hl : raw28627step0Labels = raw28627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28627 raw28627Labels permutation346 hz
    mixedMoment B raw28627step0 raw28627step0Labels = mixedMoment B raw28627step1 raw28627step1Labels := by
      have ha : raw28627step1 = (fun i j => raw28627step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28627step1 raw28627step0; decide +kernel
      have hl : raw28627step1Labels = raw28627step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28627step0 raw28627step0Labels permutation143 permutation5
    mixedMoment B raw28627step1 raw28627step1Labels = mixedMoment B raw28627step2 raw28627step2Labels := by
      have ha : raw28627step2 = raw28627step1 := by apply Matrix.ext; unfold raw28627step2 raw28627step1; decide +kernel
      have hl : raw28627step1Labels = labelEmbedding8 ∘ raw28627step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28627step1 raw28627step1Labels raw28627step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4744 node4744Labels := by rfl

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

theorem canonical29536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29536 raw29536Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw29536 raw29536Labels = mixedMoment B raw29536step0 raw29536step0Labels := by
      have hz : ∀ j, raw29536 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29536step0 = (fun i j => raw29536 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29536step0 raw29536; decide +kernel
      have hl : raw29536step0Labels = raw29536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29536 raw29536Labels permutation346 hz
    mixedMoment B raw29536step0 raw29536step0Labels = mixedMoment B raw29536step1 raw29536step1Labels := by
      have ha : raw29536step1 = (fun i j => raw29536step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29536step1 raw29536step0; decide +kernel
      have hl : raw29536step1Labels = raw29536step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29536step0 raw29536step0Labels permutation32 permutation3
    mixedMoment B raw29536step1 raw29536step1Labels = mixedMoment B raw29536step2 raw29536step2Labels := by
      have ha : raw29536step2 = raw29536step1 := by apply Matrix.ext; unfold raw29536step2 raw29536step1; decide +kernel
      have hl : raw29536step1Labels = labelEmbedding6 ∘ raw29536step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29536step1 raw29536step1Labels raw29536step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4354 node4354Labels := by rfl

theorem canonical29537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29537 raw29537Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw29537 raw29537Labels = mixedMoment B raw29537step0 raw29537step0Labels := by
      have hz : ∀ j, raw29537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29537step0 = (fun i j => raw29537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29537step0 raw29537; decide +kernel
      have hl : raw29537step0Labels = raw29537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29537 raw29537Labels permutation346 hz
    mixedMoment B raw29537step0 raw29537step0Labels = mixedMoment B raw29537step1 raw29537step1Labels := by
      have ha : raw29537step1 = (fun i j => raw29537step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29537step1 raw29537step0; decide +kernel
      have hl : raw29537step1Labels = raw29537step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29537step0 raw29537step0Labels permutation32 permutation3
    mixedMoment B raw29537step1 raw29537step1Labels = mixedMoment B raw29537step2 raw29537step2Labels := by
      have ha : raw29537step2 = raw29537step1 := by apply Matrix.ext; unfold raw29537step2 raw29537step1; decide +kernel
      have hl : raw29537step1Labels = labelEmbedding6 ∘ raw29537step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29537step1 raw29537step1Labels raw29537step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

theorem canonical29538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29538 raw29538Labels = mixedMoment B node5038 node5038Labels := by
  calc
    mixedMoment B raw29538 raw29538Labels = mixedMoment B raw29538step0 raw29538step0Labels := by
      have ha : raw29538step0 = (fun i j => raw29538 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29538step0 raw29538; decide +kernel
      have hl : raw29538step0Labels = raw29538Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29538 raw29538Labels permutation176 permutation3
    mixedMoment B raw29538step0 raw29538step0Labels = mixedMoment B raw29538step1 raw29538step1Labels := by
      have ha : raw29538step1 = raw29538step0 := by apply Matrix.ext; unfold raw29538step1 raw29538step0; decide +kernel
      have hl : raw29538step0Labels = labelEmbedding6 ∘ raw29538step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29538step0 raw29538step0Labels raw29538step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5038 node5038Labels := by rfl

theorem canonical29539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29539 raw29539Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw29539 raw29539Labels = mixedMoment B raw29539step0 raw29539step0Labels := by
      have hz : ∀ j, raw29539 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29539step0 = (fun i j => raw29539 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29539step0 raw29539; decide +kernel
      have hl : raw29539step0Labels = raw29539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29539 raw29539Labels permutation346 hz
    mixedMoment B raw29539step0 raw29539step0Labels = mixedMoment B raw29539step1 raw29539step1Labels := by
      have ha : raw29539step1 = (fun i j => raw29539step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29539step1 raw29539step0; decide +kernel
      have hl : raw29539step1Labels = raw29539step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29539step0 raw29539step0Labels permutation33 permutation3
    mixedMoment B raw29539step1 raw29539step1Labels = mixedMoment B raw29539step2 raw29539step2Labels := by
      have ha : raw29539step2 = raw29539step1 := by apply Matrix.ext; unfold raw29539step2 raw29539step1; decide +kernel
      have hl : raw29539step1Labels = labelEmbedding6 ∘ raw29539step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29539step1 raw29539step1Labels raw29539step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32791 raw32791Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw32791 raw32791Labels = mixedMoment B raw32791step0 raw32791step0Labels := by
      have hz : ∀ j, raw32791 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32791step0 = (fun i j => raw32791 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32791step0 raw32791; decide +kernel
      have hl : raw32791step0Labels = raw32791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32791 raw32791Labels permutation346 hz
    mixedMoment B raw32791step0 raw32791step0Labels = mixedMoment B raw32791step1 raw32791step1Labels := by
      have ha : raw32791step1 = (fun i j => raw32791step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32791step1 raw32791step0; decide +kernel
      have hl : raw32791step1Labels = raw32791step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32791step0 raw32791step0Labels permutation144 permutation3
    mixedMoment B raw32791step1 raw32791step1Labels = mixedMoment B raw32791step2 raw32791step2Labels := by
      have ha : raw32791step2 = -raw32791step1 := by apply Matrix.ext; change ∀ i j, raw32791step2 i j = -(raw32791step1 i j); unfold raw32791step2 raw32791step1; decide +kernel
      have hl : raw32791step2Labels = raw32791step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32791step2 raw32791step2Labels = mixedMoment B raw32791step3 raw32791step3Labels := by
      have ha : raw32791step3 = raw32791step2 := by apply Matrix.ext; unfold raw32791step3 raw32791step2; decide +kernel
      have hl : raw32791step2Labels = labelEmbedding6 ∘ raw32791step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32791step2 raw32791step2Labels raw32791step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

theorem canonical32792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32792 raw32792Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw32792 raw32792Labels = mixedMoment B raw32792step0 raw32792step0Labels := by
      have ha : raw32792step0 = (fun i j => raw32792 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32792step0 raw32792; decide +kernel
      have hl : raw32792step0Labels = raw32792Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32792 raw32792Labels permutation662 permutation3
    mixedMoment B raw32792step0 raw32792step0Labels = mixedMoment B raw32792step1 raw32792step1Labels := by
      have ha : raw32792step1 = -raw32792step0 := by apply Matrix.ext; change ∀ i j, raw32792step1 i j = -(raw32792step0 i j); unfold raw32792step1 raw32792step0; decide +kernel
      have hl : raw32792step1Labels = raw32792step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32792step1 raw32792step1Labels = mixedMoment B raw32792step2 raw32792step2Labels := by
      have ha : raw32792step2 = raw32792step1 := by apply Matrix.ext; unfold raw32792step2 raw32792step1; decide +kernel
      have hl : raw32792step1Labels = labelEmbedding6 ∘ raw32792step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32792step1 raw32792step1Labels raw32792step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical32793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32793 raw32793Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw32793 raw32793Labels = mixedMoment B raw32793step0 raw32793step0Labels := by
      have hz : ∀ j, raw32793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32793step0 = (fun i j => raw32793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32793step0 raw32793; decide +kernel
      have hl : raw32793step0Labels = raw32793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32793 raw32793Labels permutation346 hz
    mixedMoment B raw32793step0 raw32793step0Labels = mixedMoment B raw32793step1 raw32793step1Labels := by
      have ha : raw32793step1 = (fun i j => raw32793step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32793step1 raw32793step0; decide +kernel
      have hl : raw32793step1Labels = raw32793step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32793step0 raw32793step0Labels permutation142 permutation5
    mixedMoment B raw32793step1 raw32793step1Labels = mixedMoment B raw32793step2 raw32793step2Labels := by
      have ha : raw32793step2 = raw32793step1 := by apply Matrix.ext; unfold raw32793step2 raw32793step1; decide +kernel
      have hl : raw32793step1Labels = labelEmbedding8 ∘ raw32793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32793step1 raw32793step1Labels raw32793step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical32794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32794 raw32794Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw32794 raw32794Labels = mixedMoment B raw32794step0 raw32794step0Labels := by
      have hz : ∀ j, raw32794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32794step0 = (fun i j => raw32794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32794step0 raw32794; decide +kernel
      have hl : raw32794step0Labels = raw32794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32794 raw32794Labels permutation346 hz
    mixedMoment B raw32794step0 raw32794step0Labels = mixedMoment B raw32794step1 raw32794step1Labels := by
      have ha : raw32794step1 = (fun i j => raw32794step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32794step1 raw32794step0; decide +kernel
      have hl : raw32794step1Labels = raw32794step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32794step0 raw32794step0Labels permutation33 permutation2
    _ = mixedMoment B node5485 node5485Labels := by rfl

theorem canonical32795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32795 raw32795Labels = mixedMoment B node4337 node4337Labels := by
  calc
    mixedMoment B raw32795 raw32795Labels = mixedMoment B raw32795step0 raw32795step0Labels := by
      have ha : raw32795step0 = (fun i j => raw32795 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32795step0 raw32795; decide +kernel
      have hl : raw32795step0Labels = raw32795Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32795 raw32795Labels permutation164 permutation3
    mixedMoment B raw32795step0 raw32795step0Labels = mixedMoment B raw32795step1 raw32795step1Labels := by
      have ha : raw32795step1 = raw32795step0 := by apply Matrix.ext; unfold raw32795step1 raw32795step0; decide +kernel
      have hl : raw32795step0Labels = labelEmbedding6 ∘ raw32795step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32795step0 raw32795step0Labels raw32795step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4337 node4337Labels := by rfl

theorem canonical32796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32796 raw32796Labels = mixedMoment B node4936 node4936Labels := by
  calc
    mixedMoment B raw32796 raw32796Labels = mixedMoment B raw32796step0 raw32796step0Labels := by
      have ha : raw32796step0 = (fun i j => raw32796 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32796step0 raw32796; decide +kernel
      have hl : raw32796step0Labels = raw32796Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32796 raw32796Labels permutation164 permutation3
    mixedMoment B raw32796step0 raw32796step0Labels = mixedMoment B raw32796step1 raw32796step1Labels := by
      have ha : raw32796step1 = raw32796step0 := by apply Matrix.ext; unfold raw32796step1 raw32796step0; decide +kernel
      have hl : raw32796step0Labels = labelEmbedding6 ∘ raw32796step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32796step0 raw32796step0Labels raw32796step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4936 node4936Labels := by rfl

theorem canonical32797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32797 raw32797Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw32797 raw32797Labels = mixedMoment B raw32797step0 raw32797step0Labels := by
      have ha : raw32797step0 = (fun i j => raw32797 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32797step0 raw32797; decide +kernel
      have hl : raw32797step0Labels = raw32797Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32797 raw32797Labels permutation164 permutation3
    mixedMoment B raw32797step0 raw32797step0Labels = mixedMoment B raw32797step1 raw32797step1Labels := by
      have ha : raw32797step1 = raw32797step0 := by apply Matrix.ext; unfold raw32797step1 raw32797step0; decide +kernel
      have hl : raw32797step0Labels = labelEmbedding6 ∘ raw32797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32797step0 raw32797step0Labels raw32797step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

theorem canonical32798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32798 raw32798Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw32798 raw32798Labels = mixedMoment B raw32798step0 raw32798step0Labels := by
      have ha : raw32798step0 = (fun i j => raw32798 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32798step0 raw32798; decide +kernel
      have hl : raw32798step0Labels = raw32798Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32798 raw32798Labels permutation164 permutation3
    mixedMoment B raw32798step0 raw32798step0Labels = mixedMoment B raw32798step1 raw32798step1Labels := by
      have ha : raw32798step1 = raw32798step0 := by apply Matrix.ext; unfold raw32798step1 raw32798step0; decide +kernel
      have hl : raw32798step0Labels = labelEmbedding6 ∘ raw32798step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32798step0 raw32798step0Labels raw32798step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5162 node5162Labels := by rfl

theorem canonical32799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32799 raw32799Labels = mixedMoment B node4339 node4339Labels := by
  calc
    mixedMoment B raw32799 raw32799Labels = mixedMoment B raw32799step0 raw32799step0Labels := by
      have hz : ∀ j, raw32799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32799step0 = (fun i j => raw32799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32799step0 raw32799; decide +kernel
      have hl : raw32799step0Labels = raw32799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32799 raw32799Labels permutation346 hz
    mixedMoment B raw32799step0 raw32799step0Labels = mixedMoment B raw32799step1 raw32799step1Labels := by
      have ha : raw32799step1 = (fun i j => raw32799step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32799step1 raw32799step0; decide +kernel
      have hl : raw32799step1Labels = raw32799step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32799step0 raw32799step0Labels permutation34 permutation3
    mixedMoment B raw32799step1 raw32799step1Labels = mixedMoment B raw32799step2 raw32799step2Labels := by
      have ha : raw32799step2 = raw32799step1 := by apply Matrix.ext; unfold raw32799step2 raw32799step1; decide +kernel
      have hl : raw32799step1Labels = labelEmbedding6 ∘ raw32799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32799step1 raw32799step1Labels raw32799step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4339 node4339Labels := by rfl

theorem canonical32800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32800 raw32800Labels = mixedMoment B node4937 node4937Labels := by
  calc
    mixedMoment B raw32800 raw32800Labels = mixedMoment B raw32800step0 raw32800step0Labels := by
      have hz : ∀ j, raw32800 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32800step0 = (fun i j => raw32800 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32800step0 raw32800; decide +kernel
      have hl : raw32800step0Labels = raw32800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32800 raw32800Labels permutation346 hz
    mixedMoment B raw32800step0 raw32800step0Labels = mixedMoment B raw32800step1 raw32800step1Labels := by
      have ha : raw32800step1 = (fun i j => raw32800step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32800step1 raw32800step0; decide +kernel
      have hl : raw32800step1Labels = raw32800step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32800step0 raw32800step0Labels permutation34 permutation3
    mixedMoment B raw32800step1 raw32800step1Labels = mixedMoment B raw32800step2 raw32800step2Labels := by
      have ha : raw32800step2 = raw32800step1 := by apply Matrix.ext; unfold raw32800step2 raw32800step1; decide +kernel
      have hl : raw32800step1Labels = labelEmbedding6 ∘ raw32800step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32800step1 raw32800step1Labels raw32800step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4937 node4937Labels := by rfl

theorem canonical32801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32801 raw32801Labels = mixedMoment B node5032 node5032Labels := by
  calc
    mixedMoment B raw32801 raw32801Labels = mixedMoment B raw32801step0 raw32801step0Labels := by
      have ha : raw32801step0 = (fun i j => raw32801 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32801step0 raw32801; decide +kernel
      have hl : raw32801step0Labels = raw32801Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32801 raw32801Labels permutation178 permutation3
    mixedMoment B raw32801step0 raw32801step0Labels = mixedMoment B raw32801step1 raw32801step1Labels := by
      have ha : raw32801step1 = raw32801step0 := by apply Matrix.ext; unfold raw32801step1 raw32801step0; decide +kernel
      have hl : raw32801step0Labels = labelEmbedding6 ∘ raw32801step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32801step0 raw32801step0Labels raw32801step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5032 node5032Labels := by rfl

theorem canonical32802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32802 raw32802Labels = mixedMoment B node5125 node5125Labels := by
  calc
    mixedMoment B raw32802 raw32802Labels = mixedMoment B raw32802step0 raw32802step0Labels := by
      have hz : ∀ j, raw32802 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32802step0 = (fun i j => raw32802 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32802step0 raw32802; decide +kernel
      have hl : raw32802step0Labels = raw32802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32802 raw32802Labels permutation346 hz
    mixedMoment B raw32802step0 raw32802step0Labels = mixedMoment B raw32802step1 raw32802step1Labels := by
      have ha : raw32802step1 = (fun i j => raw32802step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32802step1 raw32802step0; decide +kernel
      have hl : raw32802step1Labels = raw32802step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32802step0 raw32802step0Labels permutation34 permutation3
    mixedMoment B raw32802step1 raw32802step1Labels = mixedMoment B raw32802step2 raw32802step2Labels := by
      have ha : raw32802step2 = raw32802step1 := by apply Matrix.ext; unfold raw32802step2 raw32802step1; decide +kernel
      have hl : raw32802step1Labels = labelEmbedding6 ∘ raw32802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32802step1 raw32802step1Labels raw32802step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5125 node5125Labels := by rfl

theorem canonical32803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32803 raw32803Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw32803 raw32803Labels = mixedMoment B raw32803step0 raw32803step0Labels := by
      have hz : ∀ j, raw32803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32803step0 = (fun i j => raw32803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32803step0 raw32803; decide +kernel
      have hl : raw32803step0Labels = raw32803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32803 raw32803Labels permutation346 hz
    mixedMoment B raw32803step0 raw32803step0Labels = mixedMoment B raw32803step1 raw32803step1Labels := by
      have ha : raw32803step1 = (fun i j => raw32803step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32803step1 raw32803step0; decide +kernel
      have hl : raw32803step1Labels = raw32803step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32803step0 raw32803step0Labels permutation35 permutation3
    mixedMoment B raw32803step1 raw32803step1Labels = mixedMoment B raw32803step2 raw32803step2Labels := by
      have ha : raw32803step2 = raw32803step1 := by apply Matrix.ext; unfold raw32803step2 raw32803step1; decide +kernel
      have hl : raw32803step1Labels = labelEmbedding6 ∘ raw32803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32803step1 raw32803step1Labels raw32803step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw544 raw544Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw544 raw544Labels = mixedMoment B raw544step0 raw544step0Labels := by
      have ha : raw544step0 = (fun i j => raw544 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw544step0 raw544; decide +kernel
      have hl : raw544step0Labels = raw544Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw544 raw544Labels permutation8 permutation5
    mixedMoment B raw544step0 raw544step0Labels = mixedMoment B raw544step1 raw544step1Labels := by
      have ha : raw544step1 = raw544step0 := by apply Matrix.ext; unfold raw544step1 raw544step0; decide +kernel
      have hl : raw544step0Labels = labelEmbedding1 ∘ raw544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw544step0 raw544step0Labels raw544step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3888 node3888Labels := by rfl

theorem canonical545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw545 raw545Labels = mixedMoment B node503 node503Labels := by
  calc
    mixedMoment B raw545 raw545Labels = mixedMoment B raw545step0 raw545step0Labels := by
      have ha : raw545step0 = (fun i j => raw545 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw545step0 raw545; decide +kernel
      have hl : raw545step0Labels = raw545Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw545 raw545Labels permutation8 permutation5
    _ = mixedMoment B node503 node503Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9592 raw9592Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw9592 raw9592Labels = mixedMoment B raw9592step0 raw9592step0Labels := by
      have hz : ∀ j, raw9592 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9592step0 = (fun i j => raw9592 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9592step0 raw9592; decide +kernel
      have hl : raw9592step0Labels = raw9592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9592 raw9592Labels permutation434 hz
    mixedMoment B raw9592step0 raw9592step0Labels = mixedMoment B raw9592step1 raw9592step1Labels := by
      have hz : ∀ j, raw9592step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9592step1 = (fun i j => raw9592step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9592step1 raw9592step0; decide +kernel
      have hl : raw9592step1Labels = raw9592step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9592step0 raw9592step0Labels permutation80 hz
    mixedMoment B raw9592step1 raw9592step1Labels = mixedMoment B raw9592step2 raw9592step2Labels := by
      have ha : raw9592step2 = (fun i j => raw9592step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9592step2 raw9592step1; decide +kernel
      have hl : raw9592step2Labels = raw9592step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9592step1 raw9592step1Labels permutation31 permutation3
    mixedMoment B raw9592step2 raw9592step2Labels = mixedMoment B raw9592step3 raw9592step3Labels := by
      have ha : raw9592step3 = -raw9592step2 := by apply Matrix.ext; change ∀ i j, raw9592step3 i j = -(raw9592step2 i j); unfold raw9592step3 raw9592step2; decide +kernel
      have hl : raw9592step3Labels = raw9592step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9592step3 raw9592step3Labels = mixedMoment B raw9592step4 raw9592step4Labels := by
      have ha : raw9592step4 = raw9592step3 := by apply Matrix.ext; unfold raw9592step4 raw9592step3; decide +kernel
      have hl : raw9592step3Labels = labelEmbedding6 ∘ raw9592step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9592step3 raw9592step3Labels raw9592step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9603 raw9603Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw9603 raw9603Labels = mixedMoment B raw9603step0 raw9603step0Labels := by
      have hz : ∀ j, raw9603 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9603step0 = (fun i j => raw9603 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9603step0 raw9603; decide +kernel
      have hl : raw9603step0Labels = raw9603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9603 raw9603Labels permutation434 hz
    mixedMoment B raw9603step0 raw9603step0Labels = mixedMoment B raw9603step1 raw9603step1Labels := by
      have ha : raw9603step1 = (fun i j => raw9603step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9603step1 raw9603step0; decide +kernel
      have hl : raw9603step1Labels = raw9603step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9603step0 raw9603step0Labels permutation34 permutation3
    mixedMoment B raw9603step1 raw9603step1Labels = mixedMoment B raw9603step2 raw9603step2Labels := by
      have ha : raw9603step2 = raw9603step1 := by apply Matrix.ext; unfold raw9603step2 raw9603step1; decide +kernel
      have hl : raw9603step1Labels = labelEmbedding6 ∘ raw9603step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9603step1 raw9603step1Labels raw9603step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

theorem canonical9607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9607 raw9607Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw9607 raw9607Labels = mixedMoment B raw9607step0 raw9607step0Labels := by
      have hz : ∀ j, raw9607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9607step0 = (fun i j => raw9607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9607step0 raw9607; decide +kernel
      have hl : raw9607step0Labels = raw9607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9607 raw9607Labels permutation346 hz
    mixedMoment B raw9607step0 raw9607step0Labels = mixedMoment B raw9607step1 raw9607step1Labels := by
      have ha : raw9607step1 = (fun i j => raw9607step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9607step1 raw9607step0; decide +kernel
      have hl : raw9607step1Labels = raw9607step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9607step0 raw9607step0Labels permutation34 permutation3
    mixedMoment B raw9607step1 raw9607step1Labels = mixedMoment B raw9607step2 raw9607step2Labels := by
      have ha : raw9607step2 = raw9607step1 := by apply Matrix.ext; unfold raw9607step2 raw9607step1; decide +kernel
      have hl : raw9607step1Labels = labelEmbedding6 ∘ raw9607step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9607step1 raw9607step1Labels raw9607step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

theorem canonical9609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9609 raw9609Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw9609 raw9609Labels = mixedMoment B raw9609step0 raw9609step0Labels := by
      have ha : raw9609step0 = (fun i j => raw9609 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9609step0 raw9609; decide +kernel
      have hl : raw9609step0Labels = raw9609Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9609 raw9609Labels permutation178 permutation3
    mixedMoment B raw9609step0 raw9609step0Labels = mixedMoment B raw9609step1 raw9609step1Labels := by
      have ha : raw9609step1 = raw9609step0 := by apply Matrix.ext; unfold raw9609step1 raw9609step0; decide +kernel
      have hl : raw9609step0Labels = labelEmbedding6 ∘ raw9609step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9609step0 raw9609step0Labels raw9609step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5070 node5070Labels := by rfl

theorem canonical9610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9610 raw9610Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw9610 raw9610Labels = mixedMoment B raw9610step0 raw9610step0Labels := by
      have hz : ∀ j, raw9610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9610step0 = (fun i j => raw9610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9610step0 raw9610; decide +kernel
      have hl : raw9610step0Labels = raw9610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9610 raw9610Labels permutation346 hz
    mixedMoment B raw9610step0 raw9610step0Labels = mixedMoment B raw9610step1 raw9610step1Labels := by
      have ha : raw9610step1 = (fun i j => raw9610step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9610step1 raw9610step0; decide +kernel
      have hl : raw9610step1Labels = raw9610step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9610step0 raw9610step0Labels permutation44 permutation3
    mixedMoment B raw9610step1 raw9610step1Labels = mixedMoment B raw9610step2 raw9610step2Labels := by
      have ha : raw9610step2 = raw9610step1 := by apply Matrix.ext; unfold raw9610step2 raw9610step1; decide +kernel
      have hl : raw9610step1Labels = labelEmbedding6 ∘ raw9610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9610step1 raw9610step1Labels raw9610step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

theorem canonical9611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9611 raw9611Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw9611 raw9611Labels = mixedMoment B raw9611step0 raw9611step0Labels := by
      have hz : ∀ j, raw9611 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9611step0 = (fun i j => raw9611 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9611step0 raw9611; decide +kernel
      have hl : raw9611step0Labels = raw9611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9611 raw9611Labels permutation346 hz
    mixedMoment B raw9611step0 raw9611step0Labels = mixedMoment B raw9611step1 raw9611step1Labels := by
      have ha : raw9611step1 = (fun i j => raw9611step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9611step1 raw9611step0; decide +kernel
      have hl : raw9611step1Labels = raw9611step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9611step0 raw9611step0Labels permutation34 permutation3
    mixedMoment B raw9611step1 raw9611step1Labels = mixedMoment B raw9611step2 raw9611step2Labels := by
      have ha : raw9611step2 = raw9611step1 := by apply Matrix.ext; unfold raw9611step2 raw9611step1; decide +kernel
      have hl : raw9611step1Labels = labelEmbedding6 ∘ raw9611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9611step1 raw9611step1Labels raw9611step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical9613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9613 raw9613Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw9613 raw9613Labels = mixedMoment B raw9613step0 raw9613step0Labels := by
      have hz : ∀ j, raw9613 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9613step0 = (fun i j => raw9613 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9613step0 raw9613; decide +kernel
      have hl : raw9613step0Labels = raw9613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9613 raw9613Labels permutation434 hz
    mixedMoment B raw9613step0 raw9613step0Labels = mixedMoment B raw9613step1 raw9613step1Labels := by
      have hz : ∀ j, raw9613step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9613step1 = (fun i j => raw9613step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9613step1 raw9613step0; decide +kernel
      have hl : raw9613step1Labels = raw9613step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9613step0 raw9613step0Labels permutation80 hz
    mixedMoment B raw9613step1 raw9613step1Labels = mixedMoment B raw9613step2 raw9613step2Labels := by
      have ha : raw9613step2 = (fun i j => raw9613step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9613step2 raw9613step1; decide +kernel
      have hl : raw9613step2Labels = raw9613step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9613step1 raw9613step1Labels permutation8 permutation3
    mixedMoment B raw9613step2 raw9613step2Labels = mixedMoment B raw9613step3 raw9613step3Labels := by
      have ha : raw9613step3 = raw9613step2 := by apply Matrix.ext; unfold raw9613step3 raw9613step2; decide +kernel
      have hl : raw9613step2Labels = labelEmbedding6 ∘ raw9613step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9613step2 raw9613step2Labels raw9613step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

theorem canonical9618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9618 raw9618Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw9618 raw9618Labels = mixedMoment B raw9618step0 raw9618step0Labels := by
      have hz : ∀ j, raw9618 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9618step0 = (fun i j => raw9618 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9618step0 raw9618; decide +kernel
      have hl : raw9618step0Labels = raw9618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9618 raw9618Labels permutation434 hz
    mixedMoment B raw9618step0 raw9618step0Labels = mixedMoment B raw9618step1 raw9618step1Labels := by
      have hz : ∀ j, raw9618step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9618step1 = (fun i j => raw9618step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9618step1 raw9618step0; decide +kernel
      have hl : raw9618step1Labels = raw9618step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9618step0 raw9618step0Labels permutation80 hz
    mixedMoment B raw9618step1 raw9618step1Labels = mixedMoment B raw9618step2 raw9618step2Labels := by
      have ha : raw9618step2 = (fun i j => raw9618step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9618step2 raw9618step1; decide +kernel
      have hl : raw9618step2Labels = raw9618step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9618step1 raw9618step1Labels permutation31 permutation3
    mixedMoment B raw9618step2 raw9618step2Labels = mixedMoment B raw9618step3 raw9618step3Labels := by
      have ha : raw9618step3 = -raw9618step2 := by apply Matrix.ext; change ∀ i j, raw9618step3 i j = -(raw9618step2 i j); unfold raw9618step3 raw9618step2; decide +kernel
      have hl : raw9618step3Labels = raw9618step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9618step3 raw9618step3Labels = mixedMoment B raw9618step4 raw9618step4Labels := by
      have ha : raw9618step4 = raw9618step3 := by apply Matrix.ext; unfold raw9618step4 raw9618step3; decide +kernel
      have hl : raw9618step3Labels = labelEmbedding6 ∘ raw9618step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9618step3 raw9618step3Labels raw9618step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1113 raw1113Labels = mixedMoment B node4337 node4337Labels := by
  calc
    mixedMoment B raw1113 raw1113Labels = mixedMoment B raw1113step0 raw1113step0Labels := by
      have ha : raw1113step0 = (fun i j => raw1113 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1113step0 raw1113; decide +kernel
      have hl : raw1113step0Labels = raw1113Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1113 raw1113Labels permutation152 permutation4
    mixedMoment B raw1113step0 raw1113step0Labels = mixedMoment B raw1113step1 raw1113step1Labels := by
      have ha : raw1113step1 = raw1113step0 := by apply Matrix.ext; unfold raw1113step1 raw1113step0; decide +kernel
      have hl : raw1113step0Labels = labelEmbedding7 ∘ raw1113step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1113step0 raw1113step0Labels raw1113step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4337 node4337Labels := by rfl

theorem canonical1114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1114 raw1114Labels = mixedMoment B node915 node915Labels := by
  calc
    mixedMoment B raw1114 raw1114Labels = mixedMoment B raw1114step0 raw1114step0Labels := by
      have ha : raw1114step0 = (fun i j => raw1114 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1114step0 raw1114; decide +kernel
      have hl : raw1114step0Labels = raw1114Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1114 raw1114Labels permutation152 permutation4
    _ = mixedMoment B node915 node915Labels := by rfl

theorem canonical1115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1115 raw1115Labels = mixedMoment B node1632 node1632Labels := by
  calc
    mixedMoment B raw1115 raw1115Labels = mixedMoment B raw1115step0 raw1115step0Labels := by
      have ha : raw1115step0 = (fun i j => raw1115 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1115step0 raw1115; decide +kernel
      have hl : raw1115step0Labels = raw1115Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1115 raw1115Labels permutation176 permutation6
    mixedMoment B raw1115step0 raw1115step0Labels = mixedMoment B raw1115step1 raw1115step1Labels := by
      have ha : raw1115step1 = -raw1115step0 := by apply Matrix.ext; change ∀ i j, raw1115step1 i j = -(raw1115step0 i j); unfold raw1115step1 raw1115step0; decide +kernel
      have hl : raw1115step1Labels = raw1115step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1115step1 raw1115step1Labels = mixedMoment B raw1115step2 raw1115step2Labels := by
      have ha : raw1115step2 = raw1115step1 := by apply Matrix.ext; unfold raw1115step2 raw1115step1; decide +kernel
      have hl : raw1115step1Labels = labelEmbedding1 ∘ raw1115step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1115step1 raw1115step1Labels raw1115step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1632 node1632Labels := by rfl

theorem canonical1116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1116 raw1116Labels = mixedMoment B node4338 node4338Labels := by
  calc
    mixedMoment B raw1116 raw1116Labels = mixedMoment B raw1116step0 raw1116step0Labels := by
      have ha : raw1116step0 = (fun i j => raw1116 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1116step0 raw1116; decide +kernel
      have hl : raw1116step0Labels = raw1116Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1116 raw1116Labels permutation32 permutation4
    mixedMoment B raw1116step0 raw1116step0Labels = mixedMoment B raw1116step1 raw1116step1Labels := by
      have ha : raw1116step1 = raw1116step0 := by apply Matrix.ext; unfold raw1116step1 raw1116step0; decide +kernel
      have hl : raw1116step0Labels = labelEmbedding7 ∘ raw1116step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1116step0 raw1116step0Labels raw1116step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4338 node4338Labels := by rfl

theorem canonical1117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1117 raw1117Labels = mixedMoment B node916 node916Labels := by
  calc
    mixedMoment B raw1117 raw1117Labels = mixedMoment B raw1117step0 raw1117step0Labels := by
      have ha : raw1117step0 = (fun i j => raw1117 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1117step0 raw1117; decide +kernel
      have hl : raw1117step0Labels = raw1117Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1117 raw1117Labels permutation32 permutation4
    _ = mixedMoment B node916 node916Labels := by rfl

theorem canonical1118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1118 raw1118Labels = mixedMoment B node1633 node1633Labels := by
  calc
    mixedMoment B raw1118 raw1118Labels = mixedMoment B raw1118step0 raw1118step0Labels := by
      have ha : raw1118step0 = (fun i j => raw1118 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1118step0 raw1118; decide +kernel
      have hl : raw1118step0Labels = raw1118Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1118 raw1118Labels permutation38 permutation6
    mixedMoment B raw1118step0 raw1118step0Labels = mixedMoment B raw1118step1 raw1118step1Labels := by
      have ha : raw1118step1 = -raw1118step0 := by apply Matrix.ext; change ∀ i j, raw1118step1 i j = -(raw1118step0 i j); unfold raw1118step1 raw1118step0; decide +kernel
      have hl : raw1118step1Labels = raw1118step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1118step1 raw1118step1Labels = mixedMoment B raw1118step2 raw1118step2Labels := by
      have ha : raw1118step2 = raw1118step1 := by apply Matrix.ext; unfold raw1118step2 raw1118step1; decide +kernel
      have hl : raw1118step1Labels = labelEmbedding1 ∘ raw1118step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1118step1 raw1118step1Labels raw1118step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1633 node1633Labels := by rfl

theorem canonical1119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1119 raw1119Labels = mixedMoment B node4339 node4339Labels := by
  calc
    mixedMoment B raw1119 raw1119Labels = mixedMoment B raw1119step0 raw1119step0Labels := by
      have ha : raw1119step0 = (fun i j => raw1119 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1119step0 raw1119; decide +kernel
      have hl : raw1119step0Labels = raw1119Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1119 raw1119Labels permutation32 permutation4
    mixedMoment B raw1119step0 raw1119step0Labels = mixedMoment B raw1119step1 raw1119step1Labels := by
      have ha : raw1119step1 = raw1119step0 := by apply Matrix.ext; unfold raw1119step1 raw1119step0; decide +kernel
      have hl : raw1119step0Labels = labelEmbedding7 ∘ raw1119step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1119step0 raw1119step0Labels raw1119step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4339 node4339Labels := by rfl

theorem canonical1120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1120 raw1120Labels = mixedMoment B node917 node917Labels := by
  calc
    mixedMoment B raw1120 raw1120Labels = mixedMoment B raw1120step0 raw1120step0Labels := by
      have ha : raw1120step0 = (fun i j => raw1120 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1120step0 raw1120; decide +kernel
      have hl : raw1120step0Labels = raw1120Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1120 raw1120Labels permutation32 permutation4
    _ = mixedMoment B node917 node917Labels := by rfl

theorem canonical1121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1121 raw1121Labels = mixedMoment B node1634 node1634Labels := by
  calc
    mixedMoment B raw1121 raw1121Labels = mixedMoment B raw1121step0 raw1121step0Labels := by
      have ha : raw1121step0 = (fun i j => raw1121 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1121step0 raw1121; decide +kernel
      have hl : raw1121step0Labels = raw1121Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1121 raw1121Labels permutation38 permutation6
    mixedMoment B raw1121step0 raw1121step0Labels = mixedMoment B raw1121step1 raw1121step1Labels := by
      have ha : raw1121step1 = -raw1121step0 := by apply Matrix.ext; change ∀ i j, raw1121step1 i j = -(raw1121step0 i j); unfold raw1121step1 raw1121step0; decide +kernel
      have hl : raw1121step1Labels = raw1121step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1121step1 raw1121step1Labels = mixedMoment B raw1121step2 raw1121step2Labels := by
      have ha : raw1121step2 = raw1121step1 := by apply Matrix.ext; unfold raw1121step2 raw1121step1; decide +kernel
      have hl : raw1121step1Labels = labelEmbedding1 ∘ raw1121step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1121step1 raw1121step1Labels raw1121step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1634 node1634Labels := by rfl

theorem canonical1146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1146 raw1146Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw1146 raw1146Labels = mixedMoment B raw1146step0 raw1146step0Labels := by
      have ha : raw1146step0 = (fun i j => raw1146 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1146step0 raw1146; decide +kernel
      have hl : raw1146step0Labels = raw1146Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1146 raw1146Labels permutation32 permutation4
    mixedMoment B raw1146step0 raw1146step0Labels = mixedMoment B raw1146step1 raw1146step1Labels := by
      have ha : raw1146step1 = raw1146step0 := by apply Matrix.ext; unfold raw1146step1 raw1146step0; decide +kernel
      have hl : raw1146step0Labels = labelEmbedding7 ∘ raw1146step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1146step0 raw1146step0Labels raw1146step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4354 node4354Labels := by rfl

theorem canonical1147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1147 raw1147Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw1147 raw1147Labels = mixedMoment B raw1147step0 raw1147step0Labels := by
      have ha : raw1147step0 = (fun i j => raw1147 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1147step0 raw1147; decide +kernel
      have hl : raw1147step0Labels = raw1147Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1147 raw1147Labels permutation32 permutation4
    _ = mixedMoment B node932 node932Labels := by rfl

theorem canonical1148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1148 raw1148Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw1148 raw1148Labels = mixedMoment B raw1148step0 raw1148step0Labels := by
      have ha : raw1148step0 = (fun i j => raw1148 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1148step0 raw1148; decide +kernel
      have hl : raw1148step0Labels = raw1148Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1148 raw1148Labels permutation34 permutation6
    mixedMoment B raw1148step0 raw1148step0Labels = mixedMoment B raw1148step1 raw1148step1Labels := by
      have ha : raw1148step1 = -raw1148step0 := by apply Matrix.ext; change ∀ i j, raw1148step1 i j = -(raw1148step0 i j); unfold raw1148step1 raw1148step0; decide +kernel
      have hl : raw1148step1Labels = raw1148step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1148step1 raw1148step1Labels = mixedMoment B raw1148step2 raw1148step2Labels := by
      have ha : raw1148step2 = raw1148step1 := by apply Matrix.ext; unfold raw1148step2 raw1148step1; decide +kernel
      have hl : raw1148step1Labels = labelEmbedding1 ∘ raw1148step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1148step1 raw1148step1Labels raw1148step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1681 node1681Labels := by rfl

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

theorem canonical1248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1248 raw1248Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw1248 raw1248Labels = mixedMoment B raw1248step0 raw1248step0Labels := by
      have ha : raw1248step0 = (fun i j => raw1248 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1248step0 raw1248; decide +kernel
      have hl : raw1248step0Labels = raw1248Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1248 raw1248Labels permutation32 permutation4
    mixedMoment B raw1248step0 raw1248step0Labels = mixedMoment B raw1248step1 raw1248step1Labels := by
      have ha : raw1248step1 = raw1248step0 := by apply Matrix.ext; unfold raw1248step1 raw1248step0; decide +kernel
      have hl : raw1248step0Labels = labelEmbedding7 ∘ raw1248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1248step0 raw1248step0Labels raw1248step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

theorem canonical1249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1249 raw1249Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw1249 raw1249Labels = mixedMoment B raw1249step0 raw1249step0Labels := by
      have ha : raw1249step0 = (fun i j => raw1249 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1249step0 raw1249; decide +kernel
      have hl : raw1249step0Labels = raw1249Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1249 raw1249Labels permutation32 permutation4
    _ = mixedMoment B node1035 node1035Labels := by rfl

theorem canonical1250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1250 raw1250Labels = mixedMoment B node1645 node1645Labels := by
  calc
    mixedMoment B raw1250 raw1250Labels = mixedMoment B raw1250step0 raw1250step0Labels := by
      have ha : raw1250step0 = (fun i j => raw1250 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1250step0 raw1250; decide +kernel
      have hl : raw1250step0Labels = raw1250Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1250 raw1250Labels permutation38 permutation6
    mixedMoment B raw1250step0 raw1250step0Labels = mixedMoment B raw1250step1 raw1250step1Labels := by
      have ha : raw1250step1 = -raw1250step0 := by apply Matrix.ext; change ∀ i j, raw1250step1 i j = -(raw1250step0 i j); unfold raw1250step1 raw1250step0; decide +kernel
      have hl : raw1250step1Labels = raw1250step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1250step1 raw1250step1Labels = mixedMoment B raw1250step2 raw1250step2Labels := by
      have ha : raw1250step2 = raw1250step1 := by apply Matrix.ext; unfold raw1250step2 raw1250step1; decide +kernel
      have hl : raw1250step1Labels = labelEmbedding1 ∘ raw1250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1250step1 raw1250step1Labels raw1250step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1645 node1645Labels := by rfl

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

theorem canonical5183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5183 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5183 = injectiveMoment H raw5183step0 := by
      have hz : ∀ j, raw5183 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5183step0 = (fun i j => raw5183 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5183 permutation5 hz
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
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

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound44 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node44 = Sparse.eval value44 (momentVector H) := by
  have hc : momentVector H 4 = injectiveMoment H node44 := rfl
  simp [value44, Sparse.eval, hc]

theorem sound46 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node46 = Sparse.eval value46 (momentVector H) := by
  have heq : pivotMatrix46 = (fun u v => node46 (pivotPermutation46 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node46 = injectiveMoment H pivotMatrix46 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix46 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix46 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (1 : Fin 3) = raw5183 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5183 hH).trans (sound4 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (2 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node46 + (injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value46, value10, value11, value4, Sparse.eval] at hc ⊢
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

theorem canonical4159 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4159 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4159 = injectiveMoment H raw4159step0 := by
      have heq : raw4159step0 = -raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4159).symm
    injectiveMoment H raw4159step0 = injectiveMoment H raw4159step1 := by
      have heq : raw4159step1 = (fun i j => raw4159step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4159step0 permutation7 permutation5
    _ = injectiveMoment H node36 := by rfl

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

theorem canonical1435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1435 = injectiveMoment H node31 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4966 = injectiveMoment H node44 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4160 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4160 = injectiveMoment H raw4160step0 := by
      have heq : raw4160step0 = -raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4160).symm
    injectiveMoment H raw4160step0 = injectiveMoment H raw4160step1 := by
      have heq : raw4160step1 = (fun i j => raw4160step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4160step0 permutation7 permutation5
    _ = injectiveMoment H node62 := by rfl

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

theorem canonical5141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5141 = injectiveMoment H node46 := by
  rfl

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

theorem sound210 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node210 = Sparse.eval value210 (momentVector H) := by
  have heq : pivotMatrix210 = (fun u v => node210 (pivotPermutation210 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node210 = injectiveMoment H pivotMatrix210 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix210 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix210 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix210 (0 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (0 : Fin 3) = raw4966 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4966 hH).trans (sound44 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix210 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (1 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix210 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (2 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node210 + (injectiveMoment H (mergeFirst pivotMatrix210 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix210 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix210 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value210, value36, value44, value62, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical3978 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3978 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw3978 = injectiveMoment H raw3978step0 := by
      have heq : raw3978step0 = -raw3978 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3978).symm
    injectiveMoment H raw3978step0 = injectiveMoment H raw3978step1 := by
      have heq : raw3978step1 = (fun i j => raw3978step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3978step0 permutation11 permutation8
    _ = injectiveMoment H node210 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical280
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8979 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw8979 = injectiveMoment H raw8979step0 := by
      have hz : ∀ j, raw8979 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8979step0 = (fun i j => raw8979 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8979 permutation9 hz
    _ = injectiveMoment H node11 := by rfl

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

theorem singlePair503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node503 node503Labels = Sparse.eval singlePairValue503 (familyPairVector B) := by
  have hp := single_label_three B hB node503
  have hl : node503Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node503 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 1) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node503 PairSemantics.raw5197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 2) = PairSemantics.raw8979 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node503 PairSemantics.raw8979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8979 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 3) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node503 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value210 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 4) = PairSemantics.raw3978 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node503 PairSemantics.raw3978; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3978 hH).trans (PairSemantics.sound210 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue503, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value210, Sparse.eval] at hp ⊢
  linarith only [hp]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3888 node3888Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node503 node503Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw544 singletonSmall3888
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3888) = raw544Labels := by decide +kernel
  rw [hl, canonical544 B hB] at h
  have hc0 : mixedMoment B raw544 (Fin.cases (0 : Fin 1) singletonSmall3888) =
      mixedMoment B node503 node503Labels := by
    have ha : raw544 = raw545 := by apply Matrix.ext; unfold raw544 raw545; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3888 = raw545Labels := by decide +kernel
    rw [ha, hj, canonical545 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4337 node4337Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node915 node915Labels + mixedMoment B node1632 node1632Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1113 singletonSmall4337
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4337) = raw1113Labels := by decide +kernel
  rw [hl, canonical1113 B hB] at h
  have hc0 : mixedMoment B raw1113 (Fin.cases (0 : Fin 2) singletonSmall4337) =
      mixedMoment B node915 node915Labels := by
    have ha : raw1113 = raw1114 := by apply Matrix.ext; unfold raw1113 raw1114; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4337 = raw1114Labels := by decide +kernel
    rw [ha, hj, canonical1114 B hB]
  have hc1 : mixedMoment B raw1113 (Fin.cases (1 : Fin 2) singletonSmall4337) =
      mixedMoment B node1632 node1632Labels := by
    have ha : raw1113 = raw1115 := by apply Matrix.ext; unfold raw1113 raw1115; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4337 = raw1115Labels := by decide +kernel
    rw [ha, hj, canonical1115 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4338 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4338 node4338Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node916 node916Labels + mixedMoment B node1633 node1633Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1116 singletonSmall4338
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4338) = raw1116Labels := by decide +kernel
  rw [hl, canonical1116 B hB] at h
  have hc0 : mixedMoment B raw1116 (Fin.cases (0 : Fin 2) singletonSmall4338) =
      mixedMoment B node916 node916Labels := by
    have ha : raw1116 = raw1117 := by apply Matrix.ext; unfold raw1116 raw1117; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4338 = raw1117Labels := by decide +kernel
    rw [ha, hj, canonical1117 B hB]
  have hc1 : mixedMoment B raw1116 (Fin.cases (1 : Fin 2) singletonSmall4338) =
      mixedMoment B node1633 node1633Labels := by
    have ha : raw1116 = raw1118 := by apply Matrix.ext; unfold raw1116 raw1118; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4338 = raw1118Labels := by decide +kernel
    rw [ha, hj, canonical1118 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4339 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4339 node4339Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node917 node917Labels + mixedMoment B node1634 node1634Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1119 singletonSmall4339
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4339) = raw1119Labels := by decide +kernel
  rw [hl, canonical1119 B hB] at h
  have hc0 : mixedMoment B raw1119 (Fin.cases (0 : Fin 2) singletonSmall4339) =
      mixedMoment B node917 node917Labels := by
    have ha : raw1119 = raw1120 := by apply Matrix.ext; unfold raw1119 raw1120; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4339 = raw1120Labels := by decide +kernel
    rw [ha, hj, canonical1120 B hB]
  have hc1 : mixedMoment B raw1119 (Fin.cases (1 : Fin 2) singletonSmall4339) =
      mixedMoment B node1634 node1634Labels := by
    have ha : raw1119 = raw1121 := by apply Matrix.ext; unfold raw1119 raw1121; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4339 = raw1121Labels := by decide +kernel
    rw [ha, hj, canonical1121 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4354 node4354Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node932 node932Labels + mixedMoment B node1681 node1681Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1146 singletonSmall4354
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4354) = raw1146Labels := by decide +kernel
  rw [hl, canonical1146 B hB] at h
  have hc0 : mixedMoment B raw1146 (Fin.cases (0 : Fin 2) singletonSmall4354) =
      mixedMoment B node932 node932Labels := by
    have ha : raw1146 = raw1147 := by apply Matrix.ext; unfold raw1146 raw1147; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4354 = raw1147Labels := by decide +kernel
    rw [ha, hj, canonical1147 B hB]
  have hc1 : mixedMoment B raw1146 (Fin.cases (1 : Fin 2) singletonSmall4354) =
      mixedMoment B node1681 node1681Labels := by
    have ha : raw1146 = raw1148 := by apply Matrix.ext; unfold raw1146 raw1148; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4354 = raw1148Labels := by decide +kernel
    rw [ha, hj, canonical1148 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4452 node4452Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1035 node1035Labels + mixedMoment B node1645 node1645Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1248 singletonSmall4452
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4452) = raw1248Labels := by decide +kernel
  rw [hl, canonical1248 B hB] at h
  have hc0 : mixedMoment B raw1248 (Fin.cases (0 : Fin 2) singletonSmall4452) =
      mixedMoment B node1035 node1035Labels := by
    have ha : raw1248 = raw1249 := by apply Matrix.ext; unfold raw1248 raw1249; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4452 = raw1249Labels := by decide +kernel
    rw [ha, hj, canonical1249 B hB]
  have hc1 : mixedMoment B raw1248 (Fin.cases (1 : Fin 2) singletonSmall4452) =
      mixedMoment B node1645 node1645Labels := by
    have ha : raw1248 = raw1250 := by apply Matrix.ext; unfold raw1248 raw1250; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4452 = raw1250Labels := by decide +kernel
    rw [ha, hj, canonical1250 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4721 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4721 node4721Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1875 node1875Labels + mixedMoment B node1905 node1905Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1620 singletonSmall4721
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4721) = raw1620Labels := by decide +kernel
  rw [hl, canonical1620 B hB] at h
  have hc0 : mixedMoment B raw1620 (Fin.cases (0 : Fin 2) singletonSmall4721) =
      mixedMoment B node1875 node1875Labels := by
    have ha : raw1620 = raw1621 := by apply Matrix.ext; unfold raw1620 raw1621; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4721 = raw1621Labels := by decide +kernel
    rw [ha, hj, canonical1621 B hB]
  have hc1 : mixedMoment B raw1620 (Fin.cases (1 : Fin 2) singletonSmall4721) =
      mixedMoment B node1905 node1905Labels := by
    have ha : raw1620 = raw1622 := by apply Matrix.ext; unfold raw1620 raw1622; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4721 = raw1622Labels := by decide +kernel
    rw [ha, hj, canonical1622 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4726 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4726 node4726Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1880 node1880Labels + mixedMoment B node1938 node1938Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1635 singletonSmall4726
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4726) = raw1635Labels := by decide +kernel
  rw [hl, canonical1635 B hB] at h
  have hc0 : mixedMoment B raw1635 (Fin.cases (0 : Fin 2) singletonSmall4726) =
      mixedMoment B node1880 node1880Labels := by
    have ha : raw1635 = raw1636 := by apply Matrix.ext; unfold raw1635 raw1636; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4726 = raw1636Labels := by decide +kernel
    rw [ha, hj, canonical1636 B hB]
  have hc1 : mixedMoment B raw1635 (Fin.cases (1 : Fin 2) singletonSmall4726) =
      mixedMoment B node1938 node1938Labels := by
    have ha : raw1635 = raw1637 := by apply Matrix.ext; unfold raw1635 raw1637; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4726 = raw1637Labels := by decide +kernel
    rw [ha, hj, canonical1637 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4744 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4744 node4744Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1917 node1917Labels + mixedMoment B node1924 node1924Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1662 singletonSmall4744
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4744) = raw1662Labels := by decide +kernel
  rw [hl, canonical1662 B hB] at h
  have hc0 : mixedMoment B raw1662 (Fin.cases (0 : Fin 2) singletonSmall4744) =
      mixedMoment B node1917 node1917Labels := by
    have ha : raw1662 = raw1663 := by apply Matrix.ext; unfold raw1662 raw1663; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4744 = raw1663Labels := by decide +kernel
    rw [ha, hj, canonical1663 B hB]
  have hc1 : mixedMoment B raw1662 (Fin.cases (1 : Fin 2) singletonSmall4744) =
      mixedMoment B node1924 node1924Labels := by
    have ha : raw1662 = raw1664 := by apply Matrix.ext; unfold raw1662 raw1664; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4744 = raw1664Labels := by decide +kernel
    rw [ha, hj, canonical1664 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4936 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4936 node4936Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2328 node2328Labels + mixedMoment B node3401 node3401Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1896 singletonSmall4936
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4936) = raw1896Labels := by decide +kernel
  rw [hl, canonical1896 B hB] at h
  have hc0 : mixedMoment B raw1896 (Fin.cases (0 : Fin 2) singletonSmall4936) =
      mixedMoment B node2328 node2328Labels := by
    have ha : raw1896 = raw1897 := by apply Matrix.ext; unfold raw1896 raw1897; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4936 = raw1897Labels := by decide +kernel
    rw [ha, hj, canonical1897 B hB]
  have hc1 : mixedMoment B raw1896 (Fin.cases (1 : Fin 2) singletonSmall4936) =
      mixedMoment B node3401 node3401Labels := by
    have ha : raw1896 = raw1898 := by apply Matrix.ext; unfold raw1896 raw1898; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4936 = raw1898Labels := by decide +kernel
    rw [ha, hj, canonical1898 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4937 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4937 node4937Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2329 node2329Labels + mixedMoment B node3402 node3402Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1899 singletonSmall4937
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4937) = raw1899Labels := by decide +kernel
  rw [hl, canonical1899 B hB] at h
  have hc0 : mixedMoment B raw1899 (Fin.cases (0 : Fin 2) singletonSmall4937) =
      mixedMoment B node2329 node2329Labels := by
    have ha : raw1899 = raw1900 := by apply Matrix.ext; unfold raw1899 raw1900; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4937 = raw1900Labels := by decide +kernel
    rw [ha, hj, canonical1900 B hB]
  have hc1 : mixedMoment B raw1899 (Fin.cases (1 : Fin 2) singletonSmall4937) =
      mixedMoment B node3402 node3402Labels := by
    have ha : raw1899 = raw1901 := by apply Matrix.ext; unfold raw1899 raw1901; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4937 = raw1901Labels := by decide +kernel
    rw [ha, hj, canonical1901 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4949 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4949 node4949Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2341 node2341Labels + mixedMoment B node3417 node3417Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1920 singletonSmall4949
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4949) = raw1920Labels := by decide +kernel
  rw [hl, canonical1920 B hB] at h
  have hc0 : mixedMoment B raw1920 (Fin.cases (0 : Fin 2) singletonSmall4949) =
      mixedMoment B node2341 node2341Labels := by
    have ha : raw1920 = raw1921 := by apply Matrix.ext; unfold raw1920 raw1921; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4949 = raw1921Labels := by decide +kernel
    rw [ha, hj, canonical1921 B hB]
  have hc1 : mixedMoment B raw1920 (Fin.cases (1 : Fin 2) singletonSmall4949) =
      mixedMoment B node3417 node3417Labels := by
    have ha : raw1920 = raw1922 := by apply Matrix.ext; unfold raw1920 raw1922; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4949 = raw1922Labels := by decide +kernel
    rw [ha, hj, canonical1922 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5032 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5032 node5032Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2424 node2424Labels + mixedMoment B node3440 node3440Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2049 singletonSmall5032
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5032) = raw2049Labels := by decide +kernel
  rw [hl, canonical2049 B hB] at h
  have hc0 : mixedMoment B raw2049 (Fin.cases (0 : Fin 2) singletonSmall5032) =
      mixedMoment B node2424 node2424Labels := by
    have ha : raw2049 = raw2050 := by apply Matrix.ext; unfold raw2049 raw2050; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5032 = raw2050Labels := by decide +kernel
    rw [ha, hj, canonical2050 B hB]
  have hc1 : mixedMoment B raw2049 (Fin.cases (1 : Fin 2) singletonSmall5032) =
      mixedMoment B node3440 node3440Labels := by
    have ha : raw2049 = raw2051 := by apply Matrix.ext; unfold raw2049 raw2051; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5032 = raw2051Labels := by decide +kernel
    rw [ha, hj, canonical2051 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5038 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5038 node5038Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2431 node2431Labels + mixedMoment B node3453 node3453Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2061 singletonSmall5038
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5038) = raw2061Labels := by decide +kernel
  rw [hl, canonical2061 B hB] at h
  have hc0 : mixedMoment B raw2061 (Fin.cases (0 : Fin 2) singletonSmall5038) =
      mixedMoment B node2431 node2431Labels := by
    have ha : raw2061 = raw2062 := by apply Matrix.ext; unfold raw2061 raw2062; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5038 = raw2062Labels := by decide +kernel
    rw [ha, hj, canonical2062 B hB]
  have hc1 : mixedMoment B raw2061 (Fin.cases (1 : Fin 2) singletonSmall5038) =
      mixedMoment B node3453 node3453Labels := by
    have ha : raw2061 = raw2063 := by apply Matrix.ext; unfold raw2061 raw2063; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5038 = raw2063Labels := by decide +kernel
    rw [ha, hj, canonical2063 B hB]
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

theorem singleton5070 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5070 node5070Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2477 node2477Labels + mixedMoment B node3444 node3444Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2088 singletonSmall5070
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5070) = raw2088Labels := by decide +kernel
  rw [hl, canonical2088 B hB] at h
  have hc0 : mixedMoment B raw2088 (Fin.cases (0 : Fin 2) singletonSmall5070) =
      mixedMoment B node2477 node2477Labels := by
    have ha : raw2088 = raw2089 := by apply Matrix.ext; unfold raw2088 raw2089; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5070 = raw2089Labels := by decide +kernel
    rw [ha, hj, canonical2089 B hB]
  have hc1 : mixedMoment B raw2088 (Fin.cases (1 : Fin 2) singletonSmall5070) =
      mixedMoment B node3444 node3444Labels := by
    have ha : raw2088 = raw2090 := by apply Matrix.ext; unfold raw2088 raw2090; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5070 = raw2090Labels := by decide +kernel
    rw [ha, hj, canonical2090 B hB]
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

theorem singleton5123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5123 node5123Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2536 node2536Labels + mixedMoment B node3370 node3370Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2154 singletonSmall5123
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5123) = raw2154Labels := by decide +kernel
  rw [hl, canonical2154 B hB] at h
  have hc0 : mixedMoment B raw2154 (Fin.cases (0 : Fin 2) singletonSmall5123) =
      mixedMoment B node2536 node2536Labels := by
    have ha : raw2154 = raw2155 := by apply Matrix.ext; unfold raw2154 raw2155; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5123 = raw2155Labels := by decide +kernel
    rw [ha, hj, canonical2155 B hB]
  have hc1 : mixedMoment B raw2154 (Fin.cases (1 : Fin 2) singletonSmall5123) =
      mixedMoment B node3370 node3370Labels := by
    have ha : raw2154 = raw2156 := by apply Matrix.ext; unfold raw2154 raw2156; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5123 = raw2156Labels := by decide +kernel
    rw [ha, hj, canonical2156 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5125 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5125 node5125Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2539 node2539Labels + mixedMoment B node3372 node3372Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2157 singletonSmall5125
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5125) = raw2157Labels := by decide +kernel
  rw [hl, canonical2157 B hB] at h
  have hc0 : mixedMoment B raw2157 (Fin.cases (0 : Fin 2) singletonSmall5125) =
      mixedMoment B node2539 node2539Labels := by
    have ha : raw2157 = raw2158 := by apply Matrix.ext; unfold raw2157 raw2158; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5125 = raw2158Labels := by decide +kernel
    rw [ha, hj, canonical2158 B hB]
  have hc1 : mixedMoment B raw2157 (Fin.cases (1 : Fin 2) singletonSmall5125) =
      mixedMoment B node3372 node3372Labels := by
    have ha : raw2157 = raw2159 := by apply Matrix.ext; unfold raw2157 raw2159; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5125 = raw2159Labels := by decide +kernel
    rw [ha, hj, canonical2159 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5162 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5162 node5162Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2589 node2589Labels + mixedMoment B node3563 node3563Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2187 singletonSmall5162
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5162) = raw2187Labels := by decide +kernel
  rw [hl, canonical2187 B hB] at h
  have hc0 : mixedMoment B raw2187 (Fin.cases (0 : Fin 2) singletonSmall5162) =
      mixedMoment B node2589 node2589Labels := by
    have ha : raw2187 = raw2188 := by apply Matrix.ext; unfold raw2187 raw2188; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5162 = raw2188Labels := by decide +kernel
    rw [ha, hj, canonical2188 B hB]
  have hc1 : mixedMoment B raw2187 (Fin.cases (1 : Fin 2) singletonSmall5162) =
      mixedMoment B node3563 node3563Labels := by
    have ha : raw2187 = raw2189 := by apply Matrix.ext; unfold raw2187 raw2189; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5162 = raw2189Labels := by decide +kernel
    rw [ha, hj, canonical2189 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5228 node5228Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2672 node2672Labels + mixedMoment B node3391 node3391Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2250 singletonSmall5228
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5228) = raw2250Labels := by decide +kernel
  rw [hl, canonical2250 B hB] at h
  have hc0 : mixedMoment B raw2250 (Fin.cases (0 : Fin 2) singletonSmall5228) =
      mixedMoment B node2672 node2672Labels := by
    have ha : raw2250 = raw2251 := by apply Matrix.ext; unfold raw2250 raw2251; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5228 = raw2251Labels := by decide +kernel
    rw [ha, hj, canonical2251 B hB]
  have hc1 : mixedMoment B raw2250 (Fin.cases (1 : Fin 2) singletonSmall5228) =
      mixedMoment B node3391 node3391Labels := by
    have ha : raw2250 = raw2252 := by apply Matrix.ext; unfold raw2250 raw2252; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5228 = raw2252Labels := by decide +kernel
    rw [ha, hj, canonical2252 B hB]
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

theorem singleton5401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5401 node5401Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3787 node3787Labels + mixedMoment B node3804 node3804Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2475 singletonSmall5401
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5401) = raw2475Labels := by decide +kernel
  rw [hl, canonical2475 B hB] at h
  have hc0 : mixedMoment B raw2475 (Fin.cases (0 : Fin 2) singletonSmall5401) =
      mixedMoment B node3787 node3787Labels := by
    have ha : raw2475 = raw2476 := by apply Matrix.ext; unfold raw2475 raw2476; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5401 = raw2476Labels := by decide +kernel
    rw [ha, hj, canonical2476 B hB]
  have hc1 : mixedMoment B raw2475 (Fin.cases (1 : Fin 2) singletonSmall5401) =
      mixedMoment B node3804 node3804Labels := by
    have ha : raw2475 = raw2477 := by apply Matrix.ext; unfold raw2475 raw2477; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5401 = raw2477Labels := by decide +kernel
    rw [ha, hj, canonical2477 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5404 node5404Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3790 node3790Labels + mixedMoment B node3815 node3815Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2481 singletonSmall5404
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5404) = raw2481Labels := by decide +kernel
  rw [hl, canonical2481 B hB] at h
  have hc0 : mixedMoment B raw2481 (Fin.cases (0 : Fin 2) singletonSmall5404) =
      mixedMoment B node3790 node3790Labels := by
    have ha : raw2481 = raw2482 := by apply Matrix.ext; unfold raw2481 raw2482; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5404 = raw2482Labels := by decide +kernel
    rw [ha, hj, canonical2482 B hB]
  have hc1 : mixedMoment B raw2481 (Fin.cases (1 : Fin 2) singletonSmall5404) =
      mixedMoment B node3815 node3815Labels := by
    have ha : raw2481 = raw2483 := by apply Matrix.ext; unfold raw2481 raw2483; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5404 = raw2483Labels := by decide +kernel
    rw [ha, hj, canonical2483 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5411 node5411Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3809 node3809Labels + mixedMoment B node3813 node3813Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2490 singletonSmall5411
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5411) = raw2490Labels := by decide +kernel
  rw [hl, canonical2490 B hB] at h
  have hc0 : mixedMoment B raw2490 (Fin.cases (0 : Fin 2) singletonSmall5411) =
      mixedMoment B node3809 node3809Labels := by
    have ha : raw2490 = raw2491 := by apply Matrix.ext; unfold raw2490 raw2491; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5411 = raw2491Labels := by decide +kernel
    rw [ha, hj, canonical2491 B hB]
  have hc1 : mixedMoment B raw2490 (Fin.cases (1 : Fin 2) singletonSmall5411) =
      mixedMoment B node3813 node3813Labels := by
    have ha : raw2490 = raw2492 := by apply Matrix.ext; unfold raw2490 raw2492; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5411 = raw2492Labels := by decide +kernel
    rw [ha, hj, canonical2492 B hB]
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

theorem singleton5451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5451 node5451Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3888 node3888Labels + mixedMoment B node3913 node3913Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2559 singletonSmall5451
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5451) = raw2559Labels := by decide +kernel
  rw [hl, canonical2559 B hB] at h
  have hc0 : mixedMoment B raw2559 (Fin.cases (0 : Fin 2) singletonSmall5451) =
      mixedMoment B node3888 node3888Labels := by
    have ha : raw2559 = raw2560 := by apply Matrix.ext; unfold raw2559 raw2560; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5451 = raw2560Labels := by decide +kernel
    rw [ha, hj, canonical2560 B hB]
  have hc1 : mixedMoment B raw2559 (Fin.cases (1 : Fin 2) singletonSmall5451) =
      mixedMoment B node3913 node3913Labels := by
    have ha : raw2559 = raw2561 := by apply Matrix.ext; unfold raw2559 raw2561; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5451 = raw2561Labels := by decide +kernel
    rw [ha, hj, canonical2561 B hB]
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

theorem sound915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node915 node915Labels = Sparse.eval nodeValue915 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 915) = mixedMoment B node915 node915Labels := rfl
  simpa [nodeValue915, Sparse.eval] using hc.symm

theorem sound916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node916 node916Labels = Sparse.eval nodeValue916 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 916) = mixedMoment B node916 node916Labels := rfl
  simpa [nodeValue916, Sparse.eval] using hc.symm

theorem sound917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node917 node917Labels = Sparse.eval nodeValue917 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 917) = mixedMoment B node917 node917Labels := rfl
  simpa [nodeValue917, Sparse.eval] using hc.symm

theorem sound932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node932 node932Labels = Sparse.eval nodeValue932 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 932) = mixedMoment B node932 node932Labels := rfl
  simpa [nodeValue932, Sparse.eval] using hc.symm

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

theorem sound1035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1035 node1035Labels = Sparse.eval nodeValue1035 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1035) = mixedMoment B node1035 node1035Labels := rfl
  simpa [nodeValue1035, Sparse.eval] using hc.symm

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

theorem sound1632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1632 node1632Labels = Sparse.eval nodeValue1632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1632) = mixedMoment B node1632 node1632Labels := rfl
  simpa [nodeValue1632, Sparse.eval] using hc.symm

theorem sound1633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1633 node1633Labels = Sparse.eval nodeValue1633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1633) = mixedMoment B node1633 node1633Labels := rfl
  simpa [nodeValue1633, Sparse.eval] using hc.symm

theorem sound1634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1634 node1634Labels = Sparse.eval nodeValue1634 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1634) = mixedMoment B node1634 node1634Labels := rfl
  simpa [nodeValue1634, Sparse.eval] using hc.symm

theorem sound1645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1645 node1645Labels = Sparse.eval nodeValue1645 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1645) = mixedMoment B node1645 node1645Labels := rfl
  simpa [nodeValue1645, Sparse.eval] using hc.symm

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

theorem sound1681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1681 node1681Labels = Sparse.eval nodeValue1681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1681) = mixedMoment B node1681 node1681Labels := rfl
  simpa [nodeValue1681, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1875 node1875Labels = Sparse.eval nodeValue1875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1875) = mixedMoment B node1875 node1875Labels := rfl
  simpa [nodeValue1875, Sparse.eval] using hc.symm

theorem sound1880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1880 node1880Labels = Sparse.eval nodeValue1880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1880) = mixedMoment B node1880 node1880Labels := rfl
  simpa [nodeValue1880, Sparse.eval] using hc.symm

theorem sound1905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1905 node1905Labels = Sparse.eval nodeValue1905 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1905) = mixedMoment B node1905 node1905Labels := rfl
  simpa [nodeValue1905, Sparse.eval] using hc.symm

theorem sound1917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1917 node1917Labels = Sparse.eval nodeValue1917 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1917) = mixedMoment B node1917 node1917Labels := rfl
  simpa [nodeValue1917, Sparse.eval] using hc.symm

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

theorem sound1924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1924 node1924Labels = Sparse.eval nodeValue1924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1924) = mixedMoment B node1924 node1924Labels := rfl
  simpa [nodeValue1924, Sparse.eval] using hc.symm

theorem sound1938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1938 node1938Labels = Sparse.eval nodeValue1938 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1938) = mixedMoment B node1938 node1938Labels := rfl
  simpa [nodeValue1938, Sparse.eval] using hc.symm

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

theorem sound2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2109 node2109Labels = Sparse.eval nodeValue2109 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2109) = mixedMoment B node2109 node2109Labels := rfl
  simpa [nodeValue2109, Sparse.eval] using hc.symm

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

theorem sound2328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2328 node2328Labels = Sparse.eval nodeValue2328 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2328) = mixedMoment B node2328 node2328Labels := rfl
  simpa [nodeValue2328, Sparse.eval] using hc.symm

theorem sound2329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2329 node2329Labels = Sparse.eval nodeValue2329 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2329) = mixedMoment B node2329 node2329Labels := rfl
  simpa [nodeValue2329, Sparse.eval] using hc.symm

theorem sound2341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2341 node2341Labels = Sparse.eval nodeValue2341 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2341) = mixedMoment B node2341 node2341Labels := rfl
  simpa [nodeValue2341, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2424 node2424Labels = Sparse.eval nodeValue2424 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2424) = mixedMoment B node2424 node2424Labels := rfl
  simpa [nodeValue2424, Sparse.eval] using hc.symm

theorem sound2431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2431 node2431Labels = Sparse.eval nodeValue2431 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2431) = mixedMoment B node2431 node2431Labels := rfl
  simpa [nodeValue2431, Sparse.eval] using hc.symm

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

theorem sound2477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2477 node2477Labels = Sparse.eval nodeValue2477 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2477) = mixedMoment B node2477 node2477Labels := rfl
  simpa [nodeValue2477, Sparse.eval] using hc.symm

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

theorem sound2536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2536 node2536Labels = Sparse.eval nodeValue2536 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2536) = mixedMoment B node2536 node2536Labels := rfl
  simpa [nodeValue2536, Sparse.eval] using hc.symm

theorem sound2539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2539 node2539Labels = Sparse.eval nodeValue2539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2539) = mixedMoment B node2539 node2539Labels := rfl
  simpa [nodeValue2539, Sparse.eval] using hc.symm

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

theorem sound2589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2589 node2589Labels = Sparse.eval nodeValue2589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2589) = mixedMoment B node2589 node2589Labels := rfl
  simpa [nodeValue2589, Sparse.eval] using hc.symm

theorem sound2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2590 node2590Labels = Sparse.eval nodeValue2590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2590) = mixedMoment B node2590 node2590Labels := rfl
  simpa [nodeValue2590, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2672 node2672Labels = Sparse.eval nodeValue2672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2672) = mixedMoment B node2672 node2672Labels := rfl
  simpa [nodeValue2672, Sparse.eval] using hc.symm

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

theorem sound2765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2765 node2765Labels = Sparse.eval nodeValue2765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2765) = mixedMoment B node2765 node2765Labels := rfl
  simpa [nodeValue2765, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3370 node3370Labels = Sparse.eval nodeValue3370 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3370) = mixedMoment B node3370 node3370Labels := rfl
  simpa [nodeValue3370, Sparse.eval] using hc.symm

theorem sound3372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3372 node3372Labels = Sparse.eval nodeValue3372 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3372) = mixedMoment B node3372 node3372Labels := rfl
  simpa [nodeValue3372, Sparse.eval] using hc.symm

theorem sound3391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3391 node3391Labels = Sparse.eval nodeValue3391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3391) = mixedMoment B node3391 node3391Labels := rfl
  simpa [nodeValue3391, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3401 node3401Labels = Sparse.eval nodeValue3401 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3401) = mixedMoment B node3401 node3401Labels := rfl
  simpa [nodeValue3401, Sparse.eval] using hc.symm

theorem sound3402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3402 node3402Labels = Sparse.eval nodeValue3402 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3402) = mixedMoment B node3402 node3402Labels := rfl
  simpa [nodeValue3402, Sparse.eval] using hc.symm

theorem sound3417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3417 node3417Labels = Sparse.eval nodeValue3417 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3417) = mixedMoment B node3417 node3417Labels := rfl
  simpa [nodeValue3417, Sparse.eval] using hc.symm

theorem sound3440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3440 node3440Labels = Sparse.eval nodeValue3440 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3440) = mixedMoment B node3440 node3440Labels := rfl
  simpa [nodeValue3440, Sparse.eval] using hc.symm

theorem sound3444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3444 node3444Labels = Sparse.eval nodeValue3444 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3444) = mixedMoment B node3444 node3444Labels := rfl
  simpa [nodeValue3444, Sparse.eval] using hc.symm

theorem sound3453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3453 node3453Labels = Sparse.eval nodeValue3453 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3453) = mixedMoment B node3453 node3453Labels := rfl
  simpa [nodeValue3453, Sparse.eval] using hc.symm

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

theorem sound3563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3563 node3563Labels = Sparse.eval nodeValue3563 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3563) = mixedMoment B node3563 node3563Labels := rfl
  simpa [nodeValue3563, Sparse.eval] using hc.symm

theorem sound3564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3564 node3564Labels = Sparse.eval nodeValue3564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3564) = mixedMoment B node3564 node3564Labels := rfl
  simpa [nodeValue3564, Sparse.eval] using hc.symm

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

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

theorem sound3614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3614 node3614Labels = Sparse.eval nodeValue3614 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3614) = mixedMoment B node3614 node3614Labels := rfl
  simpa [nodeValue3614, Sparse.eval] using hc.symm

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

theorem sound503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node503 node503Labels = Sparse.eval nodeValue503 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue503 (familyPairVector B) := singlePair503 B _hB
    _ = _ := by norm_num [singlePairValue503, nodeValue503, Sparse.eval, mixedVector] <;> ring

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

theorem sound3787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3787 node3787Labels = Sparse.eval nodeValue3787 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3787) = mixedMoment B node3787 node3787Labels := rfl
  simpa [nodeValue3787, Sparse.eval] using hc.symm

theorem sound3790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3790 node3790Labels = Sparse.eval nodeValue3790 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3790) = mixedMoment B node3790 node3790Labels := rfl
  simpa [nodeValue3790, Sparse.eval] using hc.symm

theorem sound3804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3804 node3804Labels = Sparse.eval nodeValue3804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3804) = mixedMoment B node3804 node3804Labels := rfl
  simpa [nodeValue3804, Sparse.eval] using hc.symm

theorem sound3809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3809 node3809Labels = Sparse.eval nodeValue3809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3809) = mixedMoment B node3809 node3809Labels := rfl
  simpa [nodeValue3809, Sparse.eval] using hc.symm

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

theorem sound3815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3815 node3815Labels = Sparse.eval nodeValue3815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3815) = mixedMoment B node3815 node3815Labels := rfl
  simpa [nodeValue3815, Sparse.eval] using hc.symm

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

theorem sound3888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3888 node3888Labels = Sparse.eval nodeValue3888 (mixedVector B) := by
  have h := singleton3888 B _hB
  rw [sound503 B _hB _hF] at h
  norm_num [nodeValue3888, nodeValue503, Sparse.eval] at h ⊢
  linarith only [h]

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4337 node4337Labels = Sparse.eval nodeValue4337 (mixedVector B) := by
  have h := singleton4337 B _hB
  rw [sound915 B _hB _hF, sound1632 B _hB _hF] at h
  norm_num [nodeValue4337, nodeValue915, nodeValue1632, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4338 node4338Labels = Sparse.eval nodeValue4338 (mixedVector B) := by
  have h := singleton4338 B _hB
  rw [sound916 B _hB _hF, sound1633 B _hB _hF] at h
  norm_num [nodeValue4338, nodeValue916, nodeValue1633, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4339 node4339Labels = Sparse.eval nodeValue4339 (mixedVector B) := by
  have h := singleton4339 B _hB
  rw [sound917 B _hB _hF, sound1634 B _hB _hF] at h
  norm_num [nodeValue4339, nodeValue917, nodeValue1634, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4354 node4354Labels = Sparse.eval nodeValue4354 (mixedVector B) := by
  have h := singleton4354 B _hB
  rw [sound932 B _hB _hF, sound1681 B _hB _hF] at h
  norm_num [nodeValue4354, nodeValue932, nodeValue1681, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4452 node4452Labels = Sparse.eval nodeValue4452 (mixedVector B) := by
  have h := singleton4452 B _hB
  rw [sound1035 B _hB _hF, sound1645 B _hB _hF] at h
  norm_num [nodeValue4452, nodeValue1035, nodeValue1645, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4721 node4721Labels = Sparse.eval nodeValue4721 (mixedVector B) := by
  have h := singleton4721 B _hB
  rw [sound1875 B _hB _hF, sound1905 B _hB _hF] at h
  norm_num [nodeValue4721, nodeValue1875, nodeValue1905, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4726 node4726Labels = Sparse.eval nodeValue4726 (mixedVector B) := by
  have h := singleton4726 B _hB
  rw [sound1880 B _hB _hF, sound1938 B _hB _hF] at h
  norm_num [nodeValue4726, nodeValue1880, nodeValue1938, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4744 node4744Labels = Sparse.eval nodeValue4744 (mixedVector B) := by
  have h := singleton4744 B _hB
  rw [sound1917 B _hB _hF, sound1924 B _hB _hF] at h
  norm_num [nodeValue4744, nodeValue1917, nodeValue1924, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4936 node4936Labels = Sparse.eval nodeValue4936 (mixedVector B) := by
  have h := singleton4936 B _hB
  rw [sound2328 B _hB _hF, sound3401 B _hB _hF] at h
  norm_num [nodeValue4936, nodeValue2328, nodeValue3401, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4937 node4937Labels = Sparse.eval nodeValue4937 (mixedVector B) := by
  have h := singleton4937 B _hB
  rw [sound2329 B _hB _hF, sound3402 B _hB _hF] at h
  norm_num [nodeValue4937, nodeValue2329, nodeValue3402, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4949 node4949Labels = Sparse.eval nodeValue4949 (mixedVector B) := by
  have h := singleton4949 B _hB
  rw [sound2341 B _hB _hF, sound3417 B _hB _hF] at h
  norm_num [nodeValue4949, nodeValue2341, nodeValue3417, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5032 node5032Labels = Sparse.eval nodeValue5032 (mixedVector B) := by
  have h := singleton5032 B _hB
  rw [sound2424 B _hB _hF, sound3440 B _hB _hF] at h
  norm_num [nodeValue5032, nodeValue2424, nodeValue3440, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5038 node5038Labels = Sparse.eval nodeValue5038 (mixedVector B) := by
  have h := singleton5038 B _hB
  rw [sound2431 B _hB _hF, sound3453 B _hB _hF] at h
  norm_num [nodeValue5038, nodeValue2431, nodeValue3453, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5070 node5070Labels = Sparse.eval nodeValue5070 (mixedVector B) := by
  have h := singleton5070 B _hB
  rw [sound2477 B _hB _hF, sound3444 B _hB _hF] at h
  norm_num [nodeValue5070, nodeValue2477, nodeValue3444, Sparse.eval] at h ⊢
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

theorem sound5123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5123 node5123Labels = Sparse.eval nodeValue5123 (mixedVector B) := by
  have h := singleton5123 B _hB
  rw [sound2536 B _hB _hF, sound3370 B _hB _hF] at h
  norm_num [nodeValue5123, nodeValue2536, nodeValue3370, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5125 node5125Labels = Sparse.eval nodeValue5125 (mixedVector B) := by
  have h := singleton5125 B _hB
  rw [sound2539 B _hB _hF, sound3372 B _hB _hF] at h
  norm_num [nodeValue5125, nodeValue2539, nodeValue3372, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5162 node5162Labels = Sparse.eval nodeValue5162 (mixedVector B) := by
  have h := singleton5162 B _hB
  rw [sound2589 B _hB _hF, sound3563 B _hB _hF] at h
  norm_num [nodeValue5162, nodeValue2589, nodeValue3563, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5163 node5163Labels = Sparse.eval nodeValue5163 (mixedVector B) := by
  have h := singleton5163 B _hB
  rw [sound2590 B _hB _hF, sound3564 B _hB _hF] at h
  norm_num [nodeValue5163, nodeValue2590, nodeValue3564, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5228 node5228Labels = Sparse.eval nodeValue5228 (mixedVector B) := by
  have h := singleton5228 B _hB
  rw [sound2672 B _hB _hF, sound3391 B _hB _hF] at h
  norm_num [nodeValue5228, nodeValue2672, nodeValue3391, Sparse.eval] at h ⊢
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

theorem sound5290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5290 node5290Labels = Sparse.eval nodeValue5290 (mixedVector B) := by
  have h := singleton5290 B _hB
  rw [sound2764 B _hB _hF, sound3581 B _hB _hF] at h
  norm_num [nodeValue5290, nodeValue2764, nodeValue3581, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5291 node5291Labels = Sparse.eval nodeValue5291 (mixedVector B) := by
  have h := singleton5291 B _hB
  rw [sound2765 B _hB _hF, sound3582 B _hB _hF] at h
  norm_num [nodeValue5291, nodeValue2765, nodeValue3582, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5401 node5401Labels = Sparse.eval nodeValue5401 (mixedVector B) := by
  have h := singleton5401 B _hB
  rw [sound3787 B _hB _hF, sound3804 B _hB _hF] at h
  norm_num [nodeValue5401, nodeValue3787, nodeValue3804, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5404 node5404Labels = Sparse.eval nodeValue5404 (mixedVector B) := by
  have h := singleton5404 B _hB
  rw [sound3790 B _hB _hF, sound3815 B _hB _hF] at h
  norm_num [nodeValue5404, nodeValue3790, nodeValue3815, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5411 node5411Labels = Sparse.eval nodeValue5411 (mixedVector B) := by
  have h := singleton5411 B _hB
  rw [sound3809 B _hB _hF, sound3813 B _hB _hF] at h
  norm_num [nodeValue5411, nodeValue3809, nodeValue3813, Sparse.eval] at h ⊢
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

theorem sound5451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5451 node5451Labels = Sparse.eval nodeValue5451 (mixedVector B) := by
  have h := singleton5451 B _hB
  rw [sound3888 B _hB _hF, sound3913 B _hB _hF] at h
  norm_num [nodeValue5451, nodeValue3888, nodeValue3913, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources74
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2394 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2394 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2394 + difference 0 1) (sourceB2394 + difference 1 0) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2394 + difference 0 1) (sourceB2394 + difference 1 0) sourceC2394) = raw32791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32791; decide +kernel
    rw [ha]
    exact (canonical32791 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2394 + difference 0 2) (sourceB2394 + difference 2 0) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA2394 + difference 0 2) (sourceB2394 + difference 2 0) sourceC2394) = raw32792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32792; decide +kernel
    rw [ha]
    exact (canonical32792 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2394 + difference 0 3) (sourceB2394 + difference 3 0) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2394 + difference 0 3) (sourceB2394 + difference 3 0) sourceC2394) = raw9592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw9592; decide +kernel
    rw [ha]
    exact (canonical9592 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2394 + difference 0 4) (sourceB2394 + difference 4 0) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA2394 + difference 0 4) (sourceB2394 + difference 4 0) sourceC2394) = raw32793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32793; decide +kernel
    rw [ha]
    exact (canonical32793 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2394 + difference 0 5) (sourceB2394 + difference 5 0) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2394 + difference 0 5) (sourceB2394 + difference 5 0) sourceC2394) = raw32794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32794; decide +kernel
    rw [ha]
    exact (canonical32794 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2394 + difference 1 0) (sourceB2394 + difference 0 1) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA2394 + difference 1 0) (sourceB2394 + difference 0 1) sourceC2394) = raw9607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw9607; decide +kernel
    rw [ha]
    exact (canonical9607 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2394 + difference 1 2) (sourceB2394 + difference 2 1) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA2394 + difference 1 2) (sourceB2394 + difference 2 1) sourceC2394) = raw9609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw9609; decide +kernel
    rw [ha]
    exact (canonical9609 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2394 + difference 1 3) (sourceB2394 + difference 3 1) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA2394 + difference 1 3) (sourceB2394 + difference 3 1) sourceC2394) = raw28619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw28619; decide +kernel
    rw [ha]
    exact (canonical28619 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2394 + difference 1 4) (sourceB2394 + difference 4 1) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2394 + difference 1 4) (sourceB2394 + difference 4 1) sourceC2394) = raw9610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw9610; decide +kernel
    rw [ha]
    exact (canonical9610 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2394 + difference 1 5) (sourceB2394 + difference 5 1) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA2394 + difference 1 5) (sourceB2394 + difference 5 1) sourceC2394) = raw9611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw9611; decide +kernel
    rw [ha]
    exact (canonical9611 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2394 + difference 2 0) (sourceB2394 + difference 0 2) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4337) := by
    have ha : (tripleCharges (sourceA2394 + difference 2 0) (sourceB2394 + difference 0 2) sourceC2394) = raw32795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32795; decide +kernel
    rw [ha]
    exact (canonical32795 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2394 + difference 2 1) (sourceB2394 + difference 1 2) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4936) := by
    have ha : (tripleCharges (sourceA2394 + difference 2 1) (sourceB2394 + difference 1 2) sourceC2394) = raw32796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32796; decide +kernel
    rw [ha]
    exact (canonical32796 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2394 + difference 2 3) (sourceB2394 + difference 3 2) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2394 + difference 2 3) (sourceB2394 + difference 3 2) sourceC2394) = raw9603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw9603; decide +kernel
    rw [ha]
    exact (canonical9603 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2394 + difference 2 4) (sourceB2394 + difference 4 2) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2394 + difference 2 4) (sourceB2394 + difference 4 2) sourceC2394) = raw32797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32797; decide +kernel
    rw [ha]
    exact (canonical32797 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2394 + difference 2 5) (sourceB2394 + difference 5 2) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA2394 + difference 2 5) (sourceB2394 + difference 5 2) sourceC2394) = raw32798 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32798; decide +kernel
    rw [ha]
    exact (canonical32798 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2394 + difference 3 0) (sourceB2394 + difference 0 3) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4339) := by
    have ha : (tripleCharges (sourceA2394 + difference 3 0) (sourceB2394 + difference 0 3) sourceC2394) = raw32799 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32799; decide +kernel
    rw [ha]
    exact (canonical32799 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2394 + difference 3 1) (sourceB2394 + difference 1 3) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4937) := by
    have ha : (tripleCharges (sourceA2394 + difference 3 1) (sourceB2394 + difference 1 3) sourceC2394) = raw32800 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32800; decide +kernel
    rw [ha]
    exact (canonical32800 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2394 + difference 3 2) (sourceB2394 + difference 2 3) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5032) := by
    have ha : (tripleCharges (sourceA2394 + difference 3 2) (sourceB2394 + difference 2 3) sourceC2394) = raw32801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32801; decide +kernel
    rw [ha]
    exact (canonical32801 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2394 + difference 3 4) (sourceB2394 + difference 4 3) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5125) := by
    have ha : (tripleCharges (sourceA2394 + difference 3 4) (sourceB2394 + difference 4 3) sourceC2394) = raw32802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32802; decide +kernel
    rw [ha]
    exact (canonical32802 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2394 + difference 3 5) (sourceB2394 + difference 5 3) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2394 + difference 3 5) (sourceB2394 + difference 5 3) sourceC2394) = raw32803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32803; decide +kernel
    rw [ha]
    exact (canonical32803 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2394 + difference 4 0) (sourceB2394 + difference 0 4) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA2394 + difference 4 0) (sourceB2394 + difference 0 4) sourceC2394) = raw29536 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw29536; decide +kernel
    rw [ha]
    exact (canonical29536 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2394 + difference 4 1) (sourceB2394 + difference 1 4) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2394 + difference 4 1) (sourceB2394 + difference 1 4) sourceC2394) = raw29537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw29537; decide +kernel
    rw [ha]
    exact (canonical29537 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2394 + difference 4 2) (sourceB2394 + difference 2 4) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5038) := by
    have ha : (tripleCharges (sourceA2394 + difference 4 2) (sourceB2394 + difference 2 4) sourceC2394) = raw29538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw29538; decide +kernel
    rw [ha]
    exact (canonical29538 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2394 + difference 4 3) (sourceB2394 + difference 3 4) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2394 + difference 4 3) (sourceB2394 + difference 3 4) sourceC2394) = raw9613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw9613; decide +kernel
    rw [ha]
    exact (canonical9613 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2394 + difference 4 5) (sourceB2394 + difference 5 4) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2394 + difference 4 5) (sourceB2394 + difference 5 4) sourceC2394) = raw29539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw29539; decide +kernel
    rw [ha]
    exact (canonical29539 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2394 + difference 5 0) (sourceB2394 + difference 0 5) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4338) := by
    have ha : (tripleCharges (sourceA2394 + difference 5 0) (sourceB2394 + difference 0 5) sourceC2394) = raw28624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw28624; decide +kernel
    rw [ha]
    exact (canonical28624 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2394 + difference 5 1) (sourceB2394 + difference 1 5) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4726) := by
    have ha : (tripleCharges (sourceA2394 + difference 5 1) (sourceB2394 + difference 1 5) sourceC2394) = raw28625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw28625; decide +kernel
    rw [ha]
    exact (canonical28625 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2394 + difference 5 2) (sourceB2394 + difference 2 5) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4721) := by
    have ha : (tripleCharges (sourceA2394 + difference 5 2) (sourceB2394 + difference 2 5) sourceC2394) = raw28626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw28626; decide +kernel
    rw [ha]
    exact (canonical28626 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2394 + difference 5 3) (sourceB2394 + difference 3 5) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2394 + difference 5 3) (sourceB2394 + difference 3 5) sourceC2394) = raw9618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw9618; decide +kernel
    rw [ha]
    exact (canonical9618 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2394 + difference 5 4) (sourceB2394 + difference 4 5) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2394 + difference 5 4) (sourceB2394 + difference 4 5) sourceC2394) = raw28627 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw28627; decide +kernel
    rw [ha]
    exact (canonical28627 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2394 sourceB2394 sourceC2394
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2394, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1944 : Integer.Sparse.reindex keyMap MixedData.row1944 = numericRow1944 := by decide +kernel

theorem numericCheck1944 (x : Master → ℝ) : Integer.Sparse.eval numericRow1944 x =
    (17280 : ℝ) * reducedSource1944 x := by
  norm_num [numericRow1944, reducedSource1944, Integer.Sparse.eval, Sparse.eval, nodeValue4337, nodeValue4338, nodeValue4339, nodeValue4354, nodeValue4452, nodeValue4721, nodeValue4726, nodeValue4744, nodeValue4868, nodeValue4936, nodeValue4937, nodeValue4949, nodeValue5032, nodeValue5038, nodeValue5070, nodeValue5123, nodeValue5125, nodeValue5162, nodeValue5163, nodeValue5172, nodeValue5176, nodeValue5228, nodeValue5290, nodeValue5291, nodeValue5401, nodeValue5404, nodeValue5411, nodeValue5451, nodeValue5485]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1944 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1944 (mixedVector B) = 0 := by
  have h4337 : mixedVector B (Sum.inr 4337) = Sparse.eval nodeValue4337 (mixedVector B) := by
    change mixedMoment B node4337 node4337Labels = _
    exact sound4337 B hB hF
  have h4338 : mixedVector B (Sum.inr 4338) = Sparse.eval nodeValue4338 (mixedVector B) := by
    change mixedMoment B node4338 node4338Labels = _
    exact sound4338 B hB hF
  have h4339 : mixedVector B (Sum.inr 4339) = Sparse.eval nodeValue4339 (mixedVector B) := by
    change mixedMoment B node4339 node4339Labels = _
    exact sound4339 B hB hF
  have h4354 : mixedVector B (Sum.inr 4354) = Sparse.eval nodeValue4354 (mixedVector B) := by
    change mixedMoment B node4354 node4354Labels = _
    exact sound4354 B hB hF
  have h4452 : mixedVector B (Sum.inr 4452) = Sparse.eval nodeValue4452 (mixedVector B) := by
    change mixedMoment B node4452 node4452Labels = _
    exact sound4452 B hB hF
  have h4721 : mixedVector B (Sum.inr 4721) = Sparse.eval nodeValue4721 (mixedVector B) := by
    change mixedMoment B node4721 node4721Labels = _
    exact sound4721 B hB hF
  have h4726 : mixedVector B (Sum.inr 4726) = Sparse.eval nodeValue4726 (mixedVector B) := by
    change mixedMoment B node4726 node4726Labels = _
    exact sound4726 B hB hF
  have h4744 : mixedVector B (Sum.inr 4744) = Sparse.eval nodeValue4744 (mixedVector B) := by
    change mixedMoment B node4744 node4744Labels = _
    exact sound4744 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4936 : mixedVector B (Sum.inr 4936) = Sparse.eval nodeValue4936 (mixedVector B) := by
    change mixedMoment B node4936 node4936Labels = _
    exact sound4936 B hB hF
  have h4937 : mixedVector B (Sum.inr 4937) = Sparse.eval nodeValue4937 (mixedVector B) := by
    change mixedMoment B node4937 node4937Labels = _
    exact sound4937 B hB hF
  have h4949 : mixedVector B (Sum.inr 4949) = Sparse.eval nodeValue4949 (mixedVector B) := by
    change mixedMoment B node4949 node4949Labels = _
    exact sound4949 B hB hF
  have h5032 : mixedVector B (Sum.inr 5032) = Sparse.eval nodeValue5032 (mixedVector B) := by
    change mixedMoment B node5032 node5032Labels = _
    exact sound5032 B hB hF
  have h5038 : mixedVector B (Sum.inr 5038) = Sparse.eval nodeValue5038 (mixedVector B) := by
    change mixedMoment B node5038 node5038Labels = _
    exact sound5038 B hB hF
  have h5070 : mixedVector B (Sum.inr 5070) = Sparse.eval nodeValue5070 (mixedVector B) := by
    change mixedMoment B node5070 node5070Labels = _
    exact sound5070 B hB hF
  have h5123 : mixedVector B (Sum.inr 5123) = Sparse.eval nodeValue5123 (mixedVector B) := by
    change mixedMoment B node5123 node5123Labels = _
    exact sound5123 B hB hF
  have h5125 : mixedVector B (Sum.inr 5125) = Sparse.eval nodeValue5125 (mixedVector B) := by
    change mixedMoment B node5125 node5125Labels = _
    exact sound5125 B hB hF
  have h5162 : mixedVector B (Sum.inr 5162) = Sparse.eval nodeValue5162 (mixedVector B) := by
    change mixedMoment B node5162 node5162Labels = _
    exact sound5162 B hB hF
  have h5163 : mixedVector B (Sum.inr 5163) = Sparse.eval nodeValue5163 (mixedVector B) := by
    change mixedMoment B node5163 node5163Labels = _
    exact sound5163 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172_e B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5228 : mixedVector B (Sum.inr 5228) = Sparse.eval nodeValue5228 (mixedVector B) := by
    change mixedMoment B node5228 node5228Labels = _
    exact sound5228 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5291 : mixedVector B (Sum.inr 5291) = Sparse.eval nodeValue5291 (mixedVector B) := by
    change mixedMoment B node5291 node5291Labels = _
    exact sound5291 B hB hF
  have h5401 : mixedVector B (Sum.inr 5401) = Sparse.eval nodeValue5401 (mixedVector B) := by
    change mixedMoment B node5401 node5401Labels = _
    exact sound5401 B hB hF
  have h5404 : mixedVector B (Sum.inr 5404) = Sparse.eval nodeValue5404 (mixedVector B) := by
    change mixedMoment B node5404 node5404Labels = _
    exact sound5404 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485_e B hB hF
  simpa only [sourceForm2394, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4337, h4338, h4339, h4354, h4452, h4721, h4726, h4744, h4868, h4936, h4937, h4949, h5032, h5038, h5070, h5123, h5125, h5162, h5163, h5172, h5176, h5228, h5290, h5291, h5401, h5404, h5411, h5451, h5485, reducedSource1944] using sourceEq2394 B hB

theorem rowSound1944_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1944 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1944, numericCheck1944, reducedZero1944 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e_oai
