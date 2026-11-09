-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:52:05.639275+00:00
-- url     : https://prove2.me/submissions/2ddd8095-79d8-4789-8125-cc0de9f454ac

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3088_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3094_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound267_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound269_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw270 raw270Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw270 raw270Labels = mixedMoment B raw270step0 raw270step0Labels := by
      have ha : raw270step0 = (fun i j => raw270 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw270step0 raw270; decide +kernel
      have hl : raw270step0Labels = raw270Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw270 raw270Labels permutation8 permutation5
    mixedMoment B raw270step0 raw270step0Labels = mixedMoment B raw270step1 raw270step1Labels := by
      have ha : raw270step1 = raw270step0 := by apply Matrix.ext; unfold raw270step1 raw270step0; decide +kernel
      have hl : raw270step0Labels = labelEmbedding1 ∘ raw270step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw270step0 raw270step0Labels raw270step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2767 node2767Labels := by rfl

theorem canonical271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw271 raw271Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw271 raw271Labels = mixedMoment B raw271step0 raw271step0Labels := by
      have ha : raw271step0 = (fun i j => raw271 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw271step0 raw271; decide +kernel
      have hl : raw271step0Labels = raw271Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw271 raw271Labels permutation8 permutation5
    _ = mixedMoment B node404 node404Labels := by rfl

theorem canonical278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw278 raw278Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw278 raw278Labels = mixedMoment B raw278step0 raw278step0Labels := by
      have ha : raw278step0 = (fun i j => raw278 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw278step0 raw278; decide +kernel
      have hl : raw278step0Labels = raw278Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw278 raw278Labels permutation8 permutation5
    mixedMoment B raw278step0 raw278step0Labels = mixedMoment B raw278step1 raw278step1Labels := by
      have ha : raw278step1 = raw278step0 := by apply Matrix.ext; unfold raw278step1 raw278step0; decide +kernel
      have hl : raw278step0Labels = labelEmbedding1 ∘ raw278step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw278step0 raw278step0Labels raw278step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

theorem canonical279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw279 raw279Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw279 raw279Labels = mixedMoment B raw279step0 raw279step0Labels := by
      have ha : raw279step0 = (fun i j => raw279 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw279step0 raw279; decide +kernel
      have hl : raw279step0Labels = raw279Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw279 raw279Labels permutation8 permutation5
    _ = mixedMoment B node412 node412Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6406 raw6406Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw6406 raw6406Labels = mixedMoment B raw6406step0 raw6406step0Labels := by
      have hz : ∀ j, raw6406 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6406step0 = (fun i j => raw6406 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6406step0 raw6406; decide +kernel
      have hl : raw6406step0Labels = raw6406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6406 raw6406Labels permutation346 hz
    mixedMoment B raw6406step0 raw6406step0Labels = mixedMoment B raw6406step1 raw6406step1Labels := by
      have ha : raw6406step1 = (fun i j => raw6406step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6406step1 raw6406step0; decide +kernel
      have hl : raw6406step1Labels = raw6406step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6406step0 raw6406step0Labels permutation32 permutation6
    _ = mixedMoment B node2732 node2732Labels := by rfl

theorem canonical6412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6412 raw6412Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw6412 raw6412Labels = mixedMoment B raw6412step0 raw6412step0Labels := by
      have hz : ∀ j, raw6412 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6412step0 = (fun i j => raw6412 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6412step0 raw6412; decide +kernel
      have hl : raw6412step0Labels = raw6412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6412 raw6412Labels permutation346 hz
    mixedMoment B raw6412step0 raw6412step0Labels = mixedMoment B raw6412step1 raw6412step1Labels := by
      have ha : raw6412step1 = (fun i j => raw6412step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6412step1 raw6412step0; decide +kernel
      have hl : raw6412step1Labels = raw6412step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6412step0 raw6412step0Labels permutation32 permutation6
    _ = mixedMoment B node2723 node2723Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6668 raw6668Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw6668 raw6668Labels = mixedMoment B raw6668step0 raw6668step0Labels := by
      have hz : ∀ j, raw6668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6668step0 = (fun i j => raw6668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6668step0 raw6668; decide +kernel
      have hl : raw6668step0Labels = raw6668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6668 raw6668Labels permutation346 hz
    mixedMoment B raw6668step0 raw6668step0Labels = mixedMoment B raw6668step1 raw6668step1Labels := by
      have ha : raw6668step1 = (fun i j => raw6668step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6668step1 raw6668step0; decide +kernel
      have hl : raw6668step1Labels = raw6668step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6668step0 raw6668step0Labels permutation38 permutation2
    _ = mixedMoment B node3039 node3039Labels := by rfl

theorem canonical6669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6669 raw6669Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw6669 raw6669Labels = mixedMoment B raw6669step0 raw6669step0Labels := by
      have hz : ∀ j, raw6669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6669step0 = (fun i j => raw6669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6669step0 raw6669; decide +kernel
      have hl : raw6669step0Labels = raw6669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6669 raw6669Labels permutation346 hz
    mixedMoment B raw6669step0 raw6669step0Labels = mixedMoment B raw6669step1 raw6669step1Labels := by
      have ha : raw6669step1 = (fun i j => raw6669step0 (permutation102 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6669step1 raw6669step0; decide +kernel
      have hl : raw6669step1Labels = raw6669step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6669step0 raw6669step0Labels permutation102 permutation4
    _ = mixedMoment B node3881 node3881Labels := by rfl

theorem canonical6670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6670 raw6670Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw6670 raw6670Labels = mixedMoment B raw6670step0 raw6670step0Labels := by
      have ha : raw6670step0 = (fun i j => raw6670 (permutation515 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6670step0 raw6670; decide +kernel
      have hl : raw6670step0Labels = raw6670Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6670 raw6670Labels permutation515 permutation4
    _ = mixedMoment B node3880 node3880Labels := by rfl

theorem canonical6671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6671 raw6671Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw6671 raw6671Labels = mixedMoment B raw6671step0 raw6671step0Labels := by
      have hz : ∀ j, raw6671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6671step0 = (fun i j => raw6671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6671step0 raw6671; decide +kernel
      have hl : raw6671step0Labels = raw6671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6671 raw6671Labels permutation346 hz
    mixedMoment B raw6671step0 raw6671step0Labels = mixedMoment B raw6671step1 raw6671step1Labels := by
      have ha : raw6671step1 = (fun i j => raw6671step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6671step1 raw6671step0; decide +kernel
      have hl : raw6671step1Labels = raw6671step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6671step0 raw6671step0Labels permutation38 permutation2
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical6672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6672 raw6672Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw6672 raw6672Labels = mixedMoment B raw6672step0 raw6672step0Labels := by
      have hz : ∀ j, raw6672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6672step0 = (fun i j => raw6672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6672step0 raw6672; decide +kernel
      have hl : raw6672step0Labels = raw6672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6672 raw6672Labels permutation346 hz
    mixedMoment B raw6672step0 raw6672step0Labels = mixedMoment B raw6672step1 raw6672step1Labels := by
      have ha : raw6672step1 = (fun i j => raw6672step0 (permutation98 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6672step1 raw6672step0; decide +kernel
      have hl : raw6672step1Labels = raw6672step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6672step0 raw6672step0Labels permutation98 permutation4
    _ = mixedMoment B node3885 node3885Labels := by rfl

theorem canonical6673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6673 raw6673Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw6673 raw6673Labels = mixedMoment B raw6673step0 raw6673step0Labels := by
      have hz : ∀ j, raw6673 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6673step0 = (fun i j => raw6673 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6673step0 raw6673; decide +kernel
      have hl : raw6673step0Labels = raw6673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6673 raw6673Labels permutation346 hz
    mixedMoment B raw6673step0 raw6673step0Labels = mixedMoment B raw6673step1 raw6673step1Labels := by
      have ha : raw6673step1 = (fun i j => raw6673step0 (permutation96 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6673step1 raw6673step0; decide +kernel
      have hl : raw6673step1Labels = raw6673step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6673step0 raw6673step0Labels permutation96 permutation4
    _ = mixedMoment B node3910 node3910Labels := by rfl

theorem canonical6674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6674 raw6674Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw6674 raw6674Labels = mixedMoment B raw6674step0 raw6674step0Labels := by
      have hz : ∀ j, raw6674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6674step0 = (fun i j => raw6674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6674step0 raw6674; decide +kernel
      have hl : raw6674step0Labels = raw6674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6674 raw6674Labels permutation346 hz
    mixedMoment B raw6674step0 raw6674step0Labels = mixedMoment B raw6674step1 raw6674step1Labels := by
      have ha : raw6674step1 = (fun i j => raw6674step0 (permutation80 i) (permutation0 j)) := by apply Matrix.ext; unfold raw6674step1 raw6674step0; decide +kernel
      have hl : raw6674step1Labels = raw6674step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6674step0 raw6674step0Labels permutation80 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical6675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6675 raw6675Labels = mixedMoment B node1370 node1370Labels := by
  calc
    mixedMoment B raw6675 raw6675Labels = mixedMoment B raw6675step0 raw6675step0Labels := by
      have hz : ∀ j, raw6675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6675step0 = (fun i j => raw6675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6675step0 raw6675; decide +kernel
      have hl : raw6675step0Labels = raw6675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6675 raw6675Labels permutation346 hz
    mixedMoment B raw6675step0 raw6675step0Labels = mixedMoment B raw6675step1 raw6675step1Labels := by
      have ha : raw6675step1 = (fun i j => raw6675step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6675step1 raw6675step0; decide +kernel
      have hl : raw6675step1Labels = raw6675step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6675step0 raw6675step0Labels permutation38 permutation2
    _ = mixedMoment B node1370 node1370Labels := by rfl

theorem canonical6676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6676 raw6676Labels = mixedMoment B node1358 node1358Labels := by
  calc
    mixedMoment B raw6676 raw6676Labels = mixedMoment B raw6676step0 raw6676step0Labels := by
      have ha : raw6676step0 = (fun i j => raw6676 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6676step0 raw6676; decide +kernel
      have hl : raw6676step0Labels = raw6676Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6676 raw6676Labels permutation200 permutation2
    _ = mixedMoment B node1358 node1358Labels := by rfl

theorem canonical6677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6677 raw6677Labels = mixedMoment B node1423 node1423Labels := by
  calc
    mixedMoment B raw6677 raw6677Labels = mixedMoment B raw6677step0 raw6677step0Labels := by
      have hz : ∀ j, raw6677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6677step0 = (fun i j => raw6677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6677step0 raw6677; decide +kernel
      have hl : raw6677step0Labels = raw6677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6677 raw6677Labels permutation346 hz
    _ = mixedMoment B node1423 node1423Labels := by rfl

theorem canonical6678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6678 raw6678Labels = mixedMoment B node1363 node1363Labels := by
  calc
    mixedMoment B raw6678 raw6678Labels = mixedMoment B raw6678step0 raw6678step0Labels := by
      have hz : ∀ j, raw6678 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6678step0 = (fun i j => raw6678 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6678step0 raw6678; decide +kernel
      have hl : raw6678step0Labels = raw6678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6678 raw6678Labels permutation346 hz
    mixedMoment B raw6678step0 raw6678step0Labels = mixedMoment B raw6678step1 raw6678step1Labels := by
      have ha : raw6678step1 = (fun i j => raw6678step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6678step1 raw6678step0; decide +kernel
      have hl : raw6678step1Labels = raw6678step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6678step0 raw6678step0Labels permutation38 permutation2
    _ = mixedMoment B node1363 node1363Labels := by rfl

theorem canonical6679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6679 raw6679Labels = mixedMoment B node1361 node1361Labels := by
  calc
    mixedMoment B raw6679 raw6679Labels = mixedMoment B raw6679step0 raw6679step0Labels := by
      have hz : ∀ j, raw6679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6679step0 = (fun i j => raw6679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6679step0 raw6679; decide +kernel
      have hl : raw6679step0Labels = raw6679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6679 raw6679Labels permutation346 hz
    mixedMoment B raw6679step0 raw6679step0Labels = mixedMoment B raw6679step1 raw6679step1Labels := by
      have ha : raw6679step1 = (fun i j => raw6679step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6679step1 raw6679step0; decide +kernel
      have hl : raw6679step1Labels = raw6679step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6679step0 raw6679step0Labels permutation38 permutation2
    _ = mixedMoment B node1361 node1361Labels := by rfl

theorem canonical6680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6680 raw6680Labels = mixedMoment B node2976 node2976Labels := by
  calc
    mixedMoment B raw6680 raw6680Labels = mixedMoment B raw6680step0 raw6680step0Labels := by
      have ha : raw6680step0 = (fun i j => raw6680 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6680step0 raw6680; decide +kernel
      have hl : raw6680step0Labels = raw6680Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6680 raw6680Labels permutation182 permutation2
    _ = mixedMoment B node2976 node2976Labels := by rfl

theorem canonical6681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6681 raw6681Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw6681 raw6681Labels = mixedMoment B raw6681step0 raw6681step0Labels := by
      have hz : ∀ j, raw6681 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6681step0 = (fun i j => raw6681 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6681step0 raw6681; decide +kernel
      have hl : raw6681step0Labels = raw6681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6681 raw6681Labels permutation346 hz
    mixedMoment B raw6681step0 raw6681step0Labels = mixedMoment B raw6681step1 raw6681step1Labels := by
      have ha : raw6681step1 = (fun i j => raw6681step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6681step1 raw6681step0; decide +kernel
      have hl : raw6681step1Labels = raw6681step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6681step0 raw6681step0Labels permutation38 permutation2
    _ = mixedMoment B node2884 node2884Labels := by rfl

theorem canonical6682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6682 raw6682Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw6682 raw6682Labels = mixedMoment B raw6682step0 raw6682step0Labels := by
      have hz : ∀ j, raw6682 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6682step0 = (fun i j => raw6682 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6682step0 raw6682; decide +kernel
      have hl : raw6682step0Labels = raw6682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6682 raw6682Labels permutation346 hz
    mixedMoment B raw6682step0 raw6682step0Labels = mixedMoment B raw6682step1 raw6682step1Labels := by
      have ha : raw6682step1 = (fun i j => raw6682step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6682step1 raw6682step0; decide +kernel
      have hl : raw6682step1Labels = raw6682step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6682step0 raw6682step0Labels permutation40 permutation2
    _ = mixedMoment B node3039 node3039Labels := by rfl

theorem canonical6683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6683 raw6683Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw6683 raw6683Labels = mixedMoment B raw6683step0 raw6683step0Labels := by
      have hz : ∀ j, raw6683 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6683step0 = (fun i j => raw6683 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6683step0 raw6683; decide +kernel
      have hl : raw6683step0Labels = raw6683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6683 raw6683Labels permutation346 hz
    mixedMoment B raw6683step0 raw6683step0Labels = mixedMoment B raw6683step1 raw6683step1Labels := by
      have ha : raw6683step1 = (fun i j => raw6683step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6683step1 raw6683step0; decide +kernel
      have hl : raw6683step1Labels = raw6683step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6683step0 raw6683step0Labels permutation38 permutation2
    _ = mixedMoment B node3053 node3053Labels := by rfl

theorem canonical6684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6684 raw6684Labels = mixedMoment B node3008 node3008Labels := by
  calc
    mixedMoment B raw6684 raw6684Labels = mixedMoment B raw6684step0 raw6684step0Labels := by
      have ha : raw6684step0 = (fun i j => raw6684 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6684step0 raw6684; decide +kernel
      have hl : raw6684step0Labels = raw6684Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6684 raw6684Labels permutation158 permutation2
    _ = mixedMoment B node3008 node3008Labels := by rfl

theorem canonical6685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6685 raw6685Labels = mixedMoment B node2627 node2627Labels := by
  calc
    mixedMoment B raw6685 raw6685Labels = mixedMoment B raw6685step0 raw6685step0Labels := by
      have hz : ∀ j, raw6685 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6685step0 = (fun i j => raw6685 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6685step0 raw6685; decide +kernel
      have hl : raw6685step0Labels = raw6685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6685 raw6685Labels permutation346 hz
    mixedMoment B raw6685step0 raw6685step0Labels = mixedMoment B raw6685step1 raw6685step1Labels := by
      have ha : raw6685step1 = (fun i j => raw6685step0 (permutation102 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6685step1 raw6685step0; decide +kernel
      have hl : raw6685step1Labels = raw6685step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6685step0 raw6685step0Labels permutation102 permutation4
    _ = mixedMoment B node2627 node2627Labels := by rfl

theorem canonical6686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6686 raw6686Labels = mixedMoment B node3011 node3011Labels := by
  calc
    mixedMoment B raw6686 raw6686Labels = mixedMoment B raw6686step0 raw6686step0Labels := by
      have hz : ∀ j, raw6686 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6686step0 = (fun i j => raw6686 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6686step0 raw6686; decide +kernel
      have hl : raw6686step0Labels = raw6686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6686 raw6686Labels permutation346 hz
    _ = mixedMoment B node3011 node3011Labels := by rfl

theorem canonical6687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6687 raw6687Labels = mixedMoment B node2946 node2946Labels := by
  calc
    mixedMoment B raw6687 raw6687Labels = mixedMoment B raw6687step0 raw6687step0Labels := by
      have hz : ∀ j, raw6687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6687step0 = (fun i j => raw6687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6687step0 raw6687; decide +kernel
      have hl : raw6687step0Labels = raw6687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6687 raw6687Labels permutation346 hz
    mixedMoment B raw6687step0 raw6687step0Labels = mixedMoment B raw6687step1 raw6687step1Labels := by
      have ha : raw6687step1 = (fun i j => raw6687step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6687step1 raw6687step0; decide +kernel
      have hl : raw6687step1Labels = raw6687step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6687step0 raw6687step0Labels permutation151 permutation2
    mixedMoment B raw6687step1 raw6687step1Labels = mixedMoment B raw6687step2 raw6687step2Labels := by
      have ha : raw6687step2 = -raw6687step1 := by apply Matrix.ext; change ∀ i j, raw6687step2 i j = -(raw6687step1 i j); unfold raw6687step2 raw6687step1; decide +kernel
      have hl : raw6687step2Labels = raw6687step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2946 node2946Labels := by rfl

theorem canonical6688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6688 raw6688Labels = mixedMoment B node2862 node2862Labels := by
  calc
    mixedMoment B raw6688 raw6688Labels = mixedMoment B raw6688step0 raw6688step0Labels := by
      have ha : raw6688step0 = (fun i j => raw6688 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6688step0 raw6688; decide +kernel
      have hl : raw6688step0Labels = raw6688Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6688 raw6688Labels permutation200 permutation2
    _ = mixedMoment B node2862 node2862Labels := by rfl

theorem canonical6689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6689 raw6689Labels = mixedMoment B node3029 node3029Labels := by
  calc
    mixedMoment B raw6689 raw6689Labels = mixedMoment B raw6689step0 raw6689step0Labels := by
      have ha : raw6689step0 = (fun i j => raw6689 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6689step0 raw6689; decide +kernel
      have hl : raw6689step0Labels = raw6689Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6689 raw6689Labels permutation202 permutation2
    _ = mixedMoment B node3029 node3029Labels := by rfl

theorem canonical6690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6690 raw6690Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw6690 raw6690Labels = mixedMoment B raw6690step0 raw6690step0Labels := by
      have ha : raw6690step0 = (fun i j => raw6690 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6690step0 raw6690; decide +kernel
      have hl : raw6690step0Labels = raw6690Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6690 raw6690Labels permutation200 permutation2
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical6691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6691 raw6691Labels = mixedMoment B node2625 node2625Labels := by
  calc
    mixedMoment B raw6691 raw6691Labels = mixedMoment B raw6691step0 raw6691step0Labels := by
      have ha : raw6691step0 = (fun i j => raw6691 (permutation519 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6691step0 raw6691; decide +kernel
      have hl : raw6691step0Labels = raw6691Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6691 raw6691Labels permutation519 permutation4
    _ = mixedMoment B node2625 node2625Labels := by rfl

theorem canonical6692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6692 raw6692Labels = mixedMoment B node2972 node2972Labels := by
  calc
    mixedMoment B raw6692 raw6692Labels = mixedMoment B raw6692step0 raw6692step0Labels := by
      have ha : raw6692step0 = (fun i j => raw6692 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6692step0 raw6692; decide +kernel
      have hl : raw6692step0Labels = raw6692Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6692 raw6692Labels permutation182 permutation2
    _ = mixedMoment B node2972 node2972Labels := by rfl

theorem canonical6693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6693 raw6693Labels = mixedMoment B node2918 node2918Labels := by
  calc
    mixedMoment B raw6693 raw6693Labels = mixedMoment B raw6693step0 raw6693step0Labels := by
      have ha : raw6693step0 = (fun i j => raw6693 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6693step0 raw6693; decide +kernel
      have hl : raw6693step0Labels = raw6693Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6693 raw6693Labels permutation676 permutation2
    mixedMoment B raw6693step0 raw6693step0Labels = mixedMoment B raw6693step1 raw6693step1Labels := by
      have ha : raw6693step1 = -raw6693step0 := by apply Matrix.ext; change ∀ i j, raw6693step1 i j = -(raw6693step0 i j); unfold raw6693step1 raw6693step0; decide +kernel
      have hl : raw6693step1Labels = raw6693step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2918 node2918Labels := by rfl

theorem canonical6694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6694 raw6694Labels = mixedMoment B node2641 node2641Labels := by
  calc
    mixedMoment B raw6694 raw6694Labels = mixedMoment B raw6694step0 raw6694step0Labels := by
      have hz : ∀ j, raw6694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6694step0 = (fun i j => raw6694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6694step0 raw6694; decide +kernel
      have hl : raw6694step0Labels = raw6694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6694 raw6694Labels permutation346 hz
    mixedMoment B raw6694step0 raw6694step0Labels = mixedMoment B raw6694step1 raw6694step1Labels := by
      have ha : raw6694step1 = (fun i j => raw6694step0 (permutation101 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6694step1 raw6694step0; decide +kernel
      have hl : raw6694step1Labels = raw6694step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6694step0 raw6694step0Labels permutation101 permutation4
    _ = mixedMoment B node2641 node2641Labels := by rfl

theorem canonical6695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6695 raw6695Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw6695 raw6695Labels = mixedMoment B raw6695step0 raw6695step0Labels := by
      have hz : ∀ j, raw6695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6695step0 = (fun i j => raw6695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6695step0 raw6695; decide +kernel
      have hl : raw6695step0Labels = raw6695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6695 raw6695Labels permutation346 hz
    mixedMoment B raw6695step0 raw6695step0Labels = mixedMoment B raw6695step1 raw6695step1Labels := by
      have ha : raw6695step1 = (fun i j => raw6695step0 (permutation97 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6695step1 raw6695step0; decide +kernel
      have hl : raw6695step1Labels = raw6695step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6695step0 raw6695step0Labels permutation97 permutation4
    _ = mixedMoment B node2754 node2754Labels := by rfl

theorem canonical6696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6696 raw6696Labels = mixedMoment B node2868 node2868Labels := by
  calc
    mixedMoment B raw6696 raw6696Labels = mixedMoment B raw6696step0 raw6696step0Labels := by
      have hz : ∀ j, raw6696 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6696step0 = (fun i j => raw6696 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6696step0 raw6696; decide +kernel
      have hl : raw6696step0Labels = raw6696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6696 raw6696Labels permutation346 hz
    mixedMoment B raw6696step0 raw6696step0Labels = mixedMoment B raw6696step1 raw6696step1Labels := by
      have ha : raw6696step1 = (fun i j => raw6696step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6696step1 raw6696step0; decide +kernel
      have hl : raw6696step1Labels = raw6696step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6696step0 raw6696step0Labels permutation38 permutation2
    _ = mixedMoment B node2868 node2868Labels := by rfl

theorem canonical6697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6697 raw6697Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw6697 raw6697Labels = mixedMoment B raw6697step0 raw6697step0Labels := by
      have hz : ∀ j, raw6697 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6697step0 = (fun i j => raw6697 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6697step0 raw6697; decide +kernel
      have hl : raw6697step0Labels = raw6697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6697 raw6697Labels permutation346 hz
    mixedMoment B raw6697step0 raw6697step0Labels = mixedMoment B raw6697step1 raw6697step1Labels := by
      have ha : raw6697step1 = (fun i j => raw6697step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6697step1 raw6697step0; decide +kernel
      have hl : raw6697step1Labels = raw6697step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6697step0 raw6697step0Labels permutation38 permutation2
    _ = mixedMoment B node2865 node2865Labels := by rfl

theorem canonical6698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6698 raw6698Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw6698 raw6698Labels = mixedMoment B raw6698step0 raw6698step0Labels := by
      have hz : ∀ j, raw6698 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6698step0 = (fun i j => raw6698 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6698step0 raw6698; decide +kernel
      have hl : raw6698step0Labels = raw6698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6698 raw6698Labels permutation346 hz
    mixedMoment B raw6698step0 raw6698step0Labels = mixedMoment B raw6698step1 raw6698step1Labels := by
      have ha : raw6698step1 = (fun i j => raw6698step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6698step1 raw6698step0; decide +kernel
      have hl : raw6698step1Labels = raw6698step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6698step0 raw6698step0Labels permutation39 permutation2
    _ = mixedMoment B node3039 node3039Labels := by rfl

theorem canonical6699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6699 raw6699Labels = mixedMoment B node3031 node3031Labels := by
  calc
    mixedMoment B raw6699 raw6699Labels = mixedMoment B raw6699step0 raw6699step0Labels := by
      have hz : ∀ j, raw6699 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6699step0 = (fun i j => raw6699 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6699step0 raw6699; decide +kernel
      have hl : raw6699step0Labels = raw6699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6699 raw6699Labels permutation346 hz
    mixedMoment B raw6699step0 raw6699step0Labels = mixedMoment B raw6699step1 raw6699step1Labels := by
      have ha : raw6699step1 = (fun i j => raw6699step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6699step1 raw6699step0; decide +kernel
      have hl : raw6699step1Labels = raw6699step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6699step0 raw6699step0Labels permutation38 permutation2
    _ = mixedMoment B node3031 node3031Labels := by rfl

theorem canonical6728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6728 raw6728Labels = mixedMoment B node3044 node3044Labels := by
  calc
    mixedMoment B raw6728 raw6728Labels = mixedMoment B raw6728step0 raw6728step0Labels := by
      have hz : ∀ j, raw6728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6728step0 = (fun i j => raw6728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6728step0 raw6728; decide +kernel
      have hl : raw6728step0Labels = raw6728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6728 raw6728Labels permutation346 hz
    mixedMoment B raw6728step0 raw6728step0Labels = mixedMoment B raw6728step1 raw6728step1Labels := by
      have ha : raw6728step1 = (fun i j => raw6728step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6728step1 raw6728step0; decide +kernel
      have hl : raw6728step1Labels = raw6728step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6728step0 raw6728step0Labels permutation32 permutation6
    _ = mixedMoment B node3044 node3044Labels := by rfl

theorem canonical6729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6729 raw6729Labels = mixedMoment B node3068 node3068Labels := by
  calc
    mixedMoment B raw6729 raw6729Labels = mixedMoment B raw6729step0 raw6729step0Labels := by
      have ha : raw6729step0 = (fun i j => raw6729 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6729step0 raw6729; decide +kernel
      have hl : raw6729step0Labels = raw6729Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6729 raw6729Labels permutation152 permutation6
    _ = mixedMoment B node3068 node3068Labels := by rfl

theorem canonical6730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6730 raw6730Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw6730 raw6730Labels = mixedMoment B raw6730step0 raw6730step0Labels := by
      have hz : ∀ j, raw6730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6730step0 = (fun i j => raw6730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6730step0 raw6730; decide +kernel
      have hl : raw6730step0Labels = raw6730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6730 raw6730Labels permutation346 hz
    mixedMoment B raw6730step0 raw6730step0Labels = mixedMoment B raw6730step1 raw6730step1Labels := by
      have ha : raw6730step1 = (fun i j => raw6730step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6730step1 raw6730step0; decide +kernel
      have hl : raw6730step1Labels = raw6730step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6730step0 raw6730step0Labels permutation32 permutation6
    _ = mixedMoment B node3088 node3088Labels := by rfl

theorem canonical6731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6731 raw6731Labels = mixedMoment B node3092 node3092Labels := by
  calc
    mixedMoment B raw6731 raw6731Labels = mixedMoment B raw6731step0 raw6731step0Labels := by
      have hz : ∀ j, raw6731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6731step0 = (fun i j => raw6731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6731step0 raw6731; decide +kernel
      have hl : raw6731step0Labels = raw6731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6731 raw6731Labels permutation346 hz
    mixedMoment B raw6731step0 raw6731step0Labels = mixedMoment B raw6731step1 raw6731step1Labels := by
      have ha : raw6731step1 = (fun i j => raw6731step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6731step1 raw6731step0; decide +kernel
      have hl : raw6731step1Labels = raw6731step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6731step0 raw6731step0Labels permutation32 permutation6
    _ = mixedMoment B node3092 node3092Labels := by rfl

theorem canonical6732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6732 raw6732Labels = mixedMoment B node3094 node3094Labels := by
  calc
    mixedMoment B raw6732 raw6732Labels = mixedMoment B raw6732step0 raw6732step0Labels := by
      have hz : ∀ j, raw6732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6732step0 = (fun i j => raw6732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6732step0 raw6732; decide +kernel
      have hl : raw6732step0Labels = raw6732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6732 raw6732Labels permutation346 hz
    mixedMoment B raw6732step0 raw6732step0Labels = mixedMoment B raw6732step1 raw6732step1Labels := by
      have ha : raw6732step1 = (fun i j => raw6732step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6732step1 raw6732step0; decide +kernel
      have hl : raw6732step1Labels = raw6732step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6732step0 raw6732step0Labels permutation32 permutation6
    _ = mixedMoment B node3094 node3094Labels := by rfl

theorem canonical6733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6733 raw6733Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw6733 raw6733Labels = mixedMoment B raw6733step0 raw6733step0Labels := by
      have hz : ∀ j, raw6733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6733step0 = (fun i j => raw6733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6733step0 raw6733; decide +kernel
      have hl : raw6733step0Labels = raw6733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6733 raw6733Labels permutation346 hz
    mixedMoment B raw6733step0 raw6733step0Labels = mixedMoment B raw6733step1 raw6733step1Labels := by
      have hz : ∀ j, raw6733step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6733step1 = (fun i j => raw6733step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6733step1 raw6733step0; decide +kernel
      have hl : raw6733step1Labels = raw6733step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6733step0 raw6733step0Labels permutation56 hz
    mixedMoment B raw6733step1 raw6733step1Labels = mixedMoment B raw6733step2 raw6733step2Labels := by
      have ha : raw6733step2 = (fun i j => raw6733step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6733step2 raw6733step1; decide +kernel
      have hl : raw6733step2Labels = raw6733step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6733step1 raw6733step1Labels permutation8 permutation6
    _ = mixedMoment B node2278 node2278Labels := by rfl

theorem canonical6734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6734 raw6734Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw6734 raw6734Labels = mixedMoment B raw6734step0 raw6734step0Labels := by
      have hz : ∀ j, raw6734 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw6734step0 = (fun i j => raw6734 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw6734step0 raw6734; decide +kernel
      have hl : raw6734step0Labels = raw6734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6734 raw6734Labels permutation265 hz
    mixedMoment B raw6734step0 raw6734step0Labels = mixedMoment B raw6734step1 raw6734step1Labels := by
      have ha : raw6734step1 = (fun i j => raw6734step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6734step1 raw6734step0; decide +kernel
      have hl : raw6734step1Labels = raw6734step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6734step0 raw6734step0Labels permutation32 permutation6
    _ = mixedMoment B node2731 node2731Labels := by rfl

theorem canonical6735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6735 raw6735Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw6735 raw6735Labels = mixedMoment B raw6735step0 raw6735step0Labels := by
      have hz : ∀ j, raw6735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6735step0 = (fun i j => raw6735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6735step0 raw6735; decide +kernel
      have hl : raw6735step0Labels = raw6735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6735 raw6735Labels permutation346 hz
    mixedMoment B raw6735step0 raw6735step0Labels = mixedMoment B raw6735step1 raw6735step1Labels := by
      have hz : ∀ j, raw6735step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6735step1 = (fun i j => raw6735step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6735step1 raw6735step0; decide +kernel
      have hl : raw6735step1Labels = raw6735step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6735step0 raw6735step0Labels permutation56 hz
    mixedMoment B raw6735step1 raw6735step1Labels = mixedMoment B raw6735step2 raw6735step2Labels := by
      have ha : raw6735step2 = (fun i j => raw6735step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6735step2 raw6735step1; decide +kernel
      have hl : raw6735step2Labels = raw6735step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6735step1 raw6735step1Labels permutation8 permutation6
    _ = mixedMoment B node2767 node2767Labels := by rfl

theorem canonical6736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6736 raw6736Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw6736 raw6736Labels = mixedMoment B raw6736step0 raw6736step0Labels := by
      have hz : ∀ j, raw6736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6736step0 = (fun i j => raw6736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6736step0 raw6736; decide +kernel
      have hl : raw6736step0Labels = raw6736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6736 raw6736Labels permutation346 hz
    mixedMoment B raw6736step0 raw6736step0Labels = mixedMoment B raw6736step1 raw6736step1Labels := by
      have hz : ∀ j, raw6736step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6736step1 = (fun i j => raw6736step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6736step1 raw6736step0; decide +kernel
      have hl : raw6736step1Labels = raw6736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6736step0 raw6736step0Labels permutation56 hz
    mixedMoment B raw6736step1 raw6736step1Labels = mixedMoment B raw6736step2 raw6736step2Labels := by
      have ha : raw6736step2 = (fun i j => raw6736step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6736step2 raw6736step1; decide +kernel
      have hl : raw6736step2Labels = raw6736step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6736step1 raw6736step1Labels permutation8 permutation6
    _ = mixedMoment B node2774 node2774Labels := by rfl

theorem canonical6737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6737 raw6737Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw6737 raw6737Labels = mixedMoment B raw6737step0 raw6737step0Labels := by
      have hz : ∀ j, raw6737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6737step0 = (fun i j => raw6737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6737step0 raw6737; decide +kernel
      have hl : raw6737step0Labels = raw6737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6737 raw6737Labels permutation346 hz
    mixedMoment B raw6737step0 raw6737step0Labels = mixedMoment B raw6737step1 raw6737step1Labels := by
      have hz : ∀ j, raw6737step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6737step1 = (fun i j => raw6737step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6737step1 raw6737step0; decide +kernel
      have hl : raw6737step1Labels = raw6737step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6737step0 raw6737step0Labels permutation56 hz
    mixedMoment B raw6737step1 raw6737step1Labels = mixedMoment B raw6737step2 raw6737step2Labels := by
      have ha : raw6737step2 = (fun i j => raw6737step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6737step2 raw6737step1; decide +kernel
      have hl : raw6737step2Labels = raw6737step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6737step1 raw6737step1Labels permutation8 permutation6
    _ = mixedMoment B node2776 node2776Labels := by rfl

theorem canonical6738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6738 raw6738Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw6738 raw6738Labels = mixedMoment B raw6738step0 raw6738step0Labels := by
      have ha : raw6738step0 = (fun i j => raw6738 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6738step0 raw6738; decide +kernel
      have hl : raw6738step0Labels = raw6738Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6738 raw6738Labels permutation152 permutation6
    _ = mixedMoment B node2195 node2195Labels := by rfl

theorem canonical6739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6739 raw6739Labels = mixedMoment B node2665 node2665Labels := by
  calc
    mixedMoment B raw6739 raw6739Labels = mixedMoment B raw6739step0 raw6739step0Labels := by
      have ha : raw6739step0 = (fun i j => raw6739 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6739step0 raw6739; decide +kernel
      have hl : raw6739step0Labels = raw6739Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6739 raw6739Labels permutation152 permutation6
    _ = mixedMoment B node2665 node2665Labels := by rfl

theorem canonical6740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6740 raw6740Labels = mixedMoment B node2709 node2709Labels := by
  calc
    mixedMoment B raw6740 raw6740Labels = mixedMoment B raw6740step0 raw6740step0Labels := by
      have ha : raw6740step0 = (fun i j => raw6740 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6740step0 raw6740; decide +kernel
      have hl : raw6740step0Labels = raw6740Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6740 raw6740Labels permutation152 permutation6
    _ = mixedMoment B node2709 node2709Labels := by rfl

theorem canonical6741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6741 raw6741Labels = mixedMoment B node2713 node2713Labels := by
  calc
    mixedMoment B raw6741 raw6741Labels = mixedMoment B raw6741step0 raw6741step0Labels := by
      have ha : raw6741step0 = (fun i j => raw6741 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6741step0 raw6741; decide +kernel
      have hl : raw6741step0Labels = raw6741Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6741 raw6741Labels permutation152 permutation6
    _ = mixedMoment B node2713 node2713Labels := by rfl

theorem canonical6742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6742 raw6742Labels = mixedMoment B node2714 node2714Labels := by
  calc
    mixedMoment B raw6742 raw6742Labels = mixedMoment B raw6742step0 raw6742step0Labels := by
      have ha : raw6742step0 = (fun i j => raw6742 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6742step0 raw6742; decide +kernel
      have hl : raw6742step0Labels = raw6742Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6742 raw6742Labels permutation152 permutation6
    _ = mixedMoment B node2714 node2714Labels := by rfl

theorem canonical6743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6743 raw6743Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw6743 raw6743Labels = mixedMoment B raw6743step0 raw6743step0Labels := by
      have hz : ∀ j, raw6743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6743step0 = (fun i j => raw6743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6743step0 raw6743; decide +kernel
      have hl : raw6743step0Labels = raw6743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6743 raw6743Labels permutation346 hz
    mixedMoment B raw6743step0 raw6743step0Labels = mixedMoment B raw6743step1 raw6743step1Labels := by
      have ha : raw6743step1 = (fun i j => raw6743step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6743step1 raw6743step0; decide +kernel
      have hl : raw6743step1Labels = raw6743step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6743step0 raw6743step0Labels permutation32 permutation6
    _ = mixedMoment B node2220 node2220Labels := by rfl

theorem canonical6744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6744 raw6744Labels = mixedMoment B node2128 node2128Labels := by
  calc
    mixedMoment B raw6744 raw6744Labels = mixedMoment B raw6744step0 raw6744step0Labels := by
      have hz : ∀ j, raw6744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6744step0 = (fun i j => raw6744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6744step0 raw6744; decide +kernel
      have hl : raw6744step0Labels = raw6744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6744 raw6744Labels permutation346 hz
    mixedMoment B raw6744step0 raw6744step0Labels = mixedMoment B raw6744step1 raw6744step1Labels := by
      have ha : raw6744step1 = (fun i j => raw6744step0 (permutation85 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6744step1 raw6744step0; decide +kernel
      have hl : raw6744step1Labels = raw6744step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6744step0 raw6744step0Labels permutation85 permutation3
    mixedMoment B raw6744step1 raw6744step1Labels = mixedMoment B raw6744step2 raw6744step2Labels := by
      have ha : raw6744step2 = -raw6744step1 := by apply Matrix.ext; change ∀ i j, raw6744step2 i j = -(raw6744step1 i j); unfold raw6744step2 raw6744step1; decide +kernel
      have hl : raw6744step2Labels = raw6744step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2128 node2128Labels := by rfl

theorem canonical6745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6745 raw6745Labels = mixedMoment B node2127 node2127Labels := by
  calc
    mixedMoment B raw6745 raw6745Labels = mixedMoment B raw6745step0 raw6745step0Labels := by
      have ha : raw6745step0 = (fun i j => raw6745 (permutation449 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6745step0 raw6745; decide +kernel
      have hl : raw6745step0Labels = raw6745Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6745 raw6745Labels permutation449 permutation3
    mixedMoment B raw6745step0 raw6745step0Labels = mixedMoment B raw6745step1 raw6745step1Labels := by
      have ha : raw6745step1 = -raw6745step0 := by apply Matrix.ext; change ∀ i j, raw6745step1 i j = -(raw6745step0 i j); unfold raw6745step1 raw6745step0; decide +kernel
      have hl : raw6745step1Labels = raw6745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2127 node2127Labels := by rfl

theorem canonical6746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6746 raw6746Labels = mixedMoment B node2129 node2129Labels := by
  calc
    mixedMoment B raw6746 raw6746Labels = mixedMoment B raw6746step0 raw6746step0Labels := by
      have hz : ∀ j, raw6746 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6746step0 = (fun i j => raw6746 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6746step0 raw6746; decide +kernel
      have hl : raw6746step0Labels = raw6746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6746 raw6746Labels permutation346 hz
    mixedMoment B raw6746step0 raw6746step0Labels = mixedMoment B raw6746step1 raw6746step1Labels := by
      have ha : raw6746step1 = (fun i j => raw6746step0 (permutation84 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6746step1 raw6746step0; decide +kernel
      have hl : raw6746step1Labels = raw6746step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6746step0 raw6746step0Labels permutation84 permutation3
    mixedMoment B raw6746step1 raw6746step1Labels = mixedMoment B raw6746step2 raw6746step2Labels := by
      have ha : raw6746step2 = -raw6746step1 := by apply Matrix.ext; change ∀ i j, raw6746step2 i j = -(raw6746step1 i j); unfold raw6746step2 raw6746step1; decide +kernel
      have hl : raw6746step2Labels = raw6746step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2129 node2129Labels := by rfl

theorem canonical6747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6747 raw6747Labels = mixedMoment B node2133 node2133Labels := by
  calc
    mixedMoment B raw6747 raw6747Labels = mixedMoment B raw6747step0 raw6747step0Labels := by
      have hz : ∀ j, raw6747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6747step0 = (fun i j => raw6747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6747step0 raw6747; decide +kernel
      have hl : raw6747step0Labels = raw6747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6747 raw6747Labels permutation346 hz
    mixedMoment B raw6747step0 raw6747step0Labels = mixedMoment B raw6747step1 raw6747step1Labels := by
      have ha : raw6747step1 = (fun i j => raw6747step0 (permutation82 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6747step1 raw6747step0; decide +kernel
      have hl : raw6747step1Labels = raw6747step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6747step0 raw6747step0Labels permutation82 permutation3
    mixedMoment B raw6747step1 raw6747step1Labels = mixedMoment B raw6747step2 raw6747step2Labels := by
      have ha : raw6747step2 = -raw6747step1 := by apply Matrix.ext; change ∀ i j, raw6747step2 i j = -(raw6747step1 i j); unfold raw6747step2 raw6747step1; decide +kernel
      have hl : raw6747step2Labels = raw6747step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2133 node2133Labels := by rfl

theorem canonical6748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6748 raw6748Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw6748 raw6748Labels = mixedMoment B raw6748step0 raw6748step0Labels := by
      have hz : ∀ j, raw6748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6748step0 = (fun i j => raw6748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6748step0 raw6748; decide +kernel
      have hl : raw6748step0Labels = raw6748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6748 raw6748Labels permutation346 hz
    mixedMoment B raw6748step0 raw6748step0Labels = mixedMoment B raw6748step1 raw6748step1Labels := by
      have ha : raw6748step1 = (fun i j => raw6748step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6748step1 raw6748step0; decide +kernel
      have hl : raw6748step1Labels = raw6748step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6748step0 raw6748step0Labels permutation32 permutation6
    _ = mixedMoment B node2216 node2216Labels := by rfl

theorem canonical6749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6749 raw6749Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw6749 raw6749Labels = mixedMoment B raw6749step0 raw6749step0Labels := by
      have hz : ∀ j, raw6749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6749step0 = (fun i j => raw6749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6749step0 raw6749; decide +kernel
      have hl : raw6749step0Labels = raw6749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6749 raw6749Labels permutation346 hz
    mixedMoment B raw6749step0 raw6749step0Labels = mixedMoment B raw6749step1 raw6749step1Labels := by
      have ha : raw6749step1 = (fun i j => raw6749step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6749step1 raw6749step0; decide +kernel
      have hl : raw6749step1Labels = raw6749step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6749step0 raw6749step0Labels permutation32 permutation6
    _ = mixedMoment B node2678 node2678Labels := by rfl

theorem canonical6750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6750 raw6750Labels = mixedMoment B node2698 node2698Labels := by
  calc
    mixedMoment B raw6750 raw6750Labels = mixedMoment B raw6750step0 raw6750step0Labels := by
      have ha : raw6750step0 = (fun i j => raw6750 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6750step0 raw6750; decide +kernel
      have hl : raw6750step0Labels = raw6750Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6750 raw6750Labels permutation152 permutation6
    _ = mixedMoment B node2698 node2698Labels := by rfl

theorem canonical6751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6751 raw6751Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw6751 raw6751Labels = mixedMoment B raw6751step0 raw6751step0Labels := by
      have hz : ∀ j, raw6751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6751step0 = (fun i j => raw6751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6751step0 raw6751; decide +kernel
      have hl : raw6751step0Labels = raw6751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6751 raw6751Labels permutation346 hz
    mixedMoment B raw6751step0 raw6751step0Labels = mixedMoment B raw6751step1 raw6751step1Labels := by
      have ha : raw6751step1 = (fun i j => raw6751step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6751step1 raw6751step0; decide +kernel
      have hl : raw6751step1Labels = raw6751step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6751step0 raw6751step0Labels permutation32 permutation6
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical6752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6752 raw6752Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw6752 raw6752Labels = mixedMoment B raw6752step0 raw6752step0Labels := by
      have hz : ∀ j, raw6752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6752step0 = (fun i j => raw6752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6752step0 raw6752; decide +kernel
      have hl : raw6752step0Labels = raw6752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6752 raw6752Labels permutation346 hz
    mixedMoment B raw6752step0 raw6752step0Labels = mixedMoment B raw6752step1 raw6752step1Labels := by
      have ha : raw6752step1 = (fun i j => raw6752step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6752step1 raw6752step0; decide +kernel
      have hl : raw6752step1Labels = raw6752step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6752step0 raw6752step0Labels permutation32 permutation6
    _ = mixedMoment B node2677 node2677Labels := by rfl

theorem canonical6753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6753 raw6753Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw6753 raw6753Labels = mixedMoment B raw6753step0 raw6753step0Labels := by
      have ha : raw6753step0 = (fun i j => raw6753 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6753step0 raw6753; decide +kernel
      have hl : raw6753step0Labels = raw6753Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6753 raw6753Labels permutation152 permutation6
    _ = mixedMoment B node2697 node2697Labels := by rfl

theorem canonical6754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6754 raw6754Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw6754 raw6754Labels = mixedMoment B raw6754step0 raw6754step0Labels := by
      have hz : ∀ j, raw6754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6754step0 = (fun i j => raw6754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6754step0 raw6754; decide +kernel
      have hl : raw6754step0Labels = raw6754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6754 raw6754Labels permutation346 hz
    mixedMoment B raw6754step0 raw6754step0Labels = mixedMoment B raw6754step1 raw6754step1Labels := by
      have ha : raw6754step1 = (fun i j => raw6754step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6754step1 raw6754step0; decide +kernel
      have hl : raw6754step1Labels = raw6754step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6754step0 raw6754step0Labels permutation32 permutation6
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical6755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6755 raw6755Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw6755 raw6755Labels = mixedMoment B raw6755step0 raw6755step0Labels := by
      have hz : ∀ j, raw6755 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6755step0 = (fun i j => raw6755 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6755step0 raw6755; decide +kernel
      have hl : raw6755step0Labels = raw6755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6755 raw6755Labels permutation346 hz
    mixedMoment B raw6755step0 raw6755step0Labels = mixedMoment B raw6755step1 raw6755step1Labels := by
      have ha : raw6755step1 = (fun i j => raw6755step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6755step1 raw6755step0; decide +kernel
      have hl : raw6755step1Labels = raw6755step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6755step0 raw6755step0Labels permutation32 permutation6
    _ = mixedMoment B node2729 node2729Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6784 raw6784Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw6784 raw6784Labels = mixedMoment B raw6784step0 raw6784step0Labels := by
      have hz : ∀ j, raw6784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6784step0 = (fun i j => raw6784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6784step0 raw6784; decide +kernel
      have hl : raw6784step0Labels = raw6784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6784 raw6784Labels permutation346 hz
    mixedMoment B raw6784step0 raw6784step0Labels = mixedMoment B raw6784step1 raw6784step1Labels := by
      have ha : raw6784step1 = (fun i j => raw6784step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6784step1 raw6784step0; decide +kernel
      have hl : raw6784step1Labels = raw6784step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6784step0 raw6784step0Labels permutation35 permutation4
    mixedMoment B raw6784step1 raw6784step1Labels = mixedMoment B raw6784step2 raw6784step2Labels := by
      have ha : raw6784step2 = -raw6784step1 := by apply Matrix.ext; change ∀ i j, raw6784step2 i j = -(raw6784step1 i j); unfold raw6784step2 raw6784step1; decide +kernel
      have hl : raw6784step2Labels = raw6784step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3535 node3535Labels := by rfl

theorem canonical6785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6785 raw6785Labels = mixedMoment B node3395 node3395Labels := by
  calc
    mixedMoment B raw6785 raw6785Labels = mixedMoment B raw6785step0 raw6785step0Labels := by
      have hz : ∀ j, raw6785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6785step0 = (fun i j => raw6785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6785step0 raw6785; decide +kernel
      have hl : raw6785step0Labels = raw6785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6785 raw6785Labels permutation346 hz
    mixedMoment B raw6785step0 raw6785step0Labels = mixedMoment B raw6785step1 raw6785step1Labels := by
      have ha : raw6785step1 = (fun i j => raw6785step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6785step1 raw6785step0; decide +kernel
      have hl : raw6785step1Labels = raw6785step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6785step0 raw6785step0Labels permutation41 permutation2
    mixedMoment B raw6785step1 raw6785step1Labels = mixedMoment B raw6785step2 raw6785step2Labels := by
      have ha : raw6785step2 = -raw6785step1 := by apply Matrix.ext; change ∀ i j, raw6785step2 i j = -(raw6785step1 i j); unfold raw6785step2 raw6785step1; decide +kernel
      have hl : raw6785step2Labels = raw6785step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3395 node3395Labels := by rfl

theorem canonical6786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6786 raw6786Labels = mixedMoment B node3388 node3388Labels := by
  calc
    mixedMoment B raw6786 raw6786Labels = mixedMoment B raw6786step0 raw6786step0Labels := by
      have ha : raw6786step0 = (fun i j => raw6786 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6786step0 raw6786; decide +kernel
      have hl : raw6786step0Labels = raw6786Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6786 raw6786Labels permutation200 permutation2
    mixedMoment B raw6786step0 raw6786step0Labels = mixedMoment B raw6786step1 raw6786step1Labels := by
      have ha : raw6786step1 = -raw6786step0 := by apply Matrix.ext; change ∀ i j, raw6786step1 i j = -(raw6786step0 i j); unfold raw6786step1 raw6786step0; decide +kernel
      have hl : raw6786step1Labels = raw6786step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3388 node3388Labels := by rfl

theorem canonical6787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6787 raw6787Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw6787 raw6787Labels = mixedMoment B raw6787step0 raw6787step0Labels := by
      have hz : ∀ j, raw6787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6787step0 = (fun i j => raw6787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6787step0 raw6787; decide +kernel
      have hl : raw6787step0Labels = raw6787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6787 raw6787Labels permutation346 hz
    mixedMoment B raw6787step0 raw6787step0Labels = mixedMoment B raw6787step1 raw6787step1Labels := by
      have ha : raw6787step1 = (fun i j => raw6787step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6787step1 raw6787step0; decide +kernel
      have hl : raw6787step1Labels = raw6787step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6787step0 raw6787step0Labels permutation38 permutation2
    mixedMoment B raw6787step1 raw6787step1Labels = mixedMoment B raw6787step2 raw6787step2Labels := by
      have ha : raw6787step2 = -raw6787step1 := by apply Matrix.ext; change ∀ i j, raw6787step2 i j = -(raw6787step1 i j); unfold raw6787step2 raw6787step1; decide +kernel
      have hl : raw6787step2Labels = raw6787step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical6788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6788 raw6788Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw6788 raw6788Labels = mixedMoment B raw6788step0 raw6788step0Labels := by
      have hz : ∀ j, raw6788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6788step0 = (fun i j => raw6788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6788step0 raw6788; decide +kernel
      have hl : raw6788step0Labels = raw6788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6788 raw6788Labels permutation346 hz
    mixedMoment B raw6788step0 raw6788step0Labels = mixedMoment B raw6788step1 raw6788step1Labels := by
      have ha : raw6788step1 = (fun i j => raw6788step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6788step1 raw6788step0; decide +kernel
      have hl : raw6788step1Labels = raw6788step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6788step0 raw6788step0Labels permutation39 permutation2
    mixedMoment B raw6788step1 raw6788step1Labels = mixedMoment B raw6788step2 raw6788step2Labels := by
      have ha : raw6788step2 = -raw6788step1 := by apply Matrix.ext; change ∀ i j, raw6788step2 i j = -(raw6788step1 i j); unfold raw6788step2 raw6788step1; decide +kernel
      have hl : raw6788step2Labels = raw6788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3392 node3392Labels := by rfl

theorem canonical6789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6789 raw6789Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw6789 raw6789Labels = mixedMoment B raw6789step0 raw6789step0Labels := by
      have hz : ∀ j, raw6789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6789step0 = (fun i j => raw6789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6789step0 raw6789; decide +kernel
      have hl : raw6789step0Labels = raw6789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6789 raw6789Labels permutation346 hz
    mixedMoment B raw6789step0 raw6789step0Labels = mixedMoment B raw6789step1 raw6789step1Labels := by
      have ha : raw6789step1 = (fun i j => raw6789step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6789step1 raw6789step0; decide +kernel
      have hl : raw6789step1Labels = raw6789step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6789step0 raw6789step0Labels permutation38 permutation2
    mixedMoment B raw6789step1 raw6789step1Labels = mixedMoment B raw6789step2 raw6789step2Labels := by
      have ha : raw6789step2 = -raw6789step1 := by apply Matrix.ext; change ∀ i j, raw6789step2 i j = -(raw6789step1 i j); unfold raw6789step2 raw6789step1; decide +kernel
      have hl : raw6789step2Labels = raw6789step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3391 node3391Labels := by rfl

theorem canonical6790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6790 raw6790Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw6790 raw6790Labels = mixedMoment B raw6790step0 raw6790step0Labels := by
      have hz : ∀ j, raw6790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6790step0 = (fun i j => raw6790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6790step0 raw6790; decide +kernel
      have hl : raw6790step0Labels = raw6790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6790 raw6790Labels permutation346 hz
    mixedMoment B raw6790step0 raw6790step0Labels = mixedMoment B raw6790step1 raw6790step1Labels := by
      have hz : ∀ j, raw6790step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6790step1 = (fun i j => raw6790step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6790step1 raw6790step0; decide +kernel
      have hl : raw6790step1Labels = raw6790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6790step0 raw6790step0Labels permutation56 hz
    mixedMoment B raw6790step1 raw6790step1Labels = mixedMoment B raw6790step2 raw6790step2Labels := by
      have ha : raw6790step2 = (fun i j => raw6790step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6790step2 raw6790step1; decide +kernel
      have hl : raw6790step2Labels = raw6790step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6790step1 raw6790step1Labels permutation11 permutation4
    mixedMoment B raw6790step2 raw6790step2Labels = mixedMoment B raw6790step3 raw6790step3Labels := by
      have ha : raw6790step3 = -raw6790step2 := by apply Matrix.ext; change ∀ i j, raw6790step3 i j = -(raw6790step2 i j); unfold raw6790step3 raw6790step2; decide +kernel
      have hl : raw6790step3Labels = raw6790step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical6791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6791 raw6791Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw6791 raw6791Labels = mixedMoment B raw6791step0 raw6791step0Labels := by
      have ha : raw6791step0 = (fun i j => raw6791 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6791step0 raw6791; decide +kernel
      have hl : raw6791step0Labels = raw6791Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6791 raw6791Labels permutation165 permutation4
    mixedMoment B raw6791step0 raw6791step0Labels = mixedMoment B raw6791step1 raw6791step1Labels := by
      have ha : raw6791step1 = -raw6791step0 := by apply Matrix.ext; change ∀ i j, raw6791step1 i j = -(raw6791step0 i j); unfold raw6791step1 raw6791step0; decide +kernel
      have hl : raw6791step1Labels = raw6791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2021 node2021Labels := by rfl

theorem canonical6792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6792 raw6792Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw6792 raw6792Labels = mixedMoment B raw6792step0 raw6792step0Labels := by
      have hz : ∀ j, raw6792 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6792step0 = (fun i j => raw6792 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6792step0 raw6792; decide +kernel
      have hl : raw6792step0Labels = raw6792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6792 raw6792Labels permutation346 hz
    mixedMoment B raw6792step0 raw6792step0Labels = mixedMoment B raw6792step1 raw6792step1Labels := by
      have ha : raw6792step1 = (fun i j => raw6792step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6792step1 raw6792step0; decide +kernel
      have hl : raw6792step1Labels = raw6792step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6792step0 raw6792step0Labels permutation35 permutation4
    mixedMoment B raw6792step1 raw6792step1Labels = mixedMoment B raw6792step2 raw6792step2Labels := by
      have ha : raw6792step2 = -raw6792step1 := by apply Matrix.ext; change ∀ i j, raw6792step2 i j = -(raw6792step1 i j); unfold raw6792step2 raw6792step1; decide +kernel
      have hl : raw6792step2Labels = raw6792step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2026 node2026Labels := by rfl

theorem canonical6793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6793 raw6793Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw6793 raw6793Labels = mixedMoment B raw6793step0 raw6793step0Labels := by
      have hz : ∀ j, raw6793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6793step0 = (fun i j => raw6793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6793step0 raw6793; decide +kernel
      have hl : raw6793step0Labels = raw6793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6793 raw6793Labels permutation346 hz
    mixedMoment B raw6793step0 raw6793step0Labels = mixedMoment B raw6793step1 raw6793step1Labels := by
      have ha : raw6793step1 = (fun i j => raw6793step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6793step1 raw6793step0; decide +kernel
      have hl : raw6793step1Labels = raw6793step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6793step0 raw6793step0Labels permutation35 permutation4
    mixedMoment B raw6793step1 raw6793step1Labels = mixedMoment B raw6793step2 raw6793step2Labels := by
      have ha : raw6793step2 = -raw6793step1 := by apply Matrix.ext; change ∀ i j, raw6793step2 i j = -(raw6793step1 i j); unfold raw6793step2 raw6793step1; decide +kernel
      have hl : raw6793step2Labels = raw6793step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2058 node2058Labels := by rfl

theorem canonical6794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6794 raw6794Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw6794 raw6794Labels = mixedMoment B raw6794step0 raw6794step0Labels := by
      have hz : ∀ j, raw6794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6794step0 = (fun i j => raw6794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6794step0 raw6794; decide +kernel
      have hl : raw6794step0Labels = raw6794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6794 raw6794Labels permutation346 hz
    mixedMoment B raw6794step0 raw6794step0Labels = mixedMoment B raw6794step1 raw6794step1Labels := by
      have ha : raw6794step1 = (fun i j => raw6794step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6794step1 raw6794step0; decide +kernel
      have hl : raw6794step1Labels = raw6794step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6794step0 raw6794step0Labels permutation34 permutation4
    mixedMoment B raw6794step1 raw6794step1Labels = mixedMoment B raw6794step2 raw6794step2Labels := by
      have ha : raw6794step2 = -raw6794step1 := by apply Matrix.ext; change ∀ i j, raw6794step2 i j = -(raw6794step1 i j); unfold raw6794step2 raw6794step1; decide +kernel
      have hl : raw6794step2Labels = raw6794step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2028 node2028Labels := by rfl

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

theorem canonical5215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5215 = injectiveMoment H raw5215step0 := by
      have hz : ∀ j, raw5215 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5215step0 = (fun i j => raw5215 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5215 permutation27 hz
    injectiveMoment H raw5215step0 = injectiveMoment H raw5215step1 := by
      have hz : ∀ j, raw5215step0 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw5215step1 = (fun i j => raw5215step0 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5215step0 permutation7 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical238
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7636 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7636 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7636 = injectiveMoment H raw7636step0 := by
      have heq : raw7636step0 = (fun i j => raw7636 (permutation15 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7636 permutation15 permutation1
    _ = injectiveMoment H node46 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical781 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw781 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw781 = injectiveMoment H raw781step0 := by
      have heq : raw781step0 = -raw781 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw781).symm
    injectiveMoment H raw781step0 = injectiveMoment H raw781step1 := by
      have heq : raw781step1 = (fun i j => raw781step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw781step0 permutation11 permutation8
    _ = injectiveMoment H node181 := by rfl

theorem canonical792 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw792 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw792 = injectiveMoment H raw792step0 := by
      have heq : raw792step0 = -raw792 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw792).symm
    injectiveMoment H raw792step0 = injectiveMoment H raw792step1 := by
      have heq : raw792step1 = (fun i j => raw792step0 (permutation12 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw792step0 permutation12 permutation8
    _ = injectiveMoment H node177 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7977 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7977 = injectiveMoment H raw7977step0 := by
      have heq : raw7977step0 = raw7977.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7977).symm
    injectiveMoment H raw7977step0 = injectiveMoment H raw7977step1 := by
      have heq : raw7977step1 = (fun i j => raw7977step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7977step0 permutation5 permutation2
    _ = injectiveMoment H node10 := by rfl

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

theorem canonical895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw895 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw895 = injectiveMoment H raw895step0 := by
      have hz : ∀ j, raw895 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw895step0 = (fun i j => raw895 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw895 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5458 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5458 = injectiveMoment H raw5458step0 := by
      have heq : raw5458step0 = raw5458.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5458).symm
    injectiveMoment H raw5458step0 = injectiveMoment H raw5458step1 := by
      have heq : raw5458step1 = (fun i j => raw5458step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5458step0 permutation6 permutation2
    _ = injectiveMoment H node10 := by rfl

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

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound37 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node37 = Sparse.eval value37 (momentVector H) := by
  have hc : momentVector H 13 = injectiveMoment H node37 := rfl
  simp [value37, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

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

theorem sound56 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node56 = Sparse.eval value56 (momentVector H) := by
  have heq : pivotMatrix56 = (fun u v => node56 (pivotPermutation56 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node56 = injectiveMoment H pivotMatrix56 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix56 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix56 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (0 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node56 + (injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value56, value10, value11, Sparse.eval] at hc ⊢
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

theorem sound63 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node63 = Sparse.eval value63 (momentVector H) := by
  have heq : pivotMatrix63 = (fun u v => node63.transpose (pivotPermutation63 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node63 = injectiveMoment H pivotMatrix63 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix63 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix63 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (0 : Fin 2) = raw5458 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5458 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (1 : Fin 2) = raw7977 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7977 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node63 + (injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value63, value10, Sparse.eval] at hc ⊢
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

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2849 = injectiveMoment H node37 := by
  rfl

theorem canonical2861 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2861 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw2861 = injectiveMoment H raw2861step0 := by
      have heq : raw2861step0 = raw2861.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2861).symm
    injectiveMoment H raw2861step0 = injectiveMoment H raw2861step1 := by
      have heq : raw2861step1 = (fun i j => raw2861step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2861step0 permutation6 permutation5
    _ = injectiveMoment H node63 := by rfl

theorem canonical2862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2862 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2862 = injectiveMoment H raw2862step0 := by
      have heq : raw2862step0 = (fun i j => raw2862 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2862 permutation3 permutation5
    _ = injectiveMoment H node56 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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

theorem sound177 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node177 = Sparse.eval value177 (momentVector H) := by
  have heq : pivotMatrix177 = (fun u v => node177 (pivotPermutation177 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node177 = injectiveMoment H pivotMatrix177 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix177 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix177 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix177 (0 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (0 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix177 (1 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (1 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix177 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node177 + (injectiveMoment H (mergeFirst pivotMatrix177 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix177 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix177 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value177, value36, value37, value41, Sparse.eval] at hc ⊢
  linarith

theorem sound181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node181 = Sparse.eval value181 (momentVector H) := by
  have heq : pivotMatrix181 = (fun u v => node181 (pivotPermutation181 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node181 = injectiveMoment H pivotMatrix181 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix181 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix181 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (0 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (1 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (2 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node181 + (injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value181, value56, value62, value63, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node404 node404Labels = Sparse.eval singlePairValue404 (familyPairVector B) := by
  have hp := single_label_three B hB node404
  have hl : node404Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node404 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 1) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node404 PairSemantics.raw5197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node404 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node404 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value181 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 4) = PairSemantics.raw781 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node404 PairSemantics.raw781; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical781 hH).trans (PairSemantics.sound181 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue404, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value65, PairSemantics.value181, Sparse.eval] at hp ⊢
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

theorem singlePair412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node412 node412Labels = Sparse.eval singlePairValue412 (familyPairVector B) := by
  have hp := single_label_three B hB node412
  have hl : node412Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node412 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 1) = PairSemantics.raw5215 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node412 PairSemantics.raw5215; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5215 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 2) = PairSemantics.raw7636 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node412 PairSemantics.raw7636; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7636 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node412 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value177 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 4) = PairSemantics.raw792 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node412 PairSemantics.raw792; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical792 hH).trans (PairSemantics.sound177 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue412, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value46, PairSemantics.value177, Sparse.eval] at hp ⊢
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

theorem singleton2767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2767 node2767Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node404 node404Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw270 singletonSmall2767
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2767) = raw270Labels := by decide +kernel
  rw [hl, canonical270 B hB] at h
  have hc0 : mixedMoment B raw270 (Fin.cases (0 : Fin 1) singletonSmall2767) =
      mixedMoment B node404 node404Labels := by
    have ha : raw270 = raw271 := by apply Matrix.ext; unfold raw270 raw271; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2767 = raw271Labels := by decide +kernel
    rw [ha, hj, canonical271 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton2776 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2776 node2776Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node412 node412Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw278 singletonSmall2776
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2776) = raw278Labels := by decide +kernel
  rw [hl, canonical278 B hB] at h
  have hc0 : mixedMoment B raw278 (Fin.cases (0 : Fin 1) singletonSmall2776) =
      mixedMoment B node412 node412Labels := by
    have ha : raw278 = raw279 := by apply Matrix.ext; unfold raw278 raw279; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2776 = raw279Labels := by decide +kernel
    rw [ha, hj, canonical279 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem sound1358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1358 node1358Labels = Sparse.eval nodeValue1358 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1358) = mixedMoment B node1358 node1358Labels := rfl
  simpa [nodeValue1358, Sparse.eval] using hc.symm

theorem sound1361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1361 node1361Labels = Sparse.eval nodeValue1361 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1361) = mixedMoment B node1361 node1361Labels := rfl
  simpa [nodeValue1361, Sparse.eval] using hc.symm

theorem sound1363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1363 node1363Labels = Sparse.eval nodeValue1363 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1363) = mixedMoment B node1363 node1363Labels := rfl
  simpa [nodeValue1363, Sparse.eval] using hc.symm

theorem sound1370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1370 node1370Labels = Sparse.eval nodeValue1370 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1370) = mixedMoment B node1370 node1370Labels := rfl
  simpa [nodeValue1370, Sparse.eval] using hc.symm

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

theorem sound1423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1423 node1423Labels = Sparse.eval nodeValue1423 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1423) = mixedMoment B node1423 node1423Labels := rfl
  simpa [nodeValue1423, Sparse.eval] using hc.symm

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

theorem sound2021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2021 node2021Labels = Sparse.eval nodeValue2021 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2021) = mixedMoment B node2021 node2021Labels := rfl
  simpa [nodeValue2021, Sparse.eval] using hc.symm

theorem sound2026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2026 node2026Labels = Sparse.eval nodeValue2026 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2026) = mixedMoment B node2026 node2026Labels := rfl
  simpa [nodeValue2026, Sparse.eval] using hc.symm

theorem sound2028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2028 node2028Labels = Sparse.eval nodeValue2028 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2028) = mixedMoment B node2028 node2028Labels := rfl
  simpa [nodeValue2028, Sparse.eval] using hc.symm

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

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

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

theorem sound2127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2127 node2127Labels = Sparse.eval nodeValue2127 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2127) = mixedMoment B node2127 node2127Labels := rfl
  simpa [nodeValue2127, Sparse.eval] using hc.symm

theorem sound2128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2128 node2128Labels = Sparse.eval nodeValue2128 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2128) = mixedMoment B node2128 node2128Labels := rfl
  simpa [nodeValue2128, Sparse.eval] using hc.symm

theorem sound2129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2129 node2129Labels = Sparse.eval nodeValue2129 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2129) = mixedMoment B node2129 node2129Labels := rfl
  simpa [nodeValue2129, Sparse.eval] using hc.symm

theorem sound2133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2133 node2133Labels = Sparse.eval nodeValue2133 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2133) = mixedMoment B node2133 node2133Labels := rfl
  simpa [nodeValue2133, Sparse.eval] using hc.symm

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

theorem sound2195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2195 node2195Labels = Sparse.eval nodeValue2195 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2195) = mixedMoment B node2195 node2195Labels := rfl
  simpa [nodeValue2195, Sparse.eval] using hc.symm

theorem sound2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2215 node2215Labels = Sparse.eval nodeValue2215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2215) = mixedMoment B node2215 node2215Labels := rfl
  simpa [nodeValue2215, Sparse.eval] using hc.symm

theorem sound2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2216 node2216Labels = Sparse.eval nodeValue2216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2216) = mixedMoment B node2216 node2216Labels := rfl
  simpa [nodeValue2216, Sparse.eval] using hc.symm

theorem sound2220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2220 node2220Labels = Sparse.eval nodeValue2220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2220) = mixedMoment B node2220 node2220Labels := rfl
  simpa [nodeValue2220, Sparse.eval] using hc.symm

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

theorem sound2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2266 node2266Labels = Sparse.eval nodeValue2266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2266) = mixedMoment B node2266 node2266Labels := rfl
  simpa [nodeValue2266, Sparse.eval] using hc.symm

theorem sound2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2278 node2278Labels = Sparse.eval nodeValue2278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2278) = mixedMoment B node2278 node2278Labels := rfl
  simpa [nodeValue2278, Sparse.eval] using hc.symm

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

theorem sound2625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2625 node2625Labels = Sparse.eval nodeValue2625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2625) = mixedMoment B node2625 node2625Labels := rfl
  simpa [nodeValue2625, Sparse.eval] using hc.symm

theorem sound2627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2627 node2627Labels = Sparse.eval nodeValue2627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2627) = mixedMoment B node2627 node2627Labels := rfl
  simpa [nodeValue2627, Sparse.eval] using hc.symm

theorem sound2641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2641 node2641Labels = Sparse.eval nodeValue2641 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2641) = mixedMoment B node2641 node2641Labels := rfl
  simpa [nodeValue2641, Sparse.eval] using hc.symm

theorem sound2665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2665 node2665Labels = Sparse.eval nodeValue2665 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2665) = mixedMoment B node2665 node2665Labels := rfl
  simpa [nodeValue2665, Sparse.eval] using hc.symm

theorem sound2677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2677 node2677Labels = Sparse.eval nodeValue2677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2677) = mixedMoment B node2677 node2677Labels := rfl
  simpa [nodeValue2677, Sparse.eval] using hc.symm

theorem sound2678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2678 node2678Labels = Sparse.eval nodeValue2678 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2678) = mixedMoment B node2678 node2678Labels := rfl
  simpa [nodeValue2678, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2709 node2709Labels = 0 := by
  exact mixedMoment_alpha B hF node2709 node2709Labels 1 permutation200
    (by decide +kernel)

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

theorem sound2697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2697 node2697Labels = Sparse.eval nodeValue2697 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2697) = mixedMoment B node2697 node2697Labels := rfl
  simpa [nodeValue2697, Sparse.eval] using hc.symm

theorem sound2698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2698 node2698Labels = Sparse.eval nodeValue2698 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2698) = mixedMoment B node2698 node2698Labels := rfl
  simpa [nodeValue2698, Sparse.eval] using hc.symm

theorem sound2709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2709 node2709Labels = Sparse.eval nodeValue2709 (mixedVector B) := by
  simpa only [nodeValue2709, Sparse.eval_nil] using zero2709 B _hB _hF

theorem sound2713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2713 node2713Labels = Sparse.eval nodeValue2713 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2713) = mixedMoment B node2713 node2713Labels := rfl
  simpa [nodeValue2713, Sparse.eval] using hc.symm

theorem sound2714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2714 node2714Labels = Sparse.eval nodeValue2714 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2714) = mixedMoment B node2714 node2714Labels := rfl
  simpa [nodeValue2714, Sparse.eval] using hc.symm

theorem sound2722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2722 node2722Labels = Sparse.eval nodeValue2722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2722) = mixedMoment B node2722 node2722Labels := rfl
  simpa [nodeValue2722, Sparse.eval] using hc.symm

theorem sound2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2723 node2723Labels = Sparse.eval nodeValue2723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2723) = mixedMoment B node2723 node2723Labels := rfl
  simpa [nodeValue2723, Sparse.eval] using hc.symm

theorem sound2729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2729 node2729Labels = Sparse.eval nodeValue2729 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2729) = mixedMoment B node2729 node2729Labels := rfl
  simpa [nodeValue2729, Sparse.eval] using hc.symm

theorem sound2731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2731 node2731Labels = Sparse.eval nodeValue2731 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2731) = mixedMoment B node2731 node2731Labels := rfl
  simpa [nodeValue2731, Sparse.eval] using hc.symm

theorem sound2732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2732 node2732Labels = Sparse.eval nodeValue2732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2732) = mixedMoment B node2732 node2732Labels := rfl
  simpa [nodeValue2732, Sparse.eval] using hc.symm

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

theorem sound404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node404 node404Labels = Sparse.eval nodeValue404 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue404 (familyPairVector B) := singlePair404 B _hB
    _ = _ := by
      norm_num [singlePairValue404, nodeValue404, Sparse.eval, mixedVector]
      ring

theorem sound412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node412 node412Labels = Sparse.eval nodeValue412 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue412 (familyPairVector B) := singlePair412 B _hB
    _ = _ := by
      norm_num [singlePairValue412, nodeValue412, Sparse.eval, mixedVector]
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

theorem sound2754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2754 node2754Labels = Sparse.eval nodeValue2754 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2754) = mixedMoment B node2754 node2754Labels := rfl
  simpa [nodeValue2754, Sparse.eval] using hc.symm

theorem sound2767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2767 node2767Labels = Sparse.eval nodeValue2767 (mixedVector B) := by
  have h := singleton2767 B _hB
  rw [sound404 B _hB _hF] at h
  norm_num [nodeValue2767, nodeValue404, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2774 node2774Labels = Sparse.eval nodeValue2774 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2774) = mixedMoment B node2774 node2774Labels := rfl
  simpa [nodeValue2774, Sparse.eval] using hc.symm

theorem sound2776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2776 node2776Labels = Sparse.eval nodeValue2776 (mixedVector B) := by
  have h := singleton2776 B _hB
  rw [sound412 B _hB _hF] at h
  norm_num [nodeValue2776, nodeValue412, Sparse.eval] at h ⊢
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

theorem sound2862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2862 node2862Labels = Sparse.eval nodeValue2862 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2862) = mixedMoment B node2862 node2862Labels := rfl
  simpa [nodeValue2862, Sparse.eval] using hc.symm

theorem sound2865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2865 node2865Labels = Sparse.eval nodeValue2865 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2865) = mixedMoment B node2865 node2865Labels := rfl
  simpa [nodeValue2865, Sparse.eval] using hc.symm

theorem sound2868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2868 node2868Labels = Sparse.eval nodeValue2868 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2868) = mixedMoment B node2868 node2868Labels := rfl
  simpa [nodeValue2868, Sparse.eval] using hc.symm

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

theorem sound2884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2884 node2884Labels = Sparse.eval nodeValue2884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2884) = mixedMoment B node2884 node2884Labels := rfl
  simpa [nodeValue2884, Sparse.eval] using hc.symm

theorem sound2918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2918 node2918Labels = Sparse.eval nodeValue2918 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2918) = mixedMoment B node2918 node2918Labels := rfl
  simpa [nodeValue2918, Sparse.eval] using hc.symm

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

theorem sound2946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2946 node2946Labels = Sparse.eval nodeValue2946 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2946) = mixedMoment B node2946 node2946Labels := rfl
  simpa [nodeValue2946, Sparse.eval] using hc.symm

theorem sound2972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2972 node2972Labels = Sparse.eval nodeValue2972 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2972) = mixedMoment B node2972 node2972Labels := rfl
  simpa [nodeValue2972, Sparse.eval] using hc.symm

theorem sound2976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2976 node2976Labels = Sparse.eval nodeValue2976 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2976) = mixedMoment B node2976 node2976Labels := rfl
  simpa [nodeValue2976, Sparse.eval] using hc.symm

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

theorem sound3008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3008 node3008Labels = Sparse.eval nodeValue3008 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3008) = mixedMoment B node3008 node3008Labels := rfl
  simpa [nodeValue3008, Sparse.eval] using hc.symm

theorem sound3011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3011 node3011Labels = Sparse.eval nodeValue3011 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3011) = mixedMoment B node3011 node3011Labels := rfl
  simpa [nodeValue3011, Sparse.eval] using hc.symm

theorem sound3029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3029 node3029Labels = Sparse.eval nodeValue3029 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3029) = mixedMoment B node3029 node3029Labels := rfl
  simpa [nodeValue3029, Sparse.eval] using hc.symm

theorem sound3031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3031 node3031Labels = Sparse.eval nodeValue3031 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3031) = mixedMoment B node3031 node3031Labels := rfl
  simpa [nodeValue3031, Sparse.eval] using hc.symm

theorem sound3037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3037 node3037Labels = Sparse.eval nodeValue3037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3037) = mixedMoment B node3037 node3037Labels := rfl
  simpa [nodeValue3037, Sparse.eval] using hc.symm

theorem sound3039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3039 node3039Labels = Sparse.eval nodeValue3039 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3039) = mixedMoment B node3039 node3039Labels := rfl
  simpa [nodeValue3039, Sparse.eval] using hc.symm

theorem sound3044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3044 node3044Labels = Sparse.eval nodeValue3044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3044) = mixedMoment B node3044 node3044Labels := rfl
  simpa [nodeValue3044, Sparse.eval] using hc.symm

theorem sound3053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3053 node3053Labels = Sparse.eval nodeValue3053 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3053) = mixedMoment B node3053 node3053Labels := rfl
  simpa [nodeValue3053, Sparse.eval] using hc.symm

theorem sound3068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3068 node3068Labels = Sparse.eval nodeValue3068 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3068) = mixedMoment B node3068 node3068Labels := rfl
  simpa [nodeValue3068, Sparse.eval] using hc.symm

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

theorem sound3092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3092 node3092Labels = Sparse.eval nodeValue3092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3092) = mixedMoment B node3092 node3092Labels := rfl
  simpa [nodeValue3092, Sparse.eval] using hc.symm

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

theorem sound3388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3388 node3388Labels = Sparse.eval nodeValue3388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3388) = mixedMoment B node3388 node3388Labels := rfl
  simpa [nodeValue3388, Sparse.eval] using hc.symm

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

theorem sound3392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3392 node3392Labels = Sparse.eval nodeValue3392 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3392) = mixedMoment B node3392 node3392Labels := rfl
  simpa [nodeValue3392, Sparse.eval] using hc.symm

theorem sound3395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3395 node3395Labels = Sparse.eval nodeValue3395 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3395) = mixedMoment B node3395 node3395Labels := rfl
  simpa [nodeValue3395, Sparse.eval] using hc.symm

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

theorem sound3535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3535 node3535Labels = Sparse.eval nodeValue3535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3535) = mixedMoment B node3535 node3535Labels := rfl
  simpa [nodeValue3535, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

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

theorem sound3880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3880 node3880Labels = Sparse.eval nodeValue3880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3880) = mixedMoment B node3880 node3880Labels := rfl
  simpa [nodeValue3880, Sparse.eval] using hc.symm

theorem sound3881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3881 node3881Labels = Sparse.eval nodeValue3881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3881) = mixedMoment B node3881 node3881Labels := rfl
  simpa [nodeValue3881, Sparse.eval] using hc.symm

theorem sound3885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3885 node3885Labels = Sparse.eval nodeValue3885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3885) = mixedMoment B node3885 node3885Labels := rfl
  simpa [nodeValue3885, Sparse.eval] using hc.symm

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

theorem sound3910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3910 node3910Labels = Sparse.eval nodeValue3910 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3910) = mixedMoment B node3910 node3910Labels := rfl
  simpa [nodeValue3910, Sparse.eval] using hc.symm

theorem sound3958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3958 node3958Labels = Sparse.eval nodeValue3958 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3958) = mixedMoment B node3958 node3958Labels := rfl
  simpa [nodeValue3958, Sparse.eval] using hc.symm

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

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources10
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq320 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm320 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA320 + difference 0 0) (sourceB320 + difference 0 0) sourceC320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA320 + difference 0 0) (sourceB320 + difference 0 0) sourceC320) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA320 sourceB320 sourceC320 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA320 + difference 1 0) (sourceB320 + difference 0 1) sourceC320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA320 + difference 1 0) (sourceB320 + difference 0 1) sourceC320) = raw6790 := by
      apply Matrix.ext; unfold tripleCharges sourceA320 sourceB320 sourceC320 difference raw6790; decide +kernel
    rw [ha]
    exact (canonical6790 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA320 + difference 2 0) (sourceB320 + difference 0 2) sourceC320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA320 + difference 2 0) (sourceB320 + difference 0 2) sourceC320) = raw6791 := by
      apply Matrix.ext; unfold tripleCharges sourceA320 sourceB320 sourceC320 difference raw6791; decide +kernel
    rw [ha]
    exact (canonical6791 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA320 + difference 3 0) (sourceB320 + difference 0 3) sourceC320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA320 + difference 3 0) (sourceB320 + difference 0 3) sourceC320) = raw6792 := by
      apply Matrix.ext; unfold tripleCharges sourceA320 sourceB320 sourceC320 difference raw6792; decide +kernel
    rw [ha]
    exact (canonical6792 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA320 + difference 4 0) (sourceB320 + difference 0 4) sourceC320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA320 + difference 4 0) (sourceB320 + difference 0 4) sourceC320) = raw6793 := by
      apply Matrix.ext; unfold tripleCharges sourceA320 sourceB320 sourceC320 difference raw6793; decide +kernel
    rw [ha]
    exact (canonical6793 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA320 + difference 5 0) (sourceB320 + difference 0 5) sourceC320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA320 + difference 5 0) (sourceB320 + difference 0 5) sourceC320) = raw6794 := by
      apply Matrix.ext; unfold tripleCharges sourceA320 sourceB320 sourceC320 difference raw6794; decide +kernel
    rw [ha]
    exact (canonical6794 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA320 + sourceB320) sourceC320) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA320 + sourceB320) sourceC320) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA320 sourceB320 sourceC320 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA320 sourceB320 sourceC320
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm320, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources9
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq305 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm305 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA305 + difference 0 0) (sourceB305 + difference 0 0) sourceC305) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA305 + difference 0 0) (sourceB305 + difference 0 0) sourceC305) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA305 sourceB305 sourceC305 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA305 + difference 0 1) (sourceB305 + difference 1 0) sourceC305) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA305 + difference 0 1) (sourceB305 + difference 1 0) sourceC305) = raw6669 := by
      apply Matrix.ext; unfold tripleCharges sourceA305 sourceB305 sourceC305 difference raw6669; decide +kernel
    rw [ha]
    exact (canonical6669 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA305 + difference 0 2) (sourceB305 + difference 2 0) sourceC305) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA305 + difference 0 2) (sourceB305 + difference 2 0) sourceC305) = raw6670 := by
      apply Matrix.ext; unfold tripleCharges sourceA305 sourceB305 sourceC305 difference raw6670; decide +kernel
    rw [ha]
    exact (canonical6670 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA305 + difference 0 3) (sourceB305 + difference 3 0) sourceC305) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA305 + difference 0 3) (sourceB305 + difference 3 0) sourceC305) = raw6671 := by
      apply Matrix.ext; unfold tripleCharges sourceA305 sourceB305 sourceC305 difference raw6671; decide +kernel
    rw [ha]
    exact (canonical6671 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA305 + difference 0 4) (sourceB305 + difference 4 0) sourceC305) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA305 + difference 0 4) (sourceB305 + difference 4 0) sourceC305) = raw6672 := by
      apply Matrix.ext; unfold tripleCharges sourceA305 sourceB305 sourceC305 difference raw6672; decide +kernel
    rw [ha]
    exact (canonical6672 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA305 + difference 0 5) (sourceB305 + difference 5 0) sourceC305) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA305 + difference 0 5) (sourceB305 + difference 5 0) sourceC305) = raw6673 := by
      apply Matrix.ext; unfold tripleCharges sourceA305 sourceB305 sourceC305 difference raw6673; decide +kernel
    rw [ha]
    exact (canonical6673 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA305 + sourceB305) sourceC305) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA305 + sourceB305) sourceC305) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA305 sourceB305 sourceC305 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA305 sourceB305 sourceC305
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm305, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq306 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm306 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA306 + difference 0 0) (sourceB306 + difference 0 0) sourceC306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA306 + difference 0 0) (sourceB306 + difference 0 0) sourceC306) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA306 sourceB306 sourceC306 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA306 + difference 1 0) (sourceB306 + difference 0 1) sourceC306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1370) := by
    have ha : (tripleCharges (sourceA306 + difference 1 0) (sourceB306 + difference 0 1) sourceC306) = raw6675 := by
      apply Matrix.ext; unfold tripleCharges sourceA306 sourceB306 sourceC306 difference raw6675; decide +kernel
    rw [ha]
    exact (canonical6675 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA306 + difference 2 0) (sourceB306 + difference 0 2) sourceC306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1358) := by
    have ha : (tripleCharges (sourceA306 + difference 2 0) (sourceB306 + difference 0 2) sourceC306) = raw6676 := by
      apply Matrix.ext; unfold tripleCharges sourceA306 sourceB306 sourceC306 difference raw6676; decide +kernel
    rw [ha]
    exact (canonical6676 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA306 + difference 3 0) (sourceB306 + difference 0 3) sourceC306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1423) := by
    have ha : (tripleCharges (sourceA306 + difference 3 0) (sourceB306 + difference 0 3) sourceC306) = raw6677 := by
      apply Matrix.ext; unfold tripleCharges sourceA306 sourceB306 sourceC306 difference raw6677; decide +kernel
    rw [ha]
    exact (canonical6677 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA306 + difference 4 0) (sourceB306 + difference 0 4) sourceC306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1363) := by
    have ha : (tripleCharges (sourceA306 + difference 4 0) (sourceB306 + difference 0 4) sourceC306) = raw6678 := by
      apply Matrix.ext; unfold tripleCharges sourceA306 sourceB306 sourceC306 difference raw6678; decide +kernel
    rw [ha]
    exact (canonical6678 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA306 + difference 5 0) (sourceB306 + difference 0 5) sourceC306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1361) := by
    have ha : (tripleCharges (sourceA306 + difference 5 0) (sourceB306 + difference 0 5) sourceC306) = raw6679 := by
      apply Matrix.ext; unfold tripleCharges sourceA306 sourceB306 sourceC306 difference raw6679; decide +kernel
    rw [ha]
    exact (canonical6679 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA306 + sourceB306) sourceC306) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA306 + sourceB306) sourceC306) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA306 sourceB306 sourceC306 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA306 sourceB306 sourceC306
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm306, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm307 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA307 + difference 1 0) (sourceB307 + difference 0 1) sourceC307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1370) := by
    have ha : (tripleCharges (sourceA307 + difference 1 0) (sourceB307 + difference 0 1) sourceC307) = raw6675 := by
      apply Matrix.ext; unfold tripleCharges sourceA307 sourceB307 sourceC307 difference raw6675; decide +kernel
    rw [ha]
    exact (canonical6675 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA307 + difference 1 1) (sourceB307 + difference 1 1) sourceC307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA307 + difference 1 1) (sourceB307 + difference 1 1) sourceC307) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA307 sourceB307 sourceC307 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA307 + difference 1 2) (sourceB307 + difference 2 1) sourceC307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA307 + difference 1 2) (sourceB307 + difference 2 1) sourceC307) = raw6680 := by
      apply Matrix.ext; unfold tripleCharges sourceA307 sourceB307 sourceC307 difference raw6680; decide +kernel
    rw [ha]
    exact (canonical6680 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA307 + difference 1 3) (sourceB307 + difference 3 1) sourceC307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA307 + difference 1 3) (sourceB307 + difference 3 1) sourceC307) = raw6681 := by
      apply Matrix.ext; unfold tripleCharges sourceA307 sourceB307 sourceC307 difference raw6681; decide +kernel
    rw [ha]
    exact (canonical6681 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA307 + difference 1 4) (sourceB307 + difference 4 1) sourceC307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA307 + difference 1 4) (sourceB307 + difference 4 1) sourceC307) = raw6682 := by
      apply Matrix.ext; unfold tripleCharges sourceA307 sourceB307 sourceC307 difference raw6682; decide +kernel
    rw [ha]
    exact (canonical6682 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA307 + difference 1 5) (sourceB307 + difference 5 1) sourceC307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA307 + difference 1 5) (sourceB307 + difference 5 1) sourceC307) = raw6683 := by
      apply Matrix.ext; unfold tripleCharges sourceA307 sourceB307 sourceC307 difference raw6683; decide +kernel
    rw [ha]
    exact (canonical6683 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA307 + sourceB307) sourceC307) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA307 + sourceB307) sourceC307) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA307 sourceB307 sourceC307 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA307 sourceB307 sourceC307
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm307, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq308 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm308 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA308 + difference 0 1) (sourceB308 + difference 1 0) sourceC308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA308 + difference 0 1) (sourceB308 + difference 1 0) sourceC308) = raw6669 := by
      apply Matrix.ext; unfold tripleCharges sourceA308 sourceB308 sourceC308 difference raw6669; decide +kernel
    rw [ha]
    exact (canonical6669 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA308 + difference 1 1) (sourceB308 + difference 1 1) sourceC308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA308 + difference 1 1) (sourceB308 + difference 1 1) sourceC308) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA308 sourceB308 sourceC308 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA308 + difference 2 1) (sourceB308 + difference 1 2) sourceC308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3008) := by
    have ha : (tripleCharges (sourceA308 + difference 2 1) (sourceB308 + difference 1 2) sourceC308) = raw6684 := by
      apply Matrix.ext; unfold tripleCharges sourceA308 sourceB308 sourceC308 difference raw6684; decide +kernel
    rw [ha]
    exact (canonical6684 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA308 + difference 3 1) (sourceB308 + difference 1 3) sourceC308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2627) := by
    have ha : (tripleCharges (sourceA308 + difference 3 1) (sourceB308 + difference 1 3) sourceC308) = raw6685 := by
      apply Matrix.ext; unfold tripleCharges sourceA308 sourceB308 sourceC308 difference raw6685; decide +kernel
    rw [ha]
    exact (canonical6685 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA308 + difference 4 1) (sourceB308 + difference 1 4) sourceC308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3011) := by
    have ha : (tripleCharges (sourceA308 + difference 4 1) (sourceB308 + difference 1 4) sourceC308) = raw6686 := by
      apply Matrix.ext; unfold tripleCharges sourceA308 sourceB308 sourceC308 difference raw6686; decide +kernel
    rw [ha]
    exact (canonical6686 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA308 + difference 5 1) (sourceB308 + difference 1 5) sourceC308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2946) := by
    have ha : (tripleCharges (sourceA308 + difference 5 1) (sourceB308 + difference 1 5) sourceC308) = raw6687 := by
      apply Matrix.ext; unfold tripleCharges sourceA308 sourceB308 sourceC308 difference raw6687; decide +kernel
    rw [ha]
    exact (canonical6687 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA308 + sourceB308) sourceC308) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA308 + sourceB308) sourceC308) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA308 sourceB308 sourceC308 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA308 sourceB308 sourceC308
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm308, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq309 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm309 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA309 + difference 2 0) (sourceB309 + difference 0 2) sourceC309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1358) := by
    have ha : (tripleCharges (sourceA309 + difference 2 0) (sourceB309 + difference 0 2) sourceC309) = raw6676 := by
      apply Matrix.ext; unfold tripleCharges sourceA309 sourceB309 sourceC309 difference raw6676; decide +kernel
    rw [ha]
    exact (canonical6676 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA309 + difference 2 1) (sourceB309 + difference 1 2) sourceC309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3008) := by
    have ha : (tripleCharges (sourceA309 + difference 2 1) (sourceB309 + difference 1 2) sourceC309) = raw6684 := by
      apply Matrix.ext; unfold tripleCharges sourceA309 sourceB309 sourceC309 difference raw6684; decide +kernel
    rw [ha]
    exact (canonical6684 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA309 + difference 2 2) (sourceB309 + difference 2 2) sourceC309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA309 + difference 2 2) (sourceB309 + difference 2 2) sourceC309) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA309 sourceB309 sourceC309 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA309 + difference 2 3) (sourceB309 + difference 3 2) sourceC309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA309 + difference 2 3) (sourceB309 + difference 3 2) sourceC309) = raw6688 := by
      apply Matrix.ext; unfold tripleCharges sourceA309 sourceB309 sourceC309 difference raw6688; decide +kernel
    rw [ha]
    exact (canonical6688 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA309 + difference 2 4) (sourceB309 + difference 4 2) sourceC309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3029) := by
    have ha : (tripleCharges (sourceA309 + difference 2 4) (sourceB309 + difference 4 2) sourceC309) = raw6689 := by
      apply Matrix.ext; unfold tripleCharges sourceA309 sourceB309 sourceC309 difference raw6689; decide +kernel
    rw [ha]
    exact (canonical6689 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA309 + difference 2 5) (sourceB309 + difference 5 2) sourceC309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA309 + difference 2 5) (sourceB309 + difference 5 2) sourceC309) = raw6690 := by
      apply Matrix.ext; unfold tripleCharges sourceA309 sourceB309 sourceC309 difference raw6690; decide +kernel
    rw [ha]
    exact (canonical6690 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA309 + sourceB309) sourceC309) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA309 + sourceB309) sourceC309) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA309 sourceB309 sourceC309 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA309 sourceB309 sourceC309
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm309, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm310 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA310 + difference 0 2) (sourceB310 + difference 2 0) sourceC310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA310 + difference 0 2) (sourceB310 + difference 2 0) sourceC310) = raw6670 := by
      apply Matrix.ext; unfold tripleCharges sourceA310 sourceB310 sourceC310 difference raw6670; decide +kernel
    rw [ha]
    exact (canonical6670 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA310 + difference 1 2) (sourceB310 + difference 2 1) sourceC310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA310 + difference 1 2) (sourceB310 + difference 2 1) sourceC310) = raw6680 := by
      apply Matrix.ext; unfold tripleCharges sourceA310 sourceB310 sourceC310 difference raw6680; decide +kernel
    rw [ha]
    exact (canonical6680 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA310 + difference 2 2) (sourceB310 + difference 2 2) sourceC310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA310 + difference 2 2) (sourceB310 + difference 2 2) sourceC310) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA310 sourceB310 sourceC310 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA310 + difference 3 2) (sourceB310 + difference 2 3) sourceC310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2625) := by
    have ha : (tripleCharges (sourceA310 + difference 3 2) (sourceB310 + difference 2 3) sourceC310) = raw6691 := by
      apply Matrix.ext; unfold tripleCharges sourceA310 sourceB310 sourceC310 difference raw6691; decide +kernel
    rw [ha]
    exact (canonical6691 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA310 + difference 4 2) (sourceB310 + difference 2 4) sourceC310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2972) := by
    have ha : (tripleCharges (sourceA310 + difference 4 2) (sourceB310 + difference 2 4) sourceC310) = raw6692 := by
      apply Matrix.ext; unfold tripleCharges sourceA310 sourceB310 sourceC310 difference raw6692; decide +kernel
    rw [ha]
    exact (canonical6692 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA310 + difference 5 2) (sourceB310 + difference 2 5) sourceC310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2918) := by
    have ha : (tripleCharges (sourceA310 + difference 5 2) (sourceB310 + difference 2 5) sourceC310) = raw6693 := by
      apply Matrix.ext; unfold tripleCharges sourceA310 sourceB310 sourceC310 difference raw6693; decide +kernel
    rw [ha]
    exact (canonical6693 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA310 + sourceB310) sourceC310) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA310 + sourceB310) sourceC310) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA310 sourceB310 sourceC310 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA310 sourceB310 sourceC310
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm310, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq311 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm311 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA311 + difference 3 0) (sourceB311 + difference 0 3) sourceC311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1423) := by
    have ha : (tripleCharges (sourceA311 + difference 3 0) (sourceB311 + difference 0 3) sourceC311) = raw6677 := by
      apply Matrix.ext; unfold tripleCharges sourceA311 sourceB311 sourceC311 difference raw6677; decide +kernel
    rw [ha]
    exact (canonical6677 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA311 + difference 3 1) (sourceB311 + difference 1 3) sourceC311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2627) := by
    have ha : (tripleCharges (sourceA311 + difference 3 1) (sourceB311 + difference 1 3) sourceC311) = raw6685 := by
      apply Matrix.ext; unfold tripleCharges sourceA311 sourceB311 sourceC311 difference raw6685; decide +kernel
    rw [ha]
    exact (canonical6685 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA311 + difference 3 2) (sourceB311 + difference 2 3) sourceC311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2625) := by
    have ha : (tripleCharges (sourceA311 + difference 3 2) (sourceB311 + difference 2 3) sourceC311) = raw6691 := by
      apply Matrix.ext; unfold tripleCharges sourceA311 sourceB311 sourceC311 difference raw6691; decide +kernel
    rw [ha]
    exact (canonical6691 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA311 + difference 3 3) (sourceB311 + difference 3 3) sourceC311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA311 + difference 3 3) (sourceB311 + difference 3 3) sourceC311) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA311 sourceB311 sourceC311 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA311 + difference 3 4) (sourceB311 + difference 4 3) sourceC311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2641) := by
    have ha : (tripleCharges (sourceA311 + difference 3 4) (sourceB311 + difference 4 3) sourceC311) = raw6694 := by
      apply Matrix.ext; unfold tripleCharges sourceA311 sourceB311 sourceC311 difference raw6694; decide +kernel
    rw [ha]
    exact (canonical6694 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA311 + difference 3 5) (sourceB311 + difference 5 3) sourceC311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA311 + difference 3 5) (sourceB311 + difference 5 3) sourceC311) = raw6695 := by
      apply Matrix.ext; unfold tripleCharges sourceA311 sourceB311 sourceC311 difference raw6695; decide +kernel
    rw [ha]
    exact (canonical6695 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA311 + sourceB311) sourceC311) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA311 + sourceB311) sourceC311) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA311 sourceB311 sourceC311 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA311 sourceB311 sourceC311
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm311, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq312 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm312 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA312 + difference 0 3) (sourceB312 + difference 3 0) sourceC312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA312 + difference 0 3) (sourceB312 + difference 3 0) sourceC312) = raw6671 := by
      apply Matrix.ext; unfold tripleCharges sourceA312 sourceB312 sourceC312 difference raw6671; decide +kernel
    rw [ha]
    exact (canonical6671 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA312 + difference 1 3) (sourceB312 + difference 3 1) sourceC312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA312 + difference 1 3) (sourceB312 + difference 3 1) sourceC312) = raw6681 := by
      apply Matrix.ext; unfold tripleCharges sourceA312 sourceB312 sourceC312 difference raw6681; decide +kernel
    rw [ha]
    exact (canonical6681 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA312 + difference 2 3) (sourceB312 + difference 3 2) sourceC312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA312 + difference 2 3) (sourceB312 + difference 3 2) sourceC312) = raw6688 := by
      apply Matrix.ext; unfold tripleCharges sourceA312 sourceB312 sourceC312 difference raw6688; decide +kernel
    rw [ha]
    exact (canonical6688 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA312 + difference 3 3) (sourceB312 + difference 3 3) sourceC312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA312 + difference 3 3) (sourceB312 + difference 3 3) sourceC312) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA312 sourceB312 sourceC312 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA312 + difference 4 3) (sourceB312 + difference 3 4) sourceC312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2868) := by
    have ha : (tripleCharges (sourceA312 + difference 4 3) (sourceB312 + difference 3 4) sourceC312) = raw6696 := by
      apply Matrix.ext; unfold tripleCharges sourceA312 sourceB312 sourceC312 difference raw6696; decide +kernel
    rw [ha]
    exact (canonical6696 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA312 + difference 5 3) (sourceB312 + difference 3 5) sourceC312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA312 + difference 5 3) (sourceB312 + difference 3 5) sourceC312) = raw6697 := by
      apply Matrix.ext; unfold tripleCharges sourceA312 sourceB312 sourceC312 difference raw6697; decide +kernel
    rw [ha]
    exact (canonical6697 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA312 + sourceB312) sourceC312) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA312 + sourceB312) sourceC312) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA312 sourceB312 sourceC312 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA312 sourceB312 sourceC312
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm312, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq313 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm313 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA313 + difference 4 0) (sourceB313 + difference 0 4) sourceC313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1363) := by
    have ha : (tripleCharges (sourceA313 + difference 4 0) (sourceB313 + difference 0 4) sourceC313) = raw6678 := by
      apply Matrix.ext; unfold tripleCharges sourceA313 sourceB313 sourceC313 difference raw6678; decide +kernel
    rw [ha]
    exact (canonical6678 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA313 + difference 4 1) (sourceB313 + difference 1 4) sourceC313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3011) := by
    have ha : (tripleCharges (sourceA313 + difference 4 1) (sourceB313 + difference 1 4) sourceC313) = raw6686 := by
      apply Matrix.ext; unfold tripleCharges sourceA313 sourceB313 sourceC313 difference raw6686; decide +kernel
    rw [ha]
    exact (canonical6686 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA313 + difference 4 2) (sourceB313 + difference 2 4) sourceC313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2972) := by
    have ha : (tripleCharges (sourceA313 + difference 4 2) (sourceB313 + difference 2 4) sourceC313) = raw6692 := by
      apply Matrix.ext; unfold tripleCharges sourceA313 sourceB313 sourceC313 difference raw6692; decide +kernel
    rw [ha]
    exact (canonical6692 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA313 + difference 4 3) (sourceB313 + difference 3 4) sourceC313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2868) := by
    have ha : (tripleCharges (sourceA313 + difference 4 3) (sourceB313 + difference 3 4) sourceC313) = raw6696 := by
      apply Matrix.ext; unfold tripleCharges sourceA313 sourceB313 sourceC313 difference raw6696; decide +kernel
    rw [ha]
    exact (canonical6696 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA313 + difference 4 4) (sourceB313 + difference 4 4) sourceC313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA313 + difference 4 4) (sourceB313 + difference 4 4) sourceC313) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA313 sourceB313 sourceC313 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA313 + difference 4 5) (sourceB313 + difference 5 4) sourceC313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA313 + difference 4 5) (sourceB313 + difference 5 4) sourceC313) = raw6698 := by
      apply Matrix.ext; unfold tripleCharges sourceA313 sourceB313 sourceC313 difference raw6698; decide +kernel
    rw [ha]
    exact (canonical6698 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA313 + sourceB313) sourceC313) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA313 + sourceB313) sourceC313) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA313 sourceB313 sourceC313 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA313 sourceB313 sourceC313
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm313, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq314 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm314 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA314 + difference 0 4) (sourceB314 + difference 4 0) sourceC314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA314 + difference 0 4) (sourceB314 + difference 4 0) sourceC314) = raw6672 := by
      apply Matrix.ext; unfold tripleCharges sourceA314 sourceB314 sourceC314 difference raw6672; decide +kernel
    rw [ha]
    exact (canonical6672 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA314 + difference 1 4) (sourceB314 + difference 4 1) sourceC314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA314 + difference 1 4) (sourceB314 + difference 4 1) sourceC314) = raw6682 := by
      apply Matrix.ext; unfold tripleCharges sourceA314 sourceB314 sourceC314 difference raw6682; decide +kernel
    rw [ha]
    exact (canonical6682 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA314 + difference 2 4) (sourceB314 + difference 4 2) sourceC314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3029) := by
    have ha : (tripleCharges (sourceA314 + difference 2 4) (sourceB314 + difference 4 2) sourceC314) = raw6689 := by
      apply Matrix.ext; unfold tripleCharges sourceA314 sourceB314 sourceC314 difference raw6689; decide +kernel
    rw [ha]
    exact (canonical6689 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA314 + difference 3 4) (sourceB314 + difference 4 3) sourceC314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2641) := by
    have ha : (tripleCharges (sourceA314 + difference 3 4) (sourceB314 + difference 4 3) sourceC314) = raw6694 := by
      apply Matrix.ext; unfold tripleCharges sourceA314 sourceB314 sourceC314 difference raw6694; decide +kernel
    rw [ha]
    exact (canonical6694 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA314 + difference 4 4) (sourceB314 + difference 4 4) sourceC314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA314 + difference 4 4) (sourceB314 + difference 4 4) sourceC314) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA314 sourceB314 sourceC314 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA314 + difference 5 4) (sourceB314 + difference 4 5) sourceC314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA314 + difference 5 4) (sourceB314 + difference 4 5) sourceC314) = raw6699 := by
      apply Matrix.ext; unfold tripleCharges sourceA314 sourceB314 sourceC314 difference raw6699; decide +kernel
    rw [ha]
    exact (canonical6699 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA314 + sourceB314) sourceC314) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA314 + sourceB314) sourceC314) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA314 sourceB314 sourceC314 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA314 sourceB314 sourceC314
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm314, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq315 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm315 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA315 + difference 5 0) (sourceB315 + difference 0 5) sourceC315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1361) := by
    have ha : (tripleCharges (sourceA315 + difference 5 0) (sourceB315 + difference 0 5) sourceC315) = raw6679 := by
      apply Matrix.ext; unfold tripleCharges sourceA315 sourceB315 sourceC315 difference raw6679; decide +kernel
    rw [ha]
    exact (canonical6679 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA315 + difference 5 1) (sourceB315 + difference 1 5) sourceC315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2946) := by
    have ha : (tripleCharges (sourceA315 + difference 5 1) (sourceB315 + difference 1 5) sourceC315) = raw6687 := by
      apply Matrix.ext; unfold tripleCharges sourceA315 sourceB315 sourceC315 difference raw6687; decide +kernel
    rw [ha]
    exact (canonical6687 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA315 + difference 5 2) (sourceB315 + difference 2 5) sourceC315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2918) := by
    have ha : (tripleCharges (sourceA315 + difference 5 2) (sourceB315 + difference 2 5) sourceC315) = raw6693 := by
      apply Matrix.ext; unfold tripleCharges sourceA315 sourceB315 sourceC315 difference raw6693; decide +kernel
    rw [ha]
    exact (canonical6693 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA315 + difference 5 3) (sourceB315 + difference 3 5) sourceC315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA315 + difference 5 3) (sourceB315 + difference 3 5) sourceC315) = raw6697 := by
      apply Matrix.ext; unfold tripleCharges sourceA315 sourceB315 sourceC315 difference raw6697; decide +kernel
    rw [ha]
    exact (canonical6697 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA315 + difference 5 4) (sourceB315 + difference 4 5) sourceC315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA315 + difference 5 4) (sourceB315 + difference 4 5) sourceC315) = raw6699 := by
      apply Matrix.ext; unfold tripleCharges sourceA315 sourceB315 sourceC315 difference raw6699; decide +kernel
    rw [ha]
    exact (canonical6699 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA315 + difference 5 5) (sourceB315 + difference 5 5) sourceC315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA315 + difference 5 5) (sourceB315 + difference 5 5) sourceC315) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA315 sourceB315 sourceC315 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA315 + sourceB315) sourceC315) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA315 + sourceB315) sourceC315) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA315 sourceB315 sourceC315 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA315 sourceB315 sourceC315
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm315, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq317 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm317 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA317 + difference 0 1) (sourceB317 + difference 1 0) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3044) := by
    have ha : (tripleCharges (sourceA317 + difference 0 1) (sourceB317 + difference 1 0) sourceC317) = raw6728 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6728; decide +kernel
    rw [ha]
    exact (canonical6728 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA317 + difference 0 2) (sourceB317 + difference 2 0) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3068) := by
    have ha : (tripleCharges (sourceA317 + difference 0 2) (sourceB317 + difference 2 0) sourceC317) = raw6729 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6729; decide +kernel
    rw [ha]
    exact (canonical6729 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA317 + difference 0 3) (sourceB317 + difference 3 0) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA317 + difference 0 3) (sourceB317 + difference 3 0) sourceC317) = raw6730 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6730; decide +kernel
    rw [ha]
    exact (canonical6730 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA317 + difference 0 4) (sourceB317 + difference 4 0) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA317 + difference 0 4) (sourceB317 + difference 4 0) sourceC317) = raw6731 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6731; decide +kernel
    rw [ha]
    exact (canonical6731 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA317 + difference 0 5) (sourceB317 + difference 5 0) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3094) := by
    have ha : (tripleCharges (sourceA317 + difference 0 5) (sourceB317 + difference 5 0) sourceC317) = raw6732 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6732; decide +kernel
    rw [ha]
    exact (canonical6732 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA317 + difference 1 0) (sourceB317 + difference 0 1) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA317 + difference 1 0) (sourceB317 + difference 0 1) sourceC317) = raw6733 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6733; decide +kernel
    rw [ha]
    exact (canonical6733 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA317 + difference 1 2) (sourceB317 + difference 2 1) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA317 + difference 1 2) (sourceB317 + difference 2 1) sourceC317) = raw6734 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6734; decide +kernel
    rw [ha]
    exact (canonical6734 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA317 + difference 1 3) (sourceB317 + difference 3 1) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA317 + difference 1 3) (sourceB317 + difference 3 1) sourceC317) = raw6735 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6735; decide +kernel
    rw [ha]
    exact (canonical6735 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA317 + difference 1 4) (sourceB317 + difference 4 1) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA317 + difference 1 4) (sourceB317 + difference 4 1) sourceC317) = raw6736 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6736; decide +kernel
    rw [ha]
    exact (canonical6736 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA317 + difference 1 5) (sourceB317 + difference 5 1) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA317 + difference 1 5) (sourceB317 + difference 5 1) sourceC317) = raw6737 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6737; decide +kernel
    rw [ha]
    exact (canonical6737 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA317 + difference 2 0) (sourceB317 + difference 0 2) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA317 + difference 2 0) (sourceB317 + difference 0 2) sourceC317) = raw6738 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6738; decide +kernel
    rw [ha]
    exact (canonical6738 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA317 + difference 2 1) (sourceB317 + difference 1 2) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2665) := by
    have ha : (tripleCharges (sourceA317 + difference 2 1) (sourceB317 + difference 1 2) sourceC317) = raw6739 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6739; decide +kernel
    rw [ha]
    exact (canonical6739 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA317 + difference 2 3) (sourceB317 + difference 3 2) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA317 + difference 2 3) (sourceB317 + difference 3 2) sourceC317) = raw6740 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6740; decide +kernel
    rw [ha]
    exact (canonical6740 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA317 + difference 2 4) (sourceB317 + difference 4 2) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2713) := by
    have ha : (tripleCharges (sourceA317 + difference 2 4) (sourceB317 + difference 4 2) sourceC317) = raw6741 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6741; decide +kernel
    rw [ha]
    exact (canonical6741 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA317 + difference 2 5) (sourceB317 + difference 5 2) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA317 + difference 2 5) (sourceB317 + difference 5 2) sourceC317) = raw6742 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6742; decide +kernel
    rw [ha]
    exact (canonical6742 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA317 + difference 3 0) (sourceB317 + difference 0 3) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA317 + difference 3 0) (sourceB317 + difference 0 3) sourceC317) = raw6743 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6743; decide +kernel
    rw [ha]
    exact (canonical6743 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA317 + difference 3 1) (sourceB317 + difference 1 3) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2128) := by
    have ha : (tripleCharges (sourceA317 + difference 3 1) (sourceB317 + difference 1 3) sourceC317) = raw6744 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6744; decide +kernel
    rw [ha]
    exact (canonical6744 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA317 + difference 3 2) (sourceB317 + difference 2 3) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2127) := by
    have ha : (tripleCharges (sourceA317 + difference 3 2) (sourceB317 + difference 2 3) sourceC317) = raw6745 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6745; decide +kernel
    rw [ha]
    exact (canonical6745 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA317 + difference 3 4) (sourceB317 + difference 4 3) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2129) := by
    have ha : (tripleCharges (sourceA317 + difference 3 4) (sourceB317 + difference 4 3) sourceC317) = raw6746 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6746; decide +kernel
    rw [ha]
    exact (canonical6746 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA317 + difference 3 5) (sourceB317 + difference 5 3) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA317 + difference 3 5) (sourceB317 + difference 5 3) sourceC317) = raw6747 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6747; decide +kernel
    rw [ha]
    exact (canonical6747 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA317 + difference 4 0) (sourceB317 + difference 0 4) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA317 + difference 4 0) (sourceB317 + difference 0 4) sourceC317) = raw6748 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6748; decide +kernel
    rw [ha]
    exact (canonical6748 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA317 + difference 4 1) (sourceB317 + difference 1 4) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA317 + difference 4 1) (sourceB317 + difference 1 4) sourceC317) = raw6749 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6749; decide +kernel
    rw [ha]
    exact (canonical6749 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA317 + difference 4 2) (sourceB317 + difference 2 4) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2698) := by
    have ha : (tripleCharges (sourceA317 + difference 4 2) (sourceB317 + difference 2 4) sourceC317) = raw6750 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6750; decide +kernel
    rw [ha]
    exact (canonical6750 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA317 + difference 4 3) (sourceB317 + difference 3 4) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA317 + difference 4 3) (sourceB317 + difference 3 4) sourceC317) = raw6412 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6412; decide +kernel
    rw [ha]
    exact (canonical6412 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA317 + difference 4 5) (sourceB317 + difference 5 4) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA317 + difference 4 5) (sourceB317 + difference 5 4) sourceC317) = raw6406 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6406; decide +kernel
    rw [ha]
    exact (canonical6406 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA317 + difference 5 0) (sourceB317 + difference 0 5) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA317 + difference 5 0) (sourceB317 + difference 0 5) sourceC317) = raw6751 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6751; decide +kernel
    rw [ha]
    exact (canonical6751 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA317 + difference 5 1) (sourceB317 + difference 1 5) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2677) := by
    have ha : (tripleCharges (sourceA317 + difference 5 1) (sourceB317 + difference 1 5) sourceC317) = raw6752 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6752; decide +kernel
    rw [ha]
    exact (canonical6752 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA317 + difference 5 2) (sourceB317 + difference 2 5) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA317 + difference 5 2) (sourceB317 + difference 2 5) sourceC317) = raw6753 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6753; decide +kernel
    rw [ha]
    exact (canonical6753 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA317 + difference 5 3) (sourceB317 + difference 3 5) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA317 + difference 5 3) (sourceB317 + difference 3 5) sourceC317) = raw6754 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6754; decide +kernel
    rw [ha]
    exact (canonical6754 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA317 + difference 5 4) (sourceB317 + difference 4 5) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA317 + difference 5 4) (sourceB317 + difference 4 5) sourceC317) = raw6755 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6755; decide +kernel
    rw [ha]
    exact (canonical6755 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA317 sourceB317 sourceC317
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm317, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq319 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm319 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA319 + difference 0 0) (sourceB319 + difference 0 0) sourceC319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA319 + difference 0 0) (sourceB319 + difference 0 0) sourceC319) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA319 sourceB319 sourceC319 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA319 + difference 0 1) (sourceB319 + difference 1 0) sourceC319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3395) := by
    have ha : (tripleCharges (sourceA319 + difference 0 1) (sourceB319 + difference 1 0) sourceC319) = raw6785 := by
      apply Matrix.ext; unfold tripleCharges sourceA319 sourceB319 sourceC319 difference raw6785; decide +kernel
    rw [ha]
    exact (canonical6785 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA319 + difference 0 2) (sourceB319 + difference 2 0) sourceC319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3388) := by
    have ha : (tripleCharges (sourceA319 + difference 0 2) (sourceB319 + difference 2 0) sourceC319) = raw6786 := by
      apply Matrix.ext; unfold tripleCharges sourceA319 sourceB319 sourceC319 difference raw6786; decide +kernel
    rw [ha]
    exact (canonical6786 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA319 + difference 0 3) (sourceB319 + difference 3 0) sourceC319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA319 + difference 0 3) (sourceB319 + difference 3 0) sourceC319) = raw6787 := by
      apply Matrix.ext; unfold tripleCharges sourceA319 sourceB319 sourceC319 difference raw6787; decide +kernel
    rw [ha]
    exact (canonical6787 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA319 + difference 0 4) (sourceB319 + difference 4 0) sourceC319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA319 + difference 0 4) (sourceB319 + difference 4 0) sourceC319) = raw6788 := by
      apply Matrix.ext; unfold tripleCharges sourceA319 sourceB319 sourceC319 difference raw6788; decide +kernel
    rw [ha]
    exact (canonical6788 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA319 + difference 0 5) (sourceB319 + difference 5 0) sourceC319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3391) := by
    have ha : (tripleCharges (sourceA319 + difference 0 5) (sourceB319 + difference 5 0) sourceC319) = raw6789 := by
      apply Matrix.ext; unfold tripleCharges sourceA319 sourceB319 sourceC319 difference raw6789; decide +kernel
    rw [ha]
    exact (canonical6789 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA319 + sourceB319) sourceC319) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA319 + sourceB319) sourceC319) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA319 sourceB319 sourceC319 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA319 sourceB319 sourceC319
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm319, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck256 : Integer.Sparse.reindex keyMap MixedData.row256 = numericRow256 := by decide +kernel

theorem numericCheck256 (x : Master → ℝ) : Integer.Sparse.eval numericRow256 x =
    (1 : ℝ) * reducedSource256 x := by
  norm_num [numericRow256, reducedSource256, Integer.Sparse.eval, Sparse.eval, nodeValue3039, nodeValue3880, nodeValue3881, nodeValue3885, nodeValue3910, nodeValue3958, nodeValue4091]

theorem reindexCheck257 : Integer.Sparse.reindex keyMap MixedData.row257 = numericRow257 := by decide +kernel

theorem numericCheck257 (x : Master → ℝ) : Integer.Sparse.eval numericRow257 x =
    (1 : ℝ) * reducedSource257 x := by
  norm_num [numericRow257, reducedSource257, Integer.Sparse.eval, Sparse.eval, nodeValue1358, nodeValue1361, nodeValue1363, nodeValue1370, nodeValue1423, nodeValue3039, nodeValue4091]

theorem reindexCheck258 : Integer.Sparse.reindex keyMap MixedData.row258 = numericRow258 := by decide +kernel

theorem numericCheck258 (x : Master → ℝ) : Integer.Sparse.eval numericRow258 x =
    (1 : ℝ) * reducedSource258 x := by
  norm_num [numericRow258, reducedSource258, Integer.Sparse.eval, Sparse.eval, nodeValue1370, nodeValue2884, nodeValue2976, nodeValue3039, nodeValue3053, nodeValue4091]

theorem reindexCheck259 : Integer.Sparse.reindex keyMap MixedData.row259 = numericRow259 := by decide +kernel

theorem numericCheck259 (x : Master → ℝ) : Integer.Sparse.eval numericRow259 x =
    (1 : ℝ) * reducedSource259 x := by
  norm_num [numericRow259, reducedSource259, Integer.Sparse.eval, Sparse.eval, nodeValue2627, nodeValue2946, nodeValue3008, nodeValue3011, nodeValue3039, nodeValue3881, nodeValue4091]

theorem reindexCheck260 : Integer.Sparse.reindex keyMap MixedData.row260 = numericRow260 := by decide +kernel

theorem numericCheck260 (x : Master → ℝ) : Integer.Sparse.eval numericRow260 x =
    (1 : ℝ) * reducedSource260 x := by
  norm_num [numericRow260, reducedSource260, Integer.Sparse.eval, Sparse.eval, nodeValue1358, nodeValue2862, nodeValue3008, nodeValue3029, nodeValue3037, nodeValue3039, nodeValue4091]

theorem reindexCheck261 : Integer.Sparse.reindex keyMap MixedData.row261 = numericRow261 := by decide +kernel

theorem numericCheck261 (x : Master → ℝ) : Integer.Sparse.eval numericRow261 x =
    (1 : ℝ) * reducedSource261 x := by
  norm_num [numericRow261, reducedSource261, Integer.Sparse.eval, Sparse.eval, nodeValue2625, nodeValue2918, nodeValue2972, nodeValue2976, nodeValue3039, nodeValue3880, nodeValue4091]

theorem reindexCheck262 : Integer.Sparse.reindex keyMap MixedData.row262 = numericRow262 := by decide +kernel

theorem numericCheck262 (x : Master → ℝ) : Integer.Sparse.eval numericRow262 x =
    (1 : ℝ) * reducedSource262 x := by
  norm_num [numericRow262, reducedSource262, Integer.Sparse.eval, Sparse.eval, nodeValue1423, nodeValue2625, nodeValue2627, nodeValue2641, nodeValue2754, nodeValue3039, nodeValue4091]

theorem reindexCheck263 : Integer.Sparse.reindex keyMap MixedData.row263 = numericRow263 := by decide +kernel

theorem numericCheck263 (x : Master → ℝ) : Integer.Sparse.eval numericRow263 x =
    (1 : ℝ) * reducedSource263 x := by
  norm_num [numericRow263, reducedSource263, Integer.Sparse.eval, Sparse.eval, nodeValue2862, nodeValue2865, nodeValue2868, nodeValue2884, nodeValue3039, nodeValue3958, nodeValue4091]

theorem reindexCheck264 : Integer.Sparse.reindex keyMap MixedData.row264 = numericRow264 := by decide +kernel

theorem numericCheck264 (x : Master → ℝ) : Integer.Sparse.eval numericRow264 x =
    (1 : ℝ) * reducedSource264 x := by
  norm_num [numericRow264, reducedSource264, Integer.Sparse.eval, Sparse.eval, nodeValue1363, nodeValue2868, nodeValue2972, nodeValue3011, nodeValue3039, nodeValue4091]

theorem reindexCheck265 : Integer.Sparse.reindex keyMap MixedData.row265 = numericRow265 := by decide +kernel

theorem numericCheck265 (x : Master → ℝ) : Integer.Sparse.eval numericRow265 x =
    (1 : ℝ) * reducedSource265 x := by
  norm_num [numericRow265, reducedSource265, Integer.Sparse.eval, Sparse.eval, nodeValue2641, nodeValue3029, nodeValue3031, nodeValue3039, nodeValue3885, nodeValue4091]

theorem reindexCheck266 : Integer.Sparse.reindex keyMap MixedData.row266 = numericRow266 := by decide +kernel

theorem numericCheck266 (x : Master → ℝ) : Integer.Sparse.eval numericRow266 x =
    (1 : ℝ) * reducedSource266 x := by
  norm_num [numericRow266, reducedSource266, Integer.Sparse.eval, Sparse.eval, nodeValue1361, nodeValue2865, nodeValue2918, nodeValue2946, nodeValue3031, nodeValue3039, nodeValue4091]

theorem reindexCheck268 : Integer.Sparse.reindex keyMap MixedData.row268 = numericRow268 := by decide +kernel

theorem numericCheck268 (x : Master → ℝ) : Integer.Sparse.eval numericRow268 x =
    (8640 : ℝ) * reducedSource268 x := by
  norm_num [numericRow268, reducedSource268, Integer.Sparse.eval, Sparse.eval, nodeValue2127, nodeValue2128, nodeValue2129, nodeValue2133, nodeValue2195, nodeValue2215, nodeValue2216, nodeValue2220, nodeValue2278, nodeValue2665, nodeValue2677, nodeValue2678, nodeValue2697, nodeValue2698, nodeValue2709, nodeValue2713, nodeValue2714, nodeValue2722, nodeValue2723, nodeValue2729, nodeValue2731, nodeValue2732, nodeValue2767, nodeValue2774, nodeValue2776, nodeValue3044, nodeValue3068, nodeValue3088, nodeValue3092, nodeValue3094]
  ring

theorem reindexCheck270 : Integer.Sparse.reindex keyMap MixedData.row270 = numericRow270 := by decide +kernel

theorem numericCheck270 (x : Master → ℝ) : Integer.Sparse.eval numericRow270 x =
    (1 : ℝ) * reducedSource270 x := by
  norm_num [numericRow270, reducedSource270, Integer.Sparse.eval, Sparse.eval, nodeValue3388, nodeValue3391, nodeValue3392, nodeValue3395, nodeValue3535, nodeValue3544, nodeValue4084]

theorem reindexCheck271 : Integer.Sparse.reindex keyMap MixedData.row271 = numericRow271 := by decide +kernel

theorem numericCheck271 (x : Master → ℝ) : Integer.Sparse.eval numericRow271 x =
    (1 : ℝ) * reducedSource271 x := by
  norm_num [numericRow271, reducedSource271, Integer.Sparse.eval, Sparse.eval, nodeValue2021, nodeValue2026, nodeValue2028, nodeValue2058, nodeValue2266, nodeValue3535, nodeValue4084]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero256 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource256 (mixedVector B) = 0 := by
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h3885 : mixedVector B (Sum.inr 3885) = Sparse.eval nodeValue3885 (mixedVector B) := by
    change mixedMoment B node3885 node3885Labels = _
    exact sound3885 B hB hF
  have h3910 : mixedVector B (Sum.inr 3910) = Sparse.eval nodeValue3910 (mixedVector B) := by
    change mixedMoment B node3910 node3910Labels = _
    exact sound3910 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm305, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3039, h3880, h3881, h3885, h3910, h3958, h4091, reducedSource256] using sourceEq305 B hB

theorem rowSound256 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row256 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck256, numericCheck256, reducedZero256 B hB hF, mul_zero]

theorem reducedZero257 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource257 (mixedVector B) = 0 := by
  have h1358 : mixedVector B (Sum.inr 1358) = Sparse.eval nodeValue1358 (mixedVector B) := by
    change mixedMoment B node1358 node1358Labels = _
    exact sound1358 B hB hF
  have h1361 : mixedVector B (Sum.inr 1361) = Sparse.eval nodeValue1361 (mixedVector B) := by
    change mixedMoment B node1361 node1361Labels = _
    exact sound1361 B hB hF
  have h1363 : mixedVector B (Sum.inr 1363) = Sparse.eval nodeValue1363 (mixedVector B) := by
    change mixedMoment B node1363 node1363Labels = _
    exact sound1363 B hB hF
  have h1370 : mixedVector B (Sum.inr 1370) = Sparse.eval nodeValue1370 (mixedVector B) := by
    change mixedMoment B node1370 node1370Labels = _
    exact sound1370 B hB hF
  have h1423 : mixedVector B (Sum.inr 1423) = Sparse.eval nodeValue1423 (mixedVector B) := by
    change mixedMoment B node1423 node1423Labels = _
    exact sound1423 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm306, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1358, h1361, h1363, h1370, h1423, h3039, h4091, reducedSource257] using sourceEq306 B hB

theorem rowSound257 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row257 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck257, numericCheck257, reducedZero257 B hB hF, mul_zero]

theorem reducedZero258 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource258 (mixedVector B) = 0 := by
  have h1370 : mixedVector B (Sum.inr 1370) = Sparse.eval nodeValue1370 (mixedVector B) := by
    change mixedMoment B node1370 node1370Labels = _
    exact sound1370 B hB hF
  have h2884 : mixedVector B (Sum.inr 2884) = Sparse.eval nodeValue2884 (mixedVector B) := by
    change mixedMoment B node2884 node2884Labels = _
    exact sound2884 B hB hF
  have h2976 : mixedVector B (Sum.inr 2976) = Sparse.eval nodeValue2976 (mixedVector B) := by
    change mixedMoment B node2976 node2976Labels = _
    exact sound2976 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3053 : mixedVector B (Sum.inr 3053) = Sparse.eval nodeValue3053 (mixedVector B) := by
    change mixedMoment B node3053 node3053Labels = _
    exact sound3053 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm307, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1370, h2884, h2976, h3039, h3053, h4091, reducedSource258] using sourceEq307 B hB

theorem rowSound258 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row258 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck258, numericCheck258, reducedZero258 B hB hF, mul_zero]

theorem reducedZero259 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource259 (mixedVector B) = 0 := by
  have h2627 : mixedVector B (Sum.inr 2627) = Sparse.eval nodeValue2627 (mixedVector B) := by
    change mixedMoment B node2627 node2627Labels = _
    exact sound2627 B hB hF
  have h2946 : mixedVector B (Sum.inr 2946) = Sparse.eval nodeValue2946 (mixedVector B) := by
    change mixedMoment B node2946 node2946Labels = _
    exact sound2946 B hB hF
  have h3008 : mixedVector B (Sum.inr 3008) = Sparse.eval nodeValue3008 (mixedVector B) := by
    change mixedMoment B node3008 node3008Labels = _
    exact sound3008 B hB hF
  have h3011 : mixedVector B (Sum.inr 3011) = Sparse.eval nodeValue3011 (mixedVector B) := by
    change mixedMoment B node3011 node3011Labels = _
    exact sound3011 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm308, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2627, h2946, h3008, h3011, h3039, h3881, h4091, reducedSource259] using sourceEq308 B hB

theorem rowSound259 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row259 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck259, numericCheck259, reducedZero259 B hB hF, mul_zero]

theorem reducedZero260 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource260 (mixedVector B) = 0 := by
  have h1358 : mixedVector B (Sum.inr 1358) = Sparse.eval nodeValue1358 (mixedVector B) := by
    change mixedMoment B node1358 node1358Labels = _
    exact sound1358 B hB hF
  have h2862 : mixedVector B (Sum.inr 2862) = Sparse.eval nodeValue2862 (mixedVector B) := by
    change mixedMoment B node2862 node2862Labels = _
    exact sound2862 B hB hF
  have h3008 : mixedVector B (Sum.inr 3008) = Sparse.eval nodeValue3008 (mixedVector B) := by
    change mixedMoment B node3008 node3008Labels = _
    exact sound3008 B hB hF
  have h3029 : mixedVector B (Sum.inr 3029) = Sparse.eval nodeValue3029 (mixedVector B) := by
    change mixedMoment B node3029 node3029Labels = _
    exact sound3029 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm309, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1358, h2862, h3008, h3029, h3037, h3039, h4091, reducedSource260] using sourceEq309 B hB

theorem rowSound260 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row260 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck260, numericCheck260, reducedZero260 B hB hF, mul_zero]

theorem reducedZero261 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource261 (mixedVector B) = 0 := by
  have h2625 : mixedVector B (Sum.inr 2625) = Sparse.eval nodeValue2625 (mixedVector B) := by
    change mixedMoment B node2625 node2625Labels = _
    exact sound2625 B hB hF
  have h2918 : mixedVector B (Sum.inr 2918) = Sparse.eval nodeValue2918 (mixedVector B) := by
    change mixedMoment B node2918 node2918Labels = _
    exact sound2918 B hB hF
  have h2972 : mixedVector B (Sum.inr 2972) = Sparse.eval nodeValue2972 (mixedVector B) := by
    change mixedMoment B node2972 node2972Labels = _
    exact sound2972 B hB hF
  have h2976 : mixedVector B (Sum.inr 2976) = Sparse.eval nodeValue2976 (mixedVector B) := by
    change mixedMoment B node2976 node2976Labels = _
    exact sound2976 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm310, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2625, h2918, h2972, h2976, h3039, h3880, h4091, reducedSource261] using sourceEq310 B hB

theorem rowSound261 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row261 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck261, numericCheck261, reducedZero261 B hB hF, mul_zero]

theorem reducedZero262 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource262 (mixedVector B) = 0 := by
  have h1423 : mixedVector B (Sum.inr 1423) = Sparse.eval nodeValue1423 (mixedVector B) := by
    change mixedMoment B node1423 node1423Labels = _
    exact sound1423 B hB hF
  have h2625 : mixedVector B (Sum.inr 2625) = Sparse.eval nodeValue2625 (mixedVector B) := by
    change mixedMoment B node2625 node2625Labels = _
    exact sound2625 B hB hF
  have h2627 : mixedVector B (Sum.inr 2627) = Sparse.eval nodeValue2627 (mixedVector B) := by
    change mixedMoment B node2627 node2627Labels = _
    exact sound2627 B hB hF
  have h2641 : mixedVector B (Sum.inr 2641) = Sparse.eval nodeValue2641 (mixedVector B) := by
    change mixedMoment B node2641 node2641Labels = _
    exact sound2641 B hB hF
  have h2754 : mixedVector B (Sum.inr 2754) = Sparse.eval nodeValue2754 (mixedVector B) := by
    change mixedMoment B node2754 node2754Labels = _
    exact sound2754 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm311, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1423, h2625, h2627, h2641, h2754, h3039, h4091, reducedSource262] using sourceEq311 B hB

theorem rowSound262 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row262 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck262, numericCheck262, reducedZero262 B hB hF, mul_zero]

theorem reducedZero263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource263 (mixedVector B) = 0 := by
  have h2862 : mixedVector B (Sum.inr 2862) = Sparse.eval nodeValue2862 (mixedVector B) := by
    change mixedMoment B node2862 node2862Labels = _
    exact sound2862 B hB hF
  have h2865 : mixedVector B (Sum.inr 2865) = Sparse.eval nodeValue2865 (mixedVector B) := by
    change mixedMoment B node2865 node2865Labels = _
    exact sound2865 B hB hF
  have h2868 : mixedVector B (Sum.inr 2868) = Sparse.eval nodeValue2868 (mixedVector B) := by
    change mixedMoment B node2868 node2868Labels = _
    exact sound2868 B hB hF
  have h2884 : mixedVector B (Sum.inr 2884) = Sparse.eval nodeValue2884 (mixedVector B) := by
    change mixedMoment B node2884 node2884Labels = _
    exact sound2884 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm312, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2862, h2865, h2868, h2884, h3039, h3958, h4091, reducedSource263] using sourceEq312 B hB

theorem rowSound263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row263 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck263, numericCheck263, reducedZero263 B hB hF, mul_zero]

theorem reducedZero264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource264 (mixedVector B) = 0 := by
  have h1363 : mixedVector B (Sum.inr 1363) = Sparse.eval nodeValue1363 (mixedVector B) := by
    change mixedMoment B node1363 node1363Labels = _
    exact sound1363 B hB hF
  have h2868 : mixedVector B (Sum.inr 2868) = Sparse.eval nodeValue2868 (mixedVector B) := by
    change mixedMoment B node2868 node2868Labels = _
    exact sound2868 B hB hF
  have h2972 : mixedVector B (Sum.inr 2972) = Sparse.eval nodeValue2972 (mixedVector B) := by
    change mixedMoment B node2972 node2972Labels = _
    exact sound2972 B hB hF
  have h3011 : mixedVector B (Sum.inr 3011) = Sparse.eval nodeValue3011 (mixedVector B) := by
    change mixedMoment B node3011 node3011Labels = _
    exact sound3011 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm313, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1363, h2868, h2972, h3011, h3039, h4091, reducedSource264] using sourceEq313 B hB

theorem rowSound264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row264 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck264, numericCheck264, reducedZero264 B hB hF, mul_zero]

theorem reducedZero265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource265 (mixedVector B) = 0 := by
  have h2641 : mixedVector B (Sum.inr 2641) = Sparse.eval nodeValue2641 (mixedVector B) := by
    change mixedMoment B node2641 node2641Labels = _
    exact sound2641 B hB hF
  have h3029 : mixedVector B (Sum.inr 3029) = Sparse.eval nodeValue3029 (mixedVector B) := by
    change mixedMoment B node3029 node3029Labels = _
    exact sound3029 B hB hF
  have h3031 : mixedVector B (Sum.inr 3031) = Sparse.eval nodeValue3031 (mixedVector B) := by
    change mixedMoment B node3031 node3031Labels = _
    exact sound3031 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3885 : mixedVector B (Sum.inr 3885) = Sparse.eval nodeValue3885 (mixedVector B) := by
    change mixedMoment B node3885 node3885Labels = _
    exact sound3885 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm314, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2641, h3029, h3031, h3039, h3885, h4091, reducedSource265] using sourceEq314 B hB

theorem rowSound265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row265 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck265, numericCheck265, reducedZero265 B hB hF, mul_zero]

theorem reducedZero266 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource266 (mixedVector B) = 0 := by
  have h1361 : mixedVector B (Sum.inr 1361) = Sparse.eval nodeValue1361 (mixedVector B) := by
    change mixedMoment B node1361 node1361Labels = _
    exact sound1361 B hB hF
  have h2865 : mixedVector B (Sum.inr 2865) = Sparse.eval nodeValue2865 (mixedVector B) := by
    change mixedMoment B node2865 node2865Labels = _
    exact sound2865 B hB hF
  have h2918 : mixedVector B (Sum.inr 2918) = Sparse.eval nodeValue2918 (mixedVector B) := by
    change mixedMoment B node2918 node2918Labels = _
    exact sound2918 B hB hF
  have h2946 : mixedVector B (Sum.inr 2946) = Sparse.eval nodeValue2946 (mixedVector B) := by
    change mixedMoment B node2946 node2946Labels = _
    exact sound2946 B hB hF
  have h3031 : mixedVector B (Sum.inr 3031) = Sparse.eval nodeValue3031 (mixedVector B) := by
    change mixedMoment B node3031 node3031Labels = _
    exact sound3031 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm315, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1361, h2865, h2918, h2946, h3031, h3039, h4091, reducedSource266] using sourceEq315 B hB

theorem rowSound266 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row266 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck266, numericCheck266, reducedZero266 B hB hF, mul_zero]

theorem reducedZero268 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource268 (mixedVector B) = 0 := by
  have h2127 : mixedVector B (Sum.inr 2127) = Sparse.eval nodeValue2127 (mixedVector B) := by
    change mixedMoment B node2127 node2127Labels = _
    exact sound2127 B hB hF
  have h2128 : mixedVector B (Sum.inr 2128) = Sparse.eval nodeValue2128 (mixedVector B) := by
    change mixedMoment B node2128 node2128Labels = _
    exact sound2128 B hB hF
  have h2129 : mixedVector B (Sum.inr 2129) = Sparse.eval nodeValue2129 (mixedVector B) := by
    change mixedMoment B node2129 node2129Labels = _
    exact sound2129 B hB hF
  have h2133 : mixedVector B (Sum.inr 2133) = Sparse.eval nodeValue2133 (mixedVector B) := by
    change mixedMoment B node2133 node2133Labels = _
    exact sound2133 B hB hF
  have h2195 : mixedVector B (Sum.inr 2195) = Sparse.eval nodeValue2195 (mixedVector B) := by
    change mixedMoment B node2195 node2195Labels = _
    exact sound2195 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2220 : mixedVector B (Sum.inr 2220) = Sparse.eval nodeValue2220 (mixedVector B) := by
    change mixedMoment B node2220 node2220Labels = _
    exact sound2220 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2665 : mixedVector B (Sum.inr 2665) = Sparse.eval nodeValue2665 (mixedVector B) := by
    change mixedMoment B node2665 node2665Labels = _
    exact sound2665 B hB hF
  have h2677 : mixedVector B (Sum.inr 2677) = Sparse.eval nodeValue2677 (mixedVector B) := by
    change mixedMoment B node2677 node2677Labels = _
    exact sound2677 B hB hF
  have h2678 : mixedVector B (Sum.inr 2678) = Sparse.eval nodeValue2678 (mixedVector B) := by
    change mixedMoment B node2678 node2678Labels = _
    exact sound2678 B hB hF
  have h2697 : mixedVector B (Sum.inr 2697) = Sparse.eval nodeValue2697 (mixedVector B) := by
    change mixedMoment B node2697 node2697Labels = _
    exact sound2697 B hB hF
  have h2698 : mixedVector B (Sum.inr 2698) = Sparse.eval nodeValue2698 (mixedVector B) := by
    change mixedMoment B node2698 node2698Labels = _
    exact sound2698 B hB hF
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h2713 : mixedVector B (Sum.inr 2713) = Sparse.eval nodeValue2713 (mixedVector B) := by
    change mixedMoment B node2713 node2713Labels = _
    exact sound2713 B hB hF
  have h2714 : mixedVector B (Sum.inr 2714) = Sparse.eval nodeValue2714 (mixedVector B) := by
    change mixedMoment B node2714 node2714Labels = _
    exact sound2714 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2729 : mixedVector B (Sum.inr 2729) = Sparse.eval nodeValue2729 (mixedVector B) := by
    change mixedMoment B node2729 node2729Labels = _
    exact sound2729 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2767 : mixedVector B (Sum.inr 2767) = Sparse.eval nodeValue2767 (mixedVector B) := by
    change mixedMoment B node2767 node2767Labels = _
    exact sound2767 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h2776 : mixedVector B (Sum.inr 2776) = Sparse.eval nodeValue2776 (mixedVector B) := by
    change mixedMoment B node2776 node2776Labels = _
    exact sound2776 B hB hF
  have h3044 : mixedVector B (Sum.inr 3044) = Sparse.eval nodeValue3044 (mixedVector B) := by
    change mixedMoment B node3044 node3044Labels = _
    exact sound3044 B hB hF
  have h3068 : mixedVector B (Sum.inr 3068) = Sparse.eval nodeValue3068 (mixedVector B) := by
    change mixedMoment B node3068 node3068Labels = _
    exact sound3068 B hB hF
  have h3088 : mixedVector B (Sum.inr 3088) = Sparse.eval nodeValue3088 (mixedVector B) := by
    change mixedMoment B node3088 node3088Labels = _
    exact sound3088_e B hB hF
  have h3092 : mixedVector B (Sum.inr 3092) = Sparse.eval nodeValue3092 (mixedVector B) := by
    change mixedMoment B node3092 node3092Labels = _
    exact sound3092 B hB hF
  have h3094 : mixedVector B (Sum.inr 3094) = Sparse.eval nodeValue3094 (mixedVector B) := by
    change mixedMoment B node3094 node3094Labels = _
    exact sound3094_e B hB hF
  simpa only [sourceForm317, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2127, h2128, h2129, h2133, h2195, h2215, h2216, h2220, h2278, h2665, h2677, h2678, h2697, h2698, h2709, h2713, h2714, h2722, h2723, h2729, h2731, h2732, h2767, h2774, h2776, h3044, h3068, h3088, h3092, h3094, reducedSource268] using sourceEq317 B hB

theorem rowSound268 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row268 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck268, numericCheck268, reducedZero268 B hB hF, mul_zero]

theorem reducedZero270 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource270 (mixedVector B) = 0 := by
  have h3388 : mixedVector B (Sum.inr 3388) = Sparse.eval nodeValue3388 (mixedVector B) := by
    change mixedMoment B node3388 node3388Labels = _
    exact sound3388 B hB hF
  have h3391 : mixedVector B (Sum.inr 3391) = Sparse.eval nodeValue3391 (mixedVector B) := by
    change mixedMoment B node3391 node3391Labels = _
    exact sound3391 B hB hF
  have h3392 : mixedVector B (Sum.inr 3392) = Sparse.eval nodeValue3392 (mixedVector B) := by
    change mixedMoment B node3392 node3392Labels = _
    exact sound3392 B hB hF
  have h3395 : mixedVector B (Sum.inr 3395) = Sparse.eval nodeValue3395 (mixedVector B) := by
    change mixedMoment B node3395 node3395Labels = _
    exact sound3395 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm319, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3388, h3391, h3392, h3395, h3535, h3544, h4084, reducedSource270] using sourceEq319 B hB

theorem rowSound270 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row270 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck270, numericCheck270, reducedZero270 B hB hF, mul_zero]

theorem reducedZero271 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource271 (mixedVector B) = 0 := by
  have h2021 : mixedVector B (Sum.inr 2021) = Sparse.eval nodeValue2021 (mixedVector B) := by
    change mixedMoment B node2021 node2021Labels = _
    exact sound2021 B hB hF
  have h2026 : mixedVector B (Sum.inr 2026) = Sparse.eval nodeValue2026 (mixedVector B) := by
    change mixedMoment B node2026 node2026Labels = _
    exact sound2026 B hB hF
  have h2028 : mixedVector B (Sum.inr 2028) = Sparse.eval nodeValue2028 (mixedVector B) := by
    change mixedMoment B node2028 node2028Labels = _
    exact sound2028 B hB hF
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm320, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2021, h2026, h2028, h2058, h2266, h3535, h4084, reducedSource271] using sourceEq320 B hB

theorem rowSound271 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row271 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck271, numericCheck271, reducedZero271 B hB hF, mul_zero]

theorem sourceRowsAt256 : MixedData.sourceRows (256 : Fin 2425) =
    MixedData.row256 := by decide +kernel

theorem sourceRowsAt257 : MixedData.sourceRows (257 : Fin 2425) =
    MixedData.row257 := by decide +kernel

theorem sourceRowsAt258 : MixedData.sourceRows (258 : Fin 2425) =
    MixedData.row258 := by decide +kernel

theorem sourceRowsAt259 : MixedData.sourceRows (259 : Fin 2425) =
    MixedData.row259 := by decide +kernel

theorem sourceRowsAt260 : MixedData.sourceRows (260 : Fin 2425) =
    MixedData.row260 := by decide +kernel

theorem sourceRowsAt261 : MixedData.sourceRows (261 : Fin 2425) =
    MixedData.row261 := by decide +kernel

theorem sourceRowsAt262 : MixedData.sourceRows (262 : Fin 2425) =
    MixedData.row262 := by decide +kernel

theorem sourceRowsAt263 : MixedData.sourceRows (263 : Fin 2425) =
    MixedData.row263 := by decide +kernel

theorem sourceRowsAt264 : MixedData.sourceRows (264 : Fin 2425) =
    MixedData.row264 := by decide +kernel

theorem sourceRowsAt265 : MixedData.sourceRows (265 : Fin 2425) =
    MixedData.row265 := by decide +kernel

theorem sourceRowsAt266 : MixedData.sourceRows (266 : Fin 2425) =
    MixedData.row266 := by decide +kernel

theorem sourceRowsAt267 : MixedData.sourceRows (267 : Fin 2425) =
    MixedData.row267 := by decide +kernel

theorem sourceRowsAt268 : MixedData.sourceRows (268 : Fin 2425) =
    MixedData.row268 := by decide +kernel

theorem sourceRowsAt269 : MixedData.sourceRows (269 : Fin 2425) =
    MixedData.row269 := by decide +kernel

theorem sourceRowsAt270 : MixedData.sourceRows (270 : Fin 2425) =
    MixedData.row270 := by decide +kernel

theorem sourceRowsAt271 : MixedData.sourceRows (271 : Fin 2425) =
    MixedData.row271 := by decide +kernel

theorem chunkSound16_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 16) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 256 ∨ k.val = 257 ∨ k.val = 258 ∨ k.val = 259 ∨ k.val = 260 ∨ k.val = 261 ∨ k.val = 262 ∨ k.val = 263 ∨ k.val = 264 ∨ k.val = 265 ∨ k.val = 266 ∨ k.val = 267 ∨ k.val = 268 ∨ k.val = 269 ∨ k.val = 270 ∨ k.val = 271 := by omega
  rcases heq with h256 | h257 | h258 | h259 | h260 | h261 | h262 | h263 | h264 | h265 | h266 | h267 | h268 | h269 | h270 | h271
  · have he : k = (256 : Fin 2425) := Fin.ext h256
    subst k
    rw [sourceRowsAt256]
    exact rowSound256 B hB hF
  · have he : k = (257 : Fin 2425) := Fin.ext h257
    subst k
    rw [sourceRowsAt257]
    exact rowSound257 B hB hF
  · have he : k = (258 : Fin 2425) := Fin.ext h258
    subst k
    rw [sourceRowsAt258]
    exact rowSound258 B hB hF
  · have he : k = (259 : Fin 2425) := Fin.ext h259
    subst k
    rw [sourceRowsAt259]
    exact rowSound259 B hB hF
  · have he : k = (260 : Fin 2425) := Fin.ext h260
    subst k
    rw [sourceRowsAt260]
    exact rowSound260 B hB hF
  · have he : k = (261 : Fin 2425) := Fin.ext h261
    subst k
    rw [sourceRowsAt261]
    exact rowSound261 B hB hF
  · have he : k = (262 : Fin 2425) := Fin.ext h262
    subst k
    rw [sourceRowsAt262]
    exact rowSound262 B hB hF
  · have he : k = (263 : Fin 2425) := Fin.ext h263
    subst k
    rw [sourceRowsAt263]
    exact rowSound263 B hB hF
  · have he : k = (264 : Fin 2425) := Fin.ext h264
    subst k
    rw [sourceRowsAt264]
    exact rowSound264 B hB hF
  · have he : k = (265 : Fin 2425) := Fin.ext h265
    subst k
    rw [sourceRowsAt265]
    exact rowSound265 B hB hF
  · have he : k = (266 : Fin 2425) := Fin.ext h266
    subst k
    rw [sourceRowsAt266]
    exact rowSound266 B hB hF
  · have he : k = (267 : Fin 2425) := Fin.ext h267
    subst k
    rw [sourceRowsAt267]
    exact rowSound267_e B hB hF
  · have he : k = (268 : Fin 2425) := Fin.ext h268
    subst k
    rw [sourceRowsAt268]
    exact rowSound268 B hB hF
  · have he : k = (269 : Fin 2425) := Fin.ext h269
    subst k
    rw [sourceRowsAt269]
    exact rowSound269_e B hB hF
  · have he : k = (270 : Fin 2425) := Fin.ext h270
    subst k
    rw [sourceRowsAt270]
    exact rowSound270 B hB hF
  · have he : k = (271 : Fin 2425) := Fin.ext h271
    subst k
    rw [sourceRowsAt271]
    exact rowSound271 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e_oai
