-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:06:50.682139+00:00
-- url     : https://prove2.me/submissions/3bcf0268-90da-47d1-8a0f-6a452f9aa1ad

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E108
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5465_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw248 raw248Labels = mixedMoment B node2605 node2605Labels := by
  calc
    mixedMoment B raw248 raw248Labels = mixedMoment B raw248step0 raw248step0Labels := by
      have ha : raw248step0 = (fun i j => raw248 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw248step0 raw248; decide +kernel
      have hl : raw248step0Labels = raw248Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw248 raw248Labels permutation8 permutation5
    mixedMoment B raw248step0 raw248step0Labels = mixedMoment B raw248step1 raw248step1Labels := by
      have ha : raw248step1 = raw248step0 := by apply Matrix.ext; unfold raw248step1 raw248step0; decide +kernel
      have hl : raw248step0Labels = labelEmbedding1 ∘ raw248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw248step0 raw248step0Labels raw248step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2605 node2605Labels := by rfl

theorem canonical249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw249 raw249Labels = mixedMoment B node344 node344Labels := by
  calc
    mixedMoment B raw249 raw249Labels = mixedMoment B raw249step0 raw249step0Labels := by
      have ha : raw249step0 = (fun i j => raw249 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw249step0 raw249; decide +kernel
      have hl : raw249step0Labels = raw249Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw249 raw249Labels permutation8 permutation5
    _ = mixedMoment B node344 node344Labels := by rfl

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

theorem canonical17663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17663 raw17663Labels = mixedMoment B node5487 node5487Labels := by
  calc
    mixedMoment B raw17663 raw17663Labels = mixedMoment B raw17663step0 raw17663step0Labels := by
      have hz : ∀ j, raw17663 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17663step0 = (fun i j => raw17663 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17663step0 raw17663; decide +kernel
      have hl : raw17663step0Labels = raw17663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17663 raw17663Labels permutation434 hz
    mixedMoment B raw17663step0 raw17663step0Labels = mixedMoment B raw17663step1 raw17663step1Labels := by
      have hz : ∀ j, raw17663step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17663step1 = (fun i j => raw17663step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17663step1 raw17663step0; decide +kernel
      have hl : raw17663step1Labels = raw17663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17663step0 raw17663step0Labels permutation80 hz
    mixedMoment B raw17663step1 raw17663step1Labels = mixedMoment B raw17663step2 raw17663step2Labels := by
      have ha : raw17663step2 = (fun i j => raw17663step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17663step2 raw17663step1; decide +kernel
      have hl : raw17663step2Labels = raw17663step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17663step1 raw17663step1Labels permutation14 permutation2
    _ = mixedMoment B node5487 node5487Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17668 raw17668Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw17668 raw17668Labels = mixedMoment B raw17668step0 raw17668step0Labels := by
      have hz : ∀ j, raw17668 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17668step0 = (fun i j => raw17668 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17668step0 raw17668; decide +kernel
      have hl : raw17668step0Labels = raw17668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17668 raw17668Labels permutation434 hz
    _ = mixedMoment B node5465 node5465Labels := by rfl

theorem canonical17672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17672 raw17672Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw17672 raw17672Labels = mixedMoment B raw17672step0 raw17672step0Labels := by
      have hz : ∀ j, raw17672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17672step0 = (fun i j => raw17672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17672step0 raw17672; decide +kernel
      have hl : raw17672step0Labels = raw17672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17672 raw17672Labels permutation346 hz
    _ = mixedMoment B node5465 node5465Labels := by rfl

theorem canonical17675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17675 raw17675Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw17675 raw17675Labels = mixedMoment B raw17675step0 raw17675step0Labels := by
      have hz : ∀ j, raw17675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17675step0 = (fun i j => raw17675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17675step0 raw17675; decide +kernel
      have hl : raw17675step0Labels = raw17675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17675 raw17675Labels permutation434 hz
    mixedMoment B raw17675step0 raw17675step0Labels = mixedMoment B raw17675step1 raw17675step1Labels := by
      have hz : ∀ j, raw17675step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17675step1 = (fun i j => raw17675step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17675step1 raw17675step0; decide +kernel
      have hl : raw17675step1Labels = raw17675step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17675step0 raw17675step0Labels permutation80 hz
    mixedMoment B raw17675step1 raw17675step1Labels = mixedMoment B raw17675step2 raw17675step2Labels := by
      have ha : raw17675step2 = (fun i j => raw17675step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17675step2 raw17675step1; decide +kernel
      have hl : raw17675step2Labels = raw17675step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17675step1 raw17675step1Labels permutation8 permutation3
    mixedMoment B raw17675step2 raw17675step2Labels = mixedMoment B raw17675step3 raw17675step3Labels := by
      have ha : raw17675step3 = raw17675step2 := by apply Matrix.ext; unfold raw17675step3 raw17675step2; decide +kernel
      have hl : raw17675step2Labels = labelEmbedding6 ∘ raw17675step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17675step2 raw17675step2Labels raw17675step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

theorem canonical17677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17677 raw17677Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw17677 raw17677Labels = mixedMoment B raw17677step0 raw17677step0Labels := by
      have hz : ∀ j, raw17677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17677step0 = (fun i j => raw17677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17677step0 raw17677; decide +kernel
      have hl : raw17677step0Labels = raw17677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17677 raw17677Labels permutation434 hz
    mixedMoment B raw17677step0 raw17677step0Labels = mixedMoment B raw17677step1 raw17677step1Labels := by
      have ha : raw17677step1 = (fun i j => raw17677step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17677step1 raw17677step0; decide +kernel
      have hl : raw17677step1Labels = raw17677step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17677step0 raw17677step0Labels permutation127 permutation2
    mixedMoment B raw17677step1 raw17677step1Labels = mixedMoment B raw17677step2 raw17677step2Labels := by
      have ha : raw17677step2 = -raw17677step1 := by apply Matrix.ext; change ∀ i j, raw17677step2 i j = -(raw17677step1 i j); unfold raw17677step2 raw17677step1; decide +kernel
      have hl : raw17677step2Labels = raw17677step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5465 node5465Labels := by rfl

theorem canonical17678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17678 raw17678Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw17678 raw17678Labels = mixedMoment B raw17678step0 raw17678step0Labels := by
      have hz : ∀ j, raw17678 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17678step0 = (fun i j => raw17678 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17678step0 raw17678; decide +kernel
      have hl : raw17678step0Labels = raw17678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17678 raw17678Labels permutation346 hz
    mixedMoment B raw17678step0 raw17678step0Labels = mixedMoment B raw17678step1 raw17678step1Labels := by
      have ha : raw17678step1 = (fun i j => raw17678step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17678step1 raw17678step0; decide +kernel
      have hl : raw17678step1Labels = raw17678step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17678step0 raw17678step0Labels permutation127 permutation2
    mixedMoment B raw17678step1 raw17678step1Labels = mixedMoment B raw17678step2 raw17678step2Labels := by
      have ha : raw17678step2 = -raw17678step1 := by apply Matrix.ext; change ∀ i j, raw17678step2 i j = -(raw17678step1 i j); unfold raw17678step2 raw17678step1; decide +kernel
      have hl : raw17678step2Labels = raw17678step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5465 node5465Labels := by rfl

theorem canonical17679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17679 raw17679Labels = mixedMoment B node5487 node5487Labels := by
  calc
    mixedMoment B raw17679 raw17679Labels = mixedMoment B raw17679step0 raw17679step0Labels := by
      have hz : ∀ j, raw17679 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17679step0 = (fun i j => raw17679 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17679step0 raw17679; decide +kernel
      have hl : raw17679step0Labels = raw17679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17679 raw17679Labels permutation434 hz
    mixedMoment B raw17679step0 raw17679step0Labels = mixedMoment B raw17679step1 raw17679step1Labels := by
      have hz : ∀ j, raw17679step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17679step1 = (fun i j => raw17679step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17679step1 raw17679step0; decide +kernel
      have hl : raw17679step1Labels = raw17679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17679step0 raw17679step0Labels permutation80 hz
    mixedMoment B raw17679step1 raw17679step1Labels = mixedMoment B raw17679step2 raw17679step2Labels := by
      have ha : raw17679step2 = (fun i j => raw17679step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17679step2 raw17679step1; decide +kernel
      have hl : raw17679step2Labels = raw17679step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17679step1 raw17679step1Labels permutation9 permutation2
    _ = mixedMoment B node5487 node5487Labels := by rfl

theorem canonical17680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17680 raw17680Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw17680 raw17680Labels = mixedMoment B raw17680step0 raw17680step0Labels := by
      have hz : ∀ j, raw17680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17680step0 = (fun i j => raw17680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17680step0 raw17680; decide +kernel
      have hl : raw17680step0Labels = raw17680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17680 raw17680Labels permutation434 hz
    mixedMoment B raw17680step0 raw17680step0Labels = mixedMoment B raw17680step1 raw17680step1Labels := by
      have hz : ∀ j, raw17680step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17680step1 = (fun i j => raw17680step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17680step1 raw17680step0; decide +kernel
      have hl : raw17680step1Labels = raw17680step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17680step0 raw17680step0Labels permutation80 hz
    mixedMoment B raw17680step1 raw17680step1Labels = mixedMoment B raw17680step2 raw17680step2Labels := by
      have ha : raw17680step2 = (fun i j => raw17680step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17680step2 raw17680step1; decide +kernel
      have hl : raw17680step2Labels = raw17680step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17680step1 raw17680step1Labels permutation30 permutation3
    mixedMoment B raw17680step2 raw17680step2Labels = mixedMoment B raw17680step3 raw17680step3Labels := by
      have ha : raw17680step3 = -raw17680step2 := by apply Matrix.ext; change ∀ i j, raw17680step3 i j = -(raw17680step2 i j); unfold raw17680step3 raw17680step2; decide +kernel
      have hl : raw17680step3Labels = raw17680step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17680step3 raw17680step3Labels = mixedMoment B raw17680step4 raw17680step4Labels := by
      have ha : raw17680step4 = raw17680step3 := by apply Matrix.ext; unfold raw17680step4 raw17680step3; decide +kernel
      have hl : raw17680step3Labels = labelEmbedding6 ∘ raw17680step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17680step3 raw17680step3Labels raw17680step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

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

theorem canonical1923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1923 raw1923Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw1923 raw1923Labels = mixedMoment B raw1923step0 raw1923step0Labels := by
      have ha : raw1923step0 = (fun i j => raw1923 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1923step0 raw1923; decide +kernel
      have hl : raw1923step0Labels = raw1923Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1923 raw1923Labels permutation32 permutation4
    mixedMoment B raw1923step0 raw1923step0Labels = mixedMoment B raw1923step1 raw1923step1Labels := by
      have ha : raw1923step1 = raw1923step0 := by apply Matrix.ext; unfold raw1923step1 raw1923step0; decide +kernel
      have hl : raw1923step0Labels = labelEmbedding7 ∘ raw1923step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1923step0 raw1923step0Labels raw1923step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

theorem canonical1924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1924 raw1924Labels = mixedMoment B node2342 node2342Labels := by
  calc
    mixedMoment B raw1924 raw1924Labels = mixedMoment B raw1924step0 raw1924step0Labels := by
      have ha : raw1924step0 = (fun i j => raw1924 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1924step0 raw1924; decide +kernel
      have hl : raw1924step0Labels = raw1924Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1924 raw1924Labels permutation32 permutation4
    _ = mixedMoment B node2342 node2342Labels := by rfl

theorem canonical1925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1925 raw1925Labels = mixedMoment B node3421 node3421Labels := by
  calc
    mixedMoment B raw1925 raw1925Labels = mixedMoment B raw1925step0 raw1925step0Labels := by
      have ha : raw1925step0 = (fun i j => raw1925 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1925step0 raw1925; decide +kernel
      have hl : raw1925step0Labels = raw1925Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1925 raw1925Labels permutation32 permutation6
    mixedMoment B raw1925step0 raw1925step0Labels = mixedMoment B raw1925step1 raw1925step1Labels := by
      have ha : raw1925step1 = -raw1925step0 := by apply Matrix.ext; change ∀ i j, raw1925step1 i j = -(raw1925step0 i j); unfold raw1925step1 raw1925step0; decide +kernel
      have hl : raw1925step1Labels = raw1925step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1925step1 raw1925step1Labels = mixedMoment B raw1925step2 raw1925step2Labels := by
      have ha : raw1925step2 = raw1925step1 := by apply Matrix.ext; unfold raw1925step2 raw1925step1; decide +kernel
      have hl : raw1925step1Labels = labelEmbedding1 ∘ raw1925step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1925step1 raw1925step1Labels raw1925step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3421 node3421Labels := by rfl

theorem canonical1926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1926 raw1926Labels = mixedMoment B node4952 node4952Labels := by
  calc
    mixedMoment B raw1926 raw1926Labels = mixedMoment B raw1926step0 raw1926step0Labels := by
      have ha : raw1926step0 = (fun i j => raw1926 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1926step0 raw1926; decide +kernel
      have hl : raw1926step0Labels = raw1926Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1926 raw1926Labels permutation8 permutation4
    mixedMoment B raw1926step0 raw1926step0Labels = mixedMoment B raw1926step1 raw1926step1Labels := by
      have ha : raw1926step1 = raw1926step0 := by apply Matrix.ext; unfold raw1926step1 raw1926step0; decide +kernel
      have hl : raw1926step0Labels = labelEmbedding7 ∘ raw1926step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1926step0 raw1926step0Labels raw1926step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4952 node4952Labels := by rfl

theorem canonical1927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1927 raw1927Labels = mixedMoment B node2344 node2344Labels := by
  calc
    mixedMoment B raw1927 raw1927Labels = mixedMoment B raw1927step0 raw1927step0Labels := by
      have ha : raw1927step0 = (fun i j => raw1927 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1927step0 raw1927; decide +kernel
      have hl : raw1927step0Labels = raw1927Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1927 raw1927Labels permutation8 permutation4
    _ = mixedMoment B node2344 node2344Labels := by rfl

theorem canonical1928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1928 raw1928Labels = mixedMoment B node3422 node3422Labels := by
  calc
    mixedMoment B raw1928 raw1928Labels = mixedMoment B raw1928step0 raw1928step0Labels := by
      have ha : raw1928step0 = (fun i j => raw1928 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1928step0 raw1928; decide +kernel
      have hl : raw1928step0Labels = raw1928Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1928 raw1928Labels permutation31 permutation6
    mixedMoment B raw1928step0 raw1928step0Labels = mixedMoment B raw1928step1 raw1928step1Labels := by
      have ha : raw1928step1 = raw1928step0 := by apply Matrix.ext; unfold raw1928step1 raw1928step0; decide +kernel
      have hl : raw1928step0Labels = labelEmbedding1 ∘ raw1928step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1928step0 raw1928step0Labels raw1928step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3422 node3422Labels := by rfl

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

theorem canonical2217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2217 raw2217Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw2217 raw2217Labels = mixedMoment B raw2217step0 raw2217step0Labels := by
      have ha : raw2217step0 = (fun i j => raw2217 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2217step0 raw2217; decide +kernel
      have hl : raw2217step0Labels = raw2217Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2217 raw2217Labels permutation8 permutation4
    mixedMoment B raw2217step0 raw2217step0Labels = mixedMoment B raw2217step1 raw2217step1Labels := by
      have ha : raw2217step1 = raw2217step0 := by apply Matrix.ext; unfold raw2217step1 raw2217step0; decide +kernel
      have hl : raw2217step0Labels = labelEmbedding7 ∘ raw2217step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2217step0 raw2217step0Labels raw2217step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

theorem canonical2218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2218 raw2218Labels = mixedMoment B node2605 node2605Labels := by
  calc
    mixedMoment B raw2218 raw2218Labels = mixedMoment B raw2218step0 raw2218step0Labels := by
      have ha : raw2218step0 = (fun i j => raw2218 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2218step0 raw2218; decide +kernel
      have hl : raw2218step0Labels = raw2218Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2218 raw2218Labels permutation8 permutation4
    _ = mixedMoment B node2605 node2605Labels := by rfl

theorem canonical2219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2219 raw2219Labels = mixedMoment B node3616 node3616Labels := by
  calc
    mixedMoment B raw2219 raw2219Labels = mixedMoment B raw2219step0 raw2219step0Labels := by
      have ha : raw2219step0 = (fun i j => raw2219 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2219step0 raw2219; decide +kernel
      have hl : raw2219step0Labels = raw2219Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2219 raw2219Labels permutation8 permutation6
    mixedMoment B raw2219step0 raw2219step0Labels = mixedMoment B raw2219step1 raw2219step1Labels := by
      have ha : raw2219step1 = -raw2219step0 := by apply Matrix.ext; change ∀ i j, raw2219step1 i j = -(raw2219step0 i j); unfold raw2219step1 raw2219step0; decide +kernel
      have hl : raw2219step1Labels = raw2219step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2219step1 raw2219step1Labels = mixedMoment B raw2219step2 raw2219step2Labels := by
      have ha : raw2219step2 = raw2219step1 := by apply Matrix.ext; unfold raw2219step2 raw2219step1; decide +kernel
      have hl : raw2219step1Labels = labelEmbedding1 ∘ raw2219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2219step1 raw2219step1Labels raw2219step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3616 node3616Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2772 raw2772Labels = mixedMoment B node5487 node5487Labels := by
  calc
    mixedMoment B raw2772 raw2772Labels = mixedMoment B raw2772step0 raw2772step0Labels := by
      have hz : ∀ j, raw2772 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2772step0 = (fun i j => raw2772 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2772step0 raw2772; decide +kernel
      have hl : raw2772step0Labels = raw2772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2772 raw2772Labels permutation434 hz
    mixedMoment B raw2772step0 raw2772step0Labels = mixedMoment B raw2772step1 raw2772step1Labels := by
      have hz : ∀ j, raw2772step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2772step1 = (fun i j => raw2772step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2772step1 raw2772step0; decide +kernel
      have hl : raw2772step1Labels = raw2772step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2772step0 raw2772step0Labels permutation80 hz
    _ = mixedMoment B node5487 node5487Labels := by rfl

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

theorem canonical27590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27590 raw27590Labels = mixedMoment B node4952 node4952Labels := by
  calc
    mixedMoment B raw27590 raw27590Labels = mixedMoment B raw27590step0 raw27590step0Labels := by
      have hz : ∀ j, raw27590 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27590step0 = (fun i j => raw27590 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27590step0 raw27590; decide +kernel
      have hl : raw27590step0Labels = raw27590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27590 raw27590Labels permutation434 hz
    mixedMoment B raw27590step0 raw27590step0Labels = mixedMoment B raw27590step1 raw27590step1Labels := by
      have hz : ∀ j, raw27590step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27590step1 = (fun i j => raw27590step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27590step1 raw27590step0; decide +kernel
      have hl : raw27590step1Labels = raw27590step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27590step0 raw27590step0Labels permutation80 hz
    mixedMoment B raw27590step1 raw27590step1Labels = mixedMoment B raw27590step2 raw27590step2Labels := by
      have ha : raw27590step2 = (fun i j => raw27590step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27590step2 raw27590step1; decide +kernel
      have hl : raw27590step2Labels = raw27590step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27590step1 raw27590step1Labels permutation8 permutation3
    mixedMoment B raw27590step2 raw27590step2Labels = mixedMoment B raw27590step3 raw27590step3Labels := by
      have ha : raw27590step3 = raw27590step2 := by apply Matrix.ext; unfold raw27590step3 raw27590step2; decide +kernel
      have hl : raw27590step2Labels = labelEmbedding6 ∘ raw27590step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27590step2 raw27590step2Labels raw27590step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4952 node4952Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical231
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29650 raw29650Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw29650 raw29650Labels = mixedMoment B raw29650step0 raw29650step0Labels := by
      have hz : ∀ j, raw29650 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29650step0 = (fun i j => raw29650 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29650step0 raw29650; decide +kernel
      have hl : raw29650step0Labels = raw29650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29650 raw29650Labels permutation434 hz
    mixedMoment B raw29650step0 raw29650step0Labels = mixedMoment B raw29650step1 raw29650step1Labels := by
      have ha : raw29650step1 = (fun i j => raw29650step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29650step1 raw29650step0; decide +kernel
      have hl : raw29650step1Labels = raw29650step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29650step0 raw29650step0Labels permutation32 permutation3
    mixedMoment B raw29650step1 raw29650step1Labels = mixedMoment B raw29650step2 raw29650step2Labels := by
      have ha : raw29650step2 = raw29650step1 := by apply Matrix.ext; unfold raw29650step2 raw29650step1; decide +kernel
      have hl : raw29650step1Labels = labelEmbedding6 ∘ raw29650step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29650step1 raw29650step1Labels raw29650step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

theorem canonical29653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29653 raw29653Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw29653 raw29653Labels = mixedMoment B raw29653step0 raw29653step0Labels := by
      have hz : ∀ j, raw29653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29653step0 = (fun i j => raw29653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29653step0 raw29653; decide +kernel
      have hl : raw29653step0Labels = raw29653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29653 raw29653Labels permutation346 hz
    mixedMoment B raw29653step0 raw29653step0Labels = mixedMoment B raw29653step1 raw29653step1Labels := by
      have ha : raw29653step1 = (fun i j => raw29653step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29653step1 raw29653step0; decide +kernel
      have hl : raw29653step1Labels = raw29653step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29653step0 raw29653step0Labels permutation32 permutation3
    mixedMoment B raw29653step1 raw29653step1Labels = mixedMoment B raw29653step2 raw29653step2Labels := by
      have ha : raw29653step2 = raw29653step1 := by apply Matrix.ext; unfold raw29653step2 raw29653step1; decide +kernel
      have hl : raw29653step1Labels = labelEmbedding6 ∘ raw29653step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29653step1 raw29653step1Labels raw29653step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

theorem canonical29656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29656 raw29656Labels = mixedMoment B node4952 node4952Labels := by
  calc
    mixedMoment B raw29656 raw29656Labels = mixedMoment B raw29656step0 raw29656step0Labels := by
      have hz : ∀ j, raw29656 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29656step0 = (fun i j => raw29656 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29656step0 raw29656; decide +kernel
      have hl : raw29656step0Labels = raw29656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29656 raw29656Labels permutation434 hz
    mixedMoment B raw29656step0 raw29656step0Labels = mixedMoment B raw29656step1 raw29656step1Labels := by
      have hz : ∀ j, raw29656step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29656step1 = (fun i j => raw29656step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29656step1 raw29656step0; decide +kernel
      have hl : raw29656step1Labels = raw29656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29656step0 raw29656step0Labels permutation80 hz
    mixedMoment B raw29656step1 raw29656step1Labels = mixedMoment B raw29656step2 raw29656step2Labels := by
      have ha : raw29656step2 = (fun i j => raw29656step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29656step2 raw29656step1; decide +kernel
      have hl : raw29656step2Labels = raw29656step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29656step1 raw29656step1Labels permutation9 permutation3
    mixedMoment B raw29656step2 raw29656step2Labels = mixedMoment B raw29656step3 raw29656step3Labels := by
      have ha : raw29656step3 = raw29656step2 := by apply Matrix.ext; unfold raw29656step3 raw29656step2; decide +kernel
      have hl : raw29656step2Labels = labelEmbedding6 ∘ raw29656step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29656step2 raw29656step2Labels raw29656step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4952 node4952Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical275
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35222 raw35222Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw35222 raw35222Labels = mixedMoment B raw35222step0 raw35222step0Labels := by
      have hz : ∀ j, raw35222 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35222step0 = (fun i j => raw35222 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35222step0 raw35222; decide +kernel
      have hl : raw35222step0Labels = raw35222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35222 raw35222Labels permutation434 hz
    mixedMoment B raw35222step0 raw35222step0Labels = mixedMoment B raw35222step1 raw35222step1Labels := by
      have hz : ∀ j, raw35222step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35222step1 = (fun i j => raw35222step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35222step1 raw35222step0; decide +kernel
      have hl : raw35222step1Labels = raw35222step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35222step0 raw35222step0Labels permutation80 hz
    mixedMoment B raw35222step1 raw35222step1Labels = mixedMoment B raw35222step2 raw35222step2Labels := by
      have ha : raw35222step2 = (fun i j => raw35222step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35222step2 raw35222step1; decide +kernel
      have hl : raw35222step2Labels = raw35222step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35222step1 raw35222step1Labels permutation14 permutation3
    mixedMoment B raw35222step2 raw35222step2Labels = mixedMoment B raw35222step3 raw35222step3Labels := by
      have ha : raw35222step3 = raw35222step2 := by apply Matrix.ext; unfold raw35222step3 raw35222step2; decide +kernel
      have hl : raw35222step2Labels = labelEmbedding6 ∘ raw35222step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35222step2 raw35222step2Labels raw35222step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

theorem canonical35223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35223 raw35223Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw35223 raw35223Labels = mixedMoment B raw35223step0 raw35223step0Labels := by
      have hz : ∀ j, raw35223 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35223step0 = (fun i j => raw35223 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35223step0 raw35223; decide +kernel
      have hl : raw35223step0Labels = raw35223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35223 raw35223Labels permutation434 hz
    mixedMoment B raw35223step0 raw35223step0Labels = mixedMoment B raw35223step1 raw35223step1Labels := by
      have ha : raw35223step1 = (fun i j => raw35223step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35223step1 raw35223step0; decide +kernel
      have hl : raw35223step1Labels = raw35223step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35223step0 raw35223step0Labels permutation126 permutation2
    mixedMoment B raw35223step1 raw35223step1Labels = mixedMoment B raw35223step2 raw35223step2Labels := by
      have ha : raw35223step2 = -raw35223step1 := by apply Matrix.ext; change ∀ i j, raw35223step2 i j = -(raw35223step1 i j); unfold raw35223step2 raw35223step1; decide +kernel
      have hl : raw35223step2Labels = raw35223step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5465 node5465Labels := by rfl

theorem canonical35224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35224 raw35224Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw35224 raw35224Labels = mixedMoment B raw35224step0 raw35224step0Labels := by
      have hz : ∀ j, raw35224 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35224step0 = (fun i j => raw35224 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35224step0 raw35224; decide +kernel
      have hl : raw35224step0Labels = raw35224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35224 raw35224Labels permutation346 hz
    mixedMoment B raw35224step0 raw35224step0Labels = mixedMoment B raw35224step1 raw35224step1Labels := by
      have ha : raw35224step1 = (fun i j => raw35224step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35224step1 raw35224step0; decide +kernel
      have hl : raw35224step1Labels = raw35224step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35224step0 raw35224step0Labels permutation126 permutation2
    mixedMoment B raw35224step1 raw35224step1Labels = mixedMoment B raw35224step2 raw35224step2Labels := by
      have ha : raw35224step2 = -raw35224step1 := by apply Matrix.ext; change ∀ i j, raw35224step2 i j = -(raw35224step1 i j); unfold raw35224step2 raw35224step1; decide +kernel
      have hl : raw35224step2Labels = raw35224step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5465 node5465Labels := by rfl

theorem canonical35225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35225 raw35225Labels = mixedMoment B node5487 node5487Labels := by
  calc
    mixedMoment B raw35225 raw35225Labels = mixedMoment B raw35225step0 raw35225step0Labels := by
      have hz : ∀ j, raw35225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35225step0 = (fun i j => raw35225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35225step0 raw35225; decide +kernel
      have hl : raw35225step0Labels = raw35225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35225 raw35225Labels permutation434 hz
    mixedMoment B raw35225step0 raw35225step0Labels = mixedMoment B raw35225step1 raw35225step1Labels := by
      have hz : ∀ j, raw35225step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35225step1 = (fun i j => raw35225step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35225step1 raw35225step0; decide +kernel
      have hl : raw35225step1Labels = raw35225step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35225step0 raw35225step0Labels permutation80 hz
    mixedMoment B raw35225step1 raw35225step1Labels = mixedMoment B raw35225step2 raw35225step2Labels := by
      have ha : raw35225step2 = (fun i j => raw35225step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35225step2 raw35225step1; decide +kernel
      have hl : raw35225step2Labels = raw35225step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35225step1 raw35225step1Labels permutation15 permutation2
    _ = mixedMoment B node5487 node5487Labels := by rfl

theorem canonical35226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35226 raw35226Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw35226 raw35226Labels = mixedMoment B raw35226step0 raw35226step0Labels := by
      have hz : ∀ j, raw35226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35226step0 = (fun i j => raw35226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35226step0 raw35226; decide +kernel
      have hl : raw35226step0Labels = raw35226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35226 raw35226Labels permutation434 hz
    mixedMoment B raw35226step0 raw35226step0Labels = mixedMoment B raw35226step1 raw35226step1Labels := by
      have ha : raw35226step1 = (fun i j => raw35226step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35226step1 raw35226step0; decide +kernel
      have hl : raw35226step1Labels = raw35226step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35226step0 raw35226step0Labels permutation56 permutation3
    mixedMoment B raw35226step1 raw35226step1Labels = mixedMoment B raw35226step2 raw35226step2Labels := by
      have ha : raw35226step2 = raw35226step1 := by apply Matrix.ext; unfold raw35226step2 raw35226step1; decide +kernel
      have hl : raw35226step1Labels = labelEmbedding6 ∘ raw35226step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35226step1 raw35226step1Labels raw35226step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

theorem canonical35227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35227 raw35227Labels = mixedMoment B node5457 node5457Labels := by
  calc
    mixedMoment B raw35227 raw35227Labels = mixedMoment B raw35227step0 raw35227step0Labels := by
      have ha : raw35227step0 = (fun i j => raw35227 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35227step0 raw35227; decide +kernel
      have hl : raw35227step0Labels = raw35227Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35227 raw35227Labels permutation158 permutation3
    mixedMoment B raw35227step0 raw35227step0Labels = mixedMoment B raw35227step1 raw35227step1Labels := by
      have ha : raw35227step1 = raw35227step0 := by apply Matrix.ext; unfold raw35227step1 raw35227step0; decide +kernel
      have hl : raw35227step0Labels = labelEmbedding6 ∘ raw35227step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35227step0 raw35227step0Labels raw35227step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5457 node5457Labels := by rfl

theorem canonical35228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35228 raw35228Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw35228 raw35228Labels = mixedMoment B raw35228step0 raw35228step0Labels := by
      have hz : ∀ j, raw35228 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35228step0 = (fun i j => raw35228 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35228step0 raw35228; decide +kernel
      have hl : raw35228step0Labels = raw35228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35228 raw35228Labels permutation434 hz
    mixedMoment B raw35228step0 raw35228step0Labels = mixedMoment B raw35228step1 raw35228step1Labels := by
      have ha : raw35228step1 = (fun i j => raw35228step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35228step1 raw35228step0; decide +kernel
      have hl : raw35228step1Labels = raw35228step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35228step0 raw35228step0Labels permutation33 permutation2
    _ = mixedMoment B node5465 node5465Labels := by rfl

theorem canonical35229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35229 raw35229Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw35229 raw35229Labels = mixedMoment B raw35229step0 raw35229step0Labels := by
      have hz : ∀ j, raw35229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35229step0 = (fun i j => raw35229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35229step0 raw35229; decide +kernel
      have hl : raw35229step0Labels = raw35229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35229 raw35229Labels permutation346 hz
    mixedMoment B raw35229step0 raw35229step0Labels = mixedMoment B raw35229step1 raw35229step1Labels := by
      have ha : raw35229step1 = (fun i j => raw35229step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35229step1 raw35229step0; decide +kernel
      have hl : raw35229step1Labels = raw35229step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35229step0 raw35229step0Labels permutation56 permutation3
    mixedMoment B raw35229step1 raw35229step1Labels = mixedMoment B raw35229step2 raw35229step2Labels := by
      have ha : raw35229step2 = raw35229step1 := by apply Matrix.ext; unfold raw35229step2 raw35229step1; decide +kernel
      have hl : raw35229step1Labels = labelEmbedding6 ∘ raw35229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35229step1 raw35229step1Labels raw35229step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

theorem canonical35230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35230 raw35230Labels = mixedMoment B node5457 node5457Labels := by
  calc
    mixedMoment B raw35230 raw35230Labels = mixedMoment B raw35230step0 raw35230step0Labels := by
      have ha : raw35230step0 = (fun i j => raw35230 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35230step0 raw35230; decide +kernel
      have hl : raw35230step0Labels = raw35230Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35230 raw35230Labels permutation152 permutation3
    mixedMoment B raw35230step0 raw35230step0Labels = mixedMoment B raw35230step1 raw35230step1Labels := by
      have ha : raw35230step1 = raw35230step0 := by apply Matrix.ext; unfold raw35230step1 raw35230step0; decide +kernel
      have hl : raw35230step0Labels = labelEmbedding6 ∘ raw35230step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35230step0 raw35230step0Labels raw35230step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5457 node5457Labels := by rfl

theorem canonical35231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35231 raw35231Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw35231 raw35231Labels = mixedMoment B raw35231step0 raw35231step0Labels := by
      have hz : ∀ j, raw35231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35231step0 = (fun i j => raw35231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35231step0 raw35231; decide +kernel
      have hl : raw35231step0Labels = raw35231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35231 raw35231Labels permutation346 hz
    mixedMoment B raw35231step0 raw35231step0Labels = mixedMoment B raw35231step1 raw35231step1Labels := by
      have ha : raw35231step1 = (fun i j => raw35231step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35231step1 raw35231step0; decide +kernel
      have hl : raw35231step1Labels = raw35231step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35231step0 raw35231step0Labels permutation33 permutation2
    _ = mixedMoment B node5465 node5465Labels := by rfl

theorem canonical35232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35232 raw35232Labels = mixedMoment B node4952 node4952Labels := by
  calc
    mixedMoment B raw35232 raw35232Labels = mixedMoment B raw35232step0 raw35232step0Labels := by
      have hz : ∀ j, raw35232 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35232step0 = (fun i j => raw35232 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35232step0 raw35232; decide +kernel
      have hl : raw35232step0Labels = raw35232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35232 raw35232Labels permutation434 hz
    mixedMoment B raw35232step0 raw35232step0Labels = mixedMoment B raw35232step1 raw35232step1Labels := by
      have hz : ∀ j, raw35232step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35232step1 = (fun i j => raw35232step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35232step1 raw35232step0; decide +kernel
      have hl : raw35232step1Labels = raw35232step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35232step0 raw35232step0Labels permutation80 hz
    mixedMoment B raw35232step1 raw35232step1Labels = mixedMoment B raw35232step2 raw35232step2Labels := by
      have ha : raw35232step2 = (fun i j => raw35232step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35232step2 raw35232step1; decide +kernel
      have hl : raw35232step2Labels = raw35232step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35232step1 raw35232step1Labels permutation15 permutation3
    mixedMoment B raw35232step2 raw35232step2Labels = mixedMoment B raw35232step3 raw35232step3Labels := by
      have ha : raw35232step3 = raw35232step2 := by apply Matrix.ext; unfold raw35232step3 raw35232step2; decide +kernel
      have hl : raw35232step2Labels = labelEmbedding6 ∘ raw35232step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35232step2 raw35232step2Labels raw35232step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4952 node4952Labels := by rfl

theorem canonical35233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35233 raw35233Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw35233 raw35233Labels = mixedMoment B raw35233step0 raw35233step0Labels := by
      have hz : ∀ j, raw35233 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35233step0 = (fun i j => raw35233 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35233step0 raw35233; decide +kernel
      have hl : raw35233step0Labels = raw35233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35233 raw35233Labels permutation434 hz
    mixedMoment B raw35233step0 raw35233step0Labels = mixedMoment B raw35233step1 raw35233step1Labels := by
      have ha : raw35233step1 = (fun i j => raw35233step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35233step1 raw35233step0; decide +kernel
      have hl : raw35233step1Labels = raw35233step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35233step0 raw35233step0Labels permutation126 permutation3
    mixedMoment B raw35233step1 raw35233step1Labels = mixedMoment B raw35233step2 raw35233step2Labels := by
      have ha : raw35233step2 = -raw35233step1 := by apply Matrix.ext; change ∀ i j, raw35233step2 i j = -(raw35233step1 i j); unfold raw35233step2 raw35233step1; decide +kernel
      have hl : raw35233step2Labels = raw35233step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35233step2 raw35233step2Labels = mixedMoment B raw35233step3 raw35233step3Labels := by
      have ha : raw35233step3 = raw35233step2 := by apply Matrix.ext; unfold raw35233step3 raw35233step2; decide +kernel
      have hl : raw35233step2Labels = labelEmbedding6 ∘ raw35233step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35233step2 raw35233step2Labels raw35233step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

theorem canonical35234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35234 raw35234Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw35234 raw35234Labels = mixedMoment B raw35234step0 raw35234step0Labels := by
      have hz : ∀ j, raw35234 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35234step0 = (fun i j => raw35234 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35234step0 raw35234; decide +kernel
      have hl : raw35234step0Labels = raw35234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35234 raw35234Labels permutation346 hz
    mixedMoment B raw35234step0 raw35234step0Labels = mixedMoment B raw35234step1 raw35234step1Labels := by
      have ha : raw35234step1 = (fun i j => raw35234step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35234step1 raw35234step0; decide +kernel
      have hl : raw35234step1Labels = raw35234step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35234step0 raw35234step0Labels permutation126 permutation3
    mixedMoment B raw35234step1 raw35234step1Labels = mixedMoment B raw35234step2 raw35234step2Labels := by
      have ha : raw35234step2 = -raw35234step1 := by apply Matrix.ext; change ∀ i j, raw35234step2 i j = -(raw35234step1 i j); unfold raw35234step2 raw35234step1; decide +kernel
      have hl : raw35234step2Labels = raw35234step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35234step2 raw35234step2Labels = mixedMoment B raw35234step3 raw35234step3Labels := by
      have ha : raw35234step3 = raw35234step2 := by apply Matrix.ext; unfold raw35234step3 raw35234step2; decide +kernel
      have hl : raw35234step2Labels = labelEmbedding6 ∘ raw35234step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35234step2 raw35234step2Labels raw35234step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

theorem canonical35235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35235 raw35235Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw35235 raw35235Labels = mixedMoment B raw35235step0 raw35235step0Labels := by
      have hz : ∀ j, raw35235 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35235step0 = (fun i j => raw35235 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35235step0 raw35235; decide +kernel
      have hl : raw35235step0Labels = raw35235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35235 raw35235Labels permutation434 hz
    mixedMoment B raw35235step0 raw35235step0Labels = mixedMoment B raw35235step1 raw35235step1Labels := by
      have hz : ∀ j, raw35235step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35235step1 = (fun i j => raw35235step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35235step1 raw35235step0; decide +kernel
      have hl : raw35235step1Labels = raw35235step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35235step0 raw35235step0Labels permutation80 hz
    mixedMoment B raw35235step1 raw35235step1Labels = mixedMoment B raw35235step2 raw35235step2Labels := by
      have ha : raw35235step2 = (fun i j => raw35235step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35235step2 raw35235step1; decide +kernel
      have hl : raw35235step2Labels = raw35235step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35235step1 raw35235step1Labels permutation24 permutation3
    mixedMoment B raw35235step2 raw35235step2Labels = mixedMoment B raw35235step3 raw35235step3Labels := by
      have ha : raw35235step3 = -raw35235step2 := by apply Matrix.ext; change ∀ i j, raw35235step3 i j = -(raw35235step2 i j); unfold raw35235step3 raw35235step2; decide +kernel
      have hl : raw35235step3Labels = raw35235step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35235step3 raw35235step3Labels = mixedMoment B raw35235step4 raw35235step4Labels := by
      have ha : raw35235step4 = raw35235step3 := by apply Matrix.ext; unfold raw35235step4 raw35235step3; decide +kernel
      have hl : raw35235step3Labels = labelEmbedding6 ∘ raw35235step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35235step3 raw35235step3Labels raw35235step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

theorem canonical35236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35236 raw35236Labels = mixedMoment B node4952 node4952Labels := by
  calc
    mixedMoment B raw35236 raw35236Labels = mixedMoment B raw35236step0 raw35236step0Labels := by
      have hz : ∀ j, raw35236 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35236step0 = (fun i j => raw35236 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35236step0 raw35236; decide +kernel
      have hl : raw35236step0Labels = raw35236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35236 raw35236Labels permutation434 hz
    mixedMoment B raw35236step0 raw35236step0Labels = mixedMoment B raw35236step1 raw35236step1Labels := by
      have hz : ∀ j, raw35236step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35236step1 = (fun i j => raw35236step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35236step1 raw35236step0; decide +kernel
      have hl : raw35236step1Labels = raw35236step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35236step0 raw35236step0Labels permutation80 hz
    mixedMoment B raw35236step1 raw35236step1Labels = mixedMoment B raw35236step2 raw35236step2Labels := by
      have ha : raw35236step2 = (fun i j => raw35236step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35236step2 raw35236step1; decide +kernel
      have hl : raw35236step2Labels = raw35236step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35236step1 raw35236step1Labels permutation14 permutation3
    mixedMoment B raw35236step2 raw35236step2Labels = mixedMoment B raw35236step3 raw35236step3Labels := by
      have ha : raw35236step3 = raw35236step2 := by apply Matrix.ext; unfold raw35236step3 raw35236step2; decide +kernel
      have hl : raw35236step2Labels = labelEmbedding6 ∘ raw35236step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35236step2 raw35236step2Labels raw35236step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4952 node4952Labels := by rfl

theorem canonical35237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35237 raw35237Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw35237 raw35237Labels = mixedMoment B raw35237step0 raw35237step0Labels := by
      have hz : ∀ j, raw35237 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35237step0 = (fun i j => raw35237 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35237step0 raw35237; decide +kernel
      have hl : raw35237step0Labels = raw35237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35237 raw35237Labels permutation434 hz
    mixedMoment B raw35237step0 raw35237step0Labels = mixedMoment B raw35237step1 raw35237step1Labels := by
      have ha : raw35237step1 = (fun i j => raw35237step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35237step1 raw35237step0; decide +kernel
      have hl : raw35237step1Labels = raw35237step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35237step0 raw35237step0Labels permutation150 permutation3
    mixedMoment B raw35237step1 raw35237step1Labels = mixedMoment B raw35237step2 raw35237step2Labels := by
      have ha : raw35237step2 = -raw35237step1 := by apply Matrix.ext; change ∀ i j, raw35237step2 i j = -(raw35237step1 i j); unfold raw35237step2 raw35237step1; decide +kernel
      have hl : raw35237step2Labels = raw35237step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35237step2 raw35237step2Labels = mixedMoment B raw35237step3 raw35237step3Labels := by
      have ha : raw35237step3 = raw35237step2 := by apply Matrix.ext; unfold raw35237step3 raw35237step2; decide +kernel
      have hl : raw35237step2Labels = labelEmbedding6 ∘ raw35237step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35237step2 raw35237step2Labels raw35237step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

theorem canonical35238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35238 raw35238Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw35238 raw35238Labels = mixedMoment B raw35238step0 raw35238step0Labels := by
      have hz : ∀ j, raw35238 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35238step0 = (fun i j => raw35238 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35238step0 raw35238; decide +kernel
      have hl : raw35238step0Labels = raw35238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35238 raw35238Labels permutation346 hz
    mixedMoment B raw35238step0 raw35238step0Labels = mixedMoment B raw35238step1 raw35238step1Labels := by
      have ha : raw35238step1 = (fun i j => raw35238step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35238step1 raw35238step0; decide +kernel
      have hl : raw35238step1Labels = raw35238step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35238step0 raw35238step0Labels permutation150 permutation3
    mixedMoment B raw35238step1 raw35238step1Labels = mixedMoment B raw35238step2 raw35238step2Labels := by
      have ha : raw35238step2 = -raw35238step1 := by apply Matrix.ext; change ∀ i j, raw35238step2 i j = -(raw35238step1 i j); unfold raw35238step2 raw35238step1; decide +kernel
      have hl : raw35238step2Labels = raw35238step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35238step2 raw35238step2Labels = mixedMoment B raw35238step3 raw35238step3Labels := by
      have ha : raw35238step3 = raw35238step2 := by apply Matrix.ext; unfold raw35238step3 raw35238step2; decide +kernel
      have hl : raw35238step2Labels = labelEmbedding6 ∘ raw35238step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35238step2 raw35238step2Labels raw35238step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

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

theorem canonical5177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5177 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5177 = injectiveMoment H raw5177step0 := by
      have hz : ∀ j, raw5177 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5177step0 = (fun i j => raw5177 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5177 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical672 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw672 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw672 = injectiveMoment H raw672step0 := by
      have heq : raw672step0 = -raw672 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw672).symm
    injectiveMoment H raw672step0 = injectiveMoment H raw672step1 := by
      have heq : raw672step1 = (fun i j => raw672step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw672step0 permutation9 permutation8
    _ = injectiveMoment H node175 := by rfl

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

theorem sound35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node35 = Sparse.eval value35 (momentVector H) := by
  have hc : momentVector H 8 = injectiveMoment H node35 := rfl
  simp [value35, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1449 = injectiveMoment H node35 := by
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

theorem canonical2862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2862 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2862 = injectiveMoment H raw2862step0 := by
      have heq : raw2862step0 = (fun i j => raw2862 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2862 permutation3 permutation5
    _ = injectiveMoment H node56 := by rfl

theorem canonical2863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2863 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2863 = injectiveMoment H raw2863step0 := by
      have heq : raw2863step0 = (fun i j => raw2863 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2863 permutation4 permutation5
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound175 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node175 = Sparse.eval value175 (momentVector H) := by
  have heq : pivotMatrix175 = (fun u v => node175 (pivotPermutation175 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node175 = injectiveMoment H pivotMatrix175 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix175 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix175 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix175 (0 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix175 (0 : Fin 3) = raw1449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1449 hH).trans (sound35 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix175 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix175 (1 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix175 (2 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix175 (2 : Fin 3) = raw2863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2863 hH).trans (sound56 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node175 + (injectiveMoment H (mergeFirst pivotMatrix175 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix175 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix175 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value175, value35, value56, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node344 node344Labels = Sparse.eval singlePairValue344 (familyPairVector B) := by
  have hp := single_label_three B hB node344
  have hl : node344Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node344 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 1) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node344 PairSemantics.raw5177; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node344 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node344 PairSemantics.raw872; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value175 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 4) = PairSemantics.raw672 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node344 PairSemantics.raw672; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical672 hH).trans (PairSemantics.sound175 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue344, PairSemantics.value0, PairSemantics.value11, PairSemantics.value25, PairSemantics.value65, PairSemantics.value175, Sparse.eval] at hp ⊢
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

theorem singleton2605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2605 node2605Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node344 node344Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw248 singletonSmall2605
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2605) = raw248Labels := by decide +kernel
  rw [hl, canonical248 B hB] at h
  have hc0 : mixedMoment B raw248 (Fin.cases (0 : Fin 1) singletonSmall2605) =
      mixedMoment B node344 node344Labels := by
    have ha : raw248 = raw249 := by apply Matrix.ext; unfold raw248 raw249; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2605 = raw249Labels := by decide +kernel
    rw [ha, hj, canonical249 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem singleton4950 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4950 node4950Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2342 node2342Labels + mixedMoment B node3421 node3421Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1923 singletonSmall4950
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4950) = raw1923Labels := by decide +kernel
  rw [hl, canonical1923 B hB] at h
  have hc0 : mixedMoment B raw1923 (Fin.cases (0 : Fin 2) singletonSmall4950) =
      mixedMoment B node2342 node2342Labels := by
    have ha : raw1923 = raw1924 := by apply Matrix.ext; unfold raw1923 raw1924; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4950 = raw1924Labels := by decide +kernel
    rw [ha, hj, canonical1924 B hB]
  have hc1 : mixedMoment B raw1923 (Fin.cases (1 : Fin 2) singletonSmall4950) =
      mixedMoment B node3421 node3421Labels := by
    have ha : raw1923 = raw1925 := by apply Matrix.ext; unfold raw1923 raw1925; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4950 = raw1925Labels := by decide +kernel
    rw [ha, hj, canonical1925 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4952 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4952 node4952Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2344 node2344Labels + mixedMoment B node3422 node3422Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1926 singletonSmall4952
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4952) = raw1926Labels := by decide +kernel
  rw [hl, canonical1926 B hB] at h
  have hc0 : mixedMoment B raw1926 (Fin.cases (0 : Fin 2) singletonSmall4952) =
      mixedMoment B node2344 node2344Labels := by
    have ha : raw1926 = raw1927 := by apply Matrix.ext; unfold raw1926 raw1927; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4952 = raw1927Labels := by decide +kernel
    rw [ha, hj, canonical1927 B hB]
  have hc1 : mixedMoment B raw1926 (Fin.cases (1 : Fin 2) singletonSmall4952) =
      mixedMoment B node3422 node3422Labels := by
    have ha : raw1926 = raw1928 := by apply Matrix.ext; unfold raw1926 raw1928; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4952 = raw1928Labels := by decide +kernel
    rw [ha, hj, canonical1928 B hB]
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

theorem singleton5177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5177 node5177Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2605 node2605Labels + mixedMoment B node3616 node3616Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2217 singletonSmall5177
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5177) = raw2217Labels := by decide +kernel
  rw [hl, canonical2217 B hB] at h
  have hc0 : mixedMoment B raw2217 (Fin.cases (0 : Fin 2) singletonSmall5177) =
      mixedMoment B node2605 node2605Labels := by
    have ha : raw2217 = raw2218 := by apply Matrix.ext; unfold raw2217 raw2218; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5177 = raw2218Labels := by decide +kernel
    rw [ha, hj, canonical2218 B hB]
  have hc1 : mixedMoment B raw2217 (Fin.cases (1 : Fin 2) singletonSmall5177) =
      mixedMoment B node3616 node3616Labels := by
    have ha : raw2217 = raw2219 := by apply Matrix.ext; unfold raw2217 raw2219; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5177 = raw2219Labels := by decide +kernel
    rw [ha, hj, canonical2219 B hB]
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

theorem zero5457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5457 node5457Labels = 0 := by
  exact mixedMoment_alpha B hF node5457 node5457Labels 2 permutation152
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2342 node2342Labels = Sparse.eval nodeValue2342 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2342) = mixedMoment B node2342 node2342Labels := rfl
  simpa [nodeValue2342, Sparse.eval] using hc.symm

theorem sound2344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2344 node2344Labels = Sparse.eval nodeValue2344 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2344) = mixedMoment B node2344 node2344Labels := rfl
  simpa [nodeValue2344, Sparse.eval] using hc.symm

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

theorem sound344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node344 node344Labels = Sparse.eval nodeValue344 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue344 (familyPairVector B) := singlePair344 B _hB
    _ = _ := by norm_num [singlePairValue344, nodeValue344, Sparse.eval, mixedVector] <;> ring

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

theorem sound2605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2605 node2605Labels = Sparse.eval nodeValue2605 (mixedVector B) := by
  have h := singleton2605 B _hB
  rw [sound344 B _hB _hF] at h
  norm_num [nodeValue2605, nodeValue344, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3421 node3421Labels = Sparse.eval nodeValue3421 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3421) = mixedMoment B node3421 node3421Labels := rfl
  simpa [nodeValue3421, Sparse.eval] using hc.symm

theorem sound3422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3422 node3422Labels = Sparse.eval nodeValue3422 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3422) = mixedMoment B node3422 node3422Labels := rfl
  simpa [nodeValue3422, Sparse.eval] using hc.symm

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

theorem sound3616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3616 node3616Labels = Sparse.eval nodeValue3616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3616) = mixedMoment B node3616 node3616Labels := rfl
  simpa [nodeValue3616, Sparse.eval] using hc.symm

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

theorem sound4950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4950 node4950Labels = Sparse.eval nodeValue4950 (mixedVector B) := by
  have h := singleton4950 B _hB
  rw [sound2342 B _hB _hF, sound3421 B _hB _hF] at h
  norm_num [nodeValue4950, nodeValue2342, nodeValue3421, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4952 node4952Labels = Sparse.eval nodeValue4952 (mixedVector B) := by
  have h := singleton4952 B _hB
  rw [sound2344 B _hB _hF, sound3422 B _hB _hF] at h
  norm_num [nodeValue4952, nodeValue2344, nodeValue3422, Sparse.eval] at h ⊢
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

theorem sound5177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5177 node5177Labels = Sparse.eval nodeValue5177 (mixedVector B) := by
  have h := singleton5177 B _hB
  rw [sound2605 B _hB _hF, sound3616 B _hB _hF] at h
  norm_num [nodeValue5177, nodeValue2605, nodeValue3616, Sparse.eval] at h ⊢
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

theorem sound5457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5457 node5457Labels = Sparse.eval nodeValue5457 (mixedVector B) := by
  simpa only [nodeValue5457, Sparse.eval_nil] using zero5457 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources79
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2550 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2550 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2550 + difference 0 1) (sourceB2550 + difference 1 0) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2550 + difference 0 1) (sourceB2550 + difference 1 0) sourceC2550) = raw35222 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35222; decide +kernel
    rw [ha]
    exact (canonical35222 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2550 + difference 0 2) (sourceB2550 + difference 2 0) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2550 + difference 0 2) (sourceB2550 + difference 2 0) sourceC2550) = raw35223 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35223; decide +kernel
    rw [ha]
    exact (canonical35223 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2550 + difference 0 3) (sourceB2550 + difference 3 0) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2550 + difference 0 3) (sourceB2550 + difference 3 0) sourceC2550) = raw35224 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35224; decide +kernel
    rw [ha]
    exact (canonical35224 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2550 + difference 0 4) (sourceB2550 + difference 4 0) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA2550 + difference 0 4) (sourceB2550 + difference 4 0) sourceC2550) = raw17663 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw17663; decide +kernel
    rw [ha]
    exact (canonical17663 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2550 + difference 0 5) (sourceB2550 + difference 5 0) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA2550 + difference 0 5) (sourceB2550 + difference 5 0) sourceC2550) = raw35225 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35225; decide +kernel
    rw [ha]
    exact (canonical35225 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2550 + difference 1 0) (sourceB2550 + difference 0 1) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2550 + difference 1 0) (sourceB2550 + difference 0 1) sourceC2550) = raw17675 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw17675; decide +kernel
    rw [ha]
    exact (canonical17675 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2550 + difference 1 2) (sourceB2550 + difference 2 1) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2550 + difference 1 2) (sourceB2550 + difference 2 1) sourceC2550) = raw17677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw17677; decide +kernel
    rw [ha]
    exact (canonical17677 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2550 + difference 1 3) (sourceB2550 + difference 3 1) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2550 + difference 1 3) (sourceB2550 + difference 3 1) sourceC2550) = raw17678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw17678; decide +kernel
    rw [ha]
    exact (canonical17678 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2550 + difference 1 4) (sourceB2550 + difference 4 1) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA2550 + difference 1 4) (sourceB2550 + difference 4 1) sourceC2550) = raw2772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw2772; decide +kernel
    rw [ha]
    exact (canonical2772 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2550 + difference 1 5) (sourceB2550 + difference 5 1) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA2550 + difference 1 5) (sourceB2550 + difference 5 1) sourceC2550) = raw17679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw17679; decide +kernel
    rw [ha]
    exact (canonical17679 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2550 + difference 2 0) (sourceB2550 + difference 0 2) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2550 + difference 2 0) (sourceB2550 + difference 0 2) sourceC2550) = raw29650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw29650; decide +kernel
    rw [ha]
    exact (canonical29650 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2550 + difference 2 1) (sourceB2550 + difference 1 2) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2550 + difference 2 1) (sourceB2550 + difference 1 2) sourceC2550) = raw35226 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35226; decide +kernel
    rw [ha]
    exact (canonical35226 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2550 + difference 2 3) (sourceB2550 + difference 3 2) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5457) := by
    have ha : (tripleCharges (sourceA2550 + difference 2 3) (sourceB2550 + difference 3 2) sourceC2550) = raw35227 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35227; decide +kernel
    rw [ha]
    exact (canonical35227 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2550 + difference 2 4) (sourceB2550 + difference 4 2) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2550 + difference 2 4) (sourceB2550 + difference 4 2) sourceC2550) = raw17668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw17668; decide +kernel
    rw [ha]
    exact (canonical17668 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2550 + difference 2 5) (sourceB2550 + difference 5 2) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2550 + difference 2 5) (sourceB2550 + difference 5 2) sourceC2550) = raw35228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35228; decide +kernel
    rw [ha]
    exact (canonical35228 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2550 + difference 3 0) (sourceB2550 + difference 0 3) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2550 + difference 3 0) (sourceB2550 + difference 0 3) sourceC2550) = raw29653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw29653; decide +kernel
    rw [ha]
    exact (canonical29653 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2550 + difference 3 1) (sourceB2550 + difference 1 3) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2550 + difference 3 1) (sourceB2550 + difference 1 3) sourceC2550) = raw35229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35229; decide +kernel
    rw [ha]
    exact (canonical35229 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2550 + difference 3 2) (sourceB2550 + difference 2 3) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5457) := by
    have ha : (tripleCharges (sourceA2550 + difference 3 2) (sourceB2550 + difference 2 3) sourceC2550) = raw35230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35230; decide +kernel
    rw [ha]
    exact (canonical35230 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2550 + difference 3 4) (sourceB2550 + difference 4 3) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2550 + difference 3 4) (sourceB2550 + difference 4 3) sourceC2550) = raw17672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw17672; decide +kernel
    rw [ha]
    exact (canonical17672 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2550 + difference 3 5) (sourceB2550 + difference 5 3) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2550 + difference 3 5) (sourceB2550 + difference 5 3) sourceC2550) = raw35231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35231; decide +kernel
    rw [ha]
    exact (canonical35231 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2550 + difference 4 0) (sourceB2550 + difference 0 4) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4952) := by
    have ha : (tripleCharges (sourceA2550 + difference 4 0) (sourceB2550 + difference 0 4) sourceC2550) = raw29656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw29656; decide +kernel
    rw [ha]
    exact (canonical29656 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2550 + difference 4 1) (sourceB2550 + difference 1 4) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4952) := by
    have ha : (tripleCharges (sourceA2550 + difference 4 1) (sourceB2550 + difference 1 4) sourceC2550) = raw35232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35232; decide +kernel
    rw [ha]
    exact (canonical35232 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2550 + difference 4 2) (sourceB2550 + difference 2 4) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2550 + difference 4 2) (sourceB2550 + difference 2 4) sourceC2550) = raw35233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35233; decide +kernel
    rw [ha]
    exact (canonical35233 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2550 + difference 4 3) (sourceB2550 + difference 3 4) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2550 + difference 4 3) (sourceB2550 + difference 3 4) sourceC2550) = raw35234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35234; decide +kernel
    rw [ha]
    exact (canonical35234 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2550 + difference 4 5) (sourceB2550 + difference 5 4) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2550 + difference 4 5) (sourceB2550 + difference 5 4) sourceC2550) = raw35235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35235; decide +kernel
    rw [ha]
    exact (canonical35235 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2550 + difference 5 0) (sourceB2550 + difference 0 5) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4952) := by
    have ha : (tripleCharges (sourceA2550 + difference 5 0) (sourceB2550 + difference 0 5) sourceC2550) = raw27590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw27590; decide +kernel
    rw [ha]
    exact (canonical27590 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2550 + difference 5 1) (sourceB2550 + difference 1 5) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4952) := by
    have ha : (tripleCharges (sourceA2550 + difference 5 1) (sourceB2550 + difference 1 5) sourceC2550) = raw35236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35236; decide +kernel
    rw [ha]
    exact (canonical35236 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2550 + difference 5 2) (sourceB2550 + difference 2 5) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2550 + difference 5 2) (sourceB2550 + difference 2 5) sourceC2550) = raw35237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35237; decide +kernel
    rw [ha]
    exact (canonical35237 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2550 + difference 5 3) (sourceB2550 + difference 3 5) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2550 + difference 5 3) (sourceB2550 + difference 3 5) sourceC2550) = raw35238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35238; decide +kernel
    rw [ha]
    exact (canonical35238 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2550 + difference 5 4) (sourceB2550 + difference 4 5) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2550 + difference 5 4) (sourceB2550 + difference 4 5) sourceC2550) = raw17680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw17680; decide +kernel
    rw [ha]
    exact (canonical17680 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2550 sourceB2550 sourceC2550
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2550, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2048 : Integer.Sparse.reindex keyMap MixedData.row2048 = numericRow2048 := by decide +kernel

theorem numericCheck2048 (x : Master → ℝ) : Integer.Sparse.eval numericRow2048 x =
    (12960 : ℝ) * reducedSource2048 x := by
  norm_num [numericRow2048, reducedSource2048, Integer.Sparse.eval, Sparse.eval, nodeValue4950, nodeValue4952, nodeValue5177, nodeValue5457, nodeValue5465, nodeValue5487]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2048 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2048 (mixedVector B) = 0 := by
  have h4950 : mixedVector B (Sum.inr 4950) = Sparse.eval nodeValue4950 (mixedVector B) := by
    change mixedMoment B node4950 node4950Labels = _
    exact sound4950 B hB hF
  have h4952 : mixedVector B (Sum.inr 4952) = Sparse.eval nodeValue4952 (mixedVector B) := by
    change mixedMoment B node4952 node4952Labels = _
    exact sound4952 B hB hF
  have h5177 : mixedVector B (Sum.inr 5177) = Sparse.eval nodeValue5177 (mixedVector B) := by
    change mixedMoment B node5177 node5177Labels = _
    exact sound5177 B hB hF
  have h5457 : mixedVector B (Sum.inr 5457) = Sparse.eval nodeValue5457 (mixedVector B) := by
    change mixedMoment B node5457 node5457Labels = _
    exact sound5457 B hB hF
  have h5465 : mixedVector B (Sum.inr 5465) = Sparse.eval nodeValue5465 (mixedVector B) := by
    change mixedMoment B node5465 node5465Labels = _
    exact sound5465_e B hB hF
  have h5487 : mixedVector B (Sum.inr 5487) = Sparse.eval nodeValue5487 (mixedVector B) := by
    change mixedMoment B node5487 node5487Labels = _
    exact sound5487 B hB hF
  simpa only [sourceForm2550, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4950, h4952, h5177, h5457, h5465, h5487, reducedSource2048] using sourceEq2550 B hB

theorem rowSound2048_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2048 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2048, numericCheck2048, reducedZero2048 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e_oai
