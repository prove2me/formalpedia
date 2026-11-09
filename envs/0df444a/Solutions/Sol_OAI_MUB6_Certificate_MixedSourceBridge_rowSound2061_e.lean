-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:54:44.481073+00:00
-- url     : https://prove2.me/submissions/b06b823c-c69e-4d8a-8176-d039e9642ecc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5388_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5418_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem canonical2253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2253 raw2253Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw2253 raw2253Labels = mixedMoment B raw2253step0 raw2253step0Labels := by
      have ha : raw2253step0 = (fun i j => raw2253 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2253step0 raw2253; decide +kernel
      have hl : raw2253step0Labels = raw2253Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2253 raw2253Labels permutation32 permutation4
    mixedMoment B raw2253step0 raw2253step0Labels = mixedMoment B raw2253step1 raw2253step1Labels := by
      have ha : raw2253step1 = raw2253step0 := by apply Matrix.ext; unfold raw2253step1 raw2253step0; decide +kernel
      have hl : raw2253step0Labels = labelEmbedding7 ∘ raw2253step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2253step0 raw2253step0Labels raw2253step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

theorem canonical2254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2254 raw2254Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw2254 raw2254Labels = mixedMoment B raw2254step0 raw2254step0Labels := by
      have ha : raw2254step0 = (fun i j => raw2254 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2254step0 raw2254; decide +kernel
      have hl : raw2254step0Labels = raw2254Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2254 raw2254Labels permutation32 permutation4
    _ = mixedMoment B node2684 node2684Labels := by rfl

theorem canonical2255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2255 raw2255Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw2255 raw2255Labels = mixedMoment B raw2255step0 raw2255step0Labels := by
      have ha : raw2255step0 = (fun i j => raw2255 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2255step0 raw2255; decide +kernel
      have hl : raw2255step0Labels = raw2255Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2255 raw2255Labels permutation32 permutation6
    mixedMoment B raw2255step0 raw2255step0Labels = mixedMoment B raw2255step1 raw2255step1Labels := by
      have ha : raw2255step1 = -raw2255step0 := by apply Matrix.ext; change ∀ i j, raw2255step1 i j = -(raw2255step0 i j); unfold raw2255step1 raw2255step0; decide +kernel
      have hl : raw2255step1Labels = raw2255step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2255step1 raw2255step1Labels = mixedMoment B raw2255step2 raw2255step2Labels := by
      have ha : raw2255step2 = raw2255step1 := by apply Matrix.ext; unfold raw2255step2 raw2255step1; decide +kernel
      have hl : raw2255step1Labels = labelEmbedding1 ∘ raw2255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2255step1 raw2255step1Labels raw2255step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3394 node3394Labels := by rfl

theorem canonical2265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2265 raw2265Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw2265 raw2265Labels = mixedMoment B raw2265step0 raw2265step0Labels := by
      have ha : raw2265step0 = (fun i j => raw2265 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2265step0 raw2265; decide +kernel
      have hl : raw2265step0Labels = raw2265Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2265 raw2265Labels permutation32 permutation4
    mixedMoment B raw2265step0 raw2265step0Labels = mixedMoment B raw2265step1 raw2265step1Labels := by
      have ha : raw2265step1 = raw2265step0 := by apply Matrix.ext; unfold raw2265step1 raw2265step0; decide +kernel
      have hl : raw2265step0Labels = labelEmbedding7 ∘ raw2265step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2265step0 raw2265step0Labels raw2265step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

theorem canonical2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2266 raw2266Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw2266 raw2266Labels = mixedMoment B raw2266step0 raw2266step0Labels := by
      have ha : raw2266step0 = (fun i j => raw2266 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2266step0 raw2266; decide +kernel
      have hl : raw2266step0Labels = raw2266Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2266 raw2266Labels permutation32 permutation4
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical2267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2267 raw2267Labels = mixedMoment B node3498 node3498Labels := by
  calc
    mixedMoment B raw2267 raw2267Labels = mixedMoment B raw2267step0 raw2267step0Labels := by
      have ha : raw2267step0 = (fun i j => raw2267 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2267step0 raw2267; decide +kernel
      have hl : raw2267step0Labels = raw2267Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2267 raw2267Labels permutation32 permutation6
    mixedMoment B raw2267step0 raw2267step0Labels = mixedMoment B raw2267step1 raw2267step1Labels := by
      have ha : raw2267step1 = -raw2267step0 := by apply Matrix.ext; change ∀ i j, raw2267step1 i j = -(raw2267step0 i j); unfold raw2267step1 raw2267step0; decide +kernel
      have hl : raw2267step1Labels = raw2267step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2267step1 raw2267step1Labels = mixedMoment B raw2267step2 raw2267step2Labels := by
      have ha : raw2267step2 = raw2267step1 := by apply Matrix.ext; unfold raw2267step2 raw2267step1; decide +kernel
      have hl : raw2267step1Labels = labelEmbedding1 ∘ raw2267step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2267step1 raw2267step1Labels raw2267step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3498 node3498Labels := by rfl

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

theorem canonical2397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2397 raw2397Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw2397 raw2397Labels = mixedMoment B raw2397step0 raw2397step0Labels := by
      have ha : raw2397step0 = (fun i j => raw2397 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2397step0 raw2397; decide +kernel
      have hl : raw2397step0Labels = raw2397Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2397 raw2397Labels permutation152 permutation4
    mixedMoment B raw2397step0 raw2397step0Labels = mixedMoment B raw2397step1 raw2397step1Labels := by
      have ha : raw2397step1 = raw2397step0 := by apply Matrix.ext; unfold raw2397step1 raw2397step0; decide +kernel
      have hl : raw2397step0Labels = labelEmbedding7 ∘ raw2397step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2397step0 raw2397step0Labels raw2397step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

theorem canonical2398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2398 raw2398Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw2398 raw2398Labels = mixedMoment B raw2398step0 raw2398step0Labels := by
      have ha : raw2398step0 = (fun i j => raw2398 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2398step0 raw2398; decide +kernel
      have hl : raw2398step0Labels = raw2398Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2398 raw2398Labels permutation152 permutation4
    _ = mixedMoment B node3692 node3692Labels := by rfl

theorem canonical2399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2399 raw2399Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw2399 raw2399Labels = mixedMoment B raw2399step0 raw2399step0Labels := by
      have ha : raw2399step0 = (fun i j => raw2399 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2399step0 raw2399; decide +kernel
      have hl : raw2399step0Labels = raw2399Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2399 raw2399Labels permutation170 permutation6
    mixedMoment B raw2399step0 raw2399step0Labels = mixedMoment B raw2399step1 raw2399step1Labels := by
      have ha : raw2399step1 = -raw2399step0 := by apply Matrix.ext; change ∀ i j, raw2399step1 i j = -(raw2399step0 i j); unfold raw2399step1 raw2399step0; decide +kernel
      have hl : raw2399step1Labels = raw2399step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2399step1 raw2399step1Labels = mixedMoment B raw2399step2 raw2399step2Labels := by
      have ha : raw2399step2 = raw2399step1 := by apply Matrix.ext; unfold raw2399step2 raw2399step1; decide +kernel
      have hl : raw2399step1Labels = labelEmbedding1 ∘ raw2399step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2399step1 raw2399step1Labels raw2399step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

theorem canonical2418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2418 raw2418Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw2418 raw2418Labels = mixedMoment B raw2418step0 raw2418step0Labels := by
      have ha : raw2418step0 = (fun i j => raw2418 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2418step0 raw2418; decide +kernel
      have hl : raw2418step0Labels = raw2418Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2418 raw2418Labels permutation32 permutation4
    mixedMoment B raw2418step0 raw2418step0Labels = mixedMoment B raw2418step1 raw2418step1Labels := by
      have ha : raw2418step1 = raw2418step0 := by apply Matrix.ext; unfold raw2418step1 raw2418step0; decide +kernel
      have hl : raw2418step0Labels = labelEmbedding7 ∘ raw2418step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2418step0 raw2418step0Labels raw2418step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

theorem canonical2419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2419 raw2419Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw2419 raw2419Labels = mixedMoment B raw2419step0 raw2419step0Labels := by
      have ha : raw2419step0 = (fun i j => raw2419 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2419step0 raw2419; decide +kernel
      have hl : raw2419step0Labels = raw2419Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2419 raw2419Labels permutation32 permutation4
    _ = mixedMoment B node3706 node3706Labels := by rfl

theorem canonical2420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2420 raw2420Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw2420 raw2420Labels = mixedMoment B raw2420step0 raw2420step0Labels := by
      have ha : raw2420step0 = (fun i j => raw2420 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2420step0 raw2420; decide +kernel
      have hl : raw2420step0Labels = raw2420Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2420 raw2420Labels permutation36 permutation6
    mixedMoment B raw2420step0 raw2420step0Labels = mixedMoment B raw2420step1 raw2420step1Labels := by
      have ha : raw2420step1 = -raw2420step0 := by apply Matrix.ext; change ∀ i j, raw2420step1 i j = -(raw2420step0 i j); unfold raw2420step1 raw2420step0; decide +kernel
      have hl : raw2420step1Labels = raw2420step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2420step1 raw2420step1Labels = mixedMoment B raw2420step2 raw2420step2Labels := by
      have ha : raw2420step2 = raw2420step1 := by apply Matrix.ext; unfold raw2420step2 raw2420step1; decide +kernel
      have hl : raw2420step1Labels = labelEmbedding1 ∘ raw2420step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2420step1 raw2420step1Labels raw2420step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3771 node3771Labels := by rfl

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

theorem canonical2439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2439 raw2439Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw2439 raw2439Labels = mixedMoment B raw2439step0 raw2439step0Labels := by
      have ha : raw2439step0 = (fun i j => raw2439 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2439step0 raw2439; decide +kernel
      have hl : raw2439step0Labels = raw2439Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2439 raw2439Labels permutation32 permutation4
    mixedMoment B raw2439step0 raw2439step0Labels = mixedMoment B raw2439step1 raw2439step1Labels := by
      have ha : raw2439step1 = raw2439step0 := by apply Matrix.ext; unfold raw2439step1 raw2439step0; decide +kernel
      have hl : raw2439step0Labels = labelEmbedding7 ∘ raw2439step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2439step0 raw2439step0Labels raw2439step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

theorem canonical2440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2440 raw2440Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw2440 raw2440Labels = mixedMoment B raw2440step0 raw2440step0Labels := by
      have ha : raw2440step0 = (fun i j => raw2440 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2440step0 raw2440; decide +kernel
      have hl : raw2440step0Labels = raw2440Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2440 raw2440Labels permutation32 permutation4
    _ = mixedMoment B node3732 node3732Labels := by rfl

theorem canonical2441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2441 raw2441Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw2441 raw2441Labels = mixedMoment B raw2441step0 raw2441step0Labels := by
      have ha : raw2441step0 = (fun i j => raw2441 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2441step0 raw2441; decide +kernel
      have hl : raw2441step0Labels = raw2441Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2441 raw2441Labels permutation149 permutation6
    mixedMoment B raw2441step0 raw2441step0Labels = mixedMoment B raw2441step1 raw2441step1Labels := by
      have ha : raw2441step1 = raw2441step0 := by apply Matrix.ext; unfold raw2441step1 raw2441step0; decide +kernel
      have hl : raw2441step0Labels = labelEmbedding1 ∘ raw2441step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2441step0 raw2441step0Labels raw2441step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3811 node3811Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical277
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35572 raw35572Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw35572 raw35572Labels = mixedMoment B raw35572step0 raw35572step0Labels := by
      have hz : ∀ j, raw35572 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35572step0 = (fun i j => raw35572 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35572step0 raw35572; decide +kernel
      have hl : raw35572step0Labels = raw35572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35572 raw35572Labels permutation346 hz
    mixedMoment B raw35572step0 raw35572step0Labels = mixedMoment B raw35572step1 raw35572step1Labels := by
      have ha : raw35572step1 = (fun i j => raw35572step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35572step1 raw35572step0; decide +kernel
      have hl : raw35572step1Labels = raw35572step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35572step0 raw35572step0Labels permutation144 permutation6
    mixedMoment B raw35572step1 raw35572step1Labels = mixedMoment B raw35572step2 raw35572step2Labels := by
      have ha : raw35572step2 = -raw35572step1 := by apply Matrix.ext; change ∀ i j, raw35572step2 i j = -(raw35572step1 i j); unfold raw35572step2 raw35572step1; decide +kernel
      have hl : raw35572step2Labels = raw35572step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35572step2 raw35572step2Labels = mixedMoment B raw35572step3 raw35572step3Labels := by
      have ha : raw35572step3 = raw35572step2 := by apply Matrix.ext; unfold raw35572step3 raw35572step2; decide +kernel
      have hl : raw35572step2Labels = labelEmbedding9 ∘ raw35572step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35572step2 raw35572step2Labels raw35572step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5418 node5418Labels := by rfl

theorem canonical35573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35573 raw35573Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw35573 raw35573Labels = mixedMoment B raw35573step0 raw35573step0Labels := by
      have ha : raw35573step0 = (fun i j => raw35573 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35573step0 raw35573; decide +kernel
      have hl : raw35573step0Labels = raw35573Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35573 raw35573Labels permutation265 permutation7
    mixedMoment B raw35573step0 raw35573step0Labels = mixedMoment B raw35573step1 raw35573step1Labels := by
      have ha : raw35573step1 = raw35573step0 := by apply Matrix.ext; unfold raw35573step1 raw35573step0; decide +kernel
      have hl : raw35573step0Labels = labelEmbedding10 ∘ raw35573step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35573step0 raw35573step0Labels raw35573step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

theorem canonical35574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35574 raw35574Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw35574 raw35574Labels = mixedMoment B raw35574step0 raw35574step0Labels := by
      have hz : ∀ j, raw35574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35574step0 = (fun i j => raw35574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35574step0 raw35574; decide +kernel
      have hl : raw35574step0Labels = raw35574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35574 raw35574Labels permutation346 hz
    mixedMoment B raw35574step0 raw35574step0Labels = mixedMoment B raw35574step1 raw35574step1Labels := by
      have ha : raw35574step1 = (fun i j => raw35574step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35574step1 raw35574step0; decide +kernel
      have hl : raw35574step1Labels = raw35574step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35574step0 raw35574step0Labels permutation58 permutation7
    mixedMoment B raw35574step1 raw35574step1Labels = mixedMoment B raw35574step2 raw35574step2Labels := by
      have ha : raw35574step2 = raw35574step1 := by apply Matrix.ext; unfold raw35574step2 raw35574step1; decide +kernel
      have hl : raw35574step1Labels = labelEmbedding10 ∘ raw35574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35574step1 raw35574step1Labels raw35574step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

theorem canonical35575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35575 raw35575Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw35575 raw35575Labels = mixedMoment B raw35575step0 raw35575step0Labels := by
      have hz : ∀ j, raw35575 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35575step0 = (fun i j => raw35575 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35575step0 raw35575; decide +kernel
      have hl : raw35575step0Labels = raw35575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35575 raw35575Labels permutation346 hz
    mixedMoment B raw35575step0 raw35575step0Labels = mixedMoment B raw35575step1 raw35575step1Labels := by
      have ha : raw35575step1 = (fun i j => raw35575step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35575step1 raw35575step0; decide +kernel
      have hl : raw35575step1Labels = raw35575step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35575step0 raw35575step0Labels permutation56 permutation7
    mixedMoment B raw35575step1 raw35575step1Labels = mixedMoment B raw35575step2 raw35575step2Labels := by
      have ha : raw35575step2 = raw35575step1 := by apply Matrix.ext; unfold raw35575step2 raw35575step1; decide +kernel
      have hl : raw35575step1Labels = labelEmbedding10 ∘ raw35575step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35575step1 raw35575step1Labels raw35575step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

theorem canonical35576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35576 raw35576Labels = mixedMoment B node5369 node5369Labels := by
  calc
    mixedMoment B raw35576 raw35576Labels = mixedMoment B raw35576step0 raw35576step0Labels := by
      have hz : ∀ j, raw35576 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35576step0 = (fun i j => raw35576 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35576step0 raw35576; decide +kernel
      have hl : raw35576step0Labels = raw35576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35576 raw35576Labels permutation346 hz
    mixedMoment B raw35576step0 raw35576step0Labels = mixedMoment B raw35576step1 raw35576step1Labels := by
      have ha : raw35576step1 = (fun i j => raw35576step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35576step1 raw35576step0; decide +kernel
      have hl : raw35576step1Labels = raw35576step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35576step0 raw35576step0Labels permutation56 permutation7
    mixedMoment B raw35576step1 raw35576step1Labels = mixedMoment B raw35576step2 raw35576step2Labels := by
      have ha : raw35576step2 = raw35576step1 := by apply Matrix.ext; unfold raw35576step2 raw35576step1; decide +kernel
      have hl : raw35576step1Labels = labelEmbedding10 ∘ raw35576step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35576step1 raw35576step1Labels raw35576step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5369 node5369Labels := by rfl

theorem canonical35577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35577 raw35577Labels = mixedMoment B node5279 node5279Labels := by
  calc
    mixedMoment B raw35577 raw35577Labels = mixedMoment B raw35577step0 raw35577step0Labels := by
      have hz : ∀ j, raw35577 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35577step0 = (fun i j => raw35577 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35577step0 raw35577; decide +kernel
      have hl : raw35577step0Labels = raw35577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35577 raw35577Labels permutation346 hz
    mixedMoment B raw35577step0 raw35577step0Labels = mixedMoment B raw35577step1 raw35577step1Labels := by
      have ha : raw35577step1 = (fun i j => raw35577step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35577step1 raw35577step0; decide +kernel
      have hl : raw35577step1Labels = raw35577step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35577step0 raw35577step0Labels permutation40 permutation4
    mixedMoment B raw35577step1 raw35577step1Labels = mixedMoment B raw35577step2 raw35577step2Labels := by
      have ha : raw35577step2 = -raw35577step1 := by apply Matrix.ext; change ∀ i j, raw35577step2 i j = -(raw35577step1 i j); unfold raw35577step2 raw35577step1; decide +kernel
      have hl : raw35577step2Labels = raw35577step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35577step2 raw35577step2Labels = mixedMoment B raw35577step3 raw35577step3Labels := by
      have ha : raw35577step3 = raw35577step2 := by apply Matrix.ext; unfold raw35577step3 raw35577step2; decide +kernel
      have hl : raw35577step2Labels = labelEmbedding7 ∘ raw35577step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35577step2 raw35577step2Labels raw35577step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5279 node5279Labels := by rfl

theorem canonical35578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35578 raw35578Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw35578 raw35578Labels = mixedMoment B raw35578step0 raw35578step0Labels := by
      have ha : raw35578step0 = (fun i j => raw35578 (permutation283 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35578step0 raw35578; decide +kernel
      have hl : raw35578step0Labels = raw35578Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35578 raw35578Labels permutation283 permutation2
    mixedMoment B raw35578step0 raw35578step0Labels = mixedMoment B raw35578step1 raw35578step1Labels := by
      have ha : raw35578step1 = -raw35578step0 := by apply Matrix.ext; change ∀ i j, raw35578step1 i j = -(raw35578step0 i j); unfold raw35578step1 raw35578step0; decide +kernel
      have hl : raw35578step1Labels = raw35578step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5231 node5231Labels := by rfl

theorem canonical35579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35579 raw35579Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw35579 raw35579Labels = mixedMoment B raw35579step0 raw35579step0Labels := by
      have hz : ∀ j, raw35579 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35579step0 = (fun i j => raw35579 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35579step0 raw35579; decide +kernel
      have hl : raw35579step0Labels = raw35579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35579 raw35579Labels permutation346 hz
    mixedMoment B raw35579step0 raw35579step0Labels = mixedMoment B raw35579step1 raw35579step1Labels := by
      have ha : raw35579step1 = (fun i j => raw35579step0 (permutation61 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35579step1 raw35579step0; decide +kernel
      have hl : raw35579step1Labels = raw35579step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35579step0 raw35579step0Labels permutation61 permutation2
    mixedMoment B raw35579step1 raw35579step1Labels = mixedMoment B raw35579step2 raw35579step2Labels := by
      have ha : raw35579step2 = -raw35579step1 := by apply Matrix.ext; change ∀ i j, raw35579step2 i j = -(raw35579step1 i j); unfold raw35579step2 raw35579step1; decide +kernel
      have hl : raw35579step2Labels = raw35579step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5233 node5233Labels := by rfl

theorem canonical35580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35580 raw35580Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw35580 raw35580Labels = mixedMoment B raw35580step0 raw35580step0Labels := by
      have hz : ∀ j, raw35580 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35580step0 = (fun i j => raw35580 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35580step0 raw35580; decide +kernel
      have hl : raw35580step0Labels = raw35580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35580 raw35580Labels permutation346 hz
    mixedMoment B raw35580step0 raw35580step0Labels = mixedMoment B raw35580step1 raw35580step1Labels := by
      have ha : raw35580step1 = (fun i j => raw35580step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35580step1 raw35580step0; decide +kernel
      have hl : raw35580step1Labels = raw35580step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35580step0 raw35580step0Labels permutation60 permutation2
    mixedMoment B raw35580step1 raw35580step1Labels = mixedMoment B raw35580step2 raw35580step2Labels := by
      have ha : raw35580step2 = -raw35580step1 := by apply Matrix.ext; change ∀ i j, raw35580step2 i j = -(raw35580step1 i j); unfold raw35580step2 raw35580step1; decide +kernel
      have hl : raw35580step2Labels = raw35580step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5233 node5233Labels := by rfl

theorem canonical35581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35581 raw35581Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw35581 raw35581Labels = mixedMoment B raw35581step0 raw35581step0Labels := by
      have hz : ∀ j, raw35581 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35581step0 = (fun i j => raw35581 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35581step0 raw35581; decide +kernel
      have hl : raw35581step0Labels = raw35581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35581 raw35581Labels permutation346 hz
    mixedMoment B raw35581step0 raw35581step0Labels = mixedMoment B raw35581step1 raw35581step1Labels := by
      have ha : raw35581step1 = (fun i j => raw35581step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35581step1 raw35581step0; decide +kernel
      have hl : raw35581step1Labels = raw35581step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35581step0 raw35581step0Labels permutation56 permutation2
    mixedMoment B raw35581step1 raw35581step1Labels = mixedMoment B raw35581step2 raw35581step2Labels := by
      have ha : raw35581step2 = -raw35581step1 := by apply Matrix.ext; change ∀ i j, raw35581step2 i j = -(raw35581step1 i j); unfold raw35581step2 raw35581step1; decide +kernel
      have hl : raw35581step2Labels = raw35581step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5237 node5237Labels := by rfl

theorem canonical35582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35582 raw35582Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw35582 raw35582Labels = mixedMoment B raw35582step0 raw35582step0Labels := by
      have ha : raw35582step0 = (fun i j => raw35582 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35582step0 raw35582; decide +kernel
      have hl : raw35582step0Labels = raw35582Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35582 raw35582Labels permutation160 permutation4
    mixedMoment B raw35582step0 raw35582step0Labels = mixedMoment B raw35582step1 raw35582step1Labels := by
      have ha : raw35582step1 = -raw35582step0 := by apply Matrix.ext; change ∀ i j, raw35582step1 i j = -(raw35582step0 i j); unfold raw35582step1 raw35582step0; decide +kernel
      have hl : raw35582step1Labels = raw35582step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35582step1 raw35582step1Labels = mixedMoment B raw35582step2 raw35582step2Labels := by
      have ha : raw35582step2 = raw35582step1 := by apply Matrix.ext; unfold raw35582step2 raw35582step1; decide +kernel
      have hl : raw35582step1Labels = labelEmbedding7 ∘ raw35582step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35582step1 raw35582step1Labels raw35582step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

theorem canonical35583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35583 raw35583Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw35583 raw35583Labels = mixedMoment B raw35583step0 raw35583step0Labels := by
      have ha : raw35583step0 = (fun i j => raw35583 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35583step0 raw35583; decide +kernel
      have hl : raw35583step0Labels = raw35583Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35583 raw35583Labels permutation152 permutation6
    mixedMoment B raw35583step0 raw35583step0Labels = mixedMoment B raw35583step1 raw35583step1Labels := by
      have ha : raw35583step1 = raw35583step0 := by apply Matrix.ext; unfold raw35583step1 raw35583step0; decide +kernel
      have hl : raw35583step0Labels = labelEmbedding9 ∘ raw35583step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35583step0 raw35583step0Labels raw35583step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical278
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35584 raw35584Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw35584 raw35584Labels = mixedMoment B raw35584step0 raw35584step0Labels := by
      have ha : raw35584step0 = (fun i j => raw35584 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35584step0 raw35584; decide +kernel
      have hl : raw35584step0Labels = raw35584Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35584 raw35584Labels permutation267 permutation7
    mixedMoment B raw35584step0 raw35584step0Labels = mixedMoment B raw35584step1 raw35584step1Labels := by
      have ha : raw35584step1 = raw35584step0 := by apply Matrix.ext; unfold raw35584step1 raw35584step0; decide +kernel
      have hl : raw35584step0Labels = labelEmbedding10 ∘ raw35584step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35584step0 raw35584step0Labels raw35584step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

theorem canonical35585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35585 raw35585Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw35585 raw35585Labels = mixedMoment B raw35585step0 raw35585step0Labels := by
      have ha : raw35585step0 = (fun i j => raw35585 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35585step0 raw35585; decide +kernel
      have hl : raw35585step0Labels = raw35585Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35585 raw35585Labels permutation265 permutation7
    mixedMoment B raw35585step0 raw35585step0Labels = mixedMoment B raw35585step1 raw35585step1Labels := by
      have ha : raw35585step1 = raw35585step0 := by apply Matrix.ext; unfold raw35585step1 raw35585step0; decide +kernel
      have hl : raw35585step0Labels = labelEmbedding10 ∘ raw35585step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35585step0 raw35585step0Labels raw35585step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

theorem canonical35586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35586 raw35586Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw35586 raw35586Labels = mixedMoment B raw35586step0 raw35586step0Labels := by
      have ha : raw35586step0 = (fun i j => raw35586 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35586step0 raw35586; decide +kernel
      have hl : raw35586step0Labels = raw35586Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35586 raw35586Labels permutation265 permutation7
    mixedMoment B raw35586step0 raw35586step0Labels = mixedMoment B raw35586step1 raw35586step1Labels := by
      have ha : raw35586step1 = raw35586step0 := by apply Matrix.ext; unfold raw35586step1 raw35586step0; decide +kernel
      have hl : raw35586step0Labels = labelEmbedding10 ∘ raw35586step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35586step0 raw35586step0Labels raw35586step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

theorem canonical35587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35587 raw35587Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw35587 raw35587Labels = mixedMoment B raw35587step0 raw35587step0Labels := by
      have hz : ∀ j, raw35587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35587step0 = (fun i j => raw35587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35587step0 raw35587; decide +kernel
      have hl : raw35587step0Labels = raw35587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35587 raw35587Labels permutation346 hz
    mixedMoment B raw35587step0 raw35587step0Labels = mixedMoment B raw35587step1 raw35587step1Labels := by
      have ha : raw35587step1 = (fun i j => raw35587step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35587step1 raw35587step0; decide +kernel
      have hl : raw35587step1Labels = raw35587step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35587step0 raw35587step0Labels permutation34 permutation4
    mixedMoment B raw35587step1 raw35587step1Labels = mixedMoment B raw35587step2 raw35587step2Labels := by
      have ha : raw35587step2 = -raw35587step1 := by apply Matrix.ext; change ∀ i j, raw35587step2 i j = -(raw35587step1 i j); unfold raw35587step2 raw35587step1; decide +kernel
      have hl : raw35587step2Labels = raw35587step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35587step2 raw35587step2Labels = mixedMoment B raw35587step3 raw35587step3Labels := by
      have ha : raw35587step3 = raw35587step2 := by apply Matrix.ext; unfold raw35587step3 raw35587step2; decide +kernel
      have hl : raw35587step2Labels = labelEmbedding7 ∘ raw35587step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35587step2 raw35587step2Labels raw35587step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

theorem canonical35588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35588 raw35588Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw35588 raw35588Labels = mixedMoment B raw35588step0 raw35588step0Labels := by
      have hz : ∀ j, raw35588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35588step0 = (fun i j => raw35588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35588step0 raw35588; decide +kernel
      have hl : raw35588step0Labels = raw35588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35588 raw35588Labels permutation346 hz
    mixedMoment B raw35588step0 raw35588step0Labels = mixedMoment B raw35588step1 raw35588step1Labels := by
      have ha : raw35588step1 = (fun i j => raw35588step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35588step1 raw35588step0; decide +kernel
      have hl : raw35588step1Labels = raw35588step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35588step0 raw35588step0Labels permutation34 permutation6
    mixedMoment B raw35588step1 raw35588step1Labels = mixedMoment B raw35588step2 raw35588step2Labels := by
      have ha : raw35588step2 = raw35588step1 := by apply Matrix.ext; unfold raw35588step2 raw35588step1; decide +kernel
      have hl : raw35588step1Labels = labelEmbedding9 ∘ raw35588step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35588step1 raw35588step1Labels raw35588step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

theorem canonical35589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35589 raw35589Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw35589 raw35589Labels = mixedMoment B raw35589step0 raw35589step0Labels := by
      have ha : raw35589step0 = (fun i j => raw35589 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35589step0 raw35589; decide +kernel
      have hl : raw35589step0Labels = raw35589Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35589 raw35589Labels permutation154 permutation6
    mixedMoment B raw35589step0 raw35589step0Labels = mixedMoment B raw35589step1 raw35589step1Labels := by
      have ha : raw35589step1 = raw35589step0 := by apply Matrix.ext; unfold raw35589step1 raw35589step0; decide +kernel
      have hl : raw35589step0Labels = labelEmbedding9 ∘ raw35589step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35589step0 raw35589step0Labels raw35589step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical35590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35590 raw35590Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw35590 raw35590Labels = mixedMoment B raw35590step0 raw35590step0Labels := by
      have hz : ∀ j, raw35590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35590step0 = (fun i j => raw35590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35590step0 raw35590; decide +kernel
      have hl : raw35590step0Labels = raw35590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35590 raw35590Labels permutation346 hz
    mixedMoment B raw35590step0 raw35590step0Labels = mixedMoment B raw35590step1 raw35590step1Labels := by
      have ha : raw35590step1 = (fun i j => raw35590step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35590step1 raw35590step0; decide +kernel
      have hl : raw35590step1Labels = raw35590step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35590step0 raw35590step0Labels permutation34 permutation6
    mixedMoment B raw35590step1 raw35590step1Labels = mixedMoment B raw35590step2 raw35590step2Labels := by
      have ha : raw35590step2 = raw35590step1 := by apply Matrix.ext; unfold raw35590step2 raw35590step1; decide +kernel
      have hl : raw35590step1Labels = labelEmbedding9 ∘ raw35590step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35590step1 raw35590step1Labels raw35590step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

theorem canonical35591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35591 raw35591Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw35591 raw35591Labels = mixedMoment B raw35591step0 raw35591step0Labels := by
      have hz : ∀ j, raw35591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35591step0 = (fun i j => raw35591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35591step0 raw35591; decide +kernel
      have hl : raw35591step0Labels = raw35591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35591 raw35591Labels permutation346 hz
    mixedMoment B raw35591step0 raw35591step0Labels = mixedMoment B raw35591step1 raw35591step1Labels := by
      have ha : raw35591step1 = (fun i j => raw35591step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35591step1 raw35591step0; decide +kernel
      have hl : raw35591step1Labels = raw35591step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35591step0 raw35591step0Labels permutation34 permutation6
    mixedMoment B raw35591step1 raw35591step1Labels = mixedMoment B raw35591step2 raw35591step2Labels := by
      have ha : raw35591step2 = raw35591step1 := by apply Matrix.ext; unfold raw35591step2 raw35591step1; decide +kernel
      have hl : raw35591step1Labels = labelEmbedding9 ∘ raw35591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35591step1 raw35591step1Labels raw35591step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5388 node5388Labels := by rfl

theorem canonical35592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35592 raw35592Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw35592 raw35592Labels = mixedMoment B raw35592step0 raw35592step0Labels := by
      have hz : ∀ j, raw35592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35592step0 = (fun i j => raw35592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35592step0 raw35592; decide +kernel
      have hl : raw35592step0Labels = raw35592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35592 raw35592Labels permutation346 hz
    mixedMoment B raw35592step0 raw35592step0Labels = mixedMoment B raw35592step1 raw35592step1Labels := by
      have ha : raw35592step1 = (fun i j => raw35592step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35592step1 raw35592step0; decide +kernel
      have hl : raw35592step1Labels = raw35592step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35592step0 raw35592step0Labels permutation32 permutation4
    mixedMoment B raw35592step1 raw35592step1Labels = mixedMoment B raw35592step2 raw35592step2Labels := by
      have ha : raw35592step2 = -raw35592step1 := by apply Matrix.ext; change ∀ i j, raw35592step2 i j = -(raw35592step1 i j); unfold raw35592step2 raw35592step1; decide +kernel
      have hl : raw35592step2Labels = raw35592step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35592step2 raw35592step2Labels = mixedMoment B raw35592step3 raw35592step3Labels := by
      have ha : raw35592step3 = raw35592step2 := by apply Matrix.ext; unfold raw35592step3 raw35592step2; decide +kernel
      have hl : raw35592step2Labels = labelEmbedding7 ∘ raw35592step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35592step2 raw35592step2Labels raw35592step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

theorem canonical35593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35593 raw35593Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw35593 raw35593Labels = mixedMoment B raw35593step0 raw35593step0Labels := by
      have hz : ∀ j, raw35593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35593step0 = (fun i j => raw35593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35593step0 raw35593; decide +kernel
      have hl : raw35593step0Labels = raw35593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35593 raw35593Labels permutation346 hz
    mixedMoment B raw35593step0 raw35593step0Labels = mixedMoment B raw35593step1 raw35593step1Labels := by
      have ha : raw35593step1 = (fun i j => raw35593step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35593step1 raw35593step0; decide +kernel
      have hl : raw35593step1Labels = raw35593step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35593step0 raw35593step0Labels permutation32 permutation6
    mixedMoment B raw35593step1 raw35593step1Labels = mixedMoment B raw35593step2 raw35593step2Labels := by
      have ha : raw35593step2 = raw35593step1 := by apply Matrix.ext; unfold raw35593step2 raw35593step1; decide +kernel
      have hl : raw35593step1Labels = labelEmbedding9 ∘ raw35593step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35593step1 raw35593step1Labels raw35593step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

theorem canonical35594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35594 raw35594Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw35594 raw35594Labels = mixedMoment B raw35594step0 raw35594step0Labels := by
      have ha : raw35594step0 = (fun i j => raw35594 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35594step0 raw35594; decide +kernel
      have hl : raw35594step0Labels = raw35594Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35594 raw35594Labels permutation152 permutation6
    mixedMoment B raw35594step0 raw35594step0Labels = mixedMoment B raw35594step1 raw35594step1Labels := by
      have ha : raw35594step1 = raw35594step0 := by apply Matrix.ext; unfold raw35594step1 raw35594step0; decide +kernel
      have hl : raw35594step0Labels = labelEmbedding9 ∘ raw35594step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35594step0 raw35594step0Labels raw35594step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical35595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35595 raw35595Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw35595 raw35595Labels = mixedMoment B raw35595step0 raw35595step0Labels := by
      have hz : ∀ j, raw35595 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35595step0 = (fun i j => raw35595 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35595step0 raw35595; decide +kernel
      have hl : raw35595step0Labels = raw35595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35595 raw35595Labels permutation346 hz
    mixedMoment B raw35595step0 raw35595step0Labels = mixedMoment B raw35595step1 raw35595step1Labels := by
      have ha : raw35595step1 = (fun i j => raw35595step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35595step1 raw35595step0; decide +kernel
      have hl : raw35595step1Labels = raw35595step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35595step0 raw35595step0Labels permutation32 permutation6
    mixedMoment B raw35595step1 raw35595step1Labels = mixedMoment B raw35595step2 raw35595step2Labels := by
      have ha : raw35595step2 = raw35595step1 := by apply Matrix.ext; unfold raw35595step2 raw35595step1; decide +kernel
      have hl : raw35595step1Labels = labelEmbedding9 ∘ raw35595step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35595step1 raw35595step1Labels raw35595step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

theorem canonical35596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35596 raw35596Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw35596 raw35596Labels = mixedMoment B raw35596step0 raw35596step0Labels := by
      have hz : ∀ j, raw35596 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35596step0 = (fun i j => raw35596 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35596step0 raw35596; decide +kernel
      have hl : raw35596step0Labels = raw35596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35596 raw35596Labels permutation346 hz
    mixedMoment B raw35596step0 raw35596step0Labels = mixedMoment B raw35596step1 raw35596step1Labels := by
      have ha : raw35596step1 = (fun i j => raw35596step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35596step1 raw35596step0; decide +kernel
      have hl : raw35596step1Labels = raw35596step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35596step0 raw35596step0Labels permutation32 permutation6
    mixedMoment B raw35596step1 raw35596step1Labels = mixedMoment B raw35596step2 raw35596step2Labels := by
      have ha : raw35596step2 = raw35596step1 := by apply Matrix.ext; unfold raw35596step2 raw35596step1; decide +kernel
      have hl : raw35596step1Labels = labelEmbedding9 ∘ raw35596step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35596step1 raw35596step1Labels raw35596step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5388 node5388Labels := by rfl

theorem canonical35597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35597 raw35597Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw35597 raw35597Labels = mixedMoment B raw35597step0 raw35597step0Labels := by
      have hz : ∀ j, raw35597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35597step0 = (fun i j => raw35597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35597step0 raw35597; decide +kernel
      have hl : raw35597step0Labels = raw35597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35597 raw35597Labels permutation346 hz
    mixedMoment B raw35597step0 raw35597step0Labels = mixedMoment B raw35597step1 raw35597step1Labels := by
      have ha : raw35597step1 = (fun i j => raw35597step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35597step1 raw35597step0; decide +kernel
      have hl : raw35597step1Labels = raw35597step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35597step0 raw35597step0Labels permutation32 permutation4
    mixedMoment B raw35597step1 raw35597step1Labels = mixedMoment B raw35597step2 raw35597step2Labels := by
      have ha : raw35597step2 = -raw35597step1 := by apply Matrix.ext; change ∀ i j, raw35597step2 i j = -(raw35597step1 i j); unfold raw35597step2 raw35597step1; decide +kernel
      have hl : raw35597step2Labels = raw35597step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35597step2 raw35597step2Labels = mixedMoment B raw35597step3 raw35597step3Labels := by
      have ha : raw35597step3 = raw35597step2 := by apply Matrix.ext; unfold raw35597step3 raw35597step2; decide +kernel
      have hl : raw35597step2Labels = labelEmbedding7 ∘ raw35597step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35597step2 raw35597step2Labels raw35597step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

theorem canonical35598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35598 raw35598Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw35598 raw35598Labels = mixedMoment B raw35598step0 raw35598step0Labels := by
      have hz : ∀ j, raw35598 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35598step0 = (fun i j => raw35598 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35598step0 raw35598; decide +kernel
      have hl : raw35598step0Labels = raw35598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35598 raw35598Labels permutation346 hz
    mixedMoment B raw35598step0 raw35598step0Labels = mixedMoment B raw35598step1 raw35598step1Labels := by
      have ha : raw35598step1 = (fun i j => raw35598step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35598step1 raw35598step0; decide +kernel
      have hl : raw35598step1Labels = raw35598step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35598step0 raw35598step0Labels permutation145 permutation4
    mixedMoment B raw35598step1 raw35598step1Labels = mixedMoment B raw35598step2 raw35598step2Labels := by
      have ha : raw35598step2 = raw35598step1 := by apply Matrix.ext; unfold raw35598step2 raw35598step1; decide +kernel
      have hl : raw35598step1Labels = labelEmbedding7 ∘ raw35598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35598step1 raw35598step1Labels raw35598step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

theorem canonical35599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35599 raw35599Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw35599 raw35599Labels = mixedMoment B raw35599step0 raw35599step0Labels := by
      have ha : raw35599step0 = (fun i j => raw35599 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35599step0 raw35599; decide +kernel
      have hl : raw35599step0Labels = raw35599Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35599 raw35599Labels permutation662 permutation4
    mixedMoment B raw35599step0 raw35599step0Labels = mixedMoment B raw35599step1 raw35599step1Labels := by
      have ha : raw35599step1 = raw35599step0 := by apply Matrix.ext; unfold raw35599step1 raw35599step0; decide +kernel
      have hl : raw35599step0Labels = labelEmbedding7 ∘ raw35599step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35599step0 raw35599step0Labels raw35599step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

theorem canonical35600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35600 raw35600Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw35600 raw35600Labels = mixedMoment B raw35600step0 raw35600step0Labels := by
      have hz : ∀ j, raw35600 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35600step0 = (fun i j => raw35600 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35600step0 raw35600; decide +kernel
      have hl : raw35600step0Labels = raw35600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35600 raw35600Labels permutation346 hz
    mixedMoment B raw35600step0 raw35600step0Labels = mixedMoment B raw35600step1 raw35600step1Labels := by
      have ha : raw35600step1 = (fun i j => raw35600step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35600step1 raw35600step0; decide +kernel
      have hl : raw35600step1Labels = raw35600step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35600step0 raw35600step0Labels permutation149 permutation4
    mixedMoment B raw35600step1 raw35600step1Labels = mixedMoment B raw35600step2 raw35600step2Labels := by
      have ha : raw35600step2 = raw35600step1 := by apply Matrix.ext; unfold raw35600step2 raw35600step1; decide +kernel
      have hl : raw35600step1Labels = labelEmbedding7 ∘ raw35600step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35600step1 raw35600step1Labels raw35600step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

theorem canonical35601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35601 raw35601Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw35601 raw35601Labels = mixedMoment B raw35601step0 raw35601step0Labels := by
      have hz : ∀ j, raw35601 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35601step0 = (fun i j => raw35601 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35601step0 raw35601; decide +kernel
      have hl : raw35601step0Labels = raw35601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35601 raw35601Labels permutation346 hz
    mixedMoment B raw35601step0 raw35601step0Labels = mixedMoment B raw35601step1 raw35601step1Labels := by
      have ha : raw35601step1 = (fun i j => raw35601step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35601step1 raw35601step0; decide +kernel
      have hl : raw35601step1Labels = raw35601step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35601step0 raw35601step0Labels permutation143 permutation4
    mixedMoment B raw35601step1 raw35601step1Labels = mixedMoment B raw35601step2 raw35601step2Labels := by
      have ha : raw35601step2 = raw35601step1 := by apply Matrix.ext; unfold raw35601step2 raw35601step1; decide +kernel
      have hl : raw35601step1Labels = labelEmbedding7 ∘ raw35601step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35601step1 raw35601step1Labels raw35601step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

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

theorem singleton5237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5237 node5237Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2684 node2684Labels + mixedMoment B node3394 node3394Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2253 singletonSmall5237
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5237) = raw2253Labels := by decide +kernel
  rw [hl, canonical2253 B hB] at h
  have hc0 : mixedMoment B raw2253 (Fin.cases (0 : Fin 2) singletonSmall5237) =
      mixedMoment B node2684 node2684Labels := by
    have ha : raw2253 = raw2254 := by apply Matrix.ext; unfold raw2253 raw2254; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5237 = raw2254Labels := by decide +kernel
    rw [ha, hj, canonical2254 B hB]
  have hc1 : mixedMoment B raw2253 (Fin.cases (1 : Fin 2) singletonSmall5237) =
      mixedMoment B node3394 node3394Labels := by
    have ha : raw2253 = raw2255 := by apply Matrix.ext; unfold raw2253 raw2255; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5237 = raw2255Labels := by decide +kernel
    rw [ha, hj, canonical2255 B hB]
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

theorem singleton5248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5248 node5248Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2705 node2705Labels + mixedMoment B node3498 node3498Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2265 singletonSmall5248
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5248) = raw2265Labels := by decide +kernel
  rw [hl, canonical2265 B hB] at h
  have hc0 : mixedMoment B raw2265 (Fin.cases (0 : Fin 2) singletonSmall5248) =
      mixedMoment B node2705 node2705Labels := by
    have ha : raw2265 = raw2266 := by apply Matrix.ext; unfold raw2265 raw2266; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5248 = raw2266Labels := by decide +kernel
    rw [ha, hj, canonical2266 B hB]
  have hc1 : mixedMoment B raw2265 (Fin.cases (1 : Fin 2) singletonSmall5248) =
      mixedMoment B node3498 node3498Labels := by
    have ha : raw2265 = raw2267 := by apply Matrix.ext; unfold raw2265 raw2267; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5248 = raw2267Labels := by decide +kernel
    rw [ha, hj, canonical2267 B hB]
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

theorem singleton5354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5354 node5354Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3692 node3692Labels + mixedMoment B node3769 node3769Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2397 singletonSmall5354
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5354) = raw2397Labels := by decide +kernel
  rw [hl, canonical2397 B hB] at h
  have hc0 : mixedMoment B raw2397 (Fin.cases (0 : Fin 2) singletonSmall5354) =
      mixedMoment B node3692 node3692Labels := by
    have ha : raw2397 = raw2398 := by apply Matrix.ext; unfold raw2397 raw2398; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5354 = raw2398Labels := by decide +kernel
    rw [ha, hj, canonical2398 B hB]
  have hc1 : mixedMoment B raw2397 (Fin.cases (1 : Fin 2) singletonSmall5354) =
      mixedMoment B node3769 node3769Labels := by
    have ha : raw2397 = raw2399 := by apply Matrix.ext; unfold raw2397 raw2399; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5354 = raw2399Labels := by decide +kernel
    rw [ha, hj, canonical2399 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5370 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5370 node5370Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3706 node3706Labels + mixedMoment B node3771 node3771Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2418 singletonSmall5370
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5370) = raw2418Labels := by decide +kernel
  rw [hl, canonical2418 B hB] at h
  have hc0 : mixedMoment B raw2418 (Fin.cases (0 : Fin 2) singletonSmall5370) =
      mixedMoment B node3706 node3706Labels := by
    have ha : raw2418 = raw2419 := by apply Matrix.ext; unfold raw2418 raw2419; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5370 = raw2419Labels := by decide +kernel
    rw [ha, hj, canonical2419 B hB]
  have hc1 : mixedMoment B raw2418 (Fin.cases (1 : Fin 2) singletonSmall5370) =
      mixedMoment B node3771 node3771Labels := by
    have ha : raw2418 = raw2420 := by apply Matrix.ext; unfold raw2418 raw2420; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5370 = raw2420Labels := by decide +kernel
    rw [ha, hj, canonical2420 B hB]
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

theorem singleton5384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5384 node5384Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3732 node3732Labels + mixedMoment B node3811 node3811Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2439 singletonSmall5384
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5384) = raw2439Labels := by decide +kernel
  rw [hl, canonical2439 B hB] at h
  have hc0 : mixedMoment B raw2439 (Fin.cases (0 : Fin 2) singletonSmall5384) =
      mixedMoment B node3732 node3732Labels := by
    have ha : raw2439 = raw2440 := by apply Matrix.ext; unfold raw2439 raw2440; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5384 = raw2440Labels := by decide +kernel
    rw [ha, hj, canonical2440 B hB]
  have hc1 : mixedMoment B raw2439 (Fin.cases (1 : Fin 2) singletonSmall5384) =
      mixedMoment B node3811 node3811Labels := by
    have ha : raw2439 = raw2441 := by apply Matrix.ext; unfold raw2439 raw2441; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5384 = raw2441Labels := by decide +kernel
    rw [ha, hj, canonical2441 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound2684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2684 node2684Labels = Sparse.eval nodeValue2684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2684) = mixedMoment B node2684 node2684Labels := rfl
  simpa [nodeValue2684, Sparse.eval] using hc.symm

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

theorem sound2705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2705 node2705Labels = Sparse.eval nodeValue2705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2705) = mixedMoment B node2705 node2705Labels := rfl
  simpa [nodeValue2705, Sparse.eval] using hc.symm

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

theorem sound3394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3394 node3394Labels = Sparse.eval nodeValue3394 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3394) = mixedMoment B node3394 node3394Labels := rfl
  simpa [nodeValue3394, Sparse.eval] using hc.symm

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

theorem sound3498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3498 node3498Labels = Sparse.eval nodeValue3498 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3498) = mixedMoment B node3498 node3498Labels := rfl
  simpa [nodeValue3498, Sparse.eval] using hc.symm

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

theorem sound3692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3692 node3692Labels = Sparse.eval nodeValue3692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3692) = mixedMoment B node3692 node3692Labels := rfl
  simpa [nodeValue3692, Sparse.eval] using hc.symm

theorem sound3706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3706 node3706Labels = Sparse.eval nodeValue3706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3706) = mixedMoment B node3706 node3706Labels := rfl
  simpa [nodeValue3706, Sparse.eval] using hc.symm

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

theorem sound3721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3721 node3721Labels = Sparse.eval nodeValue3721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3721) = mixedMoment B node3721 node3721Labels := rfl
  simpa [nodeValue3721, Sparse.eval] using hc.symm

theorem sound3732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3732 node3732Labels = Sparse.eval nodeValue3732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3732) = mixedMoment B node3732 node3732Labels := rfl
  simpa [nodeValue3732, Sparse.eval] using hc.symm

theorem sound3757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3757 node3757Labels = Sparse.eval nodeValue3757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3757) = mixedMoment B node3757 node3757Labels := rfl
  simpa [nodeValue3757, Sparse.eval] using hc.symm

theorem sound3769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3769 node3769Labels = Sparse.eval nodeValue3769 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3769) = mixedMoment B node3769 node3769Labels := rfl
  simpa [nodeValue3769, Sparse.eval] using hc.symm

theorem sound3771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3771 node3771Labels = Sparse.eval nodeValue3771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3771) = mixedMoment B node3771 node3771Labels := rfl
  simpa [nodeValue3771, Sparse.eval] using hc.symm

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

theorem sound3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3795 node3795Labels = Sparse.eval nodeValue3795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3795) = mixedMoment B node3795 node3795Labels := rfl
  simpa [nodeValue3795, Sparse.eval] using hc.symm

theorem sound3811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3811 node3811Labels = Sparse.eval nodeValue3811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3811) = mixedMoment B node3811 node3811Labels := rfl
  simpa [nodeValue3811, Sparse.eval] using hc.symm

theorem sound3836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3836 node3836Labels = Sparse.eval nodeValue3836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3836) = mixedMoment B node3836 node3836Labels := rfl
  simpa [nodeValue3836, Sparse.eval] using hc.symm

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

theorem sound5219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5219 node5219Labels = Sparse.eval nodeValue5219 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5219) = mixedMoment B node5219 node5219Labels := rfl
  simpa [nodeValue5219, Sparse.eval] using hc.symm

theorem sound5222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5222 node5222Labels = Sparse.eval nodeValue5222 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5222) = mixedMoment B node5222 node5222Labels := rfl
  simpa [nodeValue5222, Sparse.eval] using hc.symm

theorem sound5228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5228 node5228Labels = Sparse.eval nodeValue5228 (mixedVector B) := by
  have h := singleton5228 B _hB
  rw [sound2672 B _hB _hF, sound3391 B _hB _hF] at h
  norm_num [nodeValue5228, nodeValue2672, nodeValue3391, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5231 node5231Labels = Sparse.eval nodeValue5231 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5231) = mixedMoment B node5231 node5231Labels := rfl
  simpa [nodeValue5231, Sparse.eval] using hc.symm

theorem sound5233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5233 node5233Labels = Sparse.eval nodeValue5233 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5233) = mixedMoment B node5233 node5233Labels := rfl
  simpa [nodeValue5233, Sparse.eval] using hc.symm

theorem sound5237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5237 node5237Labels = Sparse.eval nodeValue5237 (mixedVector B) := by
  have h := singleton5237 B _hB
  rw [sound2684 B _hB _hF, sound3394 B _hB _hF] at h
  norm_num [nodeValue5237, nodeValue2684, nodeValue3394, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5243 node5243Labels = Sparse.eval nodeValue5243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5243) = mixedMoment B node5243 node5243Labels := rfl
  simpa [nodeValue5243, Sparse.eval] using hc.symm

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

theorem sound5248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5248 node5248Labels = Sparse.eval nodeValue5248 (mixedVector B) := by
  have h := singleton5248 B _hB
  rw [sound2705 B _hB _hF, sound3498 B _hB _hF] at h
  norm_num [nodeValue5248, nodeValue2705, nodeValue3498, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5264 node5264Labels = Sparse.eval nodeValue5264 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5264) = mixedMoment B node5264 node5264Labels := rfl
  simpa [nodeValue5264, Sparse.eval] using hc.symm

theorem sound5279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5279 node5279Labels = Sparse.eval nodeValue5279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5279) = mixedMoment B node5279 node5279Labels := rfl
  simpa [nodeValue5279, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5367 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5367 node5367Labels = 0 := by
  exact mixedMoment_order_one B hB node5367 node5367Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5369 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5369 node5369Labels = 0 := by
  exact mixedMoment_order_one B hB node5369 node5369Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5354 node5354Labels = Sparse.eval nodeValue5354 (mixedVector B) := by
  have h := singleton5354 B _hB
  rw [sound3692 B _hB _hF, sound3769 B _hB _hF] at h
  norm_num [nodeValue5354, nodeValue3692, nodeValue3769, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5367 node5367Labels = Sparse.eval nodeValue5367 (mixedVector B) := by
  simpa only [nodeValue5367, Sparse.eval_nil] using zero5367 B _hB _hF

theorem sound5369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5369 node5369Labels = Sparse.eval nodeValue5369 (mixedVector B) := by
  simpa only [nodeValue5369, Sparse.eval_nil] using zero5369 B _hB _hF

theorem sound5370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5370 node5370Labels = Sparse.eval nodeValue5370 (mixedVector B) := by
  have h := singleton5370 B _hB
  rw [sound3706 B _hB _hF, sound3771 B _hB _hF] at h
  norm_num [nodeValue5370, nodeValue3706, nodeValue3771, Sparse.eval] at h ⊢
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

theorem sound5378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5378 node5378Labels = Sparse.eval nodeValue5378 (mixedVector B) := by
  have h := singleton5378 B _hB
  rw [sound3719 B _hB _hF, sound3795 B _hB _hF] at h
  norm_num [nodeValue5378, nodeValue3719, nodeValue3795, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5380 node5380Labels = Sparse.eval nodeValue5380 (mixedVector B) := by
  have h := singleton5380 B _hB
  rw [sound3721 B _hB _hF, sound3836 B _hB _hF] at h
  norm_num [nodeValue5380, nodeValue3721, nodeValue3836, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5381 node5381Labels = Sparse.eval nodeValue5381 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5381) = mixedMoment B node5381 node5381Labels := rfl
  simpa [nodeValue5381, Sparse.eval] using hc.symm

theorem sound5384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5384 node5384Labels = Sparse.eval nodeValue5384 (mixedVector B) := by
  have h := singleton5384 B _hB
  rw [sound3732 B _hB _hF, sound3811 B _hB _hF] at h
  norm_num [nodeValue5384, nodeValue3732, nodeValue3811, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources80
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2574 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2574 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2574 + difference 0 1) (sourceB2574 + difference 1 0) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2574 + difference 0 1) (sourceB2574 + difference 1 0) sourceC2574) = raw35572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35572; decide +kernel
    rw [ha]
    exact (canonical35572 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2574 + difference 0 2) (sourceB2574 + difference 2 0) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2574 + difference 0 2) (sourceB2574 + difference 2 0) sourceC2574) = raw35573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35573; decide +kernel
    rw [ha]
    exact (canonical35573 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2574 + difference 0 3) (sourceB2574 + difference 3 0) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2574 + difference 0 3) (sourceB2574 + difference 3 0) sourceC2574) = raw35574 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35574; decide +kernel
    rw [ha]
    exact (canonical35574 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2574 + difference 0 4) (sourceB2574 + difference 4 0) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2574 + difference 0 4) (sourceB2574 + difference 4 0) sourceC2574) = raw35575 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35575; decide +kernel
    rw [ha]
    exact (canonical35575 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2574 + difference 0 5) (sourceB2574 + difference 5 0) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2574 + difference 0 5) (sourceB2574 + difference 5 0) sourceC2574) = raw35576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35576; decide +kernel
    rw [ha]
    exact (canonical35576 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2574 + difference 1 0) (sourceB2574 + difference 0 1) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5279) := by
    have ha : (tripleCharges (sourceA2574 + difference 1 0) (sourceB2574 + difference 0 1) sourceC2574) = raw35577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35577; decide +kernel
    rw [ha]
    exact (canonical35577 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2574 + difference 1 2) (sourceB2574 + difference 2 1) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA2574 + difference 1 2) (sourceB2574 + difference 2 1) sourceC2574) = raw35578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35578; decide +kernel
    rw [ha]
    exact (canonical35578 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2574 + difference 1 3) (sourceB2574 + difference 3 1) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA2574 + difference 1 3) (sourceB2574 + difference 3 1) sourceC2574) = raw35579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35579; decide +kernel
    rw [ha]
    exact (canonical35579 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2574 + difference 1 4) (sourceB2574 + difference 4 1) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA2574 + difference 1 4) (sourceB2574 + difference 4 1) sourceC2574) = raw35580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35580; decide +kernel
    rw [ha]
    exact (canonical35580 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2574 + difference 1 5) (sourceB2574 + difference 5 1) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2574 + difference 1 5) (sourceB2574 + difference 5 1) sourceC2574) = raw35581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35581; decide +kernel
    rw [ha]
    exact (canonical35581 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2574 + difference 2 0) (sourceB2574 + difference 0 2) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5219) := by
    have ha : (tripleCharges (sourceA2574 + difference 2 0) (sourceB2574 + difference 0 2) sourceC2574) = raw35582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35582; decide +kernel
    rw [ha]
    exact (canonical35582 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2574 + difference 2 1) (sourceB2574 + difference 1 2) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2574 + difference 2 1) (sourceB2574 + difference 1 2) sourceC2574) = raw35583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35583; decide +kernel
    rw [ha]
    exact (canonical35583 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2574 + difference 2 3) (sourceB2574 + difference 3 2) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA2574 + difference 2 3) (sourceB2574 + difference 3 2) sourceC2574) = raw35584 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35584; decide +kernel
    rw [ha]
    exact (canonical35584 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2574 + difference 2 4) (sourceB2574 + difference 4 2) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA2574 + difference 2 4) (sourceB2574 + difference 4 2) sourceC2574) = raw35585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35585; decide +kernel
    rw [ha]
    exact (canonical35585 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2574 + difference 2 5) (sourceB2574 + difference 5 2) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2574 + difference 2 5) (sourceB2574 + difference 5 2) sourceC2574) = raw35586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35586; decide +kernel
    rw [ha]
    exact (canonical35586 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2574 + difference 3 0) (sourceB2574 + difference 0 3) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2574 + difference 3 0) (sourceB2574 + difference 0 3) sourceC2574) = raw35587 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35587; decide +kernel
    rw [ha]
    exact (canonical35587 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2574 + difference 3 1) (sourceB2574 + difference 1 3) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2574 + difference 3 1) (sourceB2574 + difference 1 3) sourceC2574) = raw35588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35588; decide +kernel
    rw [ha]
    exact (canonical35588 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2574 + difference 3 2) (sourceB2574 + difference 2 3) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2574 + difference 3 2) (sourceB2574 + difference 2 3) sourceC2574) = raw35589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35589; decide +kernel
    rw [ha]
    exact (canonical35589 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2574 + difference 3 4) (sourceB2574 + difference 4 3) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2574 + difference 3 4) (sourceB2574 + difference 4 3) sourceC2574) = raw35590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35590; decide +kernel
    rw [ha]
    exact (canonical35590 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2574 + difference 3 5) (sourceB2574 + difference 5 3) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2574 + difference 3 5) (sourceB2574 + difference 5 3) sourceC2574) = raw35591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35591; decide +kernel
    rw [ha]
    exact (canonical35591 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2574 + difference 4 0) (sourceB2574 + difference 0 4) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2574 + difference 4 0) (sourceB2574 + difference 0 4) sourceC2574) = raw35592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35592; decide +kernel
    rw [ha]
    exact (canonical35592 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2574 + difference 4 1) (sourceB2574 + difference 1 4) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2574 + difference 4 1) (sourceB2574 + difference 1 4) sourceC2574) = raw35593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35593; decide +kernel
    rw [ha]
    exact (canonical35593 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2574 + difference 4 2) (sourceB2574 + difference 2 4) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2574 + difference 4 2) (sourceB2574 + difference 2 4) sourceC2574) = raw35594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35594; decide +kernel
    rw [ha]
    exact (canonical35594 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2574 + difference 4 3) (sourceB2574 + difference 3 4) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2574 + difference 4 3) (sourceB2574 + difference 3 4) sourceC2574) = raw35595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35595; decide +kernel
    rw [ha]
    exact (canonical35595 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2574 + difference 4 5) (sourceB2574 + difference 5 4) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2574 + difference 4 5) (sourceB2574 + difference 5 4) sourceC2574) = raw35596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35596; decide +kernel
    rw [ha]
    exact (canonical35596 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2574 + difference 5 0) (sourceB2574 + difference 0 5) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA2574 + difference 5 0) (sourceB2574 + difference 0 5) sourceC2574) = raw35597 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35597; decide +kernel
    rw [ha]
    exact (canonical35597 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2574 + difference 5 1) (sourceB2574 + difference 1 5) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2574 + difference 5 1) (sourceB2574 + difference 1 5) sourceC2574) = raw35598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35598; decide +kernel
    rw [ha]
    exact (canonical35598 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2574 + difference 5 2) (sourceB2574 + difference 2 5) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5243) := by
    have ha : (tripleCharges (sourceA2574 + difference 5 2) (sourceB2574 + difference 2 5) sourceC2574) = raw35599 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35599; decide +kernel
    rw [ha]
    exact (canonical35599 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2574 + difference 5 3) (sourceB2574 + difference 3 5) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA2574 + difference 5 3) (sourceB2574 + difference 3 5) sourceC2574) = raw35600 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35600; decide +kernel
    rw [ha]
    exact (canonical35600 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2574 + difference 5 4) (sourceB2574 + difference 4 5) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA2574 + difference 5 4) (sourceB2574 + difference 4 5) sourceC2574) = raw35601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35601; decide +kernel
    rw [ha]
    exact (canonical35601 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2574 sourceB2574 sourceC2574
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2574, Integer.Sparse.eval]
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

theorem reindexCheck2061 : Integer.Sparse.reindex keyMap MixedData.row2061 = numericRow2061 := by decide +kernel

theorem numericCheck2061 (x : Master → ℝ) : Integer.Sparse.eval numericRow2061 x =
    (8640 : ℝ) * reducedSource2061 x := by
  norm_num [numericRow2061, reducedSource2061, Integer.Sparse.eval, Sparse.eval, nodeValue5219, nodeValue5222, nodeValue5228, nodeValue5231, nodeValue5233, nodeValue5237, nodeValue5243, nodeValue5248, nodeValue5264, nodeValue5279, nodeValue5351, nodeValue5354, nodeValue5367, nodeValue5369, nodeValue5370, nodeValue5378, nodeValue5380, nodeValue5381, nodeValue5384, nodeValue5388, nodeValue5418]
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

theorem reducedZero2061 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2061 (mixedVector B) = 0 := by
  have h5219 : mixedVector B (Sum.inr 5219) = Sparse.eval nodeValue5219 (mixedVector B) := by
    change mixedMoment B node5219 node5219Labels = _
    exact sound5219 B hB hF
  have h5222 : mixedVector B (Sum.inr 5222) = Sparse.eval nodeValue5222 (mixedVector B) := by
    change mixedMoment B node5222 node5222Labels = _
    exact sound5222 B hB hF
  have h5228 : mixedVector B (Sum.inr 5228) = Sparse.eval nodeValue5228 (mixedVector B) := by
    change mixedMoment B node5228 node5228Labels = _
    exact sound5228 B hB hF
  have h5231 : mixedVector B (Sum.inr 5231) = Sparse.eval nodeValue5231 (mixedVector B) := by
    change mixedMoment B node5231 node5231Labels = _
    exact sound5231 B hB hF
  have h5233 : mixedVector B (Sum.inr 5233) = Sparse.eval nodeValue5233 (mixedVector B) := by
    change mixedMoment B node5233 node5233Labels = _
    exact sound5233 B hB hF
  have h5237 : mixedVector B (Sum.inr 5237) = Sparse.eval nodeValue5237 (mixedVector B) := by
    change mixedMoment B node5237 node5237Labels = _
    exact sound5237 B hB hF
  have h5243 : mixedVector B (Sum.inr 5243) = Sparse.eval nodeValue5243 (mixedVector B) := by
    change mixedMoment B node5243 node5243Labels = _
    exact sound5243 B hB hF
  have h5248 : mixedVector B (Sum.inr 5248) = Sparse.eval nodeValue5248 (mixedVector B) := by
    change mixedMoment B node5248 node5248Labels = _
    exact sound5248 B hB hF
  have h5264 : mixedVector B (Sum.inr 5264) = Sparse.eval nodeValue5264 (mixedVector B) := by
    change mixedMoment B node5264 node5264Labels = _
    exact sound5264 B hB hF
  have h5279 : mixedVector B (Sum.inr 5279) = Sparse.eval nodeValue5279 (mixedVector B) := by
    change mixedMoment B node5279 node5279Labels = _
    exact sound5279 B hB hF
  have h5351 : mixedVector B (Sum.inr 5351) = Sparse.eval nodeValue5351 (mixedVector B) := by
    change mixedMoment B node5351 node5351Labels = _
    exact sound5351 B hB hF
  have h5354 : mixedVector B (Sum.inr 5354) = Sparse.eval nodeValue5354 (mixedVector B) := by
    change mixedMoment B node5354 node5354Labels = _
    exact sound5354 B hB hF
  have h5367 : mixedVector B (Sum.inr 5367) = Sparse.eval nodeValue5367 (mixedVector B) := by
    change mixedMoment B node5367 node5367Labels = _
    exact sound5367 B hB hF
  have h5369 : mixedVector B (Sum.inr 5369) = Sparse.eval nodeValue5369 (mixedVector B) := by
    change mixedMoment B node5369 node5369Labels = _
    exact sound5369 B hB hF
  have h5370 : mixedVector B (Sum.inr 5370) = Sparse.eval nodeValue5370 (mixedVector B) := by
    change mixedMoment B node5370 node5370Labels = _
    exact sound5370 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5380 : mixedVector B (Sum.inr 5380) = Sparse.eval nodeValue5380 (mixedVector B) := by
    change mixedMoment B node5380 node5380Labels = _
    exact sound5380 B hB hF
  have h5381 : mixedVector B (Sum.inr 5381) = Sparse.eval nodeValue5381 (mixedVector B) := by
    change mixedMoment B node5381 node5381Labels = _
    exact sound5381 B hB hF
  have h5384 : mixedVector B (Sum.inr 5384) = Sparse.eval nodeValue5384 (mixedVector B) := by
    change mixedMoment B node5384 node5384Labels = _
    exact sound5384 B hB hF
  have h5388 : mixedVector B (Sum.inr 5388) = Sparse.eval nodeValue5388 (mixedVector B) := by
    change mixedMoment B node5388 node5388Labels = _
    exact sound5388_e B hB hF
  have h5418 : mixedVector B (Sum.inr 5418) = Sparse.eval nodeValue5418 (mixedVector B) := by
    change mixedMoment B node5418 node5418Labels = _
    exact sound5418_e B hB hF
  simpa only [sourceForm2574, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5219, h5222, h5228, h5231, h5233, h5237, h5243, h5248, h5264, h5279, h5351, h5354, h5367, h5369, h5370, h5378, h5380, h5381, h5384, h5388, h5418, reducedSource2061] using sourceEq2574 B hB

theorem rowSound2061_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2061 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2061, numericCheck2061, reducedZero2061 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061_e_oai
