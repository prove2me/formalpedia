-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:10:19.579206+00:00
-- url     : https://prove2.me/submissions/c68ed636-498e-450c-91de-ca0bd0555d09

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5416_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5433_e

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

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
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

theorem canonical1686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1686 raw1686Labels = mixedMoment B node4759 node4759Labels := by
  calc
    mixedMoment B raw1686 raw1686Labels = mixedMoment B raw1686step0 raw1686step0Labels := by
      have ha : raw1686step0 = (fun i j => raw1686 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1686step0 raw1686; decide +kernel
      have hl : raw1686step0Labels = raw1686Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1686 raw1686Labels permutation152 permutation4
    mixedMoment B raw1686step0 raw1686step0Labels = mixedMoment B raw1686step1 raw1686step1Labels := by
      have ha : raw1686step1 = raw1686step0 := by apply Matrix.ext; unfold raw1686step1 raw1686step0; decide +kernel
      have hl : raw1686step0Labels = labelEmbedding7 ∘ raw1686step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1686step0 raw1686step0Labels raw1686step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4759 node4759Labels := by rfl

theorem canonical1687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1687 raw1687Labels = mixedMoment B node1959 node1959Labels := by
  calc
    mixedMoment B raw1687 raw1687Labels = mixedMoment B raw1687step0 raw1687step0Labels := by
      have ha : raw1687step0 = (fun i j => raw1687 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1687step0 raw1687; decide +kernel
      have hl : raw1687step0Labels = raw1687Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1687 raw1687Labels permutation152 permutation4
    _ = mixedMoment B node1959 node1959Labels := by rfl

theorem canonical1688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1688 raw1688Labels = mixedMoment B node2170 node2170Labels := by
  calc
    mixedMoment B raw1688 raw1688Labels = mixedMoment B raw1688step0 raw1688step0Labels := by
      have ha : raw1688step0 = (fun i j => raw1688 (permutation662 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1688step0 raw1688; decide +kernel
      have hl : raw1688step0Labels = raw1688Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1688 raw1688Labels permutation662 permutation6
    mixedMoment B raw1688step0 raw1688step0Labels = mixedMoment B raw1688step1 raw1688step1Labels := by
      have ha : raw1688step1 = raw1688step0 := by apply Matrix.ext; unfold raw1688step1 raw1688step0; decide +kernel
      have hl : raw1688step0Labels = labelEmbedding1 ∘ raw1688step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1688step0 raw1688step0Labels raw1688step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2170 node2170Labels := by rfl

theorem canonical1692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1692 raw1692Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw1692 raw1692Labels = mixedMoment B raw1692step0 raw1692step0Labels := by
      have ha : raw1692step0 = (fun i j => raw1692 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1692step0 raw1692; decide +kernel
      have hl : raw1692step0Labels = raw1692Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1692 raw1692Labels permutation152 permutation4
    mixedMoment B raw1692step0 raw1692step0Labels = mixedMoment B raw1692step1 raw1692step1Labels := by
      have ha : raw1692step1 = raw1692step0 := by apply Matrix.ext; unfold raw1692step1 raw1692step0; decide +kernel
      have hl : raw1692step0Labels = labelEmbedding7 ∘ raw1692step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1692step0 raw1692step0Labels raw1692step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4763 node4763Labels := by rfl

theorem canonical1693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1693 raw1693Labels = mixedMoment B node1963 node1963Labels := by
  calc
    mixedMoment B raw1693 raw1693Labels = mixedMoment B raw1693step0 raw1693step0Labels := by
      have ha : raw1693step0 = (fun i j => raw1693 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1693step0 raw1693; decide +kernel
      have hl : raw1693step0Labels = raw1693Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1693 raw1693Labels permutation152 permutation4
    _ = mixedMoment B node1963 node1963Labels := by rfl

theorem canonical1694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1694 raw1694Labels = mixedMoment B node2174 node2174Labels := by
  calc
    mixedMoment B raw1694 raw1694Labels = mixedMoment B raw1694step0 raw1694step0Labels := by
      have ha : raw1694step0 = (fun i j => raw1694 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1694step0 raw1694; decide +kernel
      have hl : raw1694step0Labels = raw1694Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1694 raw1694Labels permutation152 permutation6
    mixedMoment B raw1694step0 raw1694step0Labels = mixedMoment B raw1694step1 raw1694step1Labels := by
      have ha : raw1694step1 = -raw1694step0 := by apply Matrix.ext; change ∀ i j, raw1694step1 i j = -(raw1694step0 i j); unfold raw1694step1 raw1694step0; decide +kernel
      have hl : raw1694step1Labels = raw1694step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1694step1 raw1694step1Labels = mixedMoment B raw1694step2 raw1694step2Labels := by
      have ha : raw1694step2 = raw1694step1 := by apply Matrix.ext; unfold raw1694step2 raw1694step1; decide +kernel
      have hl : raw1694step1Labels = labelEmbedding1 ∘ raw1694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1694step1 raw1694step1Labels raw1694step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2174 node2174Labels := by rfl

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

theorem canonical18382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18382 raw18382Labels = mixedMoment B node5497 node5497Labels := by
  calc
    mixedMoment B raw18382 raw18382Labels = mixedMoment B raw18382step0 raw18382step0Labels := by
      have ha : raw18382step0 = (fun i j => raw18382 (permutation293 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18382step0 raw18382; decide +kernel
      have hl : raw18382step0Labels = raw18382Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18382 raw18382Labels permutation293 permutation2
    _ = mixedMoment B node5497 node5497Labels := by rfl

theorem canonical18386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18386 raw18386Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18386 raw18386Labels = mixedMoment B raw18386step0 raw18386step0Labels := by
      have ha : raw18386step0 = (fun i j => raw18386 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18386step0 raw18386; decide +kernel
      have hl : raw18386step0Labels = raw18386Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18386 raw18386Labels permutation176 permutation3
    mixedMoment B raw18386step0 raw18386step0Labels = mixedMoment B raw18386step1 raw18386step1Labels := by
      have ha : raw18386step1 = raw18386step0 := by apply Matrix.ext; unfold raw18386step1 raw18386step0; decide +kernel
      have hl : raw18386step0Labels = labelEmbedding6 ∘ raw18386step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18386step0 raw18386step0Labels raw18386step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical18395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18395 raw18395Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw18395 raw18395Labels = mixedMoment B raw18395step0 raw18395step0Labels := by
      have ha : raw18395step0 = (fun i j => raw18395 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18395step0 raw18395; decide +kernel
      have hl : raw18395step0Labels = raw18395Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18395 raw18395Labels permutation155 permutation3
    mixedMoment B raw18395step0 raw18395step0Labels = mixedMoment B raw18395step1 raw18395step1Labels := by
      have ha : raw18395step1 = raw18395step0 := by apply Matrix.ext; unfold raw18395step1 raw18395step0; decide +kernel
      have hl : raw18395step0Labels = labelEmbedding6 ∘ raw18395step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18395step0 raw18395step0Labels raw18395step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

theorem canonical18400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18400 raw18400Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw18400 raw18400Labels = mixedMoment B raw18400step0 raw18400step0Labels := by
      have ha : raw18400step0 = (fun i j => raw18400 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18400step0 raw18400; decide +kernel
      have hl : raw18400step0Labels = raw18400Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18400 raw18400Labels permutation153 permutation3
    mixedMoment B raw18400step0 raw18400step0Labels = mixedMoment B raw18400step1 raw18400step1Labels := by
      have ha : raw18400step1 = raw18400step0 := by apply Matrix.ext; unfold raw18400step1 raw18400step0; decide +kernel
      have hl : raw18400step0Labels = labelEmbedding6 ∘ raw18400step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18400step0 raw18400step0Labels raw18400step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

theorem canonical18402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18402 raw18402Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw18402 raw18402Labels = mixedMoment B raw18402step0 raw18402step0Labels := by
      have ha : raw18402step0 = (fun i j => raw18402 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18402step0 raw18402; decide +kernel
      have hl : raw18402step0Labels = raw18402Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18402 raw18402Labels permutation158 permutation3
    mixedMoment B raw18402step0 raw18402step0Labels = mixedMoment B raw18402step1 raw18402step1Labels := by
      have ha : raw18402step1 = raw18402step0 := by apply Matrix.ext; unfold raw18402step1 raw18402step0; decide +kernel
      have hl : raw18402step0Labels = labelEmbedding6 ∘ raw18402step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18402step0 raw18402step0Labels raw18402step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

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

theorem canonical2370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2370 raw2370Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw2370 raw2370Labels = mixedMoment B raw2370step0 raw2370step0Labels := by
      have ha : raw2370step0 = (fun i j => raw2370 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2370step0 raw2370; decide +kernel
      have hl : raw2370step0Labels = raw2370Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2370 raw2370Labels permutation152 permutation4
    mixedMoment B raw2370step0 raw2370step0Labels = mixedMoment B raw2370step1 raw2370step1Labels := by
      have ha : raw2370step1 = raw2370step0 := by apply Matrix.ext; unfold raw2370step1 raw2370step0; decide +kernel
      have hl : raw2370step0Labels = labelEmbedding7 ∘ raw2370step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2370step0 raw2370step0Labels raw2370step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5335 node5335Labels := by rfl

theorem canonical2371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2371 raw2371Labels = mixedMoment B node3670 node3670Labels := by
  calc
    mixedMoment B raw2371 raw2371Labels = mixedMoment B raw2371step0 raw2371step0Labels := by
      have ha : raw2371step0 = (fun i j => raw2371 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2371step0 raw2371; decide +kernel
      have hl : raw2371step0Labels = raw2371Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2371 raw2371Labels permutation152 permutation4
    _ = mixedMoment B node3670 node3670Labels := by rfl

theorem canonical2372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2372 raw2372Labels = mixedMoment B node3753 node3753Labels := by
  calc
    mixedMoment B raw2372 raw2372Labels = mixedMoment B raw2372step0 raw2372step0Labels := by
      have ha : raw2372step0 = (fun i j => raw2372 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2372step0 raw2372; decide +kernel
      have hl : raw2372step0Labels = raw2372Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2372 raw2372Labels permutation688 permutation6
    mixedMoment B raw2372step0 raw2372step0Labels = mixedMoment B raw2372step1 raw2372step1Labels := by
      have ha : raw2372step1 = raw2372step0 := by apply Matrix.ext; unfold raw2372step1 raw2372step0; decide +kernel
      have hl : raw2372step0Labels = labelEmbedding1 ∘ raw2372step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2372step0 raw2372step0Labels raw2372step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3753 node3753Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical266
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34080 raw34080Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw34080 raw34080Labels = mixedMoment B raw34080step0 raw34080step0Labels := by
      have ha : raw34080step0 = (fun i j => raw34080 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34080step0 raw34080; decide +kernel
      have hl : raw34080step0Labels = raw34080Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34080 raw34080Labels permutation176 permutation3
    mixedMoment B raw34080step0 raw34080step0Labels = mixedMoment B raw34080step1 raw34080step1Labels := by
      have ha : raw34080step1 = raw34080step0 := by apply Matrix.ext; unfold raw34080step1 raw34080step0; decide +kernel
      have hl : raw34080step0Labels = labelEmbedding6 ∘ raw34080step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34080step0 raw34080step0Labels raw34080step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

theorem canonical34087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34087 raw34087Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw34087 raw34087Labels = mixedMoment B raw34087step0 raw34087step0Labels := by
      have ha : raw34087step0 = (fun i j => raw34087 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34087step0 raw34087; decide +kernel
      have hl : raw34087step0Labels = raw34087Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34087 raw34087Labels permutation154 permutation3
    mixedMoment B raw34087step0 raw34087step0Labels = mixedMoment B raw34087step1 raw34087step1Labels := by
      have ha : raw34087step1 = raw34087step0 := by apply Matrix.ext; unfold raw34087step1 raw34087step0; decide +kernel
      have hl : raw34087step0Labels = labelEmbedding6 ∘ raw34087step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34087step0 raw34087step0Labels raw34087step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4763 node4763Labels := by rfl

theorem canonical34091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34091 raw34091Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw34091 raw34091Labels = mixedMoment B raw34091step0 raw34091step0Labels := by
      have ha : raw34091step0 = (fun i j => raw34091 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34091step0 raw34091; decide +kernel
      have hl : raw34091step0Labels = raw34091Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34091 raw34091Labels permutation152 permutation3
    mixedMoment B raw34091step0 raw34091step0Labels = mixedMoment B raw34091step1 raw34091step1Labels := by
      have ha : raw34091step1 = raw34091step0 := by apply Matrix.ext; unfold raw34091step1 raw34091step0; decide +kernel
      have hl : raw34091step0Labels = labelEmbedding6 ∘ raw34091step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34091step0 raw34091step0Labels raw34091step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4763 node4763Labels := by rfl

theorem canonical34094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34094 raw34094Labels = mixedMoment B node4759 node4759Labels := by
  calc
    mixedMoment B raw34094 raw34094Labels = mixedMoment B raw34094step0 raw34094step0Labels := by
      have ha : raw34094step0 = (fun i j => raw34094 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34094step0 raw34094; decide +kernel
      have hl : raw34094step0Labels = raw34094Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34094 raw34094Labels permutation152 permutation3
    mixedMoment B raw34094step0 raw34094step0Labels = mixedMoment B raw34094step1 raw34094step1Labels := by
      have ha : raw34094step1 = raw34094step0 := by apply Matrix.ext; unfold raw34094step1 raw34094step0; decide +kernel
      have hl : raw34094step0Labels = labelEmbedding6 ∘ raw34094step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34094step0 raw34094step0Labels raw34094step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4759 node4759Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical291
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical37251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37251 raw37251Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw37251 raw37251Labels = mixedMoment B raw37251step0 raw37251step0Labels := by
      have ha : raw37251step0 = (fun i j => raw37251 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37251step0 raw37251; decide +kernel
      have hl : raw37251step0Labels = raw37251Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37251 raw37251Labels permutation663 permutation3
    mixedMoment B raw37251step0 raw37251step0Labels = mixedMoment B raw37251step1 raw37251step1Labels := by
      have ha : raw37251step1 = -raw37251step0 := by apply Matrix.ext; change ∀ i j, raw37251step1 i j = -(raw37251step0 i j); unfold raw37251step1 raw37251step0; decide +kernel
      have hl : raw37251step1Labels = raw37251step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37251step1 raw37251step1Labels = mixedMoment B raw37251step2 raw37251step2Labels := by
      have ha : raw37251step2 = raw37251step1 := by apply Matrix.ext; unfold raw37251step2 raw37251step1; decide +kernel
      have hl : raw37251step1Labels = labelEmbedding6 ∘ raw37251step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37251step1 raw37251step1Labels raw37251step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

theorem canonical37252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37252 raw37252Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw37252 raw37252Labels = mixedMoment B raw37252step0 raw37252step0Labels := by
      have ha : raw37252step0 = (fun i j => raw37252 (permutation661 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37252step0 raw37252; decide +kernel
      have hl : raw37252step0Labels = raw37252Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37252 raw37252Labels permutation661 permutation3
    mixedMoment B raw37252step0 raw37252step0Labels = mixedMoment B raw37252step1 raw37252step1Labels := by
      have ha : raw37252step1 = -raw37252step0 := by apply Matrix.ext; change ∀ i j, raw37252step1 i j = -(raw37252step0 i j); unfold raw37252step1 raw37252step0; decide +kernel
      have hl : raw37252step1Labels = raw37252step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37252step1 raw37252step1Labels = mixedMoment B raw37252step2 raw37252step2Labels := by
      have ha : raw37252step2 = raw37252step1 := by apply Matrix.ext; unfold raw37252step2 raw37252step1; decide +kernel
      have hl : raw37252step1Labels = labelEmbedding6 ∘ raw37252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37252step1 raw37252step1Labels raw37252step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

theorem canonical37253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37253 raw37253Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw37253 raw37253Labels = mixedMoment B raw37253step0 raw37253step0Labels := by
      have ha : raw37253step0 = (fun i j => raw37253 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37253step0 raw37253; decide +kernel
      have hl : raw37253step0Labels = raw37253Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37253 raw37253Labels permutation662 permutation3
    mixedMoment B raw37253step0 raw37253step0Labels = mixedMoment B raw37253step1 raw37253step1Labels := by
      have ha : raw37253step1 = -raw37253step0 := by apply Matrix.ext; change ∀ i j, raw37253step1 i j = -(raw37253step0 i j); unfold raw37253step1 raw37253step0; decide +kernel
      have hl : raw37253step1Labels = raw37253step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37253step1 raw37253step1Labels = mixedMoment B raw37253step2 raw37253step2Labels := by
      have ha : raw37253step2 = raw37253step1 := by apply Matrix.ext; unfold raw37253step2 raw37253step1; decide +kernel
      have hl : raw37253step1Labels = labelEmbedding6 ∘ raw37253step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37253step1 raw37253step1Labels raw37253step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical37254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37254 raw37254Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw37254 raw37254Labels = mixedMoment B raw37254step0 raw37254step0Labels := by
      have ha : raw37254step0 = (fun i j => raw37254 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37254step0 raw37254; decide +kernel
      have hl : raw37254step0Labels = raw37254Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37254 raw37254Labels permutation176 permutation3
    mixedMoment B raw37254step0 raw37254step0Labels = mixedMoment B raw37254step1 raw37254step1Labels := by
      have ha : raw37254step1 = raw37254step0 := by apply Matrix.ext; unfold raw37254step1 raw37254step0; decide +kernel
      have hl : raw37254step0Labels = labelEmbedding6 ∘ raw37254step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37254step0 raw37254step0Labels raw37254step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

theorem canonical37255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37255 raw37255Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw37255 raw37255Labels = mixedMoment B raw37255step0 raw37255step0Labels := by
      have ha : raw37255step0 = (fun i j => raw37255 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37255step0 raw37255; decide +kernel
      have hl : raw37255step0Labels = raw37255Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37255 raw37255Labels permutation188 permutation3
    mixedMoment B raw37255step0 raw37255step0Labels = mixedMoment B raw37255step1 raw37255step1Labels := by
      have ha : raw37255step1 = raw37255step0 := by apply Matrix.ext; unfold raw37255step1 raw37255step0; decide +kernel
      have hl : raw37255step0Labels = labelEmbedding6 ∘ raw37255step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37255step0 raw37255step0Labels raw37255step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

theorem canonical37256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37256 raw37256Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw37256 raw37256Labels = mixedMoment B raw37256step0 raw37256step0Labels := by
      have ha : raw37256step0 = (fun i j => raw37256 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37256step0 raw37256; decide +kernel
      have hl : raw37256step0Labels = raw37256Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37256 raw37256Labels permutation154 permutation3
    mixedMoment B raw37256step0 raw37256step0Labels = mixedMoment B raw37256step1 raw37256step1Labels := by
      have ha : raw37256step1 = raw37256step0 := by apply Matrix.ext; unfold raw37256step1 raw37256step0; decide +kernel
      have hl : raw37256step0Labels = labelEmbedding6 ∘ raw37256step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37256step0 raw37256step0Labels raw37256step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5335 node5335Labels := by rfl

theorem canonical37257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37257 raw37257Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw37257 raw37257Labels = mixedMoment B raw37257step0 raw37257step0Labels := by
      have ha : raw37257step0 = (fun i j => raw37257 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37257step0 raw37257; decide +kernel
      have hl : raw37257step0Labels = raw37257Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37257 raw37257Labels permutation178 permutation3
    mixedMoment B raw37257step0 raw37257step0Labels = mixedMoment B raw37257step1 raw37257step1Labels := by
      have ha : raw37257step1 = raw37257step0 := by apply Matrix.ext; unfold raw37257step1 raw37257step0; decide +kernel
      have hl : raw37257step0Labels = labelEmbedding6 ∘ raw37257step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37257step0 raw37257step0Labels raw37257step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5335 node5335Labels := by rfl

theorem canonical37258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37258 raw37258Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw37258 raw37258Labels = mixedMoment B raw37258step0 raw37258step0Labels := by
      have ha : raw37258step0 = (fun i j => raw37258 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37258step0 raw37258; decide +kernel
      have hl : raw37258step0Labels = raw37258Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37258 raw37258Labels permutation662 permutation3
    mixedMoment B raw37258step0 raw37258step0Labels = mixedMoment B raw37258step1 raw37258step1Labels := by
      have ha : raw37258step1 = -raw37258step0 := by apply Matrix.ext; change ∀ i j, raw37258step1 i j = -(raw37258step0 i j); unfold raw37258step1 raw37258step0; decide +kernel
      have hl : raw37258step1Labels = raw37258step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37258step1 raw37258step1Labels = mixedMoment B raw37258step2 raw37258step2Labels := by
      have ha : raw37258step2 = raw37258step1 := by apply Matrix.ext; unfold raw37258step2 raw37258step1; decide +kernel
      have hl : raw37258step1Labels = labelEmbedding6 ∘ raw37258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37258step1 raw37258step1Labels raw37258step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

theorem canonical37259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37259 raw37259Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw37259 raw37259Labels = mixedMoment B raw37259step0 raw37259step0Labels := by
      have ha : raw37259step0 = (fun i j => raw37259 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37259step0 raw37259; decide +kernel
      have hl : raw37259step0Labels = raw37259Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37259 raw37259Labels permutation152 permutation3
    mixedMoment B raw37259step0 raw37259step0Labels = mixedMoment B raw37259step1 raw37259step1Labels := by
      have ha : raw37259step1 = raw37259step0 := by apply Matrix.ext; unfold raw37259step1 raw37259step0; decide +kernel
      have hl : raw37259step0Labels = labelEmbedding6 ∘ raw37259step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37259step0 raw37259step0Labels raw37259step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5335 node5335Labels := by rfl

theorem canonical37260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37260 raw37260Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw37260 raw37260Labels = mixedMoment B raw37260step0 raw37260step0Labels := by
      have ha : raw37260step0 = (fun i j => raw37260 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37260step0 raw37260; decide +kernel
      have hl : raw37260step0Labels = raw37260Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37260 raw37260Labels permutation176 permutation3
    mixedMoment B raw37260step0 raw37260step0Labels = mixedMoment B raw37260step1 raw37260step1Labels := by
      have ha : raw37260step1 = raw37260step0 := by apply Matrix.ext; unfold raw37260step1 raw37260step0; decide +kernel
      have hl : raw37260step0Labels = labelEmbedding6 ∘ raw37260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37260step0 raw37260step0Labels raw37260step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5335 node5335Labels := by rfl

theorem canonical37261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37261 raw37261Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw37261 raw37261Labels = mixedMoment B raw37261step0 raw37261step0Labels := by
      have ha : raw37261step0 = (fun i j => raw37261 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37261step0 raw37261; decide +kernel
      have hl : raw37261step0Labels = raw37261Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37261 raw37261Labels permutation664 permutation3
    mixedMoment B raw37261step0 raw37261step0Labels = mixedMoment B raw37261step1 raw37261step1Labels := by
      have ha : raw37261step1 = -raw37261step0 := by apply Matrix.ext; change ∀ i j, raw37261step1 i j = -(raw37261step0 i j); unfold raw37261step1 raw37261step0; decide +kernel
      have hl : raw37261step1Labels = raw37261step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37261step1 raw37261step1Labels = mixedMoment B raw37261step2 raw37261step2Labels := by
      have ha : raw37261step2 = raw37261step1 := by apply Matrix.ext; unfold raw37261step2 raw37261step1; decide +kernel
      have hl : raw37261step1Labels = labelEmbedding6 ∘ raw37261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37261step1 raw37261step1Labels raw37261step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4763 node4763Labels := by rfl

theorem canonical37262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37262 raw37262Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw37262 raw37262Labels = mixedMoment B raw37262step0 raw37262step0Labels := by
      have ha : raw37262step0 = (fun i j => raw37262 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37262step0 raw37262; decide +kernel
      have hl : raw37262step0Labels = raw37262Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37262 raw37262Labels permutation662 permutation3
    mixedMoment B raw37262step0 raw37262step0Labels = mixedMoment B raw37262step1 raw37262step1Labels := by
      have ha : raw37262step1 = -raw37262step0 := by apply Matrix.ext; change ∀ i j, raw37262step1 i j = -(raw37262step0 i j); unfold raw37262step1 raw37262step0; decide +kernel
      have hl : raw37262step1Labels = raw37262step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37262step1 raw37262step1Labels = mixedMoment B raw37262step2 raw37262step2Labels := by
      have ha : raw37262step2 = raw37262step1 := by apply Matrix.ext; unfold raw37262step2 raw37262step1; decide +kernel
      have hl : raw37262step1Labels = labelEmbedding6 ∘ raw37262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37262step1 raw37262step1Labels raw37262step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4763 node4763Labels := by rfl

theorem canonical37263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37263 raw37263Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw37263 raw37263Labels = mixedMoment B raw37263step0 raw37263step0Labels := by
      have ha : raw37263step0 = (fun i j => raw37263 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37263step0 raw37263; decide +kernel
      have hl : raw37263step0Labels = raw37263Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37263 raw37263Labels permutation662 permutation3
    mixedMoment B raw37263step0 raw37263step0Labels = mixedMoment B raw37263step1 raw37263step1Labels := by
      have ha : raw37263step1 = -raw37263step0 := by apply Matrix.ext; change ∀ i j, raw37263step1 i j = -(raw37263step0 i j); unfold raw37263step1 raw37263step0; decide +kernel
      have hl : raw37263step1Labels = raw37263step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37263step1 raw37263step1Labels = mixedMoment B raw37263step2 raw37263step2Labels := by
      have ha : raw37263step2 = raw37263step1 := by apply Matrix.ext; unfold raw37263step2 raw37263step1; decide +kernel
      have hl : raw37263step1Labels = labelEmbedding6 ∘ raw37263step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37263step1 raw37263step1Labels raw37263step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

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

theorem singleton4759 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4759 node4759Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1959 node1959Labels + mixedMoment B node2170 node2170Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1686 singletonSmall4759
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4759) = raw1686Labels := by decide +kernel
  rw [hl, canonical1686 B hB] at h
  have hc0 : mixedMoment B raw1686 (Fin.cases (0 : Fin 2) singletonSmall4759) =
      mixedMoment B node1959 node1959Labels := by
    have ha : raw1686 = raw1687 := by apply Matrix.ext; unfold raw1686 raw1687; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4759 = raw1687Labels := by decide +kernel
    rw [ha, hj, canonical1687 B hB]
  have hc1 : mixedMoment B raw1686 (Fin.cases (1 : Fin 2) singletonSmall4759) =
      mixedMoment B node2170 node2170Labels := by
    have ha : raw1686 = raw1688 := by apply Matrix.ext; unfold raw1686 raw1688; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4759 = raw1688Labels := by decide +kernel
    rw [ha, hj, canonical1688 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4763 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4763 node4763Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1963 node1963Labels + mixedMoment B node2174 node2174Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1692 singletonSmall4763
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4763) = raw1692Labels := by decide +kernel
  rw [hl, canonical1692 B hB] at h
  have hc0 : mixedMoment B raw1692 (Fin.cases (0 : Fin 2) singletonSmall4763) =
      mixedMoment B node1963 node1963Labels := by
    have ha : raw1692 = raw1693 := by apply Matrix.ext; unfold raw1692 raw1693; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4763 = raw1693Labels := by decide +kernel
    rw [ha, hj, canonical1693 B hB]
  have hc1 : mixedMoment B raw1692 (Fin.cases (1 : Fin 2) singletonSmall4763) =
      mixedMoment B node2174 node2174Labels := by
    have ha : raw1692 = raw1694 := by apply Matrix.ext; unfold raw1692 raw1694; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4763 = raw1694Labels := by decide +kernel
    rw [ha, hj, canonical1694 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5335 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5335 node5335Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3670 node3670Labels + mixedMoment B node3753 node3753Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2370 singletonSmall5335
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5335) = raw2370Labels := by decide +kernel
  rw [hl, canonical2370 B hB] at h
  have hc0 : mixedMoment B raw2370 (Fin.cases (0 : Fin 2) singletonSmall5335) =
      mixedMoment B node3670 node3670Labels := by
    have ha : raw2370 = raw2371 := by apply Matrix.ext; unfold raw2370 raw2371; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5335 = raw2371Labels := by decide +kernel
    rw [ha, hj, canonical2371 B hB]
  have hc1 : mixedMoment B raw2370 (Fin.cases (1 : Fin 2) singletonSmall5335) =
      mixedMoment B node3753 node3753Labels := by
    have ha : raw2370 = raw2372 := by apply Matrix.ext; unfold raw2370 raw2372; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5335 = raw2372Labels := by decide +kernel
    rw [ha, hj, canonical2372 B hB]
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

theorem zero5497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5497 node5497Labels = 0 := by
  exact mixedMoment_alpha B hF node5497 node5497Labels 0 permutation499
    (by decide +kernel)

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

theorem sound1959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1959 node1959Labels = Sparse.eval nodeValue1959 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1959) = mixedMoment B node1959 node1959Labels := rfl
  simpa [nodeValue1959, Sparse.eval] using hc.symm

theorem sound1963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1963 node1963Labels = Sparse.eval nodeValue1963 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1963) = mixedMoment B node1963 node1963Labels := rfl
  simpa [nodeValue1963, Sparse.eval] using hc.symm

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

theorem sound2170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2170 node2170Labels = Sparse.eval nodeValue2170 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2170) = mixedMoment B node2170 node2170Labels := rfl
  simpa [nodeValue2170, Sparse.eval] using hc.symm

theorem sound2174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2174 node2174Labels = Sparse.eval nodeValue2174 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2174) = mixedMoment B node2174 node2174Labels := rfl
  simpa [nodeValue2174, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3670 node3670Labels = Sparse.eval nodeValue3670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3670) = mixedMoment B node3670 node3670Labels := rfl
  simpa [nodeValue3670, Sparse.eval] using hc.symm

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

theorem sound3753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3753 node3753Labels = Sparse.eval nodeValue3753 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3753) = mixedMoment B node3753 node3753Labels := rfl
  simpa [nodeValue3753, Sparse.eval] using hc.symm

theorem sound3757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3757 node3757Labels = Sparse.eval nodeValue3757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3757) = mixedMoment B node3757 node3757Labels := rfl
  simpa [nodeValue3757, Sparse.eval] using hc.symm

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

theorem sound3837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3837 node3837Labels = Sparse.eval nodeValue3837 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3837) = mixedMoment B node3837 node3837Labels := rfl
  simpa [nodeValue3837, Sparse.eval] using hc.symm

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

theorem sound4759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4759 node4759Labels = Sparse.eval nodeValue4759 (mixedVector B) := by
  have h := singleton4759 B _hB
  rw [sound1959 B _hB _hF, sound2170 B _hB _hF] at h
  norm_num [nodeValue4759, nodeValue1959, nodeValue2170, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4763 node4763Labels = Sparse.eval nodeValue4763 (mixedVector B) := by
  have h := singleton4763 B _hB
  rw [sound1963 B _hB _hF, sound2174 B _hB _hF] at h
  norm_num [nodeValue4763, nodeValue1963, nodeValue2174, Sparse.eval] at h ⊢
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

theorem sound5335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5335 node5335Labels = Sparse.eval nodeValue5335 (mixedVector B) := by
  have h := singleton5335 B _hB
  rw [sound3670 B _hB _hF, sound3753 B _hB _hF] at h
  norm_num [nodeValue5335, nodeValue3670, nodeValue3753, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5351 node5351Labels = Sparse.eval nodeValue5351 (mixedVector B) := by
  have h := singleton5351 B _hB
  rw [sound3689 B _hB _hF, sound3757 B _hB _hF] at h
  norm_num [nodeValue5351, nodeValue3689, nodeValue3757, Sparse.eval] at h ⊢
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

theorem sound5423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5423 node5423Labels = Sparse.eval nodeValue5423 (mixedVector B) := by
  have h := singleton5423 B _hB
  rw [sound3837 B _hB _hF] at h
  norm_num [nodeValue5423, nodeValue3837, Sparse.eval] at h ⊢
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

theorem sound5497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5497 node5497Labels = Sparse.eval nodeValue5497 (mixedVector B) := by
  simpa only [nodeValue5497, Sparse.eval_nil] using zero5497 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources82
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2651 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2651 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2651 + difference 0 1) (sourceB2651 + difference 1 0) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2651 + difference 0 1) (sourceB2651 + difference 1 0) sourceC2651) = raw37251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37251; decide +kernel
    rw [ha]
    exact (canonical37251 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2651 + difference 0 2) (sourceB2651 + difference 2 0) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2651 + difference 0 2) (sourceB2651 + difference 2 0) sourceC2651) = raw37252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37252; decide +kernel
    rw [ha]
    exact (canonical37252 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2651 + difference 0 3) (sourceB2651 + difference 3 0) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2651 + difference 0 3) (sourceB2651 + difference 3 0) sourceC2651) = raw18265 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18265; decide +kernel
    rw [ha]
    exact (canonical18265 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2651 + difference 0 4) (sourceB2651 + difference 4 0) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2651 + difference 0 4) (sourceB2651 + difference 4 0) sourceC2651) = raw37253 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37253; decide +kernel
    rw [ha]
    exact (canonical37253 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2651 + difference 0 5) (sourceB2651 + difference 5 0) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5497) := by
    have ha : (tripleCharges (sourceA2651 + difference 0 5) (sourceB2651 + difference 5 0) sourceC2651) = raw18382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18382; decide +kernel
    rw [ha]
    exact (canonical18382 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2651 + difference 1 0) (sourceB2651 + difference 0 1) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2651 + difference 1 0) (sourceB2651 + difference 0 1) sourceC2651) = raw34080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw34080; decide +kernel
    rw [ha]
    exact (canonical34080 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2651 + difference 1 2) (sourceB2651 + difference 2 1) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2651 + difference 1 2) (sourceB2651 + difference 2 1) sourceC2651) = raw37254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37254; decide +kernel
    rw [ha]
    exact (canonical37254 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2651 + difference 1 3) (sourceB2651 + difference 3 1) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA2651 + difference 1 3) (sourceB2651 + difference 3 1) sourceC2651) = raw18270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18270; decide +kernel
    rw [ha]
    exact (canonical18270 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2651 + difference 1 4) (sourceB2651 + difference 4 1) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA2651 + difference 1 4) (sourceB2651 + difference 4 1) sourceC2651) = raw37255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37255; decide +kernel
    rw [ha]
    exact (canonical37255 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2651 + difference 1 5) (sourceB2651 + difference 5 1) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2651 + difference 1 5) (sourceB2651 + difference 5 1) sourceC2651) = raw18386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18386; decide +kernel
    rw [ha]
    exact (canonical18386 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2651 + difference 2 0) (sourceB2651 + difference 0 2) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2651 + difference 2 0) (sourceB2651 + difference 0 2) sourceC2651) = raw18279 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18279; decide +kernel
    rw [ha]
    exact (canonical18279 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2651 + difference 2 1) (sourceB2651 + difference 1 2) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2651 + difference 2 1) (sourceB2651 + difference 1 2) sourceC2651) = raw18280 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18280; decide +kernel
    rw [ha]
    exact (canonical18280 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2651 + difference 2 3) (sourceB2651 + difference 3 2) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA2651 + difference 2 3) (sourceB2651 + difference 3 2) sourceC2651) = raw18402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18402; decide +kernel
    rw [ha]
    exact (canonical18402 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2651 + difference 2 4) (sourceB2651 + difference 4 2) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA2651 + difference 2 4) (sourceB2651 + difference 4 2) sourceC2651) = raw18282 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18282; decide +kernel
    rw [ha]
    exact (canonical18282 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2651 + difference 2 5) (sourceB2651 + difference 5 2) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2651 + difference 2 5) (sourceB2651 + difference 5 2) sourceC2651) = raw18283 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18283; decide +kernel
    rw [ha]
    exact (canonical18283 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2651 + difference 3 0) (sourceB2651 + difference 0 3) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2651 + difference 3 0) (sourceB2651 + difference 0 3) sourceC2651) = raw34087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw34087; decide +kernel
    rw [ha]
    exact (canonical34087 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2651 + difference 3 1) (sourceB2651 + difference 1 3) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5335) := by
    have ha : (tripleCharges (sourceA2651 + difference 3 1) (sourceB2651 + difference 1 3) sourceC2651) = raw37256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37256; decide +kernel
    rw [ha]
    exact (canonical37256 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2651 + difference 3 2) (sourceB2651 + difference 2 3) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5335) := by
    have ha : (tripleCharges (sourceA2651 + difference 3 2) (sourceB2651 + difference 2 3) sourceC2651) = raw37257 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37257; decide +kernel
    rw [ha]
    exact (canonical37257 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2651 + difference 3 4) (sourceB2651 + difference 4 3) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2651 + difference 3 4) (sourceB2651 + difference 4 3) sourceC2651) = raw37258 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37258; decide +kernel
    rw [ha]
    exact (canonical37258 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2651 + difference 3 5) (sourceB2651 + difference 5 3) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2651 + difference 3 5) (sourceB2651 + difference 5 3) sourceC2651) = raw18395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18395; decide +kernel
    rw [ha]
    exact (canonical18395 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2651 + difference 4 0) (sourceB2651 + difference 0 4) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2651 + difference 4 0) (sourceB2651 + difference 0 4) sourceC2651) = raw34091 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw34091; decide +kernel
    rw [ha]
    exact (canonical34091 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2651 + difference 4 1) (sourceB2651 + difference 1 4) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5335) := by
    have ha : (tripleCharges (sourceA2651 + difference 4 1) (sourceB2651 + difference 1 4) sourceC2651) = raw37259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37259; decide +kernel
    rw [ha]
    exact (canonical37259 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2651 + difference 4 2) (sourceB2651 + difference 2 4) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5335) := by
    have ha : (tripleCharges (sourceA2651 + difference 4 2) (sourceB2651 + difference 2 4) sourceC2651) = raw37260 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37260; decide +kernel
    rw [ha]
    exact (canonical37260 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2651 + difference 4 3) (sourceB2651 + difference 3 4) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2651 + difference 4 3) (sourceB2651 + difference 3 4) sourceC2651) = raw18286 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18286; decide +kernel
    rw [ha]
    exact (canonical18286 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2651 + difference 4 5) (sourceB2651 + difference 5 4) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2651 + difference 4 5) (sourceB2651 + difference 5 4) sourceC2651) = raw18400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18400; decide +kernel
    rw [ha]
    exact (canonical18400 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2651 + difference 5 0) (sourceB2651 + difference 0 5) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4759) := by
    have ha : (tripleCharges (sourceA2651 + difference 5 0) (sourceB2651 + difference 0 5) sourceC2651) = raw34094 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw34094; decide +kernel
    rw [ha]
    exact (canonical34094 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2651 + difference 5 1) (sourceB2651 + difference 1 5) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2651 + difference 5 1) (sourceB2651 + difference 1 5) sourceC2651) = raw37261 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37261; decide +kernel
    rw [ha]
    exact (canonical37261 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2651 + difference 5 2) (sourceB2651 + difference 2 5) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2651 + difference 5 2) (sourceB2651 + difference 2 5) sourceC2651) = raw37262 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37262; decide +kernel
    rw [ha]
    exact (canonical37262 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2651 + difference 5 3) (sourceB2651 + difference 3 5) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2651 + difference 5 3) (sourceB2651 + difference 3 5) sourceC2651) = raw18291 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18291; decide +kernel
    rw [ha]
    exact (canonical18291 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2651 + difference 5 4) (sourceB2651 + difference 4 5) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2651 + difference 5 4) (sourceB2651 + difference 4 5) sourceC2651) = raw37263 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37263; decide +kernel
    rw [ha]
    exact (canonical37263 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2651 sourceB2651 sourceC2651
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2651, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2108 : Integer.Sparse.reindex keyMap MixedData.row2108 = numericRow2108 := by decide +kernel

theorem numericCheck2108 (x : Master → ℝ) : Integer.Sparse.eval numericRow2108 x =
    (12960 : ℝ) * reducedSource2108 x := by
  norm_num [numericRow2108, reducedSource2108, Integer.Sparse.eval, Sparse.eval, nodeValue4759, nodeValue4763, nodeValue4801, nodeValue5335, nodeValue5351, nodeValue5416, nodeValue5423, nodeValue5433, nodeValue5497] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2108 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2108 (mixedVector B) = 0 := by
  have h4759 : mixedVector B (Sum.inr 4759) = Sparse.eval nodeValue4759 (mixedVector B) := by
    change mixedMoment B node4759 node4759Labels = _
    exact sound4759 B hB hF
  have h4763 : mixedVector B (Sum.inr 4763) = Sparse.eval nodeValue4763 (mixedVector B) := by
    change mixedMoment B node4763 node4763Labels = _
    exact sound4763 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h5335 : mixedVector B (Sum.inr 5335) = Sparse.eval nodeValue5335 (mixedVector B) := by
    change mixedMoment B node5335 node5335Labels = _
    exact sound5335 B hB hF
  have h5351 : mixedVector B (Sum.inr 5351) = Sparse.eval nodeValue5351 (mixedVector B) := by
    change mixedMoment B node5351 node5351Labels = _
    exact sound5351 B hB hF
  have h5416 : mixedVector B (Sum.inr 5416) = Sparse.eval nodeValue5416 (mixedVector B) := by
    change mixedMoment B node5416 node5416Labels = _
    exact sound5416_e B hB hF
  have h5423 : mixedVector B (Sum.inr 5423) = Sparse.eval nodeValue5423 (mixedVector B) := by
    change mixedMoment B node5423 node5423Labels = _
    exact sound5423 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5497 : mixedVector B (Sum.inr 5497) = Sparse.eval nodeValue5497 (mixedVector B) := by
    change mixedMoment B node5497 node5497Labels = _
    exact sound5497 B hB hF
  simpa only [sourceForm2651, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4759, h4763, h4801, h5335, h5351, h5416, h5423, h5433, h5497, reducedSource2108] using sourceEq2651 B hB

theorem rowSound2108_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2108 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2108, numericCheck2108, reducedZero2108 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108_e_oai
