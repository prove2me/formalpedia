-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound958_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:04:46.070709+00:00
-- url     : https://prove2.me/submissions/2e17978b-57f2-472a-a586-4f3ee38c7028

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E129
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5450_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5452_e
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13376 raw13376Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw13376 raw13376Labels = mixedMoment B raw13376step0 raw13376step0Labels := by
      have ha : raw13376step0 = (fun i j => raw13376 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13376step0 raw13376; decide +kernel
      have hl : raw13376step0Labels = raw13376Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13376 raw13376Labels permutation176 permutation2
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical13377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13377 raw13377Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw13377 raw13377Labels = mixedMoment B raw13377step0 raw13377step0Labels := by
      have hz : ∀ j, raw13377 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13377step0 = (fun i j => raw13377 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13377step0 raw13377; decide +kernel
      have hl : raw13377step0Labels = raw13377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13377 raw13377Labels permutation434 hz
    _ = mixedMoment B node5452 node5452Labels := by rfl

theorem canonical13378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13378 raw13378Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw13378 raw13378Labels = mixedMoment B raw13378step0 raw13378step0Labels := by
      have hz : ∀ j, raw13378 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13378step0 = (fun i j => raw13378 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13378step0 raw13378; decide +kernel
      have hl : raw13378step0Labels = raw13378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13378 raw13378Labels permutation520 hz
    _ = mixedMoment B node5452 node5452Labels := by rfl

theorem canonical13379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13379 raw13379Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw13379 raw13379Labels = mixedMoment B raw13379step0 raw13379step0Labels := by
      have hz : ∀ j, raw13379 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13379step0 = (fun i j => raw13379 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13379step0 raw13379; decide +kernel
      have hl : raw13379step0Labels = raw13379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13379 raw13379Labels permutation590 hz
    _ = mixedMoment B node5452 node5452Labels := by rfl

theorem canonical13386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13386 raw13386Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw13386 raw13386Labels = mixedMoment B raw13386step0 raw13386step0Labels := by
      have ha : raw13386step0 = (fun i j => raw13386 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13386step0 raw13386; decide +kernel
      have hl : raw13386step0Labels = raw13386Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13386 raw13386Labels permutation161 permutation2
    _ = mixedMoment B node5202 node5202Labels := by rfl

theorem canonical13391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13391 raw13391Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw13391 raw13391Labels = mixedMoment B raw13391step0 raw13391step0Labels := by
      have ha : raw13391step0 = (fun i j => raw13391 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13391step0 raw13391; decide +kernel
      have hl : raw13391step0Labels = raw13391Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13391 raw13391Labels permutation155 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

theorem canonical13396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13396 raw13396Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw13396 raw13396Labels = mixedMoment B raw13396step0 raw13396step0Labels := by
      have ha : raw13396step0 = (fun i j => raw13396 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13396step0 raw13396; decide +kernel
      have hl : raw13396step0Labels = raw13396Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13396 raw13396Labels permutation153 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

theorem canonical13401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13401 raw13401Labels = mixedMoment B node5192 node5192Labels := by
  calc
    _ = mixedMoment B node5192 node5192Labels := by rfl

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

theorem canonical18529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18529 raw18529Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw18529 raw18529Labels = mixedMoment B raw18529step0 raw18529step0Labels := by
      have ha : raw18529step0 = (fun i j => raw18529 (permutation289 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18529step0 raw18529; decide +kernel
      have hl : raw18529step0Labels = raw18529Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18529 raw18529Labels permutation289 permutation5
    mixedMoment B raw18529step0 raw18529step0Labels = mixedMoment B raw18529step1 raw18529step1Labels := by
      have ha : raw18529step1 = -raw18529step0 := by apply Matrix.ext; change ∀ i j, raw18529step1 i j = -(raw18529step0 i j); unfold raw18529step1 raw18529step0; decide +kernel
      have hl : raw18529step1Labels = raw18529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18529step1 raw18529step1Labels = mixedMoment B raw18529step2 raw18529step2Labels := by
      have ha : raw18529step2 = raw18529step1 := by apply Matrix.ext; unfold raw18529step2 raw18529step1; decide +kernel
      have hl : raw18529step1Labels = labelEmbedding8 ∘ raw18529step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18529step1 raw18529step1Labels raw18529step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5162 node5162Labels := by rfl

theorem canonical18530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18530 raw18530Labels = mixedMoment B node5462 node5462Labels := by
  calc
    mixedMoment B raw18530 raw18530Labels = mixedMoment B raw18530step0 raw18530step0Labels := by
      have ha : raw18530step0 = (fun i j => raw18530 (permutation289 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18530step0 raw18530; decide +kernel
      have hl : raw18530step0Labels = raw18530Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18530 raw18530Labels permutation289 permutation5
    mixedMoment B raw18530step0 raw18530step0Labels = mixedMoment B raw18530step1 raw18530step1Labels := by
      have ha : raw18530step1 = -raw18530step0 := by apply Matrix.ext; change ∀ i j, raw18530step1 i j = -(raw18530step0 i j); unfold raw18530step1 raw18530step0; decide +kernel
      have hl : raw18530step1Labels = raw18530step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18530step1 raw18530step1Labels = mixedMoment B raw18530step2 raw18530step2Labels := by
      have ha : raw18530step2 = raw18530step1 := by apply Matrix.ext; unfold raw18530step2 raw18530step1; decide +kernel
      have hl : raw18530step1Labels = labelEmbedding8 ∘ raw18530step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18530step1 raw18530step1Labels raw18530step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5462 node5462Labels := by rfl

theorem canonical18531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18531 raw18531Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18531 raw18531Labels = mixedMoment B raw18531step0 raw18531step0Labels := by
      have hz : ∀ j, raw18531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18531step0 = (fun i j => raw18531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18531step0 raw18531; decide +kernel
      have hl : raw18531step0Labels = raw18531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18531 raw18531Labels permutation434 hz
    mixedMoment B raw18531step0 raw18531step0Labels = mixedMoment B raw18531step1 raw18531step1Labels := by
      have ha : raw18531step1 = (fun i j => raw18531step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18531step1 raw18531step0; decide +kernel
      have hl : raw18531step1Labels = raw18531step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18531step0 raw18531step0Labels permutation65 permutation4
    mixedMoment B raw18531step1 raw18531step1Labels = mixedMoment B raw18531step2 raw18531step2Labels := by
      have ha : raw18531step2 = -raw18531step1 := by apply Matrix.ext; change ∀ i j, raw18531step2 i j = -(raw18531step1 i j); unfold raw18531step2 raw18531step1; decide +kernel
      have hl : raw18531step2Labels = raw18531step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18531step2 raw18531step2Labels = mixedMoment B raw18531step3 raw18531step3Labels := by
      have ha : raw18531step3 = raw18531step2 := by apply Matrix.ext; unfold raw18531step3 raw18531step2; decide +kernel
      have hl : raw18531step2Labels = labelEmbedding7 ∘ raw18531step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18531step2 raw18531step2Labels raw18531step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

theorem canonical18532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18532 raw18532Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18532 raw18532Labels = mixedMoment B raw18532step0 raw18532step0Labels := by
      have hz : ∀ j, raw18532 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18532step0 = (fun i j => raw18532 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18532step0 raw18532; decide +kernel
      have hl : raw18532step0Labels = raw18532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18532 raw18532Labels permutation520 hz
    mixedMoment B raw18532step0 raw18532step0Labels = mixedMoment B raw18532step1 raw18532step1Labels := by
      have ha : raw18532step1 = (fun i j => raw18532step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18532step1 raw18532step0; decide +kernel
      have hl : raw18532step1Labels = raw18532step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18532step0 raw18532step0Labels permutation65 permutation4
    mixedMoment B raw18532step1 raw18532step1Labels = mixedMoment B raw18532step2 raw18532step2Labels := by
      have ha : raw18532step2 = -raw18532step1 := by apply Matrix.ext; change ∀ i j, raw18532step2 i j = -(raw18532step1 i j); unfold raw18532step2 raw18532step1; decide +kernel
      have hl : raw18532step2Labels = raw18532step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18532step2 raw18532step2Labels = mixedMoment B raw18532step3 raw18532step3Labels := by
      have ha : raw18532step3 = raw18532step2 := by apply Matrix.ext; unfold raw18532step3 raw18532step2; decide +kernel
      have hl : raw18532step2Labels = labelEmbedding7 ∘ raw18532step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18532step2 raw18532step2Labels raw18532step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

theorem canonical18533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18533 raw18533Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18533 raw18533Labels = mixedMoment B raw18533step0 raw18533step0Labels := by
      have hz : ∀ j, raw18533 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18533step0 = (fun i j => raw18533 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18533step0 raw18533; decide +kernel
      have hl : raw18533step0Labels = raw18533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18533 raw18533Labels permutation590 hz
    mixedMoment B raw18533step0 raw18533step0Labels = mixedMoment B raw18533step1 raw18533step1Labels := by
      have ha : raw18533step1 = (fun i j => raw18533step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18533step1 raw18533step0; decide +kernel
      have hl : raw18533step1Labels = raw18533step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18533step0 raw18533step0Labels permutation65 permutation4
    mixedMoment B raw18533step1 raw18533step1Labels = mixedMoment B raw18533step2 raw18533step2Labels := by
      have ha : raw18533step2 = -raw18533step1 := by apply Matrix.ext; change ∀ i j, raw18533step2 i j = -(raw18533step1 i j); unfold raw18533step2 raw18533step1; decide +kernel
      have hl : raw18533step2Labels = raw18533step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18533step2 raw18533step2Labels = mixedMoment B raw18533step3 raw18533step3Labels := by
      have ha : raw18533step3 = raw18533step2 := by apply Matrix.ext; unfold raw18533step3 raw18533step2; decide +kernel
      have hl : raw18533step2Labels = labelEmbedding7 ∘ raw18533step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18533step2 raw18533step2Labels raw18533step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

theorem canonical18534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18534 raw18534Labels = mixedMoment B node5283 node5283Labels := by
  calc
    _ = mixedMoment B node5283 node5283Labels := by rfl

theorem canonical18535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18535 raw18535Labels = mixedMoment B node5227 node5227Labels := by
  calc
    mixedMoment B raw18535 raw18535Labels = mixedMoment B raw18535step0 raw18535step0Labels := by
      have ha : raw18535step0 = (fun i j => raw18535 (permutation265 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18535step0 raw18535; decide +kernel
      have hl : raw18535step0Labels = raw18535Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18535 raw18535Labels permutation265 permutation5
    mixedMoment B raw18535step0 raw18535step0Labels = mixedMoment B raw18535step1 raw18535step1Labels := by
      have ha : raw18535step1 = -raw18535step0 := by apply Matrix.ext; change ∀ i j, raw18535step1 i j = -(raw18535step0 i j); unfold raw18535step1 raw18535step0; decide +kernel
      have hl : raw18535step1Labels = raw18535step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18535step1 raw18535step1Labels = mixedMoment B raw18535step2 raw18535step2Labels := by
      have ha : raw18535step2 = raw18535step1 := by apply Matrix.ext; unfold raw18535step2 raw18535step1; decide +kernel
      have hl : raw18535step1Labels = labelEmbedding8 ∘ raw18535step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18535step1 raw18535step1Labels raw18535step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5227 node5227Labels := by rfl

theorem canonical18536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18536 raw18536Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18536 raw18536Labels = mixedMoment B raw18536step0 raw18536step0Labels := by
      have hz : ∀ j, raw18536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18536step0 = (fun i j => raw18536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18536step0 raw18536; decide +kernel
      have hl : raw18536step0Labels = raw18536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18536 raw18536Labels permutation434 hz
    mixedMoment B raw18536step0 raw18536step0Labels = mixedMoment B raw18536step1 raw18536step1Labels := by
      have ha : raw18536step1 = (fun i j => raw18536step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18536step1 raw18536step0; decide +kernel
      have hl : raw18536step1Labels = raw18536step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18536step0 raw18536step0Labels permutation35 permutation2
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical18537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18537 raw18537Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18537 raw18537Labels = mixedMoment B raw18537step0 raw18537step0Labels := by
      have hz : ∀ j, raw18537 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18537step0 = (fun i j => raw18537 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18537step0 raw18537; decide +kernel
      have hl : raw18537step0Labels = raw18537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18537 raw18537Labels permutation520 hz
    mixedMoment B raw18537step0 raw18537step0Labels = mixedMoment B raw18537step1 raw18537step1Labels := by
      have ha : raw18537step1 = (fun i j => raw18537step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18537step1 raw18537step0; decide +kernel
      have hl : raw18537step1Labels = raw18537step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18537step0 raw18537step0Labels permutation35 permutation2
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical18538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18538 raw18538Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18538 raw18538Labels = mixedMoment B raw18538step0 raw18538step0Labels := by
      have hz : ∀ j, raw18538 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18538step0 = (fun i j => raw18538 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18538step0 raw18538; decide +kernel
      have hl : raw18538step0Labels = raw18538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18538 raw18538Labels permutation590 hz
    mixedMoment B raw18538step0 raw18538step0Labels = mixedMoment B raw18538step1 raw18538step1Labels := by
      have ha : raw18538step1 = (fun i j => raw18538step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18538step1 raw18538step0; decide +kernel
      have hl : raw18538step1Labels = raw18538step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18538step0 raw18538step0Labels permutation35 permutation2
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical18539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18539 raw18539Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw18539 raw18539Labels = mixedMoment B raw18539step0 raw18539step0Labels := by
      have ha : raw18539step0 = (fun i j => raw18539 (permutation292 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18539step0 raw18539; decide +kernel
      have hl : raw18539step0Labels = raw18539Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18539 raw18539Labels permutation292 permutation5
    mixedMoment B raw18539step0 raw18539step0Labels = mixedMoment B raw18539step1 raw18539step1Labels := by
      have ha : raw18539step1 = -raw18539step0 := by apply Matrix.ext; change ∀ i j, raw18539step1 i j = -(raw18539step0 i j); unfold raw18539step1 raw18539step0; decide +kernel
      have hl : raw18539step1Labels = raw18539step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18539step1 raw18539step1Labels = mixedMoment B raw18539step2 raw18539step2Labels := by
      have ha : raw18539step2 = raw18539step1 := by apply Matrix.ext; unfold raw18539step2 raw18539step1; decide +kernel
      have hl : raw18539step1Labels = labelEmbedding8 ∘ raw18539step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18539step1 raw18539step1Labels raw18539step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

theorem canonical18540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18540 raw18540Labels = mixedMoment B node5391 node5391Labels := by
  calc
    mixedMoment B raw18540 raw18540Labels = mixedMoment B raw18540step0 raw18540step0Labels := by
      have ha : raw18540step0 = (fun i j => raw18540 (permutation499 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18540step0 raw18540; decide +kernel
      have hl : raw18540step0Labels = raw18540Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18540 raw18540Labels permutation499 permutation5
    mixedMoment B raw18540step0 raw18540step0Labels = mixedMoment B raw18540step1 raw18540step1Labels := by
      have ha : raw18540step1 = raw18540step0 := by apply Matrix.ext; unfold raw18540step1 raw18540step0; decide +kernel
      have hl : raw18540step0Labels = labelEmbedding8 ∘ raw18540step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18540step0 raw18540step0Labels raw18540step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5391 node5391Labels := by rfl

theorem canonical18541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18541 raw18541Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw18541 raw18541Labels = mixedMoment B raw18541step0 raw18541step0Labels := by
      have hz : ∀ j, raw18541 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18541step0 = (fun i j => raw18541 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18541step0 raw18541; decide +kernel
      have hl : raw18541step0Labels = raw18541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18541 raw18541Labels permutation520 hz
    mixedMoment B raw18541step0 raw18541step0Labels = mixedMoment B raw18541step1 raw18541step1Labels := by
      have ha : raw18541step1 = (fun i j => raw18541step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18541step1 raw18541step0; decide +kernel
      have hl : raw18541step1Labels = raw18541step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18541step0 raw18541step0Labels permutation127 permutation3
    mixedMoment B raw18541step1 raw18541step1Labels = mixedMoment B raw18541step2 raw18541step2Labels := by
      have ha : raw18541step2 = -raw18541step1 := by apply Matrix.ext; change ∀ i j, raw18541step2 i j = -(raw18541step1 i j); unfold raw18541step2 raw18541step1; decide +kernel
      have hl : raw18541step2Labels = raw18541step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18541step2 raw18541step2Labels = mixedMoment B raw18541step3 raw18541step3Labels := by
      have ha : raw18541step3 = raw18541step2 := by apply Matrix.ext; unfold raw18541step3 raw18541step2; decide +kernel
      have hl : raw18541step2Labels = labelEmbedding6 ∘ raw18541step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18541step2 raw18541step2Labels raw18541step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical18542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18542 raw18542Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw18542 raw18542Labels = mixedMoment B raw18542step0 raw18542step0Labels := by
      have hz : ∀ j, raw18542 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18542step0 = (fun i j => raw18542 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18542step0 raw18542; decide +kernel
      have hl : raw18542step0Labels = raw18542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18542 raw18542Labels permutation590 hz
    mixedMoment B raw18542step0 raw18542step0Labels = mixedMoment B raw18542step1 raw18542step1Labels := by
      have ha : raw18542step1 = (fun i j => raw18542step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18542step1 raw18542step0; decide +kernel
      have hl : raw18542step1Labels = raw18542step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18542step0 raw18542step0Labels permutation127 permutation3
    mixedMoment B raw18542step1 raw18542step1Labels = mixedMoment B raw18542step2 raw18542step2Labels := by
      have ha : raw18542step2 = -raw18542step1 := by apply Matrix.ext; change ∀ i j, raw18542step2 i j = -(raw18542step1 i j); unfold raw18542step2 raw18542step1; decide +kernel
      have hl : raw18542step2Labels = raw18542step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18542step2 raw18542step2Labels = mixedMoment B raw18542step3 raw18542step3Labels := by
      have ha : raw18542step3 = raw18542step2 := by apply Matrix.ext; unfold raw18542step3 raw18542step2; decide +kernel
      have hl : raw18542step2Labels = labelEmbedding6 ∘ raw18542step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18542step2 raw18542step2Labels raw18542step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical18543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18543 raw18543Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw18543 raw18543Labels = mixedMoment B raw18543step0 raw18543step0Labels := by
      have ha : raw18543step0 = (fun i j => raw18543 (permutation290 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18543step0 raw18543; decide +kernel
      have hl : raw18543step0Labels = raw18543Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18543 raw18543Labels permutation290 permutation5
    mixedMoment B raw18543step0 raw18543step0Labels = mixedMoment B raw18543step1 raw18543step1Labels := by
      have ha : raw18543step1 = -raw18543step0 := by apply Matrix.ext; change ∀ i j, raw18543step1 i j = -(raw18543step0 i j); unfold raw18543step1 raw18543step0; decide +kernel
      have hl : raw18543step1Labels = raw18543step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18543step1 raw18543step1Labels = mixedMoment B raw18543step2 raw18543step2Labels := by
      have ha : raw18543step2 = raw18543step1 := by apply Matrix.ext; unfold raw18543step2 raw18543step1; decide +kernel
      have hl : raw18543step1Labels = labelEmbedding8 ∘ raw18543step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18543step1 raw18543step1Labels raw18543step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

theorem canonical18544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18544 raw18544Labels = mixedMoment B node5391 node5391Labels := by
  calc
    mixedMoment B raw18544 raw18544Labels = mixedMoment B raw18544step0 raw18544step0Labels := by
      have ha : raw18544step0 = (fun i j => raw18544 (permutation563 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18544step0 raw18544; decide +kernel
      have hl : raw18544step0Labels = raw18544Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18544 raw18544Labels permutation563 permutation5
    mixedMoment B raw18544step0 raw18544step0Labels = mixedMoment B raw18544step1 raw18544step1Labels := by
      have ha : raw18544step1 = raw18544step0 := by apply Matrix.ext; unfold raw18544step1 raw18544step0; decide +kernel
      have hl : raw18544step0Labels = labelEmbedding8 ∘ raw18544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18544step0 raw18544step0Labels raw18544step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5391 node5391Labels := by rfl

theorem canonical18545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18545 raw18545Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw18545 raw18545Labels = mixedMoment B raw18545step0 raw18545step0Labels := by
      have hz : ∀ j, raw18545 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18545step0 = (fun i j => raw18545 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18545step0 raw18545; decide +kernel
      have hl : raw18545step0Labels = raw18545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18545 raw18545Labels permutation434 hz
    mixedMoment B raw18545step0 raw18545step0Labels = mixedMoment B raw18545step1 raw18545step1Labels := by
      have ha : raw18545step1 = (fun i j => raw18545step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18545step1 raw18545step0; decide +kernel
      have hl : raw18545step1Labels = raw18545step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18545step0 raw18545step0Labels permutation127 permutation3
    mixedMoment B raw18545step1 raw18545step1Labels = mixedMoment B raw18545step2 raw18545step2Labels := by
      have ha : raw18545step2 = -raw18545step1 := by apply Matrix.ext; change ∀ i j, raw18545step2 i j = -(raw18545step1 i j); unfold raw18545step2 raw18545step1; decide +kernel
      have hl : raw18545step2Labels = raw18545step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18545step2 raw18545step2Labels = mixedMoment B raw18545step3 raw18545step3Labels := by
      have ha : raw18545step3 = raw18545step2 := by apply Matrix.ext; unfold raw18545step3 raw18545step2; decide +kernel
      have hl : raw18545step2Labels = labelEmbedding6 ∘ raw18545step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18545step2 raw18545step2Labels raw18545step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical18546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18546 raw18546Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw18546 raw18546Labels = mixedMoment B raw18546step0 raw18546step0Labels := by
      have hz : ∀ j, raw18546 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18546step0 = (fun i j => raw18546 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18546step0 raw18546; decide +kernel
      have hl : raw18546step0Labels = raw18546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18546 raw18546Labels permutation590 hz
    mixedMoment B raw18546step0 raw18546step0Labels = mixedMoment B raw18546step1 raw18546step1Labels := by
      have ha : raw18546step1 = (fun i j => raw18546step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18546step1 raw18546step0; decide +kernel
      have hl : raw18546step1Labels = raw18546step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18546step0 raw18546step0Labels permutation151 permutation3
    mixedMoment B raw18546step1 raw18546step1Labels = mixedMoment B raw18546step2 raw18546step2Labels := by
      have ha : raw18546step2 = -raw18546step1 := by apply Matrix.ext; change ∀ i j, raw18546step2 i j = -(raw18546step1 i j); unfold raw18546step2 raw18546step1; decide +kernel
      have hl : raw18546step2Labels = raw18546step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18546step2 raw18546step2Labels = mixedMoment B raw18546step3 raw18546step3Labels := by
      have ha : raw18546step3 = raw18546step2 := by apply Matrix.ext; unfold raw18546step3 raw18546step2; decide +kernel
      have hl : raw18546step2Labels = labelEmbedding6 ∘ raw18546step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18546step2 raw18546step2Labels raw18546step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical18547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18547 raw18547Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw18547 raw18547Labels = mixedMoment B raw18547step0 raw18547step0Labels := by
      have ha : raw18547step0 = (fun i j => raw18547 (permutation289 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18547step0 raw18547; decide +kernel
      have hl : raw18547step0Labels = raw18547Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18547 raw18547Labels permutation289 permutation5
    mixedMoment B raw18547step0 raw18547step0Labels = mixedMoment B raw18547step1 raw18547step1Labels := by
      have ha : raw18547step1 = -raw18547step0 := by apply Matrix.ext; change ∀ i j, raw18547step1 i j = -(raw18547step0 i j); unfold raw18547step1 raw18547step0; decide +kernel
      have hl : raw18547step1Labels = raw18547step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18547step1 raw18547step1Labels = mixedMoment B raw18547step2 raw18547step2Labels := by
      have ha : raw18547step2 = raw18547step1 := by apply Matrix.ext; unfold raw18547step2 raw18547step1; decide +kernel
      have hl : raw18547step1Labels = labelEmbedding8 ∘ raw18547step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18547step1 raw18547step1Labels raw18547step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

theorem canonical18548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18548 raw18548Labels = mixedMoment B node5391 node5391Labels := by
  calc
    mixedMoment B raw18548 raw18548Labels = mixedMoment B raw18548step0 raw18548step0Labels := by
      have ha : raw18548step0 = (fun i j => raw18548 (permutation659 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18548step0 raw18548; decide +kernel
      have hl : raw18548step0Labels = raw18548Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18548 raw18548Labels permutation659 permutation5
    mixedMoment B raw18548step0 raw18548step0Labels = mixedMoment B raw18548step1 raw18548step1Labels := by
      have ha : raw18548step1 = raw18548step0 := by apply Matrix.ext; unfold raw18548step1 raw18548step0; decide +kernel
      have hl : raw18548step0Labels = labelEmbedding8 ∘ raw18548step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18548step0 raw18548step0Labels raw18548step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5391 node5391Labels := by rfl

theorem canonical18549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18549 raw18549Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw18549 raw18549Labels = mixedMoment B raw18549step0 raw18549step0Labels := by
      have hz : ∀ j, raw18549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18549step0 = (fun i j => raw18549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18549step0 raw18549; decide +kernel
      have hl : raw18549step0Labels = raw18549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18549 raw18549Labels permutation434 hz
    mixedMoment B raw18549step0 raw18549step0Labels = mixedMoment B raw18549step1 raw18549step1Labels := by
      have ha : raw18549step1 = (fun i j => raw18549step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18549step1 raw18549step0; decide +kernel
      have hl : raw18549step1Labels = raw18549step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18549step0 raw18549step0Labels permutation151 permutation3
    mixedMoment B raw18549step1 raw18549step1Labels = mixedMoment B raw18549step2 raw18549step2Labels := by
      have ha : raw18549step2 = -raw18549step1 := by apply Matrix.ext; change ∀ i j, raw18549step2 i j = -(raw18549step1 i j); unfold raw18549step2 raw18549step1; decide +kernel
      have hl : raw18549step2Labels = raw18549step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18549step2 raw18549step2Labels = mixedMoment B raw18549step3 raw18549step3Labels := by
      have ha : raw18549step3 = raw18549step2 := by apply Matrix.ext; unfold raw18549step3 raw18549step2; decide +kernel
      have hl : raw18549step2Labels = labelEmbedding6 ∘ raw18549step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18549step2 raw18549step2Labels raw18549step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical18550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18550 raw18550Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw18550 raw18550Labels = mixedMoment B raw18550step0 raw18550step0Labels := by
      have hz : ∀ j, raw18550 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18550step0 = (fun i j => raw18550 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18550step0 raw18550; decide +kernel
      have hl : raw18550step0Labels = raw18550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18550 raw18550Labels permutation520 hz
    mixedMoment B raw18550step0 raw18550step0Labels = mixedMoment B raw18550step1 raw18550step1Labels := by
      have ha : raw18550step1 = (fun i j => raw18550step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18550step1 raw18550step0; decide +kernel
      have hl : raw18550step1Labels = raw18550step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18550step0 raw18550step0Labels permutation151 permutation3
    mixedMoment B raw18550step1 raw18550step1Labels = mixedMoment B raw18550step2 raw18550step2Labels := by
      have ha : raw18550step2 = -raw18550step1 := by apply Matrix.ext; change ∀ i j, raw18550step2 i j = -(raw18550step1 i j); unfold raw18550step2 raw18550step1; decide +kernel
      have hl : raw18550step2Labels = raw18550step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18550step2 raw18550step2Labels = mixedMoment B raw18550step3 raw18550step3Labels := by
      have ha : raw18550step3 = raw18550step2 := by apply Matrix.ext; unfold raw18550step3 raw18550step2; decide +kernel
      have hl : raw18550step2Labels = labelEmbedding6 ∘ raw18550step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18550step2 raw18550step2Labels raw18550step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

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

theorem canonical2220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2220 raw2220Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw2220 raw2220Labels = mixedMoment B raw2220step0 raw2220step0Labels := by
      have ha : raw2220step0 = (fun i j => raw2220 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2220step0 raw2220; decide +kernel
      have hl : raw2220step0Labels = raw2220Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2220 raw2220Labels permutation152 permutation5
    mixedMoment B raw2220step0 raw2220step0Labels = mixedMoment B raw2220step1 raw2220step1Labels := by
      have ha : raw2220step1 = raw2220step0 := by apply Matrix.ext; unfold raw2220step1 raw2220step0; decide +kernel
      have hl : raw2220step0Labels = labelEmbedding8 ∘ raw2220step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2220step0 raw2220step0Labels raw2220step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5192 node5192Labels := by rfl

theorem canonical2221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2221 raw2221Labels = mixedMoment B node2853 node2853Labels := by
  calc
    mixedMoment B raw2221 raw2221Labels = mixedMoment B raw2221step0 raw2221step0Labels := by
      have ha : raw2221step0 = (fun i j => raw2221 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2221step0 raw2221; decide +kernel
      have hl : raw2221step0Labels = raw2221Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2221 raw2221Labels permutation152 permutation4
    _ = mixedMoment B node2853 node2853Labels := by rfl

theorem canonical2222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2222 raw2222Labels = mixedMoment B node3620 node3620Labels := by
  calc
    mixedMoment B raw2222 raw2222Labels = mixedMoment B raw2222step0 raw2222step0Labels := by
      have ha : raw2222step0 = (fun i j => raw2222 (permutation216 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2222step0 raw2222; decide +kernel
      have hl : raw2222step0Labels = raw2222Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2222 raw2222Labels permutation216 permutation3
    mixedMoment B raw2222step0 raw2222step0Labels = mixedMoment B raw2222step1 raw2222step1Labels := by
      have ha : raw2222step1 = -raw2222step0 := by apply Matrix.ext; change ∀ i j, raw2222step1 i j = -(raw2222step0 i j); unfold raw2222step1 raw2222step0; decide +kernel
      have hl : raw2222step1Labels = raw2222step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2222step1 raw2222step1Labels = mixedMoment B raw2222step2 raw2222step2Labels := by
      have ha : raw2222step2 = raw2222step1 := by apply Matrix.ext; unfold raw2222step2 raw2222step1; decide +kernel
      have hl : raw2222step1Labels = labelEmbedding1 ∘ raw2222step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2222step1 raw2222step1Labels raw2222step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3620 node3620Labels := by rfl

theorem canonical2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2226 raw2226Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw2226 raw2226Labels = mixedMoment B raw2226step0 raw2226step0Labels := by
      have ha : raw2226step0 = (fun i j => raw2226 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2226step0 raw2226; decide +kernel
      have hl : raw2226step0Labels = raw2226Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2226 raw2226Labels permutation152 permutation5
    mixedMoment B raw2226step0 raw2226step0Labels = mixedMoment B raw2226step1 raw2226step1Labels := by
      have ha : raw2226step1 = raw2226step0 := by apply Matrix.ext; unfold raw2226step1 raw2226step0; decide +kernel
      have hl : raw2226step0Labels = labelEmbedding8 ∘ raw2226step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2226step0 raw2226step0Labels raw2226step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

theorem canonical2227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2227 raw2227Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw2227 raw2227Labels = mixedMoment B raw2227step0 raw2227step0Labels := by
      have ha : raw2227step0 = (fun i j => raw2227 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2227step0 raw2227; decide +kernel
      have hl : raw2227step0Labels = raw2227Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2227 raw2227Labels permutation170 permutation4
    _ = mixedMoment B node2880 node2880Labels := by rfl

theorem canonical2228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2228 raw2228Labels = mixedMoment B node3617 node3617Labels := by
  calc
    mixedMoment B raw2228 raw2228Labels = mixedMoment B raw2228step0 raw2228step0Labels := by
      have ha : raw2228step0 = (fun i j => raw2228 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2228step0 raw2228; decide +kernel
      have hl : raw2228step0Labels = raw2228Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2228 raw2228Labels permutation184 permutation3
    mixedMoment B raw2228step0 raw2228step0Labels = mixedMoment B raw2228step1 raw2228step1Labels := by
      have ha : raw2228step1 = -raw2228step0 := by apply Matrix.ext; change ∀ i j, raw2228step1 i j = -(raw2228step0 i j); unfold raw2228step1 raw2228step0; decide +kernel
      have hl : raw2228step1Labels = raw2228step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2228step1 raw2228step1Labels = mixedMoment B raw2228step2 raw2228step2Labels := by
      have ha : raw2228step2 = raw2228step1 := by apply Matrix.ext; unfold raw2228step2 raw2228step1; decide +kernel
      have hl : raw2228step1Labels = labelEmbedding1 ∘ raw2228step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2228step1 raw2228step1Labels raw2228step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3617 node3617Labels := by rfl

theorem canonical2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2247 raw2247Labels = mixedMoment B node5227 node5227Labels := by
  calc
    mixedMoment B raw2247 raw2247Labels = mixedMoment B raw2247step0 raw2247step0Labels := by
      have ha : raw2247step0 = (fun i j => raw2247 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2247step0 raw2247; decide +kernel
      have hl : raw2247step0Labels = raw2247Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2247 raw2247Labels permutation152 permutation4
    mixedMoment B raw2247step0 raw2247step0Labels = mixedMoment B raw2247step1 raw2247step1Labels := by
      have ha : raw2247step1 = raw2247step0 := by apply Matrix.ext; unfold raw2247step1 raw2247step0; decide +kernel
      have hl : raw2247step0Labels = labelEmbedding7 ∘ raw2247step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2247step0 raw2247step0Labels raw2247step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5227 node5227Labels := by rfl

theorem canonical2248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2248 raw2248Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw2248 raw2248Labels = mixedMoment B raw2248step0 raw2248step0Labels := by
      have ha : raw2248step0 = (fun i j => raw2248 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2248step0 raw2248; decide +kernel
      have hl : raw2248step0Labels = raw2248Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2248 raw2248Labels permutation152 permutation4
    _ = mixedMoment B node2671 node2671Labels := by rfl

theorem canonical2249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2249 raw2249Labels = mixedMoment B node3390 node3390Labels := by
  calc
    mixedMoment B raw2249 raw2249Labels = mixedMoment B raw2249step0 raw2249step0Labels := by
      have ha : raw2249step0 = (fun i j => raw2249 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2249step0 raw2249; decide +kernel
      have hl : raw2249step0Labels = raw2249Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2249 raw2249Labels permutation152 permutation6
    mixedMoment B raw2249step0 raw2249step0Labels = mixedMoment B raw2249step1 raw2249step1Labels := by
      have ha : raw2249step1 = -raw2249step0 := by apply Matrix.ext; change ∀ i j, raw2249step1 i j = -(raw2249step0 i j); unfold raw2249step1 raw2249step0; decide +kernel
      have hl : raw2249step1Labels = raw2249step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2249step1 raw2249step1Labels = mixedMoment B raw2249step2 raw2249step2Labels := by
      have ha : raw2249step2 = raw2249step1 := by apply Matrix.ext; unfold raw2249step2 raw2249step1; decide +kernel
      have hl : raw2249step1Labels = labelEmbedding1 ∘ raw2249step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2249step1 raw2249step1Labels raw2249step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3390 node3390Labels := by rfl

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

theorem canonical2457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2457 raw2457Labels = mixedMoment B node5391 node5391Labels := by
  calc
    mixedMoment B raw2457 raw2457Labels = mixedMoment B raw2457step0 raw2457step0Labels := by
      have ha : raw2457step0 = (fun i j => raw2457 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2457step0 raw2457; decide +kernel
      have hl : raw2457step0Labels = raw2457Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2457 raw2457Labels permutation152 permutation4
    mixedMoment B raw2457step0 raw2457step0Labels = mixedMoment B raw2457step1 raw2457step1Labels := by
      have ha : raw2457step1 = raw2457step0 := by apply Matrix.ext; unfold raw2457step1 raw2457step0; decide +kernel
      have hl : raw2457step0Labels = labelEmbedding7 ∘ raw2457step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2457step0 raw2457step0Labels raw2457step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5391 node5391Labels := by rfl

theorem canonical2458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2458 raw2458Labels = mixedMoment B node3776 node3776Labels := by
  calc
    mixedMoment B raw2458 raw2458Labels = mixedMoment B raw2458step0 raw2458step0Labels := by
      have ha : raw2458step0 = (fun i j => raw2458 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2458step0 raw2458; decide +kernel
      have hl : raw2458step0Labels = raw2458Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2458 raw2458Labels permutation152 permutation4
    _ = mixedMoment B node3776 node3776Labels := by rfl

theorem canonical2459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2459 raw2459Labels = mixedMoment B node3778 node3778Labels := by
  calc
    mixedMoment B raw2459 raw2459Labels = mixedMoment B raw2459step0 raw2459step0Labels := by
      have ha : raw2459step0 = (fun i j => raw2459 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2459step0 raw2459; decide +kernel
      have hl : raw2459step0Labels = raw2459Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2459 raw2459Labels permutation155 permutation6
    mixedMoment B raw2459step0 raw2459step0Labels = mixedMoment B raw2459step1 raw2459step1Labels := by
      have ha : raw2459step1 = -raw2459step0 := by apply Matrix.ext; change ∀ i j, raw2459step1 i j = -(raw2459step0 i j); unfold raw2459step1 raw2459step0; decide +kernel
      have hl : raw2459step1Labels = raw2459step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2459step1 raw2459step1Labels = mixedMoment B raw2459step2 raw2459step2Labels := by
      have ha : raw2459step2 = raw2459step1 := by apply Matrix.ext; unfold raw2459step2 raw2459step1; decide +kernel
      have hl : raw2459step1Labels = labelEmbedding1 ∘ raw2459step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2459step1 raw2459step1Labels raw2459step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3778 node3778Labels := by rfl

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

theorem singleton5192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5192 node5192Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2853 node2853Labels + mixedMoment B node3620 node3620Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2220 singletonSmall5192
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5192) = raw2220Labels := by decide +kernel
  rw [hl, canonical2220 B hB] at h
  have hc0 : mixedMoment B raw2220 (Fin.cases (0 : Fin 2) singletonSmall5192) =
      mixedMoment B node2853 node2853Labels := by
    have ha : raw2220 = raw2221 := by apply Matrix.ext; unfold raw2220 raw2221; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5192 = raw2221Labels := by decide +kernel
    rw [ha, hj, canonical2221 B hB]
  have hc1 : mixedMoment B raw2220 (Fin.cases (1 : Fin 2) singletonSmall5192) =
      mixedMoment B node3620 node3620Labels := by
    have ha : raw2220 = raw2222 := by apply Matrix.ext; unfold raw2220 raw2222; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5192 = raw2222Labels := by decide +kernel
    rw [ha, hj, canonical2222 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5202 node5202Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2880 node2880Labels + mixedMoment B node3617 node3617Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2226 singletonSmall5202
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5202) = raw2226Labels := by decide +kernel
  rw [hl, canonical2226 B hB] at h
  have hc0 : mixedMoment B raw2226 (Fin.cases (0 : Fin 2) singletonSmall5202) =
      mixedMoment B node2880 node2880Labels := by
    have ha : raw2226 = raw2227 := by apply Matrix.ext; unfold raw2226 raw2227; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5202 = raw2227Labels := by decide +kernel
    rw [ha, hj, canonical2227 B hB]
  have hc1 : mixedMoment B raw2226 (Fin.cases (1 : Fin 2) singletonSmall5202) =
      mixedMoment B node3617 node3617Labels := by
    have ha : raw2226 = raw2228 := by apply Matrix.ext; unfold raw2226 raw2228; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5202 = raw2228Labels := by decide +kernel
    rw [ha, hj, canonical2228 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5227 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5227 node5227Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2671 node2671Labels + mixedMoment B node3390 node3390Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2247 singletonSmall5227
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5227) = raw2247Labels := by decide +kernel
  rw [hl, canonical2247 B hB] at h
  have hc0 : mixedMoment B raw2247 (Fin.cases (0 : Fin 2) singletonSmall5227) =
      mixedMoment B node2671 node2671Labels := by
    have ha : raw2247 = raw2248 := by apply Matrix.ext; unfold raw2247 raw2248; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5227 = raw2248Labels := by decide +kernel
    rw [ha, hj, canonical2248 B hB]
  have hc1 : mixedMoment B raw2247 (Fin.cases (1 : Fin 2) singletonSmall5227) =
      mixedMoment B node3390 node3390Labels := by
    have ha : raw2247 = raw2249 := by apply Matrix.ext; unfold raw2247 raw2249; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5227 = raw2249Labels := by decide +kernel
    rw [ha, hj, canonical2249 B hB]
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

theorem singleton5391 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5391 node5391Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3776 node3776Labels + mixedMoment B node3778 node3778Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2457 singletonSmall5391
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5391) = raw2457Labels := by decide +kernel
  rw [hl, canonical2457 B hB] at h
  have hc0 : mixedMoment B raw2457 (Fin.cases (0 : Fin 2) singletonSmall5391) =
      mixedMoment B node3776 node3776Labels := by
    have ha : raw2457 = raw2458 := by apply Matrix.ext; unfold raw2457 raw2458; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5391 = raw2458Labels := by decide +kernel
    rw [ha, hj, canonical2458 B hB]
  have hc1 : mixedMoment B raw2457 (Fin.cases (1 : Fin 2) singletonSmall5391) =
      mixedMoment B node3778 node3778Labels := by
    have ha : raw2457 = raw2459 := by apply Matrix.ext; unfold raw2457 raw2459; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5391 = raw2459Labels := by decide +kernel
    rw [ha, hj, canonical2459 B hB]
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

theorem zero5462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5462 node5462Labels = 0 := by
  exact mixedMoment_alpha B hF node5462 node5462Labels 2 permutation152
    (by decide +kernel)

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

theorem sound2671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2671 node2671Labels = Sparse.eval nodeValue2671 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2671) = mixedMoment B node2671 node2671Labels := rfl
  simpa [nodeValue2671, Sparse.eval] using hc.symm

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

theorem sound2853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2853 node2853Labels = Sparse.eval nodeValue2853 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2853) = mixedMoment B node2853 node2853Labels := rfl
  simpa [nodeValue2853, Sparse.eval] using hc.symm

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

theorem sound2880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2880 node2880Labels = Sparse.eval nodeValue2880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2880) = mixedMoment B node2880 node2880Labels := rfl
  simpa [nodeValue2880, Sparse.eval] using hc.symm

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

theorem sound3390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3390 node3390Labels = Sparse.eval nodeValue3390 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3390) = mixedMoment B node3390 node3390Labels := rfl
  simpa [nodeValue3390, Sparse.eval] using hc.symm

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

theorem sound3617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3617 node3617Labels = Sparse.eval nodeValue3617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3617) = mixedMoment B node3617 node3617Labels := rfl
  simpa [nodeValue3617, Sparse.eval] using hc.symm

theorem sound3620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3620 node3620Labels = Sparse.eval nodeValue3620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3620) = mixedMoment B node3620 node3620Labels := rfl
  simpa [nodeValue3620, Sparse.eval] using hc.symm

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

theorem sound3776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3776 node3776Labels = Sparse.eval nodeValue3776 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3776) = mixedMoment B node3776 node3776Labels := rfl
  simpa [nodeValue3776, Sparse.eval] using hc.symm

theorem sound3778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3778 node3778Labels = Sparse.eval nodeValue3778 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3778) = mixedMoment B node3778 node3778Labels := rfl
  simpa [nodeValue3778, Sparse.eval] using hc.symm

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

theorem sound4025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4025 node4025Labels = Sparse.eval nodeValue4025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4025) = mixedMoment B node4025 node4025Labels := rfl
  simpa [nodeValue4025, Sparse.eval] using hc.symm

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

theorem sound5162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5162 node5162Labels = Sparse.eval nodeValue5162 (mixedVector B) := by
  have h := singleton5162 B _hB
  rw [sound2589 B _hB _hF, sound3563 B _hB _hF] at h
  norm_num [nodeValue5162, nodeValue2589, nodeValue3563, Sparse.eval] at h ⊢
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

theorem sound5192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5192 node5192Labels = Sparse.eval nodeValue5192 (mixedVector B) := by
  have h := singleton5192 B _hB
  rw [sound2853 B _hB _hF, sound3620 B _hB _hF] at h
  norm_num [nodeValue5192, nodeValue2853, nodeValue3620, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5202 node5202Labels = Sparse.eval nodeValue5202 (mixedVector B) := by
  have h := singleton5202 B _hB
  rw [sound2880 B _hB _hF, sound3617 B _hB _hF] at h
  norm_num [nodeValue5202, nodeValue2880, nodeValue3617, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5227 node5227Labels = Sparse.eval nodeValue5227 (mixedVector B) := by
  have h := singleton5227 B _hB
  rw [sound2671 B _hB _hF, sound3390 B _hB _hF] at h
  norm_num [nodeValue5227, nodeValue2671, nodeValue3390, Sparse.eval] at h ⊢
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

theorem zero5283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5283 node5283Labels = 0 := by
  exact mixedMoment_alpha B hF node5283 node5283Labels 1 permutation152
    (by decide +kernel)

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

theorem sound5283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5283 node5283Labels = Sparse.eval nodeValue5283 (mixedVector B) := by
  simpa only [nodeValue5283, Sparse.eval_nil] using zero5283 B _hB _hF

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

theorem sound5391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5391 node5391Labels = Sparse.eval nodeValue5391 (mixedVector B) := by
  have h := singleton5391 B _hB
  rw [sound3776 B _hB _hF, sound3778 B _hB _hF] at h
  norm_num [nodeValue5391, nodeValue3776, nodeValue3778, Sparse.eval] at h ⊢
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

theorem sound5447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5447 node5447Labels = Sparse.eval nodeValue5447 (mixedVector B) := by
  have h := singleton5447 B _hB
  rw [sound3909 B _hB _hF, sound4025 B _hB _hF] at h
  norm_num [nodeValue5447, nodeValue3909, nodeValue4025, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5462 node5462Labels = Sparse.eval nodeValue5462 (mixedVector B) := by
  simpa only [nodeValue5462, Sparse.eval_nil] using zero5462 B _hB _hF

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

theorem sourceEq1105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1105 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1105 + difference 0 1) (sourceB1105 + difference 1 0) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA1105 + difference 0 1) (sourceB1105 + difference 1 0) sourceC1105) = raw18529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18529; decide +kernel
    rw [ha]
    exact (canonical18529 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1105 + difference 0 2) (sourceB1105 + difference 2 0) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5462) := by
    have ha : (tripleCharges (sourceA1105 + difference 0 2) (sourceB1105 + difference 2 0) sourceC1105) = raw18530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18530; decide +kernel
    rw [ha]
    exact (canonical18530 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1105 + difference 0 3) (sourceB1105 + difference 3 0) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1105 + difference 0 3) (sourceB1105 + difference 3 0) sourceC1105) = raw18531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18531; decide +kernel
    rw [ha]
    exact (canonical18531 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1105 + difference 0 4) (sourceB1105 + difference 4 0) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1105 + difference 0 4) (sourceB1105 + difference 4 0) sourceC1105) = raw18532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18532; decide +kernel
    rw [ha]
    exact (canonical18532 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1105 + difference 0 5) (sourceB1105 + difference 5 0) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1105 + difference 0 5) (sourceB1105 + difference 5 0) sourceC1105) = raw18533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18533; decide +kernel
    rw [ha]
    exact (canonical18533 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1105 + difference 1 0) (sourceB1105 + difference 0 1) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5283) := by
    have ha : (tripleCharges (sourceA1105 + difference 1 0) (sourceB1105 + difference 0 1) sourceC1105) = raw18534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18534; decide +kernel
    rw [ha]
    exact (canonical18534 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1105 + difference 1 2) (sourceB1105 + difference 2 1) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA1105 + difference 1 2) (sourceB1105 + difference 2 1) sourceC1105) = raw13376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw13376; decide +kernel
    rw [ha]
    exact (canonical13376 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1105 + difference 1 3) (sourceB1105 + difference 3 1) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA1105 + difference 1 3) (sourceB1105 + difference 3 1) sourceC1105) = raw13377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw13377; decide +kernel
    rw [ha]
    exact (canonical13377 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1105 + difference 1 4) (sourceB1105 + difference 4 1) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA1105 + difference 1 4) (sourceB1105 + difference 4 1) sourceC1105) = raw13378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw13378; decide +kernel
    rw [ha]
    exact (canonical13378 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1105 + difference 1 5) (sourceB1105 + difference 5 1) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA1105 + difference 1 5) (sourceB1105 + difference 5 1) sourceC1105) = raw13379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw13379; decide +kernel
    rw [ha]
    exact (canonical13379 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1105 + difference 2 0) (sourceB1105 + difference 0 2) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA1105 + difference 2 0) (sourceB1105 + difference 0 2) sourceC1105) = raw13386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw13386; decide +kernel
    rw [ha]
    exact (canonical13386 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1105 + difference 2 1) (sourceB1105 + difference 1 2) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5227) := by
    have ha : (tripleCharges (sourceA1105 + difference 2 1) (sourceB1105 + difference 1 2) sourceC1105) = raw18535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18535; decide +kernel
    rw [ha]
    exact (canonical18535 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1105 + difference 2 3) (sourceB1105 + difference 3 2) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1105 + difference 2 3) (sourceB1105 + difference 3 2) sourceC1105) = raw18536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18536; decide +kernel
    rw [ha]
    exact (canonical18536 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1105 + difference 2 4) (sourceB1105 + difference 4 2) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1105 + difference 2 4) (sourceB1105 + difference 4 2) sourceC1105) = raw18537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18537; decide +kernel
    rw [ha]
    exact (canonical18537 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1105 + difference 2 5) (sourceB1105 + difference 5 2) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1105 + difference 2 5) (sourceB1105 + difference 5 2) sourceC1105) = raw18538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18538; decide +kernel
    rw [ha]
    exact (canonical18538 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1105 + difference 3 0) (sourceB1105 + difference 0 3) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA1105 + difference 3 0) (sourceB1105 + difference 0 3) sourceC1105) = raw13391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw13391; decide +kernel
    rw [ha]
    exact (canonical13391 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1105 + difference 3 1) (sourceB1105 + difference 1 3) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA1105 + difference 3 1) (sourceB1105 + difference 1 3) sourceC1105) = raw18539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18539; decide +kernel
    rw [ha]
    exact (canonical18539 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1105 + difference 3 2) (sourceB1105 + difference 2 3) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5391) := by
    have ha : (tripleCharges (sourceA1105 + difference 3 2) (sourceB1105 + difference 2 3) sourceC1105) = raw18540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18540; decide +kernel
    rw [ha]
    exact (canonical18540 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1105 + difference 3 4) (sourceB1105 + difference 4 3) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1105 + difference 3 4) (sourceB1105 + difference 4 3) sourceC1105) = raw18541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18541; decide +kernel
    rw [ha]
    exact (canonical18541 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1105 + difference 3 5) (sourceB1105 + difference 5 3) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1105 + difference 3 5) (sourceB1105 + difference 5 3) sourceC1105) = raw18542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18542; decide +kernel
    rw [ha]
    exact (canonical18542 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1105 + difference 4 0) (sourceB1105 + difference 0 4) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA1105 + difference 4 0) (sourceB1105 + difference 0 4) sourceC1105) = raw13396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw13396; decide +kernel
    rw [ha]
    exact (canonical13396 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1105 + difference 4 1) (sourceB1105 + difference 1 4) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA1105 + difference 4 1) (sourceB1105 + difference 1 4) sourceC1105) = raw18543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18543; decide +kernel
    rw [ha]
    exact (canonical18543 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1105 + difference 4 2) (sourceB1105 + difference 2 4) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5391) := by
    have ha : (tripleCharges (sourceA1105 + difference 4 2) (sourceB1105 + difference 2 4) sourceC1105) = raw18544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18544; decide +kernel
    rw [ha]
    exact (canonical18544 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1105 + difference 4 3) (sourceB1105 + difference 3 4) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1105 + difference 4 3) (sourceB1105 + difference 3 4) sourceC1105) = raw18545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18545; decide +kernel
    rw [ha]
    exact (canonical18545 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1105 + difference 4 5) (sourceB1105 + difference 5 4) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1105 + difference 4 5) (sourceB1105 + difference 5 4) sourceC1105) = raw18546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18546; decide +kernel
    rw [ha]
    exact (canonical18546 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1105 + difference 5 0) (sourceB1105 + difference 0 5) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA1105 + difference 5 0) (sourceB1105 + difference 0 5) sourceC1105) = raw13401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw13401; decide +kernel
    rw [ha]
    exact (canonical13401 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1105 + difference 5 1) (sourceB1105 + difference 1 5) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA1105 + difference 5 1) (sourceB1105 + difference 1 5) sourceC1105) = raw18547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18547; decide +kernel
    rw [ha]
    exact (canonical18547 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1105 + difference 5 2) (sourceB1105 + difference 2 5) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5391) := by
    have ha : (tripleCharges (sourceA1105 + difference 5 2) (sourceB1105 + difference 2 5) sourceC1105) = raw18548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18548; decide +kernel
    rw [ha]
    exact (canonical18548 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1105 + difference 5 3) (sourceB1105 + difference 3 5) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1105 + difference 5 3) (sourceB1105 + difference 3 5) sourceC1105) = raw18549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18549; decide +kernel
    rw [ha]
    exact (canonical18549 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1105 + difference 5 4) (sourceB1105 + difference 4 5) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1105 + difference 5 4) (sourceB1105 + difference 4 5) sourceC1105) = raw18550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18550; decide +kernel
    rw [ha]
    exact (canonical18550 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1105 sourceB1105 sourceC1105
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1105, Integer.Sparse.eval]
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

theorem reindexCheck958 : Integer.Sparse.reindex keyMap MixedData.row958 = numericRow958 := by decide +kernel

theorem numericCheck958 (x : Master → ℝ) : Integer.Sparse.eval numericRow958 x =
    (5760 : ℝ) * reducedSource958 x := by
  norm_num [numericRow958, reducedSource958, Integer.Sparse.eval, Sparse.eval, nodeValue5123, nodeValue5162, nodeValue5192, nodeValue5202, nodeValue5227, nodeValue5283, nodeValue5391, nodeValue5411, nodeValue5447, nodeValue5450, nodeValue5452, nodeValue5462, nodeValue5485] <;> ring

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

theorem reducedZero958 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource958 (mixedVector B) = 0 := by
  have h5123 : mixedVector B (Sum.inr 5123) = Sparse.eval nodeValue5123 (mixedVector B) := by
    change mixedMoment B node5123 node5123Labels = _
    exact sound5123 B hB hF
  have h5162 : mixedVector B (Sum.inr 5162) = Sparse.eval nodeValue5162 (mixedVector B) := by
    change mixedMoment B node5162 node5162Labels = _
    exact sound5162 B hB hF
  have h5192 : mixedVector B (Sum.inr 5192) = Sparse.eval nodeValue5192 (mixedVector B) := by
    change mixedMoment B node5192 node5192Labels = _
    exact sound5192 B hB hF
  have h5202 : mixedVector B (Sum.inr 5202) = Sparse.eval nodeValue5202 (mixedVector B) := by
    change mixedMoment B node5202 node5202Labels = _
    exact sound5202 B hB hF
  have h5227 : mixedVector B (Sum.inr 5227) = Sparse.eval nodeValue5227 (mixedVector B) := by
    change mixedMoment B node5227 node5227Labels = _
    exact sound5227 B hB hF
  have h5283 : mixedVector B (Sum.inr 5283) = Sparse.eval nodeValue5283 (mixedVector B) := by
    change mixedMoment B node5283 node5283Labels = _
    exact sound5283 B hB hF
  have h5391 : mixedVector B (Sum.inr 5391) = Sparse.eval nodeValue5391 (mixedVector B) := by
    change mixedMoment B node5391 node5391Labels = _
    exact sound5391 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450_e B hB hF
  have h5452 : mixedVector B (Sum.inr 5452) = Sparse.eval nodeValue5452 (mixedVector B) := by
    change mixedMoment B node5452 node5452Labels = _
    exact sound5452_e B hB hF
  have h5462 : mixedVector B (Sum.inr 5462) = Sparse.eval nodeValue5462 (mixedVector B) := by
    change mixedMoment B node5462 node5462Labels = _
    exact sound5462 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485_e B hB hF
  simpa only [sourceForm1105, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5123, h5162, h5192, h5202, h5227, h5283, h5391, h5411, h5447, h5450, h5452, h5462, h5485, reducedSource958] using sourceEq1105 B hB

theorem rowSound958_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row958 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck958, numericCheck958, reducedZero958 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound958_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound958_e_oai
