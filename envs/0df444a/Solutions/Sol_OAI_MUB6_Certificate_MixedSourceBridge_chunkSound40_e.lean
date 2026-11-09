-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound40_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:15:17.028563+00:00
-- url     : https://prove2.me/submissions/dd54c815-81f4-422e-b481-fa2b510d09a5

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5485_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound643_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound644_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound649_e

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

theorem canonical2289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2289 raw2289Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw2289 raw2289Labels = mixedMoment B raw2289step0 raw2289step0Labels := by
      have ha : raw2289step0 = (fun i j => raw2289 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2289step0 raw2289; decide +kernel
      have hl : raw2289step0Labels = raw2289Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2289 raw2289Labels permutation32 permutation5
    mixedMoment B raw2289step0 raw2289step0Labels = mixedMoment B raw2289step1 raw2289step1Labels := by
      have ha : raw2289step1 = raw2289step0 := by apply Matrix.ext; unfold raw2289step1 raw2289step0; decide +kernel
      have hl : raw2289step0Labels = labelEmbedding8 ∘ raw2289step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2289step0 raw2289step0Labels raw2289step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2290 raw2290Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw2290 raw2290Labels = mixedMoment B raw2290step0 raw2290step0Labels := by
      have ha : raw2290step0 = (fun i j => raw2290 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2290step0 raw2290; decide +kernel
      have hl : raw2290step0Labels = raw2290Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2290 raw2290Labels permutation32 permutation4
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2291 raw2291Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw2291 raw2291Labels = mixedMoment B raw2291step0 raw2291step0Labels := by
      have ha : raw2291step0 = (fun i j => raw2291 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2291step0 raw2291; decide +kernel
      have hl : raw2291step0Labels = raw2291Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2291 raw2291Labels permutation48 permutation3
    mixedMoment B raw2291step0 raw2291step0Labels = mixedMoment B raw2291step1 raw2291step1Labels := by
      have ha : raw2291step1 = -raw2291step0 := by apply Matrix.ext; change ∀ i j, raw2291step1 i j = -(raw2291step0 i j); unfold raw2291step1 raw2291step0; decide +kernel
      have hl : raw2291step1Labels = raw2291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2291step1 raw2291step1Labels = mixedMoment B raw2291step2 raw2291step2Labels := by
      have ha : raw2291step2 = raw2291step1 := by apply Matrix.ext; unfold raw2291step2 raw2291step1; decide +kernel
      have hl : raw2291step1Labels = labelEmbedding1 ∘ raw2291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2291step1 raw2291step1Labels raw2291step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

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

theorem canonical2538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2538 raw2538Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw2538 raw2538Labels = mixedMoment B raw2538step0 raw2538step0Labels := by
      have ha : raw2538step0 = (fun i j => raw2538 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2538step0 raw2538; decide +kernel
      have hl : raw2538step0Labels = raw2538Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2538 raw2538Labels permutation32 permutation4
    mixedMoment B raw2538step0 raw2538step0Labels = mixedMoment B raw2538step1 raw2538step1Labels := by
      have ha : raw2538step1 = raw2538step0 := by apply Matrix.ext; unfold raw2538step1 raw2538step0; decide +kernel
      have hl : raw2538step0Labels = labelEmbedding7 ∘ raw2538step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2538step0 raw2538step0Labels raw2538step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical2539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2539 raw2539Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw2539 raw2539Labels = mixedMoment B raw2539step0 raw2539step0Labels := by
      have ha : raw2539step0 = (fun i j => raw2539 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2539step0 raw2539; decide +kernel
      have hl : raw2539step0Labels = raw2539Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2539 raw2539Labels permutation32 permutation4
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical2540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2540 raw2540Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw2540 raw2540Labels = mixedMoment B raw2540step0 raw2540step0Labels := by
      have ha : raw2540step0 = (fun i j => raw2540 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2540step0 raw2540; decide +kernel
      have hl : raw2540step0Labels = raw2540Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2540 raw2540Labels permutation38 permutation6
    mixedMoment B raw2540step0 raw2540step0Labels = mixedMoment B raw2540step1 raw2540step1Labels := by
      have ha : raw2540step1 = -raw2540step0 := by apply Matrix.ext; change ∀ i j, raw2540step1 i j = -(raw2540step0 i j); unfold raw2540step1 raw2540step0; decide +kernel
      have hl : raw2540step1Labels = raw2540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2540step1 raw2540step1Labels = mixedMoment B raw2540step2 raw2540step2Labels := by
      have ha : raw2540step2 = raw2540step1 := by apply Matrix.ext; unfold raw2540step2 raw2540step1; decide +kernel
      have hl : raw2540step1Labels = labelEmbedding1 ∘ raw2540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2540step1 raw2540step1Labels raw2540step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

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

theorem canonical2607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2607 raw2607Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw2607 raw2607Labels = mixedMoment B raw2607step0 raw2607step0Labels := by
      have ha : raw2607step0 = (fun i j => raw2607 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2607step0 raw2607; decide +kernel
      have hl : raw2607step0Labels = raw2607Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2607 raw2607Labels permutation32 permutation4
    mixedMoment B raw2607step0 raw2607step0Labels = mixedMoment B raw2607step1 raw2607step1Labels := by
      have ha : raw2607step1 = raw2607step0 := by apply Matrix.ext; unfold raw2607step1 raw2607step0; decide +kernel
      have hl : raw2607step0Labels = labelEmbedding7 ∘ raw2607step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2607step0 raw2607step0Labels raw2607step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical2608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2608 raw2608Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw2608 raw2608Labels = mixedMoment B raw2608step0 raw2608step0Labels := by
      have ha : raw2608step0 = (fun i j => raw2608 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2608step0 raw2608; decide +kernel
      have hl : raw2608step0Labels = raw2608Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2608 raw2608Labels permutation32 permutation4
    _ = mixedMoment B node3983 node3983Labels := by rfl

theorem canonical2609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2609 raw2609Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw2609 raw2609Labels = mixedMoment B raw2609step0 raw2609step0Labels := by
      have ha : raw2609step0 = (fun i j => raw2609 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2609step0 raw2609; decide +kernel
      have hl : raw2609step0Labels = raw2609Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2609 raw2609Labels permutation151 permutation6
    mixedMoment B raw2609step0 raw2609step0Labels = mixedMoment B raw2609step1 raw2609step1Labels := by
      have ha : raw2609step1 = raw2609step0 := by apply Matrix.ext; unfold raw2609step1 raw2609step0; decide +kernel
      have hl : raw2609step0Labels = labelEmbedding1 ∘ raw2609step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2609step0 raw2609step0Labels raw2609step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11753 raw11753Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw11753 raw11753Labels = mixedMoment B raw11753step0 raw11753step0Labels := by
      have ha : raw11753step0 = (fun i j => raw11753 (permutation195 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11753step0 raw11753; decide +kernel
      have hl : raw11753step0Labels = raw11753Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11753 raw11753Labels permutation195 permutation2
    mixedMoment B raw11753step0 raw11753step0Labels = mixedMoment B raw11753step1 raw11753step1Labels := by
      have ha : raw11753step1 = -raw11753step0 := by apply Matrix.ext; change ∀ i j, raw11753step1 i j = -(raw11753step0 i j); unfold raw11753step1 raw11753step0; decide +kernel
      have hl : raw11753step1Labels = raw11753step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3503 node3503Labels := by rfl

theorem canonical11756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11756 raw11756Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11756 raw11756Labels = mixedMoment B raw11756step0 raw11756step0Labels := by
      have hz : ∀ j, raw11756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11756step0 = (fun i j => raw11756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11756step0 raw11756; decide +kernel
      have hl : raw11756step0Labels = raw11756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11756 raw11756Labels permutation346 hz
    mixedMoment B raw11756step0 raw11756step0Labels = mixedMoment B raw11756step1 raw11756step1Labels := by
      have hz : ∀ j, raw11756step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11756step1 = (fun i j => raw11756step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11756step1 raw11756step0; decide +kernel
      have hl : raw11756step1Labels = raw11756step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11756step0 raw11756step0Labels permutation56 hz
    mixedMoment B raw11756step1 raw11756step1Labels = mixedMoment B raw11756step2 raw11756step2Labels := by
      have ha : raw11756step2 = -raw11756step1 := by apply Matrix.ext; change ∀ i j, raw11756step2 i j = -(raw11756step1 i j); unfold raw11756step2 raw11756step1; decide +kernel
      have hl : raw11756step2Labels = raw11756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical11762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11762 raw11762Labels = mixedMoment B node3500 node3500Labels := by
  calc
    mixedMoment B raw11762 raw11762Labels = mixedMoment B raw11762step0 raw11762step0Labels := by
      have ha : raw11762step0 = (fun i j => raw11762 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11762step0 raw11762; decide +kernel
      have hl : raw11762step0Labels = raw11762Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11762 raw11762Labels permutation160 permutation4
    mixedMoment B raw11762step0 raw11762step0Labels = mixedMoment B raw11762step1 raw11762step1Labels := by
      have ha : raw11762step1 = -raw11762step0 := by apply Matrix.ext; change ∀ i j, raw11762step1 i j = -(raw11762step0 i j); unfold raw11762step1 raw11762step0; decide +kernel
      have hl : raw11762step1Labels = raw11762step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3500 node3500Labels := by rfl

theorem canonical11769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11769 raw11769Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw11769 raw11769Labels = mixedMoment B raw11769step0 raw11769step0Labels := by
      have hz : ∀ j, raw11769 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11769step0 = (fun i j => raw11769 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11769step0 raw11769; decide +kernel
      have hl : raw11769step0Labels = raw11769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11769 raw11769Labels permutation265 hz
    mixedMoment B raw11769step0 raw11769step0Labels = mixedMoment B raw11769step1 raw11769step1Labels := by
      have ha : raw11769step1 = (fun i j => raw11769step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11769step1 raw11769step0; decide +kernel
      have hl : raw11769step1Labels = raw11769step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11769step0 raw11769step0Labels permutation40 permutation4
    mixedMoment B raw11769step1 raw11769step1Labels = mixedMoment B raw11769step2 raw11769step2Labels := by
      have ha : raw11769step2 = -raw11769step1 := by apply Matrix.ext; change ∀ i j, raw11769step2 i j = -(raw11769step1 i j); unfold raw11769step2 raw11769step1; decide +kernel
      have hl : raw11769step2Labels = raw11769step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical11770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11770 raw11770Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw11770 raw11770Labels = mixedMoment B raw11770step0 raw11770step0Labels := by
      have ha : raw11770step0 = (fun i j => raw11770 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11770step0 raw11770; decide +kernel
      have hl : raw11770step0Labels = raw11770Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11770 raw11770Labels permutation158 permutation4
    mixedMoment B raw11770step0 raw11770step0Labels = mixedMoment B raw11770step1 raw11770step1Labels := by
      have ha : raw11770step1 = -raw11770step0 := by apply Matrix.ext; change ∀ i j, raw11770step1 i j = -(raw11770step0 i j); unfold raw11770step1 raw11770step0; decide +kernel
      have hl : raw11770step1Labels = raw11770step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3503 node3503Labels := by rfl

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

theorem canonical12078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12078 raw12078Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw12078 raw12078Labels = mixedMoment B raw12078step0 raw12078step0Labels := by
      have hz : ∀ j, raw12078 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12078step0 = (fun i j => raw12078 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12078step0 raw12078; decide +kernel
      have hl : raw12078step0Labels = raw12078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12078 raw12078Labels permutation265 hz
    mixedMoment B raw12078step0 raw12078step0Labels = mixedMoment B raw12078step1 raw12078step1Labels := by
      have ha : raw12078step1 = (fun i j => raw12078step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12078step1 raw12078step0; decide +kernel
      have hl : raw12078step1Labels = raw12078step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12078step0 raw12078step0Labels permutation41 permutation4
    mixedMoment B raw12078step1 raw12078step1Labels = mixedMoment B raw12078step2 raw12078step2Labels := by
      have ha : raw12078step2 = -raw12078step1 := by apply Matrix.ext; change ∀ i j, raw12078step2 i j = -(raw12078step1 i j); unfold raw12078step2 raw12078step1; decide +kernel
      have hl : raw12078step2Labels = raw12078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3573 node3573Labels := by rfl

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

theorem canonical12227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12227 raw12227Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw12227 raw12227Labels = mixedMoment B raw12227step0 raw12227step0Labels := by
      have hz : ∀ j, raw12227 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12227step0 = (fun i j => raw12227 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12227step0 raw12227; decide +kernel
      have hl : raw12227step0Labels = raw12227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12227 raw12227Labels permutation346 hz
    mixedMoment B raw12227step0 raw12227step0Labels = mixedMoment B raw12227step1 raw12227step1Labels := by
      have hz : ∀ j, raw12227step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12227step1 = (fun i j => raw12227step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12227step1 raw12227step0; decide +kernel
      have hl : raw12227step1Labels = raw12227step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12227step0 raw12227step0Labels permutation56 hz
    mixedMoment B raw12227step1 raw12227step1Labels = mixedMoment B raw12227step2 raw12227step2Labels := by
      have ha : raw12227step2 = (fun i j => raw12227step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12227step2 raw12227step1; decide +kernel
      have hl : raw12227step2Labels = raw12227step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12227step1 raw12227step1Labels permutation13 permutation2
    mixedMoment B raw12227step2 raw12227step2Labels = mixedMoment B raw12227step3 raw12227step3Labels := by
      have ha : raw12227step3 = -raw12227step2 := by apply Matrix.ext; change ∀ i j, raw12227step3 i j = -(raw12227step2 i j); unfold raw12227step3 raw12227step2; decide +kernel
      have hl : raw12227step3Labels = raw12227step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3583 node3583Labels := by rfl

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

theorem canonical12320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12320 raw12320Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw12320 raw12320Labels = mixedMoment B raw12320step0 raw12320step0Labels := by
      have hz : ∀ j, raw12320 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12320step0 = (fun i j => raw12320 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12320step0 raw12320; decide +kernel
      have hl : raw12320step0Labels = raw12320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12320 raw12320Labels permutation265 hz
    _ = mixedMoment B node2763 node2763Labels := by rfl

theorem canonical12322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12322 raw12322Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw12322 raw12322Labels = mixedMoment B raw12322step0 raw12322step0Labels := by
      have hz : ∀ j, raw12322 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12322step0 = (fun i j => raw12322 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12322step0 raw12322; decide +kernel
      have hl : raw12322step0Labels = raw12322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12322 raw12322Labels permutation265 hz
    _ = mixedMoment B node3884 node3884Labels := by rfl

theorem canonical12326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12326 raw12326Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw12326 raw12326Labels = mixedMoment B raw12326step0 raw12326step0Labels := by
      have hz : ∀ j, raw12326 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12326step0 = (fun i j => raw12326 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12326step0 raw12326; decide +kernel
      have hl : raw12326step0Labels = raw12326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12326 raw12326Labels permutation520 hz
    mixedMoment B raw12326step0 raw12326step0Labels = mixedMoment B raw12326step1 raw12326step1Labels := by
      have hz : ∀ j, raw12326step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12326step1 = (fun i j => raw12326step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12326step1 raw12326step0; decide +kernel
      have hl : raw12326step1Labels = raw12326step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12326step0 raw12326step0Labels permutation56 hz
    mixedMoment B raw12326step1 raw12326step1Labels = mixedMoment B raw12326step2 raw12326step2Labels := by
      have ha : raw12326step2 = (fun i j => raw12326step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw12326step2 raw12326step1; decide +kernel
      have hl : raw12326step2Labels = raw12326step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12326step1 raw12326step1Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical12328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12328 raw12328Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw12328 raw12328Labels = mixedMoment B raw12328step0 raw12328step0Labels := by
      have hz : ∀ j, raw12328 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12328step0 = (fun i j => raw12328 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12328step0 raw12328; decide +kernel
      have hl : raw12328step0Labels = raw12328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12328 raw12328Labels permutation265 hz
    mixedMoment B raw12328step0 raw12328step0Labels = mixedMoment B raw12328step1 raw12328step1Labels := by
      have ha : raw12328step1 = (fun i j => raw12328step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12328step1 raw12328step0; decide +kernel
      have hl : raw12328step1Labels = raw12328step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12328step0 raw12328step0Labels permutation40 permutation2
    _ = mixedMoment B node1291 node1291Labels := by rfl

theorem canonical12332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12332 raw12332Labels = mixedMoment B node2587 node2587Labels := by
  calc
    mixedMoment B raw12332 raw12332Labels = mixedMoment B raw12332step0 raw12332step0Labels := by
      have ha : raw12332step0 = (fun i j => raw12332 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12332step0 raw12332; decide +kernel
      have hl : raw12332step0Labels = raw12332Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12332 raw12332Labels permutation160 permutation2
    _ = mixedMoment B node2587 node2587Labels := by rfl

theorem canonical12336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12336 raw12336Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw12336 raw12336Labels = mixedMoment B raw12336step0 raw12336step0Labels := by
      have hz : ∀ j, raw12336 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12336step0 = (fun i j => raw12336 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12336step0 raw12336; decide +kernel
      have hl : raw12336step0Labels = raw12336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12336 raw12336Labels permutation265 hz
    mixedMoment B raw12336step0 raw12336step0Labels = mixedMoment B raw12336step1 raw12336step1Labels := by
      have ha : raw12336step1 = (fun i j => raw12336step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12336step1 raw12336step0; decide +kernel
      have hl : raw12336step1Labels = raw12336step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12336step0 raw12336step0Labels permutation40 permutation2
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical12337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12337 raw12337Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw12337 raw12337Labels = mixedMoment B raw12337step0 raw12337step0Labels := by
      have hz : ∀ j, raw12337 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12337step0 = (fun i j => raw12337 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12337step0 raw12337; decide +kernel
      have hl : raw12337step0Labels = raw12337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12337 raw12337Labels permutation520 hz
    mixedMoment B raw12337step0 raw12337step0Labels = mixedMoment B raw12337step1 raw12337step1Labels := by
      have hz : ∀ j, raw12337step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12337step1 = (fun i j => raw12337step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12337step1 raw12337step0; decide +kernel
      have hl : raw12337step1Labels = raw12337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12337step0 raw12337step0Labels permutation56 hz
    mixedMoment B raw12337step1 raw12337step1Labels = mixedMoment B raw12337step2 raw12337step2Labels := by
      have ha : raw12337step2 = (fun i j => raw12337step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12337step2 raw12337step1; decide +kernel
      have hl : raw12337step2Labels = raw12337step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12337step1 raw12337step1Labels permutation10 permutation2
    _ = mixedMoment B node2782 node2782Labels := by rfl

theorem canonical12338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12338 raw12338Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw12338 raw12338Labels = mixedMoment B raw12338step0 raw12338step0Labels := by
      have hz : ∀ j, raw12338 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12338step0 = (fun i j => raw12338 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12338step0 raw12338; decide +kernel
      have hl : raw12338step0Labels = raw12338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12338 raw12338Labels permutation265 hz
    mixedMoment B raw12338step0 raw12338step0Labels = mixedMoment B raw12338step1 raw12338step1Labels := by
      have ha : raw12338step1 = (fun i j => raw12338step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12338step1 raw12338step0; decide +kernel
      have hl : raw12338step1Labels = raw12338step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12338step0 raw12338step0Labels permutation53 permutation2
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical12339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12339 raw12339Labels = mixedMoment B node2630 node2630Labels := by
  calc
    mixedMoment B raw12339 raw12339Labels = mixedMoment B raw12339step0 raw12339step0Labels := by
      have ha : raw12339step0 = (fun i j => raw12339 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12339step0 raw12339; decide +kernel
      have hl : raw12339step0Labels = raw12339Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12339 raw12339Labels permutation182 permutation2
    _ = mixedMoment B node2630 node2630Labels := by rfl

theorem canonical12340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12340 raw12340Labels = mixedMoment B node2639 node2639Labels := by
  calc
    mixedMoment B raw12340 raw12340Labels = mixedMoment B raw12340step0 raw12340step0Labels := by
      have hz : ∀ j, raw12340 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12340step0 = (fun i j => raw12340 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12340step0 raw12340; decide +kernel
      have hl : raw12340step0Labels = raw12340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12340 raw12340Labels permutation265 hz
    mixedMoment B raw12340step0 raw12340step0Labels = mixedMoment B raw12340step1 raw12340step1Labels := by
      have ha : raw12340step1 = (fun i j => raw12340step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12340step1 raw12340step0; decide +kernel
      have hl : raw12340step1Labels = raw12340step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12340step0 raw12340step0Labels permutation35 permutation2
    _ = mixedMoment B node2639 node2639Labels := by rfl

theorem canonical12341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12341 raw12341Labels = mixedMoment B node2634 node2634Labels := by
  calc
    mixedMoment B raw12341 raw12341Labels = mixedMoment B raw12341step0 raw12341step0Labels := by
      have hz : ∀ j, raw12341 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12341step0 = (fun i j => raw12341 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12341step0 raw12341; decide +kernel
      have hl : raw12341step0Labels = raw12341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12341 raw12341Labels permutation265 hz
    mixedMoment B raw12341step0 raw12341step0Labels = mixedMoment B raw12341step1 raw12341step1Labels := by
      have ha : raw12341step1 = (fun i j => raw12341step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12341step1 raw12341step0; decide +kernel
      have hl : raw12341step1Labels = raw12341step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12341step0 raw12341step0Labels permutation33 permutation2
    _ = mixedMoment B node2634 node2634Labels := by rfl

theorem canonical12342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12342 raw12342Labels = mixedMoment B node2632 node2632Labels := by
  calc
    mixedMoment B raw12342 raw12342Labels = mixedMoment B raw12342step0 raw12342step0Labels := by
      have hz : ∀ j, raw12342 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12342step0 = (fun i j => raw12342 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12342step0 raw12342; decide +kernel
      have hl : raw12342step0Labels = raw12342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12342 raw12342Labels permutation265 hz
    _ = mixedMoment B node2632 node2632Labels := by rfl

theorem canonical12343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12343 raw12343Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw12343 raw12343Labels = mixedMoment B raw12343step0 raw12343step0Labels := by
      have ha : raw12343step0 = (fun i j => raw12343 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12343step0 raw12343; decide +kernel
      have hl : raw12343step0Labels = raw12343Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12343 raw12343Labels permutation152 permutation3
    mixedMoment B raw12343step0 raw12343step0Labels = mixedMoment B raw12343step1 raw12343step1Labels := by
      have ha : raw12343step1 = raw12343step0 := by apply Matrix.ext; unfold raw12343step1 raw12343step0; decide +kernel
      have hl : raw12343step0Labels = labelEmbedding6 ∘ raw12343step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12343step0 raw12343step0Labels raw12343step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

theorem canonical12344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12344 raw12344Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw12344 raw12344Labels = mixedMoment B raw12344step0 raw12344step0Labels := by
      have hz : ∀ j, raw12344 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12344step0 = (fun i j => raw12344 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12344step0 raw12344; decide +kernel
      have hl : raw12344step0Labels = raw12344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12344 raw12344Labels permutation265 hz
    mixedMoment B raw12344step0 raw12344step0Labels = mixedMoment B raw12344step1 raw12344step1Labels := by
      have ha : raw12344step1 = (fun i j => raw12344step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12344step1 raw12344step0; decide +kernel
      have hl : raw12344step1Labels = raw12344step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12344step0 raw12344step0Labels permutation37 permutation2
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical12345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12345 raw12345Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw12345 raw12345Labels = mixedMoment B raw12345step0 raw12345step0Labels := by
      have hz : ∀ j, raw12345 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12345step0 = (fun i j => raw12345 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12345step0 raw12345; decide +kernel
      have hl : raw12345step0Labels = raw12345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12345 raw12345Labels permutation265 hz
    mixedMoment B raw12345step0 raw12345step0Labels = mixedMoment B raw12345step1 raw12345step1Labels := by
      have ha : raw12345step1 = (fun i j => raw12345step0 (permutation92 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12345step1 raw12345step0; decide +kernel
      have hl : raw12345step1Labels = raw12345step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12345step0 raw12345step0Labels permutation92 permutation6
    mixedMoment B raw12345step1 raw12345step1Labels = mixedMoment B raw12345step2 raw12345step2Labels := by
      have ha : raw12345step2 = raw12345step1 := by apply Matrix.ext; unfold raw12345step2 raw12345step1; decide +kernel
      have hl : raw12345step1Labels = labelEmbedding9 ∘ raw12345step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12345step1 raw12345step1Labels raw12345step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical12346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12346 raw12346Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw12346 raw12346Labels = mixedMoment B raw12346step0 raw12346step0Labels := by
      have hz : ∀ j, raw12346 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12346step0 = (fun i j => raw12346 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12346step0 raw12346; decide +kernel
      have hl : raw12346step0Labels = raw12346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12346 raw12346Labels permutation265 hz
    mixedMoment B raw12346step0 raw12346step0Labels = mixedMoment B raw12346step1 raw12346step1Labels := by
      have ha : raw12346step1 = (fun i j => raw12346step0 (permutation135 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12346step1 raw12346step0; decide +kernel
      have hl : raw12346step1Labels = raw12346step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12346step0 raw12346step0Labels permutation135 permutation4
    mixedMoment B raw12346step1 raw12346step1Labels = mixedMoment B raw12346step2 raw12346step2Labels := by
      have ha : raw12346step2 = raw12346step1 := by apply Matrix.ext; unfold raw12346step2 raw12346step1; decide +kernel
      have hl : raw12346step1Labels = labelEmbedding7 ∘ raw12346step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12346step1 raw12346step1Labels raw12346step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical12347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12347 raw12347Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw12347 raw12347Labels = mixedMoment B raw12347step0 raw12347step0Labels := by
      have hz : ∀ j, raw12347 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12347step0 = (fun i j => raw12347 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12347step0 raw12347; decide +kernel
      have hl : raw12347step0Labels = raw12347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12347 raw12347Labels permutation265 hz
    mixedMoment B raw12347step0 raw12347step0Labels = mixedMoment B raw12347step1 raw12347step1Labels := by
      have ha : raw12347step1 = (fun i j => raw12347step0 (permutation95 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12347step1 raw12347step0; decide +kernel
      have hl : raw12347step1Labels = raw12347step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12347step0 raw12347step0Labels permutation95 permutation7
    mixedMoment B raw12347step1 raw12347step1Labels = mixedMoment B raw12347step2 raw12347step2Labels := by
      have ha : raw12347step2 = raw12347step1 := by apply Matrix.ext; unfold raw12347step2 raw12347step1; decide +kernel
      have hl : raw12347step1Labels = labelEmbedding10 ∘ raw12347step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12347step1 raw12347step1Labels raw12347step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

theorem canonical12348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12348 raw12348Labels = mixedMoment B node4449 node4449Labels := by
  calc
    mixedMoment B raw12348 raw12348Labels = mixedMoment B raw12348step0 raw12348step0Labels := by
      have ha : raw12348step0 = (fun i j => raw12348 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12348step0 raw12348; decide +kernel
      have hl : raw12348step0Labels = raw12348Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12348 raw12348Labels permutation184 permutation3
    mixedMoment B raw12348step0 raw12348step0Labels = mixedMoment B raw12348step1 raw12348step1Labels := by
      have ha : raw12348step1 = raw12348step0 := by apply Matrix.ext; unfold raw12348step1 raw12348step0; decide +kernel
      have hl : raw12348step0Labels = labelEmbedding6 ∘ raw12348step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12348step0 raw12348step0Labels raw12348step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4449 node4449Labels := by rfl

theorem canonical12349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12349 raw12349Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw12349 raw12349Labels = mixedMoment B raw12349step0 raw12349step0Labels := by
      have ha : raw12349step0 = (fun i j => raw12349 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12349step0 raw12349; decide +kernel
      have hl : raw12349step0Labels = raw12349Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12349 raw12349Labels permutation184 permutation3
    mixedMoment B raw12349step0 raw12349step0Labels = mixedMoment B raw12349step1 raw12349step1Labels := by
      have ha : raw12349step1 = raw12349step0 := by apply Matrix.ext; unfold raw12349step1 raw12349step0; decide +kernel
      have hl : raw12349step0Labels = labelEmbedding6 ∘ raw12349step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12349step0 raw12349step0Labels raw12349step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

theorem canonical12350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12350 raw12350Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw12350 raw12350Labels = mixedMoment B raw12350step0 raw12350step0Labels := by
      have ha : raw12350step0 = (fun i j => raw12350 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12350step0 raw12350; decide +kernel
      have hl : raw12350step0Labels = raw12350Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12350 raw12350Labels permutation208 permutation3
    mixedMoment B raw12350step0 raw12350step0Labels = mixedMoment B raw12350step1 raw12350step1Labels := by
      have ha : raw12350step1 = raw12350step0 := by apply Matrix.ext; unfold raw12350step1 raw12350step0; decide +kernel
      have hl : raw12350step0Labels = labelEmbedding6 ∘ raw12350step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12350step0 raw12350step0Labels raw12350step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

theorem canonical12351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12351 raw12351Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw12351 raw12351Labels = mixedMoment B raw12351step0 raw12351step0Labels := by
      have ha : raw12351step0 = (fun i j => raw12351 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12351step0 raw12351; decide +kernel
      have hl : raw12351step0Labels = raw12351Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12351 raw12351Labels permutation232 permutation3
    mixedMoment B raw12351step0 raw12351step0Labels = mixedMoment B raw12351step1 raw12351step1Labels := by
      have ha : raw12351step1 = raw12351step0 := by apply Matrix.ext; unfold raw12351step1 raw12351step0; decide +kernel
      have hl : raw12351step0Labels = labelEmbedding6 ∘ raw12351step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12351step0 raw12351step0Labels raw12351step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

theorem canonical12352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12352 raw12352Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw12352 raw12352Labels = mixedMoment B raw12352step0 raw12352step0Labels := by
      have ha : raw12352step0 = (fun i j => raw12352 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12352step0 raw12352; decide +kernel
      have hl : raw12352step0Labels = raw12352Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12352 raw12352Labels permutation197 permutation3
    mixedMoment B raw12352step0 raw12352step0Labels = mixedMoment B raw12352step1 raw12352step1Labels := by
      have ha : raw12352step1 = raw12352step0 := by apply Matrix.ext; unfold raw12352step1 raw12352step0; decide +kernel
      have hl : raw12352step0Labels = labelEmbedding6 ∘ raw12352step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12352step0 raw12352step0Labels raw12352step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical12353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12353 raw12353Labels = mixedMoment B node4487 node4487Labels := by
  calc
    mixedMoment B raw12353 raw12353Labels = mixedMoment B raw12353step0 raw12353step0Labels := by
      have hz : ∀ j, raw12353 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12353step0 = (fun i j => raw12353 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12353step0 raw12353; decide +kernel
      have hl : raw12353step0Labels = raw12353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12353 raw12353Labels permutation265 hz
    mixedMoment B raw12353step0 raw12353step0Labels = mixedMoment B raw12353step1 raw12353step1Labels := by
      have ha : raw12353step1 = (fun i j => raw12353step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12353step1 raw12353step0; decide +kernel
      have hl : raw12353step1Labels = raw12353step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12353step0 raw12353step0Labels permutation40 permutation3
    mixedMoment B raw12353step1 raw12353step1Labels = mixedMoment B raw12353step2 raw12353step2Labels := by
      have ha : raw12353step2 = raw12353step1 := by apply Matrix.ext; unfold raw12353step2 raw12353step1; decide +kernel
      have hl : raw12353step1Labels = labelEmbedding6 ∘ raw12353step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12353step1 raw12353step1Labels raw12353step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4487 node4487Labels := by rfl

theorem canonical12354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12354 raw12354Labels = mixedMoment B node5092 node5092Labels := by
  calc
    mixedMoment B raw12354 raw12354Labels = mixedMoment B raw12354step0 raw12354step0Labels := by
      have ha : raw12354step0 = (fun i j => raw12354 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12354step0 raw12354; decide +kernel
      have hl : raw12354step0Labels = raw12354Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12354 raw12354Labels permutation160 permutation3
    mixedMoment B raw12354step0 raw12354step0Labels = mixedMoment B raw12354step1 raw12354step1Labels := by
      have ha : raw12354step1 = raw12354step0 := by apply Matrix.ext; unfold raw12354step1 raw12354step0; decide +kernel
      have hl : raw12354step0Labels = labelEmbedding6 ∘ raw12354step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12354step0 raw12354step0Labels raw12354step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5092 node5092Labels := by rfl

theorem canonical12355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12355 raw12355Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw12355 raw12355Labels = mixedMoment B raw12355step0 raw12355step0Labels := by
      have hz : ∀ j, raw12355 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12355step0 = (fun i j => raw12355 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12355step0 raw12355; decide +kernel
      have hl : raw12355step0Labels = raw12355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12355 raw12355Labels permutation265 hz
    mixedMoment B raw12355step0 raw12355step0Labels = mixedMoment B raw12355step1 raw12355step1Labels := by
      have ha : raw12355step1 = (fun i j => raw12355step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12355step1 raw12355step0; decide +kernel
      have hl : raw12355step1Labels = raw12355step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12355step0 raw12355step0Labels permutation40 permutation3
    mixedMoment B raw12355step1 raw12355step1Labels = mixedMoment B raw12355step2 raw12355step2Labels := by
      have ha : raw12355step2 = raw12355step1 := by apply Matrix.ext; unfold raw12355step2 raw12355step1; decide +kernel
      have hl : raw12355step1Labels = labelEmbedding6 ∘ raw12355step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12355step1 raw12355step1Labels raw12355step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

theorem canonical12356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12356 raw12356Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw12356 raw12356Labels = mixedMoment B raw12356step0 raw12356step0Labels := by
      have hz : ∀ j, raw12356 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12356step0 = (fun i j => raw12356 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12356step0 raw12356; decide +kernel
      have hl : raw12356step0Labels = raw12356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12356 raw12356Labels permutation265 hz
    mixedMoment B raw12356step0 raw12356step0Labels = mixedMoment B raw12356step1 raw12356step1Labels := by
      have ha : raw12356step1 = (fun i j => raw12356step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12356step1 raw12356step0; decide +kernel
      have hl : raw12356step1Labels = raw12356step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12356step0 raw12356step0Labels permutation46 permutation3
    mixedMoment B raw12356step1 raw12356step1Labels = mixedMoment B raw12356step2 raw12356step2Labels := by
      have ha : raw12356step2 = raw12356step1 := by apply Matrix.ext; unfold raw12356step2 raw12356step1; decide +kernel
      have hl : raw12356step1Labels = labelEmbedding6 ∘ raw12356step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12356step1 raw12356step1Labels raw12356step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

theorem canonical12357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12357 raw12357Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw12357 raw12357Labels = mixedMoment B raw12357step0 raw12357step0Labels := by
      have hz : ∀ j, raw12357 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12357step0 = (fun i j => raw12357 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12357step0 raw12357; decide +kernel
      have hl : raw12357step0Labels = raw12357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12357 raw12357Labels permutation265 hz
    mixedMoment B raw12357step0 raw12357step0Labels = mixedMoment B raw12357step1 raw12357step1Labels := by
      have ha : raw12357step1 = (fun i j => raw12357step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12357step1 raw12357step0; decide +kernel
      have hl : raw12357step1Labels = raw12357step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12357step0 raw12357step0Labels permutation53 permutation3
    mixedMoment B raw12357step1 raw12357step1Labels = mixedMoment B raw12357step2 raw12357step2Labels := by
      have ha : raw12357step2 = raw12357step1 := by apply Matrix.ext; unfold raw12357step2 raw12357step1; decide +kernel
      have hl : raw12357step1Labels = labelEmbedding6 ∘ raw12357step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12357step1 raw12357step1Labels raw12357step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical12358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12358 raw12358Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw12358 raw12358Labels = mixedMoment B raw12358step0 raw12358step0Labels := by
      have hz : ∀ j, raw12358 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12358step0 = (fun i j => raw12358 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12358step0 raw12358; decide +kernel
      have hl : raw12358step0Labels = raw12358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12358 raw12358Labels permutation265 hz
    mixedMoment B raw12358step0 raw12358step0Labels = mixedMoment B raw12358step1 raw12358step1Labels := by
      have ha : raw12358step1 = (fun i j => raw12358step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12358step1 raw12358step0; decide +kernel
      have hl : raw12358step1Labels = raw12358step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12358step0 raw12358step0Labels permutation35 permutation3
    mixedMoment B raw12358step1 raw12358step1Labels = mixedMoment B raw12358step2 raw12358step2Labels := by
      have ha : raw12358step2 = raw12358step1 := by apply Matrix.ext; unfold raw12358step2 raw12358step1; decide +kernel
      have hl : raw12358step1Labels = labelEmbedding6 ∘ raw12358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12358step1 raw12358step1Labels raw12358step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4459 node4459Labels := by rfl

theorem canonical12359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12359 raw12359Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw12359 raw12359Labels = mixedMoment B raw12359step0 raw12359step0Labels := by
      have ha : raw12359step0 = (fun i j => raw12359 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12359step0 raw12359; decide +kernel
      have hl : raw12359step0Labels = raw12359Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12359 raw12359Labels permutation155 permutation3
    mixedMoment B raw12359step0 raw12359step0Labels = mixedMoment B raw12359step1 raw12359step1Labels := by
      have ha : raw12359step1 = raw12359step0 := by apply Matrix.ext; unfold raw12359step1 raw12359step0; decide +kernel
      have hl : raw12359step0Labels = labelEmbedding6 ∘ raw12359step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12359step0 raw12359step0Labels raw12359step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5074 node5074Labels := by rfl

theorem canonical12360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12360 raw12360Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw12360 raw12360Labels = mixedMoment B raw12360step0 raw12360step0Labels := by
      have hz : ∀ j, raw12360 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12360step0 = (fun i j => raw12360 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12360step0 raw12360; decide +kernel
      have hl : raw12360step0Labels = raw12360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12360 raw12360Labels permutation265 hz
    mixedMoment B raw12360step0 raw12360step0Labels = mixedMoment B raw12360step1 raw12360step1Labels := by
      have ha : raw12360step1 = (fun i j => raw12360step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12360step1 raw12360step0; decide +kernel
      have hl : raw12360step1Labels = raw12360step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12360step0 raw12360step0Labels permutation35 permutation3
    mixedMoment B raw12360step1 raw12360step1Labels = mixedMoment B raw12360step2 raw12360step2Labels := by
      have ha : raw12360step2 = raw12360step1 := by apply Matrix.ext; unfold raw12360step2 raw12360step1; decide +kernel
      have hl : raw12360step1Labels = labelEmbedding6 ∘ raw12360step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12360step1 raw12360step1Labels raw12360step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

theorem canonical12361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12361 raw12361Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw12361 raw12361Labels = mixedMoment B raw12361step0 raw12361step0Labels := by
      have hz : ∀ j, raw12361 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12361step0 = (fun i j => raw12361 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12361step0 raw12361; decide +kernel
      have hl : raw12361step0Labels = raw12361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12361 raw12361Labels permutation265 hz
    mixedMoment B raw12361step0 raw12361step0Labels = mixedMoment B raw12361step1 raw12361step1Labels := by
      have ha : raw12361step1 = (fun i j => raw12361step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12361step1 raw12361step0; decide +kernel
      have hl : raw12361step1Labels = raw12361step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12361step0 raw12361step0Labels permutation45 permutation3
    mixedMoment B raw12361step1 raw12361step1Labels = mixedMoment B raw12361step2 raw12361step2Labels := by
      have ha : raw12361step2 = raw12361step1 := by apply Matrix.ext; unfold raw12361step2 raw12361step1; decide +kernel
      have hl : raw12361step1Labels = labelEmbedding6 ∘ raw12361step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12361step1 raw12361step1Labels raw12361step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

theorem canonical12362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12362 raw12362Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw12362 raw12362Labels = mixedMoment B raw12362step0 raw12362step0Labels := by
      have hz : ∀ j, raw12362 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12362step0 = (fun i j => raw12362 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12362step0 raw12362; decide +kernel
      have hl : raw12362step0Labels = raw12362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12362 raw12362Labels permutation265 hz
    mixedMoment B raw12362step0 raw12362step0Labels = mixedMoment B raw12362step1 raw12362step1Labels := by
      have ha : raw12362step1 = (fun i j => raw12362step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12362step1 raw12362step0; decide +kernel
      have hl : raw12362step1Labels = raw12362step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12362step0 raw12362step0Labels permutation37 permutation3
    mixedMoment B raw12362step1 raw12362step1Labels = mixedMoment B raw12362step2 raw12362step2Labels := by
      have ha : raw12362step2 = raw12362step1 := by apply Matrix.ext; unfold raw12362step2 raw12362step1; decide +kernel
      have hl : raw12362step1Labels = labelEmbedding6 ∘ raw12362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12362step1 raw12362step1Labels raw12362step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical12363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12363 raw12363Labels = mixedMoment B node4453 node4453Labels := by
  calc
    mixedMoment B raw12363 raw12363Labels = mixedMoment B raw12363step0 raw12363step0Labels := by
      have hz : ∀ j, raw12363 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12363step0 = (fun i j => raw12363 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12363step0 raw12363; decide +kernel
      have hl : raw12363step0Labels = raw12363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12363 raw12363Labels permutation265 hz
    mixedMoment B raw12363step0 raw12363step0Labels = mixedMoment B raw12363step1 raw12363step1Labels := by
      have ha : raw12363step1 = (fun i j => raw12363step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12363step1 raw12363step0; decide +kernel
      have hl : raw12363step1Labels = raw12363step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12363step0 raw12363step0Labels permutation33 permutation3
    mixedMoment B raw12363step1 raw12363step1Labels = mixedMoment B raw12363step2 raw12363step2Labels := by
      have ha : raw12363step2 = raw12363step1 := by apply Matrix.ext; unfold raw12363step2 raw12363step1; decide +kernel
      have hl : raw12363step1Labels = labelEmbedding6 ∘ raw12363step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12363step1 raw12363step1Labels raw12363step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4453 node4453Labels := by rfl

theorem canonical12364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12364 raw12364Labels = mixedMoment B node5071 node5071Labels := by
  calc
    mixedMoment B raw12364 raw12364Labels = mixedMoment B raw12364step0 raw12364step0Labels := by
      have ha : raw12364step0 = (fun i j => raw12364 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12364step0 raw12364; decide +kernel
      have hl : raw12364step0Labels = raw12364Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12364 raw12364Labels permutation153 permutation3
    mixedMoment B raw12364step0 raw12364step0Labels = mixedMoment B raw12364step1 raw12364step1Labels := by
      have ha : raw12364step1 = raw12364step0 := by apply Matrix.ext; unfold raw12364step1 raw12364step0; decide +kernel
      have hl : raw12364step0Labels = labelEmbedding6 ∘ raw12364step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12364step0 raw12364step0Labels raw12364step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5071 node5071Labels := by rfl

theorem canonical12365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12365 raw12365Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw12365 raw12365Labels = mixedMoment B raw12365step0 raw12365step0Labels := by
      have hz : ∀ j, raw12365 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12365step0 = (fun i j => raw12365 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12365step0 raw12365; decide +kernel
      have hl : raw12365step0Labels = raw12365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12365 raw12365Labels permutation265 hz
    mixedMoment B raw12365step0 raw12365step0Labels = mixedMoment B raw12365step1 raw12365step1Labels := by
      have ha : raw12365step1 = (fun i j => raw12365step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12365step1 raw12365step0; decide +kernel
      have hl : raw12365step1Labels = raw12365step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12365step0 raw12365step0Labels permutation33 permutation3
    mixedMoment B raw12365step1 raw12365step1Labels = mixedMoment B raw12365step2 raw12365step2Labels := by
      have ha : raw12365step2 = raw12365step1 := by apply Matrix.ext; unfold raw12365step2 raw12365step1; decide +kernel
      have hl : raw12365step1Labels = labelEmbedding6 ∘ raw12365step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12365step1 raw12365step1Labels raw12365step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5164 node5164Labels := by rfl

theorem canonical12366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12366 raw12366Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw12366 raw12366Labels = mixedMoment B raw12366step0 raw12366step0Labels := by
      have hz : ∀ j, raw12366 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12366step0 = (fun i j => raw12366 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12366step0 raw12366; decide +kernel
      have hl : raw12366step0Labels = raw12366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12366 raw12366Labels permutation265 hz
    mixedMoment B raw12366step0 raw12366step0Labels = mixedMoment B raw12366step1 raw12366step1Labels := by
      have ha : raw12366step1 = (fun i j => raw12366step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12366step1 raw12366step0; decide +kernel
      have hl : raw12366step1Labels = raw12366step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12366step0 raw12366step0Labels permutation39 permutation3
    mixedMoment B raw12366step1 raw12366step1Labels = mixedMoment B raw12366step2 raw12366step2Labels := by
      have ha : raw12366step2 = raw12366step1 := by apply Matrix.ext; unfold raw12366step2 raw12366step1; decide +kernel
      have hl : raw12366step1Labels = labelEmbedding6 ∘ raw12366step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12366step1 raw12366step1Labels raw12366step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

theorem canonical12367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12367 raw12367Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw12367 raw12367Labels = mixedMoment B raw12367step0 raw12367step0Labels := by
      have hz : ∀ j, raw12367 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12367step0 = (fun i j => raw12367 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12367step0 raw12367; decide +kernel
      have hl : raw12367step0Labels = raw12367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12367 raw12367Labels permutation265 hz
    mixedMoment B raw12367step0 raw12367step0Labels = mixedMoment B raw12367step1 raw12367step1Labels := by
      have ha : raw12367step1 = (fun i j => raw12367step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12367step1 raw12367step0; decide +kernel
      have hl : raw12367step1Labels = raw12367step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12367step0 raw12367step0Labels permutation36 permutation3
    mixedMoment B raw12367step1 raw12367step1Labels = mixedMoment B raw12367step2 raw12367step2Labels := by
      have ha : raw12367step2 = raw12367step1 := by apply Matrix.ext; unfold raw12367step2 raw12367step1; decide +kernel
      have hl : raw12367step1Labels = labelEmbedding6 ∘ raw12367step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12367step1 raw12367step1Labels raw12367step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

theorem canonical12368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12368 raw12368Labels = mixedMoment B node4450 node4450Labels := by
  calc
    mixedMoment B raw12368 raw12368Labels = mixedMoment B raw12368step0 raw12368step0Labels := by
      have hz : ∀ j, raw12368 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12368step0 = (fun i j => raw12368 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12368step0 raw12368; decide +kernel
      have hl : raw12368step0Labels = raw12368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12368 raw12368Labels permutation265 hz
    mixedMoment B raw12368step0 raw12368step0Labels = mixedMoment B raw12368step1 raw12368step1Labels := by
      have ha : raw12368step1 = (fun i j => raw12368step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12368step1 raw12368step0; decide +kernel
      have hl : raw12368step1Labels = raw12368step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12368step0 raw12368step0Labels permutation32 permutation3
    mixedMoment B raw12368step1 raw12368step1Labels = mixedMoment B raw12368step2 raw12368step2Labels := by
      have ha : raw12368step2 = raw12368step1 := by apply Matrix.ext; unfold raw12368step2 raw12368step1; decide +kernel
      have hl : raw12368step1Labels = labelEmbedding6 ∘ raw12368step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12368step1 raw12368step1Labels raw12368step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4450 node4450Labels := by rfl

theorem canonical12369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12369 raw12369Labels = mixedMoment B node5069 node5069Labels := by
  calc
    mixedMoment B raw12369 raw12369Labels = mixedMoment B raw12369step0 raw12369step0Labels := by
      have ha : raw12369step0 = (fun i j => raw12369 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12369step0 raw12369; decide +kernel
      have hl : raw12369step0Labels = raw12369Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12369 raw12369Labels permutation152 permutation3
    mixedMoment B raw12369step0 raw12369step0Labels = mixedMoment B raw12369step1 raw12369step1Labels := by
      have ha : raw12369step1 = raw12369step0 := by apply Matrix.ext; unfold raw12369step1 raw12369step0; decide +kernel
      have hl : raw12369step0Labels = labelEmbedding6 ∘ raw12369step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12369step0 raw12369step0Labels raw12369step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5069 node5069Labels := by rfl

theorem canonical12370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12370 raw12370Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw12370 raw12370Labels = mixedMoment B raw12370step0 raw12370step0Labels := by
      have hz : ∀ j, raw12370 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12370step0 = (fun i j => raw12370 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12370step0 raw12370; decide +kernel
      have hl : raw12370step0Labels = raw12370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12370 raw12370Labels permutation265 hz
    mixedMoment B raw12370step0 raw12370step0Labels = mixedMoment B raw12370step1 raw12370step1Labels := by
      have ha : raw12370step1 = (fun i j => raw12370step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12370step1 raw12370step0; decide +kernel
      have hl : raw12370step1Labels = raw12370step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12370step0 raw12370step0Labels permutation32 permutation3
    mixedMoment B raw12370step1 raw12370step1Labels = mixedMoment B raw12370step2 raw12370step2Labels := by
      have ha : raw12370step2 = raw12370step1 := by apply Matrix.ext; unfold raw12370step2 raw12370step1; decide +kernel
      have hl : raw12370step1Labels = labelEmbedding6 ∘ raw12370step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12370step1 raw12370step1Labels raw12370step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5161 node5161Labels := by rfl

theorem canonical12371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12371 raw12371Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw12371 raw12371Labels = mixedMoment B raw12371step0 raw12371step0Labels := by
      have hz : ∀ j, raw12371 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12371step0 = (fun i j => raw12371 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12371step0 raw12371; decide +kernel
      have hl : raw12371step0Labels = raw12371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12371 raw12371Labels permutation265 hz
    mixedMoment B raw12371step0 raw12371step0Labels = mixedMoment B raw12371step1 raw12371step1Labels := by
      have ha : raw12371step1 = (fun i j => raw12371step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12371step1 raw12371step0; decide +kernel
      have hl : raw12371step1Labels = raw12371step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12371step0 raw12371step0Labels permutation139 permutation5
    mixedMoment B raw12371step1 raw12371step1Labels = mixedMoment B raw12371step2 raw12371step2Labels := by
      have ha : raw12371step2 = raw12371step1 := by apply Matrix.ext; unfold raw12371step2 raw12371step1; decide +kernel
      have hl : raw12371step1Labels = labelEmbedding8 ∘ raw12371step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12371step1 raw12371step1Labels raw12371step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5140 node5140Labels := by rfl

theorem canonical12372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12372 raw12372Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw12372 raw12372Labels = mixedMoment B raw12372step0 raw12372step0Labels := by
      have hz : ∀ j, raw12372 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12372step0 = (fun i j => raw12372 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12372step0 raw12372; decide +kernel
      have hl : raw12372step0Labels = raw12372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12372 raw12372Labels permutation265 hz
    mixedMoment B raw12372step0 raw12372step0Labels = mixedMoment B raw12372step1 raw12372step1Labels := by
      have ha : raw12372step1 = (fun i j => raw12372step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12372step1 raw12372step0; decide +kernel
      have hl : raw12372step1Labels = raw12372step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12372step0 raw12372step0Labels permutation137 permutation5
    mixedMoment B raw12372step1 raw12372step1Labels = mixedMoment B raw12372step2 raw12372step2Labels := by
      have ha : raw12372step2 = raw12372step1 := by apply Matrix.ext; unfold raw12372step2 raw12372step1; decide +kernel
      have hl : raw12372step1Labels = labelEmbedding8 ∘ raw12372step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12372step1 raw12372step1Labels raw12372step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5161 node5161Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12433 raw12433Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw12433 raw12433Labels = mixedMoment B raw12433step0 raw12433step0Labels := by
      have hz : ∀ j, raw12433 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12433step0 = (fun i j => raw12433 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12433step0 raw12433; decide +kernel
      have hl : raw12433step0Labels = raw12433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12433 raw12433Labels permutation265 hz
    mixedMoment B raw12433step0 raw12433step0Labels = mixedMoment B raw12433step1 raw12433step1Labels := by
      have ha : raw12433step1 = (fun i j => raw12433step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12433step1 raw12433step0; decide +kernel
      have hl : raw12433step1Labels = raw12433step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12433step0 raw12433step0Labels permutation37 permutation2
    _ = mixedMoment B node3097 node3097Labels := by rfl

theorem canonical12434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12434 raw12434Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw12434 raw12434Labels = mixedMoment B raw12434step0 raw12434step0Labels := by
      have ha : raw12434step0 = (fun i j => raw12434 (permutation641 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12434step0 raw12434; decide +kernel
      have hl : raw12434step0Labels = raw12434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12434 raw12434Labels permutation641 permutation4
    _ = mixedMoment B node3978 node3978Labels := by rfl

theorem canonical12435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12435 raw12435Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw12435 raw12435Labels = mixedMoment B raw12435step0 raw12435step0Labels := by
      have hz : ∀ j, raw12435 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12435step0 = (fun i j => raw12435 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12435step0 raw12435; decide +kernel
      have hl : raw12435step0Labels = raw12435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12435 raw12435Labels permutation265 hz
    mixedMoment B raw12435step0 raw12435step0Labels = mixedMoment B raw12435step1 raw12435step1Labels := by
      have ha : raw12435step1 = (fun i j => raw12435step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12435step1 raw12435step0; decide +kernel
      have hl : raw12435step1Labels = raw12435step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12435step0 raw12435step0Labels permutation37 permutation2
    _ = mixedMoment B node3983 node3983Labels := by rfl

theorem canonical12436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12436 raw12436Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw12436 raw12436Labels = mixedMoment B raw12436step0 raw12436step0Labels := by
      have hz : ∀ j, raw12436 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12436step0 = (fun i j => raw12436 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12436step0 raw12436; decide +kernel
      have hl : raw12436step0Labels = raw12436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12436 raw12436Labels permutation265 hz
    mixedMoment B raw12436step0 raw12436step0Labels = mixedMoment B raw12436step1 raw12436step1Labels := by
      have ha : raw12436step1 = (fun i j => raw12436step0 (permutation82 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12436step1 raw12436step0; decide +kernel
      have hl : raw12436step1Labels = raw12436step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12436step0 raw12436step0Labels permutation82 permutation4
    mixedMoment B raw12436step1 raw12436step1Labels = mixedMoment B raw12436step2 raw12436step2Labels := by
      have ha : raw12436step2 = -raw12436step1 := by apply Matrix.ext; change ∀ i j, raw12436step2 i j = -(raw12436step1 i j); unfold raw12436step2 raw12436step1; decide +kernel
      have hl : raw12436step2Labels = raw12436step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

theorem canonical12437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12437 raw12437Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw12437 raw12437Labels = mixedMoment B raw12437step0 raw12437step0Labels := by
      have hz : ∀ j, raw12437 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12437step0 = (fun i j => raw12437 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12437step0 raw12437; decide +kernel
      have hl : raw12437step0Labels = raw12437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12437 raw12437Labels permutation265 hz
    mixedMoment B raw12437step0 raw12437step0Labels = mixedMoment B raw12437step1 raw12437step1Labels := by
      have ha : raw12437step1 = (fun i j => raw12437step0 (permutation135 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12437step1 raw12437step0; decide +kernel
      have hl : raw12437step1Labels = raw12437step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12437step0 raw12437step0Labels permutation135 permutation4
    _ = mixedMoment B node3983 node3983Labels := by rfl

theorem canonical12438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12438 raw12438Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw12438 raw12438Labels = mixedMoment B raw12438step0 raw12438step0Labels := by
      have hz : ∀ j, raw12438 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12438step0 = (fun i j => raw12438 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12438step0 raw12438; decide +kernel
      have hl : raw12438step0Labels = raw12438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12438 raw12438Labels permutation265 hz
    mixedMoment B raw12438step0 raw12438step0Labels = mixedMoment B raw12438step1 raw12438step1Labels := by
      have ha : raw12438step1 = (fun i j => raw12438step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12438step1 raw12438step0; decide +kernel
      have hl : raw12438step1Labels = raw12438step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12438step0 raw12438step0Labels permutation37 permutation2
    _ = mixedMoment B node4010 node4010Labels := by rfl

theorem canonical12439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12439 raw12439Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw12439 raw12439Labels = mixedMoment B raw12439step0 raw12439step0Labels := by
      have hz : ∀ j, raw12439 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12439step0 = (fun i j => raw12439 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12439step0 raw12439; decide +kernel
      have hl : raw12439step0Labels = raw12439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12439 raw12439Labels permutation265 hz
    mixedMoment B raw12439step0 raw12439step0Labels = mixedMoment B raw12439step1 raw12439step1Labels := by
      have ha : raw12439step1 = (fun i j => raw12439step0 (permutation92 i) (permutation0 j)) := by apply Matrix.ext; unfold raw12439step1 raw12439step0; decide +kernel
      have hl : raw12439step1Labels = raw12439step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12439step0 raw12439step0Labels permutation92 permutation0
    mixedMoment B raw12439step1 raw12439step1Labels = mixedMoment B raw12439step2 raw12439step2Labels := by
      have ha : raw12439step2 = -raw12439step1 := by apply Matrix.ext; change ∀ i j, raw12439step2 i j = -(raw12439step1 i j); unfold raw12439step2 raw12439step1; decide +kernel
      have hl : raw12439step2Labels = raw12439step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical12440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12440 raw12440Labels = mixedMoment B node1403 node1403Labels := by
  calc
    mixedMoment B raw12440 raw12440Labels = mixedMoment B raw12440step0 raw12440step0Labels := by
      have ha : raw12440step0 = (fun i j => raw12440 (permutation195 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12440step0 raw12440; decide +kernel
      have hl : raw12440step0Labels = raw12440Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12440 raw12440Labels permutation195 permutation2
    _ = mixedMoment B node1403 node1403Labels := by rfl

theorem canonical12445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12445 raw12445Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw12445 raw12445Labels = mixedMoment B raw12445step0 raw12445step0Labels := by
      have ha : raw12445step0 = (fun i j => raw12445 (permutation195 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12445step0 raw12445; decide +kernel
      have hl : raw12445step0Labels = raw12445Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12445 raw12445Labels permutation195 permutation2
    _ = mixedMoment B node2951 node2951Labels := by rfl

theorem canonical12446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12446 raw12446Labels = mixedMoment B node3091 node3091Labels := by
  calc
    mixedMoment B raw12446 raw12446Labels = mixedMoment B raw12446step0 raw12446step0Labels := by
      have ha : raw12446step0 = (fun i j => raw12446 (permutation186 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12446step0 raw12446; decide +kernel
      have hl : raw12446step0Labels = raw12446Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12446 raw12446Labels permutation186 permutation2
    _ = mixedMoment B node3091 node3091Labels := by rfl

theorem canonical12447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12447 raw12447Labels = mixedMoment B node3084 node3084Labels := by
  calc
    mixedMoment B raw12447 raw12447Labels = mixedMoment B raw12447step0 raw12447step0Labels := by
      have ha : raw12447step0 = (fun i j => raw12447 (permutation192 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12447step0 raw12447; decide +kernel
      have hl : raw12447step0Labels = raw12447Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12447 raw12447Labels permutation192 permutation2
    _ = mixedMoment B node3084 node3084Labels := by rfl

theorem canonical12448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12448 raw12448Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw12448 raw12448Labels = mixedMoment B raw12448step0 raw12448step0Labels := by
      have ha : raw12448step0 = (fun i j => raw12448 (permutation195 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12448step0 raw12448; decide +kernel
      have hl : raw12448step0Labels = raw12448Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12448 raw12448Labels permutation195 permutation2
    _ = mixedMoment B node3074 node3074Labels := by rfl

theorem canonical12453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12453 raw12453Labels = mixedMoment B node3115 node3115Labels := by
  calc
    mixedMoment B raw12453 raw12453Labels = mixedMoment B raw12453step0 raw12453step0Labels := by
      have hz : ∀ j, raw12453 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12453step0 = (fun i j => raw12453 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12453step0 raw12453; decide +kernel
      have hl : raw12453step0Labels = raw12453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12453 raw12453Labels permutation265 hz
    mixedMoment B raw12453step0 raw12453step0Labels = mixedMoment B raw12453step1 raw12453step1Labels := by
      have ha : raw12453step1 = (fun i j => raw12453step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12453step1 raw12453step0; decide +kernel
      have hl : raw12453step1Labels = raw12453step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12453step0 raw12453step0Labels permutation39 permutation2
    _ = mixedMoment B node3115 node3115Labels := by rfl

theorem canonical12456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12456 raw12456Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw12456 raw12456Labels = mixedMoment B raw12456step0 raw12456step0Labels := by
      have hz : ∀ j, raw12456 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12456step0 = (fun i j => raw12456 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12456step0 raw12456; decide +kernel
      have hl : raw12456step0Labels = raw12456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12456 raw12456Labels permutation265 hz
    mixedMoment B raw12456step0 raw12456step0Labels = mixedMoment B raw12456step1 raw12456step1Labels := by
      have ha : raw12456step1 = (fun i j => raw12456step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12456step1 raw12456step0; decide +kernel
      have hl : raw12456step1Labels = raw12456step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12456step0 raw12456step0Labels permutation37 permutation2
    _ = mixedMoment B node2954 node2954Labels := by rfl

theorem canonical12457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12457 raw12457Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw12457 raw12457Labels = mixedMoment B raw12457step0 raw12457step0Labels := by
      have hz : ∀ j, raw12457 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12457step0 = (fun i j => raw12457 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12457step0 raw12457; decide +kernel
      have hl : raw12457step0Labels = raw12457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12457 raw12457Labels permutation265 hz
    mixedMoment B raw12457step0 raw12457step0Labels = mixedMoment B raw12457step1 raw12457step1Labels := by
      have ha : raw12457step1 = (fun i j => raw12457step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12457step1 raw12457step0; decide +kernel
      have hl : raw12457step1Labels = raw12457step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12457step0 raw12457step0Labels permutation36 permutation2
    _ = mixedMoment B node2955 node2955Labels := by rfl

theorem canonical12458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12458 raw12458Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw12458 raw12458Labels = mixedMoment B raw12458step0 raw12458step0Labels := by
      have hz : ∀ j, raw12458 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12458step0 = (fun i j => raw12458 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12458step0 raw12458; decide +kernel
      have hl : raw12458step0Labels = raw12458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12458 raw12458Labels permutation265 hz
    mixedMoment B raw12458step0 raw12458step0Labels = mixedMoment B raw12458step1 raw12458step1Labels := by
      have ha : raw12458step1 = (fun i j => raw12458step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12458step1 raw12458step0; decide +kernel
      have hl : raw12458step1Labels = raw12458step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12458step0 raw12458step0Labels permutation34 permutation2
    _ = mixedMoment B node2964 node2964Labels := by rfl

theorem canonical12459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12459 raw12459Labels = mixedMoment B node3092 node3092Labels := by
  calc
    mixedMoment B raw12459 raw12459Labels = mixedMoment B raw12459step0 raw12459step0Labels := by
      have hz : ∀ j, raw12459 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12459step0 = (fun i j => raw12459 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12459step0 raw12459; decide +kernel
      have hl : raw12459step0Labels = raw12459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12459 raw12459Labels permutation265 hz
    mixedMoment B raw12459step0 raw12459step0Labels = mixedMoment B raw12459step1 raw12459step1Labels := by
      have ha : raw12459step1 = (fun i j => raw12459step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12459step1 raw12459step0; decide +kernel
      have hl : raw12459step1Labels = raw12459step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12459step0 raw12459step0Labels permutation33 permutation2
    _ = mixedMoment B node3092 node3092Labels := by rfl

theorem canonical12460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12460 raw12460Labels = mixedMoment B node2942 node2942Labels := by
  calc
    mixedMoment B raw12460 raw12460Labels = mixedMoment B raw12460step0 raw12460step0Labels := by
      have hz : ∀ j, raw12460 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12460step0 = (fun i j => raw12460 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12460step0 raw12460; decide +kernel
      have hl : raw12460step0Labels = raw12460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12460 raw12460Labels permutation265 hz
    mixedMoment B raw12460step0 raw12460step0Labels = mixedMoment B raw12460step1 raw12460step1Labels := by
      have ha : raw12460step1 = (fun i j => raw12460step0 (permutation138 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12460step1 raw12460step0; decide +kernel
      have hl : raw12460step1Labels = raw12460step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12460step0 raw12460step0Labels permutation138 permutation4
    _ = mixedMoment B node2942 node2942Labels := by rfl

theorem canonical12513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12513 raw12513Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw12513 raw12513Labels = mixedMoment B raw12513step0 raw12513step0Labels := by
      have hz : ∀ j, raw12513 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12513step0 = (fun i j => raw12513 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12513step0 raw12513; decide +kernel
      have hl : raw12513step0Labels = raw12513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12513 raw12513Labels permutation265 hz
    mixedMoment B raw12513step0 raw12513step0Labels = mixedMoment B raw12513step1 raw12513step1Labels := by
      have ha : raw12513step1 = (fun i j => raw12513step0 (permutation97 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12513step1 raw12513step0; decide +kernel
      have hl : raw12513step1Labels = raw12513step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12513step0 raw12513step0Labels permutation97 permutation2
    _ = mixedMoment B node2952 node2952Labels := by rfl

theorem canonical12514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12514 raw12514Labels = mixedMoment B node3507 node3507Labels := by
  calc
    mixedMoment B raw12514 raw12514Labels = mixedMoment B raw12514step0 raw12514step0Labels := by
      have hz : ∀ j, raw12514 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12514step0 = (fun i j => raw12514 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12514step0 raw12514; decide +kernel
      have hl : raw12514step0Labels = raw12514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12514 raw12514Labels permutation265 hz
    mixedMoment B raw12514step0 raw12514step0Labels = mixedMoment B raw12514step1 raw12514step1Labels := by
      have ha : raw12514step1 = (fun i j => raw12514step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12514step1 raw12514step0; decide +kernel
      have hl : raw12514step1Labels = raw12514step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12514step0 raw12514step0Labels permutation36 permutation2
    mixedMoment B raw12514step1 raw12514step1Labels = mixedMoment B raw12514step2 raw12514step2Labels := by
      have ha : raw12514step2 = -raw12514step1 := by apply Matrix.ext; change ∀ i j, raw12514step2 i j = -(raw12514step1 i j); unfold raw12514step2 raw12514step1; decide +kernel
      have hl : raw12514step2Labels = raw12514step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3507 node3507Labels := by rfl

theorem canonical12515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12515 raw12515Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw12515 raw12515Labels = mixedMoment B raw12515step0 raw12515step0Labels := by
      have hz : ∀ j, raw12515 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12515step0 = (fun i j => raw12515 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12515step0 raw12515; decide +kernel
      have hl : raw12515step0Labels = raw12515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12515 raw12515Labels permutation265 hz
    mixedMoment B raw12515step0 raw12515step0Labels = mixedMoment B raw12515step1 raw12515step1Labels := by
      have ha : raw12515step1 = (fun i j => raw12515step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12515step1 raw12515step0; decide +kernel
      have hl : raw12515step1Labels = raw12515step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12515step0 raw12515step0Labels permutation37 permutation2
    mixedMoment B raw12515step1 raw12515step1Labels = mixedMoment B raw12515step2 raw12515step2Labels := by
      have ha : raw12515step2 = -raw12515step1 := by apply Matrix.ext; change ∀ i j, raw12515step2 i j = -(raw12515step1 i j); unfold raw12515step2 raw12515step1; decide +kernel
      have hl : raw12515step2Labels = raw12515step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical12516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12516 raw12516Labels = mixedMoment B node2088 node2088Labels := by
  calc
    mixedMoment B raw12516 raw12516Labels = mixedMoment B raw12516step0 raw12516step0Labels := by
      have ha : raw12516step0 = (fun i j => raw12516 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12516step0 raw12516; decide +kernel
      have hl : raw12516step0Labels = raw12516Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12516 raw12516Labels permutation212 permutation4
    mixedMoment B raw12516step0 raw12516step0Labels = mixedMoment B raw12516step1 raw12516step1Labels := by
      have ha : raw12516step1 = -raw12516step0 := by apply Matrix.ext; change ∀ i j, raw12516step1 i j = -(raw12516step0 i j); unfold raw12516step1 raw12516step0; decide +kernel
      have hl : raw12516step1Labels = raw12516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2088 node2088Labels := by rfl

theorem canonical12517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12517 raw12517Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw12517 raw12517Labels = mixedMoment B raw12517step0 raw12517step0Labels := by
      have hz : ∀ j, raw12517 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12517step0 = (fun i j => raw12517 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12517step0 raw12517; decide +kernel
      have hl : raw12517step0Labels = raw12517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12517 raw12517Labels permutation346 hz
    mixedMoment B raw12517step0 raw12517step0Labels = mixedMoment B raw12517step1 raw12517step1Labels := by
      have ha : raw12517step1 = (fun i j => raw12517step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12517step1 raw12517step0; decide +kernel
      have hl : raw12517step1Labels = raw12517step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12517step0 raw12517step0Labels permutation40 permutation4
    mixedMoment B raw12517step1 raw12517step1Labels = mixedMoment B raw12517step2 raw12517step2Labels := by
      have ha : raw12517step2 = -raw12517step1 := by apply Matrix.ext; change ∀ i j, raw12517step2 i j = -(raw12517step1 i j); unfold raw12517step2 raw12517step1; decide +kernel
      have hl : raw12517step2Labels = raw12517step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical12518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12518 raw12518Labels = mixedMoment B node2950 node2950Labels := by
  calc
    mixedMoment B raw12518 raw12518Labels = mixedMoment B raw12518step0 raw12518step0Labels := by
      have ha : raw12518step0 = (fun i j => raw12518 (permutation502 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12518step0 raw12518; decide +kernel
      have hl : raw12518step0Labels = raw12518Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12518 raw12518Labels permutation502 permutation2
    _ = mixedMoment B node2950 node2950Labels := by rfl

theorem canonical12519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12519 raw12519Labels = mixedMoment B node3550 node3550Labels := by
  calc
    mixedMoment B raw12519 raw12519Labels = mixedMoment B raw12519step0 raw12519step0Labels := by
      have ha : raw12519step0 = (fun i j => raw12519 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12519step0 raw12519; decide +kernel
      have hl : raw12519step0Labels = raw12519Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12519 raw12519Labels permutation212 permutation4
    mixedMoment B raw12519step0 raw12519step0Labels = mixedMoment B raw12519step1 raw12519step1Labels := by
      have ha : raw12519step1 = -raw12519step0 := by apply Matrix.ext; change ∀ i j, raw12519step1 i j = -(raw12519step0 i j); unfold raw12519step1 raw12519step0; decide +kernel
      have hl : raw12519step1Labels = raw12519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3550 node3550Labels := by rfl

theorem canonical12520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12520 raw12520Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw12520 raw12520Labels = mixedMoment B raw12520step0 raw12520step0Labels := by
      have ha : raw12520step0 = (fun i j => raw12520 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12520step0 raw12520; decide +kernel
      have hl : raw12520step0Labels = raw12520Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12520 raw12520Labels permutation212 permutation4
    mixedMoment B raw12520step0 raw12520step0Labels = mixedMoment B raw12520step1 raw12520step1Labels := by
      have ha : raw12520step1 = -raw12520step0 := by apply Matrix.ext; change ∀ i j, raw12520step1 i j = -(raw12520step0 i j); unfold raw12520step1 raw12520step0; decide +kernel
      have hl : raw12520step1Labels = raw12520step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3571 node3571Labels := by rfl

theorem canonical12521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12521 raw12521Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw12521 raw12521Labels = mixedMoment B raw12521step0 raw12521step0Labels := by
      have hz : ∀ j, raw12521 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12521step0 = (fun i j => raw12521 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12521step0 raw12521; decide +kernel
      have hl : raw12521step0Labels = raw12521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12521 raw12521Labels permutation265 hz
    mixedMoment B raw12521step0 raw12521step0Labels = mixedMoment B raw12521step1 raw12521step1Labels := by
      have ha : raw12521step1 = (fun i j => raw12521step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12521step1 raw12521step0; decide +kernel
      have hl : raw12521step1Labels = raw12521step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12521step0 raw12521step0Labels permutation40 permutation4
    mixedMoment B raw12521step1 raw12521step1Labels = mixedMoment B raw12521step2 raw12521step2Labels := by
      have ha : raw12521step2 = -raw12521step1 := by apply Matrix.ext; change ∀ i j, raw12521step2 i j = -(raw12521step1 i j); unfold raw12521step2 raw12521step1; decide +kernel
      have hl : raw12521step2Labels = raw12521step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2094 node2094Labels := by rfl

theorem canonical12522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12522 raw12522Labels = mixedMoment B node2956 node2956Labels := by
  calc
    mixedMoment B raw12522 raw12522Labels = mixedMoment B raw12522step0 raw12522step0Labels := by
      have hz : ∀ j, raw12522 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12522step0 = (fun i j => raw12522 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12522step0 raw12522; decide +kernel
      have hl : raw12522step0Labels = raw12522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12522 raw12522Labels permutation265 hz
    mixedMoment B raw12522step0 raw12522step0Labels = mixedMoment B raw12522step1 raw12522step1Labels := by
      have ha : raw12522step1 = (fun i j => raw12522step0 (permutation96 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12522step1 raw12522step0; decide +kernel
      have hl : raw12522step1Labels = raw12522step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12522step0 raw12522step0Labels permutation96 permutation2
    _ = mixedMoment B node2956 node2956Labels := by rfl

theorem canonical12523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12523 raw12523Labels = mixedMoment B node3552 node3552Labels := by
  calc
    mixedMoment B raw12523 raw12523Labels = mixedMoment B raw12523step0 raw12523step0Labels := by
      have hz : ∀ j, raw12523 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12523step0 = (fun i j => raw12523 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12523step0 raw12523; decide +kernel
      have hl : raw12523step0Labels = raw12523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12523 raw12523Labels permutation265 hz
    mixedMoment B raw12523step0 raw12523step0Labels = mixedMoment B raw12523step1 raw12523step1Labels := by
      have ha : raw12523step1 = (fun i j => raw12523step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12523step1 raw12523step0; decide +kernel
      have hl : raw12523step1Labels = raw12523step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12523step0 raw12523step0Labels permutation40 permutation4
    mixedMoment B raw12523step1 raw12523step1Labels = mixedMoment B raw12523step2 raw12523step2Labels := by
      have ha : raw12523step2 = -raw12523step1 := by apply Matrix.ext; change ∀ i j, raw12523step2 i j = -(raw12523step1 i j); unfold raw12523step2 raw12523step1; decide +kernel
      have hl : raw12523step2Labels = raw12523step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3552 node3552Labels := by rfl

theorem canonical12524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12524 raw12524Labels = mixedMoment B node3096 node3096Labels := by
  calc
    mixedMoment B raw12524 raw12524Labels = mixedMoment B raw12524step0 raw12524step0Labels := by
      have hz : ∀ j, raw12524 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12524step0 = (fun i j => raw12524 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12524step0 raw12524; decide +kernel
      have hl : raw12524step0Labels = raw12524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12524 raw12524Labels permutation265 hz
    mixedMoment B raw12524step0 raw12524step0Labels = mixedMoment B raw12524step1 raw12524step1Labels := by
      have ha : raw12524step1 = (fun i j => raw12524step0 (permutation97 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12524step1 raw12524step0; decide +kernel
      have hl : raw12524step1Labels = raw12524step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12524step0 raw12524step0Labels permutation97 permutation2
    _ = mixedMoment B node3096 node3096Labels := by rfl

theorem canonical12525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12525 raw12525Labels = mixedMoment B node2962 node2962Labels := by
  calc
    mixedMoment B raw12525 raw12525Labels = mixedMoment B raw12525step0 raw12525step0Labels := by
      have hz : ∀ j, raw12525 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12525step0 = (fun i j => raw12525 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12525step0 raw12525; decide +kernel
      have hl : raw12525step0Labels = raw12525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12525 raw12525Labels permutation265 hz
    mixedMoment B raw12525step0 raw12525step0Labels = mixedMoment B raw12525step1 raw12525step1Labels := by
      have ha : raw12525step1 = (fun i j => raw12525step0 (permutation94 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12525step1 raw12525step0; decide +kernel
      have hl : raw12525step1Labels = raw12525step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12525step0 raw12525step0Labels permutation94 permutation2
    _ = mixedMoment B node2962 node2962Labels := by rfl

theorem canonical12526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12526 raw12526Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw12526 raw12526Labels = mixedMoment B raw12526step0 raw12526step0Labels := by
      have hz : ∀ j, raw12526 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12526step0 = (fun i j => raw12526 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12526step0 raw12526; decide +kernel
      have hl : raw12526step0Labels = raw12526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12526 raw12526Labels permutation265 hz
    mixedMoment B raw12526step0 raw12526step0Labels = mixedMoment B raw12526step1 raw12526step1Labels := by
      have ha : raw12526step1 = (fun i j => raw12526step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12526step1 raw12526step0; decide +kernel
      have hl : raw12526step1Labels = raw12526step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12526step0 raw12526step0Labels permutation38 permutation4
    mixedMoment B raw12526step1 raw12526step1Labels = mixedMoment B raw12526step2 raw12526step2Labels := by
      have ha : raw12526step2 = -raw12526step1 := by apply Matrix.ext; change ∀ i j, raw12526step2 i j = -(raw12526step1 i j); unfold raw12526step2 raw12526step1; decide +kernel
      have hl : raw12526step2Labels = raw12526step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2107 node2107Labels := by rfl

theorem canonical12527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12527 raw12527Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw12527 raw12527Labels = mixedMoment B raw12527step0 raw12527step0Labels := by
      have hz : ∀ j, raw12527 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12527step0 = (fun i j => raw12527 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12527step0 raw12527; decide +kernel
      have hl : raw12527step0Labels = raw12527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12527 raw12527Labels permutation346 hz
    mixedMoment B raw12527step0 raw12527step0Labels = mixedMoment B raw12527step1 raw12527step1Labels := by
      have hz : ∀ j, raw12527step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12527step1 = (fun i j => raw12527step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12527step1 raw12527step0; decide +kernel
      have hl : raw12527step1Labels = raw12527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12527step0 raw12527step0Labels permutation56 hz
    mixedMoment B raw12527step1 raw12527step1Labels = mixedMoment B raw12527step2 raw12527step2Labels := by
      have ha : raw12527step2 = (fun i j => raw12527step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12527step2 raw12527step1; decide +kernel
      have hl : raw12527step2Labels = raw12527step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12527step1 raw12527step1Labels permutation8 permutation4
    mixedMoment B raw12527step2 raw12527step2Labels = mixedMoment B raw12527step3 raw12527step3Labels := by
      have ha : raw12527step3 = -raw12527step2 := by apply Matrix.ext; change ∀ i j, raw12527step3 i j = -(raw12527step2 i j); unfold raw12527step3 raw12527step2; decide +kernel
      have hl : raw12527step3Labels = raw12527step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3583 node3583Labels := by rfl

theorem canonical12528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12528 raw12528Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw12528 raw12528Labels = mixedMoment B raw12528step0 raw12528step0Labels := by
      have hz : ∀ j, raw12528 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12528step0 = (fun i j => raw12528 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12528step0 raw12528; decide +kernel
      have hl : raw12528step0Labels = raw12528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12528 raw12528Labels permutation265 hz
    mixedMoment B raw12528step0 raw12528step0Labels = mixedMoment B raw12528step1 raw12528step1Labels := by
      have ha : raw12528step1 = (fun i j => raw12528step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12528step1 raw12528step0; decide +kernel
      have hl : raw12528step1Labels = raw12528step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12528step0 raw12528step0Labels permutation38 permutation4
    mixedMoment B raw12528step1 raw12528step1Labels = mixedMoment B raw12528step2 raw12528step2Labels := by
      have ha : raw12528step2 = -raw12528step1 := by apply Matrix.ext; change ∀ i j, raw12528step2 i j = -(raw12528step1 i j); unfold raw12528step2 raw12528step1; decide +kernel
      have hl : raw12528step2Labels = raw12528step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3581 node3581Labels := by rfl

theorem canonical12529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12529 raw12529Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw12529 raw12529Labels = mixedMoment B raw12529step0 raw12529step0Labels := by
      have hz : ∀ j, raw12529 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12529step0 = (fun i j => raw12529 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12529step0 raw12529; decide +kernel
      have hl : raw12529step0Labels = raw12529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12529 raw12529Labels permutation265 hz
    mixedMoment B raw12529step0 raw12529step0Labels = mixedMoment B raw12529step1 raw12529step1Labels := by
      have ha : raw12529step1 = (fun i j => raw12529step0 (permutation46 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12529step1 raw12529step0; decide +kernel
      have hl : raw12529step1Labels = raw12529step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12529step0 raw12529step0Labels permutation46 permutation4
    mixedMoment B raw12529step1 raw12529step1Labels = mixedMoment B raw12529step2 raw12529step2Labels := by
      have ha : raw12529step2 = -raw12529step1 := by apply Matrix.ext; change ∀ i j, raw12529step2 i j = -(raw12529step1 i j); unfold raw12529step2 raw12529step1; decide +kernel
      have hl : raw12529step2Labels = raw12529step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical12530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12530 raw12530Labels = mixedMoment B node2995 node2995Labels := by
  calc
    mixedMoment B raw12530 raw12530Labels = mixedMoment B raw12530step0 raw12530step0Labels := by
      have hz : ∀ j, raw12530 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12530step0 = (fun i j => raw12530 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12530step0 raw12530; decide +kernel
      have hl : raw12530step0Labels = raw12530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12530 raw12530Labels permutation265 hz
    mixedMoment B raw12530step0 raw12530step0Labels = mixedMoment B raw12530step1 raw12530step1Labels := by
      have ha : raw12530step1 = (fun i j => raw12530step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12530step1 raw12530step0; decide +kernel
      have hl : raw12530step1Labels = raw12530step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12530step0 raw12530step0Labels permutation137 permutation4
    _ = mixedMoment B node2995 node2995Labels := by rfl

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

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ac_rfl

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

theorem singleton5284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5284 node5284Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3077 node3077Labels + mixedMoment B node3625 node3625Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2289 singletonSmall5284
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5284) = raw2289Labels := by decide +kernel
  rw [hl, canonical2289 B hB] at h
  have hc0 : mixedMoment B raw2289 (Fin.cases (0 : Fin 2) singletonSmall5284) =
      mixedMoment B node3077 node3077Labels := by
    have ha : raw2289 = raw2290 := by apply Matrix.ext; unfold raw2289 raw2290; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5284 = raw2290Labels := by decide +kernel
    rw [ha, hj, canonical2290 B hB]
  have hc1 : mixedMoment B raw2289 (Fin.cases (1 : Fin 2) singletonSmall5284) =
      mixedMoment B node3625 node3625Labels := by
    have ha : raw2289 = raw2291 := by apply Matrix.ext; unfold raw2289 raw2291; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5284 = raw2291Labels := by decide +kernel
    rw [ha, hj, canonical2291 B hB]
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

theorem singleton5438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5438 node5438Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3857 node3857Labels + mixedMoment B node3876 node3876Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2538 singletonSmall5438
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5438) = raw2538Labels := by decide +kernel
  rw [hl, canonical2538 B hB] at h
  have hc0 : mixedMoment B raw2538 (Fin.cases (0 : Fin 2) singletonSmall5438) =
      mixedMoment B node3857 node3857Labels := by
    have ha : raw2538 = raw2539 := by apply Matrix.ext; unfold raw2538 raw2539; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5438 = raw2539Labels := by decide +kernel
    rw [ha, hj, canonical2539 B hB]
  have hc1 : mixedMoment B raw2538 (Fin.cases (1 : Fin 2) singletonSmall5438) =
      mixedMoment B node3876 node3876Labels := by
    have ha : raw2538 = raw2540 := by apply Matrix.ext; unfold raw2538 raw2540; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5438 = raw2540Labels := by decide +kernel
    rw [ha, hj, canonical2540 B hB]
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

theorem singleton5484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5484 node5484Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3983 node3983Labels + mixedMoment B node3983 node3983Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2607 singletonSmall5484
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5484) = raw2607Labels := by decide +kernel
  rw [hl, canonical2607 B hB] at h
  have hc0 : mixedMoment B raw2607 (Fin.cases (0 : Fin 2) singletonSmall5484) =
      mixedMoment B node3983 node3983Labels := by
    have ha : raw2607 = raw2608 := by apply Matrix.ext; unfold raw2607 raw2608; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5484 = raw2608Labels := by decide +kernel
    rw [ha, hj, canonical2608 B hB]
  have hc1 : mixedMoment B raw2607 (Fin.cases (1 : Fin 2) singletonSmall5484) =
      mixedMoment B node3983 node3983Labels := by
    have ha : raw2607 = raw2609 := by apply Matrix.ext; unfold raw2607 raw2609; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5484 = raw2609Labels := by decide +kernel
    rw [ha, hj, canonical2609 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound1291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1291 node1291Labels = Sparse.eval nodeValue1291 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1291) = mixedMoment B node1291 node1291Labels := rfl
  simpa [nodeValue1291, Sparse.eval] using hc.symm

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

theorem sound1403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1403 node1403Labels = Sparse.eval nodeValue1403 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1403) = mixedMoment B node1403 node1403Labels := rfl
  simpa [nodeValue1403, Sparse.eval] using hc.symm

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

theorem sound2088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2088 node2088Labels = Sparse.eval nodeValue2088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2088) = mixedMoment B node2088 node2088Labels := rfl
  simpa [nodeValue2088, Sparse.eval] using hc.symm

theorem sound2094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2094 node2094Labels = Sparse.eval nodeValue2094 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2094) = mixedMoment B node2094 node2094Labels := rfl
  simpa [nodeValue2094, Sparse.eval] using hc.symm

theorem sound2107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2107 node2107Labels = Sparse.eval nodeValue2107 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2107) = mixedMoment B node2107 node2107Labels := rfl
  simpa [nodeValue2107, Sparse.eval] using hc.symm

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

theorem sound2587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2587 node2587Labels = Sparse.eval nodeValue2587 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2587) = mixedMoment B node2587 node2587Labels := rfl
  simpa [nodeValue2587, Sparse.eval] using hc.symm

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

theorem sound2630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2630 node2630Labels = Sparse.eval nodeValue2630 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2630) = mixedMoment B node2630 node2630Labels := rfl
  simpa [nodeValue2630, Sparse.eval] using hc.symm

theorem sound2632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2632 node2632Labels = Sparse.eval nodeValue2632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2632) = mixedMoment B node2632 node2632Labels := rfl
  simpa [nodeValue2632, Sparse.eval] using hc.symm

theorem sound2634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2634 node2634Labels = Sparse.eval nodeValue2634 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2634) = mixedMoment B node2634 node2634Labels := rfl
  simpa [nodeValue2634, Sparse.eval] using hc.symm

theorem sound2639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2639 node2639Labels = Sparse.eval nodeValue2639 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2639) = mixedMoment B node2639 node2639Labels := rfl
  simpa [nodeValue2639, Sparse.eval] using hc.symm

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

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

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

theorem sound2763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2763 node2763Labels = Sparse.eval nodeValue2763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2763) = mixedMoment B node2763 node2763Labels := rfl
  simpa [nodeValue2763, Sparse.eval] using hc.symm

theorem sound2773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2773 node2773Labels = Sparse.eval nodeValue2773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2773) = mixedMoment B node2773 node2773Labels := rfl
  simpa [nodeValue2773, Sparse.eval] using hc.symm

theorem sound2782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2782 node2782Labels = Sparse.eval nodeValue2782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2782) = mixedMoment B node2782 node2782Labels := rfl
  simpa [nodeValue2782, Sparse.eval] using hc.symm

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

theorem sound2942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2942 node2942Labels = Sparse.eval nodeValue2942 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2942) = mixedMoment B node2942 node2942Labels := rfl
  simpa [nodeValue2942, Sparse.eval] using hc.symm

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

theorem sound2950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2950 node2950Labels = Sparse.eval nodeValue2950 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2950) = mixedMoment B node2950 node2950Labels := rfl
  simpa [nodeValue2950, Sparse.eval] using hc.symm

theorem sound2951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2951 node2951Labels = Sparse.eval nodeValue2951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2951) = mixedMoment B node2951 node2951Labels := rfl
  simpa [nodeValue2951, Sparse.eval] using hc.symm

theorem sound2952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2952 node2952Labels = Sparse.eval nodeValue2952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2952) = mixedMoment B node2952 node2952Labels := rfl
  simpa [nodeValue2952, Sparse.eval] using hc.symm

theorem sound2954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2954 node2954Labels = Sparse.eval nodeValue2954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2954) = mixedMoment B node2954 node2954Labels := rfl
  simpa [nodeValue2954, Sparse.eval] using hc.symm

theorem sound2955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2955 node2955Labels = Sparse.eval nodeValue2955 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2955) = mixedMoment B node2955 node2955Labels := rfl
  simpa [nodeValue2955, Sparse.eval] using hc.symm

theorem sound2956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2956 node2956Labels = Sparse.eval nodeValue2956 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2956) = mixedMoment B node2956 node2956Labels := rfl
  simpa [nodeValue2956, Sparse.eval] using hc.symm

theorem sound2962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2962 node2962Labels = Sparse.eval nodeValue2962 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2962) = mixedMoment B node2962 node2962Labels := rfl
  simpa [nodeValue2962, Sparse.eval] using hc.symm

theorem sound2964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2964 node2964Labels = Sparse.eval nodeValue2964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2964) = mixedMoment B node2964 node2964Labels := rfl
  simpa [nodeValue2964, Sparse.eval] using hc.symm

theorem sound2995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2995 node2995Labels = Sparse.eval nodeValue2995 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2995) = mixedMoment B node2995 node2995Labels := rfl
  simpa [nodeValue2995, Sparse.eval] using hc.symm

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

theorem sound3074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3074 node3074Labels = Sparse.eval nodeValue3074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3074) = mixedMoment B node3074 node3074Labels := rfl
  simpa [nodeValue3074, Sparse.eval] using hc.symm

theorem sound3077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3077 node3077Labels = Sparse.eval nodeValue3077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3077) = mixedMoment B node3077 node3077Labels := rfl
  simpa [nodeValue3077, Sparse.eval] using hc.symm

theorem sound3084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3084 node3084Labels = Sparse.eval nodeValue3084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3084) = mixedMoment B node3084 node3084Labels := rfl
  simpa [nodeValue3084, Sparse.eval] using hc.symm

theorem sound3091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3091 node3091Labels = Sparse.eval nodeValue3091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3091) = mixedMoment B node3091 node3091Labels := rfl
  simpa [nodeValue3091, Sparse.eval] using hc.symm

theorem sound3092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3092 node3092Labels = Sparse.eval nodeValue3092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3092) = mixedMoment B node3092 node3092Labels := rfl
  simpa [nodeValue3092, Sparse.eval] using hc.symm

theorem sound3096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3096 node3096Labels = Sparse.eval nodeValue3096 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3096) = mixedMoment B node3096 node3096Labels := rfl
  simpa [nodeValue3096, Sparse.eval] using hc.symm

theorem sound3097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3097 node3097Labels = Sparse.eval nodeValue3097 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3097) = mixedMoment B node3097 node3097Labels := rfl
  simpa [nodeValue3097, Sparse.eval] using hc.symm

theorem sound3115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3115 node3115Labels = Sparse.eval nodeValue3115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3115) = mixedMoment B node3115 node3115Labels := rfl
  simpa [nodeValue3115, Sparse.eval] using hc.symm

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

theorem sound3500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3500 node3500Labels = Sparse.eval nodeValue3500 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3500) = mixedMoment B node3500 node3500Labels := rfl
  simpa [nodeValue3500, Sparse.eval] using hc.symm

theorem sound3503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3503 node3503Labels = Sparse.eval nodeValue3503 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3503) = mixedMoment B node3503 node3503Labels := rfl
  simpa [nodeValue3503, Sparse.eval] using hc.symm

theorem sound3507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3507 node3507Labels = Sparse.eval nodeValue3507 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3507) = mixedMoment B node3507 node3507Labels := rfl
  simpa [nodeValue3507, Sparse.eval] using hc.symm

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

theorem sound3550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3550 node3550Labels = Sparse.eval nodeValue3550 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3550) = mixedMoment B node3550 node3550Labels := rfl
  simpa [nodeValue3550, Sparse.eval] using hc.symm

theorem sound3552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3552 node3552Labels = Sparse.eval nodeValue3552 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3552) = mixedMoment B node3552 node3552Labels := rfl
  simpa [nodeValue3552, Sparse.eval] using hc.symm

theorem sound3571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3571 node3571Labels = Sparse.eval nodeValue3571 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3571) = mixedMoment B node3571 node3571Labels := rfl
  simpa [nodeValue3571, Sparse.eval] using hc.symm

theorem sound3572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3572 node3572Labels = Sparse.eval nodeValue3572 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3572) = mixedMoment B node3572 node3572Labels := rfl
  simpa [nodeValue3572, Sparse.eval] using hc.symm

theorem sound3573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3573 node3573Labels = Sparse.eval nodeValue3573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3573) = mixedMoment B node3573 node3573Labels := rfl
  simpa [nodeValue3573, Sparse.eval] using hc.symm

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

theorem sound3583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3583 node3583Labels = Sparse.eval nodeValue3583 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3583) = mixedMoment B node3583 node3583Labels := rfl
  simpa [nodeValue3583, Sparse.eval] using hc.symm

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

theorem sound3606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3606 node3606Labels = Sparse.eval nodeValue3606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3606) = mixedMoment B node3606 node3606Labels := rfl
  simpa [nodeValue3606, Sparse.eval] using hc.symm

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

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

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

theorem sound3884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3884 node3884Labels = Sparse.eval nodeValue3884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3884) = mixedMoment B node3884 node3884Labels := rfl
  simpa [nodeValue3884, Sparse.eval] using hc.symm

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

theorem sound3978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3978 node3978Labels = Sparse.eval nodeValue3978 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3978) = mixedMoment B node3978 node3978Labels := rfl
  simpa [nodeValue3978, Sparse.eval] using hc.symm

theorem sound3983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3983 node3983Labels = Sparse.eval nodeValue3983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3983) = mixedMoment B node3983 node3983Labels := rfl
  simpa [nodeValue3983, Sparse.eval] using hc.symm

theorem sound4010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4010 node4010Labels = Sparse.eval nodeValue4010 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4010) = mixedMoment B node4010 node4010Labels := rfl
  simpa [nodeValue4010, Sparse.eval] using hc.symm

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

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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

theorem sound4449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4449 node4449Labels = Sparse.eval nodeValue4449 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4449) = mixedMoment B node4449 node4449Labels := rfl
  simpa [nodeValue4449, Sparse.eval] using hc.symm

theorem sound4450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4450 node4450Labels = Sparse.eval nodeValue4450 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4450) = mixedMoment B node4450 node4450Labels := rfl
  simpa [nodeValue4450, Sparse.eval] using hc.symm

theorem sound4453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4453 node4453Labels = Sparse.eval nodeValue4453 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4453) = mixedMoment B node4453 node4453Labels := rfl
  simpa [nodeValue4453, Sparse.eval] using hc.symm

theorem sound4459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4459 node4459Labels = Sparse.eval nodeValue4459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4459) = mixedMoment B node4459 node4459Labels := rfl
  simpa [nodeValue4459, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4487 node4487Labels = Sparse.eval nodeValue4487 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4487) = mixedMoment B node4487 node4487Labels := rfl
  simpa [nodeValue4487, Sparse.eval] using hc.symm

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

theorem sound5069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5069 node5069Labels = Sparse.eval nodeValue5069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5069) = mixedMoment B node5069 node5069Labels := rfl
  simpa [nodeValue5069, Sparse.eval] using hc.symm

theorem sound5071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5071 node5071Labels = Sparse.eval nodeValue5071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5071) = mixedMoment B node5071 node5071Labels := rfl
  simpa [nodeValue5071, Sparse.eval] using hc.symm

theorem sound5074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5074 node5074Labels = Sparse.eval nodeValue5074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5074) = mixedMoment B node5074 node5074Labels := rfl
  simpa [nodeValue5074, Sparse.eval] using hc.symm

theorem sound5092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5092 node5092Labels = Sparse.eval nodeValue5092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5092) = mixedMoment B node5092 node5092Labels := rfl
  simpa [nodeValue5092, Sparse.eval] using hc.symm

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

theorem sound5140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5140 node5140Labels = Sparse.eval nodeValue5140 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5140) = mixedMoment B node5140 node5140Labels := rfl
  simpa [nodeValue5140, Sparse.eval] using hc.symm

theorem sound5160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5160 node5160Labels = Sparse.eval nodeValue5160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5160) = mixedMoment B node5160 node5160Labels := rfl
  simpa [nodeValue5160, Sparse.eval] using hc.symm

theorem sound5161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5161 node5161Labels = Sparse.eval nodeValue5161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5161) = mixedMoment B node5161 node5161Labels := rfl
  simpa [nodeValue5161, Sparse.eval] using hc.symm

theorem sound5164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5164 node5164Labels = Sparse.eval nodeValue5164 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5164) = mixedMoment B node5164 node5164Labels := rfl
  simpa [nodeValue5164, Sparse.eval] using hc.symm

theorem sound5170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5170 node5170Labels = Sparse.eval nodeValue5170 (mixedVector B) := by
  have h := singleton5170 B _hB
  rw [sound2954 B _hB _hF, sound3606 B _hB _hF] at h
  norm_num [nodeValue5170, nodeValue2954, nodeValue3606, Sparse.eval] at h ⊢
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

theorem sound5226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5226 node5226Labels = Sparse.eval nodeValue5226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5226) = mixedMoment B node5226 node5226Labels := rfl
  simpa [nodeValue5226, Sparse.eval] using hc.symm

theorem sound5229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5229 node5229Labels = Sparse.eval nodeValue5229 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5229) = mixedMoment B node5229 node5229Labels := rfl
  simpa [nodeValue5229, Sparse.eval] using hc.symm

theorem sound5236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5236 node5236Labels = Sparse.eval nodeValue5236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5236) = mixedMoment B node5236 node5236Labels := rfl
  simpa [nodeValue5236, Sparse.eval] using hc.symm

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

theorem sound5255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5255 node5255Labels = Sparse.eval nodeValue5255 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5255) = mixedMoment B node5255 node5255Labels := rfl
  simpa [nodeValue5255, Sparse.eval] using hc.symm

theorem sound5260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5260 node5260Labels = Sparse.eval nodeValue5260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5260) = mixedMoment B node5260 node5260Labels := rfl
  simpa [nodeValue5260, Sparse.eval] using hc.symm

theorem sound5269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5269 node5269Labels = Sparse.eval nodeValue5269 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5269) = mixedMoment B node5269 node5269Labels := rfl
  simpa [nodeValue5269, Sparse.eval] using hc.symm

theorem sound5281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5281 node5281Labels = Sparse.eval nodeValue5281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5281) = mixedMoment B node5281 node5281Labels := rfl
  simpa [nodeValue5281, Sparse.eval] using hc.symm

theorem sound5282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5282 node5282Labels = Sparse.eval nodeValue5282 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5282) = mixedMoment B node5282 node5282Labels := rfl
  simpa [nodeValue5282, Sparse.eval] using hc.symm

theorem sound5284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5284 node5284Labels = Sparse.eval nodeValue5284 (mixedVector B) := by
  have h := singleton5284 B _hB
  rw [sound3077 B _hB _hF, sound3625 B _hB _hF] at h
  norm_num [nodeValue5284, nodeValue3077, nodeValue3625, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5289 node5289Labels = Sparse.eval nodeValue5289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5289) = mixedMoment B node5289 node5289Labels := rfl
  simpa [nodeValue5289, Sparse.eval] using hc.symm

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

theorem sound5438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5438 node5438Labels = Sparse.eval nodeValue5438 (mixedVector B) := by
  have h := singleton5438 B _hB
  rw [sound3857 B _hB _hF, sound3876 B _hB _hF] at h
  norm_num [nodeValue5438, nodeValue3857, nodeValue3876, Sparse.eval] at h ⊢
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

theorem sound5480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5480 node5480Labels = Sparse.eval nodeValue5480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5480) = mixedMoment B node5480 node5480Labels := rfl
  simpa [nodeValue5480, Sparse.eval] using hc.symm

theorem sound5484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5484 node5484Labels = Sparse.eval nodeValue5484 (mixedVector B) := by
  have h := singleton5484 B _hB
  rw [sound3983 B _hB _hF] at h
  norm_num [nodeValue5484, nodeValue3983, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources23
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq736 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm736 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA736 + difference 2 0) (sourceB736 + difference 0 2) sourceC736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA736 + difference 2 0) (sourceB736 + difference 0 2) sourceC736) = raw12328 := by
      apply Matrix.ext; unfold tripleCharges sourceA736 sourceB736 sourceC736 difference raw12328; decide +kernel
    rw [ha]
    exact (canonical12328 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA736 + difference 2 1) (sourceB736 + difference 1 2) sourceC736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2587) := by
    have ha : (tripleCharges (sourceA736 + difference 2 1) (sourceB736 + difference 1 2) sourceC736) = raw12332 := by
      apply Matrix.ext; unfold tripleCharges sourceA736 sourceB736 sourceC736 difference raw12332; decide +kernel
    rw [ha]
    exact (canonical12332 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA736 + difference 2 2) (sourceB736 + difference 2 2) sourceC736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA736 + difference 2 2) (sourceB736 + difference 2 2) sourceC736) = raw12320 := by
      apply Matrix.ext; unfold tripleCharges sourceA736 sourceB736 sourceC736 difference raw12320; decide +kernel
    rw [ha]
    exact (canonical12320 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA736 + difference 2 3) (sourceB736 + difference 3 2) sourceC736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA736 + difference 2 3) (sourceB736 + difference 3 2) sourceC736) = raw12336 := by
      apply Matrix.ext; unfold tripleCharges sourceA736 sourceB736 sourceC736 difference raw12336; decide +kernel
    rw [ha]
    exact (canonical12336 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA736 + difference 2 4) (sourceB736 + difference 4 2) sourceC736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA736 + difference 2 4) (sourceB736 + difference 4 2) sourceC736) = raw12337 := by
      apply Matrix.ext; unfold tripleCharges sourceA736 sourceB736 sourceC736 difference raw12337; decide +kernel
    rw [ha]
    exact (canonical12337 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA736 + difference 2 5) (sourceB736 + difference 5 2) sourceC736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA736 + difference 2 5) (sourceB736 + difference 5 2) sourceC736) = raw12338 := by
      apply Matrix.ext; unfold tripleCharges sourceA736 sourceB736 sourceC736 difference raw12338; decide +kernel
    rw [ha]
    exact (canonical12338 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA736 + sourceB736) sourceC736) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA736 + sourceB736) sourceC736) = raw12326 := by
      apply Matrix.ext; unfold doubleCharges sourceA736 sourceB736 sourceC736 raw12326; decide +kernel
    rw [ha]
    exact (canonical12326 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA736 sourceB736 sourceC736
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm736, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq737 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm737 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA737 + difference 0 2) (sourceB737 + difference 2 0) sourceC737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA737 + difference 0 2) (sourceB737 + difference 2 0) sourceC737) = raw12322 := by
      apply Matrix.ext; unfold tripleCharges sourceA737 sourceB737 sourceC737 difference raw12322; decide +kernel
    rw [ha]
    exact (canonical12322 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA737 + difference 1 2) (sourceB737 + difference 2 1) sourceC737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2630) := by
    have ha : (tripleCharges (sourceA737 + difference 1 2) (sourceB737 + difference 2 1) sourceC737) = raw12339 := by
      apply Matrix.ext; unfold tripleCharges sourceA737 sourceB737 sourceC737 difference raw12339; decide +kernel
    rw [ha]
    exact (canonical12339 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA737 + difference 2 2) (sourceB737 + difference 2 2) sourceC737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA737 + difference 2 2) (sourceB737 + difference 2 2) sourceC737) = raw12320 := by
      apply Matrix.ext; unfold tripleCharges sourceA737 sourceB737 sourceC737 difference raw12320; decide +kernel
    rw [ha]
    exact (canonical12320 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA737 + difference 3 2) (sourceB737 + difference 2 3) sourceC737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2639) := by
    have ha : (tripleCharges (sourceA737 + difference 3 2) (sourceB737 + difference 2 3) sourceC737) = raw12340 := by
      apply Matrix.ext; unfold tripleCharges sourceA737 sourceB737 sourceC737 difference raw12340; decide +kernel
    rw [ha]
    exact (canonical12340 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA737 + difference 4 2) (sourceB737 + difference 2 4) sourceC737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2634) := by
    have ha : (tripleCharges (sourceA737 + difference 4 2) (sourceB737 + difference 2 4) sourceC737) = raw12341 := by
      apply Matrix.ext; unfold tripleCharges sourceA737 sourceB737 sourceC737 difference raw12341; decide +kernel
    rw [ha]
    exact (canonical12341 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA737 + difference 5 2) (sourceB737 + difference 2 5) sourceC737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2632) := by
    have ha : (tripleCharges (sourceA737 + difference 5 2) (sourceB737 + difference 2 5) sourceC737) = raw12342 := by
      apply Matrix.ext; unfold tripleCharges sourceA737 sourceB737 sourceC737 difference raw12342; decide +kernel
    rw [ha]
    exact (canonical12342 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA737 + sourceB737) sourceC737) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA737 + sourceB737) sourceC737) = raw12326 := by
      apply Matrix.ext; unfold doubleCharges sourceA737 sourceB737 sourceC737 raw12326; decide +kernel
    rw [ha]
    exact (canonical12326 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA737 sourceB737 sourceC737
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm737, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq738 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm738 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA738 + difference 0 1) (sourceB738 + difference 1 0) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA738 + difference 0 1) (sourceB738 + difference 1 0) sourceC738) = raw12343 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12343; decide +kernel
    rw [ha]
    exact (canonical12343 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA738 + difference 0 2) (sourceB738 + difference 2 0) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA738 + difference 0 2) (sourceB738 + difference 2 0) sourceC738) = raw12344 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12344; decide +kernel
    rw [ha]
    exact (canonical12344 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA738 + difference 0 3) (sourceB738 + difference 3 0) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA738 + difference 0 3) (sourceB738 + difference 3 0) sourceC738) = raw12345 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12345; decide +kernel
    rw [ha]
    exact (canonical12345 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA738 + difference 0 4) (sourceB738 + difference 4 0) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA738 + difference 0 4) (sourceB738 + difference 4 0) sourceC738) = raw12346 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12346; decide +kernel
    rw [ha]
    exact (canonical12346 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA738 + difference 0 5) (sourceB738 + difference 5 0) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA738 + difference 0 5) (sourceB738 + difference 5 0) sourceC738) = raw12347 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12347; decide +kernel
    rw [ha]
    exact (canonical12347 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA738 + difference 1 0) (sourceB738 + difference 0 1) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4449) := by
    have ha : (tripleCharges (sourceA738 + difference 1 0) (sourceB738 + difference 0 1) sourceC738) = raw12348 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12348; decide +kernel
    rw [ha]
    exact (canonical12348 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA738 + difference 1 2) (sourceB738 + difference 2 1) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA738 + difference 1 2) (sourceB738 + difference 2 1) sourceC738) = raw12349 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12349; decide +kernel
    rw [ha]
    exact (canonical12349 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA738 + difference 1 3) (sourceB738 + difference 3 1) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA738 + difference 1 3) (sourceB738 + difference 3 1) sourceC738) = raw12350 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12350; decide +kernel
    rw [ha]
    exact (canonical12350 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA738 + difference 1 4) (sourceB738 + difference 4 1) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA738 + difference 1 4) (sourceB738 + difference 4 1) sourceC738) = raw12351 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12351; decide +kernel
    rw [ha]
    exact (canonical12351 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA738 + difference 1 5) (sourceB738 + difference 5 1) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA738 + difference 1 5) (sourceB738 + difference 5 1) sourceC738) = raw12352 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12352; decide +kernel
    rw [ha]
    exact (canonical12352 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA738 + difference 2 0) (sourceB738 + difference 0 2) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4487) := by
    have ha : (tripleCharges (sourceA738 + difference 2 0) (sourceB738 + difference 0 2) sourceC738) = raw12353 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12353; decide +kernel
    rw [ha]
    exact (canonical12353 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA738 + difference 2 1) (sourceB738 + difference 1 2) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5092) := by
    have ha : (tripleCharges (sourceA738 + difference 2 1) (sourceB738 + difference 1 2) sourceC738) = raw12354 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12354; decide +kernel
    rw [ha]
    exact (canonical12354 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA738 + difference 2 3) (sourceB738 + difference 3 2) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA738 + difference 2 3) (sourceB738 + difference 3 2) sourceC738) = raw12355 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12355; decide +kernel
    rw [ha]
    exact (canonical12355 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA738 + difference 2 4) (sourceB738 + difference 4 2) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5269) := by
    have ha : (tripleCharges (sourceA738 + difference 2 4) (sourceB738 + difference 4 2) sourceC738) = raw12356 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12356; decide +kernel
    rw [ha]
    exact (canonical12356 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA738 + difference 2 5) (sourceB738 + difference 5 2) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA738 + difference 2 5) (sourceB738 + difference 5 2) sourceC738) = raw12357 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12357; decide +kernel
    rw [ha]
    exact (canonical12357 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA738 + difference 3 0) (sourceB738 + difference 0 3) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA738 + difference 3 0) (sourceB738 + difference 0 3) sourceC738) = raw12358 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12358; decide +kernel
    rw [ha]
    exact (canonical12358 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA738 + difference 3 1) (sourceB738 + difference 1 3) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA738 + difference 3 1) (sourceB738 + difference 1 3) sourceC738) = raw12359 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12359; decide +kernel
    rw [ha]
    exact (canonical12359 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA738 + difference 3 2) (sourceB738 + difference 2 3) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA738 + difference 3 2) (sourceB738 + difference 2 3) sourceC738) = raw12360 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12360; decide +kernel
    rw [ha]
    exact (canonical12360 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA738 + difference 3 4) (sourceB738 + difference 4 3) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA738 + difference 3 4) (sourceB738 + difference 4 3) sourceC738) = raw12361 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12361; decide +kernel
    rw [ha]
    exact (canonical12361 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA738 + difference 3 5) (sourceB738 + difference 5 3) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA738 + difference 3 5) (sourceB738 + difference 5 3) sourceC738) = raw12362 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12362; decide +kernel
    rw [ha]
    exact (canonical12362 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA738 + difference 4 0) (sourceB738 + difference 0 4) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4453) := by
    have ha : (tripleCharges (sourceA738 + difference 4 0) (sourceB738 + difference 0 4) sourceC738) = raw12363 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12363; decide +kernel
    rw [ha]
    exact (canonical12363 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA738 + difference 4 1) (sourceB738 + difference 1 4) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5071) := by
    have ha : (tripleCharges (sourceA738 + difference 4 1) (sourceB738 + difference 1 4) sourceC738) = raw12364 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12364; decide +kernel
    rw [ha]
    exact (canonical12364 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA738 + difference 4 2) (sourceB738 + difference 2 4) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA738 + difference 4 2) (sourceB738 + difference 2 4) sourceC738) = raw12365 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12365; decide +kernel
    rw [ha]
    exact (canonical12365 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA738 + difference 4 3) (sourceB738 + difference 3 4) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA738 + difference 4 3) (sourceB738 + difference 3 4) sourceC738) = raw12366 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12366; decide +kernel
    rw [ha]
    exact (canonical12366 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA738 + difference 4 5) (sourceB738 + difference 5 4) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA738 + difference 4 5) (sourceB738 + difference 5 4) sourceC738) = raw12367 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12367; decide +kernel
    rw [ha]
    exact (canonical12367 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA738 + difference 5 0) (sourceB738 + difference 0 5) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4450) := by
    have ha : (tripleCharges (sourceA738 + difference 5 0) (sourceB738 + difference 0 5) sourceC738) = raw12368 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12368; decide +kernel
    rw [ha]
    exact (canonical12368 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA738 + difference 5 1) (sourceB738 + difference 1 5) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5069) := by
    have ha : (tripleCharges (sourceA738 + difference 5 1) (sourceB738 + difference 1 5) sourceC738) = raw12369 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12369; decide +kernel
    rw [ha]
    exact (canonical12369 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA738 + difference 5 2) (sourceB738 + difference 2 5) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA738 + difference 5 2) (sourceB738 + difference 2 5) sourceC738) = raw12370 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12370; decide +kernel
    rw [ha]
    exact (canonical12370 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA738 + difference 5 3) (sourceB738 + difference 3 5) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA738 + difference 5 3) (sourceB738 + difference 3 5) sourceC738) = raw12371 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12371; decide +kernel
    rw [ha]
    exact (canonical12371 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA738 + difference 5 4) (sourceB738 + difference 4 5) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA738 + difference 5 4) (sourceB738 + difference 4 5) sourceC738) = raw12372 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12372; decide +kernel
    rw [ha]
    exact (canonical12372 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA738 sourceB738 sourceC738
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm738, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq741 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm741 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA741 + difference 0 0) (sourceB741 + difference 0 0) sourceC741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA741 + difference 0 0) (sourceB741 + difference 0 0) sourceC741) = raw12433 := by
      apply Matrix.ext; unfold tripleCharges sourceA741 sourceB741 sourceC741 difference raw12433; decide +kernel
    rw [ha]
    exact (canonical12433 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA741 + difference 0 1) (sourceB741 + difference 1 0) sourceC741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA741 + difference 0 1) (sourceB741 + difference 1 0) sourceC741) = raw12434 := by
      apply Matrix.ext; unfold tripleCharges sourceA741 sourceB741 sourceC741 difference raw12434; decide +kernel
    rw [ha]
    exact (canonical12434 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA741 + difference 0 2) (sourceB741 + difference 2 0) sourceC741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA741 + difference 0 2) (sourceB741 + difference 2 0) sourceC741) = raw12435 := by
      apply Matrix.ext; unfold tripleCharges sourceA741 sourceB741 sourceC741 difference raw12435; decide +kernel
    rw [ha]
    exact (canonical12435 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA741 + difference 0 3) (sourceB741 + difference 3 0) sourceC741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA741 + difference 0 3) (sourceB741 + difference 3 0) sourceC741) = raw12436 := by
      apply Matrix.ext; unfold tripleCharges sourceA741 sourceB741 sourceC741 difference raw12436; decide +kernel
    rw [ha]
    exact (canonical12436 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA741 + difference 0 4) (sourceB741 + difference 4 0) sourceC741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA741 + difference 0 4) (sourceB741 + difference 4 0) sourceC741) = raw12437 := by
      apply Matrix.ext; unfold tripleCharges sourceA741 sourceB741 sourceC741 difference raw12437; decide +kernel
    rw [ha]
    exact (canonical12437 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA741 + difference 0 5) (sourceB741 + difference 5 0) sourceC741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4010) := by
    have ha : (tripleCharges (sourceA741 + difference 0 5) (sourceB741 + difference 5 0) sourceC741) = raw12438 := by
      apply Matrix.ext; unfold tripleCharges sourceA741 sourceB741 sourceC741 difference raw12438; decide +kernel
    rw [ha]
    exact (canonical12438 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA741 + sourceB741) sourceC741) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA741 + sourceB741) sourceC741) = raw12439 := by
      apply Matrix.ext; unfold doubleCharges sourceA741 sourceB741 sourceC741 raw12439; decide +kernel
    rw [ha]
    exact (canonical12439 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA741 sourceB741 sourceC741
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm741, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq743 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm743 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA743 + difference 1 0) (sourceB743 + difference 0 1) sourceC743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1403) := by
    have ha : (tripleCharges (sourceA743 + difference 1 0) (sourceB743 + difference 0 1) sourceC743) = raw12440 := by
      apply Matrix.ext; unfold tripleCharges sourceA743 sourceB743 sourceC743 difference raw12440; decide +kernel
    rw [ha]
    exact (canonical12440 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA743 + difference 1 1) (sourceB743 + difference 1 1) sourceC743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA743 + difference 1 1) (sourceB743 + difference 1 1) sourceC743) = raw12433 := by
      apply Matrix.ext; unfold tripleCharges sourceA743 sourceB743 sourceC743 difference raw12433; decide +kernel
    rw [ha]
    exact (canonical12433 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA743 + difference 1 2) (sourceB743 + difference 2 1) sourceC743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA743 + difference 1 2) (sourceB743 + difference 2 1) sourceC743) = raw12445 := by
      apply Matrix.ext; unfold tripleCharges sourceA743 sourceB743 sourceC743 difference raw12445; decide +kernel
    rw [ha]
    exact (canonical12445 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA743 + difference 1 3) (sourceB743 + difference 3 1) sourceC743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA743 + difference 1 3) (sourceB743 + difference 3 1) sourceC743) = raw12446 := by
      apply Matrix.ext; unfold tripleCharges sourceA743 sourceB743 sourceC743 difference raw12446; decide +kernel
    rw [ha]
    exact (canonical12446 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA743 + difference 1 4) (sourceB743 + difference 4 1) sourceC743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3084) := by
    have ha : (tripleCharges (sourceA743 + difference 1 4) (sourceB743 + difference 4 1) sourceC743) = raw12447 := by
      apply Matrix.ext; unfold tripleCharges sourceA743 sourceB743 sourceC743 difference raw12447; decide +kernel
    rw [ha]
    exact (canonical12447 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA743 + difference 1 5) (sourceB743 + difference 5 1) sourceC743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA743 + difference 1 5) (sourceB743 + difference 5 1) sourceC743) = raw12448 := by
      apply Matrix.ext; unfold tripleCharges sourceA743 sourceB743 sourceC743 difference raw12448; decide +kernel
    rw [ha]
    exact (canonical12448 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA743 + sourceB743) sourceC743) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA743 + sourceB743) sourceC743) = raw12439 := by
      apply Matrix.ext; unfold doubleCharges sourceA743 sourceB743 sourceC743 raw12439; decide +kernel
    rw [ha]
    exact (canonical12439 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA743 sourceB743 sourceC743
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm743, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq746 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm746 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA746 + difference 0 2) (sourceB746 + difference 2 0) sourceC746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA746 + difference 0 2) (sourceB746 + difference 2 0) sourceC746) = raw12435 := by
      apply Matrix.ext; unfold tripleCharges sourceA746 sourceB746 sourceC746 difference raw12435; decide +kernel
    rw [ha]
    exact (canonical12435 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA746 + difference 1 2) (sourceB746 + difference 2 1) sourceC746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA746 + difference 1 2) (sourceB746 + difference 2 1) sourceC746) = raw12445 := by
      apply Matrix.ext; unfold tripleCharges sourceA746 sourceB746 sourceC746 difference raw12445; decide +kernel
    rw [ha]
    exact (canonical12445 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA746 + difference 2 2) (sourceB746 + difference 2 2) sourceC746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA746 + difference 2 2) (sourceB746 + difference 2 2) sourceC746) = raw12433 := by
      apply Matrix.ext; unfold tripleCharges sourceA746 sourceB746 sourceC746 difference raw12433; decide +kernel
    rw [ha]
    exact (canonical12433 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA746 + difference 3 2) (sourceB746 + difference 2 3) sourceC746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA746 + difference 3 2) (sourceB746 + difference 2 3) sourceC746) = raw12456 := by
      apply Matrix.ext; unfold tripleCharges sourceA746 sourceB746 sourceC746 difference raw12456; decide +kernel
    rw [ha]
    exact (canonical12456 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA746 + difference 4 2) (sourceB746 + difference 2 4) sourceC746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA746 + difference 4 2) (sourceB746 + difference 2 4) sourceC746) = raw12457 := by
      apply Matrix.ext; unfold tripleCharges sourceA746 sourceB746 sourceC746 difference raw12457; decide +kernel
    rw [ha]
    exact (canonical12457 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA746 + difference 5 2) (sourceB746 + difference 2 5) sourceC746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA746 + difference 5 2) (sourceB746 + difference 2 5) sourceC746) = raw12458 := by
      apply Matrix.ext; unfold tripleCharges sourceA746 sourceB746 sourceC746 difference raw12458; decide +kernel
    rw [ha]
    exact (canonical12458 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA746 + sourceB746) sourceC746) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA746 + sourceB746) sourceC746) = raw12439 := by
      apply Matrix.ext; unfold doubleCharges sourceA746 sourceB746 sourceC746 raw12439; decide +kernel
    rw [ha]
    exact (canonical12439 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA746 sourceB746 sourceC746
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm746, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq747 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm747 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA747 + difference 0 3) (sourceB747 + difference 3 0) sourceC747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA747 + difference 0 3) (sourceB747 + difference 3 0) sourceC747) = raw12436 := by
      apply Matrix.ext; unfold tripleCharges sourceA747 sourceB747 sourceC747 difference raw12436; decide +kernel
    rw [ha]
    exact (canonical12436 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA747 + difference 1 3) (sourceB747 + difference 3 1) sourceC747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA747 + difference 1 3) (sourceB747 + difference 3 1) sourceC747) = raw12446 := by
      apply Matrix.ext; unfold tripleCharges sourceA747 sourceB747 sourceC747 difference raw12446; decide +kernel
    rw [ha]
    exact (canonical12446 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA747 + difference 2 3) (sourceB747 + difference 3 2) sourceC747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3115) := by
    have ha : (tripleCharges (sourceA747 + difference 2 3) (sourceB747 + difference 3 2) sourceC747) = raw12453 := by
      apply Matrix.ext; unfold tripleCharges sourceA747 sourceB747 sourceC747 difference raw12453; decide +kernel
    rw [ha]
    exact (canonical12453 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA747 + difference 3 3) (sourceB747 + difference 3 3) sourceC747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA747 + difference 3 3) (sourceB747 + difference 3 3) sourceC747) = raw12433 := by
      apply Matrix.ext; unfold tripleCharges sourceA747 sourceB747 sourceC747 difference raw12433; decide +kernel
    rw [ha]
    exact (canonical12433 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA747 + difference 4 3) (sourceB747 + difference 3 4) sourceC747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA747 + difference 4 3) (sourceB747 + difference 3 4) sourceC747) = raw12459 := by
      apply Matrix.ext; unfold tripleCharges sourceA747 sourceB747 sourceC747 difference raw12459; decide +kernel
    rw [ha]
    exact (canonical12459 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA747 + difference 5 3) (sourceB747 + difference 3 5) sourceC747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA747 + difference 5 3) (sourceB747 + difference 3 5) sourceC747) = raw12460 := by
      apply Matrix.ext; unfold tripleCharges sourceA747 sourceB747 sourceC747 difference raw12460; decide +kernel
    rw [ha]
    exact (canonical12460 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA747 + sourceB747) sourceC747) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA747 + sourceB747) sourceC747) = raw12439 := by
      apply Matrix.ext; unfold doubleCharges sourceA747 sourceB747 sourceC747 raw12439; decide +kernel
    rw [ha]
    exact (canonical12439 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA747 sourceB747 sourceC747
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm747, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq751 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm751 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA751 + difference 0 0) (sourceB751 + difference 0 0) sourceC751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA751 + difference 0 0) (sourceB751 + difference 0 0) sourceC751) = raw11769 := by
      apply Matrix.ext; unfold tripleCharges sourceA751 sourceB751 sourceC751 difference raw11769; decide +kernel
    rw [ha]
    exact (canonical11769 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA751 + difference 0 1) (sourceB751 + difference 1 0) sourceC751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA751 + difference 0 1) (sourceB751 + difference 1 0) sourceC751) = raw11753 := by
      apply Matrix.ext; unfold tripleCharges sourceA751 sourceB751 sourceC751 difference raw11753; decide +kernel
    rw [ha]
    exact (canonical11753 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA751 + difference 0 2) (sourceB751 + difference 2 0) sourceC751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA751 + difference 0 2) (sourceB751 + difference 2 0) sourceC751) = raw12227 := by
      apply Matrix.ext; unfold tripleCharges sourceA751 sourceB751 sourceC751 difference raw12227; decide +kernel
    rw [ha]
    exact (canonical12227 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA751 + difference 0 3) (sourceB751 + difference 3 0) sourceC751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA751 + difference 0 3) (sourceB751 + difference 3 0) sourceC751) = raw12513 := by
      apply Matrix.ext; unfold tripleCharges sourceA751 sourceB751 sourceC751 difference raw12513; decide +kernel
    rw [ha]
    exact (canonical12513 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA751 + difference 0 4) (sourceB751 + difference 4 0) sourceC751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3507) := by
    have ha : (tripleCharges (sourceA751 + difference 0 4) (sourceB751 + difference 4 0) sourceC751) = raw12514 := by
      apply Matrix.ext; unfold tripleCharges sourceA751 sourceB751 sourceC751 difference raw12514; decide +kernel
    rw [ha]
    exact (canonical12514 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA751 + difference 0 5) (sourceB751 + difference 5 0) sourceC751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA751 + difference 0 5) (sourceB751 + difference 5 0) sourceC751) = raw12515 := by
      apply Matrix.ext; unfold tripleCharges sourceA751 sourceB751 sourceC751 difference raw12515; decide +kernel
    rw [ha]
    exact (canonical12515 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA751 + sourceB751) sourceC751) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA751 + sourceB751) sourceC751) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA751 sourceB751 sourceC751 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA751 sourceB751 sourceC751
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm751, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq752 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm752 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA752 + difference 1 0) (sourceB752 + difference 0 1) sourceC752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2088) := by
    have ha : (tripleCharges (sourceA752 + difference 1 0) (sourceB752 + difference 0 1) sourceC752) = raw12516 := by
      apply Matrix.ext; unfold tripleCharges sourceA752 sourceB752 sourceC752 difference raw12516; decide +kernel
    rw [ha]
    exact (canonical12516 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA752 + difference 1 1) (sourceB752 + difference 1 1) sourceC752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA752 + difference 1 1) (sourceB752 + difference 1 1) sourceC752) = raw11769 := by
      apply Matrix.ext; unfold tripleCharges sourceA752 sourceB752 sourceC752 difference raw11769; decide +kernel
    rw [ha]
    exact (canonical11769 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA752 + difference 1 2) (sourceB752 + difference 2 1) sourceC752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA752 + difference 1 2) (sourceB752 + difference 2 1) sourceC752) = raw12517 := by
      apply Matrix.ext; unfold tripleCharges sourceA752 sourceB752 sourceC752 difference raw12517; decide +kernel
    rw [ha]
    exact (canonical12517 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA752 + difference 1 3) (sourceB752 + difference 3 1) sourceC752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2950) := by
    have ha : (tripleCharges (sourceA752 + difference 1 3) (sourceB752 + difference 3 1) sourceC752) = raw12518 := by
      apply Matrix.ext; unfold tripleCharges sourceA752 sourceB752 sourceC752 difference raw12518; decide +kernel
    rw [ha]
    exact (canonical12518 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA752 + difference 1 4) (sourceB752 + difference 4 1) sourceC752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3550) := by
    have ha : (tripleCharges (sourceA752 + difference 1 4) (sourceB752 + difference 4 1) sourceC752) = raw12519 := by
      apply Matrix.ext; unfold tripleCharges sourceA752 sourceB752 sourceC752 difference raw12519; decide +kernel
    rw [ha]
    exact (canonical12519 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA752 + difference 1 5) (sourceB752 + difference 5 1) sourceC752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA752 + difference 1 5) (sourceB752 + difference 5 1) sourceC752) = raw12520 := by
      apply Matrix.ext; unfold tripleCharges sourceA752 sourceB752 sourceC752 difference raw12520; decide +kernel
    rw [ha]
    exact (canonical12520 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA752 + sourceB752) sourceC752) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA752 + sourceB752) sourceC752) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA752 sourceB752 sourceC752 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA752 sourceB752 sourceC752
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm752, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq753 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm753 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA753 + difference 2 0) (sourceB753 + difference 0 2) sourceC753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA753 + difference 2 0) (sourceB753 + difference 0 2) sourceC753) = raw12521 := by
      apply Matrix.ext; unfold tripleCharges sourceA753 sourceB753 sourceC753 difference raw12521; decide +kernel
    rw [ha]
    exact (canonical12521 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA753 + difference 2 1) (sourceB753 + difference 1 2) sourceC753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3500) := by
    have ha : (tripleCharges (sourceA753 + difference 2 1) (sourceB753 + difference 1 2) sourceC753) = raw11762 := by
      apply Matrix.ext; unfold tripleCharges sourceA753 sourceB753 sourceC753 difference raw11762; decide +kernel
    rw [ha]
    exact (canonical11762 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA753 + difference 2 2) (sourceB753 + difference 2 2) sourceC753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA753 + difference 2 2) (sourceB753 + difference 2 2) sourceC753) = raw11769 := by
      apply Matrix.ext; unfold tripleCharges sourceA753 sourceB753 sourceC753 difference raw11769; decide +kernel
    rw [ha]
    exact (canonical11769 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA753 + difference 2 3) (sourceB753 + difference 3 2) sourceC753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2956) := by
    have ha : (tripleCharges (sourceA753 + difference 2 3) (sourceB753 + difference 3 2) sourceC753) = raw12522 := by
      apply Matrix.ext; unfold tripleCharges sourceA753 sourceB753 sourceC753 difference raw12522; decide +kernel
    rw [ha]
    exact (canonical12522 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA753 + difference 2 4) (sourceB753 + difference 4 2) sourceC753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3552) := by
    have ha : (tripleCharges (sourceA753 + difference 2 4) (sourceB753 + difference 4 2) sourceC753) = raw12523 := by
      apply Matrix.ext; unfold tripleCharges sourceA753 sourceB753 sourceC753 difference raw12523; decide +kernel
    rw [ha]
    exact (canonical12523 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA753 + difference 2 5) (sourceB753 + difference 5 2) sourceC753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA753 + difference 2 5) (sourceB753 + difference 5 2) sourceC753) = raw12078 := by
      apply Matrix.ext; unfold tripleCharges sourceA753 sourceB753 sourceC753 difference raw12078; decide +kernel
    rw [ha]
    exact (canonical12078 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA753 + sourceB753) sourceC753) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA753 + sourceB753) sourceC753) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA753 sourceB753 sourceC753 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA753 sourceB753 sourceC753
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm753, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq754 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm754 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA754 + difference 0 3) (sourceB754 + difference 3 0) sourceC754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA754 + difference 0 3) (sourceB754 + difference 3 0) sourceC754) = raw12513 := by
      apply Matrix.ext; unfold tripleCharges sourceA754 sourceB754 sourceC754 difference raw12513; decide +kernel
    rw [ha]
    exact (canonical12513 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA754 + difference 1 3) (sourceB754 + difference 3 1) sourceC754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2950) := by
    have ha : (tripleCharges (sourceA754 + difference 1 3) (sourceB754 + difference 3 1) sourceC754) = raw12518 := by
      apply Matrix.ext; unfold tripleCharges sourceA754 sourceB754 sourceC754 difference raw12518; decide +kernel
    rw [ha]
    exact (canonical12518 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA754 + difference 2 3) (sourceB754 + difference 3 2) sourceC754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2956) := by
    have ha : (tripleCharges (sourceA754 + difference 2 3) (sourceB754 + difference 3 2) sourceC754) = raw12522 := by
      apply Matrix.ext; unfold tripleCharges sourceA754 sourceB754 sourceC754 difference raw12522; decide +kernel
    rw [ha]
    exact (canonical12522 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA754 + difference 3 3) (sourceB754 + difference 3 3) sourceC754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA754 + difference 3 3) (sourceB754 + difference 3 3) sourceC754) = raw11769 := by
      apply Matrix.ext; unfold tripleCharges sourceA754 sourceB754 sourceC754 difference raw11769; decide +kernel
    rw [ha]
    exact (canonical11769 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA754 + difference 4 3) (sourceB754 + difference 3 4) sourceC754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3096) := by
    have ha : (tripleCharges (sourceA754 + difference 4 3) (sourceB754 + difference 3 4) sourceC754) = raw12524 := by
      apply Matrix.ext; unfold tripleCharges sourceA754 sourceB754 sourceC754 difference raw12524; decide +kernel
    rw [ha]
    exact (canonical12524 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA754 + difference 5 3) (sourceB754 + difference 3 5) sourceC754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2962) := by
    have ha : (tripleCharges (sourceA754 + difference 5 3) (sourceB754 + difference 3 5) sourceC754) = raw12525 := by
      apply Matrix.ext; unfold tripleCharges sourceA754 sourceB754 sourceC754 difference raw12525; decide +kernel
    rw [ha]
    exact (canonical12525 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA754 + sourceB754) sourceC754) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA754 + sourceB754) sourceC754) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA754 sourceB754 sourceC754 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA754 sourceB754 sourceC754
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm754, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq755 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm755 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA755 + difference 4 0) (sourceB755 + difference 0 4) sourceC755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA755 + difference 4 0) (sourceB755 + difference 0 4) sourceC755) = raw12526 := by
      apply Matrix.ext; unfold tripleCharges sourceA755 sourceB755 sourceC755 difference raw12526; decide +kernel
    rw [ha]
    exact (canonical12526 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA755 + difference 4 1) (sourceB755 + difference 1 4) sourceC755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA755 + difference 4 1) (sourceB755 + difference 1 4) sourceC755) = raw11770 := by
      apply Matrix.ext; unfold tripleCharges sourceA755 sourceB755 sourceC755 difference raw11770; decide +kernel
    rw [ha]
    exact (canonical11770 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA755 + difference 4 2) (sourceB755 + difference 2 4) sourceC755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA755 + difference 4 2) (sourceB755 + difference 2 4) sourceC755) = raw12527 := by
      apply Matrix.ext; unfold tripleCharges sourceA755 sourceB755 sourceC755 difference raw12527; decide +kernel
    rw [ha]
    exact (canonical12527 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA755 + difference 4 3) (sourceB755 + difference 3 4) sourceC755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3096) := by
    have ha : (tripleCharges (sourceA755 + difference 4 3) (sourceB755 + difference 3 4) sourceC755) = raw12524 := by
      apply Matrix.ext; unfold tripleCharges sourceA755 sourceB755 sourceC755 difference raw12524; decide +kernel
    rw [ha]
    exact (canonical12524 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA755 + difference 4 4) (sourceB755 + difference 4 4) sourceC755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA755 + difference 4 4) (sourceB755 + difference 4 4) sourceC755) = raw11769 := by
      apply Matrix.ext; unfold tripleCharges sourceA755 sourceB755 sourceC755 difference raw11769; decide +kernel
    rw [ha]
    exact (canonical11769 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA755 + difference 4 5) (sourceB755 + difference 5 4) sourceC755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA755 + difference 4 5) (sourceB755 + difference 5 4) sourceC755) = raw12528 := by
      apply Matrix.ext; unfold tripleCharges sourceA755 sourceB755 sourceC755 difference raw12528; decide +kernel
    rw [ha]
    exact (canonical12528 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA755 + sourceB755) sourceC755) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA755 + sourceB755) sourceC755) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA755 sourceB755 sourceC755 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA755 sourceB755 sourceC755
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm755, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq756 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm756 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA756 + difference 0 4) (sourceB756 + difference 4 0) sourceC756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3507) := by
    have ha : (tripleCharges (sourceA756 + difference 0 4) (sourceB756 + difference 4 0) sourceC756) = raw12514 := by
      apply Matrix.ext; unfold tripleCharges sourceA756 sourceB756 sourceC756 difference raw12514; decide +kernel
    rw [ha]
    exact (canonical12514 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA756 + difference 1 4) (sourceB756 + difference 4 1) sourceC756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3550) := by
    have ha : (tripleCharges (sourceA756 + difference 1 4) (sourceB756 + difference 4 1) sourceC756) = raw12519 := by
      apply Matrix.ext; unfold tripleCharges sourceA756 sourceB756 sourceC756 difference raw12519; decide +kernel
    rw [ha]
    exact (canonical12519 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA756 + difference 2 4) (sourceB756 + difference 4 2) sourceC756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3552) := by
    have ha : (tripleCharges (sourceA756 + difference 2 4) (sourceB756 + difference 4 2) sourceC756) = raw12523 := by
      apply Matrix.ext; unfold tripleCharges sourceA756 sourceB756 sourceC756 difference raw12523; decide +kernel
    rw [ha]
    exact (canonical12523 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA756 + difference 3 4) (sourceB756 + difference 4 3) sourceC756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA756 + difference 3 4) (sourceB756 + difference 4 3) sourceC756) = raw12529 := by
      apply Matrix.ext; unfold tripleCharges sourceA756 sourceB756 sourceC756 difference raw12529; decide +kernel
    rw [ha]
    exact (canonical12529 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA756 + difference 4 4) (sourceB756 + difference 4 4) sourceC756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA756 + difference 4 4) (sourceB756 + difference 4 4) sourceC756) = raw11769 := by
      apply Matrix.ext; unfold tripleCharges sourceA756 sourceB756 sourceC756 difference raw11769; decide +kernel
    rw [ha]
    exact (canonical11769 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA756 + difference 5 4) (sourceB756 + difference 4 5) sourceC756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2995) := by
    have ha : (tripleCharges (sourceA756 + difference 5 4) (sourceB756 + difference 4 5) sourceC756) = raw12530 := by
      apply Matrix.ext; unfold tripleCharges sourceA756 sourceB756 sourceC756 difference raw12530; decide +kernel
    rw [ha]
    exact (canonical12530 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA756 + sourceB756) sourceC756) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA756 + sourceB756) sourceC756) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA756 sourceB756 sourceC756 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA756 sourceB756 sourceC756
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm756, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck640 : Integer.Sparse.reindex keyMap MixedData.row640 = numericRow640 := by decide +kernel

theorem numericCheck640 (x : Master → ℝ) : Integer.Sparse.eval numericRow640 x =
    (1 : ℝ) * reducedSource640 x := by
  norm_num [numericRow640, reducedSource640, Integer.Sparse.eval, Sparse.eval, nodeValue1291, nodeValue2587, nodeValue2739, nodeValue2763, nodeValue2773, nodeValue2782, nodeValue4092]

theorem reindexCheck641 : Integer.Sparse.reindex keyMap MixedData.row641 = numericRow641 := by decide +kernel

theorem numericCheck641 (x : Master → ℝ) : Integer.Sparse.eval numericRow641 x =
    (1 : ℝ) * reducedSource641 x := by
  norm_num [numericRow641, reducedSource641, Integer.Sparse.eval, Sparse.eval, nodeValue2630, nodeValue2632, nodeValue2634, nodeValue2639, nodeValue2763, nodeValue3884, nodeValue4092]

theorem reindexCheck642 : Integer.Sparse.reindex keyMap MixedData.row642 = numericRow642 := by decide +kernel

theorem numericCheck642 (x : Master → ℝ) : Integer.Sparse.eval numericRow642 x =
    (17280 : ℝ) * reducedSource642 x := by
  norm_num [numericRow642, reducedSource642, Integer.Sparse.eval, Sparse.eval, nodeValue4449, nodeValue4450, nodeValue4453, nodeValue4459, nodeValue4487, nodeValue5069, nodeValue5071, nodeValue5074, nodeValue5092, nodeValue5140, nodeValue5160, nodeValue5161, nodeValue5164, nodeValue5170, nodeValue5226, nodeValue5229, nodeValue5236, nodeValue5255, nodeValue5260, nodeValue5269, nodeValue5281, nodeValue5282, nodeValue5284, nodeValue5289, nodeValue5438, nodeValue5480, nodeValue5484, nodeValue5485]
  ring

theorem reindexCheck645 : Integer.Sparse.reindex keyMap MixedData.row645 = numericRow645 := by decide +kernel

theorem numericCheck645 (x : Master → ℝ) : Integer.Sparse.eval numericRow645 x =
    (1 : ℝ) * reducedSource645 x := by
  norm_num [numericRow645, reducedSource645, Integer.Sparse.eval, Sparse.eval, nodeValue3097, nodeValue3876, nodeValue3978, nodeValue3983, nodeValue4010, nodeValue4091]

theorem reindexCheck646 : Integer.Sparse.reindex keyMap MixedData.row646 = numericRow646 := by decide +kernel

theorem numericCheck646 (x : Master → ℝ) : Integer.Sparse.eval numericRow646 x =
    (1 : ℝ) * reducedSource646 x := by
  norm_num [numericRow646, reducedSource646, Integer.Sparse.eval, Sparse.eval, nodeValue1403, nodeValue2951, nodeValue3074, nodeValue3084, nodeValue3091, nodeValue3097, nodeValue4091]

theorem reindexCheck647 : Integer.Sparse.reindex keyMap MixedData.row647 = numericRow647 := by decide +kernel

theorem numericCheck647 (x : Master → ℝ) : Integer.Sparse.eval numericRow647 x =
    (1 : ℝ) * reducedSource647 x := by
  norm_num [numericRow647, reducedSource647, Integer.Sparse.eval, Sparse.eval, nodeValue2951, nodeValue2954, nodeValue2955, nodeValue2964, nodeValue3097, nodeValue3983, nodeValue4091]

theorem reindexCheck648 : Integer.Sparse.reindex keyMap MixedData.row648 = numericRow648 := by decide +kernel

theorem numericCheck648 (x : Master → ℝ) : Integer.Sparse.eval numericRow648 x =
    (1 : ℝ) * reducedSource648 x := by
  norm_num [numericRow648, reducedSource648, Integer.Sparse.eval, Sparse.eval, nodeValue2942, nodeValue3091, nodeValue3092, nodeValue3097, nodeValue3115, nodeValue3876, nodeValue4091]

theorem reindexCheck650 : Integer.Sparse.reindex keyMap MixedData.row650 = numericRow650 := by decide +kernel

theorem numericCheck650 (x : Master → ℝ) : Integer.Sparse.eval numericRow650 x =
    (1 : ℝ) * reducedSource650 x := by
  norm_num [numericRow650, reducedSource650, Integer.Sparse.eval, Sparse.eval, nodeValue2952, nodeValue3503, nodeValue3507, nodeValue3534, nodeValue3572, nodeValue3583, nodeValue4083]

theorem reindexCheck651 : Integer.Sparse.reindex keyMap MixedData.row651 = numericRow651 := by decide +kernel

theorem numericCheck651 (x : Master → ℝ) : Integer.Sparse.eval numericRow651 x =
    (1 : ℝ) * reducedSource651 x := by
  norm_num [numericRow651, reducedSource651, Integer.Sparse.eval, Sparse.eval, nodeValue2088, nodeValue2950, nodeValue3550, nodeValue3571, nodeValue3572, nodeValue4083]

theorem reindexCheck652 : Integer.Sparse.reindex keyMap MixedData.row652 = numericRow652 := by decide +kernel

theorem numericCheck652 (x : Master → ℝ) : Integer.Sparse.eval numericRow652 x =
    (1 : ℝ) * reducedSource652 x := by
  norm_num [numericRow652, reducedSource652, Integer.Sparse.eval, Sparse.eval, nodeValue2094, nodeValue2956, nodeValue3500, nodeValue3552, nodeValue3572, nodeValue3573, nodeValue4083]

theorem reindexCheck653 : Integer.Sparse.reindex keyMap MixedData.row653 = numericRow653 := by decide +kernel

theorem numericCheck653 (x : Master → ℝ) : Integer.Sparse.eval numericRow653 x =
    (1 : ℝ) * reducedSource653 x := by
  norm_num [numericRow653, reducedSource653, Integer.Sparse.eval, Sparse.eval, nodeValue2950, nodeValue2952, nodeValue2956, nodeValue2962, nodeValue3096, nodeValue3572, nodeValue4083]

theorem reindexCheck654 : Integer.Sparse.reindex keyMap MixedData.row654 = numericRow654 := by decide +kernel

theorem numericCheck654 (x : Master → ℝ) : Integer.Sparse.eval numericRow654 x =
    (1 : ℝ) * reducedSource654 x := by
  norm_num [numericRow654, reducedSource654, Integer.Sparse.eval, Sparse.eval, nodeValue2107, nodeValue3096, nodeValue3503, nodeValue3572, nodeValue3581, nodeValue3583, nodeValue4083]

theorem reindexCheck655 : Integer.Sparse.reindex keyMap MixedData.row655 = numericRow655 := by decide +kernel

theorem numericCheck655 (x : Master → ℝ) : Integer.Sparse.eval numericRow655 x =
    (1 : ℝ) * reducedSource655 x := by
  norm_num [numericRow655, reducedSource655, Integer.Sparse.eval, Sparse.eval, nodeValue2995, nodeValue3507, nodeValue3550, nodeValue3552, nodeValue3572, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero640 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource640 (mixedVector B) = 0 := by
  have h1291 : mixedVector B (Sum.inr 1291) = Sparse.eval nodeValue1291 (mixedVector B) := by
    change mixedMoment B node1291 node1291Labels = _
    exact sound1291 B hB hF
  have h2587 : mixedVector B (Sum.inr 2587) = Sparse.eval nodeValue2587 (mixedVector B) := by
    change mixedMoment B node2587 node2587Labels = _
    exact sound2587 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm736, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1291, h2587, h2739, h2763, h2773, h2782, h4092, reducedSource640] using sourceEq736 B hB

theorem rowSound640 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row640 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck640, numericCheck640, reducedZero640 B hB hF, mul_zero]

theorem reducedZero641 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource641 (mixedVector B) = 0 := by
  have h2630 : mixedVector B (Sum.inr 2630) = Sparse.eval nodeValue2630 (mixedVector B) := by
    change mixedMoment B node2630 node2630Labels = _
    exact sound2630 B hB hF
  have h2632 : mixedVector B (Sum.inr 2632) = Sparse.eval nodeValue2632 (mixedVector B) := by
    change mixedMoment B node2632 node2632Labels = _
    exact sound2632 B hB hF
  have h2634 : mixedVector B (Sum.inr 2634) = Sparse.eval nodeValue2634 (mixedVector B) := by
    change mixedMoment B node2634 node2634Labels = _
    exact sound2634 B hB hF
  have h2639 : mixedVector B (Sum.inr 2639) = Sparse.eval nodeValue2639 (mixedVector B) := by
    change mixedMoment B node2639 node2639Labels = _
    exact sound2639 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm737, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2630, h2632, h2634, h2639, h2763, h3884, h4092, reducedSource641] using sourceEq737 B hB

theorem rowSound641 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row641 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck641, numericCheck641, reducedZero641 B hB hF, mul_zero]

theorem reducedZero642 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource642 (mixedVector B) = 0 := by
  have h4449 : mixedVector B (Sum.inr 4449) = Sparse.eval nodeValue4449 (mixedVector B) := by
    change mixedMoment B node4449 node4449Labels = _
    exact sound4449 B hB hF
  have h4450 : mixedVector B (Sum.inr 4450) = Sparse.eval nodeValue4450 (mixedVector B) := by
    change mixedMoment B node4450 node4450Labels = _
    exact sound4450 B hB hF
  have h4453 : mixedVector B (Sum.inr 4453) = Sparse.eval nodeValue4453 (mixedVector B) := by
    change mixedMoment B node4453 node4453Labels = _
    exact sound4453 B hB hF
  have h4459 : mixedVector B (Sum.inr 4459) = Sparse.eval nodeValue4459 (mixedVector B) := by
    change mixedMoment B node4459 node4459Labels = _
    exact sound4459 B hB hF
  have h4487 : mixedVector B (Sum.inr 4487) = Sparse.eval nodeValue4487 (mixedVector B) := by
    change mixedMoment B node4487 node4487Labels = _
    exact sound4487 B hB hF
  have h5069 : mixedVector B (Sum.inr 5069) = Sparse.eval nodeValue5069 (mixedVector B) := by
    change mixedMoment B node5069 node5069Labels = _
    exact sound5069 B hB hF
  have h5071 : mixedVector B (Sum.inr 5071) = Sparse.eval nodeValue5071 (mixedVector B) := by
    change mixedMoment B node5071 node5071Labels = _
    exact sound5071 B hB hF
  have h5074 : mixedVector B (Sum.inr 5074) = Sparse.eval nodeValue5074 (mixedVector B) := by
    change mixedMoment B node5074 node5074Labels = _
    exact sound5074 B hB hF
  have h5092 : mixedVector B (Sum.inr 5092) = Sparse.eval nodeValue5092 (mixedVector B) := by
    change mixedMoment B node5092 node5092Labels = _
    exact sound5092 B hB hF
  have h5140 : mixedVector B (Sum.inr 5140) = Sparse.eval nodeValue5140 (mixedVector B) := by
    change mixedMoment B node5140 node5140Labels = _
    exact sound5140 B hB hF
  have h5160 : mixedVector B (Sum.inr 5160) = Sparse.eval nodeValue5160 (mixedVector B) := by
    change mixedMoment B node5160 node5160Labels = _
    exact sound5160 B hB hF
  have h5161 : mixedVector B (Sum.inr 5161) = Sparse.eval nodeValue5161 (mixedVector B) := by
    change mixedMoment B node5161 node5161Labels = _
    exact sound5161 B hB hF
  have h5164 : mixedVector B (Sum.inr 5164) = Sparse.eval nodeValue5164 (mixedVector B) := by
    change mixedMoment B node5164 node5164Labels = _
    exact sound5164 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5226 : mixedVector B (Sum.inr 5226) = Sparse.eval nodeValue5226 (mixedVector B) := by
    change mixedMoment B node5226 node5226Labels = _
    exact sound5226 B hB hF
  have h5229 : mixedVector B (Sum.inr 5229) = Sparse.eval nodeValue5229 (mixedVector B) := by
    change mixedMoment B node5229 node5229Labels = _
    exact sound5229 B hB hF
  have h5236 : mixedVector B (Sum.inr 5236) = Sparse.eval nodeValue5236 (mixedVector B) := by
    change mixedMoment B node5236 node5236Labels = _
    exact sound5236 B hB hF
  have h5255 : mixedVector B (Sum.inr 5255) = Sparse.eval nodeValue5255 (mixedVector B) := by
    change mixedMoment B node5255 node5255Labels = _
    exact sound5255 B hB hF
  have h5260 : mixedVector B (Sum.inr 5260) = Sparse.eval nodeValue5260 (mixedVector B) := by
    change mixedMoment B node5260 node5260Labels = _
    exact sound5260 B hB hF
  have h5269 : mixedVector B (Sum.inr 5269) = Sparse.eval nodeValue5269 (mixedVector B) := by
    change mixedMoment B node5269 node5269Labels = _
    exact sound5269 B hB hF
  have h5281 : mixedVector B (Sum.inr 5281) = Sparse.eval nodeValue5281 (mixedVector B) := by
    change mixedMoment B node5281 node5281Labels = _
    exact sound5281 B hB hF
  have h5282 : mixedVector B (Sum.inr 5282) = Sparse.eval nodeValue5282 (mixedVector B) := by
    change mixedMoment B node5282 node5282Labels = _
    exact sound5282 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5289 : mixedVector B (Sum.inr 5289) = Sparse.eval nodeValue5289 (mixedVector B) := by
    change mixedMoment B node5289 node5289Labels = _
    exact sound5289 B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5480 : mixedVector B (Sum.inr 5480) = Sparse.eval nodeValue5480 (mixedVector B) := by
    change mixedMoment B node5480 node5480Labels = _
    exact sound5480 B hB hF
  have h5484 : mixedVector B (Sum.inr 5484) = Sparse.eval nodeValue5484 (mixedVector B) := by
    change mixedMoment B node5484 node5484Labels = _
    exact sound5484 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485_e B hB hF
  simpa only [sourceForm738, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4449, h4450, h4453, h4459, h4487, h5069, h5071, h5074, h5092, h5140, h5160, h5161, h5164, h5170, h5226, h5229, h5236, h5255, h5260, h5269, h5281, h5282, h5284, h5289, h5438, h5480, h5484, h5485, reducedSource642] using sourceEq738 B hB

theorem rowSound642 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row642 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck642, numericCheck642, reducedZero642 B hB hF, mul_zero]

theorem reducedZero645 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource645 (mixedVector B) = 0 := by
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3978 : mixedVector B (Sum.inr 3978) = Sparse.eval nodeValue3978 (mixedVector B) := by
    change mixedMoment B node3978 node3978Labels = _
    exact sound3978 B hB hF
  have h3983 : mixedVector B (Sum.inr 3983) = Sparse.eval nodeValue3983 (mixedVector B) := by
    change mixedMoment B node3983 node3983Labels = _
    exact sound3983 B hB hF
  have h4010 : mixedVector B (Sum.inr 4010) = Sparse.eval nodeValue4010 (mixedVector B) := by
    change mixedMoment B node4010 node4010Labels = _
    exact sound4010 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm741, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3097, h3876, h3978, h3983, h4010, h4091, reducedSource645] using sourceEq741 B hB

theorem rowSound645 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row645 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck645, numericCheck645, reducedZero645 B hB hF, mul_zero]

theorem reducedZero646 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource646 (mixedVector B) = 0 := by
  have h1403 : mixedVector B (Sum.inr 1403) = Sparse.eval nodeValue1403 (mixedVector B) := by
    change mixedMoment B node1403 node1403Labels = _
    exact sound1403 B hB hF
  have h2951 : mixedVector B (Sum.inr 2951) = Sparse.eval nodeValue2951 (mixedVector B) := by
    change mixedMoment B node2951 node2951Labels = _
    exact sound2951 B hB hF
  have h3074 : mixedVector B (Sum.inr 3074) = Sparse.eval nodeValue3074 (mixedVector B) := by
    change mixedMoment B node3074 node3074Labels = _
    exact sound3074 B hB hF
  have h3084 : mixedVector B (Sum.inr 3084) = Sparse.eval nodeValue3084 (mixedVector B) := by
    change mixedMoment B node3084 node3084Labels = _
    exact sound3084 B hB hF
  have h3091 : mixedVector B (Sum.inr 3091) = Sparse.eval nodeValue3091 (mixedVector B) := by
    change mixedMoment B node3091 node3091Labels = _
    exact sound3091 B hB hF
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm743, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1403, h2951, h3074, h3084, h3091, h3097, h4091, reducedSource646] using sourceEq743 B hB

theorem rowSound646 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row646 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck646, numericCheck646, reducedZero646 B hB hF, mul_zero]

theorem reducedZero647 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource647 (mixedVector B) = 0 := by
  have h2951 : mixedVector B (Sum.inr 2951) = Sparse.eval nodeValue2951 (mixedVector B) := by
    change mixedMoment B node2951 node2951Labels = _
    exact sound2951 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h2955 : mixedVector B (Sum.inr 2955) = Sparse.eval nodeValue2955 (mixedVector B) := by
    change mixedMoment B node2955 node2955Labels = _
    exact sound2955 B hB hF
  have h2964 : mixedVector B (Sum.inr 2964) = Sparse.eval nodeValue2964 (mixedVector B) := by
    change mixedMoment B node2964 node2964Labels = _
    exact sound2964 B hB hF
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h3983 : mixedVector B (Sum.inr 3983) = Sparse.eval nodeValue3983 (mixedVector B) := by
    change mixedMoment B node3983 node3983Labels = _
    exact sound3983 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm746, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2951, h2954, h2955, h2964, h3097, h3983, h4091, reducedSource647] using sourceEq746 B hB

theorem rowSound647 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row647 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck647, numericCheck647, reducedZero647 B hB hF, mul_zero]

theorem reducedZero648 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource648 (mixedVector B) = 0 := by
  have h2942 : mixedVector B (Sum.inr 2942) = Sparse.eval nodeValue2942 (mixedVector B) := by
    change mixedMoment B node2942 node2942Labels = _
    exact sound2942 B hB hF
  have h3091 : mixedVector B (Sum.inr 3091) = Sparse.eval nodeValue3091 (mixedVector B) := by
    change mixedMoment B node3091 node3091Labels = _
    exact sound3091 B hB hF
  have h3092 : mixedVector B (Sum.inr 3092) = Sparse.eval nodeValue3092 (mixedVector B) := by
    change mixedMoment B node3092 node3092Labels = _
    exact sound3092 B hB hF
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h3115 : mixedVector B (Sum.inr 3115) = Sparse.eval nodeValue3115 (mixedVector B) := by
    change mixedMoment B node3115 node3115Labels = _
    exact sound3115 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm747, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2942, h3091, h3092, h3097, h3115, h3876, h4091, reducedSource648] using sourceEq747 B hB

theorem rowSound648 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row648 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck648, numericCheck648, reducedZero648 B hB hF, mul_zero]

theorem reducedZero650 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource650 (mixedVector B) = 0 := by
  have h2952 : mixedVector B (Sum.inr 2952) = Sparse.eval nodeValue2952 (mixedVector B) := by
    change mixedMoment B node2952 node2952Labels = _
    exact sound2952 B hB hF
  have h3503 : mixedVector B (Sum.inr 3503) = Sparse.eval nodeValue3503 (mixedVector B) := by
    change mixedMoment B node3503 node3503Labels = _
    exact sound3503 B hB hF
  have h3507 : mixedVector B (Sum.inr 3507) = Sparse.eval nodeValue3507 (mixedVector B) := by
    change mixedMoment B node3507 node3507Labels = _
    exact sound3507 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm751, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2952, h3503, h3507, h3534, h3572, h3583, h4083, reducedSource650] using sourceEq751 B hB

theorem rowSound650 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row650 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck650, numericCheck650, reducedZero650 B hB hF, mul_zero]

theorem reducedZero651 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource651 (mixedVector B) = 0 := by
  have h2088 : mixedVector B (Sum.inr 2088) = Sparse.eval nodeValue2088 (mixedVector B) := by
    change mixedMoment B node2088 node2088Labels = _
    exact sound2088 B hB hF
  have h2950 : mixedVector B (Sum.inr 2950) = Sparse.eval nodeValue2950 (mixedVector B) := by
    change mixedMoment B node2950 node2950Labels = _
    exact sound2950 B hB hF
  have h3550 : mixedVector B (Sum.inr 3550) = Sparse.eval nodeValue3550 (mixedVector B) := by
    change mixedMoment B node3550 node3550Labels = _
    exact sound3550 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm752, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2088, h2950, h3550, h3571, h3572, h4083, reducedSource651] using sourceEq752 B hB

theorem rowSound651 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row651 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck651, numericCheck651, reducedZero651 B hB hF, mul_zero]

theorem reducedZero652 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource652 (mixedVector B) = 0 := by
  have h2094 : mixedVector B (Sum.inr 2094) = Sparse.eval nodeValue2094 (mixedVector B) := by
    change mixedMoment B node2094 node2094Labels = _
    exact sound2094 B hB hF
  have h2956 : mixedVector B (Sum.inr 2956) = Sparse.eval nodeValue2956 (mixedVector B) := by
    change mixedMoment B node2956 node2956Labels = _
    exact sound2956 B hB hF
  have h3500 : mixedVector B (Sum.inr 3500) = Sparse.eval nodeValue3500 (mixedVector B) := by
    change mixedMoment B node3500 node3500Labels = _
    exact sound3500 B hB hF
  have h3552 : mixedVector B (Sum.inr 3552) = Sparse.eval nodeValue3552 (mixedVector B) := by
    change mixedMoment B node3552 node3552Labels = _
    exact sound3552 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm753, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2094, h2956, h3500, h3552, h3572, h3573, h4083, reducedSource652] using sourceEq753 B hB

theorem rowSound652 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row652 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck652, numericCheck652, reducedZero652 B hB hF, mul_zero]

theorem reducedZero653 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource653 (mixedVector B) = 0 := by
  have h2950 : mixedVector B (Sum.inr 2950) = Sparse.eval nodeValue2950 (mixedVector B) := by
    change mixedMoment B node2950 node2950Labels = _
    exact sound2950 B hB hF
  have h2952 : mixedVector B (Sum.inr 2952) = Sparse.eval nodeValue2952 (mixedVector B) := by
    change mixedMoment B node2952 node2952Labels = _
    exact sound2952 B hB hF
  have h2956 : mixedVector B (Sum.inr 2956) = Sparse.eval nodeValue2956 (mixedVector B) := by
    change mixedMoment B node2956 node2956Labels = _
    exact sound2956 B hB hF
  have h2962 : mixedVector B (Sum.inr 2962) = Sparse.eval nodeValue2962 (mixedVector B) := by
    change mixedMoment B node2962 node2962Labels = _
    exact sound2962 B hB hF
  have h3096 : mixedVector B (Sum.inr 3096) = Sparse.eval nodeValue3096 (mixedVector B) := by
    change mixedMoment B node3096 node3096Labels = _
    exact sound3096 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm754, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2950, h2952, h2956, h2962, h3096, h3572, h4083, reducedSource653] using sourceEq754 B hB

theorem rowSound653 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row653 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck653, numericCheck653, reducedZero653 B hB hF, mul_zero]

theorem reducedZero654 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource654 (mixedVector B) = 0 := by
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h3096 : mixedVector B (Sum.inr 3096) = Sparse.eval nodeValue3096 (mixedVector B) := by
    change mixedMoment B node3096 node3096Labels = _
    exact sound3096 B hB hF
  have h3503 : mixedVector B (Sum.inr 3503) = Sparse.eval nodeValue3503 (mixedVector B) := by
    change mixedMoment B node3503 node3503Labels = _
    exact sound3503 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3581 : mixedVector B (Sum.inr 3581) = Sparse.eval nodeValue3581 (mixedVector B) := by
    change mixedMoment B node3581 node3581Labels = _
    exact sound3581 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm755, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2107, h3096, h3503, h3572, h3581, h3583, h4083, reducedSource654] using sourceEq755 B hB

theorem rowSound654 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row654 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck654, numericCheck654, reducedZero654 B hB hF, mul_zero]

theorem reducedZero655 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource655 (mixedVector B) = 0 := by
  have h2995 : mixedVector B (Sum.inr 2995) = Sparse.eval nodeValue2995 (mixedVector B) := by
    change mixedMoment B node2995 node2995Labels = _
    exact sound2995 B hB hF
  have h3507 : mixedVector B (Sum.inr 3507) = Sparse.eval nodeValue3507 (mixedVector B) := by
    change mixedMoment B node3507 node3507Labels = _
    exact sound3507 B hB hF
  have h3550 : mixedVector B (Sum.inr 3550) = Sparse.eval nodeValue3550 (mixedVector B) := by
    change mixedMoment B node3550 node3550Labels = _
    exact sound3550 B hB hF
  have h3552 : mixedVector B (Sum.inr 3552) = Sparse.eval nodeValue3552 (mixedVector B) := by
    change mixedMoment B node3552 node3552Labels = _
    exact sound3552 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm756, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2995, h3507, h3550, h3552, h3572, h4083, reducedSource655] using sourceEq756 B hB

theorem rowSound655 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row655 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck655, numericCheck655, reducedZero655 B hB hF, mul_zero]

theorem sourceRowsAt640 : MixedData.sourceRows (640 : Fin 2425) =
    MixedData.row640 := by decide +kernel

theorem sourceRowsAt641 : MixedData.sourceRows (641 : Fin 2425) =
    MixedData.row641 := by decide +kernel

theorem sourceRowsAt642 : MixedData.sourceRows (642 : Fin 2425) =
    MixedData.row642 := by decide +kernel

theorem sourceRowsAt643 : MixedData.sourceRows (643 : Fin 2425) =
    MixedData.row643 := by decide +kernel

theorem sourceRowsAt644 : MixedData.sourceRows (644 : Fin 2425) =
    MixedData.row644 := by decide +kernel

theorem sourceRowsAt645 : MixedData.sourceRows (645 : Fin 2425) =
    MixedData.row645 := by decide +kernel

theorem sourceRowsAt646 : MixedData.sourceRows (646 : Fin 2425) =
    MixedData.row646 := by decide +kernel

theorem sourceRowsAt647 : MixedData.sourceRows (647 : Fin 2425) =
    MixedData.row647 := by decide +kernel

theorem sourceRowsAt648 : MixedData.sourceRows (648 : Fin 2425) =
    MixedData.row648 := by decide +kernel

theorem sourceRowsAt649 : MixedData.sourceRows (649 : Fin 2425) =
    MixedData.row649 := by decide +kernel

theorem sourceRowsAt650 : MixedData.sourceRows (650 : Fin 2425) =
    MixedData.row650 := by decide +kernel

theorem sourceRowsAt651 : MixedData.sourceRows (651 : Fin 2425) =
    MixedData.row651 := by decide +kernel

theorem sourceRowsAt652 : MixedData.sourceRows (652 : Fin 2425) =
    MixedData.row652 := by decide +kernel

theorem sourceRowsAt653 : MixedData.sourceRows (653 : Fin 2425) =
    MixedData.row653 := by decide +kernel

theorem sourceRowsAt654 : MixedData.sourceRows (654 : Fin 2425) =
    MixedData.row654 := by decide +kernel

theorem sourceRowsAt655 : MixedData.sourceRows (655 : Fin 2425) =
    MixedData.row655 := by decide +kernel

theorem chunkSound40_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 40) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 640 ∨ k.val = 641 ∨ k.val = 642 ∨ k.val = 643 ∨ k.val = 644 ∨ k.val = 645 ∨ k.val = 646 ∨ k.val = 647 ∨ k.val = 648 ∨ k.val = 649 ∨ k.val = 650 ∨ k.val = 651 ∨ k.val = 652 ∨ k.val = 653 ∨ k.val = 654 ∨ k.val = 655 := by omega
  rcases heq with h640 | h641 | h642 | h643 | h644 | h645 | h646 | h647 | h648 | h649 | h650 | h651 | h652 | h653 | h654 | h655
  · have he : k = (640 : Fin 2425) := Fin.ext h640
    subst k
    rw [sourceRowsAt640]
    exact rowSound640 B hB hF
  · have he : k = (641 : Fin 2425) := Fin.ext h641
    subst k
    rw [sourceRowsAt641]
    exact rowSound641 B hB hF
  · have he : k = (642 : Fin 2425) := Fin.ext h642
    subst k
    rw [sourceRowsAt642]
    exact rowSound642 B hB hF
  · have he : k = (643 : Fin 2425) := Fin.ext h643
    subst k
    rw [sourceRowsAt643]
    exact rowSound643_e B hB hF
  · have he : k = (644 : Fin 2425) := Fin.ext h644
    subst k
    rw [sourceRowsAt644]
    exact rowSound644_e B hB hF
  · have he : k = (645 : Fin 2425) := Fin.ext h645
    subst k
    rw [sourceRowsAt645]
    exact rowSound645 B hB hF
  · have he : k = (646 : Fin 2425) := Fin.ext h646
    subst k
    rw [sourceRowsAt646]
    exact rowSound646 B hB hF
  · have he : k = (647 : Fin 2425) := Fin.ext h647
    subst k
    rw [sourceRowsAt647]
    exact rowSound647 B hB hF
  · have he : k = (648 : Fin 2425) := Fin.ext h648
    subst k
    rw [sourceRowsAt648]
    exact rowSound648 B hB hF
  · have he : k = (649 : Fin 2425) := Fin.ext h649
    subst k
    rw [sourceRowsAt649]
    exact rowSound649_e B hB hF
  · have he : k = (650 : Fin 2425) := Fin.ext h650
    subst k
    rw [sourceRowsAt650]
    exact rowSound650 B hB hF
  · have he : k = (651 : Fin 2425) := Fin.ext h651
    subst k
    rw [sourceRowsAt651]
    exact rowSound651 B hB hF
  · have he : k = (652 : Fin 2425) := Fin.ext h652
    subst k
    rw [sourceRowsAt652]
    exact rowSound652 B hB hF
  · have he : k = (653 : Fin 2425) := Fin.ext h653
    subst k
    rw [sourceRowsAt653]
    exact rowSound653 B hB hF
  · have he : k = (654 : Fin 2425) := Fin.ext h654
    subst k
    rw [sourceRowsAt654]
    exact rowSound654 B hB hF
  · have he : k = (655 : Fin 2425) := Fin.ext h655
    subst k
    rw [sourceRowsAt655]
    exact rowSound655 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound40_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound40_e_oai
