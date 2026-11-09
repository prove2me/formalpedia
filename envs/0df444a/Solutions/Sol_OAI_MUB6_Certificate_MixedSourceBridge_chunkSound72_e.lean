-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound72_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:32:45.111502+00:00
-- url     : https://prove2.me/submissions/cc30d9e2-5f95-4329-bce7-8afcd11e1c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1159_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1165_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1166_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1167_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1743 raw1743Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw1743 raw1743Labels = mixedMoment B raw1743step0 raw1743step0Labels := by
      have ha : raw1743step0 = (fun i j => raw1743 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1743step0 raw1743; decide +kernel
      have hl : raw1743step0Labels = raw1743Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1743 raw1743Labels permutation32 permutation4
    mixedMoment B raw1743step0 raw1743step0Labels = mixedMoment B raw1743step1 raw1743step1Labels := by
      have ha : raw1743step1 = raw1743step0 := by apply Matrix.ext; unfold raw1743step1 raw1743step0; decide +kernel
      have hl : raw1743step0Labels = labelEmbedding7 ∘ raw1743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1743step0 raw1743step0Labels raw1743step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical1744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1744 raw1744Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw1744 raw1744Labels = mixedMoment B raw1744step0 raw1744step0Labels := by
      have ha : raw1744step0 = (fun i j => raw1744 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1744step0 raw1744; decide +kernel
      have hl : raw1744step0Labels = raw1744Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1744 raw1744Labels permutation32 permutation4
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical1745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1745 raw1745Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw1745 raw1745Labels = mixedMoment B raw1745step0 raw1745step0Labels := by
      have ha : raw1745step0 = (fun i j => raw1745 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1745step0 raw1745; decide +kernel
      have hl : raw1745step0Labels = raw1745Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1745 raw1745Labels permutation32 permutation6
    mixedMoment B raw1745step0 raw1745step0Labels = mixedMoment B raw1745step1 raw1745step1Labels := by
      have ha : raw1745step1 = -raw1745step0 := by apply Matrix.ext; change ∀ i j, raw1745step1 i j = -(raw1745step0 i j); unfold raw1745step1 raw1745step0; decide +kernel
      have hl : raw1745step1Labels = raw1745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1745step1 raw1745step1Labels = mixedMoment B raw1745step2 raw1745step2Labels := by
      have ha : raw1745step2 = raw1745step1 := by apply Matrix.ext; unfold raw1745step2 raw1745step1; decide +kernel
      have hl : raw1745step1Labels = labelEmbedding1 ∘ raw1745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1745step1 raw1745step1Labels raw1745step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

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

theorem canonical1803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1803 raw1803Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw1803 raw1803Labels = mixedMoment B raw1803step0 raw1803step0Labels := by
      have ha : raw1803step0 = (fun i j => raw1803 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1803step0 raw1803; decide +kernel
      have hl : raw1803step0Labels = raw1803Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1803 raw1803Labels permutation8 permutation4
    mixedMoment B raw1803step0 raw1803step0Labels = mixedMoment B raw1803step1 raw1803step1Labels := by
      have ha : raw1803step1 = raw1803step0 := by apply Matrix.ext; unfold raw1803step1 raw1803step0; decide +kernel
      have hl : raw1803step0Labels = labelEmbedding7 ∘ raw1803step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1803step0 raw1803step0Labels raw1803step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

theorem canonical1804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1804 raw1804Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw1804 raw1804Labels = mixedMoment B raw1804step0 raw1804step0Labels := by
      have ha : raw1804step0 = (fun i j => raw1804 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1804step0 raw1804; decide +kernel
      have hl : raw1804step0Labels = raw1804Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1804 raw1804Labels permutation8 permutation4
    _ = mixedMoment B node2112 node2112Labels := by rfl

theorem canonical1805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1805 raw1805Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw1805 raw1805Labels = mixedMoment B raw1805step0 raw1805step0Labels := by
      have ha : raw1805step0 = (fun i j => raw1805 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1805step0 raw1805; decide +kernel
      have hl : raw1805step0Labels = raw1805Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1805 raw1805Labels permutation8 permutation6
    mixedMoment B raw1805step0 raw1805step0Labels = mixedMoment B raw1805step1 raw1805step1Labels := by
      have ha : raw1805step1 = -raw1805step0 := by apply Matrix.ext; change ∀ i j, raw1805step1 i j = -(raw1805step0 i j); unfold raw1805step1 raw1805step0; decide +kernel
      have hl : raw1805step1Labels = raw1805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1805step1 raw1805step1Labels = mixedMoment B raw1805step2 raw1805step2Labels := by
      have ha : raw1805step2 = raw1805step1 := by apply Matrix.ext; unfold raw1805step2 raw1805step1; decide +kernel
      have hl : raw1805step1Labels = labelEmbedding1 ∘ raw1805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1805step1 raw1805step1Labels raw1805step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

theorem canonical1821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1821 raw1821Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw1821 raw1821Labels = mixedMoment B raw1821step0 raw1821step0Labels := by
      have ha : raw1821step0 = (fun i j => raw1821 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1821step0 raw1821; decide +kernel
      have hl : raw1821step0Labels = raw1821Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1821 raw1821Labels permutation8 permutation4
    mixedMoment B raw1821step0 raw1821step0Labels = mixedMoment B raw1821step1 raw1821step1Labels := by
      have ha : raw1821step1 = raw1821step0 := by apply Matrix.ext; unfold raw1821step1 raw1821step0; decide +kernel
      have hl : raw1821step0Labels = labelEmbedding7 ∘ raw1821step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1821step0 raw1821step0Labels raw1821step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical1822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1822 raw1822Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw1822 raw1822Labels = mixedMoment B raw1822step0 raw1822step0Labels := by
      have ha : raw1822step0 = (fun i j => raw1822 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1822step0 raw1822; decide +kernel
      have hl : raw1822step0Labels = raw1822Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1822 raw1822Labels permutation8 permutation4
    _ = mixedMoment B node2247 node2247Labels := by rfl

theorem canonical1823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1823 raw1823Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw1823 raw1823Labels = mixedMoment B raw1823step0 raw1823step0Labels := by
      have ha : raw1823step0 = (fun i j => raw1823 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1823step0 raw1823; decide +kernel
      have hl : raw1823step0Labels = raw1823Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1823 raw1823Labels permutation8 permutation6
    mixedMoment B raw1823step0 raw1823step0Labels = mixedMoment B raw1823step1 raw1823step1Labels := by
      have ha : raw1823step1 = -raw1823step0 := by apply Matrix.ext; change ∀ i j, raw1823step1 i j = -(raw1823step0 i j); unfold raw1823step1 raw1823step0; decide +kernel
      have hl : raw1823step1Labels = raw1823step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1823step1 raw1823step1Labels = mixedMoment B raw1823step2 raw1823step2Labels := by
      have ha : raw1823step2 = raw1823step1 := by apply Matrix.ext; unfold raw1823step2 raw1823step1; decide +kernel
      have hl : raw1823step1Labels = labelEmbedding1 ∘ raw1823step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1823step1 raw1823step1Labels raw1823step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21111 raw21111Labels = mixedMoment B node1019 node1019Labels := by
  calc
    mixedMoment B raw21111 raw21111Labels = mixedMoment B raw21111step0 raw21111step0Labels := by
      have hz : ∀ j, raw21111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21111step0 = (fun i j => raw21111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21111step0 raw21111; decide +kernel
      have hl : raw21111step0Labels = raw21111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21111 raw21111Labels permutation434 hz
    _ = mixedMoment B node1019 node1019Labels := by rfl

theorem canonical21112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21112 raw21112Labels = mixedMoment B node2087 node2087Labels := by
  calc
    mixedMoment B raw21112 raw21112Labels = mixedMoment B raw21112step0 raw21112step0Labels := by
      have hz : ∀ j, raw21112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21112step0 = (fun i j => raw21112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21112step0 raw21112; decide +kernel
      have hl : raw21112step0Labels = raw21112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21112 raw21112Labels permutation434 hz
    _ = mixedMoment B node2087 node2087Labels := by rfl

theorem canonical21113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21113 raw21113Labels = mixedMoment B node2087 node2087Labels := by
  calc
    mixedMoment B raw21113 raw21113Labels = mixedMoment B raw21113step0 raw21113step0Labels := by
      have hz : ∀ j, raw21113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21113step0 = (fun i j => raw21113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21113step0 raw21113; decide +kernel
      have hl : raw21113step0Labels = raw21113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21113 raw21113Labels permutation434 hz
    mixedMoment B raw21113step0 raw21113step0Labels = mixedMoment B raw21113step1 raw21113step1Labels := by
      have ha : raw21113step1 = (fun i j => raw21113step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21113step1 raw21113step0; decide +kernel
      have hl : raw21113step1Labels = raw21113step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21113step0 raw21113step0Labels permutation38 permutation2
    _ = mixedMoment B node2087 node2087Labels := by rfl

theorem canonical21114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21114 raw21114Labels = mixedMoment B node2008 node2008Labels := by
  calc
    mixedMoment B raw21114 raw21114Labels = mixedMoment B raw21114step0 raw21114step0Labels := by
      have ha : raw21114step0 = (fun i j => raw21114 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21114step0 raw21114; decide +kernel
      have hl : raw21114step0Labels = raw21114Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21114 raw21114Labels permutation200 permutation2
    _ = mixedMoment B node2008 node2008Labels := by rfl

theorem canonical21115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21115 raw21115Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw21115 raw21115Labels = mixedMoment B raw21115step0 raw21115step0Labels := by
      have hz : ∀ j, raw21115 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21115step0 = (fun i j => raw21115 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21115step0 raw21115; decide +kernel
      have hl : raw21115step0Labels = raw21115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21115 raw21115Labels permutation434 hz
    mixedMoment B raw21115step0 raw21115step0Labels = mixedMoment B raw21115step1 raw21115step1Labels := by
      have ha : raw21115step1 = (fun i j => raw21115step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21115step1 raw21115step0; decide +kernel
      have hl : raw21115step1Labels = raw21115step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21115step0 raw21115step0Labels permutation44 permutation2
    _ = mixedMoment B node2193 node2193Labels := by rfl

theorem canonical21116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21116 raw21116Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw21116 raw21116Labels = mixedMoment B raw21116step0 raw21116step0Labels := by
      have hz : ∀ j, raw21116 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21116step0 = (fun i j => raw21116 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21116step0 raw21116; decide +kernel
      have hl : raw21116step0Labels = raw21116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21116 raw21116Labels permutation434 hz
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical21117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21117 raw21117Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw21117 raw21117Labels = mixedMoment B raw21117step0 raw21117step0Labels := by
      have hz : ∀ j, raw21117 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21117step0 = (fun i j => raw21117 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21117step0 raw21117; decide +kernel
      have hl : raw21117step0Labels = raw21117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21117 raw21117Labels permutation434 hz
    mixedMoment B raw21117step0 raw21117step0Labels = mixedMoment B raw21117step1 raw21117step1Labels := by
      have ha : raw21117step1 = (fun i j => raw21117step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21117step1 raw21117step0; decide +kernel
      have hl : raw21117step1Labels = raw21117step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21117step0 raw21117step0Labels permutation44 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical21118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21118 raw21118Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw21118 raw21118Labels = mixedMoment B raw21118step0 raw21118step0Labels := by
      have hz : ∀ j, raw21118 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21118step0 = (fun i j => raw21118 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21118step0 raw21118; decide +kernel
      have hl : raw21118step0Labels = raw21118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21118 raw21118Labels permutation434 hz
    mixedMoment B raw21118step0 raw21118step0Labels = mixedMoment B raw21118step1 raw21118step1Labels := by
      have ha : raw21118step1 = (fun i j => raw21118step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21118step1 raw21118step0; decide +kernel
      have hl : raw21118step1Labels = raw21118step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21118step0 raw21118step0Labels permutation40 permutation2
    _ = mixedMoment B node1035 node1035Labels := by rfl

theorem canonical21119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21119 raw21119Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw21119 raw21119Labels = mixedMoment B raw21119step0 raw21119step0Labels := by
      have hz : ∀ j, raw21119 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21119step0 = (fun i j => raw21119 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21119step0 raw21119; decide +kernel
      have hl : raw21119step0Labels = raw21119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21119 raw21119Labels permutation434 hz
    mixedMoment B raw21119step0 raw21119step0Labels = mixedMoment B raw21119step1 raw21119step1Labels := by
      have ha : raw21119step1 = (fun i j => raw21119step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21119step1 raw21119step0; decide +kernel
      have hl : raw21119step1Labels = raw21119step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21119step0 raw21119step0Labels permutation34 permutation2
    _ = mixedMoment B node1035 node1035Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical165
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21120 raw21120Labels = mixedMoment B node1017 node1017Labels := by
  calc
    mixedMoment B raw21120 raw21120Labels = mixedMoment B raw21120step0 raw21120step0Labels := by
      have ha : raw21120step0 = (fun i j => raw21120 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21120step0 raw21120; decide +kernel
      have hl : raw21120step0Labels = raw21120Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21120 raw21120Labels permutation154 permutation2
    _ = mixedMoment B node1017 node1017Labels := by rfl

theorem canonical21121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21121 raw21121Labels = mixedMoment B node1025 node1025Labels := by
  calc
    mixedMoment B raw21121 raw21121Labels = mixedMoment B raw21121step0 raw21121step0Labels := by
      have hz : ∀ j, raw21121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21121step0 = (fun i j => raw21121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21121step0 raw21121; decide +kernel
      have hl : raw21121step0Labels = raw21121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21121 raw21121Labels permutation434 hz
    _ = mixedMoment B node1025 node1025Labels := by rfl

theorem canonical21122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21122 raw21122Labels = mixedMoment B node972 node972Labels := by
  calc
    mixedMoment B raw21122 raw21122Labels = mixedMoment B raw21122step0 raw21122step0Labels := by
      have ha : raw21122step0 = (fun i j => raw21122 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21122step0 raw21122; decide +kernel
      have hl : raw21122step0Labels = raw21122Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21122 raw21122Labels permutation200 permutation2
    _ = mixedMoment B node972 node972Labels := by rfl

theorem canonical21123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21123 raw21123Labels = mixedMoment B node2071 node2071Labels := by
  calc
    mixedMoment B raw21123 raw21123Labels = mixedMoment B raw21123step0 raw21123step0Labels := by
      have ha : raw21123step0 = (fun i j => raw21123 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21123step0 raw21123; decide +kernel
      have hl : raw21123step0Labels = raw21123Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21123 raw21123Labels permutation158 permutation2
    _ = mixedMoment B node2071 node2071Labels := by rfl

theorem canonical21124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21124 raw21124Labels = mixedMoment B node2071 node2071Labels := by
  calc
    mixedMoment B raw21124 raw21124Labels = mixedMoment B raw21124step0 raw21124step0Labels := by
      have ha : raw21124step0 = (fun i j => raw21124 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21124step0 raw21124; decide +kernel
      have hl : raw21124step0Labels = raw21124Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21124 raw21124Labels permutation182 permutation2
    _ = mixedMoment B node2071 node2071Labels := by rfl

theorem canonical21125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21125 raw21125Labels = mixedMoment B node1898 node1898Labels := by
  calc
    mixedMoment B raw21125 raw21125Labels = mixedMoment B raw21125step0 raw21125step0Labels := by
      have ha : raw21125step0 = (fun i j => raw21125 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21125step0 raw21125; decide +kernel
      have hl : raw21125step0Labels = raw21125Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21125 raw21125Labels permutation200 permutation2
    _ = mixedMoment B node1898 node1898Labels := by rfl

theorem canonical21126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21126 raw21126Labels = mixedMoment B node2187 node2187Labels := by
  calc
    mixedMoment B raw21126 raw21126Labels = mixedMoment B raw21126step0 raw21126step0Labels := by
      have ha : raw21126step0 = (fun i j => raw21126 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21126step0 raw21126; decide +kernel
      have hl : raw21126step0Labels = raw21126Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21126 raw21126Labels permutation200 permutation2
    _ = mixedMoment B node2187 node2187Labels := by rfl

theorem canonical21127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21127 raw21127Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw21127 raw21127Labels = mixedMoment B raw21127step0 raw21127step0Labels := by
      have ha : raw21127step0 = (fun i j => raw21127 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21127step0 raw21127; decide +kernel
      have hl : raw21127step0Labels = raw21127Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21127 raw21127Labels permutation200 permutation2
    _ = mixedMoment B node2191 node2191Labels := by rfl

theorem canonical21128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21128 raw21128Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw21128 raw21128Labels = mixedMoment B raw21128step0 raw21128step0Labels := by
      have ha : raw21128step0 = (fun i j => raw21128 (permutation200 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21128step0 raw21128; decide +kernel
      have hl : raw21128step0Labels = raw21128Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21128 raw21128Labels permutation200 permutation0
    _ = mixedMoment B node4079 node4079Labels := by rfl

theorem canonical21129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21129 raw21129Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw21129 raw21129Labels = mixedMoment B raw21129step0 raw21129step0Labels := by
      have ha : raw21129step0 = (fun i j => raw21129 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21129step0 raw21129; decide +kernel
      have hl : raw21129step0Labels = raw21129Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21129 raw21129Labels permutation206 permutation2
    _ = mixedMoment B node980 node980Labels := by rfl

theorem canonical21130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21130 raw21130Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw21130 raw21130Labels = mixedMoment B raw21130step0 raw21130step0Labels := by
      have ha : raw21130step0 = (fun i j => raw21130 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21130step0 raw21130; decide +kernel
      have hl : raw21130step0Labels = raw21130Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21130 raw21130Labels permutation200 permutation2
    _ = mixedMoment B node980 node980Labels := by rfl

theorem canonical21131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21131 raw21131Labels = mixedMoment B node1018 node1018Labels := by
  calc
    _ = mixedMoment B node1018 node1018Labels := by rfl

theorem canonical21132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21132 raw21132Labels = mixedMoment B node974 node974Labels := by
  calc
    mixedMoment B raw21132 raw21132Labels = mixedMoment B raw21132step0 raw21132step0Labels := by
      have ha : raw21132step0 = (fun i j => raw21132 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21132step0 raw21132; decide +kernel
      have hl : raw21132step0Labels = raw21132Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21132 raw21132Labels permutation200 permutation2
    _ = mixedMoment B node974 node974Labels := by rfl

theorem canonical21133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21133 raw21133Labels = mixedMoment B node971 node971Labels := by
  calc
    mixedMoment B raw21133 raw21133Labels = mixedMoment B raw21133step0 raw21133step0Labels := by
      have ha : raw21133step0 = (fun i j => raw21133 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21133step0 raw21133; decide +kernel
      have hl : raw21133step0Labels = raw21133Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21133 raw21133Labels permutation200 permutation2
    _ = mixedMoment B node971 node971Labels := by rfl

theorem canonical21134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21134 raw21134Labels = mixedMoment B node2070 node2070Labels := by
  calc
    mixedMoment B raw21134 raw21134Labels = mixedMoment B raw21134step0 raw21134step0Labels := by
      have ha : raw21134step0 = (fun i j => raw21134 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21134step0 raw21134; decide +kernel
      have hl : raw21134step0Labels = raw21134Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21134 raw21134Labels permutation158 permutation2
    _ = mixedMoment B node2070 node2070Labels := by rfl

theorem canonical21135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21135 raw21135Labels = mixedMoment B node2070 node2070Labels := by
  calc
    mixedMoment B raw21135 raw21135Labels = mixedMoment B raw21135step0 raw21135step0Labels := by
      have ha : raw21135step0 = (fun i j => raw21135 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21135step0 raw21135; decide +kernel
      have hl : raw21135step0Labels = raw21135Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21135 raw21135Labels permutation182 permutation2
    _ = mixedMoment B node2070 node2070Labels := by rfl

theorem canonical21136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21136 raw21136Labels = mixedMoment B node1897 node1897Labels := by
  calc
    mixedMoment B raw21136 raw21136Labels = mixedMoment B raw21136step0 raw21136step0Labels := by
      have ha : raw21136step0 = (fun i j => raw21136 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21136step0 raw21136; decide +kernel
      have hl : raw21136step0Labels = raw21136Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21136 raw21136Labels permutation200 permutation2
    _ = mixedMoment B node1897 node1897Labels := by rfl

theorem canonical21137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21137 raw21137Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw21137 raw21137Labels = mixedMoment B raw21137step0 raw21137step0Labels := by
      have hz : ∀ j, raw21137 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21137step0 = (fun i j => raw21137 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21137step0 raw21137; decide +kernel
      have hl : raw21137step0Labels = raw21137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21137 raw21137Labels permutation520 hz
    mixedMoment B raw21137step0 raw21137step0Labels = mixedMoment B raw21137step1 raw21137step1Labels := by
      have ha : raw21137step1 = (fun i j => raw21137step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21137step1 raw21137step0; decide +kernel
      have hl : raw21137step1Labels = raw21137step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21137step0 raw21137step0Labels permutation44 permutation2
    _ = mixedMoment B node2193 node2193Labels := by rfl

theorem canonical21138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21138 raw21138Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw21138 raw21138Labels = mixedMoment B raw21138step0 raw21138step0Labels := by
      have ha : raw21138step0 = (fun i j => raw21138 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21138step0 raw21138; decide +kernel
      have hl : raw21138step0Labels = raw21138Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21138 raw21138Labels permutation200 permutation2
    _ = mixedMoment B node2190 node2190Labels := by rfl

theorem canonical21139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21139 raw21139Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw21139 raw21139Labels = mixedMoment B raw21139step0 raw21139step0Labels := by
      have hz : ∀ j, raw21139 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21139step0 = (fun i j => raw21139 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21139step0 raw21139; decide +kernel
      have hl : raw21139step0Labels = raw21139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21139 raw21139Labels permutation520 hz
    mixedMoment B raw21139step0 raw21139step0Labels = mixedMoment B raw21139step1 raw21139step1Labels := by
      have ha : raw21139step1 = (fun i j => raw21139step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21139step1 raw21139step0; decide +kernel
      have hl : raw21139step1Labels = raw21139step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21139step0 raw21139step0Labels permutation44 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical21140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21140 raw21140Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw21140 raw21140Labels = mixedMoment B raw21140step0 raw21140step0Labels := by
      have ha : raw21140step0 = (fun i j => raw21140 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21140step0 raw21140; decide +kernel
      have hl : raw21140step0Labels = raw21140Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21140 raw21140Labels permutation208 permutation2
    _ = mixedMoment B node977 node977Labels := by rfl

theorem canonical21141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21141 raw21141Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw21141 raw21141Labels = mixedMoment B raw21141step0 raw21141step0Labels := by
      have ha : raw21141step0 = (fun i j => raw21141 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21141step0 raw21141; decide +kernel
      have hl : raw21141step0Labels = raw21141Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21141 raw21141Labels permutation202 permutation2
    _ = mixedMoment B node977 node977Labels := by rfl

theorem canonical21142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21142 raw21142Labels = mixedMoment B node1017 node1017Labels := by
  calc
    _ = mixedMoment B node1017 node1017Labels := by rfl

theorem canonical21143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21143 raw21143Labels = mixedMoment B node973 node973Labels := by
  calc
    mixedMoment B raw21143 raw21143Labels = mixedMoment B raw21143step0 raw21143step0Labels := by
      have ha : raw21143step0 = (fun i j => raw21143 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21143step0 raw21143; decide +kernel
      have hl : raw21143step0Labels = raw21143Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21143 raw21143Labels permutation200 permutation2
    _ = mixedMoment B node973 node973Labels := by rfl

theorem canonical21144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21144 raw21144Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw21144 raw21144Labels = mixedMoment B raw21144step0 raw21144step0Labels := by
      have hz : ∀ j, raw21144 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21144step0 = (fun i j => raw21144 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21144step0 raw21144; decide +kernel
      have hl : raw21144step0Labels = raw21144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21144 raw21144Labels permutation434 hz
    mixedMoment B raw21144step0 raw21144step0Labels = mixedMoment B raw21144step1 raw21144step1Labels := by
      have hz : ∀ j, raw21144step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21144step1 = (fun i j => raw21144step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21144step1 raw21144step0; decide +kernel
      have hl : raw21144step1Labels = raw21144step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21144step0 raw21144step0Labels permutation80 hz
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical21145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21145 raw21145Labels = mixedMoment B node4183 node4183Labels := by
  calc
    mixedMoment B raw21145 raw21145Labels = mixedMoment B raw21145step0 raw21145step0Labels := by
      have hz : ∀ j, raw21145 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21145step0 = (fun i j => raw21145 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21145step0 raw21145; decide +kernel
      have hl : raw21145step0Labels = raw21145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21145 raw21145Labels permutation434 hz
    mixedMoment B raw21145step0 raw21145step0Labels = mixedMoment B raw21145step1 raw21145step1Labels := by
      have hz : ∀ j, raw21145step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21145step1 = (fun i j => raw21145step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21145step1 raw21145step0; decide +kernel
      have hl : raw21145step1Labels = raw21145step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21145step0 raw21145step0Labels permutation80 hz
    _ = mixedMoment B node4183 node4183Labels := by rfl

theorem canonical21146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21146 raw21146Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw21146 raw21146Labels = mixedMoment B raw21146step0 raw21146step0Labels := by
      have hz : ∀ j, raw21146 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21146step0 = (fun i j => raw21146 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21146step0 raw21146; decide +kernel
      have hl : raw21146step0Labels = raw21146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21146 raw21146Labels permutation434 hz
    mixedMoment B raw21146step0 raw21146step0Labels = mixedMoment B raw21146step1 raw21146step1Labels := by
      have ha : raw21146step1 = (fun i j => raw21146step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21146step1 raw21146step0; decide +kernel
      have hl : raw21146step1Labels = raw21146step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21146step0 raw21146step0Labels permutation38 permutation2
    _ = mixedMoment B node4352 node4352Labels := by rfl

theorem canonical21147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21147 raw21147Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw21147 raw21147Labels = mixedMoment B raw21147step0 raw21147step0Labels := by
      have hz : ∀ j, raw21147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21147step0 = (fun i j => raw21147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21147step0 raw21147; decide +kernel
      have hl : raw21147step0Labels = raw21147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21147 raw21147Labels permutation346 hz
    mixedMoment B raw21147step0 raw21147step0Labels = mixedMoment B raw21147step1 raw21147step1Labels := by
      have ha : raw21147step1 = (fun i j => raw21147step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21147step1 raw21147step0; decide +kernel
      have hl : raw21147step1Labels = raw21147step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21147step0 raw21147step0Labels permutation38 permutation2
    _ = mixedMoment B node4352 node4352Labels := by rfl

theorem canonical21148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21148 raw21148Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw21148 raw21148Labels = mixedMoment B raw21148step0 raw21148step0Labels := by
      have hz : ∀ j, raw21148 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21148step0 = (fun i j => raw21148 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21148step0 raw21148; decide +kernel
      have hl : raw21148step0Labels = raw21148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21148 raw21148Labels permutation434 hz
    mixedMoment B raw21148step0 raw21148step0Labels = mixedMoment B raw21148step1 raw21148step1Labels := by
      have hz : ∀ j, raw21148step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21148step1 = (fun i j => raw21148step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21148step1 raw21148step0; decide +kernel
      have hl : raw21148step1Labels = raw21148step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21148step0 raw21148step0Labels permutation80 hz
    mixedMoment B raw21148step1 raw21148step1Labels = mixedMoment B raw21148step2 raw21148step2Labels := by
      have ha : raw21148step2 = (fun i j => raw21148step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21148step2 raw21148step1; decide +kernel
      have hl : raw21148step2Labels = raw21148step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21148step1 raw21148step1Labels permutation10 permutation2
    _ = mixedMoment B node4463 node4463Labels := by rfl

theorem canonical21149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21149 raw21149Labels = mixedMoment B node4153 node4153Labels := by
  calc
    mixedMoment B raw21149 raw21149Labels = mixedMoment B raw21149step0 raw21149step0Labels := by
      have hz : ∀ j, raw21149 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21149step0 = (fun i j => raw21149 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21149step0 raw21149; decide +kernel
      have hl : raw21149step0Labels = raw21149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21149 raw21149Labels permutation434 hz
    _ = mixedMoment B node4153 node4153Labels := by rfl

theorem canonical21150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21150 raw21150Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw21150 raw21150Labels = mixedMoment B raw21150step0 raw21150step0Labels := by
      have hz : ∀ j, raw21150 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21150step0 = (fun i j => raw21150 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21150step0 raw21150; decide +kernel
      have hl : raw21150step0Labels = raw21150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21150 raw21150Labels permutation434 hz
    _ = mixedMoment B node4367 node4367Labels := by rfl

theorem canonical21151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21151 raw21151Labels = mixedMoment B node4327 node4327Labels := by
  calc
    mixedMoment B raw21151 raw21151Labels = mixedMoment B raw21151step0 raw21151step0Labels := by
      have ha : raw21151step0 = (fun i j => raw21151 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21151step0 raw21151; decide +kernel
      have hl : raw21151step0Labels = raw21151Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21151 raw21151Labels permutation200 permutation2
    _ = mixedMoment B node4327 node4327Labels := by rfl

theorem canonical21152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21152 raw21152Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw21152 raw21152Labels = mixedMoment B raw21152step0 raw21152step0Labels := by
      have hz : ∀ j, raw21152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21152step0 = (fun i j => raw21152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21152step0 raw21152; decide +kernel
      have hl : raw21152step0Labels = raw21152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21152 raw21152Labels permutation434 hz
    mixedMoment B raw21152step0 raw21152step0Labels = mixedMoment B raw21152step1 raw21152step1Labels := by
      have ha : raw21152step1 = (fun i j => raw21152step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21152step1 raw21152step0; decide +kernel
      have hl : raw21152step1Labels = raw21152step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21152step0 raw21152step0Labels permutation34 permutation2
    _ = mixedMoment B node4440 node4440Labels := by rfl

theorem canonical21153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21153 raw21153Labels = mixedMoment B node4153 node4153Labels := by
  calc
    mixedMoment B raw21153 raw21153Labels = mixedMoment B raw21153step0 raw21153step0Labels := by
      have hz : ∀ j, raw21153 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21153step0 = (fun i j => raw21153 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21153step0 raw21153; decide +kernel
      have hl : raw21153step0Labels = raw21153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21153 raw21153Labels permutation346 hz
    _ = mixedMoment B node4153 node4153Labels := by rfl

theorem canonical21154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21154 raw21154Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw21154 raw21154Labels = mixedMoment B raw21154step0 raw21154step0Labels := by
      have hz : ∀ j, raw21154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21154step0 = (fun i j => raw21154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21154step0 raw21154; decide +kernel
      have hl : raw21154step0Labels = raw21154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21154 raw21154Labels permutation346 hz
    _ = mixedMoment B node4367 node4367Labels := by rfl

theorem canonical21155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21155 raw21155Labels = mixedMoment B node4327 node4327Labels := by
  calc
    mixedMoment B raw21155 raw21155Labels = mixedMoment B raw21155step0 raw21155step0Labels := by
      have ha : raw21155step0 = (fun i j => raw21155 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21155step0 raw21155; decide +kernel
      have hl : raw21155step0Labels = raw21155Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21155 raw21155Labels permutation176 permutation2
    _ = mixedMoment B node4327 node4327Labels := by rfl

theorem canonical21156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21156 raw21156Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw21156 raw21156Labels = mixedMoment B raw21156step0 raw21156step0Labels := by
      have hz : ∀ j, raw21156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21156step0 = (fun i j => raw21156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21156step0 raw21156; decide +kernel
      have hl : raw21156step0Labels = raw21156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21156 raw21156Labels permutation346 hz
    mixedMoment B raw21156step0 raw21156step0Labels = mixedMoment B raw21156step1 raw21156step1Labels := by
      have ha : raw21156step1 = (fun i j => raw21156step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21156step1 raw21156step0; decide +kernel
      have hl : raw21156step1Labels = raw21156step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21156step0 raw21156step0Labels permutation34 permutation2
    _ = mixedMoment B node4440 node4440Labels := by rfl

theorem canonical21157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21157 raw21157Labels = mixedMoment B node4161 node4161Labels := by
  calc
    mixedMoment B raw21157 raw21157Labels = mixedMoment B raw21157step0 raw21157step0Labels := by
      have hz : ∀ j, raw21157 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21157step0 = (fun i j => raw21157 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21157step0 raw21157; decide +kernel
      have hl : raw21157step0Labels = raw21157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21157 raw21157Labels permutation434 hz
    mixedMoment B raw21157step0 raw21157step0Labels = mixedMoment B raw21157step1 raw21157step1Labels := by
      have hz : ∀ j, raw21157step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21157step1 = (fun i j => raw21157step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21157step1 raw21157step0; decide +kernel
      have hl : raw21157step1Labels = raw21157step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21157step0 raw21157step0Labels permutation80 hz
    _ = mixedMoment B node4161 node4161Labels := by rfl

theorem canonical21158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21158 raw21158Labels = mixedMoment B node4374 node4374Labels := by
  calc
    mixedMoment B raw21158 raw21158Labels = mixedMoment B raw21158step0 raw21158step0Labels := by
      have hz : ∀ j, raw21158 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21158step0 = (fun i j => raw21158 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21158step0 raw21158; decide +kernel
      have hl : raw21158step0Labels = raw21158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21158 raw21158Labels permutation434 hz
    mixedMoment B raw21158step0 raw21158step0Labels = mixedMoment B raw21158step1 raw21158step1Labels := by
      have hz : ∀ j, raw21158step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21158step1 = (fun i j => raw21158step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21158step1 raw21158step0; decide +kernel
      have hl : raw21158step1Labels = raw21158step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21158step0 raw21158step0Labels permutation80 hz
    _ = mixedMoment B node4374 node4374Labels := by rfl

theorem canonical21159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21159 raw21159Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw21159 raw21159Labels = mixedMoment B raw21159step0 raw21159step0Labels := by
      have hz : ∀ j, raw21159 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21159step0 = (fun i j => raw21159 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21159step0 raw21159; decide +kernel
      have hl : raw21159step0Labels = raw21159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21159 raw21159Labels permutation434 hz
    mixedMoment B raw21159step0 raw21159step0Labels = mixedMoment B raw21159step1 raw21159step1Labels := by
      have ha : raw21159step1 = (fun i j => raw21159step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21159step1 raw21159step0; decide +kernel
      have hl : raw21159step1Labels = raw21159step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21159step0 raw21159step0Labels permutation38 permutation2
    _ = mixedMoment B node4335 node4335Labels := by rfl

theorem canonical21160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21160 raw21160Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw21160 raw21160Labels = mixedMoment B raw21160step0 raw21160step0Labels := by
      have hz : ∀ j, raw21160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21160step0 = (fun i j => raw21160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21160step0 raw21160; decide +kernel
      have hl : raw21160step0Labels = raw21160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21160 raw21160Labels permutation346 hz
    mixedMoment B raw21160step0 raw21160step0Labels = mixedMoment B raw21160step1 raw21160step1Labels := by
      have ha : raw21160step1 = (fun i j => raw21160step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21160step1 raw21160step0; decide +kernel
      have hl : raw21160step1Labels = raw21160step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21160step0 raw21160step0Labels permutation38 permutation2
    _ = mixedMoment B node4335 node4335Labels := by rfl

theorem canonical21161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21161 raw21161Labels = mixedMoment B node4159 node4159Labels := by
  calc
    mixedMoment B raw21161 raw21161Labels = mixedMoment B raw21161step0 raw21161step0Labels := by
      have hz : ∀ j, raw21161 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21161step0 = (fun i j => raw21161 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21161step0 raw21161; decide +kernel
      have hl : raw21161step0Labels = raw21161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21161 raw21161Labels permutation434 hz
    mixedMoment B raw21161step0 raw21161step0Labels = mixedMoment B raw21161step1 raw21161step1Labels := by
      have hz : ∀ j, raw21161step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21161step1 = (fun i j => raw21161step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21161step1 raw21161step0; decide +kernel
      have hl : raw21161step1Labels = raw21161step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21161step0 raw21161step0Labels permutation80 hz
    _ = mixedMoment B node4159 node4159Labels := by rfl

theorem canonical21162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21162 raw21162Labels = mixedMoment B node4358 node4358Labels := by
  calc
    mixedMoment B raw21162 raw21162Labels = mixedMoment B raw21162step0 raw21162step0Labels := by
      have hz : ∀ j, raw21162 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21162step0 = (fun i j => raw21162 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21162step0 raw21162; decide +kernel
      have hl : raw21162step0Labels = raw21162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21162 raw21162Labels permutation434 hz
    mixedMoment B raw21162step0 raw21162step0Labels = mixedMoment B raw21162step1 raw21162step1Labels := by
      have hz : ∀ j, raw21162step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21162step1 = (fun i j => raw21162step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21162step1 raw21162step0; decide +kernel
      have hl : raw21162step1Labels = raw21162step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21162step0 raw21162step0Labels permutation80 hz
    mixedMoment B raw21162step1 raw21162step1Labels = mixedMoment B raw21162step2 raw21162step2Labels := by
      have ha : raw21162step2 = (fun i j => raw21162step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21162step2 raw21162step1; decide +kernel
      have hl : raw21162step2Labels = raw21162step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21162step1 raw21162step1Labels permutation31 permutation3
    mixedMoment B raw21162step2 raw21162step2Labels = mixedMoment B raw21162step3 raw21162step3Labels := by
      have ha : raw21162step3 = -raw21162step2 := by apply Matrix.ext; change ∀ i j, raw21162step3 i j = -(raw21162step2 i j); unfold raw21162step3 raw21162step2; decide +kernel
      have hl : raw21162step3Labels = raw21162step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21162step3 raw21162step3Labels = mixedMoment B raw21162step4 raw21162step4Labels := by
      have ha : raw21162step4 = raw21162step3 := by apply Matrix.ext; unfold raw21162step4 raw21162step3; decide +kernel
      have hl : raw21162step3Labels = labelEmbedding6 ∘ raw21162step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21162step3 raw21162step3Labels raw21162step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4358 node4358Labels := by rfl

theorem canonical21163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21163 raw21163Labels = mixedMoment B node4333 node4333Labels := by
  calc
    mixedMoment B raw21163 raw21163Labels = mixedMoment B raw21163step0 raw21163step0Labels := by
      have hz : ∀ j, raw21163 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21163step0 = (fun i j => raw21163 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21163step0 raw21163; decide +kernel
      have hl : raw21163step0Labels = raw21163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21163 raw21163Labels permutation434 hz
    mixedMoment B raw21163step0 raw21163step0Labels = mixedMoment B raw21163step1 raw21163step1Labels := by
      have ha : raw21163step1 = (fun i j => raw21163step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21163step1 raw21163step0; decide +kernel
      have hl : raw21163step1Labels = raw21163step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21163step0 raw21163step0Labels permutation38 permutation2
    _ = mixedMoment B node4333 node4333Labels := by rfl

theorem canonical21164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21164 raw21164Labels = mixedMoment B node4333 node4333Labels := by
  calc
    mixedMoment B raw21164 raw21164Labels = mixedMoment B raw21164step0 raw21164step0Labels := by
      have hz : ∀ j, raw21164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21164step0 = (fun i j => raw21164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21164step0 raw21164; decide +kernel
      have hl : raw21164step0Labels = raw21164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21164 raw21164Labels permutation346 hz
    mixedMoment B raw21164step0 raw21164step0Labels = mixedMoment B raw21164step1 raw21164step1Labels := by
      have ha : raw21164step1 = (fun i j => raw21164step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21164step1 raw21164step0; decide +kernel
      have hl : raw21164step1Labels = raw21164step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21164step0 raw21164step0Labels permutation38 permutation2
    _ = mixedMoment B node4333 node4333Labels := by rfl

theorem canonical21165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21165 raw21165Labels = mixedMoment B node4445 node4445Labels := by
  calc
    mixedMoment B raw21165 raw21165Labels = mixedMoment B raw21165step0 raw21165step0Labels := by
      have hz : ∀ j, raw21165 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21165step0 = (fun i j => raw21165 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21165step0 raw21165; decide +kernel
      have hl : raw21165step0Labels = raw21165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21165 raw21165Labels permutation434 hz
    mixedMoment B raw21165step0 raw21165step0Labels = mixedMoment B raw21165step1 raw21165step1Labels := by
      have hz : ∀ j, raw21165step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21165step1 = (fun i j => raw21165step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21165step1 raw21165step0; decide +kernel
      have hl : raw21165step1Labels = raw21165step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21165step0 raw21165step0Labels permutation80 hz
    _ = mixedMoment B node4445 node4445Labels := by rfl

theorem canonical21196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21196 raw21196Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw21196 raw21196Labels = mixedMoment B raw21196step0 raw21196step0Labels := by
      have hz : ∀ j, raw21196 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21196step0 = (fun i j => raw21196 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21196step0 raw21196; decide +kernel
      have hl : raw21196step0Labels = raw21196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21196 raw21196Labels permutation434 hz
    mixedMoment B raw21196step0 raw21196step0Labels = mixedMoment B raw21196step1 raw21196step1Labels := by
      have hz : ∀ j, raw21196step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21196step1 = (fun i j => raw21196step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21196step1 raw21196step0; decide +kernel
      have hl : raw21196step1Labels = raw21196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21196step0 raw21196step0Labels permutation80 hz
    mixedMoment B raw21196step1 raw21196step1Labels = mixedMoment B raw21196step2 raw21196step2Labels := by
      have ha : raw21196step2 = (fun i j => raw21196step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21196step2 raw21196step1; decide +kernel
      have hl : raw21196step2Labels = raw21196step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21196step1 raw21196step1Labels permutation8 permutation7
    mixedMoment B raw21196step2 raw21196step2Labels = mixedMoment B raw21196step3 raw21196step3Labels := by
      have ha : raw21196step3 = -raw21196step2 := by apply Matrix.ext; change ∀ i j, raw21196step3 i j = -(raw21196step2 i j); unfold raw21196step3 raw21196step2; decide +kernel
      have hl : raw21196step3Labels = raw21196step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21196step3 raw21196step3Labels = mixedMoment B raw21196step4 raw21196step4Labels := by
      have ha : raw21196step4 = raw21196step3 := by apply Matrix.ext; unfold raw21196step4 raw21196step3; decide +kernel
      have hl : raw21196step3Labels = labelEmbedding1 ∘ raw21196step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21196step3 raw21196step3Labels raw21196step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical21197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21197 raw21197Labels = mixedMoment B node1535 node1535Labels := by
  calc
    mixedMoment B raw21197 raw21197Labels = mixedMoment B raw21197step0 raw21197step0Labels := by
      have hz : ∀ j, raw21197 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21197step0 = (fun i j => raw21197 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21197step0 raw21197; decide +kernel
      have hl : raw21197step0Labels = raw21197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21197 raw21197Labels permutation434 hz
    mixedMoment B raw21197step0 raw21197step0Labels = mixedMoment B raw21197step1 raw21197step1Labels := by
      have hz : ∀ j, raw21197step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21197step1 = (fun i j => raw21197step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21197step1 raw21197step0; decide +kernel
      have hl : raw21197step1Labels = raw21197step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21197step0 raw21197step0Labels permutation80 hz
    mixedMoment B raw21197step1 raw21197step1Labels = mixedMoment B raw21197step2 raw21197step2Labels := by
      have ha : raw21197step2 = (fun i j => raw21197step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21197step2 raw21197step1; decide +kernel
      have hl : raw21197step2Labels = raw21197step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21197step1 raw21197step1Labels permutation8 permutation7
    mixedMoment B raw21197step2 raw21197step2Labels = mixedMoment B raw21197step3 raw21197step3Labels := by
      have ha : raw21197step3 = -raw21197step2 := by apply Matrix.ext; change ∀ i j, raw21197step3 i j = -(raw21197step2 i j); unfold raw21197step3 raw21197step2; decide +kernel
      have hl : raw21197step3Labels = raw21197step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21197step3 raw21197step3Labels = mixedMoment B raw21197step4 raw21197step4Labels := by
      have ha : raw21197step4 = raw21197step3 := by apply Matrix.ext; unfold raw21197step4 raw21197step3; decide +kernel
      have hl : raw21197step3Labels = labelEmbedding1 ∘ raw21197step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21197step3 raw21197step3Labels raw21197step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1535 node1535Labels := by rfl

theorem canonical21198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21198 raw21198Labels = mixedMoment B node1690 node1690Labels := by
  calc
    mixedMoment B raw21198 raw21198Labels = mixedMoment B raw21198step0 raw21198step0Labels := by
      have hz : ∀ j, raw21198 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21198step0 = (fun i j => raw21198 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21198step0 raw21198; decide +kernel
      have hl : raw21198step0Labels = raw21198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21198 raw21198Labels permutation434 hz
    mixedMoment B raw21198step0 raw21198step0Labels = mixedMoment B raw21198step1 raw21198step1Labels := by
      have ha : raw21198step1 = (fun i j => raw21198step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21198step1 raw21198step0; decide +kernel
      have hl : raw21198step1Labels = raw21198step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21198step0 raw21198step0Labels permutation38 permutation7
    mixedMoment B raw21198step1 raw21198step1Labels = mixedMoment B raw21198step2 raw21198step2Labels := by
      have ha : raw21198step2 = -raw21198step1 := by apply Matrix.ext; change ∀ i j, raw21198step2 i j = -(raw21198step1 i j); unfold raw21198step2 raw21198step1; decide +kernel
      have hl : raw21198step2Labels = raw21198step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21198step2 raw21198step2Labels = mixedMoment B raw21198step3 raw21198step3Labels := by
      have ha : raw21198step3 = raw21198step2 := by apply Matrix.ext; unfold raw21198step3 raw21198step2; decide +kernel
      have hl : raw21198step2Labels = labelEmbedding1 ∘ raw21198step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21198step2 raw21198step2Labels raw21198step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1690 node1690Labels := by rfl

theorem canonical21199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21199 raw21199Labels = mixedMoment B node1690 node1690Labels := by
  calc
    mixedMoment B raw21199 raw21199Labels = mixedMoment B raw21199step0 raw21199step0Labels := by
      have hz : ∀ j, raw21199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21199step0 = (fun i j => raw21199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21199step0 raw21199; decide +kernel
      have hl : raw21199step0Labels = raw21199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21199 raw21199Labels permutation346 hz
    mixedMoment B raw21199step0 raw21199step0Labels = mixedMoment B raw21199step1 raw21199step1Labels := by
      have ha : raw21199step1 = (fun i j => raw21199step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21199step1 raw21199step0; decide +kernel
      have hl : raw21199step1Labels = raw21199step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21199step0 raw21199step0Labels permutation38 permutation7
    mixedMoment B raw21199step1 raw21199step1Labels = mixedMoment B raw21199step2 raw21199step2Labels := by
      have ha : raw21199step2 = -raw21199step1 := by apply Matrix.ext; change ∀ i j, raw21199step2 i j = -(raw21199step1 i j); unfold raw21199step2 raw21199step1; decide +kernel
      have hl : raw21199step2Labels = raw21199step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21199step2 raw21199step2Labels = mixedMoment B raw21199step3 raw21199step3Labels := by
      have ha : raw21199step3 = raw21199step2 := by apply Matrix.ext; unfold raw21199step3 raw21199step2; decide +kernel
      have hl : raw21199step2Labels = labelEmbedding1 ∘ raw21199step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21199step2 raw21199step2Labels raw21199step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1690 node1690Labels := by rfl

theorem canonical21200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21200 raw21200Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw21200 raw21200Labels = mixedMoment B raw21200step0 raw21200step0Labels := by
      have hz : ∀ j, raw21200 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21200step0 = (fun i j => raw21200 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21200step0 raw21200; decide +kernel
      have hl : raw21200step0Labels = raw21200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21200 raw21200Labels permutation434 hz
    mixedMoment B raw21200step0 raw21200step0Labels = mixedMoment B raw21200step1 raw21200step1Labels := by
      have hz : ∀ j, raw21200step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21200step1 = (fun i j => raw21200step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21200step1 raw21200step0; decide +kernel
      have hl : raw21200step1Labels = raw21200step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21200step0 raw21200step0Labels permutation80 hz
    mixedMoment B raw21200step1 raw21200step1Labels = mixedMoment B raw21200step2 raw21200step2Labels := by
      have ha : raw21200step2 = (fun i j => raw21200step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21200step2 raw21200step1; decide +kernel
      have hl : raw21200step2Labels = raw21200step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21200step1 raw21200step1Labels permutation10 permutation7
    mixedMoment B raw21200step2 raw21200step2Labels = mixedMoment B raw21200step3 raw21200step3Labels := by
      have ha : raw21200step3 = -raw21200step2 := by apply Matrix.ext; change ∀ i j, raw21200step3 i j = -(raw21200step2 i j); unfold raw21200step3 raw21200step2; decide +kernel
      have hl : raw21200step3Labels = raw21200step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21200step3 raw21200step3Labels = mixedMoment B raw21200step4 raw21200step4Labels := by
      have ha : raw21200step4 = raw21200step3 := by apply Matrix.ext; unfold raw21200step4 raw21200step3; decide +kernel
      have hl : raw21200step3Labels = labelEmbedding1 ∘ raw21200step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21200step3 raw21200step3Labels raw21200step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical21201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21201 raw21201Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw21201 raw21201Labels = mixedMoment B raw21201step0 raw21201step0Labels := by
      have hz : ∀ j, raw21201 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21201step0 = (fun i j => raw21201 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21201step0 raw21201; decide +kernel
      have hl : raw21201step0Labels = raw21201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21201 raw21201Labels permutation434 hz
    mixedMoment B raw21201step0 raw21201step0Labels = mixedMoment B raw21201step1 raw21201step1Labels := by
      have ha : raw21201step1 = (fun i j => raw21201step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21201step1 raw21201step0; decide +kernel
      have hl : raw21201step1Labels = raw21201step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21201step0 raw21201step0Labels permutation38 permutation7
    mixedMoment B raw21201step1 raw21201step1Labels = mixedMoment B raw21201step2 raw21201step2Labels := by
      have ha : raw21201step2 = -raw21201step1 := by apply Matrix.ext; change ∀ i j, raw21201step2 i j = -(raw21201step1 i j); unfold raw21201step2 raw21201step1; decide +kernel
      have hl : raw21201step2Labels = raw21201step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21201step2 raw21201step2Labels = mixedMoment B raw21201step3 raw21201step3Labels := by
      have ha : raw21201step3 = raw21201step2 := by apply Matrix.ext; unfold raw21201step3 raw21201step2; decide +kernel
      have hl : raw21201step2Labels = labelEmbedding1 ∘ raw21201step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21201step2 raw21201step2Labels raw21201step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1514 node1514Labels := by rfl

theorem canonical21202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21202 raw21202Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw21202 raw21202Labels = mixedMoment B raw21202step0 raw21202step0Labels := by
      have hz : ∀ j, raw21202 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21202step0 = (fun i j => raw21202 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21202step0 raw21202; decide +kernel
      have hl : raw21202step0Labels = raw21202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21202 raw21202Labels permutation434 hz
    mixedMoment B raw21202step0 raw21202step0Labels = mixedMoment B raw21202step1 raw21202step1Labels := by
      have ha : raw21202step1 = (fun i j => raw21202step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21202step1 raw21202step0; decide +kernel
      have hl : raw21202step1Labels = raw21202step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21202step0 raw21202step0Labels permutation38 permutation7
    mixedMoment B raw21202step1 raw21202step1Labels = mixedMoment B raw21202step2 raw21202step2Labels := by
      have ha : raw21202step2 = -raw21202step1 := by apply Matrix.ext; change ∀ i j, raw21202step2 i j = -(raw21202step1 i j); unfold raw21202step2 raw21202step1; decide +kernel
      have hl : raw21202step2Labels = raw21202step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21202step2 raw21202step2Labels = mixedMoment B raw21202step3 raw21202step3Labels := by
      have ha : raw21202step3 = raw21202step2 := by apply Matrix.ext; unfold raw21202step3 raw21202step2; decide +kernel
      have hl : raw21202step2Labels = labelEmbedding1 ∘ raw21202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21202step2 raw21202step2Labels raw21202step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

theorem canonical21203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21203 raw21203Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw21203 raw21203Labels = mixedMoment B raw21203step0 raw21203step0Labels := by
      have ha : raw21203step0 = (fun i j => raw21203 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21203step0 raw21203; decide +kernel
      have hl : raw21203step0Labels = raw21203Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21203 raw21203Labels permutation206 permutation7
    mixedMoment B raw21203step0 raw21203step0Labels = mixedMoment B raw21203step1 raw21203step1Labels := by
      have ha : raw21203step1 = -raw21203step0 := by apply Matrix.ext; change ∀ i j, raw21203step1 i j = -(raw21203step0 i j); unfold raw21203step1 raw21203step0; decide +kernel
      have hl : raw21203step1Labels = raw21203step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21203step1 raw21203step1Labels = mixedMoment B raw21203step2 raw21203step2Labels := by
      have ha : raw21203step2 = raw21203step1 := by apply Matrix.ext; unfold raw21203step2 raw21203step1; decide +kernel
      have hl : raw21203step1Labels = labelEmbedding1 ∘ raw21203step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21203step1 raw21203step1Labels raw21203step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

theorem canonical21204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21204 raw21204Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw21204 raw21204Labels = mixedMoment B raw21204step0 raw21204step0Labels := by
      have hz : ∀ j, raw21204 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21204step0 = (fun i j => raw21204 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21204step0 raw21204; decide +kernel
      have hl : raw21204step0Labels = raw21204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21204 raw21204Labels permutation434 hz
    mixedMoment B raw21204step0 raw21204step0Labels = mixedMoment B raw21204step1 raw21204step1Labels := by
      have ha : raw21204step1 = (fun i j => raw21204step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21204step1 raw21204step0; decide +kernel
      have hl : raw21204step1Labels = raw21204step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21204step0 raw21204step0Labels permutation38 permutation7
    mixedMoment B raw21204step1 raw21204step1Labels = mixedMoment B raw21204step2 raw21204step2Labels := by
      have ha : raw21204step2 = -raw21204step1 := by apply Matrix.ext; change ∀ i j, raw21204step2 i j = -(raw21204step1 i j); unfold raw21204step2 raw21204step1; decide +kernel
      have hl : raw21204step2Labels = raw21204step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21204step2 raw21204step2Labels = mixedMoment B raw21204step3 raw21204step3Labels := by
      have ha : raw21204step3 = raw21204step2 := by apply Matrix.ext; unfold raw21204step3 raw21204step2; decide +kernel
      have hl : raw21204step2Labels = labelEmbedding1 ∘ raw21204step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21204step2 raw21204step2Labels raw21204step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

theorem canonical21205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21205 raw21205Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw21205 raw21205Labels = mixedMoment B raw21205step0 raw21205step0Labels := by
      have hz : ∀ j, raw21205 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21205step0 = (fun i j => raw21205 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21205step0 raw21205; decide +kernel
      have hl : raw21205step0Labels = raw21205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21205 raw21205Labels permutation346 hz
    mixedMoment B raw21205step0 raw21205step0Labels = mixedMoment B raw21205step1 raw21205step1Labels := by
      have ha : raw21205step1 = (fun i j => raw21205step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21205step1 raw21205step0; decide +kernel
      have hl : raw21205step1Labels = raw21205step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21205step0 raw21205step0Labels permutation38 permutation7
    mixedMoment B raw21205step1 raw21205step1Labels = mixedMoment B raw21205step2 raw21205step2Labels := by
      have ha : raw21205step2 = -raw21205step1 := by apply Matrix.ext; change ∀ i j, raw21205step2 i j = -(raw21205step1 i j); unfold raw21205step2 raw21205step1; decide +kernel
      have hl : raw21205step2Labels = raw21205step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21205step2 raw21205step2Labels = mixedMoment B raw21205step3 raw21205step3Labels := by
      have ha : raw21205step3 = raw21205step2 := by apply Matrix.ext; unfold raw21205step3 raw21205step2; decide +kernel
      have hl : raw21205step2Labels = labelEmbedding1 ∘ raw21205step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21205step2 raw21205step2Labels raw21205step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1514 node1514Labels := by rfl

theorem canonical21206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21206 raw21206Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw21206 raw21206Labels = mixedMoment B raw21206step0 raw21206step0Labels := by
      have hz : ∀ j, raw21206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21206step0 = (fun i j => raw21206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21206step0 raw21206; decide +kernel
      have hl : raw21206step0Labels = raw21206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21206 raw21206Labels permutation346 hz
    mixedMoment B raw21206step0 raw21206step0Labels = mixedMoment B raw21206step1 raw21206step1Labels := by
      have ha : raw21206step1 = (fun i j => raw21206step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21206step1 raw21206step0; decide +kernel
      have hl : raw21206step1Labels = raw21206step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21206step0 raw21206step0Labels permutation38 permutation7
    mixedMoment B raw21206step1 raw21206step1Labels = mixedMoment B raw21206step2 raw21206step2Labels := by
      have ha : raw21206step2 = -raw21206step1 := by apply Matrix.ext; change ∀ i j, raw21206step2 i j = -(raw21206step1 i j); unfold raw21206step2 raw21206step1; decide +kernel
      have hl : raw21206step2Labels = raw21206step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21206step2 raw21206step2Labels = mixedMoment B raw21206step3 raw21206step3Labels := by
      have ha : raw21206step3 = raw21206step2 := by apply Matrix.ext; unfold raw21206step3 raw21206step2; decide +kernel
      have hl : raw21206step2Labels = labelEmbedding1 ∘ raw21206step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21206step2 raw21206step2Labels raw21206step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

theorem canonical21207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21207 raw21207Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw21207 raw21207Labels = mixedMoment B raw21207step0 raw21207step0Labels := by
      have ha : raw21207step0 = (fun i j => raw21207 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21207step0 raw21207; decide +kernel
      have hl : raw21207step0Labels = raw21207Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21207 raw21207Labels permutation182 permutation7
    mixedMoment B raw21207step0 raw21207step0Labels = mixedMoment B raw21207step1 raw21207step1Labels := by
      have ha : raw21207step1 = -raw21207step0 := by apply Matrix.ext; change ∀ i j, raw21207step1 i j = -(raw21207step0 i j); unfold raw21207step1 raw21207step0; decide +kernel
      have hl : raw21207step1Labels = raw21207step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21207step1 raw21207step1Labels = mixedMoment B raw21207step2 raw21207step2Labels := by
      have ha : raw21207step2 = raw21207step1 := by apply Matrix.ext; unfold raw21207step2 raw21207step1; decide +kernel
      have hl : raw21207step1Labels = labelEmbedding1 ∘ raw21207step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21207step1 raw21207step1Labels raw21207step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

theorem canonical21208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21208 raw21208Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw21208 raw21208Labels = mixedMoment B raw21208step0 raw21208step0Labels := by
      have hz : ∀ j, raw21208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21208step0 = (fun i j => raw21208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21208step0 raw21208; decide +kernel
      have hl : raw21208step0Labels = raw21208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21208 raw21208Labels permutation346 hz
    mixedMoment B raw21208step0 raw21208step0Labels = mixedMoment B raw21208step1 raw21208step1Labels := by
      have ha : raw21208step1 = (fun i j => raw21208step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21208step1 raw21208step0; decide +kernel
      have hl : raw21208step1Labels = raw21208step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21208step0 raw21208step0Labels permutation38 permutation7
    mixedMoment B raw21208step1 raw21208step1Labels = mixedMoment B raw21208step2 raw21208step2Labels := by
      have ha : raw21208step2 = -raw21208step1 := by apply Matrix.ext; change ∀ i j, raw21208step2 i j = -(raw21208step1 i j); unfold raw21208step2 raw21208step1; decide +kernel
      have hl : raw21208step2Labels = raw21208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21208step2 raw21208step2Labels = mixedMoment B raw21208step3 raw21208step3Labels := by
      have ha : raw21208step3 = raw21208step2 := by apply Matrix.ext; unfold raw21208step3 raw21208step2; decide +kernel
      have hl : raw21208step2Labels = labelEmbedding1 ∘ raw21208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21208step2 raw21208step2Labels raw21208step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

theorem canonical21209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21209 raw21209Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw21209 raw21209Labels = mixedMoment B raw21209step0 raw21209step0Labels := by
      have hz : ∀ j, raw21209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21209step0 = (fun i j => raw21209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21209step0 raw21209; decide +kernel
      have hl : raw21209step0Labels = raw21209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21209 raw21209Labels permutation434 hz
    mixedMoment B raw21209step0 raw21209step0Labels = mixedMoment B raw21209step1 raw21209step1Labels := by
      have hz : ∀ j, raw21209step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21209step1 = (fun i j => raw21209step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21209step1 raw21209step0; decide +kernel
      have hl : raw21209step1Labels = raw21209step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21209step0 raw21209step0Labels permutation80 hz
    mixedMoment B raw21209step1 raw21209step1Labels = mixedMoment B raw21209step2 raw21209step2Labels := by
      have ha : raw21209step2 = (fun i j => raw21209step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21209step2 raw21209step1; decide +kernel
      have hl : raw21209step2Labels = raw21209step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21209step1 raw21209step1Labels permutation8 permutation7
    mixedMoment B raw21209step2 raw21209step2Labels = mixedMoment B raw21209step3 raw21209step3Labels := by
      have ha : raw21209step3 = -raw21209step2 := by apply Matrix.ext; change ∀ i j, raw21209step3 i j = -(raw21209step2 i j); unfold raw21209step3 raw21209step2; decide +kernel
      have hl : raw21209step3Labels = raw21209step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21209step3 raw21209step3Labels = mixedMoment B raw21209step4 raw21209step4Labels := by
      have ha : raw21209step4 = raw21209step3 := by apply Matrix.ext; unfold raw21209step4 raw21209step3; decide +kernel
      have hl : raw21209step3Labels = labelEmbedding1 ∘ raw21209step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21209step3 raw21209step3Labels raw21209step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1533 node1533Labels := by rfl

theorem canonical21210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21210 raw21210Labels = mixedMoment B node1748 node1748Labels := by
  calc
    mixedMoment B raw21210 raw21210Labels = mixedMoment B raw21210step0 raw21210step0Labels := by
      have hz : ∀ j, raw21210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21210step0 = (fun i j => raw21210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21210step0 raw21210; decide +kernel
      have hl : raw21210step0Labels = raw21210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21210 raw21210Labels permutation434 hz
    mixedMoment B raw21210step0 raw21210step0Labels = mixedMoment B raw21210step1 raw21210step1Labels := by
      have hz : ∀ j, raw21210step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21210step1 = (fun i j => raw21210step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21210step1 raw21210step0; decide +kernel
      have hl : raw21210step1Labels = raw21210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21210step0 raw21210step0Labels permutation80 hz
    mixedMoment B raw21210step1 raw21210step1Labels = mixedMoment B raw21210step2 raw21210step2Labels := by
      have ha : raw21210step2 = (fun i j => raw21210step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21210step2 raw21210step1; decide +kernel
      have hl : raw21210step2Labels = raw21210step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21210step1 raw21210step1Labels permutation8 permutation7
    mixedMoment B raw21210step2 raw21210step2Labels = mixedMoment B raw21210step3 raw21210step3Labels := by
      have ha : raw21210step3 = -raw21210step2 := by apply Matrix.ext; change ∀ i j, raw21210step3 i j = -(raw21210step2 i j); unfold raw21210step3 raw21210step2; decide +kernel
      have hl : raw21210step3Labels = raw21210step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21210step3 raw21210step3Labels = mixedMoment B raw21210step4 raw21210step4Labels := by
      have ha : raw21210step4 = raw21210step3 := by apply Matrix.ext; unfold raw21210step4 raw21210step3; decide +kernel
      have hl : raw21210step3Labels = labelEmbedding1 ∘ raw21210step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21210step3 raw21210step3Labels raw21210step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1748 node1748Labels := by rfl

theorem canonical21211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21211 raw21211Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw21211 raw21211Labels = mixedMoment B raw21211step0 raw21211step0Labels := by
      have hz : ∀ j, raw21211 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21211step0 = (fun i j => raw21211 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21211step0 raw21211; decide +kernel
      have hl : raw21211step0Labels = raw21211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21211 raw21211Labels permutation434 hz
    mixedMoment B raw21211step0 raw21211step0Labels = mixedMoment B raw21211step1 raw21211step1Labels := by
      have ha : raw21211step1 = (fun i j => raw21211step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21211step1 raw21211step0; decide +kernel
      have hl : raw21211step1Labels = raw21211step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21211step0 raw21211step0Labels permutation38 permutation7
    mixedMoment B raw21211step1 raw21211step1Labels = mixedMoment B raw21211step2 raw21211step2Labels := by
      have ha : raw21211step2 = -raw21211step1 := by apply Matrix.ext; change ∀ i j, raw21211step2 i j = -(raw21211step1 i j); unfold raw21211step2 raw21211step1; decide +kernel
      have hl : raw21211step2Labels = raw21211step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21211step2 raw21211step2Labels = mixedMoment B raw21211step3 raw21211step3Labels := by
      have ha : raw21211step3 = raw21211step2 := by apply Matrix.ext; unfold raw21211step3 raw21211step2; decide +kernel
      have hl : raw21211step2Labels = labelEmbedding1 ∘ raw21211step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21211step2 raw21211step2Labels raw21211step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

theorem canonical21212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21212 raw21212Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw21212 raw21212Labels = mixedMoment B raw21212step0 raw21212step0Labels := by
      have hz : ∀ j, raw21212 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21212step0 = (fun i j => raw21212 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21212step0 raw21212; decide +kernel
      have hl : raw21212step0Labels = raw21212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21212 raw21212Labels permutation346 hz
    mixedMoment B raw21212step0 raw21212step0Labels = mixedMoment B raw21212step1 raw21212step1Labels := by
      have ha : raw21212step1 = (fun i j => raw21212step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21212step1 raw21212step0; decide +kernel
      have hl : raw21212step1Labels = raw21212step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21212step0 raw21212step0Labels permutation38 permutation7
    mixedMoment B raw21212step1 raw21212step1Labels = mixedMoment B raw21212step2 raw21212step2Labels := by
      have ha : raw21212step2 = -raw21212step1 := by apply Matrix.ext; change ∀ i j, raw21212step2 i j = -(raw21212step1 i j); unfold raw21212step2 raw21212step1; decide +kernel
      have hl : raw21212step2Labels = raw21212step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21212step2 raw21212step2Labels = mixedMoment B raw21212step3 raw21212step3Labels := by
      have ha : raw21212step3 = raw21212step2 := by apply Matrix.ext; unfold raw21212step3 raw21212step2; decide +kernel
      have hl : raw21212step2Labels = labelEmbedding1 ∘ raw21212step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21212step2 raw21212step2Labels raw21212step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

theorem canonical21213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21213 raw21213Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw21213 raw21213Labels = mixedMoment B raw21213step0 raw21213step0Labels := by
      have hz : ∀ j, raw21213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21213step0 = (fun i j => raw21213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21213step0 raw21213; decide +kernel
      have hl : raw21213step0Labels = raw21213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21213 raw21213Labels permutation434 hz
    mixedMoment B raw21213step0 raw21213step0Labels = mixedMoment B raw21213step1 raw21213step1Labels := by
      have hz : ∀ j, raw21213step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21213step1 = (fun i j => raw21213step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21213step1 raw21213step0; decide +kernel
      have hl : raw21213step1Labels = raw21213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21213step0 raw21213step0Labels permutation80 hz
    mixedMoment B raw21213step1 raw21213step1Labels = mixedMoment B raw21213step2 raw21213step2Labels := by
      have ha : raw21213step2 = (fun i j => raw21213step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21213step2 raw21213step1; decide +kernel
      have hl : raw21213step2Labels = raw21213step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21213step1 raw21213step1Labels permutation8 permutation7
    mixedMoment B raw21213step2 raw21213step2Labels = mixedMoment B raw21213step3 raw21213step3Labels := by
      have ha : raw21213step3 = -raw21213step2 := by apply Matrix.ext; change ∀ i j, raw21213step3 i j = -(raw21213step2 i j); unfold raw21213step3 raw21213step2; decide +kernel
      have hl : raw21213step3Labels = raw21213step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21213step3 raw21213step3Labels = mixedMoment B raw21213step4 raw21213step4Labels := by
      have ha : raw21213step4 = raw21213step3 := by apply Matrix.ext; unfold raw21213step4 raw21213step3; decide +kernel
      have hl : raw21213step3Labels = labelEmbedding1 ∘ raw21213step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21213step3 raw21213step3Labels raw21213step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1532 node1532Labels := by rfl

theorem canonical21214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21214 raw21214Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw21214 raw21214Labels = mixedMoment B raw21214step0 raw21214step0Labels := by
      have hz : ∀ j, raw21214 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21214step0 = (fun i j => raw21214 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21214step0 raw21214; decide +kernel
      have hl : raw21214step0Labels = raw21214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21214 raw21214Labels permutation434 hz
    mixedMoment B raw21214step0 raw21214step0Labels = mixedMoment B raw21214step1 raw21214step1Labels := by
      have hz : ∀ j, raw21214step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21214step1 = (fun i j => raw21214step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21214step1 raw21214step0; decide +kernel
      have hl : raw21214step1Labels = raw21214step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21214step0 raw21214step0Labels permutation80 hz
    mixedMoment B raw21214step1 raw21214step1Labels = mixedMoment B raw21214step2 raw21214step2Labels := by
      have ha : raw21214step2 = (fun i j => raw21214step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw21214step2 raw21214step1; decide +kernel
      have hl : raw21214step2Labels = raw21214step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21214step1 raw21214step1Labels permutation30 permutation5
    mixedMoment B raw21214step2 raw21214step2Labels = mixedMoment B raw21214step3 raw21214step3Labels := by
      have ha : raw21214step3 = raw21214step2 := by apply Matrix.ext; unfold raw21214step3 raw21214step2; decide +kernel
      have hl : raw21214step2Labels = labelEmbedding1 ∘ raw21214step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21214step2 raw21214step2Labels raw21214step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1695 node1695Labels := by rfl

theorem canonical21215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21215 raw21215Labels = mixedMoment B node1688 node1688Labels := by
  calc
    mixedMoment B raw21215 raw21215Labels = mixedMoment B raw21215step0 raw21215step0Labels := by
      have hz : ∀ j, raw21215 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21215step0 = (fun i j => raw21215 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21215step0 raw21215; decide +kernel
      have hl : raw21215step0Labels = raw21215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21215 raw21215Labels permutation434 hz
    mixedMoment B raw21215step0 raw21215step0Labels = mixedMoment B raw21215step1 raw21215step1Labels := by
      have ha : raw21215step1 = (fun i j => raw21215step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw21215step1 raw21215step0; decide +kernel
      have hl : raw21215step1Labels = raw21215step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21215step0 raw21215step0Labels permutation149 permutation5
    mixedMoment B raw21215step1 raw21215step1Labels = mixedMoment B raw21215step2 raw21215step2Labels := by
      have ha : raw21215step2 = raw21215step1 := by apply Matrix.ext; unfold raw21215step2 raw21215step1; decide +kernel
      have hl : raw21215step1Labels = labelEmbedding1 ∘ raw21215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21215step1 raw21215step1Labels raw21215step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1688 node1688Labels := by rfl

theorem canonical21216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21216 raw21216Labels = mixedMoment B node1688 node1688Labels := by
  calc
    mixedMoment B raw21216 raw21216Labels = mixedMoment B raw21216step0 raw21216step0Labels := by
      have hz : ∀ j, raw21216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21216step0 = (fun i j => raw21216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21216step0 raw21216; decide +kernel
      have hl : raw21216step0Labels = raw21216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21216 raw21216Labels permutation346 hz
    mixedMoment B raw21216step0 raw21216step0Labels = mixedMoment B raw21216step1 raw21216step1Labels := by
      have ha : raw21216step1 = (fun i j => raw21216step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw21216step1 raw21216step0; decide +kernel
      have hl : raw21216step1Labels = raw21216step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21216step0 raw21216step0Labels permutation149 permutation5
    mixedMoment B raw21216step1 raw21216step1Labels = mixedMoment B raw21216step2 raw21216step2Labels := by
      have ha : raw21216step2 = raw21216step1 := by apply Matrix.ext; unfold raw21216step2 raw21216step1; decide +kernel
      have hl : raw21216step1Labels = labelEmbedding1 ∘ raw21216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21216step1 raw21216step1Labels raw21216step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1688 node1688Labels := by rfl

theorem canonical21217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21217 raw21217Labels = mixedMoment B node1749 node1749Labels := by
  calc
    mixedMoment B raw21217 raw21217Labels = mixedMoment B raw21217step0 raw21217step0Labels := by
      have hz : ∀ j, raw21217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21217step0 = (fun i j => raw21217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21217step0 raw21217; decide +kernel
      have hl : raw21217step0Labels = raw21217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21217 raw21217Labels permutation434 hz
    mixedMoment B raw21217step0 raw21217step0Labels = mixedMoment B raw21217step1 raw21217step1Labels := by
      have hz : ∀ j, raw21217step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21217step1 = (fun i j => raw21217step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21217step1 raw21217step0; decide +kernel
      have hl : raw21217step1Labels = raw21217step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21217step0 raw21217step0Labels permutation80 hz
    mixedMoment B raw21217step1 raw21217step1Labels = mixedMoment B raw21217step2 raw21217step2Labels := by
      have ha : raw21217step2 = (fun i j => raw21217step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw21217step2 raw21217step1; decide +kernel
      have hl : raw21217step2Labels = raw21217step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21217step1 raw21217step1Labels permutation29 permutation5
    mixedMoment B raw21217step2 raw21217step2Labels = mixedMoment B raw21217step3 raw21217step3Labels := by
      have ha : raw21217step3 = raw21217step2 := by apply Matrix.ext; unfold raw21217step3 raw21217step2; decide +kernel
      have hl : raw21217step2Labels = labelEmbedding1 ∘ raw21217step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21217step2 raw21217step2Labels raw21217step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1749 node1749Labels := by rfl

theorem canonical21218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21218 raw21218Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw21218 raw21218Labels = mixedMoment B raw21218step0 raw21218step0Labels := by
      have hz : ∀ j, raw21218 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21218step0 = (fun i j => raw21218 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21218step0 raw21218; decide +kernel
      have hl : raw21218step0Labels = raw21218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21218 raw21218Labels permutation434 hz
    mixedMoment B raw21218step0 raw21218step0Labels = mixedMoment B raw21218step1 raw21218step1Labels := by
      have hz : ∀ j, raw21218step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21218step1 = (fun i j => raw21218step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21218step1 raw21218step0; decide +kernel
      have hl : raw21218step1Labels = raw21218step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21218step0 raw21218step0Labels permutation80 hz
    _ = mixedMoment B node1046 node1046Labels := by rfl

theorem canonical21219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21219 raw21219Labels = mixedMoment B node611 node611Labels := by
  calc
    mixedMoment B raw21219 raw21219Labels = mixedMoment B raw21219step0 raw21219step0Labels := by
      have hz : ∀ j, raw21219 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21219step0 = (fun i j => raw21219 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21219step0 raw21219; decide +kernel
      have hl : raw21219step0Labels = raw21219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21219 raw21219Labels permutation434 hz
    mixedMoment B raw21219step0 raw21219step0Labels = mixedMoment B raw21219step1 raw21219step1Labels := by
      have hz : ∀ j, raw21219step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21219step1 = (fun i j => raw21219step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21219step1 raw21219step0; decide +kernel
      have hl : raw21219step1Labels = raw21219step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21219step0 raw21219step0Labels permutation80 hz
    _ = mixedMoment B node611 node611Labels := by rfl

theorem canonical21220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21220 raw21220Labels = mixedMoment B node581 node581Labels := by
  calc
    mixedMoment B raw21220 raw21220Labels = mixedMoment B raw21220step0 raw21220step0Labels := by
      have hz : ∀ j, raw21220 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21220step0 = (fun i j => raw21220 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21220step0 raw21220; decide +kernel
      have hl : raw21220step0Labels = raw21220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21220 raw21220Labels permutation434 hz
    _ = mixedMoment B node581 node581Labels := by rfl

theorem canonical21221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21221 raw21221Labels = mixedMoment B node581 node581Labels := by
  calc
    mixedMoment B raw21221 raw21221Labels = mixedMoment B raw21221step0 raw21221step0Labels := by
      have hz : ∀ j, raw21221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21221step0 = (fun i j => raw21221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21221step0 raw21221; decide +kernel
      have hl : raw21221step0Labels = raw21221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21221 raw21221Labels permutation346 hz
    _ = mixedMoment B node581 node581Labels := by rfl

theorem canonical21222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21222 raw21222Labels = mixedMoment B node589 node589Labels := by
  calc
    mixedMoment B raw21222 raw21222Labels = mixedMoment B raw21222step0 raw21222step0Labels := by
      have hz : ∀ j, raw21222 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21222step0 = (fun i j => raw21222 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21222step0 raw21222; decide +kernel
      have hl : raw21222step0Labels = raw21222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21222 raw21222Labels permutation434 hz
    mixedMoment B raw21222step0 raw21222step0Labels = mixedMoment B raw21222step1 raw21222step1Labels := by
      have hz : ∀ j, raw21222step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21222step1 = (fun i j => raw21222step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21222step1 raw21222step0; decide +kernel
      have hl : raw21222step1Labels = raw21222step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21222step0 raw21222step0Labels permutation80 hz
    _ = mixedMoment B node589 node589Labels := by rfl

theorem canonical21223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21223 raw21223Labels = mixedMoment B node587 node587Labels := by
  calc
    mixedMoment B raw21223 raw21223Labels = mixedMoment B raw21223step0 raw21223step0Labels := by
      have hz : ∀ j, raw21223 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21223step0 = (fun i j => raw21223 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21223step0 raw21223; decide +kernel
      have hl : raw21223step0Labels = raw21223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21223 raw21223Labels permutation434 hz
    mixedMoment B raw21223step0 raw21223step0Labels = mixedMoment B raw21223step1 raw21223step1Labels := by
      have hz : ∀ j, raw21223step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21223step1 = (fun i j => raw21223step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21223step1 raw21223step0; decide +kernel
      have hl : raw21223step1Labels = raw21223step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21223step0 raw21223step0Labels permutation80 hz
    _ = mixedMoment B node587 node587Labels := by rfl

theorem canonical21224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21224 raw21224Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw21224 raw21224Labels = mixedMoment B raw21224step0 raw21224step0Labels := by
      have hz : ∀ j, raw21224 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21224step0 = (fun i j => raw21224 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21224step0 raw21224; decide +kernel
      have hl : raw21224step0Labels = raw21224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21224 raw21224Labels permutation434 hz
    mixedMoment B raw21224step0 raw21224step0Labels = mixedMoment B raw21224step1 raw21224step1Labels := by
      have ha : raw21224step1 = (fun i j => raw21224step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21224step1 raw21224step0; decide +kernel
      have hl : raw21224step1Labels = raw21224step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21224step0 raw21224step0Labels permutation38 permutation2
    _ = mixedMoment B node930 node930Labels := by rfl

theorem canonical21225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21225 raw21225Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw21225 raw21225Labels = mixedMoment B raw21225step0 raw21225step0Labels := by
      have hz : ∀ j, raw21225 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21225step0 = (fun i j => raw21225 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21225step0 raw21225; decide +kernel
      have hl : raw21225step0Labels = raw21225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21225 raw21225Labels permutation346 hz
    mixedMoment B raw21225step0 raw21225step0Labels = mixedMoment B raw21225step1 raw21225step1Labels := by
      have ha : raw21225step1 = (fun i j => raw21225step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21225step1 raw21225step0; decide +kernel
      have hl : raw21225step1Labels = raw21225step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21225step0 raw21225step0Labels permutation38 permutation2
    _ = mixedMoment B node930 node930Labels := by rfl

theorem canonical21226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21226 raw21226Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw21226 raw21226Labels = mixedMoment B raw21226step0 raw21226step0Labels := by
      have hz : ∀ j, raw21226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21226step0 = (fun i j => raw21226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21226step0 raw21226; decide +kernel
      have hl : raw21226step0Labels = raw21226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21226 raw21226Labels permutation434 hz
    mixedMoment B raw21226step0 raw21226step0Labels = mixedMoment B raw21226step1 raw21226step1Labels := by
      have hz : ∀ j, raw21226step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21226step1 = (fun i j => raw21226step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21226step1 raw21226step0; decide +kernel
      have hl : raw21226step1Labels = raw21226step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21226step0 raw21226step0Labels permutation80 hz
    mixedMoment B raw21226step1 raw21226step1Labels = mixedMoment B raw21226step2 raw21226step2Labels := by
      have ha : raw21226step2 = (fun i j => raw21226step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21226step2 raw21226step1; decide +kernel
      have hl : raw21226step2Labels = raw21226step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21226step1 raw21226step1Labels permutation10 permutation2
    _ = mixedMoment B node1046 node1046Labels := by rfl

theorem canonical21227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21227 raw21227Labels = mixedMoment B node1086 node1086Labels := by
  calc
    mixedMoment B raw21227 raw21227Labels = mixedMoment B raw21227step0 raw21227step0Labels := by
      have hz : ∀ j, raw21227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21227step0 = (fun i j => raw21227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21227step0 raw21227; decide +kernel
      have hl : raw21227step0Labels = raw21227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21227 raw21227Labels permutation434 hz
    mixedMoment B raw21227step0 raw21227step0Labels = mixedMoment B raw21227step1 raw21227step1Labels := by
      have hz : ∀ j, raw21227step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21227step1 = (fun i j => raw21227step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21227step1 raw21227step0; decide +kernel
      have hl : raw21227step1Labels = raw21227step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21227step0 raw21227step0Labels permutation80 hz
    _ = mixedMoment B node1086 node1086Labels := by rfl

theorem canonical21228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21228 raw21228Labels = mixedMoment B node945 node945Labels := by
  calc
    mixedMoment B raw21228 raw21228Labels = mixedMoment B raw21228step0 raw21228step0Labels := by
      have hz : ∀ j, raw21228 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21228step0 = (fun i j => raw21228 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21228step0 raw21228; decide +kernel
      have hl : raw21228step0Labels = raw21228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21228 raw21228Labels permutation434 hz
    _ = mixedMoment B node945 node945Labels := by rfl

theorem canonical21229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21229 raw21229Labels = mixedMoment B node945 node945Labels := by
  calc
    mixedMoment B raw21229 raw21229Labels = mixedMoment B raw21229step0 raw21229step0Labels := by
      have hz : ∀ j, raw21229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21229step0 = (fun i j => raw21229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21229step0 raw21229; decide +kernel
      have hl : raw21229step0Labels = raw21229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21229 raw21229Labels permutation346 hz
    _ = mixedMoment B node945 node945Labels := by rfl

theorem canonical21230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21230 raw21230Labels = mixedMoment B node953 node953Labels := by
  calc
    mixedMoment B raw21230 raw21230Labels = mixedMoment B raw21230step0 raw21230step0Labels := by
      have hz : ∀ j, raw21230 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21230step0 = (fun i j => raw21230 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21230step0 raw21230; decide +kernel
      have hl : raw21230step0Labels = raw21230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21230 raw21230Labels permutation434 hz
    mixedMoment B raw21230step0 raw21230step0Labels = mixedMoment B raw21230step1 raw21230step1Labels := by
      have hz : ∀ j, raw21230step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21230step1 = (fun i j => raw21230step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21230step1 raw21230step0; decide +kernel
      have hl : raw21230step1Labels = raw21230step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21230step0 raw21230step0Labels permutation80 hz
    _ = mixedMoment B node953 node953Labels := by rfl

theorem canonical21231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21231 raw21231Labels = mixedMoment B node951 node951Labels := by
  calc
    mixedMoment B raw21231 raw21231Labels = mixedMoment B raw21231step0 raw21231step0Labels := by
      have hz : ∀ j, raw21231 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21231step0 = (fun i j => raw21231 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21231step0 raw21231; decide +kernel
      have hl : raw21231step0Labels = raw21231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21231 raw21231Labels permutation434 hz
    mixedMoment B raw21231step0 raw21231step0Labels = mixedMoment B raw21231step1 raw21231step1Labels := by
      have hz : ∀ j, raw21231step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21231step1 = (fun i j => raw21231step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21231step1 raw21231step0; decide +kernel
      have hl : raw21231step1Labels = raw21231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21231step0 raw21231step0Labels permutation80 hz
    _ = mixedMoment B node951 node951Labels := by rfl

theorem canonical21232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21232 raw21232Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw21232 raw21232Labels = mixedMoment B raw21232step0 raw21232step0Labels := by
      have hz : ∀ j, raw21232 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21232step0 = (fun i j => raw21232 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21232step0 raw21232; decide +kernel
      have hl : raw21232step0Labels = raw21232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21232 raw21232Labels permutation434 hz
    mixedMoment B raw21232step0 raw21232step0Labels = mixedMoment B raw21232step1 raw21232step1Labels := by
      have ha : raw21232step1 = (fun i j => raw21232step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21232step1 raw21232step0; decide +kernel
      have hl : raw21232step1Labels = raw21232step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21232step0 raw21232step0Labels permutation38 permutation2
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical21233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21233 raw21233Labels = mixedMoment B node905 node905Labels := by
  calc
    mixedMoment B raw21233 raw21233Labels = mixedMoment B raw21233step0 raw21233step0Labels := by
      have ha : raw21233step0 = (fun i j => raw21233 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21233step0 raw21233; decide +kernel
      have hl : raw21233step0Labels = raw21233Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21233 raw21233Labels permutation176 permutation2
    _ = mixedMoment B node905 node905Labels := by rfl

theorem canonical21234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21234 raw21234Labels = mixedMoment B node913 node913Labels := by
  calc
    mixedMoment B raw21234 raw21234Labels = mixedMoment B raw21234step0 raw21234step0Labels := by
      have hz : ∀ j, raw21234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21234step0 = (fun i j => raw21234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21234step0 raw21234; decide +kernel
      have hl : raw21234step0Labels = raw21234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21234 raw21234Labels permutation434 hz
    mixedMoment B raw21234step0 raw21234step0Labels = mixedMoment B raw21234step1 raw21234step1Labels := by
      have ha : raw21234step1 = (fun i j => raw21234step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21234step1 raw21234step0; decide +kernel
      have hl : raw21234step1Labels = raw21234step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21234step0 raw21234step0Labels permutation38 permutation2
    _ = mixedMoment B node913 node913Labels := by rfl

theorem canonical21235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21235 raw21235Labels = mixedMoment B node911 node911Labels := by
  calc
    mixedMoment B raw21235 raw21235Labels = mixedMoment B raw21235step0 raw21235step0Labels := by
      have hz : ∀ j, raw21235 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21235step0 = (fun i j => raw21235 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21235step0 raw21235; decide +kernel
      have hl : raw21235step0Labels = raw21235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21235 raw21235Labels permutation434 hz
    mixedMoment B raw21235step0 raw21235step0Labels = mixedMoment B raw21235step1 raw21235step1Labels := by
      have ha : raw21235step1 = (fun i j => raw21235step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21235step1 raw21235step0; decide +kernel
      have hl : raw21235step1Labels = raw21235step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21235step0 raw21235step0Labels permutation38 permutation2
    _ = mixedMoment B node911 node911Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw825 raw825Labels = mixedMoment B node4183 node4183Labels := by
  calc
    mixedMoment B raw825 raw825Labels = mixedMoment B raw825step0 raw825step0Labels := by
      have ha : raw825step0 = (fun i j => raw825 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw825step0 raw825; decide +kernel
      have hl : raw825step0Labels = raw825Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw825 raw825Labels permutation8 permutation4
    mixedMoment B raw825step0 raw825step0Labels = mixedMoment B raw825step1 raw825step1Labels := by
      have ha : raw825step1 = raw825step0 := by apply Matrix.ext; unfold raw825step1 raw825step0; decide +kernel
      have hl : raw825step0Labels = labelEmbedding7 ∘ raw825step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw825step0 raw825step0Labels raw825step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4183 node4183Labels := by rfl

theorem canonical826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw826 raw826Labels = mixedMoment B node611 node611Labels := by
  calc
    mixedMoment B raw826 raw826Labels = mixedMoment B raw826step0 raw826step0Labels := by
      have ha : raw826step0 = (fun i j => raw826 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw826step0 raw826; decide +kernel
      have hl : raw826step0Labels = raw826Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw826 raw826Labels permutation8 permutation4
    _ = mixedMoment B node611 node611Labels := by rfl

theorem canonical827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw827 raw827Labels = mixedMoment B node1535 node1535Labels := by
  calc
    mixedMoment B raw827 raw827Labels = mixedMoment B raw827step0 raw827step0Labels := by
      have ha : raw827step0 = (fun i j => raw827 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw827step0 raw827; decide +kernel
      have hl : raw827step0Labels = raw827Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw827 raw827Labels permutation8 permutation6
    mixedMoment B raw827step0 raw827step0Labels = mixedMoment B raw827step1 raw827step1Labels := by
      have ha : raw827step1 = -raw827step0 := by apply Matrix.ext; change ∀ i j, raw827step1 i j = -(raw827step0 i j); unfold raw827step1 raw827step0; decide +kernel
      have hl : raw827step1Labels = raw827step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw827step1 raw827step1Labels = mixedMoment B raw827step2 raw827step2Labels := by
      have ha : raw827step2 = raw827step1 := by apply Matrix.ext; unfold raw827step2 raw827step1; decide +kernel
      have hl : raw827step1Labels = labelEmbedding1 ∘ raw827step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw827step1 raw827step1Labels raw827step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1535 node1535Labels := by rfl

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

theorem canonical1143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1143 raw1143Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw1143 raw1143Labels = mixedMoment B raw1143step0 raw1143step0Labels := by
      have ha : raw1143step0 = (fun i j => raw1143 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1143step0 raw1143; decide +kernel
      have hl : raw1143step0Labels = raw1143Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1143 raw1143Labels permutation32 permutation4
    mixedMoment B raw1143step0 raw1143step0Labels = mixedMoment B raw1143step1 raw1143step1Labels := by
      have ha : raw1143step1 = raw1143step0 := by apply Matrix.ext; unfold raw1143step1 raw1143step0; decide +kernel
      have hl : raw1143step0Labels = labelEmbedding7 ∘ raw1143step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1143step0 raw1143step0Labels raw1143step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4352 node4352Labels := by rfl

theorem canonical1144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1144 raw1144Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw1144 raw1144Labels = mixedMoment B raw1144step0 raw1144step0Labels := by
      have ha : raw1144step0 = (fun i j => raw1144 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1144step0 raw1144; decide +kernel
      have hl : raw1144step0Labels = raw1144Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1144 raw1144Labels permutation32 permutation4
    _ = mixedMoment B node930 node930Labels := by rfl

theorem canonical1145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1145 raw1145Labels = mixedMoment B node1690 node1690Labels := by
  calc
    mixedMoment B raw1145 raw1145Labels = mixedMoment B raw1145step0 raw1145step0Labels := by
      have ha : raw1145step0 = (fun i j => raw1145 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1145step0 raw1145; decide +kernel
      have hl : raw1145step0Labels = raw1145Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1145 raw1145Labels permutation32 permutation6
    mixedMoment B raw1145step0 raw1145step0Labels = mixedMoment B raw1145step1 raw1145step1Labels := by
      have ha : raw1145step1 = -raw1145step0 := by apply Matrix.ext; change ∀ i j, raw1145step1 i j = -(raw1145step0 i j); unfold raw1145step1 raw1145step0; decide +kernel
      have hl : raw1145step1Labels = raw1145step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1145step1 raw1145step1Labels = mixedMoment B raw1145step2 raw1145step2Labels := by
      have ha : raw1145step2 = raw1145step1 := by apply Matrix.ext; unfold raw1145step2 raw1145step1; decide +kernel
      have hl : raw1145step1Labels = labelEmbedding1 ∘ raw1145step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1145step1 raw1145step1Labels raw1145step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1690 node1690Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11403 raw11403Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw11403 raw11403Labels = mixedMoment B raw11403step0 raw11403step0Labels := by
      have hz : ∀ j, raw11403 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11403step0 = (fun i j => raw11403 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11403step0 raw11403; decide +kernel
      have hl : raw11403step0Labels = raw11403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11403 raw11403Labels permutation434 hz
    mixedMoment B raw11403step0 raw11403step0Labels = mixedMoment B raw11403step1 raw11403step1Labels := by
      have hz : ∀ j, raw11403step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11403step1 = (fun i j => raw11403step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11403step1 raw11403step0; decide +kernel
      have hl : raw11403step1Labels = raw11403step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11403step0 raw11403step0Labels permutation80 hz
    _ = mixedMoment B node4502 node4502Labels := by rfl

theorem canonical11408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11408 raw11408Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw11408 raw11408Labels = mixedMoment B raw11408step0 raw11408step0Labels := by
      have hz : ∀ j, raw11408 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11408step0 = (fun i j => raw11408 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11408step0 raw11408; decide +kernel
      have hl : raw11408step0Labels = raw11408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11408 raw11408Labels permutation434 hz
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical11413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11413 raw11413Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw11413 raw11413Labels = mixedMoment B raw11413step0 raw11413step0Labels := by
      have hz : ∀ j, raw11413 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11413step0 = (fun i j => raw11413 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11413step0 raw11413; decide +kernel
      have hl : raw11413step0Labels = raw11413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11413 raw11413Labels permutation346 hz
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical11418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11418 raw11418Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw11418 raw11418Labels = mixedMoment B raw11418step0 raw11418step0Labels := by
      have hz : ∀ j, raw11418 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11418step0 = (fun i j => raw11418 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11418step0 raw11418; decide +kernel
      have hl : raw11418step0Labels = raw11418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11418 raw11418Labels permutation434 hz
    mixedMoment B raw11418step0 raw11418step0Labels = mixedMoment B raw11418step1 raw11418step1Labels := by
      have hz : ∀ j, raw11418step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11418step1 = (fun i j => raw11418step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11418step1 raw11418step0; decide +kernel
      have hl : raw11418step1Labels = raw11418step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11418step0 raw11418step0Labels permutation80 hz
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical11424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11424 raw11424Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw11424 raw11424Labels = mixedMoment B raw11424step0 raw11424step0Labels := by
      have hz : ∀ j, raw11424 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11424step0 = (fun i j => raw11424 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11424step0 raw11424; decide +kernel
      have hl : raw11424step0Labels = raw11424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11424 raw11424Labels permutation434 hz
    mixedMoment B raw11424step0 raw11424step0Labels = mixedMoment B raw11424step1 raw11424step1Labels := by
      have hz : ∀ j, raw11424step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11424step1 = (fun i j => raw11424step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11424step1 raw11424step0; decide +kernel
      have hl : raw11424step1Labels = raw11424step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11424step0 raw11424step0Labels permutation80 hz
    _ = mixedMoment B node4871 node4871Labels := by rfl

theorem canonical11425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11425 raw11425Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw11425 raw11425Labels = mixedMoment B raw11425step0 raw11425step0Labels := by
      have hz : ∀ j, raw11425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11425step0 = (fun i j => raw11425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11425step0 raw11425; decide +kernel
      have hl : raw11425step0Labels = raw11425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11425 raw11425Labels permutation434 hz
    mixedMoment B raw11425step0 raw11425step0Labels = mixedMoment B raw11425step1 raw11425step1Labels := by
      have ha : raw11425step1 = (fun i j => raw11425step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11425step1 raw11425step0; decide +kernel
      have hl : raw11425step1Labels = raw11425step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11425step0 raw11425step0Labels permutation38 permutation2
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical11426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11426 raw11426Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw11426 raw11426Labels = mixedMoment B raw11426step0 raw11426step0Labels := by
      have hz : ∀ j, raw11426 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11426step0 = (fun i j => raw11426 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11426step0 raw11426; decide +kernel
      have hl : raw11426step0Labels = raw11426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11426 raw11426Labels permutation346 hz
    mixedMoment B raw11426step0 raw11426step0Labels = mixedMoment B raw11426step1 raw11426step1Labels := by
      have ha : raw11426step1 = (fun i j => raw11426step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11426step1 raw11426step0; decide +kernel
      have hl : raw11426step1Labels = raw11426step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11426step0 raw11426step0Labels permutation38 permutation2
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical11427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11427 raw11427Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw11427 raw11427Labels = mixedMoment B raw11427step0 raw11427step0Labels := by
      have hz : ∀ j, raw11427 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11427step0 = (fun i j => raw11427 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11427step0 raw11427; decide +kernel
      have hl : raw11427step0Labels = raw11427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11427 raw11427Labels permutation434 hz
    mixedMoment B raw11427step0 raw11427step0Labels = mixedMoment B raw11427step1 raw11427step1Labels := by
      have hz : ∀ j, raw11427step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11427step1 = (fun i j => raw11427step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11427step1 raw11427step0; decide +kernel
      have hl : raw11427step1Labels = raw11427step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11427step0 raw11427step0Labels permutation80 hz
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical11433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11433 raw11433Labels = mixedMoment B node1753 node1753Labels := by
  calc
    mixedMoment B raw11433 raw11433Labels = mixedMoment B raw11433step0 raw11433step0Labels := by
      have hz : ∀ j, raw11433 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11433step0 = (fun i j => raw11433 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11433step0 raw11433; decide +kernel
      have hl : raw11433step0Labels = raw11433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11433 raw11433Labels permutation434 hz
    mixedMoment B raw11433step0 raw11433step0Labels = mixedMoment B raw11433step1 raw11433step1Labels := by
      have hz : ∀ j, raw11433step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11433step1 = (fun i j => raw11433step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11433step1 raw11433step0; decide +kernel
      have hl : raw11433step1Labels = raw11433step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11433step0 raw11433step0Labels permutation80 hz
    mixedMoment B raw11433step1 raw11433step1Labels = mixedMoment B raw11433step2 raw11433step2Labels := by
      have ha : raw11433step2 = (fun i j => raw11433step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11433step2 raw11433step1; decide +kernel
      have hl : raw11433step2Labels = raw11433step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11433step1 raw11433step1Labels permutation8 permutation7
    mixedMoment B raw11433step2 raw11433step2Labels = mixedMoment B raw11433step3 raw11433step3Labels := by
      have ha : raw11433step3 = -raw11433step2 := by apply Matrix.ext; change ∀ i j, raw11433step3 i j = -(raw11433step2 i j); unfold raw11433step3 raw11433step2; decide +kernel
      have hl : raw11433step3Labels = raw11433step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11433step3 raw11433step3Labels = mixedMoment B raw11433step4 raw11433step4Labels := by
      have ha : raw11433step4 = raw11433step3 := by apply Matrix.ext; unfold raw11433step4 raw11433step3; decide +kernel
      have hl : raw11433step3Labels = labelEmbedding1 ∘ raw11433step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11433step3 raw11433step3Labels raw11433step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1753 node1753Labels := by rfl

theorem canonical11438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11438 raw11438Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw11438 raw11438Labels = mixedMoment B raw11438step0 raw11438step0Labels := by
      have hz : ∀ j, raw11438 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11438step0 = (fun i j => raw11438 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11438step0 raw11438; decide +kernel
      have hl : raw11438step0Labels = raw11438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11438 raw11438Labels permutation434 hz
    mixedMoment B raw11438step0 raw11438step0Labels = mixedMoment B raw11438step1 raw11438step1Labels := by
      have ha : raw11438step1 = (fun i j => raw11438step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11438step1 raw11438step0; decide +kernel
      have hl : raw11438step1Labels = raw11438step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11438step0 raw11438step0Labels permutation38 permutation7
    mixedMoment B raw11438step1 raw11438step1Labels = mixedMoment B raw11438step2 raw11438step2Labels := by
      have ha : raw11438step2 = -raw11438step1 := by apply Matrix.ext; change ∀ i j, raw11438step2 i j = -(raw11438step1 i j); unfold raw11438step2 raw11438step1; decide +kernel
      have hl : raw11438step2Labels = raw11438step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11438step2 raw11438step2Labels = mixedMoment B raw11438step3 raw11438step3Labels := by
      have ha : raw11438step3 = raw11438step2 := by apply Matrix.ext; unfold raw11438step3 raw11438step2; decide +kernel
      have hl : raw11438step2Labels = labelEmbedding1 ∘ raw11438step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11438step2 raw11438step2Labels raw11438step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical11443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11443 raw11443Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw11443 raw11443Labels = mixedMoment B raw11443step0 raw11443step0Labels := by
      have hz : ∀ j, raw11443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11443step0 = (fun i j => raw11443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11443step0 raw11443; decide +kernel
      have hl : raw11443step0Labels = raw11443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11443 raw11443Labels permutation346 hz
    mixedMoment B raw11443step0 raw11443step0Labels = mixedMoment B raw11443step1 raw11443step1Labels := by
      have ha : raw11443step1 = (fun i j => raw11443step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11443step1 raw11443step0; decide +kernel
      have hl : raw11443step1Labels = raw11443step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11443step0 raw11443step0Labels permutation38 permutation7
    mixedMoment B raw11443step1 raw11443step1Labels = mixedMoment B raw11443step2 raw11443step2Labels := by
      have ha : raw11443step2 = -raw11443step1 := by apply Matrix.ext; change ∀ i j, raw11443step2 i j = -(raw11443step1 i j); unfold raw11443step2 raw11443step1; decide +kernel
      have hl : raw11443step2Labels = raw11443step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11443step2 raw11443step2Labels = mixedMoment B raw11443step3 raw11443step3Labels := by
      have ha : raw11443step3 = raw11443step2 := by apply Matrix.ext; unfold raw11443step3 raw11443step2; decide +kernel
      have hl : raw11443step2Labels = labelEmbedding1 ∘ raw11443step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11443step2 raw11443step2Labels raw11443step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical11448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11448 raw11448Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw11448 raw11448Labels = mixedMoment B raw11448step0 raw11448step0Labels := by
      have hz : ∀ j, raw11448 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11448step0 = (fun i j => raw11448 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11448step0 raw11448; decide +kernel
      have hl : raw11448step0Labels = raw11448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11448 raw11448Labels permutation434 hz
    mixedMoment B raw11448step0 raw11448step0Labels = mixedMoment B raw11448step1 raw11448step1Labels := by
      have hz : ∀ j, raw11448step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11448step1 = (fun i j => raw11448step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11448step1 raw11448step0; decide +kernel
      have hl : raw11448step1Labels = raw11448step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11448step0 raw11448step0Labels permutation80 hz
    mixedMoment B raw11448step1 raw11448step1Labels = mixedMoment B raw11448step2 raw11448step2Labels := by
      have ha : raw11448step2 = (fun i j => raw11448step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11448step2 raw11448step1; decide +kernel
      have hl : raw11448step2Labels = raw11448step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11448step1 raw11448step1Labels permutation8 permutation7
    mixedMoment B raw11448step2 raw11448step2Labels = mixedMoment B raw11448step3 raw11448step3Labels := by
      have ha : raw11448step3 = -raw11448step2 := by apply Matrix.ext; change ∀ i j, raw11448step3 i j = -(raw11448step2 i j); unfold raw11448step3 raw11448step2; decide +kernel
      have hl : raw11448step3Labels = raw11448step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11448step3 raw11448step3Labels = mixedMoment B raw11448step4 raw11448step4Labels := by
      have ha : raw11448step4 = raw11448step3 := by apply Matrix.ext; unfold raw11448step4 raw11448step3; decide +kernel
      have hl : raw11448step3Labels = labelEmbedding1 ∘ raw11448step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11448step3 raw11448step3Labels raw11448step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1751 node1751Labels := by rfl

theorem canonical11454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11454 raw11454Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw11454 raw11454Labels = mixedMoment B raw11454step0 raw11454step0Labels := by
      have hz : ∀ j, raw11454 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11454step0 = (fun i j => raw11454 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11454step0 raw11454; decide +kernel
      have hl : raw11454step0Labels = raw11454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11454 raw11454Labels permutation434 hz
    mixedMoment B raw11454step0 raw11454step0Labels = mixedMoment B raw11454step1 raw11454step1Labels := by
      have hz : ∀ j, raw11454step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11454step1 = (fun i j => raw11454step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11454step1 raw11454step0; decide +kernel
      have hl : raw11454step1Labels = raw11454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11454step0 raw11454step0Labels permutation80 hz
    mixedMoment B raw11454step1 raw11454step1Labels = mixedMoment B raw11454step2 raw11454step2Labels := by
      have ha : raw11454step2 = (fun i j => raw11454step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11454step2 raw11454step1; decide +kernel
      have hl : raw11454step2Labels = raw11454step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11454step1 raw11454step1Labels permutation8 permutation7
    mixedMoment B raw11454step2 raw11454step2Labels = mixedMoment B raw11454step3 raw11454step3Labels := by
      have ha : raw11454step3 = -raw11454step2 := by apply Matrix.ext; change ∀ i j, raw11454step3 i j = -(raw11454step2 i j); unfold raw11454step3 raw11454step2; decide +kernel
      have hl : raw11454step3Labels = raw11454step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11454step3 raw11454step3Labels = mixedMoment B raw11454step4 raw11454step4Labels := by
      have ha : raw11454step4 = raw11454step3 := by apply Matrix.ext; unfold raw11454step4 raw11454step3; decide +kernel
      have hl : raw11454step3Labels = labelEmbedding1 ∘ raw11454step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11454step3 raw11454step3Labels raw11454step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

theorem canonical11455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11455 raw11455Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw11455 raw11455Labels = mixedMoment B raw11455step0 raw11455step0Labels := by
      have hz : ∀ j, raw11455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11455step0 = (fun i j => raw11455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11455step0 raw11455; decide +kernel
      have hl : raw11455step0Labels = raw11455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11455 raw11455Labels permutation434 hz
    mixedMoment B raw11455step0 raw11455step0Labels = mixedMoment B raw11455step1 raw11455step1Labels := by
      have ha : raw11455step1 = (fun i j => raw11455step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11455step1 raw11455step0; decide +kernel
      have hl : raw11455step1Labels = raw11455step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11455step0 raw11455step0Labels permutation38 permutation7
    mixedMoment B raw11455step1 raw11455step1Labels = mixedMoment B raw11455step2 raw11455step2Labels := by
      have ha : raw11455step2 = -raw11455step1 := by apply Matrix.ext; change ∀ i j, raw11455step2 i j = -(raw11455step1 i j); unfold raw11455step2 raw11455step1; decide +kernel
      have hl : raw11455step2Labels = raw11455step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11455step2 raw11455step2Labels = mixedMoment B raw11455step3 raw11455step3Labels := by
      have ha : raw11455step3 = raw11455step2 := by apply Matrix.ext; unfold raw11455step3 raw11455step2; decide +kernel
      have hl : raw11455step2Labels = labelEmbedding1 ∘ raw11455step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11455step2 raw11455step2Labels raw11455step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical11456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11456 raw11456Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw11456 raw11456Labels = mixedMoment B raw11456step0 raw11456step0Labels := by
      have hz : ∀ j, raw11456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11456step0 = (fun i j => raw11456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11456step0 raw11456; decide +kernel
      have hl : raw11456step0Labels = raw11456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11456 raw11456Labels permutation346 hz
    mixedMoment B raw11456step0 raw11456step0Labels = mixedMoment B raw11456step1 raw11456step1Labels := by
      have ha : raw11456step1 = (fun i j => raw11456step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11456step1 raw11456step0; decide +kernel
      have hl : raw11456step1Labels = raw11456step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11456step0 raw11456step0Labels permutation38 permutation7
    mixedMoment B raw11456step1 raw11456step1Labels = mixedMoment B raw11456step2 raw11456step2Labels := by
      have ha : raw11456step2 = -raw11456step1 := by apply Matrix.ext; change ∀ i j, raw11456step2 i j = -(raw11456step1 i j); unfold raw11456step2 raw11456step1; decide +kernel
      have hl : raw11456step2Labels = raw11456step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11456step2 raw11456step2Labels = mixedMoment B raw11456step3 raw11456step3Labels := by
      have ha : raw11456step3 = raw11456step2 := by apply Matrix.ext; unfold raw11456step3 raw11456step2; decide +kernel
      have hl : raw11456step2Labels = labelEmbedding1 ∘ raw11456step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11456step2 raw11456step2Labels raw11456step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical11457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11457 raw11457Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw11457 raw11457Labels = mixedMoment B raw11457step0 raw11457step0Labels := by
      have hz : ∀ j, raw11457 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11457step0 = (fun i j => raw11457 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11457step0 raw11457; decide +kernel
      have hl : raw11457step0Labels = raw11457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11457 raw11457Labels permutation434 hz
    mixedMoment B raw11457step0 raw11457step0Labels = mixedMoment B raw11457step1 raw11457step1Labels := by
      have hz : ∀ j, raw11457step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11457step1 = (fun i j => raw11457step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11457step1 raw11457step0; decide +kernel
      have hl : raw11457step1Labels = raw11457step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11457step0 raw11457step0Labels permutation80 hz
    mixedMoment B raw11457step1 raw11457step1Labels = mixedMoment B raw11457step2 raw11457step2Labels := by
      have ha : raw11457step2 = (fun i j => raw11457step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11457step2 raw11457step1; decide +kernel
      have hl : raw11457step2Labels = raw11457step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11457step1 raw11457step1Labels permutation8 permutation7
    mixedMoment B raw11457step2 raw11457step2Labels = mixedMoment B raw11457step3 raw11457step3Labels := by
      have ha : raw11457step3 = -raw11457step2 := by apply Matrix.ext; change ∀ i j, raw11457step3 i j = -(raw11457step2 i j); unfold raw11457step3 raw11457step2; decide +kernel
      have hl : raw11457step3Labels = raw11457step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11457step3 raw11457step3Labels = mixedMoment B raw11457step4 raw11457step4Labels := by
      have ha : raw11457step4 = raw11457step3 := by apply Matrix.ext; unfold raw11457step4 raw11457step3; decide +kernel
      have hl : raw11457step3Labels = labelEmbedding1 ∘ raw11457step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11457step3 raw11457step3Labels raw11457step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

theorem canonical11463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11463 raw11463Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw11463 raw11463Labels = mixedMoment B raw11463step0 raw11463step0Labels := by
      have hz : ∀ j, raw11463 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11463step0 = (fun i j => raw11463 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11463step0 raw11463; decide +kernel
      have hl : raw11463step0Labels = raw11463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11463 raw11463Labels permutation434 hz
    mixedMoment B raw11463step0 raw11463step0Labels = mixedMoment B raw11463step1 raw11463step1Labels := by
      have hz : ∀ j, raw11463step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11463step1 = (fun i j => raw11463step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11463step1 raw11463step0; decide +kernel
      have hl : raw11463step1Labels = raw11463step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11463step0 raw11463step0Labels permutation80 hz
    _ = mixedMoment B node2112 node2112Labels := by rfl

theorem canonical11464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11464 raw11464Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11464 raw11464Labels = mixedMoment B raw11464step0 raw11464step0Labels := by
      have hz : ∀ j, raw11464 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11464step0 = (fun i j => raw11464 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11464step0 raw11464; decide +kernel
      have hl : raw11464step0Labels = raw11464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11464 raw11464Labels permutation434 hz
    mixedMoment B raw11464step0 raw11464step0Labels = mixedMoment B raw11464step1 raw11464step1Labels := by
      have hz : ∀ j, raw11464step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11464step1 = (fun i j => raw11464step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11464step1 raw11464step0; decide +kernel
      have hl : raw11464step1Labels = raw11464step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11464step0 raw11464step0Labels permutation80 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

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

theorem canonical1260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1260 raw1260Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw1260 raw1260Labels = mixedMoment B raw1260step0 raw1260step0Labels := by
      have ha : raw1260step0 = (fun i j => raw1260 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1260step0 raw1260; decide +kernel
      have hl : raw1260step0Labels = raw1260Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1260 raw1260Labels permutation32 permutation4
    mixedMoment B raw1260step0 raw1260step0Labels = mixedMoment B raw1260step1 raw1260step1Labels := by
      have ha : raw1260step1 = raw1260step0 := by apply Matrix.ext; unfold raw1260step1 raw1260step0; decide +kernel
      have hl : raw1260step0Labels = labelEmbedding7 ∘ raw1260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1260step0 raw1260step0Labels raw1260step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical1261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1261 raw1261Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw1261 raw1261Labels = mixedMoment B raw1261step0 raw1261step0Labels := by
      have ha : raw1261step0 = (fun i j => raw1261 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1261step0 raw1261; decide +kernel
      have hl : raw1261step0Labels = raw1261Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1261 raw1261Labels permutation32 permutation4
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical1262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1262 raw1262Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw1262 raw1262Labels = mixedMoment B raw1262step0 raw1262step0Labels := by
      have ha : raw1262step0 = (fun i j => raw1262 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1262step0 raw1262; decide +kernel
      have hl : raw1262step0Labels = raw1262Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1262 raw1262Labels permutation38 permutation6
    mixedMoment B raw1262step0 raw1262step0Labels = mixedMoment B raw1262step1 raw1262step1Labels := by
      have ha : raw1262step1 = -raw1262step0 := by apply Matrix.ext; change ∀ i j, raw1262step1 i j = -(raw1262step0 i j); unfold raw1262step1 raw1262step0; decide +kernel
      have hl : raw1262step1Labels = raw1262step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1262step1 raw1262step1Labels = mixedMoment B raw1262step2 raw1262step2Labels := by
      have ha : raw1262step2 = raw1262step1 := by apply Matrix.ext; unfold raw1262step2 raw1262step1; decide +kernel
      have hl : raw1262step1Labels = labelEmbedding1 ∘ raw1262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1262step1 raw1262step1Labels raw1262step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical1269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1269 raw1269Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw1269 raw1269Labels = mixedMoment B raw1269step0 raw1269step0Labels := by
      have ha : raw1269step0 = (fun i j => raw1269 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1269step0 raw1269; decide +kernel
      have hl : raw1269step0Labels = raw1269Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1269 raw1269Labels permutation8 permutation4
    mixedMoment B raw1269step0 raw1269step0Labels = mixedMoment B raw1269step1 raw1269step1Labels := by
      have ha : raw1269step1 = raw1269step0 := by apply Matrix.ext; unfold raw1269step1 raw1269step0; decide +kernel
      have hl : raw1269step0Labels = labelEmbedding7 ∘ raw1269step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1269step0 raw1269step0Labels raw1269step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

theorem canonical1270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1270 raw1270Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw1270 raw1270Labels = mixedMoment B raw1270step0 raw1270step0Labels := by
      have ha : raw1270step0 = (fun i j => raw1270 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1270step0 raw1270; decide +kernel
      have hl : raw1270step0Labels = raw1270Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1270 raw1270Labels permutation8 permutation4
    _ = mixedMoment B node1046 node1046Labels := by rfl

theorem canonical1271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1271 raw1271Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw1271 raw1271Labels = mixedMoment B raw1271step0 raw1271step0Labels := by
      have ha : raw1271step0 = (fun i j => raw1271 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1271step0 raw1271; decide +kernel
      have hl : raw1271step0Labels = raw1271Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1271 raw1271Labels permutation8 permutation6
    mixedMoment B raw1271step0 raw1271step0Labels = mixedMoment B raw1271step1 raw1271step1Labels := by
      have ha : raw1271step1 = -raw1271step0 := by apply Matrix.ext; change ∀ i j, raw1271step1 i j = -(raw1271step0 i j); unfold raw1271step1 raw1271step0; decide +kernel
      have hl : raw1271step1Labels = raw1271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1271step1 raw1271step1Labels = mixedMoment B raw1271step2 raw1271step2Labels := by
      have ha : raw1271step2 = raw1271step1 := by apply Matrix.ext; unfold raw1271step2 raw1271step1; decide +kernel
      have hl : raw1271step1Labels = labelEmbedding1 ∘ raw1271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1271step1 raw1271step1Labels raw1271step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical1275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1275 raw1275Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw1275 raw1275Labels = mixedMoment B raw1275step0 raw1275step0Labels := by
      have ha : raw1275step0 = (fun i j => raw1275 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1275step0 raw1275; decide +kernel
      have hl : raw1275step0Labels = raw1275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1275 raw1275Labels permutation8 permutation4
    mixedMoment B raw1275step0 raw1275step0Labels = mixedMoment B raw1275step1 raw1275step1Labels := by
      have ha : raw1275step1 = raw1275step0 := by apply Matrix.ext; unfold raw1275step1 raw1275step0; decide +kernel
      have hl : raw1275step0Labels = labelEmbedding7 ∘ raw1275step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1275step0 raw1275step0Labels raw1275step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical1276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1276 raw1276Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw1276 raw1276Labels = mixedMoment B raw1276step0 raw1276step0Labels := by
      have ha : raw1276step0 = (fun i j => raw1276 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1276step0 raw1276; decide +kernel
      have hl : raw1276step0Labels = raw1276Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1276 raw1276Labels permutation8 permutation4
    _ = mixedMoment B node1050 node1050Labels := by rfl

theorem canonical1277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1277 raw1277Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw1277 raw1277Labels = mixedMoment B raw1277step0 raw1277step0Labels := by
      have ha : raw1277step0 = (fun i j => raw1277 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1277step0 raw1277; decide +kernel
      have hl : raw1277step0Labels = raw1277Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1277 raw1277Labels permutation8 permutation6
    mixedMoment B raw1277step0 raw1277step0Labels = mixedMoment B raw1277step1 raw1277step1Labels := by
      have ha : raw1277step1 = -raw1277step0 := by apply Matrix.ext; change ∀ i j, raw1277step1 i j = -(raw1277step0 i j); unfold raw1277step1 raw1277step0; decide +kernel
      have hl : raw1277step1Labels = raw1277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1277step1 raw1277step1Labels = mixedMoment B raw1277step2 raw1277step2Labels := by
      have ha : raw1277step2 = raw1277step1 := by apply Matrix.ext; unfold raw1277step2 raw1277step1; decide +kernel
      have hl : raw1277step1Labels = labelEmbedding1 ∘ raw1277step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1277step1 raw1277step1Labels raw1277step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1751 node1751Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4183 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4183 node4183Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node611 node611Labels + mixedMoment B node1535 node1535Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw825 singletonSmall4183
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4183) = raw825Labels := by decide +kernel
  rw [hl, canonical825 B hB] at h
  have hc0 : mixedMoment B raw825 (Fin.cases (0 : Fin 2) singletonSmall4183) =
      mixedMoment B node611 node611Labels := by
    have ha : raw825 = raw826 := by apply Matrix.ext; unfold raw825 raw826; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4183 = raw826Labels := by decide +kernel
    rw [ha, hj, canonical826 B hB]
  have hc1 : mixedMoment B raw825 (Fin.cases (1 : Fin 2) singletonSmall4183) =
      mixedMoment B node1535 node1535Labels := by
    have ha : raw825 = raw827 := by apply Matrix.ext; unfold raw825 raw827; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4183 = raw827Labels := by decide +kernel
    rw [ha, hj, canonical827 B hB]
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

theorem singleton4352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4352 node4352Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node930 node930Labels + mixedMoment B node1690 node1690Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1143 singletonSmall4352
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4352) = raw1143Labels := by decide +kernel
  rw [hl, canonical1143 B hB] at h
  have hc0 : mixedMoment B raw1143 (Fin.cases (0 : Fin 2) singletonSmall4352) =
      mixedMoment B node930 node930Labels := by
    have ha : raw1143 = raw1144 := by apply Matrix.ext; unfold raw1143 raw1144; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4352 = raw1144Labels := by decide +kernel
    rw [ha, hj, canonical1144 B hB]
  have hc1 : mixedMoment B raw1143 (Fin.cases (1 : Fin 2) singletonSmall4352) =
      mixedMoment B node1690 node1690Labels := by
    have ha : raw1143 = raw1145 := by apply Matrix.ext; unfold raw1143 raw1145; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4352 = raw1145Labels := by decide +kernel
    rw [ha, hj, canonical1145 B hB]
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

theorem singleton4458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4458 node4458Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1041 node1041Labels + mixedMoment B node1724 node1724Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1260 singletonSmall4458
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4458) = raw1260Labels := by decide +kernel
  rw [hl, canonical1260 B hB] at h
  have hc0 : mixedMoment B raw1260 (Fin.cases (0 : Fin 2) singletonSmall4458) =
      mixedMoment B node1041 node1041Labels := by
    have ha : raw1260 = raw1261 := by apply Matrix.ext; unfold raw1260 raw1261; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4458 = raw1261Labels := by decide +kernel
    rw [ha, hj, canonical1261 B hB]
  have hc1 : mixedMoment B raw1260 (Fin.cases (1 : Fin 2) singletonSmall4458) =
      mixedMoment B node1724 node1724Labels := by
    have ha : raw1260 = raw1262 := by apply Matrix.ext; unfold raw1260 raw1262; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4458 = raw1262Labels := by decide +kernel
    rw [ha, hj, canonical1262 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4463 node4463Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1046 node1046Labels + mixedMoment B node1750 node1750Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1269 singletonSmall4463
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4463) = raw1269Labels := by decide +kernel
  rw [hl, canonical1269 B hB] at h
  have hc0 : mixedMoment B raw1269 (Fin.cases (0 : Fin 2) singletonSmall4463) =
      mixedMoment B node1046 node1046Labels := by
    have ha : raw1269 = raw1270 := by apply Matrix.ext; unfold raw1269 raw1270; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4463 = raw1270Labels := by decide +kernel
    rw [ha, hj, canonical1270 B hB]
  have hc1 : mixedMoment B raw1269 (Fin.cases (1 : Fin 2) singletonSmall4463) =
      mixedMoment B node1750 node1750Labels := by
    have ha : raw1269 = raw1271 := by apply Matrix.ext; unfold raw1269 raw1271; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4463 = raw1271Labels := by decide +kernel
    rw [ha, hj, canonical1271 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4467 node4467Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1050 node1050Labels + mixedMoment B node1751 node1751Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1275 singletonSmall4467
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4467) = raw1275Labels := by decide +kernel
  rw [hl, canonical1275 B hB] at h
  have hc0 : mixedMoment B raw1275 (Fin.cases (0 : Fin 2) singletonSmall4467) =
      mixedMoment B node1050 node1050Labels := by
    have ha : raw1275 = raw1276 := by apply Matrix.ext; unfold raw1275 raw1276; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4467 = raw1276Labels := by decide +kernel
    rw [ha, hj, canonical1276 B hB]
  have hc1 : mixedMoment B raw1275 (Fin.cases (1 : Fin 2) singletonSmall4467) =
      mixedMoment B node1751 node1751Labels := by
    have ha : raw1275 = raw1277 := by apply Matrix.ext; unfold raw1275 raw1277; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4467 = raw1277Labels := by decide +kernel
    rw [ha, hj, canonical1277 B hB]
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

theorem singleton4807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4807 node4807Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2025 node2025Labels + mixedMoment B node2224 node2224Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1743 singletonSmall4807
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4807) = raw1743Labels := by decide +kernel
  rw [hl, canonical1743 B hB] at h
  have hc0 : mixedMoment B raw1743 (Fin.cases (0 : Fin 2) singletonSmall4807) =
      mixedMoment B node2025 node2025Labels := by
    have ha : raw1743 = raw1744 := by apply Matrix.ext; unfold raw1743 raw1744; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4807 = raw1744Labels := by decide +kernel
    rw [ha, hj, canonical1744 B hB]
  have hc1 : mixedMoment B raw1743 (Fin.cases (1 : Fin 2) singletonSmall4807) =
      mixedMoment B node2224 node2224Labels := by
    have ha : raw1743 = raw1745 := by apply Matrix.ext; unfold raw1743 raw1745; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4807 = raw1745Labels := by decide +kernel
    rw [ha, hj, canonical1745 B hB]
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

theorem singleton4871 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4871 node4871Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2112 node2112Labels + mixedMoment B node2287 node2287Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1803 singletonSmall4871
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4871) = raw1803Labels := by decide +kernel
  rw [hl, canonical1803 B hB] at h
  have hc0 : mixedMoment B raw1803 (Fin.cases (0 : Fin 2) singletonSmall4871) =
      mixedMoment B node2112 node2112Labels := by
    have ha : raw1803 = raw1804 := by apply Matrix.ext; unfold raw1803 raw1804; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4871 = raw1804Labels := by decide +kernel
    rw [ha, hj, canonical1804 B hB]
  have hc1 : mixedMoment B raw1803 (Fin.cases (1 : Fin 2) singletonSmall4871) =
      mixedMoment B node2287 node2287Labels := by
    have ha : raw1803 = raw1805 := by apply Matrix.ext; unfold raw1803 raw1805; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4871 = raw1805Labels := by decide +kernel
    rw [ha, hj, canonical1805 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4890 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4890 node4890Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2247 node2247Labels + mixedMoment B node2290 node2290Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1821 singletonSmall4890
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4890) = raw1821Labels := by decide +kernel
  rw [hl, canonical1821 B hB] at h
  have hc0 : mixedMoment B raw1821 (Fin.cases (0 : Fin 2) singletonSmall4890) =
      mixedMoment B node2247 node2247Labels := by
    have ha : raw1821 = raw1822 := by apply Matrix.ext; unfold raw1821 raw1822; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4890 = raw1822Labels := by decide +kernel
    rw [ha, hj, canonical1822 B hB]
  have hc1 : mixedMoment B raw1821 (Fin.cases (1 : Fin 2) singletonSmall4890) =
      mixedMoment B node2290 node2290Labels := by
    have ha : raw1821 = raw1823 := by apply Matrix.ext; unfold raw1821 raw1823; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4890 = raw1823Labels := by decide +kernel
    rw [ha, hj, canonical1823 B hB]
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

theorem sound905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node905 node905Labels = Sparse.eval nodeValue905 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 905) = mixedMoment B node905 node905Labels := rfl
  simpa [nodeValue905, Sparse.eval] using hc.symm

theorem sound911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node911 node911Labels = Sparse.eval nodeValue911 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 911) = mixedMoment B node911 node911Labels := rfl
  simpa [nodeValue911, Sparse.eval] using hc.symm

theorem sound913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node913 node913Labels = Sparse.eval nodeValue913 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 913) = mixedMoment B node913 node913Labels := rfl
  simpa [nodeValue913, Sparse.eval] using hc.symm

theorem sound930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node930 node930Labels = Sparse.eval nodeValue930 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 930) = mixedMoment B node930 node930Labels := rfl
  simpa [nodeValue930, Sparse.eval] using hc.symm

theorem sound945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node945 node945Labels = Sparse.eval nodeValue945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 945) = mixedMoment B node945 node945Labels := rfl
  simpa [nodeValue945, Sparse.eval] using hc.symm

theorem sound951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node951 node951Labels = Sparse.eval nodeValue951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 951) = mixedMoment B node951 node951Labels := rfl
  simpa [nodeValue951, Sparse.eval] using hc.symm

theorem sound953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node953 node953Labels = Sparse.eval nodeValue953 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 953) = mixedMoment B node953 node953Labels := rfl
  simpa [nodeValue953, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node971 node971Labels = 0 := by
  exact mixedMoment_alpha B hF node971 node971Labels 1 permutation200
    (by decide +kernel)

theorem zero974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node974 node974Labels = 0 := by
  exact mixedMoment_alpha B hF node974 node974Labels 1 permutation200
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node971 node971Labels = Sparse.eval nodeValue971 (mixedVector B) := by
  simpa only [nodeValue971, Sparse.eval_nil] using zero971 B _hB _hF

theorem sound972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node972 node972Labels = Sparse.eval nodeValue972 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 972) = mixedMoment B node972 node972Labels := rfl
  simpa [nodeValue972, Sparse.eval] using hc.symm

theorem sound973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node973 node973Labels = Sparse.eval nodeValue973 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 973) = mixedMoment B node973 node973Labels := rfl
  simpa [nodeValue973, Sparse.eval] using hc.symm

theorem sound974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node974 node974Labels = Sparse.eval nodeValue974 (mixedVector B) := by
  simpa only [nodeValue974, Sparse.eval_nil] using zero974 B _hB _hF

theorem sound977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node977 node977Labels = Sparse.eval nodeValue977 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 977) = mixedMoment B node977 node977Labels := rfl
  simpa [nodeValue977, Sparse.eval] using hc.symm

theorem sound980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node980 node980Labels = Sparse.eval nodeValue980 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 980) = mixedMoment B node980 node980Labels := rfl
  simpa [nodeValue980, Sparse.eval] using hc.symm

theorem sound1017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1017 node1017Labels = Sparse.eval nodeValue1017 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1017) = mixedMoment B node1017 node1017Labels := rfl
  simpa [nodeValue1017, Sparse.eval] using hc.symm

theorem sound1018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1018 node1018Labels = Sparse.eval nodeValue1018 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1018) = mixedMoment B node1018 node1018Labels := rfl
  simpa [nodeValue1018, Sparse.eval] using hc.symm

theorem sound1019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1019 node1019Labels = Sparse.eval nodeValue1019 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1019) = mixedMoment B node1019 node1019Labels := rfl
  simpa [nodeValue1019, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1086 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1086 node1086Labels = 0 := by
  exact mixedMoment_order_one B hB node1086 node1086Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1025 node1025Labels = Sparse.eval nodeValue1025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1025) = mixedMoment B node1025 node1025Labels := rfl
  simpa [nodeValue1025, Sparse.eval] using hc.symm

theorem sound1035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1035 node1035Labels = Sparse.eval nodeValue1035 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1035) = mixedMoment B node1035 node1035Labels := rfl
  simpa [nodeValue1035, Sparse.eval] using hc.symm

theorem sound1041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1041 node1041Labels = Sparse.eval nodeValue1041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1041) = mixedMoment B node1041 node1041Labels := rfl
  simpa [nodeValue1041, Sparse.eval] using hc.symm

theorem sound1046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1046 node1046Labels = Sparse.eval nodeValue1046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1046) = mixedMoment B node1046 node1046Labels := rfl
  simpa [nodeValue1046, Sparse.eval] using hc.symm

theorem sound1050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1050 node1050Labels = Sparse.eval nodeValue1050 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1050) = mixedMoment B node1050 node1050Labels := rfl
  simpa [nodeValue1050, Sparse.eval] using hc.symm

theorem sound1086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1086 node1086Labels = Sparse.eval nodeValue1086 (mixedVector B) := by
  simpa only [nodeValue1086, Sparse.eval_nil] using zero1086 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1514 node1514Labels = Sparse.eval nodeValue1514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1514) = mixedMoment B node1514 node1514Labels := rfl
  simpa [nodeValue1514, Sparse.eval] using hc.symm

theorem sound1532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1532 node1532Labels = Sparse.eval nodeValue1532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1532) = mixedMoment B node1532 node1532Labels := rfl
  simpa [nodeValue1532, Sparse.eval] using hc.symm

theorem sound1533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1533 node1533Labels = Sparse.eval nodeValue1533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1533) = mixedMoment B node1533 node1533Labels := rfl
  simpa [nodeValue1533, Sparse.eval] using hc.symm

theorem sound1535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1535 node1535Labels = Sparse.eval nodeValue1535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1535) = mixedMoment B node1535 node1535Labels := rfl
  simpa [nodeValue1535, Sparse.eval] using hc.symm

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

theorem sound1670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1670 node1670Labels = Sparse.eval nodeValue1670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1670) = mixedMoment B node1670 node1670Labels := rfl
  simpa [nodeValue1670, Sparse.eval] using hc.symm

theorem sound1688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1688 node1688Labels = Sparse.eval nodeValue1688 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1688) = mixedMoment B node1688 node1688Labels := rfl
  simpa [nodeValue1688, Sparse.eval] using hc.symm

theorem sound1689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1689 node1689Labels = Sparse.eval nodeValue1689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1689) = mixedMoment B node1689 node1689Labels := rfl
  simpa [nodeValue1689, Sparse.eval] using hc.symm

theorem sound1690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1690 node1690Labels = Sparse.eval nodeValue1690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1690) = mixedMoment B node1690 node1690Labels := rfl
  simpa [nodeValue1690, Sparse.eval] using hc.symm

theorem sound1695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1695 node1695Labels = Sparse.eval nodeValue1695 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1695) = mixedMoment B node1695 node1695Labels := rfl
  simpa [nodeValue1695, Sparse.eval] using hc.symm

theorem sound1720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1720 node1720Labels = Sparse.eval nodeValue1720 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1720) = mixedMoment B node1720 node1720Labels := rfl
  simpa [nodeValue1720, Sparse.eval] using hc.symm

theorem sound1723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1723 node1723Labels = Sparse.eval nodeValue1723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1723) = mixedMoment B node1723 node1723Labels := rfl
  simpa [nodeValue1723, Sparse.eval] using hc.symm

theorem sound1724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1724 node1724Labels = Sparse.eval nodeValue1724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1724) = mixedMoment B node1724 node1724Labels := rfl
  simpa [nodeValue1724, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1753 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1753 node1753Labels = 0 := by
  exact mixedMoment_order_one B hB node1753 node1753Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1748 node1748Labels = Sparse.eval nodeValue1748 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1748) = mixedMoment B node1748 node1748Labels := rfl
  simpa [nodeValue1748, Sparse.eval] using hc.symm

theorem sound1749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1749 node1749Labels = Sparse.eval nodeValue1749 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1749) = mixedMoment B node1749 node1749Labels := rfl
  simpa [nodeValue1749, Sparse.eval] using hc.symm

theorem sound1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1750 node1750Labels = Sparse.eval nodeValue1750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1750) = mixedMoment B node1750 node1750Labels := rfl
  simpa [nodeValue1750, Sparse.eval] using hc.symm

theorem sound1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1751 node1751Labels = Sparse.eval nodeValue1751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1751) = mixedMoment B node1751 node1751Labels := rfl
  simpa [nodeValue1751, Sparse.eval] using hc.symm

theorem sound1753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1753 node1753Labels = Sparse.eval nodeValue1753 (mixedVector B) := by
  simpa only [nodeValue1753, Sparse.eval_nil] using zero1753 B _hB _hF

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

theorem sound1897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1897 node1897Labels = Sparse.eval nodeValue1897 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1897) = mixedMoment B node1897 node1897Labels := rfl
  simpa [nodeValue1897, Sparse.eval] using hc.symm

theorem sound1898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1898 node1898Labels = Sparse.eval nodeValue1898 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1898) = mixedMoment B node1898 node1898Labels := rfl
  simpa [nodeValue1898, Sparse.eval] using hc.symm

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

theorem sound2008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2008 node2008Labels = Sparse.eval nodeValue2008 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2008) = mixedMoment B node2008 node2008Labels := rfl
  simpa [nodeValue2008, Sparse.eval] using hc.symm

theorem sound2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2025 node2025Labels = Sparse.eval nodeValue2025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2025) = mixedMoment B node2025 node2025Labels := rfl
  simpa [nodeValue2025, Sparse.eval] using hc.symm

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

theorem sound2070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2070 node2070Labels = Sparse.eval nodeValue2070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2070) = mixedMoment B node2070 node2070Labels := rfl
  simpa [nodeValue2070, Sparse.eval] using hc.symm

theorem sound2071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2071 node2071Labels = Sparse.eval nodeValue2071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2071) = mixedMoment B node2071 node2071Labels := rfl
  simpa [nodeValue2071, Sparse.eval] using hc.symm

theorem sound2087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2087 node2087Labels = Sparse.eval nodeValue2087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2087) = mixedMoment B node2087 node2087Labels := rfl
  simpa [nodeValue2087, Sparse.eval] using hc.symm

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

theorem sound2112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2112 node2112Labels = Sparse.eval nodeValue2112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2112) = mixedMoment B node2112 node2112Labels := rfl
  simpa [nodeValue2112, Sparse.eval] using hc.symm

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

theorem sound2187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2187 node2187Labels = Sparse.eval nodeValue2187 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2187) = mixedMoment B node2187 node2187Labels := rfl
  simpa [nodeValue2187, Sparse.eval] using hc.symm

theorem sound2190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2190 node2190Labels = Sparse.eval nodeValue2190 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2190) = mixedMoment B node2190 node2190Labels := rfl
  simpa [nodeValue2190, Sparse.eval] using hc.symm

theorem sound2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2191 node2191Labels = Sparse.eval nodeValue2191 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2191) = mixedMoment B node2191 node2191Labels := rfl
  simpa [nodeValue2191, Sparse.eval] using hc.symm

theorem sound2193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2193 node2193Labels = Sparse.eval nodeValue2193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2193) = mixedMoment B node2193 node2193Labels := rfl
  simpa [nodeValue2193, Sparse.eval] using hc.symm

theorem sound2224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2224 node2224Labels = Sparse.eval nodeValue2224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2224) = mixedMoment B node2224 node2224Labels := rfl
  simpa [nodeValue2224, Sparse.eval] using hc.symm

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

theorem zero2291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = 0 := by
  exact mixedMoment_order_one B hB node2291 node2291Labels 1
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

theorem sound2242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2242 node2242Labels = Sparse.eval nodeValue2242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2242) = mixedMoment B node2242 node2242Labels := rfl
  simpa [nodeValue2242, Sparse.eval] using hc.symm

theorem sound2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2247 node2247Labels = Sparse.eval nodeValue2247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2247) = mixedMoment B node2247 node2247Labels := rfl
  simpa [nodeValue2247, Sparse.eval] using hc.symm

theorem sound2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2287 node2287Labels = Sparse.eval nodeValue2287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2287) = mixedMoment B node2287 node2287Labels := rfl
  simpa [nodeValue2287, Sparse.eval] using hc.symm

theorem sound2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2290 node2290Labels = Sparse.eval nodeValue2290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2290) = mixedMoment B node2290 node2290Labels := rfl
  simpa [nodeValue2290, Sparse.eval] using hc.symm

theorem sound2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = Sparse.eval nodeValue2291 (mixedVector B) := by
  simpa only [nodeValue2291, Sparse.eval_nil] using zero2291 B _hB _hF

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

theorem sound4079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4079 node4079Labels = Sparse.eval nodeValue4079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4079) = mixedMoment B node4079 node4079Labels := rfl
  simpa [nodeValue4079, Sparse.eval] using hc.symm

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node581 node581Labels = Sparse.eval nodeValue581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 581) = mixedMoment B node581 node581Labels := rfl
  simpa [nodeValue581, Sparse.eval] using hc.symm

theorem sound587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node587 node587Labels = Sparse.eval nodeValue587 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 587) = mixedMoment B node587 node587Labels := rfl
  simpa [nodeValue587, Sparse.eval] using hc.symm

theorem sound589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node589 node589Labels = Sparse.eval nodeValue589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 589) = mixedMoment B node589 node589Labels := rfl
  simpa [nodeValue589, Sparse.eval] using hc.symm

theorem sound611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node611 node611Labels = Sparse.eval nodeValue611 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 611) = mixedMoment B node611 node611Labels := rfl
  simpa [nodeValue611, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4153 node4153Labels = Sparse.eval nodeValue4153 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4153) = mixedMoment B node4153 node4153Labels := rfl
  simpa [nodeValue4153, Sparse.eval] using hc.symm

theorem sound4159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4159 node4159Labels = Sparse.eval nodeValue4159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4159) = mixedMoment B node4159 node4159Labels := rfl
  simpa [nodeValue4159, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4161 node4161Labels = Sparse.eval nodeValue4161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4161) = mixedMoment B node4161 node4161Labels := rfl
  simpa [nodeValue4161, Sparse.eval] using hc.symm

theorem sound4183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4183 node4183Labels = Sparse.eval nodeValue4183 (mixedVector B) := by
  have h := singleton4183 B _hB
  rw [sound611 B _hB _hF, sound1535 B _hB _hF] at h
  norm_num [nodeValue4183, nodeValue611, nodeValue1535, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4327 node4327Labels = Sparse.eval nodeValue4327 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4327) = mixedMoment B node4327 node4327Labels := rfl
  simpa [nodeValue4327, Sparse.eval] using hc.symm

theorem sound4333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4333 node4333Labels = Sparse.eval nodeValue4333 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4333) = mixedMoment B node4333 node4333Labels := rfl
  simpa [nodeValue4333, Sparse.eval] using hc.symm

theorem sound4335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4335 node4335Labels = Sparse.eval nodeValue4335 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4335) = mixedMoment B node4335 node4335Labels := rfl
  simpa [nodeValue4335, Sparse.eval] using hc.symm

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

theorem sound4352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4352 node4352Labels = Sparse.eval nodeValue4352 (mixedVector B) := by
  have h := singleton4352 B _hB
  rw [sound930 B _hB _hF, sound1690 B _hB _hF] at h
  norm_num [nodeValue4352, nodeValue930, nodeValue1690, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4358 node4358Labels = Sparse.eval nodeValue4358 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4358) = mixedMoment B node4358 node4358Labels := rfl
  simpa [nodeValue4358, Sparse.eval] using hc.symm

theorem sound4367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4367 node4367Labels = Sparse.eval nodeValue4367 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4367) = mixedMoment B node4367 node4367Labels := rfl
  simpa [nodeValue4367, Sparse.eval] using hc.symm

theorem sound4374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4374 node4374Labels = Sparse.eval nodeValue4374 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4374) = mixedMoment B node4374 node4374Labels := rfl
  simpa [nodeValue4374, Sparse.eval] using hc.symm

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

theorem sound4440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4440 node4440Labels = Sparse.eval nodeValue4440 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4440) = mixedMoment B node4440 node4440Labels := rfl
  simpa [nodeValue4440, Sparse.eval] using hc.symm

theorem sound4445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4445 node4445Labels = Sparse.eval nodeValue4445 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4445) = mixedMoment B node4445 node4445Labels := rfl
  simpa [nodeValue4445, Sparse.eval] using hc.symm

theorem sound4458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4458 node4458Labels = Sparse.eval nodeValue4458 (mixedVector B) := by
  have h := singleton4458 B _hB
  rw [sound1041 B _hB _hF, sound1724 B _hB _hF] at h
  norm_num [nodeValue4458, nodeValue1041, nodeValue1724, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4463 node4463Labels = Sparse.eval nodeValue4463 (mixedVector B) := by
  have h := singleton4463 B _hB
  rw [sound1046 B _hB _hF, sound1750 B _hB _hF] at h
  norm_num [nodeValue4463, nodeValue1046, nodeValue1750, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4467 node4467Labels = Sparse.eval nodeValue4467 (mixedVector B) := by
  have h := singleton4467 B _hB
  rw [sound1050 B _hB _hF, sound1751 B _hB _hF] at h
  norm_num [nodeValue4467, nodeValue1050, nodeValue1751, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4502 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4502 node4502Labels = 0 := by
  exact mixedMoment_order_one B hB node4502 node4502Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4502 node4502Labels = Sparse.eval nodeValue4502 (mixedVector B) := by
  simpa only [nodeValue4502, Sparse.eval_nil] using zero4502 B _hB _hF

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

theorem sound4807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4807 node4807Labels = Sparse.eval nodeValue4807 (mixedVector B) := by
  have h := singleton4807 B _hB
  rw [sound2025 B _hB _hF, sound2224 B _hB _hF] at h
  norm_num [nodeValue4807, nodeValue2025, nodeValue2224, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem zero4895 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = 0 := by
  exact mixedMoment_order_one B hB node4895 node4895Labels 1
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

theorem sound4871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4871 node4871Labels = Sparse.eval nodeValue4871 (mixedVector B) := by
  have h := singleton4871 B _hB
  rw [sound2112 B _hB _hF, sound2287 B _hB _hF] at h
  norm_num [nodeValue4871, nodeValue2112, nodeValue2287, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4890 node4890Labels = Sparse.eval nodeValue4890 (mixedVector B) := by
  have h := singleton4890 B _hB
  rw [sound2247 B _hB _hF, sound2290 B _hB _hF] at h
  norm_num [nodeValue4890, nodeValue2247, nodeValue2290, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = Sparse.eval nodeValue4895 (mixedVector B) := by
  simpa only [nodeValue4895, Sparse.eval_nil] using zero4895 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources41
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1329 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1329 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1329 + difference 0 0) (sourceB1329 + difference 0 0) sourceC1329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1019) := by
    have ha : (tripleCharges (sourceA1329 + difference 0 0) (sourceB1329 + difference 0 0) sourceC1329) = raw21111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1329 sourceB1329 sourceC1329 difference raw21111; decide +kernel
    rw [ha]
    exact (canonical21111 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1329 + difference 0 1) (sourceB1329 + difference 1 0) sourceC1329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2087) := by
    have ha : (tripleCharges (sourceA1329 + difference 0 1) (sourceB1329 + difference 1 0) sourceC1329) = raw21112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1329 sourceB1329 sourceC1329 difference raw21112; decide +kernel
    rw [ha]
    exact (canonical21112 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1329 + difference 0 2) (sourceB1329 + difference 2 0) sourceC1329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2087) := by
    have ha : (tripleCharges (sourceA1329 + difference 0 2) (sourceB1329 + difference 2 0) sourceC1329) = raw21113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1329 sourceB1329 sourceC1329 difference raw21113; decide +kernel
    rw [ha]
    exact (canonical21113 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1329 + difference 0 3) (sourceB1329 + difference 3 0) sourceC1329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2008) := by
    have ha : (tripleCharges (sourceA1329 + difference 0 3) (sourceB1329 + difference 3 0) sourceC1329) = raw21114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1329 sourceB1329 sourceC1329 difference raw21114; decide +kernel
    rw [ha]
    exact (canonical21114 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1329 + difference 0 4) (sourceB1329 + difference 4 0) sourceC1329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1329 + difference 0 4) (sourceB1329 + difference 4 0) sourceC1329) = raw21115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1329 sourceB1329 sourceC1329 difference raw21115; decide +kernel
    rw [ha]
    exact (canonical21115 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1329 + difference 0 5) (sourceB1329 + difference 5 0) sourceC1329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA1329 + difference 0 5) (sourceB1329 + difference 5 0) sourceC1329) = raw21116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1329 sourceB1329 sourceC1329 difference raw21116; decide +kernel
    rw [ha]
    exact (canonical21116 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1329 + sourceB1329) sourceC1329) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1329 + sourceB1329) sourceC1329) = raw21117 := by
      apply Matrix.ext; unfold doubleCharges sourceA1329 sourceB1329 sourceC1329 raw21117; decide +kernel
    rw [ha]
    exact (canonical21117 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1329 sourceB1329 sourceC1329
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1329, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1330 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1330 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1330 + difference 0 5) (sourceB1330 + difference 5 0) sourceC1330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA1330 + difference 0 5) (sourceB1330 + difference 5 0) sourceC1330) = raw21116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1330 sourceB1330 sourceC1330 difference raw21116; decide +kernel
    rw [ha]
    exact (canonical21116 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1330 + difference 1 5) (sourceB1330 + difference 5 1) sourceC1330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1330 + difference 1 5) (sourceB1330 + difference 5 1) sourceC1330) = raw21118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1330 sourceB1330 sourceC1330 difference raw21118; decide +kernel
    rw [ha]
    exact (canonical21118 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1330 + difference 2 5) (sourceB1330 + difference 5 2) sourceC1330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1330 + difference 2 5) (sourceB1330 + difference 5 2) sourceC1330) = raw21119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1330 sourceB1330 sourceC1330 difference raw21119; decide +kernel
    rw [ha]
    exact (canonical21119 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1330 + difference 3 5) (sourceB1330 + difference 5 3) sourceC1330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1017) := by
    have ha : (tripleCharges (sourceA1330 + difference 3 5) (sourceB1330 + difference 5 3) sourceC1330) = raw21120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1330 sourceB1330 sourceC1330 difference raw21120; decide +kernel
    rw [ha]
    exact (canonical21120 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1330 + difference 4 5) (sourceB1330 + difference 5 4) sourceC1330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1025) := by
    have ha : (tripleCharges (sourceA1330 + difference 4 5) (sourceB1330 + difference 5 4) sourceC1330) = raw21121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1330 sourceB1330 sourceC1330 difference raw21121; decide +kernel
    rw [ha]
    exact (canonical21121 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1330 + difference 5 5) (sourceB1330 + difference 5 5) sourceC1330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1019) := by
    have ha : (tripleCharges (sourceA1330 + difference 5 5) (sourceB1330 + difference 5 5) sourceC1330) = raw21111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1330 sourceB1330 sourceC1330 difference raw21111; decide +kernel
    rw [ha]
    exact (canonical21111 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1330 + sourceB1330) sourceC1330) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1330 + sourceB1330) sourceC1330) = raw21117 := by
      apply Matrix.ext; unfold doubleCharges sourceA1330 sourceB1330 sourceC1330 raw21117; decide +kernel
    rw [ha]
    exact (canonical21117 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1330 sourceB1330 sourceC1330
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1330, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1331 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1331 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1331 + difference 0 0) (sourceB1331 + difference 0 0) sourceC1331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 972) := by
    have ha : (tripleCharges (sourceA1331 + difference 0 0) (sourceB1331 + difference 0 0) sourceC1331) = raw21122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1331 sourceB1331 sourceC1331 difference raw21122; decide +kernel
    rw [ha]
    exact (canonical21122 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1331 + difference 0 1) (sourceB1331 + difference 1 0) sourceC1331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2071) := by
    have ha : (tripleCharges (sourceA1331 + difference 0 1) (sourceB1331 + difference 1 0) sourceC1331) = raw21123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1331 sourceB1331 sourceC1331 difference raw21123; decide +kernel
    rw [ha]
    exact (canonical21123 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1331 + difference 0 2) (sourceB1331 + difference 2 0) sourceC1331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2071) := by
    have ha : (tripleCharges (sourceA1331 + difference 0 2) (sourceB1331 + difference 2 0) sourceC1331) = raw21124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1331 sourceB1331 sourceC1331 difference raw21124; decide +kernel
    rw [ha]
    exact (canonical21124 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1331 + difference 0 3) (sourceB1331 + difference 3 0) sourceC1331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA1331 + difference 0 3) (sourceB1331 + difference 3 0) sourceC1331) = raw21125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1331 sourceB1331 sourceC1331 difference raw21125; decide +kernel
    rw [ha]
    exact (canonical21125 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1331 + difference 0 4) (sourceB1331 + difference 4 0) sourceC1331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2187) := by
    have ha : (tripleCharges (sourceA1331 + difference 0 4) (sourceB1331 + difference 4 0) sourceC1331) = raw21126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1331 sourceB1331 sourceC1331 difference raw21126; decide +kernel
    rw [ha]
    exact (canonical21126 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1331 + difference 0 5) (sourceB1331 + difference 5 0) sourceC1331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1331 + difference 0 5) (sourceB1331 + difference 5 0) sourceC1331) = raw21127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1331 sourceB1331 sourceC1331 difference raw21127; decide +kernel
    rw [ha]
    exact (canonical21127 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1331 + sourceB1331) sourceC1331) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1331 + sourceB1331) sourceC1331) = raw21128 := by
      apply Matrix.ext; unfold doubleCharges sourceA1331 sourceB1331 sourceC1331 raw21128; decide +kernel
    rw [ha]
    exact (canonical21128 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1331 sourceB1331 sourceC1331
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1331, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1332 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1332 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1332 + difference 0 5) (sourceB1332 + difference 5 0) sourceC1332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1332 + difference 0 5) (sourceB1332 + difference 5 0) sourceC1332) = raw21127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1332 sourceB1332 sourceC1332 difference raw21127; decide +kernel
    rw [ha]
    exact (canonical21127 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1332 + difference 1 5) (sourceB1332 + difference 5 1) sourceC1332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1332 + difference 1 5) (sourceB1332 + difference 5 1) sourceC1332) = raw21129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1332 sourceB1332 sourceC1332 difference raw21129; decide +kernel
    rw [ha]
    exact (canonical21129 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1332 + difference 2 5) (sourceB1332 + difference 5 2) sourceC1332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1332 + difference 2 5) (sourceB1332 + difference 5 2) sourceC1332) = raw21130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1332 sourceB1332 sourceC1332 difference raw21130; decide +kernel
    rw [ha]
    exact (canonical21130 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1332 + difference 3 5) (sourceB1332 + difference 5 3) sourceC1332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1018) := by
    have ha : (tripleCharges (sourceA1332 + difference 3 5) (sourceB1332 + difference 5 3) sourceC1332) = raw21131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1332 sourceB1332 sourceC1332 difference raw21131; decide +kernel
    rw [ha]
    exact (canonical21131 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1332 + difference 4 5) (sourceB1332 + difference 5 4) sourceC1332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 974) := by
    have ha : (tripleCharges (sourceA1332 + difference 4 5) (sourceB1332 + difference 5 4) sourceC1332) = raw21132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1332 sourceB1332 sourceC1332 difference raw21132; decide +kernel
    rw [ha]
    exact (canonical21132 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1332 + difference 5 5) (sourceB1332 + difference 5 5) sourceC1332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 972) := by
    have ha : (tripleCharges (sourceA1332 + difference 5 5) (sourceB1332 + difference 5 5) sourceC1332) = raw21122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1332 sourceB1332 sourceC1332 difference raw21122; decide +kernel
    rw [ha]
    exact (canonical21122 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1332 + sourceB1332) sourceC1332) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1332 + sourceB1332) sourceC1332) = raw21128 := by
      apply Matrix.ext; unfold doubleCharges sourceA1332 sourceB1332 sourceC1332 raw21128; decide +kernel
    rw [ha]
    exact (canonical21128 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1332 sourceB1332 sourceC1332
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1332, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1333 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1333 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1333 + difference 0 0) (sourceB1333 + difference 0 0) sourceC1333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 971) := by
    have ha : (tripleCharges (sourceA1333 + difference 0 0) (sourceB1333 + difference 0 0) sourceC1333) = raw21133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1333 sourceB1333 sourceC1333 difference raw21133; decide +kernel
    rw [ha]
    exact (canonical21133 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1333 + difference 0 1) (sourceB1333 + difference 1 0) sourceC1333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2070) := by
    have ha : (tripleCharges (sourceA1333 + difference 0 1) (sourceB1333 + difference 1 0) sourceC1333) = raw21134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1333 sourceB1333 sourceC1333 difference raw21134; decide +kernel
    rw [ha]
    exact (canonical21134 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1333 + difference 0 2) (sourceB1333 + difference 2 0) sourceC1333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2070) := by
    have ha : (tripleCharges (sourceA1333 + difference 0 2) (sourceB1333 + difference 2 0) sourceC1333) = raw21135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1333 sourceB1333 sourceC1333 difference raw21135; decide +kernel
    rw [ha]
    exact (canonical21135 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1333 + difference 0 3) (sourceB1333 + difference 3 0) sourceC1333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1897) := by
    have ha : (tripleCharges (sourceA1333 + difference 0 3) (sourceB1333 + difference 3 0) sourceC1333) = raw21136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1333 sourceB1333 sourceC1333 difference raw21136; decide +kernel
    rw [ha]
    exact (canonical21136 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1333 + difference 0 4) (sourceB1333 + difference 4 0) sourceC1333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1333 + difference 0 4) (sourceB1333 + difference 4 0) sourceC1333) = raw21137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1333 sourceB1333 sourceC1333 difference raw21137; decide +kernel
    rw [ha]
    exact (canonical21137 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1333 + difference 0 5) (sourceB1333 + difference 5 0) sourceC1333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA1333 + difference 0 5) (sourceB1333 + difference 5 0) sourceC1333) = raw21138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1333 sourceB1333 sourceC1333 difference raw21138; decide +kernel
    rw [ha]
    exact (canonical21138 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1333 + sourceB1333) sourceC1333) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1333 + sourceB1333) sourceC1333) = raw21139 := by
      apply Matrix.ext; unfold doubleCharges sourceA1333 sourceB1333 sourceC1333 raw21139; decide +kernel
    rw [ha]
    exact (canonical21139 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1333 sourceB1333 sourceC1333
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1333, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1334 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1334 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1334 + difference 0 5) (sourceB1334 + difference 5 0) sourceC1334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA1334 + difference 0 5) (sourceB1334 + difference 5 0) sourceC1334) = raw21138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1334 sourceB1334 sourceC1334 difference raw21138; decide +kernel
    rw [ha]
    exact (canonical21138 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1334 + difference 1 5) (sourceB1334 + difference 5 1) sourceC1334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1334 + difference 1 5) (sourceB1334 + difference 5 1) sourceC1334) = raw21140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1334 sourceB1334 sourceC1334 difference raw21140; decide +kernel
    rw [ha]
    exact (canonical21140 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1334 + difference 2 5) (sourceB1334 + difference 5 2) sourceC1334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1334 + difference 2 5) (sourceB1334 + difference 5 2) sourceC1334) = raw21141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1334 sourceB1334 sourceC1334 difference raw21141; decide +kernel
    rw [ha]
    exact (canonical21141 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1334 + difference 3 5) (sourceB1334 + difference 5 3) sourceC1334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1017) := by
    have ha : (tripleCharges (sourceA1334 + difference 3 5) (sourceB1334 + difference 5 3) sourceC1334) = raw21142 := by
      apply Matrix.ext; unfold tripleCharges sourceA1334 sourceB1334 sourceC1334 difference raw21142; decide +kernel
    rw [ha]
    exact (canonical21142 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1334 + difference 4 5) (sourceB1334 + difference 5 4) sourceC1334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 973) := by
    have ha : (tripleCharges (sourceA1334 + difference 4 5) (sourceB1334 + difference 5 4) sourceC1334) = raw21143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1334 sourceB1334 sourceC1334 difference raw21143; decide +kernel
    rw [ha]
    exact (canonical21143 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1334 + difference 5 5) (sourceB1334 + difference 5 5) sourceC1334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 971) := by
    have ha : (tripleCharges (sourceA1334 + difference 5 5) (sourceB1334 + difference 5 5) sourceC1334) = raw21133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1334 sourceB1334 sourceC1334 difference raw21133; decide +kernel
    rw [ha]
    exact (canonical21133 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1334 + sourceB1334) sourceC1334) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1334 + sourceB1334) sourceC1334) = raw21139 := by
      apply Matrix.ext; unfold doubleCharges sourceA1334 sourceB1334 sourceC1334 raw21139; decide +kernel
    rw [ha]
    exact (canonical21139 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1334 sourceB1334 sourceC1334
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1334, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1335 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1335 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1335 + difference 0 1) (sourceB1335 + difference 1 0) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA1335 + difference 0 1) (sourceB1335 + difference 1 0) sourceC1335) = raw11424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw11424; decide +kernel
    rw [ha]
    exact (canonical11424 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1335 + difference 0 2) (sourceB1335 + difference 2 0) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1335 + difference 0 2) (sourceB1335 + difference 2 0) sourceC1335) = raw11425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw11425; decide +kernel
    rw [ha]
    exact (canonical11425 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1335 + difference 0 3) (sourceB1335 + difference 3 0) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1335 + difference 0 3) (sourceB1335 + difference 3 0) sourceC1335) = raw11426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw11426; decide +kernel
    rw [ha]
    exact (canonical11426 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1335 + difference 0 4) (sourceB1335 + difference 4 0) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA1335 + difference 0 4) (sourceB1335 + difference 4 0) sourceC1335) = raw11427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw11427; decide +kernel
    rw [ha]
    exact (canonical11427 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1335 + difference 0 5) (sourceB1335 + difference 5 0) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1335 + difference 0 5) (sourceB1335 + difference 5 0) sourceC1335) = raw21144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21144; decide +kernel
    rw [ha]
    exact (canonical21144 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1335 + difference 1 0) (sourceB1335 + difference 0 1) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4183) := by
    have ha : (tripleCharges (sourceA1335 + difference 1 0) (sourceB1335 + difference 0 1) sourceC1335) = raw21145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21145; decide +kernel
    rw [ha]
    exact (canonical21145 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1335 + difference 1 2) (sourceB1335 + difference 2 1) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA1335 + difference 1 2) (sourceB1335 + difference 2 1) sourceC1335) = raw21146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21146; decide +kernel
    rw [ha]
    exact (canonical21146 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1335 + difference 1 3) (sourceB1335 + difference 3 1) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA1335 + difference 1 3) (sourceB1335 + difference 3 1) sourceC1335) = raw21147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21147; decide +kernel
    rw [ha]
    exact (canonical21147 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1335 + difference 1 4) (sourceB1335 + difference 4 1) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1335 + difference 1 4) (sourceB1335 + difference 4 1) sourceC1335) = raw21148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21148; decide +kernel
    rw [ha]
    exact (canonical21148 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1335 + difference 1 5) (sourceB1335 + difference 5 1) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1335 + difference 1 5) (sourceB1335 + difference 5 1) sourceC1335) = raw11403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw11403; decide +kernel
    rw [ha]
    exact (canonical11403 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1335 + difference 2 0) (sourceB1335 + difference 0 2) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4153) := by
    have ha : (tripleCharges (sourceA1335 + difference 2 0) (sourceB1335 + difference 0 2) sourceC1335) = raw21149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21149; decide +kernel
    rw [ha]
    exact (canonical21149 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1335 + difference 2 1) (sourceB1335 + difference 1 2) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4367) := by
    have ha : (tripleCharges (sourceA1335 + difference 2 1) (sourceB1335 + difference 1 2) sourceC1335) = raw21150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21150; decide +kernel
    rw [ha]
    exact (canonical21150 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1335 + difference 2 3) (sourceB1335 + difference 3 2) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4327) := by
    have ha : (tripleCharges (sourceA1335 + difference 2 3) (sourceB1335 + difference 3 2) sourceC1335) = raw21151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21151; decide +kernel
    rw [ha]
    exact (canonical21151 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1335 + difference 2 4) (sourceB1335 + difference 4 2) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA1335 + difference 2 4) (sourceB1335 + difference 4 2) sourceC1335) = raw21152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21152; decide +kernel
    rw [ha]
    exact (canonical21152 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1335 + difference 2 5) (sourceB1335 + difference 5 2) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1335 + difference 2 5) (sourceB1335 + difference 5 2) sourceC1335) = raw11408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw11408; decide +kernel
    rw [ha]
    exact (canonical11408 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1335 + difference 3 0) (sourceB1335 + difference 0 3) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4153) := by
    have ha : (tripleCharges (sourceA1335 + difference 3 0) (sourceB1335 + difference 0 3) sourceC1335) = raw21153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21153; decide +kernel
    rw [ha]
    exact (canonical21153 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1335 + difference 3 1) (sourceB1335 + difference 1 3) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4367) := by
    have ha : (tripleCharges (sourceA1335 + difference 3 1) (sourceB1335 + difference 1 3) sourceC1335) = raw21154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21154; decide +kernel
    rw [ha]
    exact (canonical21154 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1335 + difference 3 2) (sourceB1335 + difference 2 3) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4327) := by
    have ha : (tripleCharges (sourceA1335 + difference 3 2) (sourceB1335 + difference 2 3) sourceC1335) = raw21155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21155; decide +kernel
    rw [ha]
    exact (canonical21155 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1335 + difference 3 4) (sourceB1335 + difference 4 3) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA1335 + difference 3 4) (sourceB1335 + difference 4 3) sourceC1335) = raw21156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21156; decide +kernel
    rw [ha]
    exact (canonical21156 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1335 + difference 3 5) (sourceB1335 + difference 5 3) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1335 + difference 3 5) (sourceB1335 + difference 5 3) sourceC1335) = raw11413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw11413; decide +kernel
    rw [ha]
    exact (canonical11413 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1335 + difference 4 0) (sourceB1335 + difference 0 4) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4161) := by
    have ha : (tripleCharges (sourceA1335 + difference 4 0) (sourceB1335 + difference 0 4) sourceC1335) = raw21157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21157; decide +kernel
    rw [ha]
    exact (canonical21157 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1335 + difference 4 1) (sourceB1335 + difference 1 4) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4374) := by
    have ha : (tripleCharges (sourceA1335 + difference 4 1) (sourceB1335 + difference 1 4) sourceC1335) = raw21158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21158; decide +kernel
    rw [ha]
    exact (canonical21158 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1335 + difference 4 2) (sourceB1335 + difference 2 4) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA1335 + difference 4 2) (sourceB1335 + difference 2 4) sourceC1335) = raw21159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21159; decide +kernel
    rw [ha]
    exact (canonical21159 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1335 + difference 4 3) (sourceB1335 + difference 3 4) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA1335 + difference 4 3) (sourceB1335 + difference 3 4) sourceC1335) = raw21160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21160; decide +kernel
    rw [ha]
    exact (canonical21160 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1335 + difference 4 5) (sourceB1335 + difference 5 4) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1335 + difference 4 5) (sourceB1335 + difference 5 4) sourceC1335) = raw11418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw11418; decide +kernel
    rw [ha]
    exact (canonical11418 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1335 + difference 5 0) (sourceB1335 + difference 0 5) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4159) := by
    have ha : (tripleCharges (sourceA1335 + difference 5 0) (sourceB1335 + difference 0 5) sourceC1335) = raw21161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21161; decide +kernel
    rw [ha]
    exact (canonical21161 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1335 + difference 5 1) (sourceB1335 + difference 1 5) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4358) := by
    have ha : (tripleCharges (sourceA1335 + difference 5 1) (sourceB1335 + difference 1 5) sourceC1335) = raw21162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21162; decide +kernel
    rw [ha]
    exact (canonical21162 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1335 + difference 5 2) (sourceB1335 + difference 2 5) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4333) := by
    have ha : (tripleCharges (sourceA1335 + difference 5 2) (sourceB1335 + difference 2 5) sourceC1335) = raw21163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21163; decide +kernel
    rw [ha]
    exact (canonical21163 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1335 + difference 5 3) (sourceB1335 + difference 3 5) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4333) := by
    have ha : (tripleCharges (sourceA1335 + difference 5 3) (sourceB1335 + difference 3 5) sourceC1335) = raw21164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21164; decide +kernel
    rw [ha]
    exact (canonical21164 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1335 + difference 5 4) (sourceB1335 + difference 4 5) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4445) := by
    have ha : (tripleCharges (sourceA1335 + difference 5 4) (sourceB1335 + difference 4 5) sourceC1335) = raw21165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21165; decide +kernel
    rw [ha]
    exact (canonical21165 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1335 sourceB1335 sourceC1335
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1335, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1337 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1337 + difference 0 1) (sourceB1337 + difference 1 0) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA1337 + difference 0 1) (sourceB1337 + difference 1 0) sourceC1337) = raw11454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw11454; decide +kernel
    rw [ha]
    exact (canonical11454 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1337 + difference 0 2) (sourceB1337 + difference 2 0) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1337 + difference 0 2) (sourceB1337 + difference 2 0) sourceC1337) = raw11455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw11455; decide +kernel
    rw [ha]
    exact (canonical11455 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1337 + difference 0 3) (sourceB1337 + difference 3 0) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1337 + difference 0 3) (sourceB1337 + difference 3 0) sourceC1337) = raw11456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw11456; decide +kernel
    rw [ha]
    exact (canonical11456 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1337 + difference 0 4) (sourceB1337 + difference 4 0) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA1337 + difference 0 4) (sourceB1337 + difference 4 0) sourceC1337) = raw11457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw11457; decide +kernel
    rw [ha]
    exact (canonical11457 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1337 + difference 0 5) (sourceB1337 + difference 5 0) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA1337 + difference 0 5) (sourceB1337 + difference 5 0) sourceC1337) = raw21196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21196; decide +kernel
    rw [ha]
    exact (canonical21196 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1337 + difference 1 0) (sourceB1337 + difference 0 1) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1535) := by
    have ha : (tripleCharges (sourceA1337 + difference 1 0) (sourceB1337 + difference 0 1) sourceC1337) = raw21197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21197; decide +kernel
    rw [ha]
    exact (canonical21197 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1337 + difference 1 2) (sourceB1337 + difference 2 1) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1690) := by
    have ha : (tripleCharges (sourceA1337 + difference 1 2) (sourceB1337 + difference 2 1) sourceC1337) = raw21198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21198; decide +kernel
    rw [ha]
    exact (canonical21198 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1337 + difference 1 3) (sourceB1337 + difference 3 1) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1690) := by
    have ha : (tripleCharges (sourceA1337 + difference 1 3) (sourceB1337 + difference 3 1) sourceC1337) = raw21199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21199; decide +kernel
    rw [ha]
    exact (canonical21199 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1337 + difference 1 4) (sourceB1337 + difference 4 1) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1337 + difference 1 4) (sourceB1337 + difference 4 1) sourceC1337) = raw21200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21200; decide +kernel
    rw [ha]
    exact (canonical21200 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1337 + difference 1 5) (sourceB1337 + difference 5 1) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1753) := by
    have ha : (tripleCharges (sourceA1337 + difference 1 5) (sourceB1337 + difference 5 1) sourceC1337) = raw11433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw11433; decide +kernel
    rw [ha]
    exact (canonical11433 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1337 + difference 2 0) (sourceB1337 + difference 0 2) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1514) := by
    have ha : (tripleCharges (sourceA1337 + difference 2 0) (sourceB1337 + difference 0 2) sourceC1337) = raw21201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21201; decide +kernel
    rw [ha]
    exact (canonical21201 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1337 + difference 2 1) (sourceB1337 + difference 1 2) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA1337 + difference 2 1) (sourceB1337 + difference 1 2) sourceC1337) = raw21202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21202; decide +kernel
    rw [ha]
    exact (canonical21202 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1337 + difference 2 3) (sourceB1337 + difference 3 2) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1670) := by
    have ha : (tripleCharges (sourceA1337 + difference 2 3) (sourceB1337 + difference 3 2) sourceC1337) = raw21203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21203; decide +kernel
    rw [ha]
    exact (canonical21203 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1337 + difference 2 4) (sourceB1337 + difference 4 2) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1337 + difference 2 4) (sourceB1337 + difference 4 2) sourceC1337) = raw21204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21204; decide +kernel
    rw [ha]
    exact (canonical21204 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1337 + difference 2 5) (sourceB1337 + difference 5 2) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1337 + difference 2 5) (sourceB1337 + difference 5 2) sourceC1337) = raw11438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw11438; decide +kernel
    rw [ha]
    exact (canonical11438 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1337 + difference 3 0) (sourceB1337 + difference 0 3) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1514) := by
    have ha : (tripleCharges (sourceA1337 + difference 3 0) (sourceB1337 + difference 0 3) sourceC1337) = raw21205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21205; decide +kernel
    rw [ha]
    exact (canonical21205 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1337 + difference 3 1) (sourceB1337 + difference 1 3) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA1337 + difference 3 1) (sourceB1337 + difference 1 3) sourceC1337) = raw21206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21206; decide +kernel
    rw [ha]
    exact (canonical21206 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1337 + difference 3 2) (sourceB1337 + difference 2 3) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1670) := by
    have ha : (tripleCharges (sourceA1337 + difference 3 2) (sourceB1337 + difference 2 3) sourceC1337) = raw21207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21207; decide +kernel
    rw [ha]
    exact (canonical21207 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1337 + difference 3 4) (sourceB1337 + difference 4 3) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1337 + difference 3 4) (sourceB1337 + difference 4 3) sourceC1337) = raw21208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21208; decide +kernel
    rw [ha]
    exact (canonical21208 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1337 + difference 3 5) (sourceB1337 + difference 5 3) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1337 + difference 3 5) (sourceB1337 + difference 5 3) sourceC1337) = raw11443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw11443; decide +kernel
    rw [ha]
    exact (canonical11443 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1337 + difference 4 0) (sourceB1337 + difference 0 4) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1533) := by
    have ha : (tripleCharges (sourceA1337 + difference 4 0) (sourceB1337 + difference 0 4) sourceC1337) = raw21209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21209; decide +kernel
    rw [ha]
    exact (canonical21209 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1337 + difference 4 1) (sourceB1337 + difference 1 4) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA1337 + difference 4 1) (sourceB1337 + difference 1 4) sourceC1337) = raw21210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21210; decide +kernel
    rw [ha]
    exact (canonical21210 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1337 + difference 4 2) (sourceB1337 + difference 2 4) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA1337 + difference 4 2) (sourceB1337 + difference 2 4) sourceC1337) = raw21211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21211; decide +kernel
    rw [ha]
    exact (canonical21211 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1337 + difference 4 3) (sourceB1337 + difference 3 4) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA1337 + difference 4 3) (sourceB1337 + difference 3 4) sourceC1337) = raw21212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21212; decide +kernel
    rw [ha]
    exact (canonical21212 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1337 + difference 4 5) (sourceB1337 + difference 5 4) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1337 + difference 4 5) (sourceB1337 + difference 5 4) sourceC1337) = raw11448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw11448; decide +kernel
    rw [ha]
    exact (canonical11448 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1337 + difference 5 0) (sourceB1337 + difference 0 5) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1532) := by
    have ha : (tripleCharges (sourceA1337 + difference 5 0) (sourceB1337 + difference 0 5) sourceC1337) = raw21213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21213; decide +kernel
    rw [ha]
    exact (canonical21213 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1337 + difference 5 1) (sourceB1337 + difference 1 5) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1695) := by
    have ha : (tripleCharges (sourceA1337 + difference 5 1) (sourceB1337 + difference 1 5) sourceC1337) = raw21214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21214; decide +kernel
    rw [ha]
    exact (canonical21214 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1337 + difference 5 2) (sourceB1337 + difference 2 5) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1688) := by
    have ha : (tripleCharges (sourceA1337 + difference 5 2) (sourceB1337 + difference 2 5) sourceC1337) = raw21215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21215; decide +kernel
    rw [ha]
    exact (canonical21215 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1337 + difference 5 3) (sourceB1337 + difference 3 5) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1688) := by
    have ha : (tripleCharges (sourceA1337 + difference 5 3) (sourceB1337 + difference 3 5) sourceC1337) = raw21216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21216; decide +kernel
    rw [ha]
    exact (canonical21216 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1337 + difference 5 4) (sourceB1337 + difference 4 5) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1749) := by
    have ha : (tripleCharges (sourceA1337 + difference 5 4) (sourceB1337 + difference 4 5) sourceC1337) = raw21217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21217; decide +kernel
    rw [ha]
    exact (canonical21217 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1337 sourceB1337 sourceC1337
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1337, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1338 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1338 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1338 + difference 0 0) (sourceB1338 + difference 0 0) sourceC1338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1338 + difference 0 0) (sourceB1338 + difference 0 0) sourceC1338) = raw21218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1338 sourceB1338 sourceC1338 difference raw21218; decide +kernel
    rw [ha]
    exact (canonical21218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1338 + difference 1 0) (sourceB1338 + difference 0 1) sourceC1338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 611) := by
    have ha : (tripleCharges (sourceA1338 + difference 1 0) (sourceB1338 + difference 0 1) sourceC1338) = raw21219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1338 sourceB1338 sourceC1338 difference raw21219; decide +kernel
    rw [ha]
    exact (canonical21219 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1338 + difference 2 0) (sourceB1338 + difference 0 2) sourceC1338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 581) := by
    have ha : (tripleCharges (sourceA1338 + difference 2 0) (sourceB1338 + difference 0 2) sourceC1338) = raw21220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1338 sourceB1338 sourceC1338 difference raw21220; decide +kernel
    rw [ha]
    exact (canonical21220 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1338 + difference 3 0) (sourceB1338 + difference 0 3) sourceC1338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 581) := by
    have ha : (tripleCharges (sourceA1338 + difference 3 0) (sourceB1338 + difference 0 3) sourceC1338) = raw21221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1338 sourceB1338 sourceC1338 difference raw21221; decide +kernel
    rw [ha]
    exact (canonical21221 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1338 + difference 4 0) (sourceB1338 + difference 0 4) sourceC1338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 589) := by
    have ha : (tripleCharges (sourceA1338 + difference 4 0) (sourceB1338 + difference 0 4) sourceC1338) = raw21222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1338 sourceB1338 sourceC1338 difference raw21222; decide +kernel
    rw [ha]
    exact (canonical21222 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1338 + difference 5 0) (sourceB1338 + difference 0 5) sourceC1338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 587) := by
    have ha : (tripleCharges (sourceA1338 + difference 5 0) (sourceB1338 + difference 0 5) sourceC1338) = raw21223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1338 sourceB1338 sourceC1338 difference raw21223; decide +kernel
    rw [ha]
    exact (canonical21223 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1338 + sourceB1338) sourceC1338) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1338 + sourceB1338) sourceC1338) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1338 sourceB1338 sourceC1338 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1338 sourceB1338 sourceC1338
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1338, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1339 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1339 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1339 + difference 1 0) (sourceB1339 + difference 0 1) sourceC1339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 611) := by
    have ha : (tripleCharges (sourceA1339 + difference 1 0) (sourceB1339 + difference 0 1) sourceC1339) = raw21219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1339 sourceB1339 sourceC1339 difference raw21219; decide +kernel
    rw [ha]
    exact (canonical21219 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1339 + difference 1 1) (sourceB1339 + difference 1 1) sourceC1339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1339 + difference 1 1) (sourceB1339 + difference 1 1) sourceC1339) = raw21218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1339 sourceB1339 sourceC1339 difference raw21218; decide +kernel
    rw [ha]
    exact (canonical21218 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1339 + difference 1 2) (sourceB1339 + difference 2 1) sourceC1339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 930) := by
    have ha : (tripleCharges (sourceA1339 + difference 1 2) (sourceB1339 + difference 2 1) sourceC1339) = raw21224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1339 sourceB1339 sourceC1339 difference raw21224; decide +kernel
    rw [ha]
    exact (canonical21224 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1339 + difference 1 3) (sourceB1339 + difference 3 1) sourceC1339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 930) := by
    have ha : (tripleCharges (sourceA1339 + difference 1 3) (sourceB1339 + difference 3 1) sourceC1339) = raw21225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1339 sourceB1339 sourceC1339 difference raw21225; decide +kernel
    rw [ha]
    exact (canonical21225 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1339 + difference 1 4) (sourceB1339 + difference 4 1) sourceC1339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1339 + difference 1 4) (sourceB1339 + difference 4 1) sourceC1339) = raw21226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1339 sourceB1339 sourceC1339 difference raw21226; decide +kernel
    rw [ha]
    exact (canonical21226 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1339 + difference 1 5) (sourceB1339 + difference 5 1) sourceC1339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1086) := by
    have ha : (tripleCharges (sourceA1339 + difference 1 5) (sourceB1339 + difference 5 1) sourceC1339) = raw21227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1339 sourceB1339 sourceC1339 difference raw21227; decide +kernel
    rw [ha]
    exact (canonical21227 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1339 + sourceB1339) sourceC1339) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1339 + sourceB1339) sourceC1339) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1339 sourceB1339 sourceC1339 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1339 sourceB1339 sourceC1339
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1339, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1340 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1340 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1340 + difference 0 1) (sourceB1340 + difference 1 0) sourceC1340) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA1340 + difference 0 1) (sourceB1340 + difference 1 0) sourceC1340) = raw11463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1340 sourceB1340 sourceC1340 difference raw11463; decide +kernel
    rw [ha]
    exact (canonical11463 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1340 + difference 1 1) (sourceB1340 + difference 1 1) sourceC1340) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1340 + difference 1 1) (sourceB1340 + difference 1 1) sourceC1340) = raw21218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1340 sourceB1340 sourceC1340 difference raw21218; decide +kernel
    rw [ha]
    exact (canonical21218 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1340 + difference 2 1) (sourceB1340 + difference 1 2) sourceC1340) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 945) := by
    have ha : (tripleCharges (sourceA1340 + difference 2 1) (sourceB1340 + difference 1 2) sourceC1340) = raw21228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1340 sourceB1340 sourceC1340 difference raw21228; decide +kernel
    rw [ha]
    exact (canonical21228 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1340 + difference 3 1) (sourceB1340 + difference 1 3) sourceC1340) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 945) := by
    have ha : (tripleCharges (sourceA1340 + difference 3 1) (sourceB1340 + difference 1 3) sourceC1340) = raw21229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1340 sourceB1340 sourceC1340 difference raw21229; decide +kernel
    rw [ha]
    exact (canonical21229 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1340 + difference 4 1) (sourceB1340 + difference 1 4) sourceC1340) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 953) := by
    have ha : (tripleCharges (sourceA1340 + difference 4 1) (sourceB1340 + difference 1 4) sourceC1340) = raw21230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1340 sourceB1340 sourceC1340 difference raw21230; decide +kernel
    rw [ha]
    exact (canonical21230 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1340 + difference 5 1) (sourceB1340 + difference 1 5) sourceC1340) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 951) := by
    have ha : (tripleCharges (sourceA1340 + difference 5 1) (sourceB1340 + difference 1 5) sourceC1340) = raw21231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1340 sourceB1340 sourceC1340 difference raw21231; decide +kernel
    rw [ha]
    exact (canonical21231 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1340 + sourceB1340) sourceC1340) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1340 + sourceB1340) sourceC1340) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1340 sourceB1340 sourceC1340 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1340 sourceB1340 sourceC1340
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1340, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1341 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1341 + difference 0 2) (sourceB1341 + difference 2 0) sourceC1341) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1341 + difference 0 2) (sourceB1341 + difference 2 0) sourceC1341) = raw21232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1341 sourceB1341 sourceC1341 difference raw21232; decide +kernel
    rw [ha]
    exact (canonical21232 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1341 + difference 1 2) (sourceB1341 + difference 2 1) sourceC1341) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 930) := by
    have ha : (tripleCharges (sourceA1341 + difference 1 2) (sourceB1341 + difference 2 1) sourceC1341) = raw21224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1341 sourceB1341 sourceC1341 difference raw21224; decide +kernel
    rw [ha]
    exact (canonical21224 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1341 + difference 2 2) (sourceB1341 + difference 2 2) sourceC1341) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1341 + difference 2 2) (sourceB1341 + difference 2 2) sourceC1341) = raw21218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1341 sourceB1341 sourceC1341 difference raw21218; decide +kernel
    rw [ha]
    exact (canonical21218 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1341 + difference 3 2) (sourceB1341 + difference 2 3) sourceC1341) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 905) := by
    have ha : (tripleCharges (sourceA1341 + difference 3 2) (sourceB1341 + difference 2 3) sourceC1341) = raw21233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1341 sourceB1341 sourceC1341 difference raw21233; decide +kernel
    rw [ha]
    exact (canonical21233 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1341 + difference 4 2) (sourceB1341 + difference 2 4) sourceC1341) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 913) := by
    have ha : (tripleCharges (sourceA1341 + difference 4 2) (sourceB1341 + difference 2 4) sourceC1341) = raw21234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1341 sourceB1341 sourceC1341 difference raw21234; decide +kernel
    rw [ha]
    exact (canonical21234 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1341 + difference 5 2) (sourceB1341 + difference 2 5) sourceC1341) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 911) := by
    have ha : (tripleCharges (sourceA1341 + difference 5 2) (sourceB1341 + difference 2 5) sourceC1341) = raw21235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1341 sourceB1341 sourceC1341 difference raw21235; decide +kernel
    rw [ha]
    exact (canonical21235 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1341 + sourceB1341) sourceC1341) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1341 + sourceB1341) sourceC1341) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1341 sourceB1341 sourceC1341 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1341 sourceB1341 sourceC1341
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1341, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1152 : Integer.Sparse.reindex keyMap MixedData.row1152 = numericRow1152 := by decide +kernel

theorem numericCheck1152 (x : Master → ℝ) : Integer.Sparse.eval numericRow1152 x =
    (1 : ℝ) * reducedSource1152 x := by
  norm_num [numericRow1152, reducedSource1152, Integer.Sparse.eval, Sparse.eval, nodeValue1019, nodeValue2008, nodeValue2087, nodeValue2193, nodeValue2242, nodeValue4080]

theorem reindexCheck1153 : Integer.Sparse.reindex keyMap MixedData.row1153 = numericRow1153 := by decide +kernel

theorem numericCheck1153 (x : Master → ℝ) : Integer.Sparse.eval numericRow1153 x =
    (1 : ℝ) * reducedSource1153 x := by
  norm_num [numericRow1153, reducedSource1153, Integer.Sparse.eval, Sparse.eval, nodeValue1017, nodeValue1019, nodeValue1025, nodeValue1035, nodeValue2242, nodeValue4080]

theorem reindexCheck1154 : Integer.Sparse.reindex keyMap MixedData.row1154 = numericRow1154 := by decide +kernel

theorem numericCheck1154 (x : Master → ℝ) : Integer.Sparse.eval numericRow1154 x =
    (1 : ℝ) * reducedSource1154 x := by
  norm_num [numericRow1154, reducedSource1154, Integer.Sparse.eval, Sparse.eval, nodeValue972, nodeValue1898, nodeValue2071, nodeValue2187, nodeValue2191, nodeValue4079]

theorem reindexCheck1155 : Integer.Sparse.reindex keyMap MixedData.row1155 = numericRow1155 := by decide +kernel

theorem numericCheck1155 (x : Master → ℝ) : Integer.Sparse.eval numericRow1155 x =
    (1 : ℝ) * reducedSource1155 x := by
  norm_num [numericRow1155, reducedSource1155, Integer.Sparse.eval, Sparse.eval, nodeValue972, nodeValue974, nodeValue980, nodeValue1018, nodeValue2191, nodeValue4079]

theorem reindexCheck1156 : Integer.Sparse.reindex keyMap MixedData.row1156 = numericRow1156 := by decide +kernel

theorem numericCheck1156 (x : Master → ℝ) : Integer.Sparse.eval numericRow1156 x =
    (1 : ℝ) * reducedSource1156 x := by
  norm_num [numericRow1156, reducedSource1156, Integer.Sparse.eval, Sparse.eval, nodeValue971, nodeValue1897, nodeValue2070, nodeValue2190, nodeValue2193, nodeValue4080]

theorem reindexCheck1157 : Integer.Sparse.reindex keyMap MixedData.row1157 = numericRow1157 := by decide +kernel

theorem numericCheck1157 (x : Master → ℝ) : Integer.Sparse.eval numericRow1157 x =
    (1 : ℝ) * reducedSource1157 x := by
  norm_num [numericRow1157, reducedSource1157, Integer.Sparse.eval, Sparse.eval, nodeValue971, nodeValue973, nodeValue977, nodeValue1017, nodeValue2190, nodeValue4080]

theorem reindexCheck1158 : Integer.Sparse.reindex keyMap MixedData.row1158 = numericRow1158 := by decide +kernel

theorem numericCheck1158 (x : Master → ℝ) : Integer.Sparse.eval numericRow1158 x =
    (4 : ℝ) * reducedSource1158 x := by
  norm_num [numericRow1158, reducedSource1158, Integer.Sparse.eval, Sparse.eval, nodeValue4153, nodeValue4159, nodeValue4161, nodeValue4183, nodeValue4327, nodeValue4333, nodeValue4335, nodeValue4352, nodeValue4358, nodeValue4367, nodeValue4374, nodeValue4440, nodeValue4445, nodeValue4458, nodeValue4463, nodeValue4467, nodeValue4502, nodeValue4807, nodeValue4871, nodeValue4890, nodeValue4895]
  ring

theorem reindexCheck1160 : Integer.Sparse.reindex keyMap MixedData.row1160 = numericRow1160 := by decide +kernel

theorem numericCheck1160 (x : Master → ℝ) : Integer.Sparse.eval numericRow1160 x =
    (1 : ℝ) * reducedSource1160 x := by
  norm_num [numericRow1160, reducedSource1160, Integer.Sparse.eval, Sparse.eval, nodeValue1514, nodeValue1532, nodeValue1533, nodeValue1535, nodeValue1670, nodeValue1688, nodeValue1689, nodeValue1690, nodeValue1695, nodeValue1720, nodeValue1723, nodeValue1724, nodeValue1748, nodeValue1749, nodeValue1750, nodeValue1751, nodeValue1753, nodeValue2224, nodeValue2287, nodeValue2290, nodeValue2291]

theorem reindexCheck1161 : Integer.Sparse.reindex keyMap MixedData.row1161 = numericRow1161 := by decide +kernel

theorem numericCheck1161 (x : Master → ℝ) : Integer.Sparse.eval numericRow1161 x =
    (1 : ℝ) * reducedSource1161 x := by
  norm_num [numericRow1161, reducedSource1161, Integer.Sparse.eval, Sparse.eval, nodeValue581, nodeValue587, nodeValue589, nodeValue611, nodeValue1046, nodeValue4083]

theorem reindexCheck1162 : Integer.Sparse.reindex keyMap MixedData.row1162 = numericRow1162 := by decide +kernel

theorem numericCheck1162 (x : Master → ℝ) : Integer.Sparse.eval numericRow1162 x =
    (1 : ℝ) * reducedSource1162 x := by
  norm_num [numericRow1162, reducedSource1162, Integer.Sparse.eval, Sparse.eval, nodeValue611, nodeValue930, nodeValue1046, nodeValue1086, nodeValue4083]

theorem reindexCheck1163 : Integer.Sparse.reindex keyMap MixedData.row1163 = numericRow1163 := by decide +kernel

theorem numericCheck1163 (x : Master → ℝ) : Integer.Sparse.eval numericRow1163 x =
    (1 : ℝ) * reducedSource1163 x := by
  norm_num [numericRow1163, reducedSource1163, Integer.Sparse.eval, Sparse.eval, nodeValue945, nodeValue951, nodeValue953, nodeValue1046, nodeValue2112, nodeValue4083]

theorem reindexCheck1164 : Integer.Sparse.reindex keyMap MixedData.row1164 = numericRow1164 := by decide +kernel

theorem numericCheck1164 (x : Master → ℝ) : Integer.Sparse.eval numericRow1164 x =
    (1 : ℝ) * reducedSource1164 x := by
  norm_num [numericRow1164, reducedSource1164, Integer.Sparse.eval, Sparse.eval, nodeValue905, nodeValue911, nodeValue913, nodeValue930, nodeValue1046, nodeValue2025, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1152 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1152 (mixedVector B) = 0 := by
  have h1019 : mixedVector B (Sum.inr 1019) = Sparse.eval nodeValue1019 (mixedVector B) := by
    change mixedMoment B node1019 node1019Labels = _
    exact sound1019 B hB hF
  have h2008 : mixedVector B (Sum.inr 2008) = Sparse.eval nodeValue2008 (mixedVector B) := by
    change mixedMoment B node2008 node2008Labels = _
    exact sound2008 B hB hF
  have h2087 : mixedVector B (Sum.inr 2087) = Sparse.eval nodeValue2087 (mixedVector B) := by
    change mixedMoment B node2087 node2087Labels = _
    exact sound2087 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1329, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1019, h2008, h2087, h2193, h2242, h4080, reducedSource1152] using sourceEq1329 B hB

theorem rowSound1152 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1152 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1152, numericCheck1152, reducedZero1152 B hB hF, mul_zero]

theorem reducedZero1153 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1153 (mixedVector B) = 0 := by
  have h1017 : mixedVector B (Sum.inr 1017) = Sparse.eval nodeValue1017 (mixedVector B) := by
    change mixedMoment B node1017 node1017Labels = _
    exact sound1017 B hB hF
  have h1019 : mixedVector B (Sum.inr 1019) = Sparse.eval nodeValue1019 (mixedVector B) := by
    change mixedMoment B node1019 node1019Labels = _
    exact sound1019 B hB hF
  have h1025 : mixedVector B (Sum.inr 1025) = Sparse.eval nodeValue1025 (mixedVector B) := by
    change mixedMoment B node1025 node1025Labels = _
    exact sound1025 B hB hF
  have h1035 : mixedVector B (Sum.inr 1035) = Sparse.eval nodeValue1035 (mixedVector B) := by
    change mixedMoment B node1035 node1035Labels = _
    exact sound1035 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1330, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1017, h1019, h1025, h1035, h2242, h4080, reducedSource1153] using sourceEq1330 B hB

theorem rowSound1153 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1153 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1153, numericCheck1153, reducedZero1153 B hB hF, mul_zero]

theorem reducedZero1154 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1154 (mixedVector B) = 0 := by
  have h972 : mixedVector B (Sum.inr 972) = Sparse.eval nodeValue972 (mixedVector B) := by
    change mixedMoment B node972 node972Labels = _
    exact sound972 B hB hF
  have h1898 : mixedVector B (Sum.inr 1898) = Sparse.eval nodeValue1898 (mixedVector B) := by
    change mixedMoment B node1898 node1898Labels = _
    exact sound1898 B hB hF
  have h2071 : mixedVector B (Sum.inr 2071) = Sparse.eval nodeValue2071 (mixedVector B) := by
    change mixedMoment B node2071 node2071Labels = _
    exact sound2071 B hB hF
  have h2187 : mixedVector B (Sum.inr 2187) = Sparse.eval nodeValue2187 (mixedVector B) := by
    change mixedMoment B node2187 node2187Labels = _
    exact sound2187 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1331, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h972, h1898, h2071, h2187, h2191, h4079, reducedSource1154] using sourceEq1331 B hB

theorem rowSound1154 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1154 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1154, numericCheck1154, reducedZero1154 B hB hF, mul_zero]

theorem reducedZero1155 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1155 (mixedVector B) = 0 := by
  have h972 : mixedVector B (Sum.inr 972) = Sparse.eval nodeValue972 (mixedVector B) := by
    change mixedMoment B node972 node972Labels = _
    exact sound972 B hB hF
  have h974 : mixedVector B (Sum.inr 974) = Sparse.eval nodeValue974 (mixedVector B) := by
    change mixedMoment B node974 node974Labels = _
    exact sound974 B hB hF
  have h980 : mixedVector B (Sum.inr 980) = Sparse.eval nodeValue980 (mixedVector B) := by
    change mixedMoment B node980 node980Labels = _
    exact sound980 B hB hF
  have h1018 : mixedVector B (Sum.inr 1018) = Sparse.eval nodeValue1018 (mixedVector B) := by
    change mixedMoment B node1018 node1018Labels = _
    exact sound1018 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1332, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h972, h974, h980, h1018, h2191, h4079, reducedSource1155] using sourceEq1332 B hB

theorem rowSound1155 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1155 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1155, numericCheck1155, reducedZero1155 B hB hF, mul_zero]

theorem reducedZero1156 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1156 (mixedVector B) = 0 := by
  have h971 : mixedVector B (Sum.inr 971) = Sparse.eval nodeValue971 (mixedVector B) := by
    change mixedMoment B node971 node971Labels = _
    exact sound971 B hB hF
  have h1897 : mixedVector B (Sum.inr 1897) = Sparse.eval nodeValue1897 (mixedVector B) := by
    change mixedMoment B node1897 node1897Labels = _
    exact sound1897 B hB hF
  have h2070 : mixedVector B (Sum.inr 2070) = Sparse.eval nodeValue2070 (mixedVector B) := by
    change mixedMoment B node2070 node2070Labels = _
    exact sound2070 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1333, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h971, h1897, h2070, h2190, h2193, h4080, reducedSource1156] using sourceEq1333 B hB

theorem rowSound1156 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1156 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1156, numericCheck1156, reducedZero1156 B hB hF, mul_zero]

theorem reducedZero1157 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1157 (mixedVector B) = 0 := by
  have h971 : mixedVector B (Sum.inr 971) = Sparse.eval nodeValue971 (mixedVector B) := by
    change mixedMoment B node971 node971Labels = _
    exact sound971 B hB hF
  have h973 : mixedVector B (Sum.inr 973) = Sparse.eval nodeValue973 (mixedVector B) := by
    change mixedMoment B node973 node973Labels = _
    exact sound973 B hB hF
  have h977 : mixedVector B (Sum.inr 977) = Sparse.eval nodeValue977 (mixedVector B) := by
    change mixedMoment B node977 node977Labels = _
    exact sound977 B hB hF
  have h1017 : mixedVector B (Sum.inr 1017) = Sparse.eval nodeValue1017 (mixedVector B) := by
    change mixedMoment B node1017 node1017Labels = _
    exact sound1017 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1334, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h971, h973, h977, h1017, h2190, h4080, reducedSource1157] using sourceEq1334 B hB

theorem rowSound1157 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1157 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1157, numericCheck1157, reducedZero1157 B hB hF, mul_zero]

theorem reducedZero1158 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1158 (mixedVector B) = 0 := by
  have h4153 : mixedVector B (Sum.inr 4153) = Sparse.eval nodeValue4153 (mixedVector B) := by
    change mixedMoment B node4153 node4153Labels = _
    exact sound4153 B hB hF
  have h4159 : mixedVector B (Sum.inr 4159) = Sparse.eval nodeValue4159 (mixedVector B) := by
    change mixedMoment B node4159 node4159Labels = _
    exact sound4159 B hB hF
  have h4161 : mixedVector B (Sum.inr 4161) = Sparse.eval nodeValue4161 (mixedVector B) := by
    change mixedMoment B node4161 node4161Labels = _
    exact sound4161 B hB hF
  have h4183 : mixedVector B (Sum.inr 4183) = Sparse.eval nodeValue4183 (mixedVector B) := by
    change mixedMoment B node4183 node4183Labels = _
    exact sound4183 B hB hF
  have h4327 : mixedVector B (Sum.inr 4327) = Sparse.eval nodeValue4327 (mixedVector B) := by
    change mixedMoment B node4327 node4327Labels = _
    exact sound4327 B hB hF
  have h4333 : mixedVector B (Sum.inr 4333) = Sparse.eval nodeValue4333 (mixedVector B) := by
    change mixedMoment B node4333 node4333Labels = _
    exact sound4333 B hB hF
  have h4335 : mixedVector B (Sum.inr 4335) = Sparse.eval nodeValue4335 (mixedVector B) := by
    change mixedMoment B node4335 node4335Labels = _
    exact sound4335 B hB hF
  have h4352 : mixedVector B (Sum.inr 4352) = Sparse.eval nodeValue4352 (mixedVector B) := by
    change mixedMoment B node4352 node4352Labels = _
    exact sound4352 B hB hF
  have h4358 : mixedVector B (Sum.inr 4358) = Sparse.eval nodeValue4358 (mixedVector B) := by
    change mixedMoment B node4358 node4358Labels = _
    exact sound4358 B hB hF
  have h4367 : mixedVector B (Sum.inr 4367) = Sparse.eval nodeValue4367 (mixedVector B) := by
    change mixedMoment B node4367 node4367Labels = _
    exact sound4367 B hB hF
  have h4374 : mixedVector B (Sum.inr 4374) = Sparse.eval nodeValue4374 (mixedVector B) := by
    change mixedMoment B node4374 node4374Labels = _
    exact sound4374 B hB hF
  have h4440 : mixedVector B (Sum.inr 4440) = Sparse.eval nodeValue4440 (mixedVector B) := by
    change mixedMoment B node4440 node4440Labels = _
    exact sound4440 B hB hF
  have h4445 : mixedVector B (Sum.inr 4445) = Sparse.eval nodeValue4445 (mixedVector B) := by
    change mixedMoment B node4445 node4445Labels = _
    exact sound4445 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4502 : mixedVector B (Sum.inr 4502) = Sparse.eval nodeValue4502 (mixedVector B) := by
    change mixedMoment B node4502 node4502Labels = _
    exact sound4502 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  simpa only [sourceForm1335, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4153, h4159, h4161, h4183, h4327, h4333, h4335, h4352, h4358, h4367, h4374, h4440, h4445, h4458, h4463, h4467, h4502, h4807, h4871, h4890, h4895, reducedSource1158] using sourceEq1335 B hB

theorem rowSound1158 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1158 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1158, numericCheck1158, reducedZero1158 B hB hF, mul_zero]

theorem reducedZero1160 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1160 (mixedVector B) = 0 := by
  have h1514 : mixedVector B (Sum.inr 1514) = Sparse.eval nodeValue1514 (mixedVector B) := by
    change mixedMoment B node1514 node1514Labels = _
    exact sound1514 B hB hF
  have h1532 : mixedVector B (Sum.inr 1532) = Sparse.eval nodeValue1532 (mixedVector B) := by
    change mixedMoment B node1532 node1532Labels = _
    exact sound1532 B hB hF
  have h1533 : mixedVector B (Sum.inr 1533) = Sparse.eval nodeValue1533 (mixedVector B) := by
    change mixedMoment B node1533 node1533Labels = _
    exact sound1533 B hB hF
  have h1535 : mixedVector B (Sum.inr 1535) = Sparse.eval nodeValue1535 (mixedVector B) := by
    change mixedMoment B node1535 node1535Labels = _
    exact sound1535 B hB hF
  have h1670 : mixedVector B (Sum.inr 1670) = Sparse.eval nodeValue1670 (mixedVector B) := by
    change mixedMoment B node1670 node1670Labels = _
    exact sound1670 B hB hF
  have h1688 : mixedVector B (Sum.inr 1688) = Sparse.eval nodeValue1688 (mixedVector B) := by
    change mixedMoment B node1688 node1688Labels = _
    exact sound1688 B hB hF
  have h1689 : mixedVector B (Sum.inr 1689) = Sparse.eval nodeValue1689 (mixedVector B) := by
    change mixedMoment B node1689 node1689Labels = _
    exact sound1689 B hB hF
  have h1690 : mixedVector B (Sum.inr 1690) = Sparse.eval nodeValue1690 (mixedVector B) := by
    change mixedMoment B node1690 node1690Labels = _
    exact sound1690 B hB hF
  have h1695 : mixedVector B (Sum.inr 1695) = Sparse.eval nodeValue1695 (mixedVector B) := by
    change mixedMoment B node1695 node1695Labels = _
    exact sound1695 B hB hF
  have h1720 : mixedVector B (Sum.inr 1720) = Sparse.eval nodeValue1720 (mixedVector B) := by
    change mixedMoment B node1720 node1720Labels = _
    exact sound1720 B hB hF
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h1748 : mixedVector B (Sum.inr 1748) = Sparse.eval nodeValue1748 (mixedVector B) := by
    change mixedMoment B node1748 node1748Labels = _
    exact sound1748 B hB hF
  have h1749 : mixedVector B (Sum.inr 1749) = Sparse.eval nodeValue1749 (mixedVector B) := by
    change mixedMoment B node1749 node1749Labels = _
    exact sound1749 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h1753 : mixedVector B (Sum.inr 1753) = Sparse.eval nodeValue1753 (mixedVector B) := by
    change mixedMoment B node1753 node1753Labels = _
    exact sound1753 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  simpa only [sourceForm1337, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1514, h1532, h1533, h1535, h1670, h1688, h1689, h1690, h1695, h1720, h1723, h1724, h1748, h1749, h1750, h1751, h1753, h2224, h2287, h2290, h2291, reducedSource1160] using sourceEq1337 B hB

theorem rowSound1160 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1160 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1160, numericCheck1160, reducedZero1160 B hB hF, mul_zero]

theorem reducedZero1161 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1161 (mixedVector B) = 0 := by
  have h581 : mixedVector B (Sum.inr 581) = Sparse.eval nodeValue581 (mixedVector B) := by
    change mixedMoment B node581 node581Labels = _
    exact sound581 B hB hF
  have h587 : mixedVector B (Sum.inr 587) = Sparse.eval nodeValue587 (mixedVector B) := by
    change mixedMoment B node587 node587Labels = _
    exact sound587 B hB hF
  have h589 : mixedVector B (Sum.inr 589) = Sparse.eval nodeValue589 (mixedVector B) := by
    change mixedMoment B node589 node589Labels = _
    exact sound589 B hB hF
  have h611 : mixedVector B (Sum.inr 611) = Sparse.eval nodeValue611 (mixedVector B) := by
    change mixedMoment B node611 node611Labels = _
    exact sound611 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1338, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h581, h587, h589, h611, h1046, h4083, reducedSource1161] using sourceEq1338 B hB

theorem rowSound1161 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1161 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1161, numericCheck1161, reducedZero1161 B hB hF, mul_zero]

theorem reducedZero1162 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1162 (mixedVector B) = 0 := by
  have h611 : mixedVector B (Sum.inr 611) = Sparse.eval nodeValue611 (mixedVector B) := by
    change mixedMoment B node611 node611Labels = _
    exact sound611 B hB hF
  have h930 : mixedVector B (Sum.inr 930) = Sparse.eval nodeValue930 (mixedVector B) := by
    change mixedMoment B node930 node930Labels = _
    exact sound930 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h1086 : mixedVector B (Sum.inr 1086) = Sparse.eval nodeValue1086 (mixedVector B) := by
    change mixedMoment B node1086 node1086Labels = _
    exact sound1086 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1339, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h611, h930, h1046, h1086, h4083, reducedSource1162] using sourceEq1339 B hB

theorem rowSound1162 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1162 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1162, numericCheck1162, reducedZero1162 B hB hF, mul_zero]

theorem reducedZero1163 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1163 (mixedVector B) = 0 := by
  have h945 : mixedVector B (Sum.inr 945) = Sparse.eval nodeValue945 (mixedVector B) := by
    change mixedMoment B node945 node945Labels = _
    exact sound945 B hB hF
  have h951 : mixedVector B (Sum.inr 951) = Sparse.eval nodeValue951 (mixedVector B) := by
    change mixedMoment B node951 node951Labels = _
    exact sound951 B hB hF
  have h953 : mixedVector B (Sum.inr 953) = Sparse.eval nodeValue953 (mixedVector B) := by
    change mixedMoment B node953 node953Labels = _
    exact sound953 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1340, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h945, h951, h953, h1046, h2112, h4083, reducedSource1163] using sourceEq1340 B hB

theorem rowSound1163 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1163 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1163, numericCheck1163, reducedZero1163 B hB hF, mul_zero]

theorem reducedZero1164 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1164 (mixedVector B) = 0 := by
  have h905 : mixedVector B (Sum.inr 905) = Sparse.eval nodeValue905 (mixedVector B) := by
    change mixedMoment B node905 node905Labels = _
    exact sound905 B hB hF
  have h911 : mixedVector B (Sum.inr 911) = Sparse.eval nodeValue911 (mixedVector B) := by
    change mixedMoment B node911 node911Labels = _
    exact sound911 B hB hF
  have h913 : mixedVector B (Sum.inr 913) = Sparse.eval nodeValue913 (mixedVector B) := by
    change mixedMoment B node913 node913Labels = _
    exact sound913 B hB hF
  have h930 : mixedVector B (Sum.inr 930) = Sparse.eval nodeValue930 (mixedVector B) := by
    change mixedMoment B node930 node930Labels = _
    exact sound930 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1341, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h905, h911, h913, h930, h1046, h2025, h4083, reducedSource1164] using sourceEq1341 B hB

theorem rowSound1164 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1164 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1164, numericCheck1164, reducedZero1164 B hB hF, mul_zero]

theorem sourceRowsAt1152 : MixedData.sourceRows (1152 : Fin 2425) =
    MixedData.row1152 := by decide +kernel

theorem sourceRowsAt1153 : MixedData.sourceRows (1153 : Fin 2425) =
    MixedData.row1153 := by decide +kernel

theorem sourceRowsAt1154 : MixedData.sourceRows (1154 : Fin 2425) =
    MixedData.row1154 := by decide +kernel

theorem sourceRowsAt1155 : MixedData.sourceRows (1155 : Fin 2425) =
    MixedData.row1155 := by decide +kernel

theorem sourceRowsAt1156 : MixedData.sourceRows (1156 : Fin 2425) =
    MixedData.row1156 := by decide +kernel

theorem sourceRowsAt1157 : MixedData.sourceRows (1157 : Fin 2425) =
    MixedData.row1157 := by decide +kernel

theorem sourceRowsAt1158 : MixedData.sourceRows (1158 : Fin 2425) =
    MixedData.row1158 := by decide +kernel

theorem sourceRowsAt1159 : MixedData.sourceRows (1159 : Fin 2425) =
    MixedData.row1159 := by decide +kernel

theorem sourceRowsAt1160 : MixedData.sourceRows (1160 : Fin 2425) =
    MixedData.row1160 := by decide +kernel

theorem sourceRowsAt1161 : MixedData.sourceRows (1161 : Fin 2425) =
    MixedData.row1161 := by decide +kernel

theorem sourceRowsAt1162 : MixedData.sourceRows (1162 : Fin 2425) =
    MixedData.row1162 := by decide +kernel

theorem sourceRowsAt1163 : MixedData.sourceRows (1163 : Fin 2425) =
    MixedData.row1163 := by decide +kernel

theorem sourceRowsAt1164 : MixedData.sourceRows (1164 : Fin 2425) =
    MixedData.row1164 := by decide +kernel

theorem sourceRowsAt1165 : MixedData.sourceRows (1165 : Fin 2425) =
    MixedData.row1165 := by decide +kernel

theorem sourceRowsAt1166 : MixedData.sourceRows (1166 : Fin 2425) =
    MixedData.row1166 := by decide +kernel

theorem sourceRowsAt1167 : MixedData.sourceRows (1167 : Fin 2425) =
    MixedData.row1167 := by decide +kernel

theorem chunkSound72_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 72) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1152 ∨ k.val = 1153 ∨ k.val = 1154 ∨ k.val = 1155 ∨ k.val = 1156 ∨ k.val = 1157 ∨ k.val = 1158 ∨ k.val = 1159 ∨ k.val = 1160 ∨ k.val = 1161 ∨ k.val = 1162 ∨ k.val = 1163 ∨ k.val = 1164 ∨ k.val = 1165 ∨ k.val = 1166 ∨ k.val = 1167 := by omega
  rcases heq with h1152 | h1153 | h1154 | h1155 | h1156 | h1157 | h1158 | h1159 | h1160 | h1161 | h1162 | h1163 | h1164 | h1165 | h1166 | h1167
  · have he : k = (1152 : Fin 2425) := Fin.ext h1152
    subst k
    rw [sourceRowsAt1152]
    exact rowSound1152 B hB hF
  · have he : k = (1153 : Fin 2425) := Fin.ext h1153
    subst k
    rw [sourceRowsAt1153]
    exact rowSound1153 B hB hF
  · have he : k = (1154 : Fin 2425) := Fin.ext h1154
    subst k
    rw [sourceRowsAt1154]
    exact rowSound1154 B hB hF
  · have he : k = (1155 : Fin 2425) := Fin.ext h1155
    subst k
    rw [sourceRowsAt1155]
    exact rowSound1155 B hB hF
  · have he : k = (1156 : Fin 2425) := Fin.ext h1156
    subst k
    rw [sourceRowsAt1156]
    exact rowSound1156 B hB hF
  · have he : k = (1157 : Fin 2425) := Fin.ext h1157
    subst k
    rw [sourceRowsAt1157]
    exact rowSound1157 B hB hF
  · have he : k = (1158 : Fin 2425) := Fin.ext h1158
    subst k
    rw [sourceRowsAt1158]
    exact rowSound1158 B hB hF
  · have he : k = (1159 : Fin 2425) := Fin.ext h1159
    subst k
    rw [sourceRowsAt1159]
    exact rowSound1159_e B hB hF
  · have he : k = (1160 : Fin 2425) := Fin.ext h1160
    subst k
    rw [sourceRowsAt1160]
    exact rowSound1160 B hB hF
  · have he : k = (1161 : Fin 2425) := Fin.ext h1161
    subst k
    rw [sourceRowsAt1161]
    exact rowSound1161 B hB hF
  · have he : k = (1162 : Fin 2425) := Fin.ext h1162
    subst k
    rw [sourceRowsAt1162]
    exact rowSound1162 B hB hF
  · have he : k = (1163 : Fin 2425) := Fin.ext h1163
    subst k
    rw [sourceRowsAt1163]
    exact rowSound1163 B hB hF
  · have he : k = (1164 : Fin 2425) := Fin.ext h1164
    subst k
    rw [sourceRowsAt1164]
    exact rowSound1164 B hB hF
  · have he : k = (1165 : Fin 2425) := Fin.ext h1165
    subst k
    rw [sourceRowsAt1165]
    exact rowSound1165_e B hB hF
  · have he : k = (1166 : Fin 2425) := Fin.ext h1166
    subst k
    rw [sourceRowsAt1166]
    exact rowSound1166_e B hB hF
  · have he : k = (1167 : Fin 2425) := Fin.ext h1167
    subst k
    rw [sourceRowsAt1167]
    exact rowSound1167_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound72_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound72_e_oai
