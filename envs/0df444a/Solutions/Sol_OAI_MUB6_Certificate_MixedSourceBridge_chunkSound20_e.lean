-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:25:15.459202+00:00
-- url     : https://prove2.me/submissions/30ce17d8-f2a4-4149-bf95-48017fb79d83

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E117
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound326_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound327_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound335_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw534 raw534Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw534 raw534Labels = mixedMoment B raw534step0 raw534step0Labels := by
      have ha : raw534step0 = (fun i j => raw534 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw534step0 raw534; decide +kernel
      have hl : raw534step0Labels = raw534Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw534 raw534Labels permutation32 permutation5
    mixedMoment B raw534step0 raw534step0Labels = mixedMoment B raw534step1 raw534step1Labels := by
      have ha : raw534step1 = raw534step0 := by apply Matrix.ext; unfold raw534step1 raw534step0; decide +kernel
      have hl : raw534step0Labels = labelEmbedding1 ∘ raw534step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw534step0 raw534step0Labels raw534step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3858 node3858Labels := by rfl

theorem canonical535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw535 raw535Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw535 raw535Labels = mixedMoment B raw535step0 raw535step0Labels := by
      have ha : raw535step0 = (fun i j => raw535 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw535step0 raw535; decide +kernel
      have hl : raw535step0Labels = raw535Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw535 raw535Labels permutation32 permutation5
    _ = mixedMoment B node494 node494Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7381 raw7381Labels = mixedMoment B node2710 node2710Labels := by
  calc
    _ = mixedMoment B node2710 node2710Labels := by rfl

theorem canonical7382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7382 raw7382Labels = mixedMoment B node3801 node3801Labels := by
  calc
    _ = mixedMoment B node3801 node3801Labels := by rfl

theorem canonical7383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7383 raw7383Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw7383 raw7383Labels = mixedMoment B raw7383step0 raw7383step0Labels := by
      have ha : raw7383step0 = (fun i j => raw7383 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7383step0 raw7383; decide +kernel
      have hl : raw7383step0Labels = raw7383Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7383 raw7383Labels permutation176 permutation2
    _ = mixedMoment B node3872 node3872Labels := by rfl

theorem canonical7384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7384 raw7384Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw7384 raw7384Labels = mixedMoment B raw7384step0 raw7384step0Labels := by
      have ha : raw7384step0 = (fun i j => raw7384 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7384step0 raw7384; decide +kernel
      have hl : raw7384step0Labels = raw7384Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7384 raw7384Labels permutation200 permutation2
    _ = mixedMoment B node3872 node3872Labels := by rfl

theorem canonical7385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7385 raw7385Labels = mixedMoment B node3899 node3899Labels := by
  calc
    _ = mixedMoment B node3899 node3899Labels := by rfl

theorem canonical7386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7386 raw7386Labels = mixedMoment B node3901 node3901Labels := by
  calc
    mixedMoment B raw7386 raw7386Labels = mixedMoment B raw7386step0 raw7386step0Labels := by
      have ha : raw7386step0 = (fun i j => raw7386 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7386step0 raw7386; decide +kernel
      have hl : raw7386step0Labels = raw7386Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7386 raw7386Labels permutation153 permutation2
    _ = mixedMoment B node3901 node3901Labels := by rfl

theorem canonical7387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7387 raw7387Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw7387 raw7387Labels = mixedMoment B raw7387step0 raw7387step0Labels := by
      have hz : ∀ j, raw7387 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw7387step0 = (fun i j => raw7387 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw7387step0 raw7387; decide +kernel
      have hl : raw7387step0Labels = raw7387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7387 raw7387Labels permutation590 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical7388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7388 raw7388Labels = mixedMoment B node1248 node1248Labels := by
  calc
    mixedMoment B raw7388 raw7388Labels = mixedMoment B raw7388step0 raw7388step0Labels := by
      have ha : raw7388step0 = (fun i j => raw7388 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7388step0 raw7388; decide +kernel
      have hl : raw7388step0Labels = raw7388Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7388 raw7388Labels permutation182 permutation2
    _ = mixedMoment B node1248 node1248Labels := by rfl

theorem canonical7389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7389 raw7389Labels = mixedMoment B node1216 node1216Labels := by
  calc
    mixedMoment B raw7389 raw7389Labels = mixedMoment B raw7389step0 raw7389step0Labels := by
      have ha : raw7389step0 = (fun i j => raw7389 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7389step0 raw7389; decide +kernel
      have hl : raw7389step0Labels = raw7389Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7389 raw7389Labels permutation158 permutation2
    _ = mixedMoment B node1216 node1216Labels := by rfl

theorem canonical7393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7393 raw7393Labels = mixedMoment B node2623 node2623Labels := by
  calc
    mixedMoment B raw7393 raw7393Labels = mixedMoment B raw7393step0 raw7393step0Labels := by
      have ha : raw7393step0 = (fun i j => raw7393 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7393step0 raw7393; decide +kernel
      have hl : raw7393step0Labels = raw7393Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7393 raw7393Labels permutation182 permutation2
    _ = mixedMoment B node2623 node2623Labels := by rfl

theorem canonical7394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7394 raw7394Labels = mixedMoment B node2623 node2623Labels := by
  calc
    mixedMoment B raw7394 raw7394Labels = mixedMoment B raw7394step0 raw7394step0Labels := by
      have ha : raw7394step0 = (fun i j => raw7394 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7394step0 raw7394; decide +kernel
      have hl : raw7394step0Labels = raw7394Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7394 raw7394Labels permutation206 permutation2
    _ = mixedMoment B node2623 node2623Labels := by rfl

theorem canonical7395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7395 raw7395Labels = mixedMoment B node2745 node2745Labels := by
  calc
    mixedMoment B raw7395 raw7395Labels = mixedMoment B raw7395step0 raw7395step0Labels := by
      have ha : raw7395step0 = (fun i j => raw7395 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7395step0 raw7395; decide +kernel
      have hl : raw7395step0Labels = raw7395Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7395 raw7395Labels permutation184 permutation2
    _ = mixedMoment B node2745 node2745Labels := by rfl

theorem canonical7396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7396 raw7396Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw7396 raw7396Labels = mixedMoment B raw7396step0 raw7396step0Labels := by
      have ha : raw7396step0 = (fun i j => raw7396 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7396step0 raw7396; decide +kernel
      have hl : raw7396step0Labels = raw7396Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7396 raw7396Labels permutation183 permutation2
    _ = mixedMoment B node2750 node2750Labels := by rfl

theorem canonical7397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7397 raw7397Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw7397 raw7397Labels = mixedMoment B raw7397step0 raw7397step0Labels := by
      have ha : raw7397step0 = (fun i j => raw7397 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7397step0 raw7397; decide +kernel
      have hl : raw7397step0Labels = raw7397Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7397 raw7397Labels permutation158 permutation2
    _ = mixedMoment B node2483 node2483Labels := by rfl

theorem canonical7398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7398 raw7398Labels = mixedMoment B node2483 node2483Labels := by
  calc
    _ = mixedMoment B node2483 node2483Labels := by rfl

theorem canonical7399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7399 raw7399Labels = mixedMoment B node2473 node2473Labels := by
  calc
    mixedMoment B raw7399 raw7399Labels = mixedMoment B raw7399step0 raw7399step0Labels := by
      have ha : raw7399step0 = (fun i j => raw7399 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7399step0 raw7399; decide +kernel
      have hl : raw7399step0Labels = raw7399Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7399 raw7399Labels permutation153 permutation2
    _ = mixedMoment B node2473 node2473Labels := by rfl

theorem canonical7400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7400 raw7400Labels = mixedMoment B node2471 node2471Labels := by
  calc
    _ = mixedMoment B node2471 node2471Labels := by rfl

theorem canonical7401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7401 raw7401Labels = mixedMoment B node2617 node2617Labels := by
  calc
    mixedMoment B raw7401 raw7401Labels = mixedMoment B raw7401step0 raw7401step0Labels := by
      have ha : raw7401step0 = (fun i j => raw7401 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7401step0 raw7401; decide +kernel
      have hl : raw7401step0Labels = raw7401Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7401 raw7401Labels permutation200 permutation2
    _ = mixedMoment B node2617 node2617Labels := by rfl

theorem canonical7402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7402 raw7402Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw7402 raw7402Labels = mixedMoment B raw7402step0 raw7402step0Labels := by
      have ha : raw7402step0 = (fun i j => raw7402 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7402step0 raw7402; decide +kernel
      have hl : raw7402step0Labels = raw7402Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7402 raw7402Labels permutation160 permutation2
    _ = mixedMoment B node2710 node2710Labels := by rfl

theorem canonical7403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7403 raw7403Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw7403 raw7403Labels = mixedMoment B raw7403step0 raw7403step0Labels := by
      have ha : raw7403step0 = (fun i j => raw7403 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7403step0 raw7403; decide +kernel
      have hl : raw7403step0Labels = raw7403Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7403 raw7403Labels permutation162 permutation2
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical7404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7404 raw7404Labels = mixedMoment B node2617 node2617Labels := by
  calc
    mixedMoment B raw7404 raw7404Labels = mixedMoment B raw7404step0 raw7404step0Labels := by
      have ha : raw7404step0 = (fun i j => raw7404 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7404step0 raw7404; decide +kernel
      have hl : raw7404step0Labels = raw7404Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7404 raw7404Labels permutation176 permutation2
    _ = mixedMoment B node2617 node2617Labels := by rfl

theorem canonical7405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7405 raw7405Labels = mixedMoment B node2612 node2612Labels := by
  calc
    mixedMoment B raw7405 raw7405Labels = mixedMoment B raw7405step0 raw7405step0Labels := by
      have ha : raw7405step0 = (fun i j => raw7405 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7405step0 raw7405; decide +kernel
      have hl : raw7405step0Labels = raw7405Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7405 raw7405Labels permutation177 permutation2
    _ = mixedMoment B node2612 node2612Labels := by rfl

theorem canonical7406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7406 raw7406Labels = mixedMoment B node2611 node2611Labels := by
  calc
    mixedMoment B raw7406 raw7406Labels = mixedMoment B raw7406step0 raw7406step0Labels := by
      have ha : raw7406step0 = (fun i j => raw7406 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7406step0 raw7406; decide +kernel
      have hl : raw7406step0Labels = raw7406Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7406 raw7406Labels permutation176 permutation2
    _ = mixedMoment B node2611 node2611Labels := by rfl

theorem canonical7407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7407 raw7407Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw7407 raw7407Labels = mixedMoment B raw7407step0 raw7407step0Labels := by
      have ha : raw7407step0 = (fun i j => raw7407 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7407step0 raw7407; decide +kernel
      have hl : raw7407step0Labels = raw7407Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7407 raw7407Labels permutation154 permutation2
    _ = mixedMoment B node2710 node2710Labels := by rfl

theorem canonical7408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7408 raw7408Labels = mixedMoment B node2707 node2707Labels := by
  calc
    _ = mixedMoment B node2707 node2707Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7469 raw7469Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw7469 raw7469Labels = mixedMoment B raw7469step0 raw7469step0Labels := by
      have ha : raw7469step0 = (fun i j => raw7469 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7469step0 raw7469; decide +kernel
      have hl : raw7469step0Labels = raw7469Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7469 raw7469Labels permutation620 permutation7
    mixedMoment B raw7469step0 raw7469step0Labels = mixedMoment B raw7469step1 raw7469step1Labels := by
      have ha : raw7469step1 = raw7469step0 := by apply Matrix.ext; unfold raw7469step1 raw7469step0; decide +kernel
      have hl : raw7469step0Labels = labelEmbedding1 ∘ raw7469step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7469step0 raw7469step0Labels raw7469step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

theorem canonical7470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7470 raw7470Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw7470 raw7470Labels = mixedMoment B raw7470step0 raw7470step0Labels := by
      have ha : raw7470step0 = (fun i j => raw7470 (permutation622 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7470step0 raw7470; decide +kernel
      have hl : raw7470step0Labels = raw7470Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7470 raw7470Labels permutation622 permutation7
    mixedMoment B raw7470step0 raw7470step0Labels = mixedMoment B raw7470step1 raw7470step1Labels := by
      have ha : raw7470step1 = raw7470step0 := by apply Matrix.ext; unfold raw7470step1 raw7470step0; decide +kernel
      have hl : raw7470step0Labels = labelEmbedding1 ∘ raw7470step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7470step0 raw7470step0Labels raw7470step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical7471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7471 raw7471Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw7471 raw7471Labels = mixedMoment B raw7471step0 raw7471step0Labels := by
      have ha : raw7471step0 = (fun i j => raw7471 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7471step0 raw7471; decide +kernel
      have hl : raw7471step0Labels = raw7471Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7471 raw7471Labels permutation620 permutation7
    mixedMoment B raw7471step0 raw7471step0Labels = mixedMoment B raw7471step1 raw7471step1Labels := by
      have ha : raw7471step1 = raw7471step0 := by apply Matrix.ext; unfold raw7471step1 raw7471step0; decide +kernel
      have hl : raw7471step0Labels = labelEmbedding1 ∘ raw7471step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7471step0 raw7471step0Labels raw7471step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical7472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7472 raw7472Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw7472 raw7472Labels = mixedMoment B raw7472step0 raw7472step0Labels := by
      have hz : ∀ j, raw7472 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7472step0 = (fun i j => raw7472 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7472step0 raw7472; decide +kernel
      have hl : raw7472step0Labels = raw7472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7472 raw7472Labels permutation520 hz
    mixedMoment B raw7472step0 raw7472step0Labels = mixedMoment B raw7472step1 raw7472step1Labels := by
      have ha : raw7472step1 = (fun i j => raw7472step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7472step1 raw7472step0; decide +kernel
      have hl : raw7472step1Labels = raw7472step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7472step0 raw7472step0Labels permutation137 permutation7
    mixedMoment B raw7472step1 raw7472step1Labels = mixedMoment B raw7472step2 raw7472step2Labels := by
      have ha : raw7472step2 = raw7472step1 := by apply Matrix.ext; unfold raw7472step2 raw7472step1; decide +kernel
      have hl : raw7472step1Labels = labelEmbedding1 ∘ raw7472step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7472step1 raw7472step1Labels raw7472step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3858 node3858Labels := by rfl

theorem canonical7473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7473 raw7473Labels = mixedMoment B node3991 node3991Labels := by
  calc
    mixedMoment B raw7473 raw7473Labels = mixedMoment B raw7473step0 raw7473step0Labels := by
      have ha : raw7473step0 = (fun i j => raw7473 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7473step0 raw7473; decide +kernel
      have hl : raw7473step0Labels = raw7473Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7473 raw7473Labels permutation620 permutation7
    mixedMoment B raw7473step0 raw7473step0Labels = mixedMoment B raw7473step1 raw7473step1Labels := by
      have ha : raw7473step1 = raw7473step0 := by apply Matrix.ext; unfold raw7473step1 raw7473step0; decide +kernel
      have hl : raw7473step0Labels = labelEmbedding1 ∘ raw7473step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7473step0 raw7473step0Labels raw7473step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3991 node3991Labels := by rfl

theorem canonical7474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7474 raw7474Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw7474 raw7474Labels = mixedMoment B raw7474step0 raw7474step0Labels := by
      have ha : raw7474step0 = (fun i j => raw7474 (permutation170 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7474step0 raw7474; decide +kernel
      have hl : raw7474step0Labels = raw7474Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7474 raw7474Labels permutation170 permutation5
    mixedMoment B raw7474step0 raw7474step0Labels = mixedMoment B raw7474step1 raw7474step1Labels := by
      have ha : raw7474step1 = -raw7474step0 := by apply Matrix.ext; change ∀ i j, raw7474step1 i j = -(raw7474step0 i j); unfold raw7474step1 raw7474step0; decide +kernel
      have hl : raw7474step1Labels = raw7474step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7474step1 raw7474step1Labels = mixedMoment B raw7474step2 raw7474step2Labels := by
      have ha : raw7474step2 = raw7474step1 := by apply Matrix.ext; unfold raw7474step2 raw7474step1; decide +kernel
      have hl : raw7474step1Labels = labelEmbedding1 ∘ raw7474step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7474step1 raw7474step1Labels raw7474step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

theorem canonical7475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7475 raw7475Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw7475 raw7475Labels = mixedMoment B raw7475step0 raw7475step0Labels := by
      have ha : raw7475step0 = (fun i j => raw7475 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7475step0 raw7475; decide +kernel
      have hl : raw7475step0Labels = raw7475Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7475 raw7475Labels permutation180 permutation5
    mixedMoment B raw7475step0 raw7475step0Labels = mixedMoment B raw7475step1 raw7475step1Labels := by
      have ha : raw7475step1 = -raw7475step0 := by apply Matrix.ext; change ∀ i j, raw7475step1 i j = -(raw7475step0 i j); unfold raw7475step1 raw7475step0; decide +kernel
      have hl : raw7475step1Labels = raw7475step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7475step1 raw7475step1Labels = mixedMoment B raw7475step2 raw7475step2Labels := by
      have ha : raw7475step2 = raw7475step1 := by apply Matrix.ext; unfold raw7475step2 raw7475step1; decide +kernel
      have hl : raw7475step1Labels = labelEmbedding1 ∘ raw7475step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7475step1 raw7475step1Labels raw7475step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

theorem canonical7476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7476 raw7476Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw7476 raw7476Labels = mixedMoment B raw7476step0 raw7476step0Labels := by
      have ha : raw7476step0 = (fun i j => raw7476 (permutation204 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7476step0 raw7476; decide +kernel
      have hl : raw7476step0Labels = raw7476Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7476 raw7476Labels permutation204 permutation5
    mixedMoment B raw7476step0 raw7476step0Labels = mixedMoment B raw7476step1 raw7476step1Labels := by
      have ha : raw7476step1 = -raw7476step0 := by apply Matrix.ext; change ∀ i j, raw7476step1 i j = -(raw7476step0 i j); unfold raw7476step1 raw7476step0; decide +kernel
      have hl : raw7476step1Labels = raw7476step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7476step1 raw7476step1Labels = mixedMoment B raw7476step2 raw7476step2Labels := by
      have ha : raw7476step2 = raw7476step1 := by apply Matrix.ext; unfold raw7476step2 raw7476step1; decide +kernel
      have hl : raw7476step1Labels = labelEmbedding1 ∘ raw7476step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7476step1 raw7476step1Labels raw7476step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

theorem canonical7477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7477 raw7477Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw7477 raw7477Labels = mixedMoment B raw7477step0 raw7477step0Labels := by
      have hz : ∀ j, raw7477 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7477step0 = (fun i j => raw7477 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7477step0 raw7477; decide +kernel
      have hl : raw7477step0Labels = raw7477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7477 raw7477Labels permutation520 hz
    mixedMoment B raw7477step0 raw7477step0Labels = mixedMoment B raw7477step1 raw7477step1Labels := by
      have ha : raw7477step1 = (fun i j => raw7477step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7477step1 raw7477step0; decide +kernel
      have hl : raw7477step1Labels = raw7477step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7477step0 raw7477step0Labels permutation36 permutation5
    mixedMoment B raw7477step1 raw7477step1Labels = mixedMoment B raw7477step2 raw7477step2Labels := by
      have ha : raw7477step2 = -raw7477step1 := by apply Matrix.ext; change ∀ i j, raw7477step2 i j = -(raw7477step1 i j); unfold raw7477step2 raw7477step1; decide +kernel
      have hl : raw7477step2Labels = raw7477step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7477step2 raw7477step2Labels = mixedMoment B raw7477step3 raw7477step3Labels := by
      have ha : raw7477step3 = raw7477step2 := by apply Matrix.ext; unfold raw7477step3 raw7477step2; decide +kernel
      have hl : raw7477step2Labels = labelEmbedding1 ∘ raw7477step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7477step2 raw7477step2Labels raw7477step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

theorem canonical7478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7478 raw7478Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw7478 raw7478Labels = mixedMoment B raw7478step0 raw7478step0Labels := by
      have ha : raw7478step0 = (fun i j => raw7478 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7478step0 raw7478; decide +kernel
      have hl : raw7478step0Labels = raw7478Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7478 raw7478Labels permutation246 permutation5
    mixedMoment B raw7478step0 raw7478step0Labels = mixedMoment B raw7478step1 raw7478step1Labels := by
      have ha : raw7478step1 = -raw7478step0 := by apply Matrix.ext; change ∀ i j, raw7478step1 i j = -(raw7478step0 i j); unfold raw7478step1 raw7478step0; decide +kernel
      have hl : raw7478step1Labels = raw7478step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7478step1 raw7478step1Labels = mixedMoment B raw7478step2 raw7478step2Labels := by
      have ha : raw7478step2 = raw7478step1 := by apply Matrix.ext; unfold raw7478step2 raw7478step1; decide +kernel
      have hl : raw7478step1Labels = labelEmbedding1 ∘ raw7478step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7478step1 raw7478step1Labels raw7478step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

theorem canonical7479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7479 raw7479Labels = mixedMoment B node1607 node1607Labels := by
  calc
    mixedMoment B raw7479 raw7479Labels = mixedMoment B raw7479step0 raw7479step0Labels := by
      have ha : raw7479step0 = (fun i j => raw7479 (permutation173 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7479step0 raw7479; decide +kernel
      have hl : raw7479step0Labels = raw7479Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7479 raw7479Labels permutation173 permutation5
    mixedMoment B raw7479step0 raw7479step0Labels = mixedMoment B raw7479step1 raw7479step1Labels := by
      have ha : raw7479step1 = -raw7479step0 := by apply Matrix.ext; change ∀ i j, raw7479step1 i j = -(raw7479step0 i j); unfold raw7479step1 raw7479step0; decide +kernel
      have hl : raw7479step1Labels = raw7479step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7479step1 raw7479step1Labels = mixedMoment B raw7479step2 raw7479step2Labels := by
      have ha : raw7479step2 = raw7479step1 := by apply Matrix.ext; unfold raw7479step2 raw7479step1; decide +kernel
      have hl : raw7479step1Labels = labelEmbedding1 ∘ raw7479step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7479step1 raw7479step1Labels raw7479step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1607 node1607Labels := by rfl

theorem canonical7480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7480 raw7480Labels = mixedMoment B node3346 node3346Labels := by
  calc
    mixedMoment B raw7480 raw7480Labels = mixedMoment B raw7480step0 raw7480step0Labels := by
      have ha : raw7480step0 = (fun i j => raw7480 (permutation173 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7480step0 raw7480; decide +kernel
      have hl : raw7480step0Labels = raw7480Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7480 raw7480Labels permutation173 permutation5
    mixedMoment B raw7480step0 raw7480step0Labels = mixedMoment B raw7480step1 raw7480step1Labels := by
      have ha : raw7480step1 = -raw7480step0 := by apply Matrix.ext; change ∀ i j, raw7480step1 i j = -(raw7480step0 i j); unfold raw7480step1 raw7480step0; decide +kernel
      have hl : raw7480step1Labels = raw7480step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7480step1 raw7480step1Labels = mixedMoment B raw7480step2 raw7480step2Labels := by
      have ha : raw7480step2 = raw7480step1 := by apply Matrix.ext; unfold raw7480step2 raw7480step1; decide +kernel
      have hl : raw7480step1Labels = labelEmbedding1 ∘ raw7480step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7480step1 raw7480step1Labels raw7480step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3346 node3346Labels := by rfl

theorem canonical7481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7481 raw7481Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw7481 raw7481Labels = mixedMoment B raw7481step0 raw7481step0Labels := by
      have ha : raw7481step0 = (fun i j => raw7481 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7481step0 raw7481; decide +kernel
      have hl : raw7481step0Labels = raw7481Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7481 raw7481Labels permutation163 permutation5
    mixedMoment B raw7481step0 raw7481step0Labels = mixedMoment B raw7481step1 raw7481step1Labels := by
      have ha : raw7481step1 = -raw7481step0 := by apply Matrix.ext; change ∀ i j, raw7481step1 i j = -(raw7481step0 i j); unfold raw7481step1 raw7481step0; decide +kernel
      have hl : raw7481step1Labels = raw7481step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7481step1 raw7481step1Labels = mixedMoment B raw7481step2 raw7481step2Labels := by
      have ha : raw7481step2 = raw7481step1 := by apply Matrix.ext; unfold raw7481step2 raw7481step1; decide +kernel
      have hl : raw7481step1Labels = labelEmbedding1 ∘ raw7481step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7481step1 raw7481step1Labels raw7481step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

theorem canonical7482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7482 raw7482Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw7482 raw7482Labels = mixedMoment B raw7482step0 raw7482step0Labels := by
      have hz : ∀ j, raw7482 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7482step0 = (fun i j => raw7482 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7482step0 raw7482; decide +kernel
      have hl : raw7482step0Labels = raw7482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7482 raw7482Labels permutation520 hz
    mixedMoment B raw7482step0 raw7482step0Labels = mixedMoment B raw7482step1 raw7482step1Labels := by
      have ha : raw7482step1 = (fun i j => raw7482step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7482step1 raw7482step0; decide +kernel
      have hl : raw7482step1Labels = raw7482step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7482step0 raw7482step0Labels permutation37 permutation5
    mixedMoment B raw7482step1 raw7482step1Labels = mixedMoment B raw7482step2 raw7482step2Labels := by
      have ha : raw7482step2 = -raw7482step1 := by apply Matrix.ext; change ∀ i j, raw7482step2 i j = -(raw7482step1 i j); unfold raw7482step2 raw7482step1; decide +kernel
      have hl : raw7482step2Labels = raw7482step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7482step2 raw7482step2Labels = mixedMoment B raw7482step3 raw7482step3Labels := by
      have ha : raw7482step3 = raw7482step2 := by apply Matrix.ext; unfold raw7482step3 raw7482step2; decide +kernel
      have hl : raw7482step2Labels = labelEmbedding1 ∘ raw7482step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7482step2 raw7482step2Labels raw7482step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

theorem canonical7483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7483 raw7483Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw7483 raw7483Labels = mixedMoment B raw7483step0 raw7483step0Labels := by
      have ha : raw7483step0 = (fun i j => raw7483 (permutation173 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7483step0 raw7483; decide +kernel
      have hl : raw7483step0Labels = raw7483Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7483 raw7483Labels permutation173 permutation5
    mixedMoment B raw7483step0 raw7483step0Labels = mixedMoment B raw7483step1 raw7483step1Labels := by
      have ha : raw7483step1 = -raw7483step0 := by apply Matrix.ext; change ∀ i j, raw7483step1 i j = -(raw7483step0 i j); unfold raw7483step1 raw7483step0; decide +kernel
      have hl : raw7483step1Labels = raw7483step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7483step1 raw7483step1Labels = mixedMoment B raw7483step2 raw7483step2Labels := by
      have ha : raw7483step2 = raw7483step1 := by apply Matrix.ext; unfold raw7483step2 raw7483step1; decide +kernel
      have hl : raw7483step1Labels = labelEmbedding1 ∘ raw7483step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7483step1 raw7483step1Labels raw7483step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3503 node3503Labels := by rfl

theorem canonical7484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7484 raw7484Labels = mixedMoment B node1607 node1607Labels := by
  calc
    mixedMoment B raw7484 raw7484Labels = mixedMoment B raw7484step0 raw7484step0Labels := by
      have ha : raw7484step0 = (fun i j => raw7484 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7484step0 raw7484; decide +kernel
      have hl : raw7484step0Labels = raw7484Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7484 raw7484Labels permutation171 permutation5
    mixedMoment B raw7484step0 raw7484step0Labels = mixedMoment B raw7484step1 raw7484step1Labels := by
      have ha : raw7484step1 = -raw7484step0 := by apply Matrix.ext; change ∀ i j, raw7484step1 i j = -(raw7484step0 i j); unfold raw7484step1 raw7484step0; decide +kernel
      have hl : raw7484step1Labels = raw7484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7484step1 raw7484step1Labels = mixedMoment B raw7484step2 raw7484step2Labels := by
      have ha : raw7484step2 = raw7484step1 := by apply Matrix.ext; unfold raw7484step2 raw7484step1; decide +kernel
      have hl : raw7484step1Labels = labelEmbedding1 ∘ raw7484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7484step1 raw7484step1Labels raw7484step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1607 node1607Labels := by rfl

theorem canonical7485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7485 raw7485Labels = mixedMoment B node3346 node3346Labels := by
  calc
    mixedMoment B raw7485 raw7485Labels = mixedMoment B raw7485step0 raw7485step0Labels := by
      have ha : raw7485step0 = (fun i j => raw7485 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7485step0 raw7485; decide +kernel
      have hl : raw7485step0Labels = raw7485Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7485 raw7485Labels permutation171 permutation5
    mixedMoment B raw7485step0 raw7485step0Labels = mixedMoment B raw7485step1 raw7485step1Labels := by
      have ha : raw7485step1 = -raw7485step0 := by apply Matrix.ext; change ∀ i j, raw7485step1 i j = -(raw7485step0 i j); unfold raw7485step1 raw7485step0; decide +kernel
      have hl : raw7485step1Labels = raw7485step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7485step1 raw7485step1Labels = mixedMoment B raw7485step2 raw7485step2Labels := by
      have ha : raw7485step2 = raw7485step1 := by apply Matrix.ext; unfold raw7485step2 raw7485step1; decide +kernel
      have hl : raw7485step1Labels = labelEmbedding1 ∘ raw7485step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7485step1 raw7485step1Labels raw7485step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3346 node3346Labels := by rfl

theorem canonical7486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7486 raw7486Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw7486 raw7486Labels = mixedMoment B raw7486step0 raw7486step0Labels := by
      have ha : raw7486step0 = (fun i j => raw7486 (permutation157 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7486step0 raw7486; decide +kernel
      have hl : raw7486step0Labels = raw7486Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7486 raw7486Labels permutation157 permutation5
    mixedMoment B raw7486step0 raw7486step0Labels = mixedMoment B raw7486step1 raw7486step1Labels := by
      have ha : raw7486step1 = -raw7486step0 := by apply Matrix.ext; change ∀ i j, raw7486step1 i j = -(raw7486step0 i j); unfold raw7486step1 raw7486step0; decide +kernel
      have hl : raw7486step1Labels = raw7486step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7486step1 raw7486step1Labels = mixedMoment B raw7486step2 raw7486step2Labels := by
      have ha : raw7486step2 = raw7486step1 := by apply Matrix.ext; unfold raw7486step2 raw7486step1; decide +kernel
      have hl : raw7486step1Labels = labelEmbedding1 ∘ raw7486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7486step1 raw7486step1Labels raw7486step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

theorem canonical7487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7487 raw7487Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw7487 raw7487Labels = mixedMoment B raw7487step0 raw7487step0Labels := by
      have hz : ∀ j, raw7487 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7487step0 = (fun i j => raw7487 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7487step0 raw7487; decide +kernel
      have hl : raw7487step0Labels = raw7487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7487 raw7487Labels permutation520 hz
    mixedMoment B raw7487step0 raw7487step0Labels = mixedMoment B raw7487step1 raw7487step1Labels := by
      have ha : raw7487step1 = (fun i j => raw7487step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7487step1 raw7487step0; decide +kernel
      have hl : raw7487step1Labels = raw7487step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7487step0 raw7487step0Labels permutation36 permutation5
    mixedMoment B raw7487step1 raw7487step1Labels = mixedMoment B raw7487step2 raw7487step2Labels := by
      have ha : raw7487step2 = -raw7487step1 := by apply Matrix.ext; change ∀ i j, raw7487step2 i j = -(raw7487step1 i j); unfold raw7487step2 raw7487step1; decide +kernel
      have hl : raw7487step2Labels = raw7487step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7487step2 raw7487step2Labels = mixedMoment B raw7487step3 raw7487step3Labels := by
      have ha : raw7487step3 = raw7487step2 := by apply Matrix.ext; unfold raw7487step3 raw7487step2; decide +kernel
      have hl : raw7487step2Labels = labelEmbedding1 ∘ raw7487step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7487step2 raw7487step2Labels raw7487step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

theorem canonical7488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7488 raw7488Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw7488 raw7488Labels = mixedMoment B raw7488step0 raw7488step0Labels := by
      have ha : raw7488step0 = (fun i j => raw7488 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7488step0 raw7488; decide +kernel
      have hl : raw7488step0Labels = raw7488Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7488 raw7488Labels permutation171 permutation5
    mixedMoment B raw7488step0 raw7488step0Labels = mixedMoment B raw7488step1 raw7488step1Labels := by
      have ha : raw7488step1 = -raw7488step0 := by apply Matrix.ext; change ∀ i j, raw7488step1 i j = -(raw7488step0 i j); unfold raw7488step1 raw7488step0; decide +kernel
      have hl : raw7488step1Labels = raw7488step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7488step1 raw7488step1Labels = mixedMoment B raw7488step2 raw7488step2Labels := by
      have ha : raw7488step2 = raw7488step1 := by apply Matrix.ext; unfold raw7488step2 raw7488step1; decide +kernel
      have hl : raw7488step1Labels = labelEmbedding1 ∘ raw7488step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7488step1 raw7488step1Labels raw7488step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3503 node3503Labels := by rfl

theorem canonical7489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7489 raw7489Labels = mixedMoment B node1606 node1606Labels := by
  calc
    mixedMoment B raw7489 raw7489Labels = mixedMoment B raw7489step0 raw7489step0Labels := by
      have ha : raw7489step0 = (fun i j => raw7489 (permutation170 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7489step0 raw7489; decide +kernel
      have hl : raw7489step0Labels = raw7489Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7489 raw7489Labels permutation170 permutation5
    mixedMoment B raw7489step0 raw7489step0Labels = mixedMoment B raw7489step1 raw7489step1Labels := by
      have ha : raw7489step1 = -raw7489step0 := by apply Matrix.ext; change ∀ i j, raw7489step1 i j = -(raw7489step0 i j); unfold raw7489step1 raw7489step0; decide +kernel
      have hl : raw7489step1Labels = raw7489step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7489step1 raw7489step1Labels = mixedMoment B raw7489step2 raw7489step2Labels := by
      have ha : raw7489step2 = raw7489step1 := by apply Matrix.ext; unfold raw7489step2 raw7489step1; decide +kernel
      have hl : raw7489step1Labels = labelEmbedding1 ∘ raw7489step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7489step1 raw7489step1Labels raw7489step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1606 node1606Labels := by rfl

theorem canonical7490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7490 raw7490Labels = mixedMoment B node3345 node3345Labels := by
  calc
    mixedMoment B raw7490 raw7490Labels = mixedMoment B raw7490step0 raw7490step0Labels := by
      have ha : raw7490step0 = (fun i j => raw7490 (permutation170 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7490step0 raw7490; decide +kernel
      have hl : raw7490step0Labels = raw7490Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7490 raw7490Labels permutation170 permutation5
    mixedMoment B raw7490step0 raw7490step0Labels = mixedMoment B raw7490step1 raw7490step1Labels := by
      have ha : raw7490step1 = -raw7490step0 := by apply Matrix.ext; change ∀ i j, raw7490step1 i j = -(raw7490step0 i j); unfold raw7490step1 raw7490step0; decide +kernel
      have hl : raw7490step1Labels = raw7490step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7490step1 raw7490step1Labels = mixedMoment B raw7490step2 raw7490step2Labels := by
      have ha : raw7490step2 = raw7490step1 := by apply Matrix.ext; unfold raw7490step2 raw7490step1; decide +kernel
      have hl : raw7490step1Labels = labelEmbedding1 ∘ raw7490step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7490step1 raw7490step1Labels raw7490step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3345 node3345Labels := by rfl

theorem canonical7491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7491 raw7491Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw7491 raw7491Labels = mixedMoment B raw7491step0 raw7491step0Labels := by
      have ha : raw7491step0 = (fun i j => raw7491 (permutation156 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7491step0 raw7491; decide +kernel
      have hl : raw7491step0Labels = raw7491Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7491 raw7491Labels permutation156 permutation5
    mixedMoment B raw7491step0 raw7491step0Labels = mixedMoment B raw7491step1 raw7491step1Labels := by
      have ha : raw7491step1 = -raw7491step0 := by apply Matrix.ext; change ∀ i j, raw7491step1 i j = -(raw7491step0 i j); unfold raw7491step1 raw7491step0; decide +kernel
      have hl : raw7491step1Labels = raw7491step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7491step1 raw7491step1Labels = mixedMoment B raw7491step2 raw7491step2Labels := by
      have ha : raw7491step2 = raw7491step1 := by apply Matrix.ext; unfold raw7491step2 raw7491step1; decide +kernel
      have hl : raw7491step1Labels = labelEmbedding1 ∘ raw7491step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7491step1 raw7491step1Labels raw7491step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical7492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7492 raw7492Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw7492 raw7492Labels = mixedMoment B raw7492step0 raw7492step0Labels := by
      have ha : raw7492step0 = (fun i j => raw7492 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7492step0 raw7492; decide +kernel
      have hl : raw7492step0Labels = raw7492Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7492 raw7492Labels permutation162 permutation5
    mixedMoment B raw7492step0 raw7492step0Labels = mixedMoment B raw7492step1 raw7492step1Labels := by
      have ha : raw7492step1 = -raw7492step0 := by apply Matrix.ext; change ∀ i j, raw7492step1 i j = -(raw7492step0 i j); unfold raw7492step1 raw7492step0; decide +kernel
      have hl : raw7492step1Labels = raw7492step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7492step1 raw7492step1Labels = mixedMoment B raw7492step2 raw7492step2Labels := by
      have ha : raw7492step2 = raw7492step1 := by apply Matrix.ext; unfold raw7492step2 raw7492step1; decide +kernel
      have hl : raw7492step1Labels = labelEmbedding1 ∘ raw7492step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7492step1 raw7492step1Labels raw7492step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical7493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7493 raw7493Labels = mixedMoment B node3502 node3502Labels := by
  calc
    mixedMoment B raw7493 raw7493Labels = mixedMoment B raw7493step0 raw7493step0Labels := by
      have ha : raw7493step0 = (fun i j => raw7493 (permutation170 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7493step0 raw7493; decide +kernel
      have hl : raw7493step0Labels = raw7493Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7493 raw7493Labels permutation170 permutation5
    mixedMoment B raw7493step0 raw7493step0Labels = mixedMoment B raw7493step1 raw7493step1Labels := by
      have ha : raw7493step1 = -raw7493step0 := by apply Matrix.ext; change ∀ i j, raw7493step1 i j = -(raw7493step0 i j); unfold raw7493step1 raw7493step0; decide +kernel
      have hl : raw7493step1Labels = raw7493step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7493step1 raw7493step1Labels = mixedMoment B raw7493step2 raw7493step2Labels := by
      have ha : raw7493step2 = raw7493step1 := by apply Matrix.ext; unfold raw7493step2 raw7493step1; decide +kernel
      have hl : raw7493step1Labels = labelEmbedding1 ∘ raw7493step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7493step1 raw7493step1Labels raw7493step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3502 node3502Labels := by rfl

theorem canonical7494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7494 raw7494Labels = mixedMoment B node1613 node1613Labels := by
  calc
    mixedMoment B raw7494 raw7494Labels = mixedMoment B raw7494step0 raw7494step0Labels := by
      have ha : raw7494step0 = (fun i j => raw7494 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7494step0 raw7494; decide +kernel
      have hl : raw7494step0Labels = raw7494Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7494 raw7494Labels permutation152 permutation5
    mixedMoment B raw7494step0 raw7494step0Labels = mixedMoment B raw7494step1 raw7494step1Labels := by
      have ha : raw7494step1 = -raw7494step0 := by apply Matrix.ext; change ∀ i j, raw7494step1 i j = -(raw7494step0 i j); unfold raw7494step1 raw7494step0; decide +kernel
      have hl : raw7494step1Labels = raw7494step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7494step1 raw7494step1Labels = mixedMoment B raw7494step2 raw7494step2Labels := by
      have ha : raw7494step2 = raw7494step1 := by apply Matrix.ext; unfold raw7494step2 raw7494step1; decide +kernel
      have hl : raw7494step1Labels = labelEmbedding1 ∘ raw7494step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7494step1 raw7494step1Labels raw7494step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1613 node1613Labels := by rfl

theorem canonical7495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7495 raw7495Labels = mixedMoment B node3350 node3350Labels := by
  calc
    mixedMoment B raw7495 raw7495Labels = mixedMoment B raw7495step0 raw7495step0Labels := by
      have ha : raw7495step0 = (fun i j => raw7495 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7495step0 raw7495; decide +kernel
      have hl : raw7495step0Labels = raw7495Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7495 raw7495Labels permutation152 permutation5
    mixedMoment B raw7495step0 raw7495step0Labels = mixedMoment B raw7495step1 raw7495step1Labels := by
      have ha : raw7495step1 = -raw7495step0 := by apply Matrix.ext; change ∀ i j, raw7495step1 i j = -(raw7495step0 i j); unfold raw7495step1 raw7495step0; decide +kernel
      have hl : raw7495step1Labels = raw7495step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7495step1 raw7495step1Labels = mixedMoment B raw7495step2 raw7495step2Labels := by
      have ha : raw7495step2 = raw7495step1 := by apply Matrix.ext; unfold raw7495step2 raw7495step1; decide +kernel
      have hl : raw7495step1Labels = labelEmbedding1 ∘ raw7495step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7495step1 raw7495step1Labels raw7495step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3350 node3350Labels := by rfl

theorem canonical7496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7496 raw7496Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw7496 raw7496Labels = mixedMoment B raw7496step0 raw7496step0Labels := by
      have ha : raw7496step0 = (fun i j => raw7496 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7496step0 raw7496; decide +kernel
      have hl : raw7496step0Labels = raw7496Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7496 raw7496Labels permutation152 permutation5
    mixedMoment B raw7496step0 raw7496step0Labels = mixedMoment B raw7496step1 raw7496step1Labels := by
      have ha : raw7496step1 = -raw7496step0 := by apply Matrix.ext; change ∀ i j, raw7496step1 i j = -(raw7496step0 i j); unfold raw7496step1 raw7496step0; decide +kernel
      have hl : raw7496step1Labels = raw7496step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7496step1 raw7496step1Labels = mixedMoment B raw7496step2 raw7496step2Labels := by
      have ha : raw7496step2 = raw7496step1 := by apply Matrix.ext; unfold raw7496step2 raw7496step1; decide +kernel
      have hl : raw7496step1Labels = labelEmbedding1 ∘ raw7496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7496step1 raw7496step1Labels raw7496step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

theorem canonical7497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7497 raw7497Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw7497 raw7497Labels = mixedMoment B raw7497step0 raw7497step0Labels := by
      have ha : raw7497step0 = (fun i j => raw7497 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7497step0 raw7497; decide +kernel
      have hl : raw7497step0Labels = raw7497Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7497 raw7497Labels permutation158 permutation5
    mixedMoment B raw7497step0 raw7497step0Labels = mixedMoment B raw7497step1 raw7497step1Labels := by
      have ha : raw7497step1 = -raw7497step0 := by apply Matrix.ext; change ∀ i j, raw7497step1 i j = -(raw7497step0 i j); unfold raw7497step1 raw7497step0; decide +kernel
      have hl : raw7497step1Labels = raw7497step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7497step1 raw7497step1Labels = mixedMoment B raw7497step2 raw7497step2Labels := by
      have ha : raw7497step2 = raw7497step1 := by apply Matrix.ext; unfold raw7497step2 raw7497step1; decide +kernel
      have hl : raw7497step1Labels = labelEmbedding1 ∘ raw7497step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7497step1 raw7497step1Labels raw7497step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

theorem canonical7498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7498 raw7498Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw7498 raw7498Labels = mixedMoment B raw7498step0 raw7498step0Labels := by
      have hz : ∀ j, raw7498 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7498step0 = (fun i j => raw7498 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7498step0 raw7498; decide +kernel
      have hl : raw7498step0Labels = raw7498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7498 raw7498Labels permutation520 hz
    mixedMoment B raw7498step0 raw7498step0Labels = mixedMoment B raw7498step1 raw7498step1Labels := by
      have ha : raw7498step1 = (fun i j => raw7498step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7498step1 raw7498step0; decide +kernel
      have hl : raw7498step1Labels = raw7498step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7498step0 raw7498step0Labels permutation32 permutation5
    mixedMoment B raw7498step1 raw7498step1Labels = mixedMoment B raw7498step2 raw7498step2Labels := by
      have ha : raw7498step2 = -raw7498step1 := by apply Matrix.ext; change ∀ i j, raw7498step2 i j = -(raw7498step1 i j); unfold raw7498step2 raw7498step1; decide +kernel
      have hl : raw7498step2Labels = raw7498step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7498step2 raw7498step2Labels = mixedMoment B raw7498step3 raw7498step3Labels := by
      have ha : raw7498step3 = raw7498step2 := by apply Matrix.ext; unfold raw7498step3 raw7498step2; decide +kernel
      have hl : raw7498step2Labels = labelEmbedding1 ∘ raw7498step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7498step2 raw7498step2Labels raw7498step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3543 node3543Labels := by rfl

theorem canonical7499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7499 raw7499Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw7499 raw7499Labels = mixedMoment B raw7499step0 raw7499step0Labels := by
      have ha : raw7499step0 = (fun i j => raw7499 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7499step0 raw7499; decide +kernel
      have hl : raw7499step0Labels = raw7499Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7499 raw7499Labels permutation182 permutation2
    _ = mixedMoment B node3064 node3064Labels := by rfl

theorem canonical7500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7500 raw7500Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw7500 raw7500Labels = mixedMoment B raw7500step0 raw7500step0Labels := by
      have ha : raw7500step0 = (fun i j => raw7500 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7500step0 raw7500; decide +kernel
      have hl : raw7500step0Labels = raw7500Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7500 raw7500Labels permutation682 permutation2
    mixedMoment B raw7500step0 raw7500step0Labels = mixedMoment B raw7500step1 raw7500step1Labels := by
      have ha : raw7500step1 = -raw7500step0 := by apply Matrix.ext; change ∀ i j, raw7500step1 i j = -(raw7500step0 i j); unfold raw7500step1 raw7500step0; decide +kernel
      have hl : raw7500step1Labels = raw7500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3846 node3846Labels := by rfl

theorem canonical7501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7501 raw7501Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw7501 raw7501Labels = mixedMoment B raw7501step0 raw7501step0Labels := by
      have ha : raw7501step0 = (fun i j => raw7501 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7501step0 raw7501; decide +kernel
      have hl : raw7501step0Labels = raw7501Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7501 raw7501Labels permutation676 permutation2
    mixedMoment B raw7501step0 raw7501step0Labels = mixedMoment B raw7501step1 raw7501step1Labels := by
      have ha : raw7501step1 = -raw7501step0 := by apply Matrix.ext; change ∀ i j, raw7501step1 i j = -(raw7501step0 i j); unfold raw7501step1 raw7501step0; decide +kernel
      have hl : raw7501step1Labels = raw7501step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical7502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7502 raw7502Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw7502 raw7502Labels = mixedMoment B raw7502step0 raw7502step0Labels := by
      have ha : raw7502step0 = (fun i j => raw7502 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7502step0 raw7502; decide +kernel
      have hl : raw7502step0Labels = raw7502Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7502 raw7502Labels permutation674 permutation2
    mixedMoment B raw7502step0 raw7502step0Labels = mixedMoment B raw7502step1 raw7502step1Labels := by
      have ha : raw7502step1 = -raw7502step0 := by apply Matrix.ext; change ∀ i j, raw7502step1 i j = -(raw7502step0 i j); unfold raw7502step1 raw7502step0; decide +kernel
      have hl : raw7502step1Labels = raw7502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical7503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7503 raw7503Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw7503 raw7503Labels = mixedMoment B raw7503step0 raw7503step0Labels := by
      have hz : ∀ j, raw7503 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7503step0 = (fun i j => raw7503 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7503step0 raw7503; decide +kernel
      have hl : raw7503step0Labels = raw7503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7503 raw7503Labels permutation520 hz
    mixedMoment B raw7503step0 raw7503step0Labels = mixedMoment B raw7503step1 raw7503step1Labels := by
      have ha : raw7503step1 = (fun i j => raw7503step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7503step1 raw7503step0; decide +kernel
      have hl : raw7503step1Labels = raw7503step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7503step0 raw7503step0Labels permutation137 permutation2
    mixedMoment B raw7503step1 raw7503step1Labels = mixedMoment B raw7503step2 raw7503step2Labels := by
      have ha : raw7503step2 = -raw7503step1 := by apply Matrix.ext; change ∀ i j, raw7503step2 i j = -(raw7503step1 i j); unfold raw7503step2 raw7503step1; decide +kernel
      have hl : raw7503step2Labels = raw7503step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3902 node3902Labels := by rfl

theorem canonical7504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7504 raw7504Labels = mixedMoment B node4008 node4008Labels := by
  calc
    mixedMoment B raw7504 raw7504Labels = mixedMoment B raw7504step0 raw7504step0Labels := by
      have ha : raw7504step0 = (fun i j => raw7504 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7504step0 raw7504; decide +kernel
      have hl : raw7504step0Labels = raw7504Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7504 raw7504Labels permutation182 permutation2
    _ = mixedMoment B node4008 node4008Labels := by rfl

theorem canonical7505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7505 raw7505Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw7505 raw7505Labels = mixedMoment B raw7505step0 raw7505step0Labels := by
      have hz : ∀ j, raw7505 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7505step0 = (fun i j => raw7505 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7505step0 raw7505; decide +kernel
      have hl : raw7505step0Labels = raw7505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7505 raw7505Labels permutation520 hz
    mixedMoment B raw7505step0 raw7505step0Labels = mixedMoment B raw7505step1 raw7505step1Labels := by
      have ha : raw7505step1 = (fun i j => raw7505step0 (permutation134 i) (permutation0 j)) := by apply Matrix.ext; unfold raw7505step1 raw7505step0; decide +kernel
      have hl : raw7505step1Labels = raw7505step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7505step0 raw7505step0Labels permutation134 permutation0
    mixedMoment B raw7505step1 raw7505step1Labels = mixedMoment B raw7505step2 raw7505step2Labels := by
      have ha : raw7505step2 = -raw7505step1 := by apply Matrix.ext; change ∀ i j, raw7505step2 i j = -(raw7505step1 i j); unfold raw7505step2 raw7505step1; decide +kernel
      have hl : raw7505step2Labels = raw7505step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical7506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7506 raw7506Labels = mixedMoment B node1383 node1383Labels := by
  calc
    mixedMoment B raw7506 raw7506Labels = mixedMoment B raw7506step0 raw7506step0Labels := by
      have ha : raw7506step0 = (fun i j => raw7506 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7506step0 raw7506; decide +kernel
      have hl : raw7506step0Labels = raw7506Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7506 raw7506Labels permutation184 permutation2
    _ = mixedMoment B node1383 node1383Labels := by rfl

theorem canonical7507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7507 raw7507Labels = mixedMoment B node1392 node1392Labels := by
  calc
    mixedMoment B raw7507 raw7507Labels = mixedMoment B raw7507step0 raw7507step0Labels := by
      have ha : raw7507step0 = (fun i j => raw7507 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7507step0 raw7507; decide +kernel
      have hl : raw7507step0Labels = raw7507Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7507 raw7507Labels permutation200 permutation2
    _ = mixedMoment B node1392 node1392Labels := by rfl

theorem canonical7508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7508 raw7508Labels = mixedMoment B node1392 node1392Labels := by
  calc
    mixedMoment B raw7508 raw7508Labels = mixedMoment B raw7508step0 raw7508step0Labels := by
      have ha : raw7508step0 = (fun i j => raw7508 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7508step0 raw7508; decide +kernel
      have hl : raw7508step0Labels = raw7508Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7508 raw7508Labels permutation176 permutation2
    _ = mixedMoment B node1392 node1392Labels := by rfl

theorem canonical7509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7509 raw7509Labels = mixedMoment B node1380 node1380Labels := by
  calc
    mixedMoment B raw7509 raw7509Labels = mixedMoment B raw7509step0 raw7509step0Labels := by
      have ha : raw7509step0 = (fun i j => raw7509 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7509step0 raw7509; decide +kernel
      have hl : raw7509step0Labels = raw7509Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7509 raw7509Labels permutation182 permutation2
    _ = mixedMoment B node1380 node1380Labels := by rfl

theorem canonical7510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7510 raw7510Labels = mixedMoment B node1378 node1378Labels := by
  calc
    mixedMoment B raw7510 raw7510Labels = mixedMoment B raw7510step0 raw7510step0Labels := by
      have ha : raw7510step0 = (fun i j => raw7510 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7510step0 raw7510; decide +kernel
      have hl : raw7510step0Labels = raw7510Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7510 raw7510Labels permutation182 permutation2
    _ = mixedMoment B node1378 node1378Labels := by rfl

theorem canonical7511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7511 raw7511Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw7511 raw7511Labels = mixedMoment B raw7511step0 raw7511step0Labels := by
      have ha : raw7511step0 = (fun i j => raw7511 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7511step0 raw7511; decide +kernel
      have hl : raw7511step0Labels = raw7511Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7511 raw7511Labels permutation184 permutation2
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical7512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7512 raw7512Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw7512 raw7512Labels = mixedMoment B raw7512step0 raw7512step0Labels := by
      have ha : raw7512step0 = (fun i j => raw7512 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7512step0 raw7512; decide +kernel
      have hl : raw7512step0Labels = raw7512Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7512 raw7512Labels permutation208 permutation2
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical7513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7513 raw7513Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw7513 raw7513Labels = mixedMoment B raw7513step0 raw7513step0Labels := by
      have hz : ∀ j, raw7513 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7513step0 = (fun i j => raw7513 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7513step0 raw7513; decide +kernel
      have hl : raw7513step0Labels = raw7513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7513 raw7513Labels permutation520 hz
    mixedMoment B raw7513step0 raw7513step0Labels = mixedMoment B raw7513step1 raw7513step1Labels := by
      have ha : raw7513step1 = (fun i j => raw7513step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7513step1 raw7513step0; decide +kernel
      have hl : raw7513step1Labels = raw7513step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7513step0 raw7513step0Labels permutation40 permutation2
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical7514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7514 raw7514Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw7514 raw7514Labels = mixedMoment B raw7514step0 raw7514step0Labels := by
      have ha : raw7514step0 = (fun i j => raw7514 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7514step0 raw7514; decide +kernel
      have hl : raw7514step0Labels = raw7514Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7514 raw7514Labels permutation184 permutation2
    _ = mixedMoment B node3074 node3074Labels := by rfl

theorem canonical7515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7515 raw7515Labels = mixedMoment B node3013 node3013Labels := by
  calc
    mixedMoment B raw7515 raw7515Labels = mixedMoment B raw7515step0 raw7515step0Labels := by
      have ha : raw7515step0 = (fun i j => raw7515 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7515step0 raw7515; decide +kernel
      have hl : raw7515step0Labels = raw7515Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7515 raw7515Labels permutation158 permutation2
    _ = mixedMoment B node3013 node3013Labels := by rfl

theorem canonical7516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7516 raw7516Labels = mixedMoment B node3013 node3013Labels := by
  calc
    _ = mixedMoment B node3013 node3013Labels := by rfl

theorem canonical7517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7517 raw7517Labels = mixedMoment B node3012 node3012Labels := by
  calc
    _ = mixedMoment B node3012 node3012Labels := by rfl

theorem canonical7518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7518 raw7518Labels = mixedMoment B node2562 node2562Labels := by
  calc
    mixedMoment B raw7518 raw7518Labels = mixedMoment B raw7518step0 raw7518step0Labels := by
      have ha : raw7518step0 = (fun i j => raw7518 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7518step0 raw7518; decide +kernel
      have hl : raw7518step0Labels = raw7518Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7518 raw7518Labels permutation682 permutation2
    mixedMoment B raw7518step0 raw7518step0Labels = mixedMoment B raw7518step1 raw7518step1Labels := by
      have ha : raw7518step1 = -raw7518step0 := by apply Matrix.ext; change ∀ i j, raw7518step1 i j = -(raw7518step0 i j); unfold raw7518step1 raw7518step0; decide +kernel
      have hl : raw7518step1Labels = raw7518step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2562 node2562Labels := by rfl

theorem canonical7519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7519 raw7519Labels = mixedMoment B node2933 node2933Labels := by
  calc
    mixedMoment B raw7519 raw7519Labels = mixedMoment B raw7519step0 raw7519step0Labels := by
      have ha : raw7519step0 = (fun i j => raw7519 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7519step0 raw7519; decide +kernel
      have hl : raw7519step0Labels = raw7519Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7519 raw7519Labels permutation176 permutation2
    _ = mixedMoment B node2933 node2933Labels := by rfl

theorem canonical7520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7520 raw7520Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw7520 raw7520Labels = mixedMoment B raw7520step0 raw7520step0Labels := by
      have ha : raw7520step0 = (fun i j => raw7520 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7520step0 raw7520; decide +kernel
      have hl : raw7520step0Labels = raw7520Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7520 raw7520Labels permutation182 permutation2
    _ = mixedMoment B node2916 node2916Labels := by rfl

theorem canonical7521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7521 raw7521Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw7521 raw7521Labels = mixedMoment B raw7521step0 raw7521step0Labels := by
      have ha : raw7521step0 = (fun i j => raw7521 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7521step0 raw7521; decide +kernel
      have hl : raw7521step0Labels = raw7521Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7521 raw7521Labels permutation676 permutation2
    mixedMoment B raw7521step0 raw7521step0Labels = mixedMoment B raw7521step1 raw7521step1Labels := by
      have ha : raw7521step1 = -raw7521step0 := by apply Matrix.ext; change ∀ i j, raw7521step1 i j = -(raw7521step0 i j); unfold raw7521step1 raw7521step0; decide +kernel
      have hl : raw7521step1Labels = raw7521step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2543 node2543Labels := by rfl

theorem canonical7522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7522 raw7522Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw7522 raw7522Labels = mixedMoment B raw7522step0 raw7522step0Labels := by
      have ha : raw7522step0 = (fun i j => raw7522 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7522step0 raw7522; decide +kernel
      have hl : raw7522step0Labels = raw7522Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7522 raw7522Labels permutation206 permutation2
    _ = mixedMoment B node2916 node2916Labels := by rfl

theorem canonical7523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7523 raw7523Labels = mixedMoment B node3066 node3066Labels := by
  calc
    mixedMoment B raw7523 raw7523Labels = mixedMoment B raw7523step0 raw7523step0Labels := by
      have ha : raw7523step0 = (fun i j => raw7523 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7523step0 raw7523; decide +kernel
      have hl : raw7523step0Labels = raw7523Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7523 raw7523Labels permutation183 permutation2
    _ = mixedMoment B node3066 node3066Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3960 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3960 = injectiveMoment H node655 := by
  calc
    injectiveMoment H raw3960 = injectiveMoment H raw3960step0 := by
      have heq : raw3960step0 = -raw3960 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3960).symm
    injectiveMoment H raw3960step0 = injectiveMoment H raw3960step1 := by
      have heq : raw3960step1 = (fun i j => raw3960step0 (permutation33 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3960step0 permutation33 permutation8
    _ = injectiveMoment H node655 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4096 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4096 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4096 = injectiveMoment H raw4096step0 := by
      have hz : ∀ j, raw4096 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw4096step0 = (fun i j => raw4096 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4096 permutation15 hz
    injectiveMoment H raw4096step0 = injectiveMoment H raw4096step1 := by
      have heq : raw4096step1 = (fun i j => raw4096step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4096step0 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

theorem canonical4110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4110 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4110 = injectiveMoment H raw4110step0 := by
      have hz : ∀ j, raw4110 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw4110step0 = (fun i j => raw4110 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4110 permutation21 hz
    injectiveMoment H raw4110step0 = injectiveMoment H raw4110step1 := by
      have heq : raw4110step1 = (fun i j => raw4110step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4110step0 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

theorem canonical4117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4117 = injectiveMoment H node207 := by
  rfl

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

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

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

theorem canonical5139 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5139 = injectiveMoment H node232 := by
  rfl

end MUB6.Certificate.PairSemantics

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

theorem canonical5165 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5165 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5165 = injectiveMoment H raw5165step0 := by
      have hz : ∀ j, raw5165 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5165step0 = (fun i j => raw5165 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5165 permutation104 hz
    injectiveMoment H raw5165step0 = injectiveMoment H raw5165step1 := by
      have hz : ∀ j, raw5165step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5165step1 = (fun i j => raw5165step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5165step0 permutation21 hz
    injectiveMoment H raw5165step1 = injectiveMoment H raw5165step2 := by
      have hz : ∀ j, raw5165step1 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5165step2 = (fun i j => raw5165step1 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5165step1 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7981 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7981 = injectiveMoment H raw7981step0 := by
      have hz : ∀ j, raw7981 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7981step0 = (fun i j => raw7981 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981 permutation128 hz
    injectiveMoment H raw7981step0 = injectiveMoment H raw7981step1 := by
      have hz : ∀ j, raw7981step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7981step1 = (fun i j => raw7981step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step0 permutation27 hz
    injectiveMoment H raw7981step1 = injectiveMoment H raw7981step2 := by
      have hz : ∀ j, raw7981step1 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7981step2 = (fun i j => raw7981step1 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step1 permutation7 hz
    injectiveMoment H raw7981step2 = injectiveMoment H raw7981step3 := by
      have hz : ∀ j, raw7981step2 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7981step3 = (fun i j => raw7981step2 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step2 permutation2 hz
    injectiveMoment H raw7981step3 = injectiveMoment H raw7981step4 := by
      have hz : ∀ j, raw7981step3 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7981step4 = (fun i j => raw7981step3 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step3 permutation0 hz
    injectiveMoment H raw7981step4 = injectiveMoment H raw7981step5 := by
      have hz : ∀ i, raw7981step4 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7981step5 = (fun i j => raw7981step4 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7981step4 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical282
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9030 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9030 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw9030 = injectiveMoment H raw9030step0 := by
      have hz : ∀ j, raw9030 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9030step0 = (fun i j => raw9030 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9030 permutation33 hz
    injectiveMoment H raw9030step0 = injectiveMoment H raw9030step1 := by
      have heq : raw9030step1 = (fun i j => raw9030step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9030step0 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

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

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4956 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4956 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4956 = injectiveMoment H raw4956step0 := by
      have heq : raw4956step0 = -raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4956).symm
    injectiveMoment H raw4956step0 = injectiveMoment H raw4956step1 := by
      have heq : raw4956step1 = (fun i j => raw4956step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4956step0 permutation4 permutation8
    _ = injectiveMoment H node62 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2803 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2803 = injectiveMoment H node176 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound207 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node207 = Sparse.eval value207 (momentVector H) := by
  have heq : pivotMatrix207 = (fun u v => node207 (pivotPermutation207 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node207 = injectiveMoment H pivotMatrix207 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix207 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix207 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix207 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (0 : Fin 3) = raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4956 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix207 (1 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (1 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix207 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (2 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node207 + (injectiveMoment H (mergeFirst pivotMatrix207 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix207 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix207 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value207, value41, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound232 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node232 = Sparse.eval value232 (momentVector H) := by
  have heq : pivotMatrix232 = (fun u v => node232 (pivotPermutation232 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node232 = injectiveMoment H pivotMatrix232 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix232 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix232 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix232 (0 : Fin 4)) =
      Sparse.eval value26 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (0 : Fin 4) = raw914 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical914 hH).trans (sound26 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix232 (1 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (1 : Fin 4) = raw5177 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5177 hH).trans (sound11 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix232 (2 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (2 : Fin 4) = raw5197 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5197 hH).trans (sound11 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix232 (3 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (3 : Fin 4) = raw5204 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5204 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node232 + (injectiveMoment H (mergeFirst pivotMatrix232 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value232, value11, value26, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound10
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound655 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node655 = Sparse.eval value655 (momentVector H) := by
  have heq : pivotMatrix655 = (fun u v => node655 (pivotPermutation655 u) v) := by apply Matrix.ext; unfold pivotMatrix655 node655 pivotPermutation655; decide +kernel
  have hmoment : injectiveMoment H node655 = injectiveMoment H pivotMatrix655 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix655 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix655 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix655 (0 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix655 (0 : Fin 4) = raw2803 := by apply Matrix.ext; unfold mergeFirst pivotMatrix655 raw2803; decide +kernel
    rw [heq]
    exact (canonical2803 hH).trans (sound176 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix655 (1 : Fin 4)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix655 (1 : Fin 4) = raw4096 := by apply Matrix.ext; unfold mergeFirst pivotMatrix655 raw4096; decide +kernel
    rw [heq]
    exact (canonical4096 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix655 (2 : Fin 4)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix655 (2 : Fin 4) = raw4110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix655 raw4110; decide +kernel
    rw [heq]
    exact (canonical4110 hH).trans (sound62 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix655 (3 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix655 (3 : Fin 4) = raw4117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix655 raw4117; decide +kernel
    rw [heq]
    exact (canonical4117 hH).trans (sound207 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node655 + (injectiveMoment H (mergeFirst pivotMatrix655 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix655 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix655 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix655 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value655, value176, value207, value62, Sparse.eval] at hc ⊢
  linarith

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

theorem singlePair494 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node494 node494Labels = Sparse.eval singlePairValue494 (familyPairVector B) := by
  have hp := single_label_three B hB node494
  have hl : node494Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node494 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 1) = PairSemantics.raw5165 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node494 PairSemantics.raw5165; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5165 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 2) = PairSemantics.raw9030 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node494 PairSemantics.raw9030; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9030 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 3) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node494 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value655 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 4) = PairSemantics.raw3960 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node494 PairSemantics.raw3960; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3960 hH).trans (PairSemantics.sound655 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue494, PairSemantics.value0, PairSemantics.value4, PairSemantics.value65, PairSemantics.value232, PairSemantics.value655, Sparse.eval] at hp ⊢
  linarith only [hp]

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

theorem singleton3858 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3858 node3858Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node494 node494Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw534 singletonSmall3858
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3858) = raw534Labels := by decide +kernel
  rw [hl, canonical534 B hB] at h
  have hc0 : mixedMoment B raw534 (Fin.cases (0 : Fin 1) singletonSmall3858) =
      mixedMoment B node494 node494Labels := by
    have ha : raw534 = raw535 := by apply Matrix.ext; unfold raw534 raw535; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3858 = raw535Labels := by decide +kernel
    rw [ha, hj, canonical535 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1216 node1216Labels = Sparse.eval nodeValue1216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1216) = mixedMoment B node1216 node1216Labels := rfl
  simpa [nodeValue1216, Sparse.eval] using hc.symm

theorem sound1248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1248 node1248Labels = Sparse.eval nodeValue1248 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1248) = mixedMoment B node1248 node1248Labels := rfl
  simpa [nodeValue1248, Sparse.eval] using hc.symm

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

theorem sound1378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1378 node1378Labels = Sparse.eval nodeValue1378 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1378) = mixedMoment B node1378 node1378Labels := rfl
  simpa [nodeValue1378, Sparse.eval] using hc.symm

theorem sound1380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1380 node1380Labels = Sparse.eval nodeValue1380 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1380) = mixedMoment B node1380 node1380Labels := rfl
  simpa [nodeValue1380, Sparse.eval] using hc.symm

theorem sound1383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1383 node1383Labels = Sparse.eval nodeValue1383 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1383) = mixedMoment B node1383 node1383Labels := rfl
  simpa [nodeValue1383, Sparse.eval] using hc.symm

theorem sound1392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1392 node1392Labels = Sparse.eval nodeValue1392 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1392) = mixedMoment B node1392 node1392Labels := rfl
  simpa [nodeValue1392, Sparse.eval] using hc.symm

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

theorem sound1606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1606 node1606Labels = Sparse.eval nodeValue1606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1606) = mixedMoment B node1606 node1606Labels := rfl
  simpa [nodeValue1606, Sparse.eval] using hc.symm

theorem sound1607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1607 node1607Labels = Sparse.eval nodeValue1607 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1607) = mixedMoment B node1607 node1607Labels := rfl
  simpa [nodeValue1607, Sparse.eval] using hc.symm

theorem sound1613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1613 node1613Labels = Sparse.eval nodeValue1613 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1613) = mixedMoment B node1613 node1613Labels := rfl
  simpa [nodeValue1613, Sparse.eval] using hc.symm

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

theorem sound1713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1713 node1713Labels = Sparse.eval nodeValue1713 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1713) = mixedMoment B node1713 node1713Labels := rfl
  simpa [nodeValue1713, Sparse.eval] using hc.symm

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

theorem sound2471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2471 node2471Labels = Sparse.eval nodeValue2471 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2471) = mixedMoment B node2471 node2471Labels := rfl
  simpa [nodeValue2471, Sparse.eval] using hc.symm

theorem sound2473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2473 node2473Labels = Sparse.eval nodeValue2473 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2473) = mixedMoment B node2473 node2473Labels := rfl
  simpa [nodeValue2473, Sparse.eval] using hc.symm

theorem sound2483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2483 node2483Labels = Sparse.eval nodeValue2483 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2483) = mixedMoment B node2483 node2483Labels := rfl
  simpa [nodeValue2483, Sparse.eval] using hc.symm

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

theorem sound2543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2543 node2543Labels = Sparse.eval nodeValue2543 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2543) = mixedMoment B node2543 node2543Labels := rfl
  simpa [nodeValue2543, Sparse.eval] using hc.symm

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

theorem sound2562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2562 node2562Labels = Sparse.eval nodeValue2562 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2562) = mixedMoment B node2562 node2562Labels := rfl
  simpa [nodeValue2562, Sparse.eval] using hc.symm

theorem sound2611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2611 node2611Labels = Sparse.eval nodeValue2611 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2611) = mixedMoment B node2611 node2611Labels := rfl
  simpa [nodeValue2611, Sparse.eval] using hc.symm

theorem sound2612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2612 node2612Labels = Sparse.eval nodeValue2612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2612) = mixedMoment B node2612 node2612Labels := rfl
  simpa [nodeValue2612, Sparse.eval] using hc.symm

theorem sound2617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2617 node2617Labels = Sparse.eval nodeValue2617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2617) = mixedMoment B node2617 node2617Labels := rfl
  simpa [nodeValue2617, Sparse.eval] using hc.symm

theorem sound2623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2623 node2623Labels = Sparse.eval nodeValue2623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2623) = mixedMoment B node2623 node2623Labels := rfl
  simpa [nodeValue2623, Sparse.eval] using hc.symm

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

theorem sound2707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2707 node2707Labels = Sparse.eval nodeValue2707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2707) = mixedMoment B node2707 node2707Labels := rfl
  simpa [nodeValue2707, Sparse.eval] using hc.symm

theorem sound2710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2710 node2710Labels = Sparse.eval nodeValue2710 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2710) = mixedMoment B node2710 node2710Labels := rfl
  simpa [nodeValue2710, Sparse.eval] using hc.symm

theorem sound2721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2721 node2721Labels = Sparse.eval nodeValue2721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2721) = mixedMoment B node2721 node2721Labels := rfl
  simpa [nodeValue2721, Sparse.eval] using hc.symm

theorem sound2745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2745 node2745Labels = Sparse.eval nodeValue2745 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2745) = mixedMoment B node2745 node2745Labels := rfl
  simpa [nodeValue2745, Sparse.eval] using hc.symm

theorem sound2750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2750 node2750Labels = Sparse.eval nodeValue2750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2750) = mixedMoment B node2750 node2750Labels := rfl
  simpa [nodeValue2750, Sparse.eval] using hc.symm

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

theorem sound2916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2916 node2916Labels = Sparse.eval nodeValue2916 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2916) = mixedMoment B node2916 node2916Labels := rfl
  simpa [nodeValue2916, Sparse.eval] using hc.symm

theorem sound2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2924 node2924Labels = Sparse.eval nodeValue2924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2924) = mixedMoment B node2924 node2924Labels := rfl
  simpa [nodeValue2924, Sparse.eval] using hc.symm

theorem sound2933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2933 node2933Labels = Sparse.eval nodeValue2933 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2933) = mixedMoment B node2933 node2933Labels := rfl
  simpa [nodeValue2933, Sparse.eval] using hc.symm

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

theorem sound3012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3012 node3012Labels = Sparse.eval nodeValue3012 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3012) = mixedMoment B node3012 node3012Labels := rfl
  simpa [nodeValue3012, Sparse.eval] using hc.symm

theorem sound3013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3013 node3013Labels = Sparse.eval nodeValue3013 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3013) = mixedMoment B node3013 node3013Labels := rfl
  simpa [nodeValue3013, Sparse.eval] using hc.symm

theorem sound3064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3064 node3064Labels = Sparse.eval nodeValue3064 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3064) = mixedMoment B node3064 node3064Labels := rfl
  simpa [nodeValue3064, Sparse.eval] using hc.symm

theorem sound3066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3066 node3066Labels = Sparse.eval nodeValue3066 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3066) = mixedMoment B node3066 node3066Labels := rfl
  simpa [nodeValue3066, Sparse.eval] using hc.symm

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

theorem sound3345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3345 node3345Labels = Sparse.eval nodeValue3345 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3345) = mixedMoment B node3345 node3345Labels := rfl
  simpa [nodeValue3345, Sparse.eval] using hc.symm

theorem sound3346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3346 node3346Labels = Sparse.eval nodeValue3346 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3346) = mixedMoment B node3346 node3346Labels := rfl
  simpa [nodeValue3346, Sparse.eval] using hc.symm

theorem sound3350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3350 node3350Labels = Sparse.eval nodeValue3350 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3350) = mixedMoment B node3350 node3350Labels := rfl
  simpa [nodeValue3350, Sparse.eval] using hc.symm

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

theorem sound3502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3502 node3502Labels = Sparse.eval nodeValue3502 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3502) = mixedMoment B node3502 node3502Labels := rfl
  simpa [nodeValue3502, Sparse.eval] using hc.symm

theorem sound3503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3503 node3503Labels = Sparse.eval nodeValue3503 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3503) = mixedMoment B node3503 node3503Labels := rfl
  simpa [nodeValue3503, Sparse.eval] using hc.symm

theorem sound3516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3516 node3516Labels = Sparse.eval nodeValue3516 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3516) = mixedMoment B node3516 node3516Labels := rfl
  simpa [nodeValue3516, Sparse.eval] using hc.symm

theorem sound3517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3517 node3517Labels = Sparse.eval nodeValue3517 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3517) = mixedMoment B node3517 node3517Labels := rfl
  simpa [nodeValue3517, Sparse.eval] using hc.symm

theorem sound3519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3519 node3519Labels = Sparse.eval nodeValue3519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3519) = mixedMoment B node3519 node3519Labels := rfl
  simpa [nodeValue3519, Sparse.eval] using hc.symm

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

theorem sound3540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3540 node3540Labels = Sparse.eval nodeValue3540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3540) = mixedMoment B node3540 node3540Labels := rfl
  simpa [nodeValue3540, Sparse.eval] using hc.symm

theorem sound3543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3543 node3543Labels = Sparse.eval nodeValue3543 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3543) = mixedMoment B node3543 node3543Labels := rfl
  simpa [nodeValue3543, Sparse.eval] using hc.symm

theorem sound3571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3571 node3571Labels = Sparse.eval nodeValue3571 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3571) = mixedMoment B node3571 node3571Labels := rfl
  simpa [nodeValue3571, Sparse.eval] using hc.symm

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

theorem sound3605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3605 node3605Labels = Sparse.eval nodeValue3605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3605) = mixedMoment B node3605 node3605Labels := rfl
  simpa [nodeValue3605, Sparse.eval] using hc.symm

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

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

theorem sound494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node494 node494Labels = Sparse.eval nodeValue494 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue494 (familyPairVector B) := singlePair494 B _hB
    _ = _ := by norm_num [singlePairValue494, nodeValue494, Sparse.eval, mixedVector] <;> ring

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

theorem sound3801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3801 node3801Labels = Sparse.eval nodeValue3801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3801) = mixedMoment B node3801 node3801Labels := rfl
  simpa [nodeValue3801, Sparse.eval] using hc.symm

theorem sound3838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3838 node3838Labels = Sparse.eval nodeValue3838 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3838) = mixedMoment B node3838 node3838Labels := rfl
  simpa [nodeValue3838, Sparse.eval] using hc.symm

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

theorem sound3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3843 node3843Labels = Sparse.eval nodeValue3843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3843) = mixedMoment B node3843 node3843Labels := rfl
  simpa [nodeValue3843, Sparse.eval] using hc.symm

theorem sound3846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3846 node3846Labels = Sparse.eval nodeValue3846 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3846) = mixedMoment B node3846 node3846Labels := rfl
  simpa [nodeValue3846, Sparse.eval] using hc.symm

theorem sound3858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3858 node3858Labels = Sparse.eval nodeValue3858 (mixedVector B) := by
  have h := singleton3858 B _hB
  rw [sound494 B _hB _hF] at h
  norm_num [nodeValue3858, nodeValue494, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3872 node3872Labels = Sparse.eval nodeValue3872 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3872) = mixedMoment B node3872 node3872Labels := rfl
  simpa [nodeValue3872, Sparse.eval] using hc.symm

theorem sound3874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3874 node3874Labels = Sparse.eval nodeValue3874 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3874) = mixedMoment B node3874 node3874Labels := rfl
  simpa [nodeValue3874, Sparse.eval] using hc.symm

theorem sound3899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3899 node3899Labels = Sparse.eval nodeValue3899 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3899) = mixedMoment B node3899 node3899Labels := rfl
  simpa [nodeValue3899, Sparse.eval] using hc.symm

theorem sound3901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3901 node3901Labels = Sparse.eval nodeValue3901 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3901) = mixedMoment B node3901 node3901Labels := rfl
  simpa [nodeValue3901, Sparse.eval] using hc.symm

theorem sound3902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3902 node3902Labels = Sparse.eval nodeValue3902 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3902) = mixedMoment B node3902 node3902Labels := rfl
  simpa [nodeValue3902, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3991 node3991Labels = 0 := by
  exact mixedMoment_alpha B hF node3991 node3991Labels 1 permutation161
    (by decide +kernel)

theorem zero4008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4008 node4008Labels = 0 := by
  exact mixedMoment_alpha B hF node4008 node4008Labels 1 permutation213
    (by decide +kernel)

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

theorem sound3991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3991 node3991Labels = Sparse.eval nodeValue3991 (mixedVector B) := by
  simpa only [nodeValue3991, Sparse.eval_nil] using zero3991 B _hB _hF

theorem sound4008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4008 node4008Labels = Sparse.eval nodeValue4008 (mixedVector B) := by
  simpa only [nodeValue4008, Sparse.eval_nil] using zero4008 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources11
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq382 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm382 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA382 + difference 0 0) (sourceB382 + difference 0 0) sourceC382) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA382 + difference 0 0) (sourceB382 + difference 0 0) sourceC382) = raw7381 := by
      apply Matrix.ext; unfold tripleCharges sourceA382 sourceB382 sourceC382 difference raw7381; decide +kernel
    rw [ha]
    exact (canonical7381 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA382 + difference 0 1) (sourceB382 + difference 1 0) sourceC382) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA382 + difference 0 1) (sourceB382 + difference 1 0) sourceC382) = raw7382 := by
      apply Matrix.ext; unfold tripleCharges sourceA382 sourceB382 sourceC382 difference raw7382; decide +kernel
    rw [ha]
    exact (canonical7382 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA382 + difference 0 2) (sourceB382 + difference 2 0) sourceC382) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA382 + difference 0 2) (sourceB382 + difference 2 0) sourceC382) = raw7383 := by
      apply Matrix.ext; unfold tripleCharges sourceA382 sourceB382 sourceC382 difference raw7383; decide +kernel
    rw [ha]
    exact (canonical7383 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA382 + difference 0 3) (sourceB382 + difference 3 0) sourceC382) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA382 + difference 0 3) (sourceB382 + difference 3 0) sourceC382) = raw7384 := by
      apply Matrix.ext; unfold tripleCharges sourceA382 sourceB382 sourceC382 difference raw7384; decide +kernel
    rw [ha]
    exact (canonical7384 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA382 + difference 0 4) (sourceB382 + difference 4 0) sourceC382) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3899) := by
    have ha : (tripleCharges (sourceA382 + difference 0 4) (sourceB382 + difference 4 0) sourceC382) = raw7385 := by
      apply Matrix.ext; unfold tripleCharges sourceA382 sourceB382 sourceC382 difference raw7385; decide +kernel
    rw [ha]
    exact (canonical7385 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA382 + difference 0 5) (sourceB382 + difference 5 0) sourceC382) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3901) := by
    have ha : (tripleCharges (sourceA382 + difference 0 5) (sourceB382 + difference 5 0) sourceC382) = raw7386 := by
      apply Matrix.ext; unfold tripleCharges sourceA382 sourceB382 sourceC382 difference raw7386; decide +kernel
    rw [ha]
    exact (canonical7386 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA382 + sourceB382) sourceC382) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA382 + sourceB382) sourceC382) = raw7387 := by
      apply Matrix.ext; unfold doubleCharges sourceA382 sourceB382 sourceC382 raw7387; decide +kernel
    rw [ha]
    exact (canonical7387 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA382 sourceB382 sourceC382
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm382, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources12
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm384 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA384 + difference 1 0) (sourceB384 + difference 0 1) sourceC384) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1248) := by
    have ha : (tripleCharges (sourceA384 + difference 1 0) (sourceB384 + difference 0 1) sourceC384) = raw7388 := by
      apply Matrix.ext; unfold tripleCharges sourceA384 sourceB384 sourceC384 difference raw7388; decide +kernel
    rw [ha]
    exact (canonical7388 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA384 + difference 1 1) (sourceB384 + difference 1 1) sourceC384) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA384 + difference 1 1) (sourceB384 + difference 1 1) sourceC384) = raw7381 := by
      apply Matrix.ext; unfold tripleCharges sourceA384 sourceB384 sourceC384 difference raw7381; decide +kernel
    rw [ha]
    exact (canonical7381 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA384 + difference 1 2) (sourceB384 + difference 2 1) sourceC384) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2623) := by
    have ha : (tripleCharges (sourceA384 + difference 1 2) (sourceB384 + difference 2 1) sourceC384) = raw7393 := by
      apply Matrix.ext; unfold tripleCharges sourceA384 sourceB384 sourceC384 difference raw7393; decide +kernel
    rw [ha]
    exact (canonical7393 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA384 + difference 1 3) (sourceB384 + difference 3 1) sourceC384) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2623) := by
    have ha : (tripleCharges (sourceA384 + difference 1 3) (sourceB384 + difference 3 1) sourceC384) = raw7394 := by
      apply Matrix.ext; unfold tripleCharges sourceA384 sourceB384 sourceC384 difference raw7394; decide +kernel
    rw [ha]
    exact (canonical7394 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA384 + difference 1 4) (sourceB384 + difference 4 1) sourceC384) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2745) := by
    have ha : (tripleCharges (sourceA384 + difference 1 4) (sourceB384 + difference 4 1) sourceC384) = raw7395 := by
      apply Matrix.ext; unfold tripleCharges sourceA384 sourceB384 sourceC384 difference raw7395; decide +kernel
    rw [ha]
    exact (canonical7395 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA384 + difference 1 5) (sourceB384 + difference 5 1) sourceC384) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA384 + difference 1 5) (sourceB384 + difference 5 1) sourceC384) = raw7396 := by
      apply Matrix.ext; unfold tripleCharges sourceA384 sourceB384 sourceC384 difference raw7396; decide +kernel
    rw [ha]
    exact (canonical7396 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA384 + sourceB384) sourceC384) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA384 + sourceB384) sourceC384) = raw7387 := by
      apply Matrix.ext; unfold doubleCharges sourceA384 sourceB384 sourceC384 raw7387; decide +kernel
    rw [ha]
    exact (canonical7387 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA384 sourceB384 sourceC384
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm384, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq385 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm385 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA385 + difference 0 1) (sourceB385 + difference 1 0) sourceC385) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA385 + difference 0 1) (sourceB385 + difference 1 0) sourceC385) = raw7382 := by
      apply Matrix.ext; unfold tripleCharges sourceA385 sourceB385 sourceC385 difference raw7382; decide +kernel
    rw [ha]
    exact (canonical7382 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA385 + difference 1 1) (sourceB385 + difference 1 1) sourceC385) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA385 + difference 1 1) (sourceB385 + difference 1 1) sourceC385) = raw7381 := by
      apply Matrix.ext; unfold tripleCharges sourceA385 sourceB385 sourceC385 difference raw7381; decide +kernel
    rw [ha]
    exact (canonical7381 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA385 + difference 2 1) (sourceB385 + difference 1 2) sourceC385) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA385 + difference 2 1) (sourceB385 + difference 1 2) sourceC385) = raw7397 := by
      apply Matrix.ext; unfold tripleCharges sourceA385 sourceB385 sourceC385 difference raw7397; decide +kernel
    rw [ha]
    exact (canonical7397 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA385 + difference 3 1) (sourceB385 + difference 1 3) sourceC385) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA385 + difference 3 1) (sourceB385 + difference 1 3) sourceC385) = raw7398 := by
      apply Matrix.ext; unfold tripleCharges sourceA385 sourceB385 sourceC385 difference raw7398; decide +kernel
    rw [ha]
    exact (canonical7398 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA385 + difference 4 1) (sourceB385 + difference 1 4) sourceC385) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2473) := by
    have ha : (tripleCharges (sourceA385 + difference 4 1) (sourceB385 + difference 1 4) sourceC385) = raw7399 := by
      apply Matrix.ext; unfold tripleCharges sourceA385 sourceB385 sourceC385 difference raw7399; decide +kernel
    rw [ha]
    exact (canonical7399 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA385 + difference 5 1) (sourceB385 + difference 1 5) sourceC385) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA385 + difference 5 1) (sourceB385 + difference 1 5) sourceC385) = raw7400 := by
      apply Matrix.ext; unfold tripleCharges sourceA385 sourceB385 sourceC385 difference raw7400; decide +kernel
    rw [ha]
    exact (canonical7400 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA385 + sourceB385) sourceC385) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA385 + sourceB385) sourceC385) = raw7387 := by
      apply Matrix.ext; unfold doubleCharges sourceA385 sourceB385 sourceC385 raw7387; decide +kernel
    rw [ha]
    exact (canonical7387 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA385 sourceB385 sourceC385
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm385, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq386 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm386 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA386 + difference 2 0) (sourceB386 + difference 0 2) sourceC386) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA386 + difference 2 0) (sourceB386 + difference 0 2) sourceC386) = raw7389 := by
      apply Matrix.ext; unfold tripleCharges sourceA386 sourceB386 sourceC386 difference raw7389; decide +kernel
    rw [ha]
    exact (canonical7389 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA386 + difference 2 1) (sourceB386 + difference 1 2) sourceC386) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA386 + difference 2 1) (sourceB386 + difference 1 2) sourceC386) = raw7397 := by
      apply Matrix.ext; unfold tripleCharges sourceA386 sourceB386 sourceC386 difference raw7397; decide +kernel
    rw [ha]
    exact (canonical7397 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA386 + difference 2 2) (sourceB386 + difference 2 2) sourceC386) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA386 + difference 2 2) (sourceB386 + difference 2 2) sourceC386) = raw7381 := by
      apply Matrix.ext; unfold tripleCharges sourceA386 sourceB386 sourceC386 difference raw7381; decide +kernel
    rw [ha]
    exact (canonical7381 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA386 + difference 2 3) (sourceB386 + difference 3 2) sourceC386) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2617) := by
    have ha : (tripleCharges (sourceA386 + difference 2 3) (sourceB386 + difference 3 2) sourceC386) = raw7401 := by
      apply Matrix.ext; unfold tripleCharges sourceA386 sourceB386 sourceC386 difference raw7401; decide +kernel
    rw [ha]
    exact (canonical7401 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA386 + difference 2 4) (sourceB386 + difference 4 2) sourceC386) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA386 + difference 2 4) (sourceB386 + difference 4 2) sourceC386) = raw7402 := by
      apply Matrix.ext; unfold tripleCharges sourceA386 sourceB386 sourceC386 difference raw7402; decide +kernel
    rw [ha]
    exact (canonical7402 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA386 + difference 2 5) (sourceB386 + difference 5 2) sourceC386) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA386 + difference 2 5) (sourceB386 + difference 5 2) sourceC386) = raw7403 := by
      apply Matrix.ext; unfold tripleCharges sourceA386 sourceB386 sourceC386 difference raw7403; decide +kernel
    rw [ha]
    exact (canonical7403 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA386 + sourceB386) sourceC386) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA386 + sourceB386) sourceC386) = raw7387 := by
      apply Matrix.ext; unfold doubleCharges sourceA386 sourceB386 sourceC386 raw7387; decide +kernel
    rw [ha]
    exact (canonical7387 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA386 sourceB386 sourceC386
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm386, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq387 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm387 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA387 + difference 0 2) (sourceB387 + difference 2 0) sourceC387) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA387 + difference 0 2) (sourceB387 + difference 2 0) sourceC387) = raw7383 := by
      apply Matrix.ext; unfold tripleCharges sourceA387 sourceB387 sourceC387 difference raw7383; decide +kernel
    rw [ha]
    exact (canonical7383 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA387 + difference 1 2) (sourceB387 + difference 2 1) sourceC387) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2623) := by
    have ha : (tripleCharges (sourceA387 + difference 1 2) (sourceB387 + difference 2 1) sourceC387) = raw7393 := by
      apply Matrix.ext; unfold tripleCharges sourceA387 sourceB387 sourceC387 difference raw7393; decide +kernel
    rw [ha]
    exact (canonical7393 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA387 + difference 2 2) (sourceB387 + difference 2 2) sourceC387) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA387 + difference 2 2) (sourceB387 + difference 2 2) sourceC387) = raw7381 := by
      apply Matrix.ext; unfold tripleCharges sourceA387 sourceB387 sourceC387 difference raw7381; decide +kernel
    rw [ha]
    exact (canonical7381 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA387 + difference 3 2) (sourceB387 + difference 2 3) sourceC387) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2617) := by
    have ha : (tripleCharges (sourceA387 + difference 3 2) (sourceB387 + difference 2 3) sourceC387) = raw7404 := by
      apply Matrix.ext; unfold tripleCharges sourceA387 sourceB387 sourceC387 difference raw7404; decide +kernel
    rw [ha]
    exact (canonical7404 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA387 + difference 4 2) (sourceB387 + difference 2 4) sourceC387) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2612) := by
    have ha : (tripleCharges (sourceA387 + difference 4 2) (sourceB387 + difference 2 4) sourceC387) = raw7405 := by
      apply Matrix.ext; unfold tripleCharges sourceA387 sourceB387 sourceC387 difference raw7405; decide +kernel
    rw [ha]
    exact (canonical7405 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA387 + difference 5 2) (sourceB387 + difference 2 5) sourceC387) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2611) := by
    have ha : (tripleCharges (sourceA387 + difference 5 2) (sourceB387 + difference 2 5) sourceC387) = raw7406 := by
      apply Matrix.ext; unfold tripleCharges sourceA387 sourceB387 sourceC387 difference raw7406; decide +kernel
    rw [ha]
    exact (canonical7406 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA387 + sourceB387) sourceC387) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA387 + sourceB387) sourceC387) = raw7387 := by
      apply Matrix.ext; unfold doubleCharges sourceA387 sourceB387 sourceC387 raw7387; decide +kernel
    rw [ha]
    exact (canonical7387 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA387 sourceB387 sourceC387
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm387, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq388 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm388 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA388 + difference 0 4) (sourceB388 + difference 4 0) sourceC388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3899) := by
    have ha : (tripleCharges (sourceA388 + difference 0 4) (sourceB388 + difference 4 0) sourceC388) = raw7385 := by
      apply Matrix.ext; unfold tripleCharges sourceA388 sourceB388 sourceC388 difference raw7385; decide +kernel
    rw [ha]
    exact (canonical7385 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA388 + difference 1 4) (sourceB388 + difference 4 1) sourceC388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2745) := by
    have ha : (tripleCharges (sourceA388 + difference 1 4) (sourceB388 + difference 4 1) sourceC388) = raw7395 := by
      apply Matrix.ext; unfold tripleCharges sourceA388 sourceB388 sourceC388 difference raw7395; decide +kernel
    rw [ha]
    exact (canonical7395 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA388 + difference 2 4) (sourceB388 + difference 4 2) sourceC388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA388 + difference 2 4) (sourceB388 + difference 4 2) sourceC388) = raw7402 := by
      apply Matrix.ext; unfold tripleCharges sourceA388 sourceB388 sourceC388 difference raw7402; decide +kernel
    rw [ha]
    exact (canonical7402 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA388 + difference 3 4) (sourceB388 + difference 4 3) sourceC388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA388 + difference 3 4) (sourceB388 + difference 4 3) sourceC388) = raw7407 := by
      apply Matrix.ext; unfold tripleCharges sourceA388 sourceB388 sourceC388 difference raw7407; decide +kernel
    rw [ha]
    exact (canonical7407 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA388 + difference 4 4) (sourceB388 + difference 4 4) sourceC388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA388 + difference 4 4) (sourceB388 + difference 4 4) sourceC388) = raw7381 := by
      apply Matrix.ext; unfold tripleCharges sourceA388 sourceB388 sourceC388 difference raw7381; decide +kernel
    rw [ha]
    exact (canonical7381 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA388 + difference 5 4) (sourceB388 + difference 4 5) sourceC388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2707) := by
    have ha : (tripleCharges (sourceA388 + difference 5 4) (sourceB388 + difference 4 5) sourceC388) = raw7408 := by
      apply Matrix.ext; unfold tripleCharges sourceA388 sourceB388 sourceC388 difference raw7408; decide +kernel
    rw [ha]
    exact (canonical7408 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA388 + sourceB388) sourceC388) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA388 + sourceB388) sourceC388) = raw7387 := by
      apply Matrix.ext; unfold doubleCharges sourceA388 sourceB388 sourceC388 raw7387; decide +kernel
    rw [ha]
    exact (canonical7387 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA388 sourceB388 sourceC388
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm388, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq391 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm391 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA391 + difference 0 1) (sourceB391 + difference 1 0) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA391 + difference 0 1) (sourceB391 + difference 1 0) sourceC391) = raw7469 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7469; decide +kernel
    rw [ha]
    exact (canonical7469 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA391 + difference 0 2) (sourceB391 + difference 2 0) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA391 + difference 0 2) (sourceB391 + difference 2 0) sourceC391) = raw7470 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7470; decide +kernel
    rw [ha]
    exact (canonical7470 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA391 + difference 0 3) (sourceB391 + difference 3 0) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA391 + difference 0 3) (sourceB391 + difference 3 0) sourceC391) = raw7471 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7471; decide +kernel
    rw [ha]
    exact (canonical7471 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA391 + difference 0 4) (sourceB391 + difference 4 0) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3858) := by
    have ha : (tripleCharges (sourceA391 + difference 0 4) (sourceB391 + difference 4 0) sourceC391) = raw7472 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7472; decide +kernel
    rw [ha]
    exact (canonical7472 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA391 + difference 0 5) (sourceB391 + difference 5 0) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3991) := by
    have ha : (tripleCharges (sourceA391 + difference 0 5) (sourceB391 + difference 5 0) sourceC391) = raw7473 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7473; decide +kernel
    rw [ha]
    exact (canonical7473 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA391 + difference 1 0) (sourceB391 + difference 0 1) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA391 + difference 1 0) (sourceB391 + difference 0 1) sourceC391) = raw7474 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7474; decide +kernel
    rw [ha]
    exact (canonical7474 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA391 + difference 1 2) (sourceB391 + difference 2 1) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA391 + difference 1 2) (sourceB391 + difference 2 1) sourceC391) = raw7475 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7475; decide +kernel
    rw [ha]
    exact (canonical7475 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA391 + difference 1 3) (sourceB391 + difference 3 1) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA391 + difference 1 3) (sourceB391 + difference 3 1) sourceC391) = raw7476 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7476; decide +kernel
    rw [ha]
    exact (canonical7476 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA391 + difference 1 4) (sourceB391 + difference 4 1) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA391 + difference 1 4) (sourceB391 + difference 4 1) sourceC391) = raw7477 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7477; decide +kernel
    rw [ha]
    exact (canonical7477 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA391 + difference 1 5) (sourceB391 + difference 5 1) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA391 + difference 1 5) (sourceB391 + difference 5 1) sourceC391) = raw7478 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7478; decide +kernel
    rw [ha]
    exact (canonical7478 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA391 + difference 2 0) (sourceB391 + difference 0 2) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1607) := by
    have ha : (tripleCharges (sourceA391 + difference 2 0) (sourceB391 + difference 0 2) sourceC391) = raw7479 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7479; decide +kernel
    rw [ha]
    exact (canonical7479 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA391 + difference 2 1) (sourceB391 + difference 1 2) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3346) := by
    have ha : (tripleCharges (sourceA391 + difference 2 1) (sourceB391 + difference 1 2) sourceC391) = raw7480 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7480; decide +kernel
    rw [ha]
    exact (canonical7480 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA391 + difference 2 3) (sourceB391 + difference 3 2) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA391 + difference 2 3) (sourceB391 + difference 3 2) sourceC391) = raw7481 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7481; decide +kernel
    rw [ha]
    exact (canonical7481 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA391 + difference 2 4) (sourceB391 + difference 4 2) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA391 + difference 2 4) (sourceB391 + difference 4 2) sourceC391) = raw7482 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7482; decide +kernel
    rw [ha]
    exact (canonical7482 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA391 + difference 2 5) (sourceB391 + difference 5 2) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA391 + difference 2 5) (sourceB391 + difference 5 2) sourceC391) = raw7483 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7483; decide +kernel
    rw [ha]
    exact (canonical7483 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA391 + difference 3 0) (sourceB391 + difference 0 3) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1607) := by
    have ha : (tripleCharges (sourceA391 + difference 3 0) (sourceB391 + difference 0 3) sourceC391) = raw7484 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7484; decide +kernel
    rw [ha]
    exact (canonical7484 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA391 + difference 3 1) (sourceB391 + difference 1 3) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3346) := by
    have ha : (tripleCharges (sourceA391 + difference 3 1) (sourceB391 + difference 1 3) sourceC391) = raw7485 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7485; decide +kernel
    rw [ha]
    exact (canonical7485 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA391 + difference 3 2) (sourceB391 + difference 2 3) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA391 + difference 3 2) (sourceB391 + difference 2 3) sourceC391) = raw7486 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7486; decide +kernel
    rw [ha]
    exact (canonical7486 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA391 + difference 3 4) (sourceB391 + difference 4 3) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA391 + difference 3 4) (sourceB391 + difference 4 3) sourceC391) = raw7487 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7487; decide +kernel
    rw [ha]
    exact (canonical7487 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA391 + difference 3 5) (sourceB391 + difference 5 3) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA391 + difference 3 5) (sourceB391 + difference 5 3) sourceC391) = raw7488 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7488; decide +kernel
    rw [ha]
    exact (canonical7488 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA391 + difference 4 0) (sourceB391 + difference 0 4) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1606) := by
    have ha : (tripleCharges (sourceA391 + difference 4 0) (sourceB391 + difference 0 4) sourceC391) = raw7489 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7489; decide +kernel
    rw [ha]
    exact (canonical7489 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA391 + difference 4 1) (sourceB391 + difference 1 4) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3345) := by
    have ha : (tripleCharges (sourceA391 + difference 4 1) (sourceB391 + difference 1 4) sourceC391) = raw7490 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7490; decide +kernel
    rw [ha]
    exact (canonical7490 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA391 + difference 4 2) (sourceB391 + difference 2 4) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA391 + difference 4 2) (sourceB391 + difference 2 4) sourceC391) = raw7491 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7491; decide +kernel
    rw [ha]
    exact (canonical7491 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA391 + difference 4 3) (sourceB391 + difference 3 4) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA391 + difference 4 3) (sourceB391 + difference 3 4) sourceC391) = raw7492 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7492; decide +kernel
    rw [ha]
    exact (canonical7492 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA391 + difference 4 5) (sourceB391 + difference 5 4) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3502) := by
    have ha : (tripleCharges (sourceA391 + difference 4 5) (sourceB391 + difference 5 4) sourceC391) = raw7493 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7493; decide +kernel
    rw [ha]
    exact (canonical7493 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA391 + difference 5 0) (sourceB391 + difference 0 5) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1613) := by
    have ha : (tripleCharges (sourceA391 + difference 5 0) (sourceB391 + difference 0 5) sourceC391) = raw7494 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7494; decide +kernel
    rw [ha]
    exact (canonical7494 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA391 + difference 5 1) (sourceB391 + difference 1 5) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3350) := by
    have ha : (tripleCharges (sourceA391 + difference 5 1) (sourceB391 + difference 1 5) sourceC391) = raw7495 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7495; decide +kernel
    rw [ha]
    exact (canonical7495 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA391 + difference 5 2) (sourceB391 + difference 2 5) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA391 + difference 5 2) (sourceB391 + difference 2 5) sourceC391) = raw7496 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7496; decide +kernel
    rw [ha]
    exact (canonical7496 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA391 + difference 5 3) (sourceB391 + difference 3 5) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA391 + difference 5 3) (sourceB391 + difference 3 5) sourceC391) = raw7497 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7497; decide +kernel
    rw [ha]
    exact (canonical7497 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA391 + difference 5 4) (sourceB391 + difference 4 5) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA391 + difference 5 4) (sourceB391 + difference 4 5) sourceC391) = raw7498 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7498; decide +kernel
    rw [ha]
    exact (canonical7498 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA391 sourceB391 sourceC391
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm391, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq392 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm392 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA392 + difference 0 0) (sourceB392 + difference 0 0) sourceC392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA392 + difference 0 0) (sourceB392 + difference 0 0) sourceC392) = raw7499 := by
      apply Matrix.ext; unfold tripleCharges sourceA392 sourceB392 sourceC392 difference raw7499; decide +kernel
    rw [ha]
    exact (canonical7499 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA392 + difference 0 1) (sourceB392 + difference 1 0) sourceC392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA392 + difference 0 1) (sourceB392 + difference 1 0) sourceC392) = raw7500 := by
      apply Matrix.ext; unfold tripleCharges sourceA392 sourceB392 sourceC392 difference raw7500; decide +kernel
    rw [ha]
    exact (canonical7500 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA392 + difference 0 2) (sourceB392 + difference 2 0) sourceC392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA392 + difference 0 2) (sourceB392 + difference 2 0) sourceC392) = raw7501 := by
      apply Matrix.ext; unfold tripleCharges sourceA392 sourceB392 sourceC392 difference raw7501; decide +kernel
    rw [ha]
    exact (canonical7501 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA392 + difference 0 3) (sourceB392 + difference 3 0) sourceC392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA392 + difference 0 3) (sourceB392 + difference 3 0) sourceC392) = raw7502 := by
      apply Matrix.ext; unfold tripleCharges sourceA392 sourceB392 sourceC392 difference raw7502; decide +kernel
    rw [ha]
    exact (canonical7502 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA392 + difference 0 4) (sourceB392 + difference 4 0) sourceC392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA392 + difference 0 4) (sourceB392 + difference 4 0) sourceC392) = raw7503 := by
      apply Matrix.ext; unfold tripleCharges sourceA392 sourceB392 sourceC392 difference raw7503; decide +kernel
    rw [ha]
    exact (canonical7503 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA392 + difference 0 5) (sourceB392 + difference 5 0) sourceC392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4008) := by
    have ha : (tripleCharges (sourceA392 + difference 0 5) (sourceB392 + difference 5 0) sourceC392) = raw7504 := by
      apply Matrix.ext; unfold tripleCharges sourceA392 sourceB392 sourceC392 difference raw7504; decide +kernel
    rw [ha]
    exact (canonical7504 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA392 + sourceB392) sourceC392) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA392 + sourceB392) sourceC392) = raw7505 := by
      apply Matrix.ext; unfold doubleCharges sourceA392 sourceB392 sourceC392 raw7505; decide +kernel
    rw [ha]
    exact (canonical7505 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA392 sourceB392 sourceC392
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm392, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm393 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA393 + difference 0 0) (sourceB393 + difference 0 0) sourceC393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA393 + difference 0 0) (sourceB393 + difference 0 0) sourceC393) = raw7499 := by
      apply Matrix.ext; unfold tripleCharges sourceA393 sourceB393 sourceC393 difference raw7499; decide +kernel
    rw [ha]
    exact (canonical7499 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA393 + difference 1 0) (sourceB393 + difference 0 1) sourceC393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1383) := by
    have ha : (tripleCharges (sourceA393 + difference 1 0) (sourceB393 + difference 0 1) sourceC393) = raw7506 := by
      apply Matrix.ext; unfold tripleCharges sourceA393 sourceB393 sourceC393 difference raw7506; decide +kernel
    rw [ha]
    exact (canonical7506 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA393 + difference 2 0) (sourceB393 + difference 0 2) sourceC393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1392) := by
    have ha : (tripleCharges (sourceA393 + difference 2 0) (sourceB393 + difference 0 2) sourceC393) = raw7507 := by
      apply Matrix.ext; unfold tripleCharges sourceA393 sourceB393 sourceC393 difference raw7507; decide +kernel
    rw [ha]
    exact (canonical7507 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA393 + difference 3 0) (sourceB393 + difference 0 3) sourceC393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1392) := by
    have ha : (tripleCharges (sourceA393 + difference 3 0) (sourceB393 + difference 0 3) sourceC393) = raw7508 := by
      apply Matrix.ext; unfold tripleCharges sourceA393 sourceB393 sourceC393 difference raw7508; decide +kernel
    rw [ha]
    exact (canonical7508 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA393 + difference 4 0) (sourceB393 + difference 0 4) sourceC393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1380) := by
    have ha : (tripleCharges (sourceA393 + difference 4 0) (sourceB393 + difference 0 4) sourceC393) = raw7509 := by
      apply Matrix.ext; unfold tripleCharges sourceA393 sourceB393 sourceC393 difference raw7509; decide +kernel
    rw [ha]
    exact (canonical7509 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA393 + difference 5 0) (sourceB393 + difference 0 5) sourceC393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1378) := by
    have ha : (tripleCharges (sourceA393 + difference 5 0) (sourceB393 + difference 0 5) sourceC393) = raw7510 := by
      apply Matrix.ext; unfold tripleCharges sourceA393 sourceB393 sourceC393 difference raw7510; decide +kernel
    rw [ha]
    exact (canonical7510 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA393 + sourceB393) sourceC393) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA393 + sourceB393) sourceC393) = raw7505 := by
      apply Matrix.ext; unfold doubleCharges sourceA393 sourceB393 sourceC393 raw7505; decide +kernel
    rw [ha]
    exact (canonical7505 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA393 sourceB393 sourceC393
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm393, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq394 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm394 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA394 + difference 1 0) (sourceB394 + difference 0 1) sourceC394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1383) := by
    have ha : (tripleCharges (sourceA394 + difference 1 0) (sourceB394 + difference 0 1) sourceC394) = raw7506 := by
      apply Matrix.ext; unfold tripleCharges sourceA394 sourceB394 sourceC394 difference raw7506; decide +kernel
    rw [ha]
    exact (canonical7506 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA394 + difference 1 1) (sourceB394 + difference 1 1) sourceC394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA394 + difference 1 1) (sourceB394 + difference 1 1) sourceC394) = raw7499 := by
      apply Matrix.ext; unfold tripleCharges sourceA394 sourceB394 sourceC394 difference raw7499; decide +kernel
    rw [ha]
    exact (canonical7499 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA394 + difference 1 2) (sourceB394 + difference 2 1) sourceC394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA394 + difference 1 2) (sourceB394 + difference 2 1) sourceC394) = raw7511 := by
      apply Matrix.ext; unfold tripleCharges sourceA394 sourceB394 sourceC394 difference raw7511; decide +kernel
    rw [ha]
    exact (canonical7511 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA394 + difference 1 3) (sourceB394 + difference 3 1) sourceC394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA394 + difference 1 3) (sourceB394 + difference 3 1) sourceC394) = raw7512 := by
      apply Matrix.ext; unfold tripleCharges sourceA394 sourceB394 sourceC394 difference raw7512; decide +kernel
    rw [ha]
    exact (canonical7512 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA394 + difference 1 4) (sourceB394 + difference 4 1) sourceC394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA394 + difference 1 4) (sourceB394 + difference 4 1) sourceC394) = raw7513 := by
      apply Matrix.ext; unfold tripleCharges sourceA394 sourceB394 sourceC394 difference raw7513; decide +kernel
    rw [ha]
    exact (canonical7513 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA394 + difference 1 5) (sourceB394 + difference 5 1) sourceC394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA394 + difference 1 5) (sourceB394 + difference 5 1) sourceC394) = raw7514 := by
      apply Matrix.ext; unfold tripleCharges sourceA394 sourceB394 sourceC394 difference raw7514; decide +kernel
    rw [ha]
    exact (canonical7514 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA394 + sourceB394) sourceC394) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA394 + sourceB394) sourceC394) = raw7505 := by
      apply Matrix.ext; unfold doubleCharges sourceA394 sourceB394 sourceC394 raw7505; decide +kernel
    rw [ha]
    exact (canonical7505 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA394 sourceB394 sourceC394
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm394, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm395 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA395 + difference 0 1) (sourceB395 + difference 1 0) sourceC395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA395 + difference 0 1) (sourceB395 + difference 1 0) sourceC395) = raw7500 := by
      apply Matrix.ext; unfold tripleCharges sourceA395 sourceB395 sourceC395 difference raw7500; decide +kernel
    rw [ha]
    exact (canonical7500 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA395 + difference 1 1) (sourceB395 + difference 1 1) sourceC395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA395 + difference 1 1) (sourceB395 + difference 1 1) sourceC395) = raw7499 := by
      apply Matrix.ext; unfold tripleCharges sourceA395 sourceB395 sourceC395 difference raw7499; decide +kernel
    rw [ha]
    exact (canonical7499 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA395 + difference 2 1) (sourceB395 + difference 1 2) sourceC395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3013) := by
    have ha : (tripleCharges (sourceA395 + difference 2 1) (sourceB395 + difference 1 2) sourceC395) = raw7515 := by
      apply Matrix.ext; unfold tripleCharges sourceA395 sourceB395 sourceC395 difference raw7515; decide +kernel
    rw [ha]
    exact (canonical7515 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA395 + difference 3 1) (sourceB395 + difference 1 3) sourceC395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3013) := by
    have ha : (tripleCharges (sourceA395 + difference 3 1) (sourceB395 + difference 1 3) sourceC395) = raw7516 := by
      apply Matrix.ext; unfold tripleCharges sourceA395 sourceB395 sourceC395 difference raw7516; decide +kernel
    rw [ha]
    exact (canonical7516 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA395 + difference 4 1) (sourceB395 + difference 1 4) sourceC395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3012) := by
    have ha : (tripleCharges (sourceA395 + difference 4 1) (sourceB395 + difference 1 4) sourceC395) = raw7517 := by
      apply Matrix.ext; unfold tripleCharges sourceA395 sourceB395 sourceC395 difference raw7517; decide +kernel
    rw [ha]
    exact (canonical7517 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA395 + difference 5 1) (sourceB395 + difference 1 5) sourceC395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2562) := by
    have ha : (tripleCharges (sourceA395 + difference 5 1) (sourceB395 + difference 1 5) sourceC395) = raw7518 := by
      apply Matrix.ext; unfold tripleCharges sourceA395 sourceB395 sourceC395 difference raw7518; decide +kernel
    rw [ha]
    exact (canonical7518 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA395 + sourceB395) sourceC395) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA395 + sourceB395) sourceC395) = raw7505 := by
      apply Matrix.ext; unfold doubleCharges sourceA395 sourceB395 sourceC395 raw7505; decide +kernel
    rw [ha]
    exact (canonical7505 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA395 sourceB395 sourceC395
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm395, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq396 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm396 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA396 + difference 0 2) (sourceB396 + difference 2 0) sourceC396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA396 + difference 0 2) (sourceB396 + difference 2 0) sourceC396) = raw7501 := by
      apply Matrix.ext; unfold tripleCharges sourceA396 sourceB396 sourceC396 difference raw7501; decide +kernel
    rw [ha]
    exact (canonical7501 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA396 + difference 1 2) (sourceB396 + difference 2 1) sourceC396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA396 + difference 1 2) (sourceB396 + difference 2 1) sourceC396) = raw7511 := by
      apply Matrix.ext; unfold tripleCharges sourceA396 sourceB396 sourceC396 difference raw7511; decide +kernel
    rw [ha]
    exact (canonical7511 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA396 + difference 2 2) (sourceB396 + difference 2 2) sourceC396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA396 + difference 2 2) (sourceB396 + difference 2 2) sourceC396) = raw7499 := by
      apply Matrix.ext; unfold tripleCharges sourceA396 sourceB396 sourceC396 difference raw7499; decide +kernel
    rw [ha]
    exact (canonical7499 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA396 + difference 3 2) (sourceB396 + difference 2 3) sourceC396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2933) := by
    have ha : (tripleCharges (sourceA396 + difference 3 2) (sourceB396 + difference 2 3) sourceC396) = raw7519 := by
      apply Matrix.ext; unfold tripleCharges sourceA396 sourceB396 sourceC396 difference raw7519; decide +kernel
    rw [ha]
    exact (canonical7519 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA396 + difference 4 2) (sourceB396 + difference 2 4) sourceC396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA396 + difference 4 2) (sourceB396 + difference 2 4) sourceC396) = raw7520 := by
      apply Matrix.ext; unfold tripleCharges sourceA396 sourceB396 sourceC396 difference raw7520; decide +kernel
    rw [ha]
    exact (canonical7520 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA396 + difference 5 2) (sourceB396 + difference 2 5) sourceC396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA396 + difference 5 2) (sourceB396 + difference 2 5) sourceC396) = raw7521 := by
      apply Matrix.ext; unfold tripleCharges sourceA396 sourceB396 sourceC396 difference raw7521; decide +kernel
    rw [ha]
    exact (canonical7521 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA396 + sourceB396) sourceC396) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA396 + sourceB396) sourceC396) = raw7505 := by
      apply Matrix.ext; unfold doubleCharges sourceA396 sourceB396 sourceC396 raw7505; decide +kernel
    rw [ha]
    exact (canonical7505 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA396 sourceB396 sourceC396
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm396, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq397 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm397 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA397 + difference 4 0) (sourceB397 + difference 0 4) sourceC397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1380) := by
    have ha : (tripleCharges (sourceA397 + difference 4 0) (sourceB397 + difference 0 4) sourceC397) = raw7509 := by
      apply Matrix.ext; unfold tripleCharges sourceA397 sourceB397 sourceC397 difference raw7509; decide +kernel
    rw [ha]
    exact (canonical7509 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA397 + difference 4 1) (sourceB397 + difference 1 4) sourceC397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3012) := by
    have ha : (tripleCharges (sourceA397 + difference 4 1) (sourceB397 + difference 1 4) sourceC397) = raw7517 := by
      apply Matrix.ext; unfold tripleCharges sourceA397 sourceB397 sourceC397 difference raw7517; decide +kernel
    rw [ha]
    exact (canonical7517 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA397 + difference 4 2) (sourceB397 + difference 2 4) sourceC397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA397 + difference 4 2) (sourceB397 + difference 2 4) sourceC397) = raw7520 := by
      apply Matrix.ext; unfold tripleCharges sourceA397 sourceB397 sourceC397 difference raw7520; decide +kernel
    rw [ha]
    exact (canonical7520 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA397 + difference 4 3) (sourceB397 + difference 3 4) sourceC397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA397 + difference 4 3) (sourceB397 + difference 3 4) sourceC397) = raw7522 := by
      apply Matrix.ext; unfold tripleCharges sourceA397 sourceB397 sourceC397 difference raw7522; decide +kernel
    rw [ha]
    exact (canonical7522 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA397 + difference 4 4) (sourceB397 + difference 4 4) sourceC397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA397 + difference 4 4) (sourceB397 + difference 4 4) sourceC397) = raw7499 := by
      apply Matrix.ext; unfold tripleCharges sourceA397 sourceB397 sourceC397 difference raw7499; decide +kernel
    rw [ha]
    exact (canonical7499 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA397 + difference 4 5) (sourceB397 + difference 5 4) sourceC397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3066) := by
    have ha : (tripleCharges (sourceA397 + difference 4 5) (sourceB397 + difference 5 4) sourceC397) = raw7523 := by
      apply Matrix.ext; unfold tripleCharges sourceA397 sourceB397 sourceC397 difference raw7523; decide +kernel
    rw [ha]
    exact (canonical7523 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA397 + sourceB397) sourceC397) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA397 + sourceB397) sourceC397) = raw7505 := by
      apply Matrix.ext; unfold doubleCharges sourceA397 sourceB397 sourceC397 raw7505; decide +kernel
    rw [ha]
    exact (canonical7505 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA397 sourceB397 sourceC397
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm397, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck320 : Integer.Sparse.reindex keyMap MixedData.row320 = numericRow320 := by decide +kernel

theorem numericCheck320 (x : Master → ℝ) : Integer.Sparse.eval numericRow320 x =
    (1 : ℝ) * reducedSource320 x := by
  norm_num [numericRow320, reducedSource320, Integer.Sparse.eval, Sparse.eval, nodeValue2710, nodeValue3801, nodeValue3872, nodeValue3899, nodeValue3901, nodeValue4091]

theorem reindexCheck321 : Integer.Sparse.reindex keyMap MixedData.row321 = numericRow321 := by decide +kernel

theorem numericCheck321 (x : Master → ℝ) : Integer.Sparse.eval numericRow321 x =
    (1 : ℝ) * reducedSource321 x := by
  norm_num [numericRow321, reducedSource321, Integer.Sparse.eval, Sparse.eval, nodeValue1248, nodeValue2623, nodeValue2710, nodeValue2745, nodeValue2750, nodeValue4091]

theorem reindexCheck322 : Integer.Sparse.reindex keyMap MixedData.row322 = numericRow322 := by decide +kernel

theorem numericCheck322 (x : Master → ℝ) : Integer.Sparse.eval numericRow322 x =
    (1 : ℝ) * reducedSource322 x := by
  norm_num [numericRow322, reducedSource322, Integer.Sparse.eval, Sparse.eval, nodeValue2471, nodeValue2473, nodeValue2483, nodeValue2710, nodeValue3801, nodeValue4091]

theorem reindexCheck323 : Integer.Sparse.reindex keyMap MixedData.row323 = numericRow323 := by decide +kernel

theorem numericCheck323 (x : Master → ℝ) : Integer.Sparse.eval numericRow323 x =
    (1 : ℝ) * reducedSource323 x := by
  norm_num [numericRow323, reducedSource323, Integer.Sparse.eval, Sparse.eval, nodeValue1216, nodeValue2483, nodeValue2617, nodeValue2710, nodeValue2721, nodeValue4091]

theorem reindexCheck324 : Integer.Sparse.reindex keyMap MixedData.row324 = numericRow324 := by decide +kernel

theorem numericCheck324 (x : Master → ℝ) : Integer.Sparse.eval numericRow324 x =
    (1 : ℝ) * reducedSource324 x := by
  norm_num [numericRow324, reducedSource324, Integer.Sparse.eval, Sparse.eval, nodeValue2611, nodeValue2612, nodeValue2617, nodeValue2623, nodeValue2710, nodeValue3872, nodeValue4091]

theorem reindexCheck325 : Integer.Sparse.reindex keyMap MixedData.row325 = numericRow325 := by decide +kernel

theorem numericCheck325 (x : Master → ℝ) : Integer.Sparse.eval numericRow325 x =
    (1 : ℝ) * reducedSource325 x := by
  norm_num [numericRow325, reducedSource325, Integer.Sparse.eval, Sparse.eval, nodeValue2707, nodeValue2710, nodeValue2745, nodeValue3899, nodeValue4091]

theorem reindexCheck328 : Integer.Sparse.reindex keyMap MixedData.row328 = numericRow328 := by decide +kernel

theorem numericCheck328 (x : Master → ℝ) : Integer.Sparse.eval numericRow328 x =
    (4320 : ℝ) * reducedSource328 x := by
  norm_num [numericRow328, reducedSource328, Integer.Sparse.eval, Sparse.eval, nodeValue1606, nodeValue1607, nodeValue1613, nodeValue1713, nodeValue3345, nodeValue3346, nodeValue3350, nodeValue3502, nodeValue3503, nodeValue3516, nodeValue3517, nodeValue3519, nodeValue3540, nodeValue3543, nodeValue3571, nodeValue3605, nodeValue3625, nodeValue3843, nodeValue3858, nodeValue3874, nodeValue3991]
  ring

theorem reindexCheck329 : Integer.Sparse.reindex keyMap MixedData.row329 = numericRow329 := by decide +kernel

theorem numericCheck329 (x : Master → ℝ) : Integer.Sparse.eval numericRow329 x =
    (1 : ℝ) * reducedSource329 x := by
  norm_num [numericRow329, reducedSource329, Integer.Sparse.eval, Sparse.eval, nodeValue3064, nodeValue3838, nodeValue3846, nodeValue3902, nodeValue4008, nodeValue4091]

theorem reindexCheck330 : Integer.Sparse.reindex keyMap MixedData.row330 = numericRow330 := by decide +kernel

theorem numericCheck330 (x : Master → ℝ) : Integer.Sparse.eval numericRow330 x =
    (1 : ℝ) * reducedSource330 x := by
  norm_num [numericRow330, reducedSource330, Integer.Sparse.eval, Sparse.eval, nodeValue1378, nodeValue1380, nodeValue1383, nodeValue1392, nodeValue3064, nodeValue4091]

theorem reindexCheck331 : Integer.Sparse.reindex keyMap MixedData.row331 = numericRow331 := by decide +kernel

theorem numericCheck331 (x : Master → ℝ) : Integer.Sparse.eval numericRow331 x =
    (1 : ℝ) * reducedSource331 x := by
  norm_num [numericRow331, reducedSource331, Integer.Sparse.eval, Sparse.eval, nodeValue1383, nodeValue2924, nodeValue3064, nodeValue3074, nodeValue3077, nodeValue4091]

theorem reindexCheck332 : Integer.Sparse.reindex keyMap MixedData.row332 = numericRow332 := by decide +kernel

theorem numericCheck332 (x : Master → ℝ) : Integer.Sparse.eval numericRow332 x =
    (1 : ℝ) * reducedSource332 x := by
  norm_num [numericRow332, reducedSource332, Integer.Sparse.eval, Sparse.eval, nodeValue2562, nodeValue3012, nodeValue3013, nodeValue3064, nodeValue3846, nodeValue4091]

theorem reindexCheck333 : Integer.Sparse.reindex keyMap MixedData.row333 = numericRow333 := by decide +kernel

theorem numericCheck333 (x : Master → ℝ) : Integer.Sparse.eval numericRow333 x =
    (1 : ℝ) * reducedSource333 x := by
  norm_num [numericRow333, reducedSource333, Integer.Sparse.eval, Sparse.eval, nodeValue2543, nodeValue2916, nodeValue2924, nodeValue2933, nodeValue3064, nodeValue3838, nodeValue4091]

theorem reindexCheck334 : Integer.Sparse.reindex keyMap MixedData.row334 = numericRow334 := by decide +kernel

theorem numericCheck334 (x : Master → ℝ) : Integer.Sparse.eval numericRow334 x =
    (1 : ℝ) * reducedSource334 x := by
  norm_num [numericRow334, reducedSource334, Integer.Sparse.eval, Sparse.eval, nodeValue1380, nodeValue2916, nodeValue3012, nodeValue3064, nodeValue3066, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero320 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource320 (mixedVector B) = 0 := by
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3899 : mixedVector B (Sum.inr 3899) = Sparse.eval nodeValue3899 (mixedVector B) := by
    change mixedMoment B node3899 node3899Labels = _
    exact sound3899 B hB hF
  have h3901 : mixedVector B (Sum.inr 3901) = Sparse.eval nodeValue3901 (mixedVector B) := by
    change mixedMoment B node3901 node3901Labels = _
    exact sound3901 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm382, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2710, h3801, h3872, h3899, h3901, h4091, reducedSource320] using sourceEq382 B hB

theorem rowSound320 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row320 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck320, numericCheck320, reducedZero320 B hB hF, mul_zero]

theorem reducedZero321 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource321 (mixedVector B) = 0 := by
  have h1248 : mixedVector B (Sum.inr 1248) = Sparse.eval nodeValue1248 (mixedVector B) := by
    change mixedMoment B node1248 node1248Labels = _
    exact sound1248 B hB hF
  have h2623 : mixedVector B (Sum.inr 2623) = Sparse.eval nodeValue2623 (mixedVector B) := by
    change mixedMoment B node2623 node2623Labels = _
    exact sound2623 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h2745 : mixedVector B (Sum.inr 2745) = Sparse.eval nodeValue2745 (mixedVector B) := by
    change mixedMoment B node2745 node2745Labels = _
    exact sound2745 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm384, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1248, h2623, h2710, h2745, h2750, h4091, reducedSource321] using sourceEq384 B hB

theorem rowSound321 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row321 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck321, numericCheck321, reducedZero321 B hB hF, mul_zero]

theorem reducedZero322 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource322 (mixedVector B) = 0 := by
  have h2471 : mixedVector B (Sum.inr 2471) = Sparse.eval nodeValue2471 (mixedVector B) := by
    change mixedMoment B node2471 node2471Labels = _
    exact sound2471 B hB hF
  have h2473 : mixedVector B (Sum.inr 2473) = Sparse.eval nodeValue2473 (mixedVector B) := by
    change mixedMoment B node2473 node2473Labels = _
    exact sound2473 B hB hF
  have h2483 : mixedVector B (Sum.inr 2483) = Sparse.eval nodeValue2483 (mixedVector B) := by
    change mixedMoment B node2483 node2483Labels = _
    exact sound2483 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm385, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2471, h2473, h2483, h2710, h3801, h4091, reducedSource322] using sourceEq385 B hB

theorem rowSound322 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row322 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck322, numericCheck322, reducedZero322 B hB hF, mul_zero]

theorem reducedZero323 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource323 (mixedVector B) = 0 := by
  have h1216 : mixedVector B (Sum.inr 1216) = Sparse.eval nodeValue1216 (mixedVector B) := by
    change mixedMoment B node1216 node1216Labels = _
    exact sound1216 B hB hF
  have h2483 : mixedVector B (Sum.inr 2483) = Sparse.eval nodeValue2483 (mixedVector B) := by
    change mixedMoment B node2483 node2483Labels = _
    exact sound2483 B hB hF
  have h2617 : mixedVector B (Sum.inr 2617) = Sparse.eval nodeValue2617 (mixedVector B) := by
    change mixedMoment B node2617 node2617Labels = _
    exact sound2617 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm386, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1216, h2483, h2617, h2710, h2721, h4091, reducedSource323] using sourceEq386 B hB

theorem rowSound323 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row323 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck323, numericCheck323, reducedZero323 B hB hF, mul_zero]

theorem reducedZero324 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource324 (mixedVector B) = 0 := by
  have h2611 : mixedVector B (Sum.inr 2611) = Sparse.eval nodeValue2611 (mixedVector B) := by
    change mixedMoment B node2611 node2611Labels = _
    exact sound2611 B hB hF
  have h2612 : mixedVector B (Sum.inr 2612) = Sparse.eval nodeValue2612 (mixedVector B) := by
    change mixedMoment B node2612 node2612Labels = _
    exact sound2612 B hB hF
  have h2617 : mixedVector B (Sum.inr 2617) = Sparse.eval nodeValue2617 (mixedVector B) := by
    change mixedMoment B node2617 node2617Labels = _
    exact sound2617 B hB hF
  have h2623 : mixedVector B (Sum.inr 2623) = Sparse.eval nodeValue2623 (mixedVector B) := by
    change mixedMoment B node2623 node2623Labels = _
    exact sound2623 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm387, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2611, h2612, h2617, h2623, h2710, h3872, h4091, reducedSource324] using sourceEq387 B hB

theorem rowSound324 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row324 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck324, numericCheck324, reducedZero324 B hB hF, mul_zero]

theorem reducedZero325 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource325 (mixedVector B) = 0 := by
  have h2707 : mixedVector B (Sum.inr 2707) = Sparse.eval nodeValue2707 (mixedVector B) := by
    change mixedMoment B node2707 node2707Labels = _
    exact sound2707 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h2745 : mixedVector B (Sum.inr 2745) = Sparse.eval nodeValue2745 (mixedVector B) := by
    change mixedMoment B node2745 node2745Labels = _
    exact sound2745 B hB hF
  have h3899 : mixedVector B (Sum.inr 3899) = Sparse.eval nodeValue3899 (mixedVector B) := by
    change mixedMoment B node3899 node3899Labels = _
    exact sound3899 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm388, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2707, h2710, h2745, h3899, h4091, reducedSource325] using sourceEq388 B hB

theorem rowSound325 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row325 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck325, numericCheck325, reducedZero325 B hB hF, mul_zero]

theorem reducedZero328 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource328 (mixedVector B) = 0 := by
  have h1606 : mixedVector B (Sum.inr 1606) = Sparse.eval nodeValue1606 (mixedVector B) := by
    change mixedMoment B node1606 node1606Labels = _
    exact sound1606 B hB hF
  have h1607 : mixedVector B (Sum.inr 1607) = Sparse.eval nodeValue1607 (mixedVector B) := by
    change mixedMoment B node1607 node1607Labels = _
    exact sound1607 B hB hF
  have h1613 : mixedVector B (Sum.inr 1613) = Sparse.eval nodeValue1613 (mixedVector B) := by
    change mixedMoment B node1613 node1613Labels = _
    exact sound1613 B hB hF
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h3345 : mixedVector B (Sum.inr 3345) = Sparse.eval nodeValue3345 (mixedVector B) := by
    change mixedMoment B node3345 node3345Labels = _
    exact sound3345 B hB hF
  have h3346 : mixedVector B (Sum.inr 3346) = Sparse.eval nodeValue3346 (mixedVector B) := by
    change mixedMoment B node3346 node3346Labels = _
    exact sound3346 B hB hF
  have h3350 : mixedVector B (Sum.inr 3350) = Sparse.eval nodeValue3350 (mixedVector B) := by
    change mixedMoment B node3350 node3350Labels = _
    exact sound3350 B hB hF
  have h3502 : mixedVector B (Sum.inr 3502) = Sparse.eval nodeValue3502 (mixedVector B) := by
    change mixedMoment B node3502 node3502Labels = _
    exact sound3502 B hB hF
  have h3503 : mixedVector B (Sum.inr 3503) = Sparse.eval nodeValue3503 (mixedVector B) := by
    change mixedMoment B node3503 node3503Labels = _
    exact sound3503 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3517 : mixedVector B (Sum.inr 3517) = Sparse.eval nodeValue3517 (mixedVector B) := by
    change mixedMoment B node3517 node3517Labels = _
    exact sound3517 B hB hF
  have h3519 : mixedVector B (Sum.inr 3519) = Sparse.eval nodeValue3519 (mixedVector B) := by
    change mixedMoment B node3519 node3519Labels = _
    exact sound3519 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3543 : mixedVector B (Sum.inr 3543) = Sparse.eval nodeValue3543 (mixedVector B) := by
    change mixedMoment B node3543 node3543Labels = _
    exact sound3543 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h3605 : mixedVector B (Sum.inr 3605) = Sparse.eval nodeValue3605 (mixedVector B) := by
    change mixedMoment B node3605 node3605Labels = _
    exact sound3605 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h3843 : mixedVector B (Sum.inr 3843) = Sparse.eval nodeValue3843 (mixedVector B) := by
    change mixedMoment B node3843 node3843Labels = _
    exact sound3843 B hB hF
  have h3858 : mixedVector B (Sum.inr 3858) = Sparse.eval nodeValue3858 (mixedVector B) := by
    change mixedMoment B node3858 node3858Labels = _
    exact sound3858 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h3991 : mixedVector B (Sum.inr 3991) = Sparse.eval nodeValue3991 (mixedVector B) := by
    change mixedMoment B node3991 node3991Labels = _
    exact sound3991 B hB hF
  simpa only [sourceForm391, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1606, h1607, h1613, h1713, h3345, h3346, h3350, h3502, h3503, h3516, h3517, h3519, h3540, h3543, h3571, h3605, h3625, h3843, h3858, h3874, h3991, reducedSource328] using sourceEq391 B hB

theorem rowSound328 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row328 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck328, numericCheck328, reducedZero328 B hB hF, mul_zero]

theorem reducedZero329 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource329 (mixedVector B) = 0 := by
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3902 : mixedVector B (Sum.inr 3902) = Sparse.eval nodeValue3902 (mixedVector B) := by
    change mixedMoment B node3902 node3902Labels = _
    exact sound3902 B hB hF
  have h4008 : mixedVector B (Sum.inr 4008) = Sparse.eval nodeValue4008 (mixedVector B) := by
    change mixedMoment B node4008 node4008Labels = _
    exact sound4008 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm392, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3064, h3838, h3846, h3902, h4008, h4091, reducedSource329] using sourceEq392 B hB

theorem rowSound329 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row329 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck329, numericCheck329, reducedZero329 B hB hF, mul_zero]

theorem reducedZero330 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource330 (mixedVector B) = 0 := by
  have h1378 : mixedVector B (Sum.inr 1378) = Sparse.eval nodeValue1378 (mixedVector B) := by
    change mixedMoment B node1378 node1378Labels = _
    exact sound1378 B hB hF
  have h1380 : mixedVector B (Sum.inr 1380) = Sparse.eval nodeValue1380 (mixedVector B) := by
    change mixedMoment B node1380 node1380Labels = _
    exact sound1380 B hB hF
  have h1383 : mixedVector B (Sum.inr 1383) = Sparse.eval nodeValue1383 (mixedVector B) := by
    change mixedMoment B node1383 node1383Labels = _
    exact sound1383 B hB hF
  have h1392 : mixedVector B (Sum.inr 1392) = Sparse.eval nodeValue1392 (mixedVector B) := by
    change mixedMoment B node1392 node1392Labels = _
    exact sound1392 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm393, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1378, h1380, h1383, h1392, h3064, h4091, reducedSource330] using sourceEq393 B hB

theorem rowSound330 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row330 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck330, numericCheck330, reducedZero330 B hB hF, mul_zero]

theorem reducedZero331 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource331 (mixedVector B) = 0 := by
  have h1383 : mixedVector B (Sum.inr 1383) = Sparse.eval nodeValue1383 (mixedVector B) := by
    change mixedMoment B node1383 node1383Labels = _
    exact sound1383 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3074 : mixedVector B (Sum.inr 3074) = Sparse.eval nodeValue3074 (mixedVector B) := by
    change mixedMoment B node3074 node3074Labels = _
    exact sound3074 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm394, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1383, h2924, h3064, h3074, h3077, h4091, reducedSource331] using sourceEq394 B hB

theorem rowSound331 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row331 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck331, numericCheck331, reducedZero331 B hB hF, mul_zero]

theorem reducedZero332 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource332 (mixedVector B) = 0 := by
  have h2562 : mixedVector B (Sum.inr 2562) = Sparse.eval nodeValue2562 (mixedVector B) := by
    change mixedMoment B node2562 node2562Labels = _
    exact sound2562 B hB hF
  have h3012 : mixedVector B (Sum.inr 3012) = Sparse.eval nodeValue3012 (mixedVector B) := by
    change mixedMoment B node3012 node3012Labels = _
    exact sound3012 B hB hF
  have h3013 : mixedVector B (Sum.inr 3013) = Sparse.eval nodeValue3013 (mixedVector B) := by
    change mixedMoment B node3013 node3013Labels = _
    exact sound3013 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm395, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2562, h3012, h3013, h3064, h3846, h4091, reducedSource332] using sourceEq395 B hB

theorem rowSound332 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row332 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck332, numericCheck332, reducedZero332 B hB hF, mul_zero]

theorem reducedZero333 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource333 (mixedVector B) = 0 := by
  have h2543 : mixedVector B (Sum.inr 2543) = Sparse.eval nodeValue2543 (mixedVector B) := by
    change mixedMoment B node2543 node2543Labels = _
    exact sound2543 B hB hF
  have h2916 : mixedVector B (Sum.inr 2916) = Sparse.eval nodeValue2916 (mixedVector B) := by
    change mixedMoment B node2916 node2916Labels = _
    exact sound2916 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h2933 : mixedVector B (Sum.inr 2933) = Sparse.eval nodeValue2933 (mixedVector B) := by
    change mixedMoment B node2933 node2933Labels = _
    exact sound2933 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm396, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2543, h2916, h2924, h2933, h3064, h3838, h4091, reducedSource333] using sourceEq396 B hB

theorem rowSound333 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row333 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck333, numericCheck333, reducedZero333 B hB hF, mul_zero]

theorem reducedZero334 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource334 (mixedVector B) = 0 := by
  have h1380 : mixedVector B (Sum.inr 1380) = Sparse.eval nodeValue1380 (mixedVector B) := by
    change mixedMoment B node1380 node1380Labels = _
    exact sound1380 B hB hF
  have h2916 : mixedVector B (Sum.inr 2916) = Sparse.eval nodeValue2916 (mixedVector B) := by
    change mixedMoment B node2916 node2916Labels = _
    exact sound2916 B hB hF
  have h3012 : mixedVector B (Sum.inr 3012) = Sparse.eval nodeValue3012 (mixedVector B) := by
    change mixedMoment B node3012 node3012Labels = _
    exact sound3012 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3066 : mixedVector B (Sum.inr 3066) = Sparse.eval nodeValue3066 (mixedVector B) := by
    change mixedMoment B node3066 node3066Labels = _
    exact sound3066 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm397, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1380, h2916, h3012, h3064, h3066, h4091, reducedSource334] using sourceEq397 B hB

theorem rowSound334 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row334 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck334, numericCheck334, reducedZero334 B hB hF, mul_zero]

theorem sourceRowsAt320 : MixedData.sourceRows (320 : Fin 2425) =
    MixedData.row320 := by decide +kernel

theorem sourceRowsAt321 : MixedData.sourceRows (321 : Fin 2425) =
    MixedData.row321 := by decide +kernel

theorem sourceRowsAt322 : MixedData.sourceRows (322 : Fin 2425) =
    MixedData.row322 := by decide +kernel

theorem sourceRowsAt323 : MixedData.sourceRows (323 : Fin 2425) =
    MixedData.row323 := by decide +kernel

theorem sourceRowsAt324 : MixedData.sourceRows (324 : Fin 2425) =
    MixedData.row324 := by decide +kernel

theorem sourceRowsAt325 : MixedData.sourceRows (325 : Fin 2425) =
    MixedData.row325 := by decide +kernel

theorem sourceRowsAt326 : MixedData.sourceRows (326 : Fin 2425) =
    MixedData.row326 := by decide +kernel

theorem sourceRowsAt327 : MixedData.sourceRows (327 : Fin 2425) =
    MixedData.row327 := by decide +kernel

theorem sourceRowsAt328 : MixedData.sourceRows (328 : Fin 2425) =
    MixedData.row328 := by decide +kernel

theorem sourceRowsAt329 : MixedData.sourceRows (329 : Fin 2425) =
    MixedData.row329 := by decide +kernel

theorem sourceRowsAt330 : MixedData.sourceRows (330 : Fin 2425) =
    MixedData.row330 := by decide +kernel

theorem sourceRowsAt331 : MixedData.sourceRows (331 : Fin 2425) =
    MixedData.row331 := by decide +kernel

theorem sourceRowsAt332 : MixedData.sourceRows (332 : Fin 2425) =
    MixedData.row332 := by decide +kernel

theorem sourceRowsAt333 : MixedData.sourceRows (333 : Fin 2425) =
    MixedData.row333 := by decide +kernel

theorem sourceRowsAt334 : MixedData.sourceRows (334 : Fin 2425) =
    MixedData.row334 := by decide +kernel

theorem sourceRowsAt335 : MixedData.sourceRows (335 : Fin 2425) =
    MixedData.row335 := by decide +kernel

theorem chunkSound20_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 20) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 320 ∨ k.val = 321 ∨ k.val = 322 ∨ k.val = 323 ∨ k.val = 324 ∨ k.val = 325 ∨ k.val = 326 ∨ k.val = 327 ∨ k.val = 328 ∨ k.val = 329 ∨ k.val = 330 ∨ k.val = 331 ∨ k.val = 332 ∨ k.val = 333 ∨ k.val = 334 ∨ k.val = 335 := by omega
  rcases heq with h320 | h321 | h322 | h323 | h324 | h325 | h326 | h327 | h328 | h329 | h330 | h331 | h332 | h333 | h334 | h335
  · have he : k = (320 : Fin 2425) := Fin.ext h320
    subst k
    rw [sourceRowsAt320]
    exact rowSound320 B hB hF
  · have he : k = (321 : Fin 2425) := Fin.ext h321
    subst k
    rw [sourceRowsAt321]
    exact rowSound321 B hB hF
  · have he : k = (322 : Fin 2425) := Fin.ext h322
    subst k
    rw [sourceRowsAt322]
    exact rowSound322 B hB hF
  · have he : k = (323 : Fin 2425) := Fin.ext h323
    subst k
    rw [sourceRowsAt323]
    exact rowSound323 B hB hF
  · have he : k = (324 : Fin 2425) := Fin.ext h324
    subst k
    rw [sourceRowsAt324]
    exact rowSound324 B hB hF
  · have he : k = (325 : Fin 2425) := Fin.ext h325
    subst k
    rw [sourceRowsAt325]
    exact rowSound325 B hB hF
  · have he : k = (326 : Fin 2425) := Fin.ext h326
    subst k
    rw [sourceRowsAt326]
    exact rowSound326_e B hB hF
  · have he : k = (327 : Fin 2425) := Fin.ext h327
    subst k
    rw [sourceRowsAt327]
    exact rowSound327_e B hB hF
  · have he : k = (328 : Fin 2425) := Fin.ext h328
    subst k
    rw [sourceRowsAt328]
    exact rowSound328 B hB hF
  · have he : k = (329 : Fin 2425) := Fin.ext h329
    subst k
    rw [sourceRowsAt329]
    exact rowSound329 B hB hF
  · have he : k = (330 : Fin 2425) := Fin.ext h330
    subst k
    rw [sourceRowsAt330]
    exact rowSound330 B hB hF
  · have he : k = (331 : Fin 2425) := Fin.ext h331
    subst k
    rw [sourceRowsAt331]
    exact rowSound331 B hB hF
  · have he : k = (332 : Fin 2425) := Fin.ext h332
    subst k
    rw [sourceRowsAt332]
    exact rowSound332 B hB hF
  · have he : k = (333 : Fin 2425) := Fin.ext h333
    subst k
    rw [sourceRowsAt333]
    exact rowSound333 B hB hF
  · have he : k = (334 : Fin 2425) := Fin.ext h334
    subst k
    rw [sourceRowsAt334]
    exact rowSound334 B hB hF
  · have he : k = (335 : Fin 2425) := Fin.ext h335
    subst k
    rw [sourceRowsAt335]
    exact rowSound335_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20_e_oai
