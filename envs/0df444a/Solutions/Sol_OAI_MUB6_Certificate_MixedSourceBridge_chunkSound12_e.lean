-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:02:33.816145+00:00
-- url     : https://prove2.me/submissions/d0537334-8860-4a4b-ae64-919c4a78a249

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
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E125
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound199_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound207_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw546 raw546Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw546 raw546Labels = mixedMoment B raw546step0 raw546step0Labels := by
      have ha : raw546step0 = (fun i j => raw546 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw546step0 raw546; decide +kernel
      have hl : raw546step0Labels = raw546Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw546 raw546Labels permutation8 permutation5
    mixedMoment B raw546step0 raw546step0Labels = mixedMoment B raw546step1 raw546step1Labels := by
      have ha : raw546step1 = raw546step0 := by apply Matrix.ext; unfold raw546step1 raw546step0; decide +kernel
      have hl : raw546step0Labels = labelEmbedding1 ∘ raw546step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw546step0 raw546step0Labels raw546step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3889 node3889Labels := by rfl

theorem canonical547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw547 raw547Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw547 raw547Labels = mixedMoment B raw547step0 raw547step0Labels := by
      have ha : raw547step0 = (fun i j => raw547 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw547step0 raw547; decide +kernel
      have hl : raw547step0Labels = raw547Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw547 raw547Labels permutation31 permutation4
    mixedMoment B raw547step0 raw547step0Labels = mixedMoment B raw547step1 raw547step1Labels := by
      have ha : raw547step1 = -raw547step0 := by apply Matrix.ext; change ∀ i j, raw547step1 i j = -(raw547step0 i j); unfold raw547step1 raw547step0; decide +kernel
      have hl : raw547step1Labels = raw547step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node496 node496Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5861 raw5861Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw5861 raw5861Labels = mixedMoment B raw5861step0 raw5861step0Labels := by
      have hz : ∀ j, raw5861 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5861step0 = (fun i j => raw5861 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5861step0 raw5861; decide +kernel
      have hl : raw5861step0Labels = raw5861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5861 raw5861Labels permutation434 hz
    mixedMoment B raw5861step0 raw5861step0Labels = mixedMoment B raw5861step1 raw5861step1Labels := by
      have hz : ∀ j, raw5861step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5861step1 = (fun i j => raw5861step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5861step1 raw5861step0; decide +kernel
      have hl : raw5861step1Labels = raw5861step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5861step0 raw5861step0Labels permutation80 hz
    _ = mixedMoment B node2744 node2744Labels := by rfl

theorem canonical5862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5862 raw5862Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw5862 raw5862Labels = mixedMoment B raw5862step0 raw5862step0Labels := by
      have hz : ∀ j, raw5862 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5862step0 = (fun i j => raw5862 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5862step0 raw5862; decide +kernel
      have hl : raw5862step0Labels = raw5862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5862 raw5862Labels permutation434 hz
    mixedMoment B raw5862step0 raw5862step0Labels = mixedMoment B raw5862step1 raw5862step1Labels := by
      have hz : ∀ j, raw5862step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5862step1 = (fun i j => raw5862step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5862step1 raw5862step0; decide +kernel
      have hl : raw5862step1Labels = raw5862step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5862step0 raw5862step0Labels permutation80 hz
    mixedMoment B raw5862step1 raw5862step1Labels = mixedMoment B raw5862step2 raw5862step2Labels := by
      have ha : raw5862step2 = (fun i j => raw5862step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5862step2 raw5862step1; decide +kernel
      have hl : raw5862step2Labels = raw5862step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5862step1 raw5862step1Labels permutation22 permutation4
    mixedMoment B raw5862step2 raw5862step2Labels = mixedMoment B raw5862step3 raw5862step3Labels := by
      have ha : raw5862step3 = -raw5862step2 := by apply Matrix.ext; change ∀ i j, raw5862step3 i j = -(raw5862step2 i j); unfold raw5862step3 raw5862step2; decide +kernel
      have hl : raw5862step3Labels = raw5862step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3626 node3626Labels := by rfl

theorem canonical5863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5863 raw5863Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw5863 raw5863Labels = mixedMoment B raw5863step0 raw5863step0Labels := by
      have hz : ∀ j, raw5863 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5863step0 = (fun i j => raw5863 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5863step0 raw5863; decide +kernel
      have hl : raw5863step0Labels = raw5863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5863 raw5863Labels permutation434 hz
    mixedMoment B raw5863step0 raw5863step0Labels = mixedMoment B raw5863step1 raw5863step1Labels := by
      have ha : raw5863step1 = (fun i j => raw5863step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5863step1 raw5863step0; decide +kernel
      have hl : raw5863step1Labels = raw5863step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5863step0 raw5863step0Labels permutation116 permutation4
    mixedMoment B raw5863step1 raw5863step1Labels = mixedMoment B raw5863step2 raw5863step2Labels := by
      have ha : raw5863step2 = -raw5863step1 := by apply Matrix.ext; change ∀ i j, raw5863step2 i j = -(raw5863step1 i j); unfold raw5863step2 raw5863step1; decide +kernel
      have hl : raw5863step2Labels = raw5863step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical5865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5865 raw5865Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw5865 raw5865Labels = mixedMoment B raw5865step0 raw5865step0Labels := by
      have hz : ∀ j, raw5865 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5865step0 = (fun i j => raw5865 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5865step0 raw5865; decide +kernel
      have hl : raw5865step0Labels = raw5865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5865 raw5865Labels permutation434 hz
    mixedMoment B raw5865step0 raw5865step0Labels = mixedMoment B raw5865step1 raw5865step1Labels := by
      have hz : ∀ j, raw5865step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5865step1 = (fun i j => raw5865step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5865step1 raw5865step0; decide +kernel
      have hl : raw5865step1Labels = raw5865step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5865step0 raw5865step0Labels permutation80 hz
    mixedMoment B raw5865step1 raw5865step1Labels = mixedMoment B raw5865step2 raw5865step2Labels := by
      have ha : raw5865step2 = (fun i j => raw5865step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5865step2 raw5865step1; decide +kernel
      have hl : raw5865step2Labels = raw5865step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5865step1 raw5865step1Labels permutation20 permutation4
    mixedMoment B raw5865step2 raw5865step2Labels = mixedMoment B raw5865step3 raw5865step3Labels := by
      have ha : raw5865step3 = -raw5865step2 := by apply Matrix.ext; change ∀ i j, raw5865step3 i j = -(raw5865step2 i j); unfold raw5865step3 raw5865step2; decide +kernel
      have hl : raw5865step3Labels = raw5865step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical5867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5867 raw5867Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5867 raw5867Labels = mixedMoment B raw5867step0 raw5867step0Labels := by
      have hz : ∀ j, raw5867 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw5867step0 = (fun i j => raw5867 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw5867step0 raw5867; decide +kernel
      have hl : raw5867step0Labels = raw5867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5867 raw5867Labels permutation590 hz
    mixedMoment B raw5867step0 raw5867step0Labels = mixedMoment B raw5867step1 raw5867step1Labels := by
      have hz : ∀ j, raw5867step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5867step1 = (fun i j => raw5867step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5867step1 raw5867step0; decide +kernel
      have hl : raw5867step1Labels = raw5867step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5867step0 raw5867step0Labels permutation104 hz
    mixedMoment B raw5867step1 raw5867step1Labels = mixedMoment B raw5867step2 raw5867step2Labels := by
      have hz : ∀ j, raw5867step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5867step2 = (fun i j => raw5867step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5867step2 raw5867step1; decide +kernel
      have hl : raw5867step2Labels = raw5867step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5867step1 raw5867step1Labels permutation20 hz
    mixedMoment B raw5867step2 raw5867step2Labels = mixedMoment B raw5867step3 raw5867step3Labels := by
      have ha : raw5867step3 = (fun i j => raw5867step2 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5867step3 raw5867step2; decide +kernel
      have hl : raw5867step3Labels = raw5867step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5867step2 raw5867step2Labels permutation7 permutation0
    mixedMoment B raw5867step3 raw5867step3Labels = mixedMoment B raw5867step4 raw5867step4Labels := by
      have ha : raw5867step4 = -raw5867step3 := by apply Matrix.ext; change ∀ i j, raw5867step4 i j = -(raw5867step3 i j); unfold raw5867step4 raw5867step3; decide +kernel
      have hl : raw5867step4Labels = raw5867step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical5869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5869 raw5869Labels = mixedMoment B node1238 node1238Labels := by
  calc
    mixedMoment B raw5869 raw5869Labels = mixedMoment B raw5869step0 raw5869step0Labels := by
      have hz : ∀ j, raw5869 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5869step0 = (fun i j => raw5869 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5869step0 raw5869; decide +kernel
      have hl : raw5869step0Labels = raw5869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5869 raw5869Labels permutation434 hz
    _ = mixedMoment B node1238 node1238Labels := by rfl

theorem canonical5871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5871 raw5871Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw5871 raw5871Labels = mixedMoment B raw5871step0 raw5871step0Labels := by
      have hz : ∀ j, raw5871 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5871step0 = (fun i j => raw5871 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5871step0 raw5871; decide +kernel
      have hl : raw5871step0Labels = raw5871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5871 raw5871Labels permutation434 hz
    mixedMoment B raw5871step0 raw5871step0Labels = mixedMoment B raw5871step1 raw5871step1Labels := by
      have hz : ∀ j, raw5871step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5871step1 = (fun i j => raw5871step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5871step1 raw5871step0; decide +kernel
      have hl : raw5871step1Labels = raw5871step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5871step0 raw5871step0Labels permutation80 hz
    mixedMoment B raw5871step1 raw5871step1Labels = mixedMoment B raw5871step2 raw5871step2Labels := by
      have ha : raw5871step2 = (fun i j => raw5871step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5871step2 raw5871step1; decide +kernel
      have hl : raw5871step2Labels = raw5871step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5871step1 raw5871step1Labels permutation9 permutation2
    _ = mixedMoment B node1245 node1245Labels := by rfl

theorem canonical5872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5872 raw5872Labels = mixedMoment B node1244 node1244Labels := by
  calc
    mixedMoment B raw5872 raw5872Labels = mixedMoment B raw5872step0 raw5872step0Labels := by
      have hz : ∀ j, raw5872 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5872step0 = (fun i j => raw5872 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5872step0 raw5872; decide +kernel
      have hl : raw5872step0Labels = raw5872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5872 raw5872Labels permutation434 hz
    mixedMoment B raw5872step0 raw5872step0Labels = mixedMoment B raw5872step1 raw5872step1Labels := by
      have hz : ∀ j, raw5872step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5872step1 = (fun i j => raw5872step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5872step1 raw5872step0; decide +kernel
      have hl : raw5872step1Labels = raw5872step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5872step0 raw5872step0Labels permutation80 hz
    _ = mixedMoment B node1244 node1244Labels := by rfl

theorem canonical5873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5873 raw5873Labels = mixedMoment B node2592 node2592Labels := by
  calc
    mixedMoment B raw5873 raw5873Labels = mixedMoment B raw5873step0 raw5873step0Labels := by
      have hz : ∀ j, raw5873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5873step0 = (fun i j => raw5873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5873step0 raw5873; decide +kernel
      have hl : raw5873step0Labels = raw5873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5873 raw5873Labels permutation434 hz
    mixedMoment B raw5873step0 raw5873step0Labels = mixedMoment B raw5873step1 raw5873step1Labels := by
      have ha : raw5873step1 = (fun i j => raw5873step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5873step1 raw5873step0; decide +kernel
      have hl : raw5873step1Labels = raw5873step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5873step0 raw5873step0Labels permutation38 permutation2
    _ = mixedMoment B node2592 node2592Labels := by rfl

theorem canonical5875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5875 raw5875Labels = mixedMoment B node2138 node2138Labels := by
  calc
    mixedMoment B raw5875 raw5875Labels = mixedMoment B raw5875step0 raw5875step0Labels := by
      have hz : ∀ j, raw5875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5875step0 = (fun i j => raw5875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5875step0 raw5875; decide +kernel
      have hl : raw5875step0Labels = raw5875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5875 raw5875Labels permutation434 hz
    mixedMoment B raw5875step0 raw5875step0Labels = mixedMoment B raw5875step1 raw5875step1Labels := by
      have hz : ∀ j, raw5875step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5875step1 = (fun i j => raw5875step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5875step1 raw5875step0; decide +kernel
      have hl : raw5875step1Labels = raw5875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5875step0 raw5875step0Labels permutation80 hz
    mixedMoment B raw5875step1 raw5875step1Labels = mixedMoment B raw5875step2 raw5875step2Labels := by
      have ha : raw5875step2 = (fun i j => raw5875step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5875step2 raw5875step1; decide +kernel
      have hl : raw5875step2Labels = raw5875step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5875step1 raw5875step1Labels permutation21 permutation4
    mixedMoment B raw5875step2 raw5875step2Labels = mixedMoment B raw5875step3 raw5875step3Labels := by
      have ha : raw5875step3 = -raw5875step2 := by apply Matrix.ext; change ∀ i j, raw5875step3 i j = -(raw5875step2 i j); unfold raw5875step3 raw5875step2; decide +kernel
      have hl : raw5875step3Labels = raw5875step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2138 node2138Labels := by rfl

theorem canonical5877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5877 raw5877Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw5877 raw5877Labels = mixedMoment B raw5877step0 raw5877step0Labels := by
      have hz : ∀ j, raw5877 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5877step0 = (fun i j => raw5877 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5877step0 raw5877; decide +kernel
      have hl : raw5877step0Labels = raw5877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5877 raw5877Labels permutation434 hz
    _ = mixedMoment B node2513 node2513Labels := by rfl

theorem canonical5878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5878 raw5878Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw5878 raw5878Labels = mixedMoment B raw5878step0 raw5878step0Labels := by
      have hz : ∀ j, raw5878 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5878step0 = (fun i j => raw5878 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5878step0 raw5878; decide +kernel
      have hl : raw5878step0Labels = raw5878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5878 raw5878Labels permutation346 hz
    _ = mixedMoment B node2513 node2513Labels := by rfl

theorem canonical5879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5879 raw5879Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw5879 raw5879Labels = mixedMoment B raw5879step0 raw5879step0Labels := by
      have hz : ∀ j, raw5879 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5879step0 = (fun i j => raw5879 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5879step0 raw5879; decide +kernel
      have hl : raw5879step0Labels = raw5879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5879 raw5879Labels permutation434 hz
    mixedMoment B raw5879step0 raw5879step0Labels = mixedMoment B raw5879step1 raw5879step1Labels := by
      have hz : ∀ j, raw5879step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5879step1 = (fun i j => raw5879step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5879step1 raw5879step0; decide +kernel
      have hl : raw5879step1Labels = raw5879step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5879step0 raw5879step0Labels permutation80 hz
    mixedMoment B raw5879step1 raw5879step1Labels = mixedMoment B raw5879step2 raw5879step2Labels := by
      have ha : raw5879step2 = (fun i j => raw5879step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5879step2 raw5879step1; decide +kernel
      have hl : raw5879step2Labels = raw5879step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5879step1 raw5879step1Labels permutation9 permutation2
    _ = mixedMoment B node2522 node2522Labels := by rfl

theorem canonical5880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5880 raw5880Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw5880 raw5880Labels = mixedMoment B raw5880step0 raw5880step0Labels := by
      have hz : ∀ j, raw5880 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5880step0 = (fun i j => raw5880 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5880step0 raw5880; decide +kernel
      have hl : raw5880step0Labels = raw5880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5880 raw5880Labels permutation434 hz
    mixedMoment B raw5880step0 raw5880step0Labels = mixedMoment B raw5880step1 raw5880step1Labels := by
      have hz : ∀ j, raw5880step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5880step1 = (fun i j => raw5880step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5880step1 raw5880step0; decide +kernel
      have hl : raw5880step1Labels = raw5880step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5880step0 raw5880step0Labels permutation80 hz
    _ = mixedMoment B node2520 node2520Labels := by rfl

theorem canonical5881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5881 raw5881Labels = mixedMoment B node2555 node2555Labels := by
  calc
    mixedMoment B raw5881 raw5881Labels = mixedMoment B raw5881step0 raw5881step0Labels := by
      have ha : raw5881step0 = (fun i j => raw5881 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5881step0 raw5881; decide +kernel
      have hl : raw5881step0Labels = raw5881Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5881 raw5881Labels permutation200 permutation2
    _ = mixedMoment B node2555 node2555Labels := by rfl

theorem canonical5882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5882 raw5882Labels = mixedMoment B node2133 node2133Labels := by
  calc
    mixedMoment B raw5882 raw5882Labels = mixedMoment B raw5882step0 raw5882step0Labels := by
      have hz : ∀ j, raw5882 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5882step0 = (fun i j => raw5882 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5882step0 raw5882; decide +kernel
      have hl : raw5882step0Labels = raw5882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5882 raw5882Labels permutation434 hz
    mixedMoment B raw5882step0 raw5882step0Labels = mixedMoment B raw5882step1 raw5882step1Labels := by
      have ha : raw5882step1 = (fun i j => raw5882step0 (permutation106 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5882step1 raw5882step0; decide +kernel
      have hl : raw5882step1Labels = raw5882step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5882step0 raw5882step0Labels permutation106 permutation4
    mixedMoment B raw5882step1 raw5882step1Labels = mixedMoment B raw5882step2 raw5882step2Labels := by
      have ha : raw5882step2 = -raw5882step1 := by apply Matrix.ext; change ∀ i j, raw5882step2 i j = -(raw5882step1 i j); unfold raw5882step2 raw5882step1; decide +kernel
      have hl : raw5882step2Labels = raw5882step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2133 node2133Labels := by rfl

theorem canonical5883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5883 raw5883Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw5883 raw5883Labels = mixedMoment B raw5883step0 raw5883step0Labels := by
      have hz : ∀ j, raw5883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5883step0 = (fun i j => raw5883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5883step0 raw5883; decide +kernel
      have hl : raw5883step0Labels = raw5883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5883 raw5883Labels permutation434 hz
    mixedMoment B raw5883step0 raw5883step0Labels = mixedMoment B raw5883step1 raw5883step1Labels := by
      have ha : raw5883step1 = (fun i j => raw5883step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5883step1 raw5883step0; decide +kernel
      have hl : raw5883step1Labels = raw5883step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5883step0 raw5883step0Labels permutation33 permutation2
    _ = mixedMoment B node2738 node2738Labels := by rfl

theorem canonical5884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5884 raw5884Labels = mixedMoment B node2555 node2555Labels := by
  calc
    mixedMoment B raw5884 raw5884Labels = mixedMoment B raw5884step0 raw5884step0Labels := by
      have ha : raw5884step0 = (fun i j => raw5884 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5884step0 raw5884; decide +kernel
      have hl : raw5884step0Labels = raw5884Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5884 raw5884Labels permutation176 permutation2
    _ = mixedMoment B node2555 node2555Labels := by rfl

theorem canonical5885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5885 raw5885Labels = mixedMoment B node2560 node2560Labels := by
  calc
    mixedMoment B raw5885 raw5885Labels = mixedMoment B raw5885step0 raw5885step0Labels := by
      have hz : ∀ j, raw5885 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5885step0 = (fun i j => raw5885 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5885step0 raw5885; decide +kernel
      have hl : raw5885step0Labels = raw5885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5885 raw5885Labels permutation434 hz
    mixedMoment B raw5885step0 raw5885step0Labels = mixedMoment B raw5885step1 raw5885step1Labels := by
      have ha : raw5885step1 = (fun i j => raw5885step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5885step1 raw5885step0; decide +kernel
      have hl : raw5885step1Labels = raw5885step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5885step0 raw5885step0Labels permutation39 permutation2
    _ = mixedMoment B node2560 node2560Labels := by rfl

theorem canonical5886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5886 raw5886Labels = mixedMoment B node2559 node2559Labels := by
  calc
    mixedMoment B raw5886 raw5886Labels = mixedMoment B raw5886step0 raw5886step0Labels := by
      have hz : ∀ j, raw5886 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5886step0 = (fun i j => raw5886 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5886step0 raw5886; decide +kernel
      have hl : raw5886step0Labels = raw5886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5886 raw5886Labels permutation434 hz
    mixedMoment B raw5886step0 raw5886step0Labels = mixedMoment B raw5886step1 raw5886step1Labels := by
      have ha : raw5886step1 = (fun i j => raw5886step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5886step1 raw5886step0; decide +kernel
      have hl : raw5886step1Labels = raw5886step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5886step0 raw5886step0Labels permutation38 permutation2
    _ = mixedMoment B node2559 node2559Labels := by rfl

theorem canonical5887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5887 raw5887Labels = mixedMoment B node2560 node2560Labels := by
  calc
    mixedMoment B raw5887 raw5887Labels = mixedMoment B raw5887step0 raw5887step0Labels := by
      have hz : ∀ j, raw5887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5887step0 = (fun i j => raw5887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5887step0 raw5887; decide +kernel
      have hl : raw5887step0Labels = raw5887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5887 raw5887Labels permutation346 hz
    mixedMoment B raw5887step0 raw5887step0Labels = mixedMoment B raw5887step1 raw5887step1Labels := by
      have ha : raw5887step1 = (fun i j => raw5887step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5887step1 raw5887step0; decide +kernel
      have hl : raw5887step1Labels = raw5887step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5887step0 raw5887step0Labels permutation39 permutation2
    _ = mixedMoment B node2560 node2560Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5888 raw5888Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw5888 raw5888Labels = mixedMoment B raw5888step0 raw5888step0Labels := by
      have hz : ∀ j, raw5888 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5888step0 = (fun i j => raw5888 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5888step0 raw5888; decide +kernel
      have hl : raw5888step0Labels = raw5888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5888 raw5888Labels permutation434 hz
    mixedMoment B raw5888step0 raw5888step0Labels = mixedMoment B raw5888step1 raw5888step1Labels := by
      have hz : ∀ j, raw5888step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5888step1 = (fun i j => raw5888step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5888step1 raw5888step0; decide +kernel
      have hl : raw5888step1Labels = raw5888step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5888step0 raw5888step0Labels permutation80 hz
    mixedMoment B raw5888step1 raw5888step1Labels = mixedMoment B raw5888step2 raw5888step2Labels := by
      have ha : raw5888step2 = (fun i j => raw5888step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5888step2 raw5888step1; decide +kernel
      have hl : raw5888step2Labels = raw5888step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5888step1 raw5888step1Labels permutation9 permutation2
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical5889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5889 raw5889Labels = mixedMoment B node2133 node2133Labels := by
  calc
    mixedMoment B raw5889 raw5889Labels = mixedMoment B raw5889step0 raw5889step0Labels := by
      have hz : ∀ j, raw5889 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5889step0 = (fun i j => raw5889 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5889step0 raw5889; decide +kernel
      have hl : raw5889step0Labels = raw5889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5889 raw5889Labels permutation346 hz
    mixedMoment B raw5889step0 raw5889step0Labels = mixedMoment B raw5889step1 raw5889step1Labels := by
      have ha : raw5889step1 = (fun i j => raw5889step0 (permutation106 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5889step1 raw5889step0; decide +kernel
      have hl : raw5889step1Labels = raw5889step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5889step0 raw5889step0Labels permutation106 permutation4
    mixedMoment B raw5889step1 raw5889step1Labels = mixedMoment B raw5889step2 raw5889step2Labels := by
      have ha : raw5889step2 = -raw5889step1 := by apply Matrix.ext; change ∀ i j, raw5889step2 i j = -(raw5889step1 i j); unfold raw5889step2 raw5889step1; decide +kernel
      have hl : raw5889step2Labels = raw5889step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2133 node2133Labels := by rfl

theorem canonical5890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5890 raw5890Labels = mixedMoment B node2136 node2136Labels := by
  calc
    mixedMoment B raw5890 raw5890Labels = mixedMoment B raw5890step0 raw5890step0Labels := by
      have hz : ∀ j, raw5890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5890step0 = (fun i j => raw5890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5890step0 raw5890; decide +kernel
      have hl : raw5890step0Labels = raw5890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5890 raw5890Labels permutation434 hz
    mixedMoment B raw5890step0 raw5890step0Labels = mixedMoment B raw5890step1 raw5890step1Labels := by
      have hz : ∀ j, raw5890step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5890step1 = (fun i j => raw5890step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5890step1 raw5890step0; decide +kernel
      have hl : raw5890step1Labels = raw5890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5890step0 raw5890step0Labels permutation80 hz
    mixedMoment B raw5890step1 raw5890step1Labels = mixedMoment B raw5890step2 raw5890step2Labels := by
      have ha : raw5890step2 = (fun i j => raw5890step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5890step2 raw5890step1; decide +kernel
      have hl : raw5890step2Labels = raw5890step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5890step1 raw5890step1Labels permutation20 permutation4
    mixedMoment B raw5890step2 raw5890step2Labels = mixedMoment B raw5890step3 raw5890step3Labels := by
      have ha : raw5890step3 = -raw5890step2 := by apply Matrix.ext; change ∀ i j, raw5890step3 i j = -(raw5890step2 i j); unfold raw5890step3 raw5890step2; decide +kernel
      have hl : raw5890step3Labels = raw5890step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2136 node2136Labels := by rfl

theorem canonical5891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5891 raw5891Labels = mixedMoment B node2559 node2559Labels := by
  calc
    mixedMoment B raw5891 raw5891Labels = mixedMoment B raw5891step0 raw5891step0Labels := by
      have hz : ∀ j, raw5891 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5891step0 = (fun i j => raw5891 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5891step0 raw5891; decide +kernel
      have hl : raw5891step0Labels = raw5891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5891 raw5891Labels permutation346 hz
    mixedMoment B raw5891step0 raw5891step0Labels = mixedMoment B raw5891step1 raw5891step1Labels := by
      have ha : raw5891step1 = (fun i j => raw5891step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5891step1 raw5891step0; decide +kernel
      have hl : raw5891step1Labels = raw5891step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5891step0 raw5891step0Labels permutation38 permutation2
    _ = mixedMoment B node2559 node2559Labels := by rfl

theorem canonical5922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5922 raw5922Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw5922 raw5922Labels = mixedMoment B raw5922step0 raw5922step0Labels := by
      have hz : ∀ j, raw5922 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5922step0 = (fun i j => raw5922 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5922step0 raw5922; decide +kernel
      have hl : raw5922step0Labels = raw5922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5922 raw5922Labels permutation434 hz
    mixedMoment B raw5922step0 raw5922step0Labels = mixedMoment B raw5922step1 raw5922step1Labels := by
      have hz : ∀ j, raw5922step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5922step1 = (fun i j => raw5922step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5922step1 raw5922step0; decide +kernel
      have hl : raw5922step1Labels = raw5922step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5922step0 raw5922step0Labels permutation80 hz
    mixedMoment B raw5922step1 raw5922step1Labels = mixedMoment B raw5922step2 raw5922step2Labels := by
      have ha : raw5922step2 = (fun i j => raw5922step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5922step2 raw5922step1; decide +kernel
      have hl : raw5922step2Labels = raw5922step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5922step1 raw5922step1Labels permutation20 permutation6
    mixedMoment B raw5922step2 raw5922step2Labels = mixedMoment B raw5922step3 raw5922step3Labels := by
      have ha : raw5922step3 = -raw5922step2 := by apply Matrix.ext; change ∀ i j, raw5922step3 i j = -(raw5922step2 i j); unfold raw5922step3 raw5922step2; decide +kernel
      have hl : raw5922step3Labels = raw5922step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3584 node3584Labels := by rfl

theorem canonical5923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5923 raw5923Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw5923 raw5923Labels = mixedMoment B raw5923step0 raw5923step0Labels := by
      have hz : ∀ j, raw5923 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5923step0 = (fun i j => raw5923 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5923step0 raw5923; decide +kernel
      have hl : raw5923step0Labels = raw5923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5923 raw5923Labels permutation434 hz
    mixedMoment B raw5923step0 raw5923step0Labels = mixedMoment B raw5923step1 raw5923step1Labels := by
      have ha : raw5923step1 = (fun i j => raw5923step0 (permutation106 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5923step1 raw5923step0; decide +kernel
      have hl : raw5923step1Labels = raw5923step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5923step0 raw5923step0Labels permutation106 permutation6
    mixedMoment B raw5923step1 raw5923step1Labels = mixedMoment B raw5923step2 raw5923step2Labels := by
      have ha : raw5923step2 = -raw5923step1 := by apply Matrix.ext; change ∀ i j, raw5923step2 i j = -(raw5923step1 i j); unfold raw5923step2 raw5923step1; decide +kernel
      have hl : raw5923step2Labels = raw5923step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical5924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5924 raw5924Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw5924 raw5924Labels = mixedMoment B raw5924step0 raw5924step0Labels := by
      have hz : ∀ j, raw5924 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5924step0 = (fun i j => raw5924 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5924step0 raw5924; decide +kernel
      have hl : raw5924step0Labels = raw5924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5924 raw5924Labels permutation346 hz
    mixedMoment B raw5924step0 raw5924step0Labels = mixedMoment B raw5924step1 raw5924step1Labels := by
      have ha : raw5924step1 = (fun i j => raw5924step0 (permutation106 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5924step1 raw5924step0; decide +kernel
      have hl : raw5924step1Labels = raw5924step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5924step0 raw5924step0Labels permutation106 permutation6
    mixedMoment B raw5924step1 raw5924step1Labels = mixedMoment B raw5924step2 raw5924step2Labels := by
      have ha : raw5924step2 = -raw5924step1 := by apply Matrix.ext; change ∀ i j, raw5924step2 i j = -(raw5924step1 i j); unfold raw5924step2 raw5924step1; decide +kernel
      have hl : raw5924step2Labels = raw5924step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical5925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5925 raw5925Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw5925 raw5925Labels = mixedMoment B raw5925step0 raw5925step0Labels := by
      have hz : ∀ j, raw5925 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5925step0 = (fun i j => raw5925 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5925step0 raw5925; decide +kernel
      have hl : raw5925step0Labels = raw5925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5925 raw5925Labels permutation434 hz
    mixedMoment B raw5925step0 raw5925step0Labels = mixedMoment B raw5925step1 raw5925step1Labels := by
      have hz : ∀ j, raw5925step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5925step1 = (fun i j => raw5925step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5925step1 raw5925step0; decide +kernel
      have hl : raw5925step1Labels = raw5925step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5925step0 raw5925step0Labels permutation80 hz
    mixedMoment B raw5925step1 raw5925step1Labels = mixedMoment B raw5925step2 raw5925step2Labels := by
      have ha : raw5925step2 = (fun i j => raw5925step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5925step2 raw5925step1; decide +kernel
      have hl : raw5925step2Labels = raw5925step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5925step1 raw5925step1Labels permutation20 permutation6
    mixedMoment B raw5925step2 raw5925step2Labels = mixedMoment B raw5925step3 raw5925step3Labels := by
      have ha : raw5925step3 = -raw5925step2 := by apply Matrix.ext; change ∀ i j, raw5925step3 i j = -(raw5925step2 i j); unfold raw5925step3 raw5925step2; decide +kernel
      have hl : raw5925step3Labels = raw5925step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3889 node3889Labels := by rfl

theorem canonical5926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5926 raw5926Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw5926 raw5926Labels = mixedMoment B raw5926step0 raw5926step0Labels := by
      have hz : ∀ j, raw5926 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5926step0 = (fun i j => raw5926 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5926step0 raw5926; decide +kernel
      have hl : raw5926step0Labels = raw5926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5926 raw5926Labels permutation434 hz
    mixedMoment B raw5926step0 raw5926step0Labels = mixedMoment B raw5926step1 raw5926step1Labels := by
      have hz : ∀ j, raw5926step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5926step1 = (fun i j => raw5926step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5926step1 raw5926step0; decide +kernel
      have hl : raw5926step1Labels = raw5926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5926step0 raw5926step0Labels permutation80 hz
    mixedMoment B raw5926step1 raw5926step1Labels = mixedMoment B raw5926step2 raw5926step2Labels := by
      have ha : raw5926step2 = (fun i j => raw5926step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5926step2 raw5926step1; decide +kernel
      have hl : raw5926step2Labels = raw5926step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5926step1 raw5926step1Labels permutation20 permutation6
    mixedMoment B raw5926step2 raw5926step2Labels = mixedMoment B raw5926step3 raw5926step3Labels := by
      have ha : raw5926step3 = -raw5926step2 := by apply Matrix.ext; change ∀ i j, raw5926step3 i j = -(raw5926step2 i j); unfold raw5926step3 raw5926step2; decide +kernel
      have hl : raw5926step3Labels = raw5926step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3583 node3583Labels := by rfl

theorem canonical5927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5927 raw5927Labels = mixedMoment B node1084 node1084Labels := by
  calc
    mixedMoment B raw5927 raw5927Labels = mixedMoment B raw5927step0 raw5927step0Labels := by
      have hz : ∀ j, raw5927 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5927step0 = (fun i j => raw5927 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5927step0 raw5927; decide +kernel
      have hl : raw5927step0Labels = raw5927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5927 raw5927Labels permutation434 hz
    mixedMoment B raw5927step0 raw5927step0Labels = mixedMoment B raw5927step1 raw5927step1Labels := by
      have hz : ∀ j, raw5927step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5927step1 = (fun i j => raw5927step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5927step1 raw5927step0; decide +kernel
      have hl : raw5927step1Labels = raw5927step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5927step0 raw5927step0Labels permutation80 hz
    mixedMoment B raw5927step1 raw5927step1Labels = mixedMoment B raw5927step2 raw5927step2Labels := by
      have ha : raw5927step2 = (fun i j => raw5927step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5927step2 raw5927step1; decide +kernel
      have hl : raw5927step2Labels = raw5927step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5927step1 raw5927step1Labels permutation8 permutation3
    _ = mixedMoment B node1084 node1084Labels := by rfl

theorem canonical5928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5928 raw5928Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw5928 raw5928Labels = mixedMoment B raw5928step0 raw5928step0Labels := by
      have hz : ∀ j, raw5928 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5928step0 = (fun i j => raw5928 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5928step0 raw5928; decide +kernel
      have hl : raw5928step0Labels = raw5928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5928 raw5928Labels permutation434 hz
    mixedMoment B raw5928step0 raw5928step0Labels = mixedMoment B raw5928step1 raw5928step1Labels := by
      have ha : raw5928step1 = (fun i j => raw5928step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5928step1 raw5928step0; decide +kernel
      have hl : raw5928step1Labels = raw5928step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5928step0 raw5928step0Labels permutation38 permutation3
    _ = mixedMoment B node2513 node2513Labels := by rfl

theorem canonical5929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5929 raw5929Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw5929 raw5929Labels = mixedMoment B raw5929step0 raw5929step0Labels := by
      have hz : ∀ j, raw5929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5929step0 = (fun i j => raw5929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5929step0 raw5929; decide +kernel
      have hl : raw5929step0Labels = raw5929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5929 raw5929Labels permutation346 hz
    mixedMoment B raw5929step0 raw5929step0Labels = mixedMoment B raw5929step1 raw5929step1Labels := by
      have ha : raw5929step1 = (fun i j => raw5929step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5929step1 raw5929step0; decide +kernel
      have hl : raw5929step1Labels = raw5929step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5929step0 raw5929step0Labels permutation38 permutation3
    _ = mixedMoment B node2513 node2513Labels := by rfl

theorem canonical5930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5930 raw5930Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw5930 raw5930Labels = mixedMoment B raw5930step0 raw5930step0Labels := by
      have hz : ∀ j, raw5930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5930step0 = (fun i j => raw5930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5930step0 raw5930; decide +kernel
      have hl : raw5930step0Labels = raw5930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5930 raw5930Labels permutation434 hz
    mixedMoment B raw5930step0 raw5930step0Labels = mixedMoment B raw5930step1 raw5930step1Labels := by
      have hz : ∀ j, raw5930step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5930step1 = (fun i j => raw5930step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5930step1 raw5930step0; decide +kernel
      have hl : raw5930step1Labels = raw5930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5930step0 raw5930step0Labels permutation80 hz
    mixedMoment B raw5930step1 raw5930step1Labels = mixedMoment B raw5930step2 raw5930step2Labels := by
      have ha : raw5930step2 = (fun i j => raw5930step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5930step2 raw5930step1; decide +kernel
      have hl : raw5930step2Labels = raw5930step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5930step1 raw5930step1Labels permutation10 permutation3
    _ = mixedMoment B node2776 node2776Labels := by rfl

theorem canonical5931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5931 raw5931Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw5931 raw5931Labels = mixedMoment B raw5931step0 raw5931step0Labels := by
      have hz : ∀ j, raw5931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5931step0 = (fun i j => raw5931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5931step0 raw5931; decide +kernel
      have hl : raw5931step0Labels = raw5931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5931 raw5931Labels permutation434 hz
    mixedMoment B raw5931step0 raw5931step0Labels = mixedMoment B raw5931step1 raw5931step1Labels := by
      have hz : ∀ j, raw5931step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5931step1 = (fun i j => raw5931step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5931step1 raw5931step0; decide +kernel
      have hl : raw5931step1Labels = raw5931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5931step0 raw5931step0Labels permutation80 hz
    mixedMoment B raw5931step1 raw5931step1Labels = mixedMoment B raw5931step2 raw5931step2Labels := by
      have ha : raw5931step2 = (fun i j => raw5931step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5931step2 raw5931step1; decide +kernel
      have hl : raw5931step2Labels = raw5931step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5931step1 raw5931step1Labels permutation12 permutation3
    _ = mixedMoment B node2781 node2781Labels := by rfl

theorem canonical5932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5932 raw5932Labels = mixedMoment B node1006 node1006Labels := by
  calc
    mixedMoment B raw5932 raw5932Labels = mixedMoment B raw5932step0 raw5932step0Labels := by
      have hz : ∀ j, raw5932 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5932step0 = (fun i j => raw5932 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5932step0 raw5932; decide +kernel
      have hl : raw5932step0Labels = raw5932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5932 raw5932Labels permutation434 hz
    mixedMoment B raw5932step0 raw5932step0Labels = mixedMoment B raw5932step1 raw5932step1Labels := by
      have ha : raw5932step1 = (fun i j => raw5932step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5932step1 raw5932step0; decide +kernel
      have hl : raw5932step1Labels = raw5932step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5932step0 raw5932step0Labels permutation32 permutation3
    _ = mixedMoment B node1006 node1006Labels := by rfl

theorem canonical5933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5933 raw5933Labels = mixedMoment B node2405 node2405Labels := by
  calc
    mixedMoment B raw5933 raw5933Labels = mixedMoment B raw5933step0 raw5933step0Labels := by
      have hz : ∀ j, raw5933 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5933step0 = (fun i j => raw5933 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5933step0 raw5933; decide +kernel
      have hl : raw5933step0Labels = raw5933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5933 raw5933Labels permutation434 hz
    mixedMoment B raw5933step0 raw5933step0Labels = mixedMoment B raw5933step1 raw5933step1Labels := by
      have ha : raw5933step1 = (fun i j => raw5933step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5933step1 raw5933step0; decide +kernel
      have hl : raw5933step1Labels = raw5933step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5933step0 raw5933step0Labels permutation32 permutation3
    _ = mixedMoment B node2405 node2405Labels := by rfl

theorem canonical5934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5934 raw5934Labels = mixedMoment B node2463 node2463Labels := by
  calc
    mixedMoment B raw5934 raw5934Labels = mixedMoment B raw5934step0 raw5934step0Labels := by
      have ha : raw5934step0 = (fun i j => raw5934 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5934step0 raw5934; decide +kernel
      have hl : raw5934step0Labels = raw5934Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5934 raw5934Labels permutation200 permutation3
    _ = mixedMoment B node2463 node2463Labels := by rfl

theorem canonical5935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5935 raw5935Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw5935 raw5935Labels = mixedMoment B raw5935step0 raw5935step0Labels := by
      have hz : ∀ j, raw5935 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5935step0 = (fun i j => raw5935 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5935step0 raw5935; decide +kernel
      have hl : raw5935step0Labels = raw5935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5935 raw5935Labels permutation434 hz
    mixedMoment B raw5935step0 raw5935step0Labels = mixedMoment B raw5935step1 raw5935step1Labels := by
      have ha : raw5935step1 = (fun i j => raw5935step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5935step1 raw5935step0; decide +kernel
      have hl : raw5935step1Labels = raw5935step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5935step0 raw5935step0Labels permutation34 permutation3
    _ = mixedMoment B node2732 node2732Labels := by rfl

theorem canonical5936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5936 raw5936Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw5936 raw5936Labels = mixedMoment B raw5936step0 raw5936step0Labels := by
      have hz : ∀ j, raw5936 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5936step0 = (fun i j => raw5936 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5936step0 raw5936; decide +kernel
      have hl : raw5936step0Labels = raw5936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5936 raw5936Labels permutation434 hz
    mixedMoment B raw5936step0 raw5936step0Labels = mixedMoment B raw5936step1 raw5936step1Labels := by
      have ha : raw5936step1 = (fun i j => raw5936step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5936step1 raw5936step0; decide +kernel
      have hl : raw5936step1Labels = raw5936step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5936step0 raw5936step0Labels permutation36 permutation3
    _ = mixedMoment B node2735 node2735Labels := by rfl

theorem canonical5937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5937 raw5937Labels = mixedMoment B node1006 node1006Labels := by
  calc
    mixedMoment B raw5937 raw5937Labels = mixedMoment B raw5937step0 raw5937step0Labels := by
      have hz : ∀ j, raw5937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5937step0 = (fun i j => raw5937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5937step0 raw5937; decide +kernel
      have hl : raw5937step0Labels = raw5937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5937 raw5937Labels permutation346 hz
    mixedMoment B raw5937step0 raw5937step0Labels = mixedMoment B raw5937step1 raw5937step1Labels := by
      have ha : raw5937step1 = (fun i j => raw5937step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5937step1 raw5937step0; decide +kernel
      have hl : raw5937step1Labels = raw5937step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5937step0 raw5937step0Labels permutation32 permutation3
    _ = mixedMoment B node1006 node1006Labels := by rfl

theorem canonical5938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5938 raw5938Labels = mixedMoment B node2405 node2405Labels := by
  calc
    mixedMoment B raw5938 raw5938Labels = mixedMoment B raw5938step0 raw5938step0Labels := by
      have hz : ∀ j, raw5938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5938step0 = (fun i j => raw5938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5938step0 raw5938; decide +kernel
      have hl : raw5938step0Labels = raw5938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5938 raw5938Labels permutation346 hz
    mixedMoment B raw5938step0 raw5938step0Labels = mixedMoment B raw5938step1 raw5938step1Labels := by
      have ha : raw5938step1 = (fun i j => raw5938step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5938step1 raw5938step0; decide +kernel
      have hl : raw5938step1Labels = raw5938step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5938step0 raw5938step0Labels permutation32 permutation3
    _ = mixedMoment B node2405 node2405Labels := by rfl

theorem canonical5939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5939 raw5939Labels = mixedMoment B node2463 node2463Labels := by
  calc
    mixedMoment B raw5939 raw5939Labels = mixedMoment B raw5939step0 raw5939step0Labels := by
      have ha : raw5939step0 = (fun i j => raw5939 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5939step0 raw5939; decide +kernel
      have hl : raw5939step0Labels = raw5939Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5939 raw5939Labels permutation176 permutation3
    _ = mixedMoment B node2463 node2463Labels := by rfl

theorem canonical5940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5940 raw5940Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw5940 raw5940Labels = mixedMoment B raw5940step0 raw5940step0Labels := by
      have hz : ∀ j, raw5940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5940step0 = (fun i j => raw5940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5940step0 raw5940; decide +kernel
      have hl : raw5940step0Labels = raw5940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5940 raw5940Labels permutation346 hz
    mixedMoment B raw5940step0 raw5940step0Labels = mixedMoment B raw5940step1 raw5940step1Labels := by
      have ha : raw5940step1 = (fun i j => raw5940step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5940step1 raw5940step0; decide +kernel
      have hl : raw5940step1Labels = raw5940step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5940step0 raw5940step0Labels permutation34 permutation3
    _ = mixedMoment B node2732 node2732Labels := by rfl

theorem canonical5941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5941 raw5941Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw5941 raw5941Labels = mixedMoment B raw5941step0 raw5941step0Labels := by
      have hz : ∀ j, raw5941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5941step0 = (fun i j => raw5941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5941step0 raw5941; decide +kernel
      have hl : raw5941step0Labels = raw5941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5941 raw5941Labels permutation346 hz
    mixedMoment B raw5941step0 raw5941step0Labels = mixedMoment B raw5941step1 raw5941step1Labels := by
      have ha : raw5941step1 = (fun i j => raw5941step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5941step1 raw5941step0; decide +kernel
      have hl : raw5941step1Labels = raw5941step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5941step0 raw5941step0Labels permutation36 permutation3
    _ = mixedMoment B node2735 node2735Labels := by rfl

theorem canonical5942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5942 raw5942Labels = mixedMoment B node1011 node1011Labels := by
  calc
    mixedMoment B raw5942 raw5942Labels = mixedMoment B raw5942step0 raw5942step0Labels := by
      have hz : ∀ j, raw5942 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5942step0 = (fun i j => raw5942 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5942step0 raw5942; decide +kernel
      have hl : raw5942step0Labels = raw5942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5942 raw5942Labels permutation434 hz
    mixedMoment B raw5942step0 raw5942step0Labels = mixedMoment B raw5942step1 raw5942step1Labels := by
      have hz : ∀ j, raw5942step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5942step1 = (fun i j => raw5942step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5942step1 raw5942step0; decide +kernel
      have hl : raw5942step1Labels = raw5942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5942step0 raw5942step0Labels permutation80 hz
    mixedMoment B raw5942step1 raw5942step1Labels = mixedMoment B raw5942step2 raw5942step2Labels := by
      have ha : raw5942step2 = (fun i j => raw5942step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5942step2 raw5942step1; decide +kernel
      have hl : raw5942step2Labels = raw5942step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5942step1 raw5942step1Labels permutation9 permutation3
    _ = mixedMoment B node1011 node1011Labels := by rfl

theorem canonical5943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5943 raw5943Labels = mixedMoment B node2409 node2409Labels := by
  calc
    mixedMoment B raw5943 raw5943Labels = mixedMoment B raw5943step0 raw5943step0Labels := by
      have hz : ∀ j, raw5943 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5943step0 = (fun i j => raw5943 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5943step0 raw5943; decide +kernel
      have hl : raw5943step0Labels = raw5943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5943 raw5943Labels permutation434 hz
    mixedMoment B raw5943step0 raw5943step0Labels = mixedMoment B raw5943step1 raw5943step1Labels := by
      have hz : ∀ j, raw5943step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5943step1 = (fun i j => raw5943step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5943step1 raw5943step0; decide +kernel
      have hl : raw5943step1Labels = raw5943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5943step0 raw5943step0Labels permutation80 hz
    mixedMoment B raw5943step1 raw5943step1Labels = mixedMoment B raw5943step2 raw5943step2Labels := by
      have ha : raw5943step2 = (fun i j => raw5943step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5943step2 raw5943step1; decide +kernel
      have hl : raw5943step2Labels = raw5943step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5943step1 raw5943step1Labels permutation9 permutation3
    _ = mixedMoment B node2409 node2409Labels := by rfl

theorem canonical5944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5944 raw5944Labels = mixedMoment B node2466 node2466Labels := by
  calc
    mixedMoment B raw5944 raw5944Labels = mixedMoment B raw5944step0 raw5944step0Labels := by
      have hz : ∀ j, raw5944 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5944step0 = (fun i j => raw5944 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5944step0 raw5944; decide +kernel
      have hl : raw5944step0Labels = raw5944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5944 raw5944Labels permutation434 hz
    mixedMoment B raw5944step0 raw5944step0Labels = mixedMoment B raw5944step1 raw5944step1Labels := by
      have ha : raw5944step1 = (fun i j => raw5944step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5944step1 raw5944step0; decide +kernel
      have hl : raw5944step1Labels = raw5944step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5944step0 raw5944step0Labels permutation39 permutation3
    _ = mixedMoment B node2466 node2466Labels := by rfl

theorem canonical5945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5945 raw5945Labels = mixedMoment B node2466 node2466Labels := by
  calc
    mixedMoment B raw5945 raw5945Labels = mixedMoment B raw5945step0 raw5945step0Labels := by
      have hz : ∀ j, raw5945 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5945step0 = (fun i j => raw5945 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5945step0 raw5945; decide +kernel
      have hl : raw5945step0Labels = raw5945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5945 raw5945Labels permutation346 hz
    mixedMoment B raw5945step0 raw5945step0Labels = mixedMoment B raw5945step1 raw5945step1Labels := by
      have ha : raw5945step1 = (fun i j => raw5945step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5945step1 raw5945step0; decide +kernel
      have hl : raw5945step1Labels = raw5945step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5945step0 raw5945step0Labels permutation39 permutation3
    _ = mixedMoment B node2466 node2466Labels := by rfl

theorem canonical5946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5946 raw5946Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw5946 raw5946Labels = mixedMoment B raw5946step0 raw5946step0Labels := by
      have hz : ∀ j, raw5946 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5946step0 = (fun i j => raw5946 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5946step0 raw5946; decide +kernel
      have hl : raw5946step0Labels = raw5946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5946 raw5946Labels permutation434 hz
    mixedMoment B raw5946step0 raw5946step0Labels = mixedMoment B raw5946step1 raw5946step1Labels := by
      have hz : ∀ j, raw5946step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5946step1 = (fun i j => raw5946step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5946step1 raw5946step0; decide +kernel
      have hl : raw5946step1Labels = raw5946step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5946step0 raw5946step0Labels permutation80 hz
    mixedMoment B raw5946step1 raw5946step1Labels = mixedMoment B raw5946step2 raw5946step2Labels := by
      have ha : raw5946step2 = (fun i j => raw5946step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5946step2 raw5946step1; decide +kernel
      have hl : raw5946step2Labels = raw5946step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5946step1 raw5946step1Labels permutation9 permutation3
    _ = mixedMoment B node2737 node2737Labels := by rfl

theorem canonical5947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5947 raw5947Labels = mixedMoment B node1010 node1010Labels := by
  calc
    mixedMoment B raw5947 raw5947Labels = mixedMoment B raw5947step0 raw5947step0Labels := by
      have hz : ∀ j, raw5947 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5947step0 = (fun i j => raw5947 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5947step0 raw5947; decide +kernel
      have hl : raw5947step0Labels = raw5947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5947 raw5947Labels permutation434 hz
    mixedMoment B raw5947step0 raw5947step0Labels = mixedMoment B raw5947step1 raw5947step1Labels := by
      have hz : ∀ j, raw5947step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5947step1 = (fun i j => raw5947step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5947step1 raw5947step0; decide +kernel
      have hl : raw5947step1Labels = raw5947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5947step0 raw5947step0Labels permutation80 hz
    mixedMoment B raw5947step1 raw5947step1Labels = mixedMoment B raw5947step2 raw5947step2Labels := by
      have ha : raw5947step2 = (fun i j => raw5947step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5947step2 raw5947step1; decide +kernel
      have hl : raw5947step2Labels = raw5947step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5947step1 raw5947step1Labels permutation8 permutation3
    _ = mixedMoment B node1010 node1010Labels := by rfl

theorem canonical5948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5948 raw5948Labels = mixedMoment B node2408 node2408Labels := by
  calc
    mixedMoment B raw5948 raw5948Labels = mixedMoment B raw5948step0 raw5948step0Labels := by
      have hz : ∀ j, raw5948 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5948step0 = (fun i j => raw5948 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5948step0 raw5948; decide +kernel
      have hl : raw5948step0Labels = raw5948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5948 raw5948Labels permutation434 hz
    mixedMoment B raw5948step0 raw5948step0Labels = mixedMoment B raw5948step1 raw5948step1Labels := by
      have hz : ∀ j, raw5948step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5948step1 = (fun i j => raw5948step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5948step1 raw5948step0; decide +kernel
      have hl : raw5948step1Labels = raw5948step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5948step0 raw5948step0Labels permutation80 hz
    mixedMoment B raw5948step1 raw5948step1Labels = mixedMoment B raw5948step2 raw5948step2Labels := by
      have ha : raw5948step2 = (fun i j => raw5948step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5948step2 raw5948step1; decide +kernel
      have hl : raw5948step2Labels = raw5948step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5948step1 raw5948step1Labels permutation8 permutation3
    _ = mixedMoment B node2408 node2408Labels := by rfl

theorem canonical5949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5949 raw5949Labels = mixedMoment B node2465 node2465Labels := by
  calc
    mixedMoment B raw5949 raw5949Labels = mixedMoment B raw5949step0 raw5949step0Labels := by
      have hz : ∀ j, raw5949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5949step0 = (fun i j => raw5949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5949step0 raw5949; decide +kernel
      have hl : raw5949step0Labels = raw5949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5949 raw5949Labels permutation434 hz
    mixedMoment B raw5949step0 raw5949step0Labels = mixedMoment B raw5949step1 raw5949step1Labels := by
      have ha : raw5949step1 = (fun i j => raw5949step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5949step1 raw5949step0; decide +kernel
      have hl : raw5949step1Labels = raw5949step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5949step0 raw5949step0Labels permutation38 permutation3
    _ = mixedMoment B node2465 node2465Labels := by rfl

theorem canonical5950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5950 raw5950Labels = mixedMoment B node2465 node2465Labels := by
  calc
    mixedMoment B raw5950 raw5950Labels = mixedMoment B raw5950step0 raw5950step0Labels := by
      have hz : ∀ j, raw5950 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5950step0 = (fun i j => raw5950 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5950step0 raw5950; decide +kernel
      have hl : raw5950step0Labels = raw5950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5950 raw5950Labels permutation346 hz
    mixedMoment B raw5950step0 raw5950step0Labels = mixedMoment B raw5950step1 raw5950step1Labels := by
      have ha : raw5950step1 = (fun i j => raw5950step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5950step1 raw5950step0; decide +kernel
      have hl : raw5950step1Labels = raw5950step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5950step0 raw5950step0Labels permutation38 permutation3
    _ = mixedMoment B node2465 node2465Labels := by rfl

theorem canonical5951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5951 raw5951Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw5951 raw5951Labels = mixedMoment B raw5951step0 raw5951step0Labels := by
      have hz : ∀ j, raw5951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5951step0 = (fun i j => raw5951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5951step0 raw5951; decide +kernel
      have hl : raw5951step0Labels = raw5951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5951 raw5951Labels permutation434 hz
    mixedMoment B raw5951step0 raw5951step0Labels = mixedMoment B raw5951step1 raw5951step1Labels := by
      have hz : ∀ j, raw5951step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5951step1 = (fun i j => raw5951step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5951step1 raw5951step0; decide +kernel
      have hl : raw5951step1Labels = raw5951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5951step0 raw5951step0Labels permutation80 hz
    mixedMoment B raw5951step1 raw5951step1Labels = mixedMoment B raw5951step2 raw5951step2Labels := by
      have ha : raw5951step2 = (fun i j => raw5951step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5951step2 raw5951step1; decide +kernel
      have hl : raw5951step2Labels = raw5951step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5951step1 raw5951step1Labels permutation8 permutation3
    _ = mixedMoment B node2734 node2734Labels := by rfl

theorem canonical5982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5982 raw5982Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw5982 raw5982Labels = mixedMoment B raw5982step0 raw5982step0Labels := by
      have hz : ∀ j, raw5982 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5982step0 = (fun i j => raw5982 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5982step0 raw5982; decide +kernel
      have hl : raw5982step0Labels = raw5982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5982 raw5982Labels permutation434 hz
    mixedMoment B raw5982step0 raw5982step0Labels = mixedMoment B raw5982step1 raw5982step1Labels := by
      have hz : ∀ j, raw5982step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5982step1 = (fun i j => raw5982step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5982step1 raw5982step0; decide +kernel
      have hl : raw5982step1Labels = raw5982step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5982step0 raw5982step0Labels permutation80 hz
    mixedMoment B raw5982step1 raw5982step1Labels = mixedMoment B raw5982step2 raw5982step2Labels := by
      have ha : raw5982step2 = (fun i j => raw5982step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5982step2 raw5982step1; decide +kernel
      have hl : raw5982step2Labels = raw5982step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5982step1 raw5982step1Labels permutation25 permutation4
    _ = mixedMoment B node2777 node2777Labels := by rfl

theorem canonical5983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5983 raw5983Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw5983 raw5983Labels = mixedMoment B raw5983step0 raw5983step0Labels := by
      have hz : ∀ j, raw5983 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5983step0 = (fun i j => raw5983 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5983step0 raw5983; decide +kernel
      have hl : raw5983step0Labels = raw5983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5983 raw5983Labels permutation434 hz
    mixedMoment B raw5983step0 raw5983step0Labels = mixedMoment B raw5983step1 raw5983step1Labels := by
      have hz : ∀ j, raw5983step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5983step1 = (fun i j => raw5983step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5983step1 raw5983step0; decide +kernel
      have hl : raw5983step1Labels = raw5983step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5983step0 raw5983step0Labels permutation80 hz
    mixedMoment B raw5983step1 raw5983step1Labels = mixedMoment B raw5983step2 raw5983step2Labels := by
      have ha : raw5983step2 = (fun i j => raw5983step1 (permutation24 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5983step2 raw5983step1; decide +kernel
      have hl : raw5983step2Labels = raw5983step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5983step1 raw5983step1Labels permutation24 permutation4
    _ = mixedMoment B node2774 node2774Labels := by rfl

theorem canonical5984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5984 raw5984Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw5984 raw5984Labels = mixedMoment B raw5984step0 raw5984step0Labels := by
      have hz : ∀ j, raw5984 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5984step0 = (fun i j => raw5984 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5984step0 raw5984; decide +kernel
      have hl : raw5984step0Labels = raw5984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5984 raw5984Labels permutation434 hz
    mixedMoment B raw5984step0 raw5984step0Labels = mixedMoment B raw5984step1 raw5984step1Labels := by
      have ha : raw5984step1 = (fun i j => raw5984step0 (permutation123 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5984step1 raw5984step0; decide +kernel
      have hl : raw5984step1Labels = raw5984step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5984step0 raw5984step0Labels permutation123 permutation4
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical5985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5985 raw5985Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw5985 raw5985Labels = mixedMoment B raw5985step0 raw5985step0Labels := by
      have hz : ∀ j, raw5985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5985step0 = (fun i j => raw5985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5985step0 raw5985; decide +kernel
      have hl : raw5985step0Labels = raw5985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5985 raw5985Labels permutation346 hz
    mixedMoment B raw5985step0 raw5985step0Labels = mixedMoment B raw5985step1 raw5985step1Labels := by
      have ha : raw5985step1 = (fun i j => raw5985step0 (permutation123 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5985step1 raw5985step0; decide +kernel
      have hl : raw5985step1Labels = raw5985step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5985step0 raw5985step0Labels permutation123 permutation4
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical5986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5986 raw5986Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw5986 raw5986Labels = mixedMoment B raw5986step0 raw5986step0Labels := by
      have hz : ∀ j, raw5986 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5986step0 = (fun i j => raw5986 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5986step0 raw5986; decide +kernel
      have hl : raw5986step0Labels = raw5986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5986 raw5986Labels permutation434 hz
    mixedMoment B raw5986step0 raw5986step0Labels = mixedMoment B raw5986step1 raw5986step1Labels := by
      have hz : ∀ j, raw5986step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5986step1 = (fun i j => raw5986step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5986step1 raw5986step0; decide +kernel
      have hl : raw5986step1Labels = raw5986step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5986step0 raw5986step0Labels permutation80 hz
    mixedMoment B raw5986step1 raw5986step1Labels = mixedMoment B raw5986step2 raw5986step2Labels := by
      have ha : raw5986step2 = (fun i j => raw5986step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5986step2 raw5986step1; decide +kernel
      have hl : raw5986step2Labels = raw5986step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5986step1 raw5986step1Labels permutation29 permutation2
    mixedMoment B raw5986step2 raw5986step2Labels = mixedMoment B raw5986step3 raw5986step3Labels := by
      have ha : raw5986step3 = -raw5986step2 := by apply Matrix.ext; change ∀ i j, raw5986step3 i j = -(raw5986step2 i j); unfold raw5986step3 raw5986step2; decide +kernel
      have hl : raw5986step3Labels = raw5986step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3907 node3907Labels := by rfl

theorem canonical5987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5987 raw5987Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw5987 raw5987Labels = mixedMoment B raw5987step0 raw5987step0Labels := by
      have hz : ∀ j, raw5987 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5987step0 = (fun i j => raw5987 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5987step0 raw5987; decide +kernel
      have hl : raw5987step0Labels = raw5987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5987 raw5987Labels permutation434 hz
    mixedMoment B raw5987step0 raw5987step0Labels = mixedMoment B raw5987step1 raw5987step1Labels := by
      have hz : ∀ j, raw5987step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5987step1 = (fun i j => raw5987step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5987step1 raw5987step0; decide +kernel
      have hl : raw5987step1Labels = raw5987step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5987step0 raw5987step0Labels permutation80 hz
    mixedMoment B raw5987step1 raw5987step1Labels = mixedMoment B raw5987step2 raw5987step2Labels := by
      have ha : raw5987step2 = (fun i j => raw5987step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5987step2 raw5987step1; decide +kernel
      have hl : raw5987step2Labels = raw5987step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5987step1 raw5987step1Labels permutation20 permutation4
    _ = mixedMoment B node2782 node2782Labels := by rfl

theorem canonical5988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5988 raw5988Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw5988 raw5988Labels = mixedMoment B raw5988step0 raw5988step0Labels := by
      have hz : ∀ j, raw5988 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5988step0 = (fun i j => raw5988 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5988step0 raw5988; decide +kernel
      have hl : raw5988step0Labels = raw5988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5988 raw5988Labels permutation434 hz
    mixedMoment B raw5988step0 raw5988step0Labels = mixedMoment B raw5988step1 raw5988step1Labels := by
      have hz : ∀ j, raw5988step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5988step1 = (fun i j => raw5988step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5988step1 raw5988step0; decide +kernel
      have hl : raw5988step1Labels = raw5988step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5988step0 raw5988step0Labels permutation80 hz
    mixedMoment B raw5988step1 raw5988step1Labels = mixedMoment B raw5988step2 raw5988step2Labels := by
      have ha : raw5988step2 = (fun i j => raw5988step1 (permutation20 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5988step2 raw5988step1; decide +kernel
      have hl : raw5988step2Labels = raw5988step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5988step1 raw5988step1Labels permutation20 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical5989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5989 raw5989Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw5989 raw5989Labels = mixedMoment B raw5989step0 raw5989step0Labels := by
      have hz : ∀ j, raw5989 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5989step0 = (fun i j => raw5989 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5989step0 raw5989; decide +kernel
      have hl : raw5989step0Labels = raw5989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5989 raw5989Labels permutation434 hz
    mixedMoment B raw5989step0 raw5989step0Labels = mixedMoment B raw5989step1 raw5989step1Labels := by
      have hz : ∀ j, raw5989step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5989step1 = (fun i j => raw5989step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5989step1 raw5989step0; decide +kernel
      have hl : raw5989step1Labels = raw5989step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5989step0 raw5989step0Labels permutation80 hz
    mixedMoment B raw5989step1 raw5989step1Labels = mixedMoment B raw5989step2 raw5989step2Labels := by
      have ha : raw5989step2 = (fun i j => raw5989step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5989step2 raw5989step1; decide +kernel
      have hl : raw5989step2Labels = raw5989step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5989step1 raw5989step1Labels permutation10 permutation2
    _ = mixedMoment B node1436 node1436Labels := by rfl

theorem canonical5990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5990 raw5990Labels = mixedMoment B node1422 node1422Labels := by
  calc
    mixedMoment B raw5990 raw5990Labels = mixedMoment B raw5990step0 raw5990step0Labels := by
      have hz : ∀ j, raw5990 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5990step0 = (fun i j => raw5990 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5990step0 raw5990; decide +kernel
      have hl : raw5990step0Labels = raw5990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5990 raw5990Labels permutation434 hz
    mixedMoment B raw5990step0 raw5990step0Labels = mixedMoment B raw5990step1 raw5990step1Labels := by
      have ha : raw5990step1 = (fun i j => raw5990step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5990step1 raw5990step0; decide +kernel
      have hl : raw5990step1Labels = raw5990step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5990step0 raw5990step0Labels permutation34 permutation2
    _ = mixedMoment B node1422 node1422Labels := by rfl

theorem canonical5991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5991 raw5991Labels = mixedMoment B node1422 node1422Labels := by
  calc
    mixedMoment B raw5991 raw5991Labels = mixedMoment B raw5991step0 raw5991step0Labels := by
      have hz : ∀ j, raw5991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5991step0 = (fun i j => raw5991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5991step0 raw5991; decide +kernel
      have hl : raw5991step0Labels = raw5991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5991 raw5991Labels permutation346 hz
    mixedMoment B raw5991step0 raw5991step0Labels = mixedMoment B raw5991step1 raw5991step1Labels := by
      have ha : raw5991step1 = (fun i j => raw5991step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5991step1 raw5991step0; decide +kernel
      have hl : raw5991step1Labels = raw5991step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5991step0 raw5991step0Labels permutation34 permutation2
    _ = mixedMoment B node1422 node1422Labels := by rfl

theorem canonical5992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5992 raw5992Labels = mixedMoment B node1282 node1282Labels := by
  calc
    mixedMoment B raw5992 raw5992Labels = mixedMoment B raw5992step0 raw5992step0Labels := by
      have hz : ∀ j, raw5992 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5992step0 = (fun i j => raw5992 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5992step0 raw5992; decide +kernel
      have hl : raw5992step0Labels = raw5992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5992 raw5992Labels permutation434 hz
    mixedMoment B raw5992step0 raw5992step0Labels = mixedMoment B raw5992step1 raw5992step1Labels := by
      have hz : ∀ j, raw5992step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5992step1 = (fun i j => raw5992step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5992step1 raw5992step0; decide +kernel
      have hl : raw5992step1Labels = raw5992step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5992step0 raw5992step0Labels permutation80 hz
    mixedMoment B raw5992step1 raw5992step1Labels = mixedMoment B raw5992step2 raw5992step2Labels := by
      have ha : raw5992step2 = (fun i j => raw5992step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5992step2 raw5992step1; decide +kernel
      have hl : raw5992step2Labels = raw5992step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5992step1 raw5992step1Labels permutation25 permutation4
    _ = mixedMoment B node1282 node1282Labels := by rfl

theorem canonical5993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5993 raw5993Labels = mixedMoment B node1424 node1424Labels := by
  calc
    mixedMoment B raw5993 raw5993Labels = mixedMoment B raw5993step0 raw5993step0Labels := by
      have hz : ∀ j, raw5993 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5993step0 = (fun i j => raw5993 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5993step0 raw5993; decide +kernel
      have hl : raw5993step0Labels = raw5993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5993 raw5993Labels permutation434 hz
    mixedMoment B raw5993step0 raw5993step0Labels = mixedMoment B raw5993step1 raw5993step1Labels := by
      have hz : ∀ j, raw5993step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5993step1 = (fun i j => raw5993step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5993step1 raw5993step0; decide +kernel
      have hl : raw5993step1Labels = raw5993step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5993step0 raw5993step0Labels permutation80 hz
    _ = mixedMoment B node1424 node1424Labels := by rfl

theorem canonical5994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5994 raw5994Labels = mixedMoment B node2759 node2759Labels := by
  calc
    mixedMoment B raw5994 raw5994Labels = mixedMoment B raw5994step0 raw5994step0Labels := by
      have hz : ∀ j, raw5994 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5994step0 = (fun i j => raw5994 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5994step0 raw5994; decide +kernel
      have hl : raw5994step0Labels = raw5994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5994 raw5994Labels permutation434 hz
    mixedMoment B raw5994step0 raw5994step0Labels = mixedMoment B raw5994step1 raw5994step1Labels := by
      have ha : raw5994step1 = (fun i j => raw5994step0 (permutation115 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5994step1 raw5994step0; decide +kernel
      have hl : raw5994step1Labels = raw5994step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5994step0 raw5994step0Labels permutation115 permutation4
    _ = mixedMoment B node2759 node2759Labels := by rfl

theorem canonical5995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5995 raw5995Labels = mixedMoment B node2759 node2759Labels := by
  calc
    mixedMoment B raw5995 raw5995Labels = mixedMoment B raw5995step0 raw5995step0Labels := by
      have hz : ∀ j, raw5995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5995step0 = (fun i j => raw5995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5995step0 raw5995; decide +kernel
      have hl : raw5995step0Labels = raw5995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5995 raw5995Labels permutation346 hz
    mixedMoment B raw5995step0 raw5995step0Labels = mixedMoment B raw5995step1 raw5995step1Labels := by
      have ha : raw5995step1 = (fun i j => raw5995step0 (permutation115 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5995step1 raw5995step0; decide +kernel
      have hl : raw5995step1Labels = raw5995step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5995step0 raw5995step0Labels permutation115 permutation4
    _ = mixedMoment B node2759 node2759Labels := by rfl

theorem canonical5996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5996 raw5996Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw5996 raw5996Labels = mixedMoment B raw5996step0 raw5996step0Labels := by
      have hz : ∀ j, raw5996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5996step0 = (fun i j => raw5996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5996step0 raw5996; decide +kernel
      have hl : raw5996step0Labels = raw5996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5996 raw5996Labels permutation434 hz
    mixedMoment B raw5996step0 raw5996step0Labels = mixedMoment B raw5996step1 raw5996step1Labels := by
      have hz : ∀ j, raw5996step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5996step1 = (fun i j => raw5996step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5996step1 raw5996step0; decide +kernel
      have hl : raw5996step1Labels = raw5996step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5996step0 raw5996step0Labels permutation80 hz
    mixedMoment B raw5996step1 raw5996step1Labels = mixedMoment B raw5996step2 raw5996step2Labels := by
      have ha : raw5996step2 = (fun i j => raw5996step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5996step2 raw5996step1; decide +kernel
      have hl : raw5996step2Labels = raw5996step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5996step1 raw5996step1Labels permutation10 permutation2
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical5997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5997 raw5997Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw5997 raw5997Labels = mixedMoment B raw5997step0 raw5997step0Labels := by
      have hz : ∀ j, raw5997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5997step0 = (fun i j => raw5997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5997step0 raw5997; decide +kernel
      have hl : raw5997step0Labels = raw5997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5997 raw5997Labels permutation434 hz
    mixedMoment B raw5997step0 raw5997step0Labels = mixedMoment B raw5997step1 raw5997step1Labels := by
      have hz : ∀ j, raw5997step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5997step1 = (fun i j => raw5997step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5997step1 raw5997step0; decide +kernel
      have hl : raw5997step1Labels = raw5997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5997step0 raw5997step0Labels permutation80 hz
    mixedMoment B raw5997step1 raw5997step1Labels = mixedMoment B raw5997step2 raw5997step2Labels := by
      have ha : raw5997step2 = (fun i j => raw5997step1 (permutation23 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5997step2 raw5997step1; decide +kernel
      have hl : raw5997step2Labels = raw5997step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5997step1 raw5997step1Labels permutation23 permutation4
    _ = mixedMoment B node2769 node2769Labels := by rfl

theorem canonical5998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5998 raw5998Labels = mixedMoment B node2582 node2582Labels := by
  calc
    mixedMoment B raw5998 raw5998Labels = mixedMoment B raw5998step0 raw5998step0Labels := by
      have hz : ∀ j, raw5998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5998step0 = (fun i j => raw5998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5998step0 raw5998; decide +kernel
      have hl : raw5998step0Labels = raw5998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5998 raw5998Labels permutation434 hz
    mixedMoment B raw5998step0 raw5998step0Labels = mixedMoment B raw5998step1 raw5998step1Labels := by
      have ha : raw5998step1 = (fun i j => raw5998step0 (permutation120 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5998step1 raw5998step0; decide +kernel
      have hl : raw5998step1Labels = raw5998step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5998step0 raw5998step0Labels permutation120 permutation4
    _ = mixedMoment B node2582 node2582Labels := by rfl

theorem canonical5999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5999 raw5999Labels = mixedMoment B node2582 node2582Labels := by
  calc
    mixedMoment B raw5999 raw5999Labels = mixedMoment B raw5999step0 raw5999step0Labels := by
      have hz : ∀ j, raw5999 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5999step0 = (fun i j => raw5999 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5999step0 raw5999; decide +kernel
      have hl : raw5999step0Labels = raw5999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5999 raw5999Labels permutation346 hz
    mixedMoment B raw5999step0 raw5999step0Labels = mixedMoment B raw5999step1 raw5999step1Labels := by
      have ha : raw5999step1 = (fun i j => raw5999step0 (permutation120 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5999step1 raw5999step0; decide +kernel
      have hl : raw5999step1Labels = raw5999step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5999step0 raw5999step0Labels permutation120 permutation4
    _ = mixedMoment B node2582 node2582Labels := by rfl

theorem canonical6000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6000 raw6000Labels = mixedMoment B node1283 node1283Labels := by
  calc
    mixedMoment B raw6000 raw6000Labels = mixedMoment B raw6000step0 raw6000step0Labels := by
      have hz : ∀ j, raw6000 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6000step0 = (fun i j => raw6000 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6000step0 raw6000; decide +kernel
      have hl : raw6000step0Labels = raw6000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6000 raw6000Labels permutation434 hz
    mixedMoment B raw6000step0 raw6000step0Labels = mixedMoment B raw6000step1 raw6000step1Labels := by
      have hz : ∀ j, raw6000step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6000step1 = (fun i j => raw6000step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6000step1 raw6000step0; decide +kernel
      have hl : raw6000step1Labels = raw6000step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6000step0 raw6000step0Labels permutation80 hz
    mixedMoment B raw6000step1 raw6000step1Labels = mixedMoment B raw6000step2 raw6000step2Labels := by
      have ha : raw6000step2 = (fun i j => raw6000step1 (permutation24 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6000step2 raw6000step1; decide +kernel
      have hl : raw6000step2Labels = raw6000step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6000step1 raw6000step1Labels permutation24 permutation4
    _ = mixedMoment B node1283 node1283Labels := by rfl

theorem canonical6001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6001 raw6001Labels = mixedMoment B node2651 node2651Labels := by
  calc
    mixedMoment B raw6001 raw6001Labels = mixedMoment B raw6001step0 raw6001step0Labels := by
      have hz : ∀ j, raw6001 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6001step0 = (fun i j => raw6001 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6001step0 raw6001; decide +kernel
      have hl : raw6001step0Labels = raw6001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6001 raw6001Labels permutation434 hz
    mixedMoment B raw6001step0 raw6001step0Labels = mixedMoment B raw6001step1 raw6001step1Labels := by
      have hz : ∀ j, raw6001step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6001step1 = (fun i j => raw6001step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6001step1 raw6001step0; decide +kernel
      have hl : raw6001step1Labels = raw6001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6001step0 raw6001step0Labels permutation80 hz
    mixedMoment B raw6001step1 raw6001step1Labels = mixedMoment B raw6001step2 raw6001step2Labels := by
      have ha : raw6001step2 = (fun i j => raw6001step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6001step2 raw6001step1; decide +kernel
      have hl : raw6001step2Labels = raw6001step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6001step1 raw6001step1Labels permutation31 permutation2
    mixedMoment B raw6001step2 raw6001step2Labels = mixedMoment B raw6001step3 raw6001step3Labels := by
      have ha : raw6001step3 = -raw6001step2 := by apply Matrix.ext; change ∀ i j, raw6001step3 i j = -(raw6001step2 i j); unfold raw6001step3 raw6001step2; decide +kernel
      have hl : raw6001step3Labels = raw6001step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2651 node2651Labels := by rfl

theorem canonical6002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6002 raw6002Labels = mixedMoment B node2580 node2580Labels := by
  calc
    mixedMoment B raw6002 raw6002Labels = mixedMoment B raw6002step0 raw6002step0Labels := by
      have ha : raw6002step0 = (fun i j => raw6002 (permutation552 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6002step0 raw6002; decide +kernel
      have hl : raw6002step0Labels = raw6002Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6002 raw6002Labels permutation552 permutation4
    _ = mixedMoment B node2580 node2580Labels := by rfl

theorem canonical6003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6003 raw6003Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw6003 raw6003Labels = mixedMoment B raw6003step0 raw6003step0Labels := by
      have hz : ∀ j, raw6003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6003step0 = (fun i j => raw6003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6003step0 raw6003; decide +kernel
      have hl : raw6003step0Labels = raw6003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6003 raw6003Labels permutation434 hz
    mixedMoment B raw6003step0 raw6003step0Labels = mixedMoment B raw6003step1 raw6003step1Labels := by
      have ha : raw6003step1 = (fun i j => raw6003step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6003step1 raw6003step0; decide +kernel
      have hl : raw6003step1Labels = raw6003step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6003step0 raw6003step0Labels permutation44 permutation2
    _ = mixedMoment B node3038 node3038Labels := by rfl

theorem canonical6004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6004 raw6004Labels = mixedMoment B node2600 node2600Labels := by
  calc
    mixedMoment B raw6004 raw6004Labels = mixedMoment B raw6004step0 raw6004step0Labels := by
      have hz : ∀ j, raw6004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6004step0 = (fun i j => raw6004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6004step0 raw6004; decide +kernel
      have hl : raw6004step0Labels = raw6004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6004 raw6004Labels permutation434 hz
    mixedMoment B raw6004step0 raw6004step0Labels = mixedMoment B raw6004step1 raw6004step1Labels := by
      have ha : raw6004step1 = (fun i j => raw6004step0 (permutation119 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6004step1 raw6004step0; decide +kernel
      have hl : raw6004step1Labels = raw6004step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6004step0 raw6004step0Labels permutation119 permutation4
    _ = mixedMoment B node2600 node2600Labels := by rfl

theorem canonical6005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6005 raw6005Labels = mixedMoment B node2580 node2580Labels := by
  calc
    mixedMoment B raw6005 raw6005Labels = mixedMoment B raw6005step0 raw6005step0Labels := by
      have ha : raw6005step0 = (fun i j => raw6005 (permutation568 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6005step0 raw6005; decide +kernel
      have hl : raw6005step0Labels = raw6005Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6005 raw6005Labels permutation568 permutation4
    _ = mixedMoment B node2580 node2580Labels := by rfl

theorem canonical6006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6006 raw6006Labels = mixedMoment B node1280 node1280Labels := by
  calc
    mixedMoment B raw6006 raw6006Labels = mixedMoment B raw6006step0 raw6006step0Labels := by
      have hz : ∀ j, raw6006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6006step0 = (fun i j => raw6006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6006step0 raw6006; decide +kernel
      have hl : raw6006step0Labels = raw6006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6006 raw6006Labels permutation434 hz
    mixedMoment B raw6006step0 raw6006step0Labels = mixedMoment B raw6006step1 raw6006step1Labels := by
      have ha : raw6006step1 = (fun i j => raw6006step0 (permutation127 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6006step1 raw6006step0; decide +kernel
      have hl : raw6006step1Labels = raw6006step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6006step0 raw6006step0Labels permutation127 permutation4
    _ = mixedMoment B node1280 node1280Labels := by rfl

theorem canonical6007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6007 raw6007Labels = mixedMoment B node2647 node2647Labels := by
  calc
    mixedMoment B raw6007 raw6007Labels = mixedMoment B raw6007step0 raw6007step0Labels := by
      have hz : ∀ j, raw6007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6007step0 = (fun i j => raw6007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6007step0 raw6007; decide +kernel
      have hl : raw6007step0Labels = raw6007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6007 raw6007Labels permutation434 hz
    mixedMoment B raw6007step0 raw6007step0Labels = mixedMoment B raw6007step1 raw6007step1Labels := by
      have ha : raw6007step1 = (fun i j => raw6007step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6007step1 raw6007step0; decide +kernel
      have hl : raw6007step1Labels = raw6007step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6007step0 raw6007step0Labels permutation149 permutation2
    mixedMoment B raw6007step1 raw6007step1Labels = mixedMoment B raw6007step2 raw6007step2Labels := by
      have ha : raw6007step2 = -raw6007step1 := by apply Matrix.ext; change ∀ i j, raw6007step2 i j = -(raw6007step1 i j); unfold raw6007step2 raw6007step1; decide +kernel
      have hl : raw6007step2Labels = raw6007step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2647 node2647Labels := by rfl

theorem canonical6008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6008 raw6008Labels = mixedMoment B node1280 node1280Labels := by
  calc
    mixedMoment B raw6008 raw6008Labels = mixedMoment B raw6008step0 raw6008step0Labels := by
      have hz : ∀ j, raw6008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6008step0 = (fun i j => raw6008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6008step0 raw6008; decide +kernel
      have hl : raw6008step0Labels = raw6008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6008 raw6008Labels permutation346 hz
    mixedMoment B raw6008step0 raw6008step0Labels = mixedMoment B raw6008step1 raw6008step1Labels := by
      have ha : raw6008step1 = (fun i j => raw6008step0 (permutation127 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6008step1 raw6008step0; decide +kernel
      have hl : raw6008step1Labels = raw6008step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6008step0 raw6008step0Labels permutation127 permutation4
    _ = mixedMoment B node1280 node1280Labels := by rfl

theorem canonical6009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6009 raw6009Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw6009 raw6009Labels = mixedMoment B raw6009step0 raw6009step0Labels := by
      have hz : ∀ j, raw6009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6009step0 = (fun i j => raw6009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6009step0 raw6009; decide +kernel
      have hl : raw6009step0Labels = raw6009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6009 raw6009Labels permutation434 hz
    mixedMoment B raw6009step0 raw6009step0Labels = mixedMoment B raw6009step1 raw6009step1Labels := by
      have hz : ∀ j, raw6009step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6009step1 = (fun i j => raw6009step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6009step1 raw6009step0; decide +kernel
      have hl : raw6009step1Labels = raw6009step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6009step0 raw6009step0Labels permutation80 hz
    mixedMoment B raw6009step1 raw6009step1Labels = mixedMoment B raw6009step2 raw6009step2Labels := by
      have ha : raw6009step2 = (fun i j => raw6009step1 (permutation23 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6009step2 raw6009step1; decide +kernel
      have hl : raw6009step2Labels = raw6009step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6009step1 raw6009step1Labels permutation23 permutation4
    _ = mixedMoment B node1306 node1306Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5185 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5185 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5185 = injectiveMoment H raw5185step0 := by
      have hz : ∀ j, raw5185 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5185step0 = (fun i j => raw5185 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5185 permutation27 hz
    injectiveMoment H raw5185step0 = injectiveMoment H raw5185step1 := by
      have hz : ∀ j, raw5185step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5185step1 = (fun i j => raw5185step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5185step0 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical281
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9013 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9013 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9013 = injectiveMoment H raw9013step0 := by
      have hz : ∀ j, raw9013 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9013step0 = (fun i j => raw9013 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9013 permutation9 hz
    injectiveMoment H raw9013step0 = injectiveMoment H raw9013step1 := by
      have heq : raw9013step1 = (fun i j => raw9013step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9013step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

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

theorem sound203 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node203 = Sparse.eval value203 (momentVector H) := by
  have heq : pivotMatrix203 = (fun u v => node203 (pivotPermutation203 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node203 = injectiveMoment H pivotMatrix203 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix203 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix203 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (0 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (1 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (2 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node203 + (injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value203, value36, value41, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3963 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3963 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw3963 = injectiveMoment H raw3963step0 := by
      have heq : raw3963step0 = -raw3963 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3963).symm
    injectiveMoment H raw3963step0 = injectiveMoment H raw3963step1 := by
      have heq : raw3963step1 = (fun i j => raw3963step0 (permutation10 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3963step0 permutation10 permutation8
    _ = injectiveMoment H node203 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SinglePriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node496 node496Labels = Sparse.eval singlePairValue496 (familyPairVector B) := by
  have hp := single_label_three B hB node496
  have hl : node496Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node496 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 1) = PairSemantics.raw5185 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node496 PairSemantics.raw5185; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5185 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 2) = PairSemantics.raw9013 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node496 PairSemantics.raw9013; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9013 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 3) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node496 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value203 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 4) = PairSemantics.raw3963 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node496 PairSemantics.raw3963; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3963 hH).trans (PairSemantics.sound203 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue496, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value46, PairSemantics.value203, Sparse.eval] at hp ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3889 node3889Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node496 node496Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw546 singletonSmall3889
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3889) = raw546Labels := by decide +kernel
  rw [hl, canonical546 B hB] at h
  have hc0 : mixedMoment B raw546 (Fin.cases (0 : Fin 1) singletonSmall3889) =
      mixedMoment B node496 node496Labels := by
    have ha : raw546 = raw547 := by apply Matrix.ext; unfold raw546 raw547; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3889 = raw547Labels := by decide +kernel
    rw [ha, hj, canonical547 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SoundPriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node496 node496Labels = Sparse.eval nodeValue496 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue496 (familyPairVector B) := singlePair496 B _hB
    _ = _ := by norm_num [singlePairValue496, nodeValue496, Sparse.eval, mixedVector] <;> ring

theorem sound2279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2279 node2279Labels = Sparse.eval nodeValue2279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2279) = mixedMoment B node2279 node2279Labels := rfl
  simpa [nodeValue2279, Sparse.eval] using hc.symm

theorem sound3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3054 node3054Labels = Sparse.eval nodeValue3054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3054) = mixedMoment B node3054 node3054Labels := rfl
  simpa [nodeValue3054, Sparse.eval] using hc.symm

theorem sound3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3626 node3626Labels = Sparse.eval nodeValue3626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3626) = mixedMoment B node3626 node3626Labels := rfl
  simpa [nodeValue3626, Sparse.eval] using hc.symm

theorem sound3907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3907 node3907Labels = Sparse.eval nodeValue3907 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3907) = mixedMoment B node3907 node3907Labels := rfl
  simpa [nodeValue3907, Sparse.eval] using hc.symm

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

theorem sound1006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1006 node1006Labels = Sparse.eval nodeValue1006 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1006) = mixedMoment B node1006 node1006Labels := rfl
  simpa [nodeValue1006, Sparse.eval] using hc.symm

theorem sound1010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1010 node1010Labels = Sparse.eval nodeValue1010 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1010) = mixedMoment B node1010 node1010Labels := rfl
  simpa [nodeValue1010, Sparse.eval] using hc.symm

theorem sound1011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1011 node1011Labels = Sparse.eval nodeValue1011 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1011) = mixedMoment B node1011 node1011Labels := rfl
  simpa [nodeValue1011, Sparse.eval] using hc.symm

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

theorem sound1084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1084 node1084Labels = Sparse.eval nodeValue1084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1084) = mixedMoment B node1084 node1084Labels := rfl
  simpa [nodeValue1084, Sparse.eval] using hc.symm

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

theorem sound1238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1238 node1238Labels = Sparse.eval nodeValue1238 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1238) = mixedMoment B node1238 node1238Labels := rfl
  simpa [nodeValue1238, Sparse.eval] using hc.symm

theorem sound1244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1244 node1244Labels = Sparse.eval nodeValue1244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1244) = mixedMoment B node1244 node1244Labels := rfl
  simpa [nodeValue1244, Sparse.eval] using hc.symm

theorem sound1245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1245 node1245Labels = Sparse.eval nodeValue1245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1245) = mixedMoment B node1245 node1245Labels := rfl
  simpa [nodeValue1245, Sparse.eval] using hc.symm

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

theorem sound1280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1280 node1280Labels = Sparse.eval nodeValue1280 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1280) = mixedMoment B node1280 node1280Labels := rfl
  simpa [nodeValue1280, Sparse.eval] using hc.symm

theorem sound1282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1282 node1282Labels = Sparse.eval nodeValue1282 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1282) = mixedMoment B node1282 node1282Labels := rfl
  simpa [nodeValue1282, Sparse.eval] using hc.symm

theorem sound1283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1283 node1283Labels = Sparse.eval nodeValue1283 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1283) = mixedMoment B node1283 node1283Labels := rfl
  simpa [nodeValue1283, Sparse.eval] using hc.symm

theorem sound1306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1306 node1306Labels = Sparse.eval nodeValue1306 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1306) = mixedMoment B node1306 node1306Labels := rfl
  simpa [nodeValue1306, Sparse.eval] using hc.symm

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

theorem sound1422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1422 node1422Labels = Sparse.eval nodeValue1422 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1422) = mixedMoment B node1422 node1422Labels := rfl
  simpa [nodeValue1422, Sparse.eval] using hc.symm

theorem sound1424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1424 node1424Labels = Sparse.eval nodeValue1424 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1424) = mixedMoment B node1424 node1424Labels := rfl
  simpa [nodeValue1424, Sparse.eval] using hc.symm

theorem sound1436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1436 node1436Labels = Sparse.eval nodeValue1436 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1436) = mixedMoment B node1436 node1436Labels := rfl
  simpa [nodeValue1436, Sparse.eval] using hc.symm

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

theorem sound2133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2133 node2133Labels = Sparse.eval nodeValue2133 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2133) = mixedMoment B node2133 node2133Labels := rfl
  simpa [nodeValue2133, Sparse.eval] using hc.symm

theorem sound2136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2136 node2136Labels = Sparse.eval nodeValue2136 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2136) = mixedMoment B node2136 node2136Labels := rfl
  simpa [nodeValue2136, Sparse.eval] using hc.symm

theorem sound2138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2138 node2138Labels = Sparse.eval nodeValue2138 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2138) = mixedMoment B node2138 node2138Labels := rfl
  simpa [nodeValue2138, Sparse.eval] using hc.symm

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

theorem sound2405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2405 node2405Labels = Sparse.eval nodeValue2405 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2405) = mixedMoment B node2405 node2405Labels := rfl
  simpa [nodeValue2405, Sparse.eval] using hc.symm

theorem sound2408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2408 node2408Labels = Sparse.eval nodeValue2408 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2408) = mixedMoment B node2408 node2408Labels := rfl
  simpa [nodeValue2408, Sparse.eval] using hc.symm

theorem sound2409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2409 node2409Labels = Sparse.eval nodeValue2409 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2409) = mixedMoment B node2409 node2409Labels := rfl
  simpa [nodeValue2409, Sparse.eval] using hc.symm

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

theorem sound2463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2463 node2463Labels = Sparse.eval nodeValue2463 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2463) = mixedMoment B node2463 node2463Labels := rfl
  simpa [nodeValue2463, Sparse.eval] using hc.symm

theorem sound2465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2465 node2465Labels = Sparse.eval nodeValue2465 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2465) = mixedMoment B node2465 node2465Labels := rfl
  simpa [nodeValue2465, Sparse.eval] using hc.symm

theorem sound2466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2466 node2466Labels = Sparse.eval nodeValue2466 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2466) = mixedMoment B node2466 node2466Labels := rfl
  simpa [nodeValue2466, Sparse.eval] using hc.symm

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

theorem sound2513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2513 node2513Labels = Sparse.eval nodeValue2513 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2513) = mixedMoment B node2513 node2513Labels := rfl
  simpa [nodeValue2513, Sparse.eval] using hc.symm

theorem sound2520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2520 node2520Labels = Sparse.eval nodeValue2520 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2520) = mixedMoment B node2520 node2520Labels := rfl
  simpa [nodeValue2520, Sparse.eval] using hc.symm

theorem sound2522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2522 node2522Labels = Sparse.eval nodeValue2522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2522) = mixedMoment B node2522 node2522Labels := rfl
  simpa [nodeValue2522, Sparse.eval] using hc.symm

theorem sound2555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2555 node2555Labels = Sparse.eval nodeValue2555 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2555) = mixedMoment B node2555 node2555Labels := rfl
  simpa [nodeValue2555, Sparse.eval] using hc.symm

theorem sound2559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2559 node2559Labels = Sparse.eval nodeValue2559 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2559) = mixedMoment B node2559 node2559Labels := rfl
  simpa [nodeValue2559, Sparse.eval] using hc.symm

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

theorem sound2560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2560 node2560Labels = Sparse.eval nodeValue2560 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2560) = mixedMoment B node2560 node2560Labels := rfl
  simpa [nodeValue2560, Sparse.eval] using hc.symm

theorem sound2580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2580 node2580Labels = Sparse.eval nodeValue2580 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2580) = mixedMoment B node2580 node2580Labels := rfl
  simpa [nodeValue2580, Sparse.eval] using hc.symm

theorem sound2582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2582 node2582Labels = Sparse.eval nodeValue2582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2582) = mixedMoment B node2582 node2582Labels := rfl
  simpa [nodeValue2582, Sparse.eval] using hc.symm

theorem sound2592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2592 node2592Labels = Sparse.eval nodeValue2592 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2592) = mixedMoment B node2592 node2592Labels := rfl
  simpa [nodeValue2592, Sparse.eval] using hc.symm

theorem sound2600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2600 node2600Labels = Sparse.eval nodeValue2600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2600) = mixedMoment B node2600 node2600Labels := rfl
  simpa [nodeValue2600, Sparse.eval] using hc.symm

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

theorem sound2647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2647 node2647Labels = Sparse.eval nodeValue2647 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2647) = mixedMoment B node2647 node2647Labels := rfl
  simpa [nodeValue2647, Sparse.eval] using hc.symm

theorem sound2651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2651 node2651Labels = Sparse.eval nodeValue2651 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2651) = mixedMoment B node2651 node2651Labels := rfl
  simpa [nodeValue2651, Sparse.eval] using hc.symm

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

theorem sound2732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2732 node2732Labels = Sparse.eval nodeValue2732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2732) = mixedMoment B node2732 node2732Labels := rfl
  simpa [nodeValue2732, Sparse.eval] using hc.symm

theorem sound2734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2734 node2734Labels = Sparse.eval nodeValue2734 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2734) = mixedMoment B node2734 node2734Labels := rfl
  simpa [nodeValue2734, Sparse.eval] using hc.symm

theorem sound2735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2735 node2735Labels = Sparse.eval nodeValue2735 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2735) = mixedMoment B node2735 node2735Labels := rfl
  simpa [nodeValue2735, Sparse.eval] using hc.symm

theorem sound2737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2737 node2737Labels = Sparse.eval nodeValue2737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2737) = mixedMoment B node2737 node2737Labels := rfl
  simpa [nodeValue2737, Sparse.eval] using hc.symm

theorem sound2738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2738 node2738Labels = Sparse.eval nodeValue2738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2738) = mixedMoment B node2738 node2738Labels := rfl
  simpa [nodeValue2738, Sparse.eval] using hc.symm

theorem sound2740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2740 node2740Labels = Sparse.eval nodeValue2740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2740) = mixedMoment B node2740 node2740Labels := rfl
  simpa [nodeValue2740, Sparse.eval] using hc.symm

theorem sound2744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2744 node2744Labels = Sparse.eval nodeValue2744 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2744) = mixedMoment B node2744 node2744Labels := rfl
  simpa [nodeValue2744, Sparse.eval] using hc.symm

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

theorem sound2759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2759 node2759Labels = Sparse.eval nodeValue2759 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2759) = mixedMoment B node2759 node2759Labels := rfl
  simpa [nodeValue2759, Sparse.eval] using hc.symm

theorem sound2769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2769 node2769Labels = Sparse.eval nodeValue2769 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2769) = mixedMoment B node2769 node2769Labels := rfl
  simpa [nodeValue2769, Sparse.eval] using hc.symm

theorem sound2773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2773 node2773Labels = Sparse.eval nodeValue2773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2773) = mixedMoment B node2773 node2773Labels := rfl
  simpa [nodeValue2773, Sparse.eval] using hc.symm

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

theorem sound2777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2777 node2777Labels = Sparse.eval nodeValue2777 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2777) = mixedMoment B node2777 node2777Labels := rfl
  simpa [nodeValue2777, Sparse.eval] using hc.symm

theorem sound2781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2781 node2781Labels = Sparse.eval nodeValue2781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2781) = mixedMoment B node2781 node2781Labels := rfl
  simpa [nodeValue2781, Sparse.eval] using hc.symm

theorem sound2782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2782 node2782Labels = Sparse.eval nodeValue2782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2782) = mixedMoment B node2782 node2782Labels := rfl
  simpa [nodeValue2782, Sparse.eval] using hc.symm

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

theorem sound3038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3038 node3038Labels = Sparse.eval nodeValue3038 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3038) = mixedMoment B node3038 node3038Labels := rfl
  simpa [nodeValue3038, Sparse.eval] using hc.symm

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

theorem sound3541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3541 node3541Labels = Sparse.eval nodeValue3541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3541) = mixedMoment B node3541 node3541Labels := rfl
  simpa [nodeValue3541, Sparse.eval] using hc.symm

theorem sound3573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3573 node3573Labels = Sparse.eval nodeValue3573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3573) = mixedMoment B node3573 node3573Labels := rfl
  simpa [nodeValue3573, Sparse.eval] using hc.symm

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

theorem sound3584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3584 node3584Labels = Sparse.eval nodeValue3584 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3584) = mixedMoment B node3584 node3584Labels := rfl
  simpa [nodeValue3584, Sparse.eval] using hc.symm

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

theorem sound3889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3889 node3889Labels = Sparse.eval nodeValue3889 (mixedVector B) := by
  have h := singleton3889 B _hB
  rw [sound496 B _hB _hF] at h
  norm_num [nodeValue3889, nodeValue496, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources7
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq226 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm226 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA226 + difference 0 1) (sourceB226 + difference 1 0) sourceC226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA226 + difference 0 1) (sourceB226 + difference 1 0) sourceC226) = raw5862 := by
      apply Matrix.ext; unfold tripleCharges sourceA226 sourceB226 sourceC226 difference raw5862; decide +kernel
    rw [ha]
    exact (canonical5862 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA226 + difference 1 1) (sourceB226 + difference 1 1) sourceC226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA226 + difference 1 1) (sourceB226 + difference 1 1) sourceC226) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA226 sourceB226 sourceC226 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA226 + difference 2 1) (sourceB226 + difference 1 2) sourceC226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA226 + difference 2 1) (sourceB226 + difference 1 2) sourceC226) = raw5877 := by
      apply Matrix.ext; unfold tripleCharges sourceA226 sourceB226 sourceC226 difference raw5877; decide +kernel
    rw [ha]
    exact (canonical5877 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA226 + difference 3 1) (sourceB226 + difference 1 3) sourceC226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA226 + difference 3 1) (sourceB226 + difference 1 3) sourceC226) = raw5878 := by
      apply Matrix.ext; unfold tripleCharges sourceA226 sourceB226 sourceC226 difference raw5878; decide +kernel
    rw [ha]
    exact (canonical5878 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA226 + difference 4 1) (sourceB226 + difference 1 4) sourceC226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA226 + difference 4 1) (sourceB226 + difference 1 4) sourceC226) = raw5879 := by
      apply Matrix.ext; unfold tripleCharges sourceA226 sourceB226 sourceC226 difference raw5879; decide +kernel
    rw [ha]
    exact (canonical5879 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA226 + difference 5 1) (sourceB226 + difference 1 5) sourceC226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA226 + difference 5 1) (sourceB226 + difference 1 5) sourceC226) = raw5880 := by
      apply Matrix.ext; unfold tripleCharges sourceA226 sourceB226 sourceC226 difference raw5880; decide +kernel
    rw [ha]
    exact (canonical5880 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA226 + sourceB226) sourceC226) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA226 + sourceB226) sourceC226) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA226 sourceB226 sourceC226 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA226 sourceB226 sourceC226
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm226, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq227 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm227 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA227 + difference 2 0) (sourceB227 + difference 0 2) sourceC227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1238) := by
    have ha : (tripleCharges (sourceA227 + difference 2 0) (sourceB227 + difference 0 2) sourceC227) = raw5869 := by
      apply Matrix.ext; unfold tripleCharges sourceA227 sourceB227 sourceC227 difference raw5869; decide +kernel
    rw [ha]
    exact (canonical5869 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA227 + difference 2 1) (sourceB227 + difference 1 2) sourceC227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA227 + difference 2 1) (sourceB227 + difference 1 2) sourceC227) = raw5877 := by
      apply Matrix.ext; unfold tripleCharges sourceA227 sourceB227 sourceC227 difference raw5877; decide +kernel
    rw [ha]
    exact (canonical5877 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA227 + difference 2 2) (sourceB227 + difference 2 2) sourceC227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA227 + difference 2 2) (sourceB227 + difference 2 2) sourceC227) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA227 sourceB227 sourceC227 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA227 + difference 2 3) (sourceB227 + difference 3 2) sourceC227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2555) := by
    have ha : (tripleCharges (sourceA227 + difference 2 3) (sourceB227 + difference 3 2) sourceC227) = raw5881 := by
      apply Matrix.ext; unfold tripleCharges sourceA227 sourceB227 sourceC227 difference raw5881; decide +kernel
    rw [ha]
    exact (canonical5881 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA227 + difference 2 4) (sourceB227 + difference 4 2) sourceC227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA227 + difference 2 4) (sourceB227 + difference 4 2) sourceC227) = raw5882 := by
      apply Matrix.ext; unfold tripleCharges sourceA227 sourceB227 sourceC227 difference raw5882; decide +kernel
    rw [ha]
    exact (canonical5882 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA227 + difference 2 5) (sourceB227 + difference 5 2) sourceC227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA227 + difference 2 5) (sourceB227 + difference 5 2) sourceC227) = raw5883 := by
      apply Matrix.ext; unfold tripleCharges sourceA227 sourceB227 sourceC227 difference raw5883; decide +kernel
    rw [ha]
    exact (canonical5883 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA227 + sourceB227) sourceC227) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA227 + sourceB227) sourceC227) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA227 sourceB227 sourceC227 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA227 sourceB227 sourceC227
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm227, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm228 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA228 + difference 0 2) (sourceB228 + difference 2 0) sourceC228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA228 + difference 0 2) (sourceB228 + difference 2 0) sourceC228) = raw5863 := by
      apply Matrix.ext; unfold tripleCharges sourceA228 sourceB228 sourceC228 difference raw5863; decide +kernel
    rw [ha]
    exact (canonical5863 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA228 + difference 1 2) (sourceB228 + difference 2 1) sourceC228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2592) := by
    have ha : (tripleCharges (sourceA228 + difference 1 2) (sourceB228 + difference 2 1) sourceC228) = raw5873 := by
      apply Matrix.ext; unfold tripleCharges sourceA228 sourceB228 sourceC228 difference raw5873; decide +kernel
    rw [ha]
    exact (canonical5873 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA228 + difference 2 2) (sourceB228 + difference 2 2) sourceC228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA228 + difference 2 2) (sourceB228 + difference 2 2) sourceC228) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA228 sourceB228 sourceC228 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA228 + difference 3 2) (sourceB228 + difference 2 3) sourceC228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2555) := by
    have ha : (tripleCharges (sourceA228 + difference 3 2) (sourceB228 + difference 2 3) sourceC228) = raw5884 := by
      apply Matrix.ext; unfold tripleCharges sourceA228 sourceB228 sourceC228 difference raw5884; decide +kernel
    rw [ha]
    exact (canonical5884 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA228 + difference 4 2) (sourceB228 + difference 2 4) sourceC228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2560) := by
    have ha : (tripleCharges (sourceA228 + difference 4 2) (sourceB228 + difference 2 4) sourceC228) = raw5885 := by
      apply Matrix.ext; unfold tripleCharges sourceA228 sourceB228 sourceC228 difference raw5885; decide +kernel
    rw [ha]
    exact (canonical5885 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA228 + difference 5 2) (sourceB228 + difference 2 5) sourceC228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2559) := by
    have ha : (tripleCharges (sourceA228 + difference 5 2) (sourceB228 + difference 2 5) sourceC228) = raw5886 := by
      apply Matrix.ext; unfold tripleCharges sourceA228 sourceB228 sourceC228 difference raw5886; decide +kernel
    rw [ha]
    exact (canonical5886 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA228 + sourceB228) sourceC228) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA228 + sourceB228) sourceC228) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA228 sourceB228 sourceC228 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA228 sourceB228 sourceC228
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm228, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq229 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm229 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA229 + difference 4 0) (sourceB229 + difference 0 4) sourceC229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA229 + difference 4 0) (sourceB229 + difference 0 4) sourceC229) = raw5871 := by
      apply Matrix.ext; unfold tripleCharges sourceA229 sourceB229 sourceC229 difference raw5871; decide +kernel
    rw [ha]
    exact (canonical5871 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA229 + difference 4 1) (sourceB229 + difference 1 4) sourceC229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA229 + difference 4 1) (sourceB229 + difference 1 4) sourceC229) = raw5879 := by
      apply Matrix.ext; unfold tripleCharges sourceA229 sourceB229 sourceC229 difference raw5879; decide +kernel
    rw [ha]
    exact (canonical5879 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA229 + difference 4 2) (sourceB229 + difference 2 4) sourceC229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2560) := by
    have ha : (tripleCharges (sourceA229 + difference 4 2) (sourceB229 + difference 2 4) sourceC229) = raw5885 := by
      apply Matrix.ext; unfold tripleCharges sourceA229 sourceB229 sourceC229 difference raw5885; decide +kernel
    rw [ha]
    exact (canonical5885 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA229 + difference 4 3) (sourceB229 + difference 3 4) sourceC229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2560) := by
    have ha : (tripleCharges (sourceA229 + difference 4 3) (sourceB229 + difference 3 4) sourceC229) = raw5887 := by
      apply Matrix.ext; unfold tripleCharges sourceA229 sourceB229 sourceC229 difference raw5887; decide +kernel
    rw [ha]
    exact (canonical5887 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA229 + difference 4 4) (sourceB229 + difference 4 4) sourceC229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA229 + difference 4 4) (sourceB229 + difference 4 4) sourceC229) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA229 sourceB229 sourceC229 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA229 + difference 4 5) (sourceB229 + difference 5 4) sourceC229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA229 + difference 4 5) (sourceB229 + difference 5 4) sourceC229) = raw5888 := by
      apply Matrix.ext; unfold tripleCharges sourceA229 sourceB229 sourceC229 difference raw5888; decide +kernel
    rw [ha]
    exact (canonical5888 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA229 + sourceB229) sourceC229) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA229 + sourceB229) sourceC229) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA229 sourceB229 sourceC229 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA229 sourceB229 sourceC229
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm229, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq230 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm230 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA230 + difference 0 4) (sourceB230 + difference 4 0) sourceC230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA230 + difference 0 4) (sourceB230 + difference 4 0) sourceC230) = raw5865 := by
      apply Matrix.ext; unfold tripleCharges sourceA230 sourceB230 sourceC230 difference raw5865; decide +kernel
    rw [ha]
    exact (canonical5865 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA230 + difference 1 4) (sourceB230 + difference 4 1) sourceC230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2138) := by
    have ha : (tripleCharges (sourceA230 + difference 1 4) (sourceB230 + difference 4 1) sourceC230) = raw5875 := by
      apply Matrix.ext; unfold tripleCharges sourceA230 sourceB230 sourceC230 difference raw5875; decide +kernel
    rw [ha]
    exact (canonical5875 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA230 + difference 2 4) (sourceB230 + difference 4 2) sourceC230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA230 + difference 2 4) (sourceB230 + difference 4 2) sourceC230) = raw5882 := by
      apply Matrix.ext; unfold tripleCharges sourceA230 sourceB230 sourceC230 difference raw5882; decide +kernel
    rw [ha]
    exact (canonical5882 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA230 + difference 3 4) (sourceB230 + difference 4 3) sourceC230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA230 + difference 3 4) (sourceB230 + difference 4 3) sourceC230) = raw5889 := by
      apply Matrix.ext; unfold tripleCharges sourceA230 sourceB230 sourceC230 difference raw5889; decide +kernel
    rw [ha]
    exact (canonical5889 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA230 + difference 4 4) (sourceB230 + difference 4 4) sourceC230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA230 + difference 4 4) (sourceB230 + difference 4 4) sourceC230) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA230 sourceB230 sourceC230 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA230 + difference 5 4) (sourceB230 + difference 4 5) sourceC230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA230 + difference 5 4) (sourceB230 + difference 4 5) sourceC230) = raw5890 := by
      apply Matrix.ext; unfold tripleCharges sourceA230 sourceB230 sourceC230 difference raw5890; decide +kernel
    rw [ha]
    exact (canonical5890 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA230 + sourceB230) sourceC230) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA230 + sourceB230) sourceC230) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA230 sourceB230 sourceC230 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA230 sourceB230 sourceC230
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm230, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq231 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm231 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA231 + difference 5 0) (sourceB231 + difference 0 5) sourceC231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1244) := by
    have ha : (tripleCharges (sourceA231 + difference 5 0) (sourceB231 + difference 0 5) sourceC231) = raw5872 := by
      apply Matrix.ext; unfold tripleCharges sourceA231 sourceB231 sourceC231 difference raw5872; decide +kernel
    rw [ha]
    exact (canonical5872 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA231 + difference 5 1) (sourceB231 + difference 1 5) sourceC231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA231 + difference 5 1) (sourceB231 + difference 1 5) sourceC231) = raw5880 := by
      apply Matrix.ext; unfold tripleCharges sourceA231 sourceB231 sourceC231 difference raw5880; decide +kernel
    rw [ha]
    exact (canonical5880 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA231 + difference 5 2) (sourceB231 + difference 2 5) sourceC231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2559) := by
    have ha : (tripleCharges (sourceA231 + difference 5 2) (sourceB231 + difference 2 5) sourceC231) = raw5886 := by
      apply Matrix.ext; unfold tripleCharges sourceA231 sourceB231 sourceC231 difference raw5886; decide +kernel
    rw [ha]
    exact (canonical5886 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA231 + difference 5 3) (sourceB231 + difference 3 5) sourceC231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2559) := by
    have ha : (tripleCharges (sourceA231 + difference 5 3) (sourceB231 + difference 3 5) sourceC231) = raw5891 := by
      apply Matrix.ext; unfold tripleCharges sourceA231 sourceB231 sourceC231 difference raw5891; decide +kernel
    rw [ha]
    exact (canonical5891 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA231 + difference 5 4) (sourceB231 + difference 4 5) sourceC231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA231 + difference 5 4) (sourceB231 + difference 4 5) sourceC231) = raw5890 := by
      apply Matrix.ext; unfold tripleCharges sourceA231 sourceB231 sourceC231 difference raw5890; decide +kernel
    rw [ha]
    exact (canonical5890 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA231 + difference 5 5) (sourceB231 + difference 5 5) sourceC231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA231 + difference 5 5) (sourceB231 + difference 5 5) sourceC231) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA231 sourceB231 sourceC231 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA231 + sourceB231) sourceC231) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA231 + sourceB231) sourceC231) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA231 sourceB231 sourceC231 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA231 sourceB231 sourceC231
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm231, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq233 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm233 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA233 + difference 0 1) (sourceB233 + difference 1 0) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA233 + difference 0 1) (sourceB233 + difference 1 0) sourceC233) = raw5922 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5922; decide +kernel
    rw [ha]
    exact (canonical5922 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA233 + difference 0 2) (sourceB233 + difference 2 0) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA233 + difference 0 2) (sourceB233 + difference 2 0) sourceC233) = raw5923 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5923; decide +kernel
    rw [ha]
    exact (canonical5923 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA233 + difference 0 3) (sourceB233 + difference 3 0) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA233 + difference 0 3) (sourceB233 + difference 3 0) sourceC233) = raw5924 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5924; decide +kernel
    rw [ha]
    exact (canonical5924 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA233 + difference 0 4) (sourceB233 + difference 4 0) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA233 + difference 0 4) (sourceB233 + difference 4 0) sourceC233) = raw5925 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5925; decide +kernel
    rw [ha]
    exact (canonical5925 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA233 + difference 0 5) (sourceB233 + difference 5 0) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA233 + difference 0 5) (sourceB233 + difference 5 0) sourceC233) = raw5926 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5926; decide +kernel
    rw [ha]
    exact (canonical5926 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA233 + difference 1 0) (sourceB233 + difference 0 1) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1084) := by
    have ha : (tripleCharges (sourceA233 + difference 1 0) (sourceB233 + difference 0 1) sourceC233) = raw5927 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5927; decide +kernel
    rw [ha]
    exact (canonical5927 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA233 + difference 1 2) (sourceB233 + difference 2 1) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA233 + difference 1 2) (sourceB233 + difference 2 1) sourceC233) = raw5928 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5928; decide +kernel
    rw [ha]
    exact (canonical5928 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA233 + difference 1 3) (sourceB233 + difference 3 1) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA233 + difference 1 3) (sourceB233 + difference 3 1) sourceC233) = raw5929 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5929; decide +kernel
    rw [ha]
    exact (canonical5929 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA233 + difference 1 4) (sourceB233 + difference 4 1) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA233 + difference 1 4) (sourceB233 + difference 4 1) sourceC233) = raw5930 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5930; decide +kernel
    rw [ha]
    exact (canonical5930 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA233 + difference 1 5) (sourceB233 + difference 5 1) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA233 + difference 1 5) (sourceB233 + difference 5 1) sourceC233) = raw5931 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5931; decide +kernel
    rw [ha]
    exact (canonical5931 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA233 + difference 2 0) (sourceB233 + difference 0 2) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1006) := by
    have ha : (tripleCharges (sourceA233 + difference 2 0) (sourceB233 + difference 0 2) sourceC233) = raw5932 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5932; decide +kernel
    rw [ha]
    exact (canonical5932 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA233 + difference 2 1) (sourceB233 + difference 1 2) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2405) := by
    have ha : (tripleCharges (sourceA233 + difference 2 1) (sourceB233 + difference 1 2) sourceC233) = raw5933 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5933; decide +kernel
    rw [ha]
    exact (canonical5933 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA233 + difference 2 3) (sourceB233 + difference 3 2) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2463) := by
    have ha : (tripleCharges (sourceA233 + difference 2 3) (sourceB233 + difference 3 2) sourceC233) = raw5934 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5934; decide +kernel
    rw [ha]
    exact (canonical5934 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA233 + difference 2 4) (sourceB233 + difference 4 2) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA233 + difference 2 4) (sourceB233 + difference 4 2) sourceC233) = raw5935 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5935; decide +kernel
    rw [ha]
    exact (canonical5935 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA233 + difference 2 5) (sourceB233 + difference 5 2) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA233 + difference 2 5) (sourceB233 + difference 5 2) sourceC233) = raw5936 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5936; decide +kernel
    rw [ha]
    exact (canonical5936 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA233 + difference 3 0) (sourceB233 + difference 0 3) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1006) := by
    have ha : (tripleCharges (sourceA233 + difference 3 0) (sourceB233 + difference 0 3) sourceC233) = raw5937 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5937; decide +kernel
    rw [ha]
    exact (canonical5937 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA233 + difference 3 1) (sourceB233 + difference 1 3) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2405) := by
    have ha : (tripleCharges (sourceA233 + difference 3 1) (sourceB233 + difference 1 3) sourceC233) = raw5938 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5938; decide +kernel
    rw [ha]
    exact (canonical5938 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA233 + difference 3 2) (sourceB233 + difference 2 3) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2463) := by
    have ha : (tripleCharges (sourceA233 + difference 3 2) (sourceB233 + difference 2 3) sourceC233) = raw5939 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5939; decide +kernel
    rw [ha]
    exact (canonical5939 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA233 + difference 3 4) (sourceB233 + difference 4 3) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA233 + difference 3 4) (sourceB233 + difference 4 3) sourceC233) = raw5940 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5940; decide +kernel
    rw [ha]
    exact (canonical5940 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA233 + difference 3 5) (sourceB233 + difference 5 3) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA233 + difference 3 5) (sourceB233 + difference 5 3) sourceC233) = raw5941 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5941; decide +kernel
    rw [ha]
    exact (canonical5941 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA233 + difference 4 0) (sourceB233 + difference 0 4) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1011) := by
    have ha : (tripleCharges (sourceA233 + difference 4 0) (sourceB233 + difference 0 4) sourceC233) = raw5942 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5942; decide +kernel
    rw [ha]
    exact (canonical5942 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA233 + difference 4 1) (sourceB233 + difference 1 4) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2409) := by
    have ha : (tripleCharges (sourceA233 + difference 4 1) (sourceB233 + difference 1 4) sourceC233) = raw5943 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5943; decide +kernel
    rw [ha]
    exact (canonical5943 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA233 + difference 4 2) (sourceB233 + difference 2 4) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2466) := by
    have ha : (tripleCharges (sourceA233 + difference 4 2) (sourceB233 + difference 2 4) sourceC233) = raw5944 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5944; decide +kernel
    rw [ha]
    exact (canonical5944 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA233 + difference 4 3) (sourceB233 + difference 3 4) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2466) := by
    have ha : (tripleCharges (sourceA233 + difference 4 3) (sourceB233 + difference 3 4) sourceC233) = raw5945 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5945; decide +kernel
    rw [ha]
    exact (canonical5945 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA233 + difference 4 5) (sourceB233 + difference 5 4) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA233 + difference 4 5) (sourceB233 + difference 5 4) sourceC233) = raw5946 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5946; decide +kernel
    rw [ha]
    exact (canonical5946 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA233 + difference 5 0) (sourceB233 + difference 0 5) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1010) := by
    have ha : (tripleCharges (sourceA233 + difference 5 0) (sourceB233 + difference 0 5) sourceC233) = raw5947 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5947; decide +kernel
    rw [ha]
    exact (canonical5947 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA233 + difference 5 1) (sourceB233 + difference 1 5) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2408) := by
    have ha : (tripleCharges (sourceA233 + difference 5 1) (sourceB233 + difference 1 5) sourceC233) = raw5948 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5948; decide +kernel
    rw [ha]
    exact (canonical5948 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA233 + difference 5 2) (sourceB233 + difference 2 5) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2465) := by
    have ha : (tripleCharges (sourceA233 + difference 5 2) (sourceB233 + difference 2 5) sourceC233) = raw5949 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5949; decide +kernel
    rw [ha]
    exact (canonical5949 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA233 + difference 5 3) (sourceB233 + difference 3 5) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2465) := by
    have ha : (tripleCharges (sourceA233 + difference 5 3) (sourceB233 + difference 3 5) sourceC233) = raw5950 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5950; decide +kernel
    rw [ha]
    exact (canonical5950 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA233 + difference 5 4) (sourceB233 + difference 4 5) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA233 + difference 5 4) (sourceB233 + difference 4 5) sourceC233) = raw5951 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5951; decide +kernel
    rw [ha]
    exact (canonical5951 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA233 sourceB233 sourceC233
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm233, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq235 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm235 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA235 + difference 0 0) (sourceB235 + difference 0 0) sourceC235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA235 + difference 0 0) (sourceB235 + difference 0 0) sourceC235) = raw5982 := by
      apply Matrix.ext; unfold tripleCharges sourceA235 sourceB235 sourceC235 difference raw5982; decide +kernel
    rw [ha]
    exact (canonical5982 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA235 + difference 0 1) (sourceB235 + difference 1 0) sourceC235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA235 + difference 0 1) (sourceB235 + difference 1 0) sourceC235) = raw5983 := by
      apply Matrix.ext; unfold tripleCharges sourceA235 sourceB235 sourceC235 difference raw5983; decide +kernel
    rw [ha]
    exact (canonical5983 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA235 + difference 0 2) (sourceB235 + difference 2 0) sourceC235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA235 + difference 0 2) (sourceB235 + difference 2 0) sourceC235) = raw5984 := by
      apply Matrix.ext; unfold tripleCharges sourceA235 sourceB235 sourceC235 difference raw5984; decide +kernel
    rw [ha]
    exact (canonical5984 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA235 + difference 0 3) (sourceB235 + difference 3 0) sourceC235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA235 + difference 0 3) (sourceB235 + difference 3 0) sourceC235) = raw5985 := by
      apply Matrix.ext; unfold tripleCharges sourceA235 sourceB235 sourceC235 difference raw5985; decide +kernel
    rw [ha]
    exact (canonical5985 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA235 + difference 0 4) (sourceB235 + difference 4 0) sourceC235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA235 + difference 0 4) (sourceB235 + difference 4 0) sourceC235) = raw5986 := by
      apply Matrix.ext; unfold tripleCharges sourceA235 sourceB235 sourceC235 difference raw5986; decide +kernel
    rw [ha]
    exact (canonical5986 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA235 + difference 0 5) (sourceB235 + difference 5 0) sourceC235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA235 + difference 0 5) (sourceB235 + difference 5 0) sourceC235) = raw5987 := by
      apply Matrix.ext; unfold tripleCharges sourceA235 sourceB235 sourceC235 difference raw5987; decide +kernel
    rw [ha]
    exact (canonical5987 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA235 + sourceB235) sourceC235) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA235 + sourceB235) sourceC235) = raw5988 := by
      apply Matrix.ext; unfold doubleCharges sourceA235 sourceB235 sourceC235 raw5988; decide +kernel
    rw [ha]
    exact (canonical5988 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA235 sourceB235 sourceC235
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm235, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq236 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm236 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA236 + difference 0 0) (sourceB236 + difference 0 0) sourceC236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA236 + difference 0 0) (sourceB236 + difference 0 0) sourceC236) = raw5982 := by
      apply Matrix.ext; unfold tripleCharges sourceA236 sourceB236 sourceC236 difference raw5982; decide +kernel
    rw [ha]
    exact (canonical5982 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA236 + difference 1 0) (sourceB236 + difference 0 1) sourceC236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA236 + difference 1 0) (sourceB236 + difference 0 1) sourceC236) = raw5989 := by
      apply Matrix.ext; unfold tripleCharges sourceA236 sourceB236 sourceC236 difference raw5989; decide +kernel
    rw [ha]
    exact (canonical5989 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA236 + difference 2 0) (sourceB236 + difference 0 2) sourceC236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1422) := by
    have ha : (tripleCharges (sourceA236 + difference 2 0) (sourceB236 + difference 0 2) sourceC236) = raw5990 := by
      apply Matrix.ext; unfold tripleCharges sourceA236 sourceB236 sourceC236 difference raw5990; decide +kernel
    rw [ha]
    exact (canonical5990 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA236 + difference 3 0) (sourceB236 + difference 0 3) sourceC236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1422) := by
    have ha : (tripleCharges (sourceA236 + difference 3 0) (sourceB236 + difference 0 3) sourceC236) = raw5991 := by
      apply Matrix.ext; unfold tripleCharges sourceA236 sourceB236 sourceC236 difference raw5991; decide +kernel
    rw [ha]
    exact (canonical5991 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA236 + difference 4 0) (sourceB236 + difference 0 4) sourceC236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1282) := by
    have ha : (tripleCharges (sourceA236 + difference 4 0) (sourceB236 + difference 0 4) sourceC236) = raw5992 := by
      apply Matrix.ext; unfold tripleCharges sourceA236 sourceB236 sourceC236 difference raw5992; decide +kernel
    rw [ha]
    exact (canonical5992 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA236 + difference 5 0) (sourceB236 + difference 0 5) sourceC236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1424) := by
    have ha : (tripleCharges (sourceA236 + difference 5 0) (sourceB236 + difference 0 5) sourceC236) = raw5993 := by
      apply Matrix.ext; unfold tripleCharges sourceA236 sourceB236 sourceC236 difference raw5993; decide +kernel
    rw [ha]
    exact (canonical5993 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA236 + sourceB236) sourceC236) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA236 + sourceB236) sourceC236) = raw5988 := by
      apply Matrix.ext; unfold doubleCharges sourceA236 sourceB236 sourceC236 raw5988; decide +kernel
    rw [ha]
    exact (canonical5988 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA236 sourceB236 sourceC236
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm236, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm237 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA237 + difference 1 0) (sourceB237 + difference 0 1) sourceC237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA237 + difference 1 0) (sourceB237 + difference 0 1) sourceC237) = raw5989 := by
      apply Matrix.ext; unfold tripleCharges sourceA237 sourceB237 sourceC237 difference raw5989; decide +kernel
    rw [ha]
    exact (canonical5989 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA237 + difference 1 1) (sourceB237 + difference 1 1) sourceC237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA237 + difference 1 1) (sourceB237 + difference 1 1) sourceC237) = raw5982 := by
      apply Matrix.ext; unfold tripleCharges sourceA237 sourceB237 sourceC237 difference raw5982; decide +kernel
    rw [ha]
    exact (canonical5982 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA237 + difference 1 2) (sourceB237 + difference 2 1) sourceC237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2759) := by
    have ha : (tripleCharges (sourceA237 + difference 1 2) (sourceB237 + difference 2 1) sourceC237) = raw5994 := by
      apply Matrix.ext; unfold tripleCharges sourceA237 sourceB237 sourceC237 difference raw5994; decide +kernel
    rw [ha]
    exact (canonical5994 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA237 + difference 1 3) (sourceB237 + difference 3 1) sourceC237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2759) := by
    have ha : (tripleCharges (sourceA237 + difference 1 3) (sourceB237 + difference 3 1) sourceC237) = raw5995 := by
      apply Matrix.ext; unfold tripleCharges sourceA237 sourceB237 sourceC237 difference raw5995; decide +kernel
    rw [ha]
    exact (canonical5995 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA237 + difference 1 4) (sourceB237 + difference 4 1) sourceC237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA237 + difference 1 4) (sourceB237 + difference 4 1) sourceC237) = raw5996 := by
      apply Matrix.ext; unfold tripleCharges sourceA237 sourceB237 sourceC237 difference raw5996; decide +kernel
    rw [ha]
    exact (canonical5996 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA237 + difference 1 5) (sourceB237 + difference 5 1) sourceC237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA237 + difference 1 5) (sourceB237 + difference 5 1) sourceC237) = raw5997 := by
      apply Matrix.ext; unfold tripleCharges sourceA237 sourceB237 sourceC237 difference raw5997; decide +kernel
    rw [ha]
    exact (canonical5997 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA237 + sourceB237) sourceC237) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA237 + sourceB237) sourceC237) = raw5988 := by
      apply Matrix.ext; unfold doubleCharges sourceA237 sourceB237 sourceC237 raw5988; decide +kernel
    rw [ha]
    exact (canonical5988 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA237 sourceB237 sourceC237
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm237, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm238 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA238 + difference 0 1) (sourceB238 + difference 1 0) sourceC238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA238 + difference 0 1) (sourceB238 + difference 1 0) sourceC238) = raw5983 := by
      apply Matrix.ext; unfold tripleCharges sourceA238 sourceB238 sourceC238 difference raw5983; decide +kernel
    rw [ha]
    exact (canonical5983 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA238 + difference 1 1) (sourceB238 + difference 1 1) sourceC238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA238 + difference 1 1) (sourceB238 + difference 1 1) sourceC238) = raw5982 := by
      apply Matrix.ext; unfold tripleCharges sourceA238 sourceB238 sourceC238 difference raw5982; decide +kernel
    rw [ha]
    exact (canonical5982 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA238 + difference 2 1) (sourceB238 + difference 1 2) sourceC238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2582) := by
    have ha : (tripleCharges (sourceA238 + difference 2 1) (sourceB238 + difference 1 2) sourceC238) = raw5998 := by
      apply Matrix.ext; unfold tripleCharges sourceA238 sourceB238 sourceC238 difference raw5998; decide +kernel
    rw [ha]
    exact (canonical5998 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA238 + difference 3 1) (sourceB238 + difference 1 3) sourceC238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2582) := by
    have ha : (tripleCharges (sourceA238 + difference 3 1) (sourceB238 + difference 1 3) sourceC238) = raw5999 := by
      apply Matrix.ext; unfold tripleCharges sourceA238 sourceB238 sourceC238 difference raw5999; decide +kernel
    rw [ha]
    exact (canonical5999 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA238 + difference 4 1) (sourceB238 + difference 1 4) sourceC238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1283) := by
    have ha : (tripleCharges (sourceA238 + difference 4 1) (sourceB238 + difference 1 4) sourceC238) = raw6000 := by
      apply Matrix.ext; unfold tripleCharges sourceA238 sourceB238 sourceC238 difference raw6000; decide +kernel
    rw [ha]
    exact (canonical6000 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA238 + difference 5 1) (sourceB238 + difference 1 5) sourceC238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2651) := by
    have ha : (tripleCharges (sourceA238 + difference 5 1) (sourceB238 + difference 1 5) sourceC238) = raw6001 := by
      apply Matrix.ext; unfold tripleCharges sourceA238 sourceB238 sourceC238 difference raw6001; decide +kernel
    rw [ha]
    exact (canonical6001 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA238 + sourceB238) sourceC238) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA238 + sourceB238) sourceC238) = raw5988 := by
      apply Matrix.ext; unfold doubleCharges sourceA238 sourceB238 sourceC238 raw5988; decide +kernel
    rw [ha]
    exact (canonical5988 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA238 sourceB238 sourceC238
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm238, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq239 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm239 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA239 + difference 2 0) (sourceB239 + difference 0 2) sourceC239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1422) := by
    have ha : (tripleCharges (sourceA239 + difference 2 0) (sourceB239 + difference 0 2) sourceC239) = raw5990 := by
      apply Matrix.ext; unfold tripleCharges sourceA239 sourceB239 sourceC239 difference raw5990; decide +kernel
    rw [ha]
    exact (canonical5990 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA239 + difference 2 1) (sourceB239 + difference 1 2) sourceC239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2582) := by
    have ha : (tripleCharges (sourceA239 + difference 2 1) (sourceB239 + difference 1 2) sourceC239) = raw5998 := by
      apply Matrix.ext; unfold tripleCharges sourceA239 sourceB239 sourceC239 difference raw5998; decide +kernel
    rw [ha]
    exact (canonical5998 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA239 + difference 2 2) (sourceB239 + difference 2 2) sourceC239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA239 + difference 2 2) (sourceB239 + difference 2 2) sourceC239) = raw5982 := by
      apply Matrix.ext; unfold tripleCharges sourceA239 sourceB239 sourceC239 difference raw5982; decide +kernel
    rw [ha]
    exact (canonical5982 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA239 + difference 2 3) (sourceB239 + difference 3 2) sourceC239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2580) := by
    have ha : (tripleCharges (sourceA239 + difference 2 3) (sourceB239 + difference 3 2) sourceC239) = raw6002 := by
      apply Matrix.ext; unfold tripleCharges sourceA239 sourceB239 sourceC239 difference raw6002; decide +kernel
    rw [ha]
    exact (canonical6002 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA239 + difference 2 4) (sourceB239 + difference 4 2) sourceC239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA239 + difference 2 4) (sourceB239 + difference 4 2) sourceC239) = raw6003 := by
      apply Matrix.ext; unfold tripleCharges sourceA239 sourceB239 sourceC239 difference raw6003; decide +kernel
    rw [ha]
    exact (canonical6003 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA239 + difference 2 5) (sourceB239 + difference 5 2) sourceC239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2600) := by
    have ha : (tripleCharges (sourceA239 + difference 2 5) (sourceB239 + difference 5 2) sourceC239) = raw6004 := by
      apply Matrix.ext; unfold tripleCharges sourceA239 sourceB239 sourceC239 difference raw6004; decide +kernel
    rw [ha]
    exact (canonical6004 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA239 + sourceB239) sourceC239) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA239 + sourceB239) sourceC239) = raw5988 := by
      apply Matrix.ext; unfold doubleCharges sourceA239 sourceB239 sourceC239 raw5988; decide +kernel
    rw [ha]
    exact (canonical5988 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA239 sourceB239 sourceC239
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm239, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq240 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm240 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA240 + difference 0 2) (sourceB240 + difference 2 0) sourceC240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA240 + difference 0 2) (sourceB240 + difference 2 0) sourceC240) = raw5984 := by
      apply Matrix.ext; unfold tripleCharges sourceA240 sourceB240 sourceC240 difference raw5984; decide +kernel
    rw [ha]
    exact (canonical5984 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA240 + difference 1 2) (sourceB240 + difference 2 1) sourceC240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2759) := by
    have ha : (tripleCharges (sourceA240 + difference 1 2) (sourceB240 + difference 2 1) sourceC240) = raw5994 := by
      apply Matrix.ext; unfold tripleCharges sourceA240 sourceB240 sourceC240 difference raw5994; decide +kernel
    rw [ha]
    exact (canonical5994 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA240 + difference 2 2) (sourceB240 + difference 2 2) sourceC240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA240 + difference 2 2) (sourceB240 + difference 2 2) sourceC240) = raw5982 := by
      apply Matrix.ext; unfold tripleCharges sourceA240 sourceB240 sourceC240 difference raw5982; decide +kernel
    rw [ha]
    exact (canonical5982 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA240 + difference 3 2) (sourceB240 + difference 2 3) sourceC240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2580) := by
    have ha : (tripleCharges (sourceA240 + difference 3 2) (sourceB240 + difference 2 3) sourceC240) = raw6005 := by
      apply Matrix.ext; unfold tripleCharges sourceA240 sourceB240 sourceC240 difference raw6005; decide +kernel
    rw [ha]
    exact (canonical6005 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA240 + difference 4 2) (sourceB240 + difference 2 4) sourceC240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1280) := by
    have ha : (tripleCharges (sourceA240 + difference 4 2) (sourceB240 + difference 2 4) sourceC240) = raw6006 := by
      apply Matrix.ext; unfold tripleCharges sourceA240 sourceB240 sourceC240 difference raw6006; decide +kernel
    rw [ha]
    exact (canonical6006 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA240 + difference 5 2) (sourceB240 + difference 2 5) sourceC240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2647) := by
    have ha : (tripleCharges (sourceA240 + difference 5 2) (sourceB240 + difference 2 5) sourceC240) = raw6007 := by
      apply Matrix.ext; unfold tripleCharges sourceA240 sourceB240 sourceC240 difference raw6007; decide +kernel
    rw [ha]
    exact (canonical6007 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA240 + sourceB240) sourceC240) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA240 + sourceB240) sourceC240) = raw5988 := by
      apply Matrix.ext; unfold doubleCharges sourceA240 sourceB240 sourceC240 raw5988; decide +kernel
    rw [ha]
    exact (canonical5988 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA240 sourceB240 sourceC240
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm240, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm241 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA241 + difference 4 0) (sourceB241 + difference 0 4) sourceC241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1282) := by
    have ha : (tripleCharges (sourceA241 + difference 4 0) (sourceB241 + difference 0 4) sourceC241) = raw5992 := by
      apply Matrix.ext; unfold tripleCharges sourceA241 sourceB241 sourceC241 difference raw5992; decide +kernel
    rw [ha]
    exact (canonical5992 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA241 + difference 4 1) (sourceB241 + difference 1 4) sourceC241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1283) := by
    have ha : (tripleCharges (sourceA241 + difference 4 1) (sourceB241 + difference 1 4) sourceC241) = raw6000 := by
      apply Matrix.ext; unfold tripleCharges sourceA241 sourceB241 sourceC241 difference raw6000; decide +kernel
    rw [ha]
    exact (canonical6000 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA241 + difference 4 2) (sourceB241 + difference 2 4) sourceC241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1280) := by
    have ha : (tripleCharges (sourceA241 + difference 4 2) (sourceB241 + difference 2 4) sourceC241) = raw6006 := by
      apply Matrix.ext; unfold tripleCharges sourceA241 sourceB241 sourceC241 difference raw6006; decide +kernel
    rw [ha]
    exact (canonical6006 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA241 + difference 4 3) (sourceB241 + difference 3 4) sourceC241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1280) := by
    have ha : (tripleCharges (sourceA241 + difference 4 3) (sourceB241 + difference 3 4) sourceC241) = raw6008 := by
      apply Matrix.ext; unfold tripleCharges sourceA241 sourceB241 sourceC241 difference raw6008; decide +kernel
    rw [ha]
    exact (canonical6008 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA241 + difference 4 4) (sourceB241 + difference 4 4) sourceC241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA241 + difference 4 4) (sourceB241 + difference 4 4) sourceC241) = raw5982 := by
      apply Matrix.ext; unfold tripleCharges sourceA241 sourceB241 sourceC241 difference raw5982; decide +kernel
    rw [ha]
    exact (canonical5982 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA241 + difference 4 5) (sourceB241 + difference 5 4) sourceC241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA241 + difference 4 5) (sourceB241 + difference 5 4) sourceC241) = raw6009 := by
      apply Matrix.ext; unfold tripleCharges sourceA241 sourceB241 sourceC241 difference raw6009; decide +kernel
    rw [ha]
    exact (canonical6009 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA241 + sourceB241) sourceC241) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA241 + sourceB241) sourceC241) = raw5988 := by
      apply Matrix.ext; unfold doubleCharges sourceA241 sourceB241 sourceC241 raw5988; decide +kernel
    rw [ha]
    exact (canonical5988 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA241 sourceB241 sourceC241
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm241, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck192 : Integer.Sparse.reindex keyMap MixedData.row192 = numericRow192 := by decide +kernel

theorem numericCheck192 (x : Master → ℝ) : Integer.Sparse.eval numericRow192 x =
    (1 : ℝ) * reducedSource192 x := by
  norm_num [numericRow192, reducedSource192, Integer.Sparse.eval, Sparse.eval, nodeValue2513, nodeValue2520, nodeValue2522, nodeValue2744, nodeValue3626, nodeValue4084]

theorem reindexCheck193 : Integer.Sparse.reindex keyMap MixedData.row193 = numericRow193 := by decide +kernel

theorem numericCheck193 (x : Master → ℝ) : Integer.Sparse.eval numericRow193 x =
    (1 : ℝ) * reducedSource193 x := by
  norm_num [numericRow193, reducedSource193, Integer.Sparse.eval, Sparse.eval, nodeValue1238, nodeValue2133, nodeValue2513, nodeValue2555, nodeValue2738, nodeValue2744, nodeValue4084]

theorem reindexCheck194 : Integer.Sparse.reindex keyMap MixedData.row194 = numericRow194 := by decide +kernel

theorem numericCheck194 (x : Master → ℝ) : Integer.Sparse.eval numericRow194 x =
    (1 : ℝ) * reducedSource194 x := by
  norm_num [numericRow194, reducedSource194, Integer.Sparse.eval, Sparse.eval, nodeValue2555, nodeValue2559, nodeValue2560, nodeValue2592, nodeValue2744, nodeValue3541, nodeValue4084]

theorem reindexCheck195 : Integer.Sparse.reindex keyMap MixedData.row195 = numericRow195 := by decide +kernel

theorem numericCheck195 (x : Master → ℝ) : Integer.Sparse.eval numericRow195 x =
    (1 : ℝ) * reducedSource195 x := by
  norm_num [numericRow195, reducedSource195, Integer.Sparse.eval, Sparse.eval, nodeValue1245, nodeValue2522, nodeValue2560, nodeValue2740, nodeValue2744, nodeValue4084]

theorem reindexCheck196 : Integer.Sparse.reindex keyMap MixedData.row196 = numericRow196 := by decide +kernel

theorem numericCheck196 (x : Master → ℝ) : Integer.Sparse.eval numericRow196 x =
    (1 : ℝ) * reducedSource196 x := by
  norm_num [numericRow196, reducedSource196, Integer.Sparse.eval, Sparse.eval, nodeValue2133, nodeValue2136, nodeValue2138, nodeValue2279, nodeValue2744, nodeValue4084]

theorem reindexCheck197 : Integer.Sparse.reindex keyMap MixedData.row197 = numericRow197 := by decide +kernel

theorem numericCheck197 (x : Master → ℝ) : Integer.Sparse.eval numericRow197 x =
    (1 : ℝ) * reducedSource197 x := by
  norm_num [numericRow197, reducedSource197, Integer.Sparse.eval, Sparse.eval, nodeValue1244, nodeValue2136, nodeValue2520, nodeValue2559, nodeValue2744, nodeValue4084]

theorem reindexCheck198 : Integer.Sparse.reindex keyMap MixedData.row198 = numericRow198 := by decide +kernel

theorem numericCheck198 (x : Master → ℝ) : Integer.Sparse.eval numericRow198 x =
    (2160 : ℝ) * reducedSource198 x := by
  norm_num [numericRow198, reducedSource198, Integer.Sparse.eval, Sparse.eval, nodeValue1006, nodeValue1010, nodeValue1011, nodeValue1084, nodeValue2405, nodeValue2408, nodeValue2409, nodeValue2463, nodeValue2465, nodeValue2466, nodeValue2513, nodeValue2732, nodeValue2734, nodeValue2735, nodeValue2737, nodeValue2776, nodeValue2781, nodeValue3573, nodeValue3583, nodeValue3584, nodeValue3889]
  ring

theorem reindexCheck200 : Integer.Sparse.reindex keyMap MixedData.row200 = numericRow200 := by decide +kernel

theorem numericCheck200 (x : Master → ℝ) : Integer.Sparse.eval numericRow200 x =
    (1 : ℝ) * reducedSource200 x := by
  norm_num [numericRow200, reducedSource200, Integer.Sparse.eval, Sparse.eval, nodeValue2773, nodeValue2774, nodeValue2777, nodeValue2782, nodeValue3907, nodeValue4092]

theorem reindexCheck201 : Integer.Sparse.reindex keyMap MixedData.row201 = numericRow201 := by decide +kernel

theorem numericCheck201 (x : Master → ℝ) : Integer.Sparse.eval numericRow201 x =
    (1 : ℝ) * reducedSource201 x := by
  norm_num [numericRow201, reducedSource201, Integer.Sparse.eval, Sparse.eval, nodeValue1282, nodeValue1422, nodeValue1424, nodeValue1436, nodeValue2777, nodeValue4092]

theorem reindexCheck202 : Integer.Sparse.reindex keyMap MixedData.row202 = numericRow202 := by decide +kernel

theorem numericCheck202 (x : Master → ℝ) : Integer.Sparse.eval numericRow202 x =
    (1 : ℝ) * reducedSource202 x := by
  norm_num [numericRow202, reducedSource202, Integer.Sparse.eval, Sparse.eval, nodeValue1436, nodeValue2759, nodeValue2769, nodeValue2777, nodeValue3054, nodeValue4092]

theorem reindexCheck203 : Integer.Sparse.reindex keyMap MixedData.row203 = numericRow203 := by decide +kernel

theorem numericCheck203 (x : Master → ℝ) : Integer.Sparse.eval numericRow203 x =
    (1 : ℝ) * reducedSource203 x := by
  norm_num [numericRow203, reducedSource203, Integer.Sparse.eval, Sparse.eval, nodeValue1283, nodeValue2582, nodeValue2651, nodeValue2774, nodeValue2777, nodeValue4092]

theorem reindexCheck204 : Integer.Sparse.reindex keyMap MixedData.row204 = numericRow204 := by decide +kernel

theorem numericCheck204 (x : Master → ℝ) : Integer.Sparse.eval numericRow204 x =
    (1 : ℝ) * reducedSource204 x := by
  norm_num [numericRow204, reducedSource204, Integer.Sparse.eval, Sparse.eval, nodeValue1422, nodeValue2580, nodeValue2582, nodeValue2600, nodeValue2777, nodeValue3038, nodeValue4092]

theorem reindexCheck205 : Integer.Sparse.reindex keyMap MixedData.row205 = numericRow205 := by decide +kernel

theorem numericCheck205 (x : Master → ℝ) : Integer.Sparse.eval numericRow205 x =
    (1 : ℝ) * reducedSource205 x := by
  norm_num [numericRow205, reducedSource205, Integer.Sparse.eval, Sparse.eval, nodeValue1280, nodeValue2580, nodeValue2647, nodeValue2759, nodeValue2773, nodeValue2777, nodeValue4092]

theorem reindexCheck206 : Integer.Sparse.reindex keyMap MixedData.row206 = numericRow206 := by decide +kernel

theorem numericCheck206 (x : Master → ℝ) : Integer.Sparse.eval numericRow206 x =
    (1 : ℝ) * reducedSource206 x := by
  norm_num [numericRow206, reducedSource206, Integer.Sparse.eval, Sparse.eval, nodeValue1280, nodeValue1282, nodeValue1283, nodeValue1306, nodeValue2777, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero192 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource192 (mixedVector B) = 0 := by
  have h2513 : mixedVector B (Sum.inr 2513) = Sparse.eval nodeValue2513 (mixedVector B) := by
    change mixedMoment B node2513 node2513Labels = _
    exact sound2513 B hB hF
  have h2520 : mixedVector B (Sum.inr 2520) = Sparse.eval nodeValue2520 (mixedVector B) := by
    change mixedMoment B node2520 node2520Labels = _
    exact sound2520 B hB hF
  have h2522 : mixedVector B (Sum.inr 2522) = Sparse.eval nodeValue2522 (mixedVector B) := by
    change mixedMoment B node2522 node2522Labels = _
    exact sound2522 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm226, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2513, h2520, h2522, h2744, h3626, h4084, reducedSource192] using sourceEq226 B hB

theorem rowSound192 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row192 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck192, numericCheck192, reducedZero192 B hB hF, mul_zero]

theorem reducedZero193 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource193 (mixedVector B) = 0 := by
  have h1238 : mixedVector B (Sum.inr 1238) = Sparse.eval nodeValue1238 (mixedVector B) := by
    change mixedMoment B node1238 node1238Labels = _
    exact sound1238 B hB hF
  have h2133 : mixedVector B (Sum.inr 2133) = Sparse.eval nodeValue2133 (mixedVector B) := by
    change mixedMoment B node2133 node2133Labels = _
    exact sound2133 B hB hF
  have h2513 : mixedVector B (Sum.inr 2513) = Sparse.eval nodeValue2513 (mixedVector B) := by
    change mixedMoment B node2513 node2513Labels = _
    exact sound2513 B hB hF
  have h2555 : mixedVector B (Sum.inr 2555) = Sparse.eval nodeValue2555 (mixedVector B) := by
    change mixedMoment B node2555 node2555Labels = _
    exact sound2555 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm227, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1238, h2133, h2513, h2555, h2738, h2744, h4084, reducedSource193] using sourceEq227 B hB

theorem rowSound193 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row193 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck193, numericCheck193, reducedZero193 B hB hF, mul_zero]

theorem reducedZero194 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource194 (mixedVector B) = 0 := by
  have h2555 : mixedVector B (Sum.inr 2555) = Sparse.eval nodeValue2555 (mixedVector B) := by
    change mixedMoment B node2555 node2555Labels = _
    exact sound2555 B hB hF
  have h2559 : mixedVector B (Sum.inr 2559) = Sparse.eval nodeValue2559 (mixedVector B) := by
    change mixedMoment B node2559 node2559Labels = _
    exact sound2559 B hB hF
  have h2560 : mixedVector B (Sum.inr 2560) = Sparse.eval nodeValue2560 (mixedVector B) := by
    change mixedMoment B node2560 node2560Labels = _
    exact sound2560 B hB hF
  have h2592 : mixedVector B (Sum.inr 2592) = Sparse.eval nodeValue2592 (mixedVector B) := by
    change mixedMoment B node2592 node2592Labels = _
    exact sound2592 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm228, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2555, h2559, h2560, h2592, h2744, h3541, h4084, reducedSource194] using sourceEq228 B hB

theorem rowSound194 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row194 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck194, numericCheck194, reducedZero194 B hB hF, mul_zero]

theorem reducedZero195 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource195 (mixedVector B) = 0 := by
  have h1245 : mixedVector B (Sum.inr 1245) = Sparse.eval nodeValue1245 (mixedVector B) := by
    change mixedMoment B node1245 node1245Labels = _
    exact sound1245 B hB hF
  have h2522 : mixedVector B (Sum.inr 2522) = Sparse.eval nodeValue2522 (mixedVector B) := by
    change mixedMoment B node2522 node2522Labels = _
    exact sound2522 B hB hF
  have h2560 : mixedVector B (Sum.inr 2560) = Sparse.eval nodeValue2560 (mixedVector B) := by
    change mixedMoment B node2560 node2560Labels = _
    exact sound2560 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm229, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1245, h2522, h2560, h2740, h2744, h4084, reducedSource195] using sourceEq229 B hB

theorem rowSound195 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row195 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck195, numericCheck195, reducedZero195 B hB hF, mul_zero]

theorem reducedZero196 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource196 (mixedVector B) = 0 := by
  have h2133 : mixedVector B (Sum.inr 2133) = Sparse.eval nodeValue2133 (mixedVector B) := by
    change mixedMoment B node2133 node2133Labels = _
    exact sound2133 B hB hF
  have h2136 : mixedVector B (Sum.inr 2136) = Sparse.eval nodeValue2136 (mixedVector B) := by
    change mixedMoment B node2136 node2136Labels = _
    exact sound2136 B hB hF
  have h2138 : mixedVector B (Sum.inr 2138) = Sparse.eval nodeValue2138 (mixedVector B) := by
    change mixedMoment B node2138 node2138Labels = _
    exact sound2138 B hB hF
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm230, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2133, h2136, h2138, h2279, h2744, h4084, reducedSource196] using sourceEq230 B hB

theorem rowSound196 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row196 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck196, numericCheck196, reducedZero196 B hB hF, mul_zero]

theorem reducedZero197 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource197 (mixedVector B) = 0 := by
  have h1244 : mixedVector B (Sum.inr 1244) = Sparse.eval nodeValue1244 (mixedVector B) := by
    change mixedMoment B node1244 node1244Labels = _
    exact sound1244 B hB hF
  have h2136 : mixedVector B (Sum.inr 2136) = Sparse.eval nodeValue2136 (mixedVector B) := by
    change mixedMoment B node2136 node2136Labels = _
    exact sound2136 B hB hF
  have h2520 : mixedVector B (Sum.inr 2520) = Sparse.eval nodeValue2520 (mixedVector B) := by
    change mixedMoment B node2520 node2520Labels = _
    exact sound2520 B hB hF
  have h2559 : mixedVector B (Sum.inr 2559) = Sparse.eval nodeValue2559 (mixedVector B) := by
    change mixedMoment B node2559 node2559Labels = _
    exact sound2559 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm231, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1244, h2136, h2520, h2559, h2744, h4084, reducedSource197] using sourceEq231 B hB

theorem rowSound197 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row197 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck197, numericCheck197, reducedZero197 B hB hF, mul_zero]

theorem reducedZero198 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource198 (mixedVector B) = 0 := by
  have h1006 : mixedVector B (Sum.inr 1006) = Sparse.eval nodeValue1006 (mixedVector B) := by
    change mixedMoment B node1006 node1006Labels = _
    exact sound1006 B hB hF
  have h1010 : mixedVector B (Sum.inr 1010) = Sparse.eval nodeValue1010 (mixedVector B) := by
    change mixedMoment B node1010 node1010Labels = _
    exact sound1010 B hB hF
  have h1011 : mixedVector B (Sum.inr 1011) = Sparse.eval nodeValue1011 (mixedVector B) := by
    change mixedMoment B node1011 node1011Labels = _
    exact sound1011 B hB hF
  have h1084 : mixedVector B (Sum.inr 1084) = Sparse.eval nodeValue1084 (mixedVector B) := by
    change mixedMoment B node1084 node1084Labels = _
    exact sound1084 B hB hF
  have h2405 : mixedVector B (Sum.inr 2405) = Sparse.eval nodeValue2405 (mixedVector B) := by
    change mixedMoment B node2405 node2405Labels = _
    exact sound2405 B hB hF
  have h2408 : mixedVector B (Sum.inr 2408) = Sparse.eval nodeValue2408 (mixedVector B) := by
    change mixedMoment B node2408 node2408Labels = _
    exact sound2408 B hB hF
  have h2409 : mixedVector B (Sum.inr 2409) = Sparse.eval nodeValue2409 (mixedVector B) := by
    change mixedMoment B node2409 node2409Labels = _
    exact sound2409 B hB hF
  have h2463 : mixedVector B (Sum.inr 2463) = Sparse.eval nodeValue2463 (mixedVector B) := by
    change mixedMoment B node2463 node2463Labels = _
    exact sound2463 B hB hF
  have h2465 : mixedVector B (Sum.inr 2465) = Sparse.eval nodeValue2465 (mixedVector B) := by
    change mixedMoment B node2465 node2465Labels = _
    exact sound2465 B hB hF
  have h2466 : mixedVector B (Sum.inr 2466) = Sparse.eval nodeValue2466 (mixedVector B) := by
    change mixedMoment B node2466 node2466Labels = _
    exact sound2466 B hB hF
  have h2513 : mixedVector B (Sum.inr 2513) = Sparse.eval nodeValue2513 (mixedVector B) := by
    change mixedMoment B node2513 node2513Labels = _
    exact sound2513 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2735 : mixedVector B (Sum.inr 2735) = Sparse.eval nodeValue2735 (mixedVector B) := by
    change mixedMoment B node2735 node2735Labels = _
    exact sound2735 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h2776 : mixedVector B (Sum.inr 2776) = Sparse.eval nodeValue2776 (mixedVector B) := by
    change mixedMoment B node2776 node2776Labels = _
    exact sound2776 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h3889 : mixedVector B (Sum.inr 3889) = Sparse.eval nodeValue3889 (mixedVector B) := by
    change mixedMoment B node3889 node3889Labels = _
    exact sound3889 B hB hF
  simpa only [sourceForm233, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1006, h1010, h1011, h1084, h2405, h2408, h2409, h2463, h2465, h2466, h2513, h2732, h2734, h2735, h2737, h2776, h2781, h3573, h3583, h3584, h3889, reducedSource198] using sourceEq233 B hB

theorem rowSound198 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row198 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck198, numericCheck198, reducedZero198 B hB hF, mul_zero]

theorem reducedZero200 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource200 (mixedVector B) = 0 := by
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  have h3907 : mixedVector B (Sum.inr 3907) = Sparse.eval nodeValue3907 (mixedVector B) := by
    change mixedMoment B node3907 node3907Labels = _
    exact sound3907 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm235, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2773, h2774, h2777, h2782, h3907, h4092, reducedSource200] using sourceEq235 B hB

theorem rowSound200 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row200 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck200, numericCheck200, reducedZero200 B hB hF, mul_zero]

theorem reducedZero201 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource201 (mixedVector B) = 0 := by
  have h1282 : mixedVector B (Sum.inr 1282) = Sparse.eval nodeValue1282 (mixedVector B) := by
    change mixedMoment B node1282 node1282Labels = _
    exact sound1282 B hB hF
  have h1422 : mixedVector B (Sum.inr 1422) = Sparse.eval nodeValue1422 (mixedVector B) := by
    change mixedMoment B node1422 node1422Labels = _
    exact sound1422 B hB hF
  have h1424 : mixedVector B (Sum.inr 1424) = Sparse.eval nodeValue1424 (mixedVector B) := by
    change mixedMoment B node1424 node1424Labels = _
    exact sound1424 B hB hF
  have h1436 : mixedVector B (Sum.inr 1436) = Sparse.eval nodeValue1436 (mixedVector B) := by
    change mixedMoment B node1436 node1436Labels = _
    exact sound1436 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm236, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1282, h1422, h1424, h1436, h2777, h4092, reducedSource201] using sourceEq236 B hB

theorem rowSound201 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row201 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck201, numericCheck201, reducedZero201 B hB hF, mul_zero]

theorem reducedZero202 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource202 (mixedVector B) = 0 := by
  have h1436 : mixedVector B (Sum.inr 1436) = Sparse.eval nodeValue1436 (mixedVector B) := by
    change mixedMoment B node1436 node1436Labels = _
    exact sound1436 B hB hF
  have h2759 : mixedVector B (Sum.inr 2759) = Sparse.eval nodeValue2759 (mixedVector B) := by
    change mixedMoment B node2759 node2759Labels = _
    exact sound2759 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm237, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1436, h2759, h2769, h2777, h3054, h4092, reducedSource202] using sourceEq237 B hB

theorem rowSound202 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row202 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck202, numericCheck202, reducedZero202 B hB hF, mul_zero]

theorem reducedZero203 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource203 (mixedVector B) = 0 := by
  have h1283 : mixedVector B (Sum.inr 1283) = Sparse.eval nodeValue1283 (mixedVector B) := by
    change mixedMoment B node1283 node1283Labels = _
    exact sound1283 B hB hF
  have h2582 : mixedVector B (Sum.inr 2582) = Sparse.eval nodeValue2582 (mixedVector B) := by
    change mixedMoment B node2582 node2582Labels = _
    exact sound2582 B hB hF
  have h2651 : mixedVector B (Sum.inr 2651) = Sparse.eval nodeValue2651 (mixedVector B) := by
    change mixedMoment B node2651 node2651Labels = _
    exact sound2651 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm238, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1283, h2582, h2651, h2774, h2777, h4092, reducedSource203] using sourceEq238 B hB

theorem rowSound203 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row203 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck203, numericCheck203, reducedZero203 B hB hF, mul_zero]

theorem reducedZero204 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource204 (mixedVector B) = 0 := by
  have h1422 : mixedVector B (Sum.inr 1422) = Sparse.eval nodeValue1422 (mixedVector B) := by
    change mixedMoment B node1422 node1422Labels = _
    exact sound1422 B hB hF
  have h2580 : mixedVector B (Sum.inr 2580) = Sparse.eval nodeValue2580 (mixedVector B) := by
    change mixedMoment B node2580 node2580Labels = _
    exact sound2580 B hB hF
  have h2582 : mixedVector B (Sum.inr 2582) = Sparse.eval nodeValue2582 (mixedVector B) := by
    change mixedMoment B node2582 node2582Labels = _
    exact sound2582 B hB hF
  have h2600 : mixedVector B (Sum.inr 2600) = Sparse.eval nodeValue2600 (mixedVector B) := by
    change mixedMoment B node2600 node2600Labels = _
    exact sound2600 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm239, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1422, h2580, h2582, h2600, h2777, h3038, h4092, reducedSource204] using sourceEq239 B hB

theorem rowSound204 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row204 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck204, numericCheck204, reducedZero204 B hB hF, mul_zero]

theorem reducedZero205 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource205 (mixedVector B) = 0 := by
  have h1280 : mixedVector B (Sum.inr 1280) = Sparse.eval nodeValue1280 (mixedVector B) := by
    change mixedMoment B node1280 node1280Labels = _
    exact sound1280 B hB hF
  have h2580 : mixedVector B (Sum.inr 2580) = Sparse.eval nodeValue2580 (mixedVector B) := by
    change mixedMoment B node2580 node2580Labels = _
    exact sound2580 B hB hF
  have h2647 : mixedVector B (Sum.inr 2647) = Sparse.eval nodeValue2647 (mixedVector B) := by
    change mixedMoment B node2647 node2647Labels = _
    exact sound2647 B hB hF
  have h2759 : mixedVector B (Sum.inr 2759) = Sparse.eval nodeValue2759 (mixedVector B) := by
    change mixedMoment B node2759 node2759Labels = _
    exact sound2759 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm240, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1280, h2580, h2647, h2759, h2773, h2777, h4092, reducedSource205] using sourceEq240 B hB

theorem rowSound205 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row205 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck205, numericCheck205, reducedZero205 B hB hF, mul_zero]

theorem reducedZero206 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource206 (mixedVector B) = 0 := by
  have h1280 : mixedVector B (Sum.inr 1280) = Sparse.eval nodeValue1280 (mixedVector B) := by
    change mixedMoment B node1280 node1280Labels = _
    exact sound1280 B hB hF
  have h1282 : mixedVector B (Sum.inr 1282) = Sparse.eval nodeValue1282 (mixedVector B) := by
    change mixedMoment B node1282 node1282Labels = _
    exact sound1282 B hB hF
  have h1283 : mixedVector B (Sum.inr 1283) = Sparse.eval nodeValue1283 (mixedVector B) := by
    change mixedMoment B node1283 node1283Labels = _
    exact sound1283 B hB hF
  have h1306 : mixedVector B (Sum.inr 1306) = Sparse.eval nodeValue1306 (mixedVector B) := by
    change mixedMoment B node1306 node1306Labels = _
    exact sound1306 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm241, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1280, h1282, h1283, h1306, h2777, h4092, reducedSource206] using sourceEq241 B hB

theorem rowSound206 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row206 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck206, numericCheck206, reducedZero206 B hB hF, mul_zero]

theorem sourceRowsAt192 : MixedData.sourceRows (192 : Fin 2425) =
    MixedData.row192 := by decide +kernel

theorem sourceRowsAt193 : MixedData.sourceRows (193 : Fin 2425) =
    MixedData.row193 := by decide +kernel

theorem sourceRowsAt194 : MixedData.sourceRows (194 : Fin 2425) =
    MixedData.row194 := by decide +kernel

theorem sourceRowsAt195 : MixedData.sourceRows (195 : Fin 2425) =
    MixedData.row195 := by decide +kernel

theorem sourceRowsAt196 : MixedData.sourceRows (196 : Fin 2425) =
    MixedData.row196 := by decide +kernel

theorem sourceRowsAt197 : MixedData.sourceRows (197 : Fin 2425) =
    MixedData.row197 := by decide +kernel

theorem sourceRowsAt198 : MixedData.sourceRows (198 : Fin 2425) =
    MixedData.row198 := by decide +kernel

theorem sourceRowsAt199 : MixedData.sourceRows (199 : Fin 2425) =
    MixedData.row199 := by decide +kernel

theorem sourceRowsAt200 : MixedData.sourceRows (200 : Fin 2425) =
    MixedData.row200 := by decide +kernel

theorem sourceRowsAt201 : MixedData.sourceRows (201 : Fin 2425) =
    MixedData.row201 := by decide +kernel

theorem sourceRowsAt202 : MixedData.sourceRows (202 : Fin 2425) =
    MixedData.row202 := by decide +kernel

theorem sourceRowsAt203 : MixedData.sourceRows (203 : Fin 2425) =
    MixedData.row203 := by decide +kernel

theorem sourceRowsAt204 : MixedData.sourceRows (204 : Fin 2425) =
    MixedData.row204 := by decide +kernel

theorem sourceRowsAt205 : MixedData.sourceRows (205 : Fin 2425) =
    MixedData.row205 := by decide +kernel

theorem sourceRowsAt206 : MixedData.sourceRows (206 : Fin 2425) =
    MixedData.row206 := by decide +kernel

theorem sourceRowsAt207 : MixedData.sourceRows (207 : Fin 2425) =
    MixedData.row207 := by decide +kernel

theorem chunkSound12_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 12) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 192 ∨ k.val = 193 ∨ k.val = 194 ∨ k.val = 195 ∨ k.val = 196 ∨ k.val = 197 ∨ k.val = 198 ∨ k.val = 199 ∨ k.val = 200 ∨ k.val = 201 ∨ k.val = 202 ∨ k.val = 203 ∨ k.val = 204 ∨ k.val = 205 ∨ k.val = 206 ∨ k.val = 207 := by omega
  rcases heq with h192 | h193 | h194 | h195 | h196 | h197 | h198 | h199 | h200 | h201 | h202 | h203 | h204 | h205 | h206 | h207
  · have he : k = (192 : Fin 2425) := Fin.ext h192
    subst k
    rw [sourceRowsAt192]
    exact rowSound192 B hB hF
  · have he : k = (193 : Fin 2425) := Fin.ext h193
    subst k
    rw [sourceRowsAt193]
    exact rowSound193 B hB hF
  · have he : k = (194 : Fin 2425) := Fin.ext h194
    subst k
    rw [sourceRowsAt194]
    exact rowSound194 B hB hF
  · have he : k = (195 : Fin 2425) := Fin.ext h195
    subst k
    rw [sourceRowsAt195]
    exact rowSound195 B hB hF
  · have he : k = (196 : Fin 2425) := Fin.ext h196
    subst k
    rw [sourceRowsAt196]
    exact rowSound196 B hB hF
  · have he : k = (197 : Fin 2425) := Fin.ext h197
    subst k
    rw [sourceRowsAt197]
    exact rowSound197 B hB hF
  · have he : k = (198 : Fin 2425) := Fin.ext h198
    subst k
    rw [sourceRowsAt198]
    exact rowSound198 B hB hF
  · have he : k = (199 : Fin 2425) := Fin.ext h199
    subst k
    rw [sourceRowsAt199]
    exact rowSound199_e B hB hF
  · have he : k = (200 : Fin 2425) := Fin.ext h200
    subst k
    rw [sourceRowsAt200]
    exact rowSound200 B hB hF
  · have he : k = (201 : Fin 2425) := Fin.ext h201
    subst k
    rw [sourceRowsAt201]
    exact rowSound201 B hB hF
  · have he : k = (202 : Fin 2425) := Fin.ext h202
    subst k
    rw [sourceRowsAt202]
    exact rowSound202 B hB hF
  · have he : k = (203 : Fin 2425) := Fin.ext h203
    subst k
    rw [sourceRowsAt203]
    exact rowSound203 B hB hF
  · have he : k = (204 : Fin 2425) := Fin.ext h204
    subst k
    rw [sourceRowsAt204]
    exact rowSound204 B hB hF
  · have he : k = (205 : Fin 2425) := Fin.ext h205
    subst k
    rw [sourceRowsAt205]
    exact rowSound205 B hB hF
  · have he : k = (206 : Fin 2425) := Fin.ext h206
    subst k
    rw [sourceRowsAt206]
    exact rowSound206 B hB hF
  · have he : k = (207 : Fin 2425) := Fin.ext h207
    subst k
    rw [sourceRowsAt207]
    exact rowSound207_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e_oai
