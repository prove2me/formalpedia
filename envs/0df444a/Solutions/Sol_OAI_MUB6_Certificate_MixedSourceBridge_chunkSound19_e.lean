-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:14:49.682692+00:00
-- url     : https://prove2.me/submissions/8c1c10bd-542c-400c-a1cd-d95b5ffabcdf

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound310_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound311_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound319_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem canonical1761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1761 raw1761Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw1761 raw1761Labels = mixedMoment B raw1761step0 raw1761step0Labels := by
      have ha : raw1761step0 = (fun i j => raw1761 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1761step0 raw1761; decide +kernel
      have hl : raw1761step0Labels = raw1761Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1761 raw1761Labels permutation152 permutation4
    mixedMoment B raw1761step0 raw1761step0Labels = mixedMoment B raw1761step1 raw1761step1Labels := by
      have ha : raw1761step1 = raw1761step0 := by apply Matrix.ext; unfold raw1761step1 raw1761step0; decide +kernel
      have hl : raw1761step0Labels = labelEmbedding7 ∘ raw1761step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1761step0 raw1761step0Labels raw1761step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

theorem canonical1762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1762 raw1762Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw1762 raw1762Labels = mixedMoment B raw1762step0 raw1762step0Labels := by
      have ha : raw1762step0 = (fun i j => raw1762 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1762step0 raw1762; decide +kernel
      have hl : raw1762step0Labels = raw1762Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1762 raw1762Labels permutation152 permutation4
    _ = mixedMoment B node2051 node2051Labels := by rfl

theorem canonical1763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1763 raw1763Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw1763 raw1763Labels = mixedMoment B raw1763step0 raw1763step0Labels := by
      have ha : raw1763step0 = (fun i j => raw1763 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1763step0 raw1763; decide +kernel
      have hl : raw1763step0Labels = raw1763Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1763 raw1763Labels permutation152 permutation6
    mixedMoment B raw1763step0 raw1763step0Labels = mixedMoment B raw1763step1 raw1763step1Labels := by
      have ha : raw1763step1 = -raw1763step0 := by apply Matrix.ext; change ∀ i j, raw1763step1 i j = -(raw1763step0 i j); unfold raw1763step1 raw1763step0; decide +kernel
      have hl : raw1763step1Labels = raw1763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1763step1 raw1763step1Labels = mixedMoment B raw1763step2 raw1763step2Labels := by
      have ha : raw1763step2 = raw1763step1 := by apply Matrix.ext; unfold raw1763step2 raw1763step1; decide +kernel
      have hl : raw1763step1Labels = labelEmbedding1 ∘ raw1763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1763step1 raw1763step1Labels raw1763step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2191 node2191Labels := by rfl

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

theorem canonical1815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1815 raw1815Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw1815 raw1815Labels = mixedMoment B raw1815step0 raw1815step0Labels := by
      have ha : raw1815step0 = (fun i j => raw1815 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1815step0 raw1815; decide +kernel
      have hl : raw1815step0Labels = raw1815Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1815 raw1815Labels permutation32 permutation4
    mixedMoment B raw1815step0 raw1815step0Labels = mixedMoment B raw1815step1 raw1815step1Labels := by
      have ha : raw1815step1 = raw1815step0 := by apply Matrix.ext; unfold raw1815step1 raw1815step0; decide +kernel
      have hl : raw1815step0Labels = labelEmbedding7 ∘ raw1815step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1815step0 raw1815step0Labels raw1815step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical1816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1816 raw1816Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw1816 raw1816Labels = mixedMoment B raw1816step0 raw1816step0Labels := by
      have ha : raw1816step0 = (fun i j => raw1816 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1816step0 raw1816; decide +kernel
      have hl : raw1816step0Labels = raw1816Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1816 raw1816Labels permutation32 permutation4
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical1817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1817 raw1817Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw1817 raw1817Labels = mixedMoment B raw1817step0 raw1817step0Labels := by
      have ha : raw1817step0 = (fun i j => raw1817 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1817step0 raw1817; decide +kernel
      have hl : raw1817step0Labels = raw1817Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1817 raw1817Labels permutation44 permutation6
    mixedMoment B raw1817step0 raw1817step0Labels = mixedMoment B raw1817step1 raw1817step1Labels := by
      have ha : raw1817step1 = -raw1817step0 := by apply Matrix.ext; change ∀ i j, raw1817step1 i j = -(raw1817step0 i j); unfold raw1817step1 raw1817step0; decide +kernel
      have hl : raw1817step1Labels = raw1817step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1817step1 raw1817step1Labels = mixedMoment B raw1817step2 raw1817step2Labels := by
      have ha : raw1817step2 = raw1817step1 := by apply Matrix.ext; unfold raw1817step2 raw1817step1; decide +kernel
      have hl : raw1817step1Labels = labelEmbedding1 ∘ raw1817step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1817step1 raw1817step1Labels raw1817step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

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

theorem canonical2259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2259 raw2259Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw2259 raw2259Labels = mixedMoment B raw2259step0 raw2259step0Labels := by
      have ha : raw2259step0 = (fun i j => raw2259 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2259step0 raw2259; decide +kernel
      have hl : raw2259step0Labels = raw2259Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2259 raw2259Labels permutation152 permutation4
    mixedMoment B raw2259step0 raw2259step0Labels = mixedMoment B raw2259step1 raw2259step1Labels := by
      have ha : raw2259step1 = raw2259step0 := by apply Matrix.ext; unfold raw2259step1 raw2259step0; decide +kernel
      have hl : raw2259step0Labels = labelEmbedding7 ∘ raw2259step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2259step0 raw2259step0Labels raw2259step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

theorem canonical2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2260 raw2260Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw2260 raw2260Labels = mixedMoment B raw2260step0 raw2260step0Labels := by
      have ha : raw2260step0 = (fun i j => raw2260 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2260step0 raw2260; decide +kernel
      have hl : raw2260step0Labels = raw2260Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2260 raw2260Labels permutation152 permutation4
    _ = mixedMoment B node2694 node2694Labels := by rfl

theorem canonical2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2261 raw2261Labels = mixedMoment B node3493 node3493Labels := by
  calc
    mixedMoment B raw2261 raw2261Labels = mixedMoment B raw2261step0 raw2261step0Labels := by
      have ha : raw2261step0 = (fun i j => raw2261 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2261step0 raw2261; decide +kernel
      have hl : raw2261step0Labels = raw2261Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2261 raw2261Labels permutation152 permutation6
    mixedMoment B raw2261step0 raw2261step0Labels = mixedMoment B raw2261step1 raw2261step1Labels := by
      have ha : raw2261step1 = -raw2261step0 := by apply Matrix.ext; change ∀ i j, raw2261step1 i j = -(raw2261step0 i j); unfold raw2261step1 raw2261step0; decide +kernel
      have hl : raw2261step1Labels = raw2261step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2261step1 raw2261step1Labels = mixedMoment B raw2261step2 raw2261step2Labels := by
      have ha : raw2261step2 = raw2261step1 := by apply Matrix.ext; unfold raw2261step2 raw2261step1; decide +kernel
      have hl : raw2261step1Labels = labelEmbedding1 ∘ raw2261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2261step1 raw2261step1Labels raw2261step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3493 node3493Labels := by rfl

theorem canonical2271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2271 raw2271Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw2271 raw2271Labels = mixedMoment B raw2271step0 raw2271step0Labels := by
      have ha : raw2271step0 = (fun i j => raw2271 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2271step0 raw2271; decide +kernel
      have hl : raw2271step0Labels = raw2271Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2271 raw2271Labels permutation32 permutation4
    mixedMoment B raw2271step0 raw2271step0Labels = mixedMoment B raw2271step1 raw2271step1Labels := by
      have ha : raw2271step1 = raw2271step0 := by apply Matrix.ext; unfold raw2271step1 raw2271step0; decide +kernel
      have hl : raw2271step0Labels = labelEmbedding7 ∘ raw2271step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2271step0 raw2271step0Labels raw2271step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical2272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2272 raw2272Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw2272 raw2272Labels = mixedMoment B raw2272step0 raw2272step0Labels := by
      have ha : raw2272step0 = (fun i j => raw2272 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2272step0 raw2272; decide +kernel
      have hl : raw2272step0Labels = raw2272Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2272 raw2272Labels permutation32 permutation4
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical2273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2273 raw2273Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw2273 raw2273Labels = mixedMoment B raw2273step0 raw2273step0Labels := by
      have ha : raw2273step0 = (fun i j => raw2273 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2273step0 raw2273; decide +kernel
      have hl : raw2273step0Labels = raw2273Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2273 raw2273Labels permutation34 permutation6
    mixedMoment B raw2273step0 raw2273step0Labels = mixedMoment B raw2273step1 raw2273step1Labels := by
      have ha : raw2273step1 = -raw2273step0 := by apply Matrix.ext; change ∀ i j, raw2273step1 i j = -(raw2273step0 i j); unfold raw2273step1 raw2273step0; decide +kernel
      have hl : raw2273step1Labels = raw2273step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2273step1 raw2273step1Labels = mixedMoment B raw2273step2 raw2273step2Labels := by
      have ha : raw2273step2 = raw2273step1 := by apply Matrix.ext; unfold raw2273step2 raw2273step1; decide +kernel
      have hl : raw2273step1Labels = labelEmbedding1 ∘ raw2273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2273step1 raw2273step1Labels raw2273step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2274 raw2274Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw2274 raw2274Labels = mixedMoment B raw2274step0 raw2274step0Labels := by
      have ha : raw2274step0 = (fun i j => raw2274 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2274step0 raw2274; decide +kernel
      have hl : raw2274step0Labels = raw2274Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2274 raw2274Labels permutation32 permutation4
    mixedMoment B raw2274step0 raw2274step0Labels = mixedMoment B raw2274step1 raw2274step1Labels := by
      have ha : raw2274step1 = raw2274step0 := by apply Matrix.ext; unfold raw2274step1 raw2274step0; decide +kernel
      have hl : raw2274step0Labels = labelEmbedding7 ∘ raw2274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2274step0 raw2274step0Labels raw2274step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2275 raw2275Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw2275 raw2275Labels = mixedMoment B raw2275step0 raw2275step0Labels := by
      have ha : raw2275step0 = (fun i j => raw2275 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2275step0 raw2275; decide +kernel
      have hl : raw2275step0Labels = raw2275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2275 raw2275Labels permutation32 permutation4
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2276 raw2276Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw2276 raw2276Labels = mixedMoment B raw2276step0 raw2276step0Labels := by
      have ha : raw2276step0 = (fun i j => raw2276 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2276step0 raw2276; decide +kernel
      have hl : raw2276step0Labels = raw2276Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2276 raw2276Labels permutation32 permutation6
    mixedMoment B raw2276step0 raw2276step0Labels = mixedMoment B raw2276step1 raw2276step1Labels := by
      have ha : raw2276step1 = -raw2276step0 := by apply Matrix.ext; change ∀ i j, raw2276step1 i j = -(raw2276step0 i j); unfold raw2276step1 raw2276step0; decide +kernel
      have hl : raw2276step1Labels = raw2276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2276step1 raw2276step1Labels = mixedMoment B raw2276step2 raw2276step2Labels := by
      have ha : raw2276step2 = raw2276step1 := by apply Matrix.ext; unfold raw2276step2 raw2276step1; decide +kernel
      have hl : raw2276step1Labels = labelEmbedding1 ∘ raw2276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2276step1 raw2276step1Labels raw2276step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

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

theorem canonical2301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2301 raw2301Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw2301 raw2301Labels = mixedMoment B raw2301step0 raw2301step0Labels := by
      have ha : raw2301step0 = (fun i j => raw2301 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2301step0 raw2301; decide +kernel
      have hl : raw2301step0Labels = raw2301Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2301 raw2301Labels permutation8 permutation4
    mixedMoment B raw2301step0 raw2301step0Labels = mixedMoment B raw2301step1 raw2301step1Labels := by
      have ha : raw2301step1 = raw2301step0 := by apply Matrix.ext; unfold raw2301step1 raw2301step0; decide +kernel
      have hl : raw2301step0Labels = labelEmbedding7 ∘ raw2301step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2301step0 raw2301step0Labels raw2301step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

theorem canonical2302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2302 raw2302Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw2302 raw2302Labels = mixedMoment B raw2302step0 raw2302step0Labels := by
      have ha : raw2302step0 = (fun i j => raw2302 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2302step0 raw2302; decide +kernel
      have hl : raw2302step0Labels = raw2302Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2302 raw2302Labels permutation8 permutation4
    _ = mixedMoment B node2767 node2767Labels := by rfl

theorem canonical2303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2303 raw2303Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw2303 raw2303Labels = mixedMoment B raw2303step0 raw2303step0Labels := by
      have ha : raw2303step0 = (fun i j => raw2303 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2303step0 raw2303; decide +kernel
      have hl : raw2303step0Labels = raw2303Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2303 raw2303Labels permutation10 permutation6
    mixedMoment B raw2303step0 raw2303step0Labels = mixedMoment B raw2303step1 raw2303step1Labels := by
      have ha : raw2303step1 = -raw2303step0 := by apply Matrix.ext; change ∀ i j, raw2303step1 i j = -(raw2303step0 i j); unfold raw2303step1 raw2303step0; decide +kernel
      have hl : raw2303step1Labels = raw2303step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2303step1 raw2303step1Labels = mixedMoment B raw2303step2 raw2303step2Labels := by
      have ha : raw2303step2 = raw2303step1 := by apply Matrix.ext; unfold raw2303step2 raw2303step1; decide +kernel
      have hl : raw2303step1Labels = labelEmbedding1 ∘ raw2303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2303step1 raw2303step1Labels raw2303step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3627 node3627Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical5658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5658 raw5658Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw5658 raw5658Labels = mixedMoment B raw5658step0 raw5658step0Labels := by
      have hz : ∀ j, raw5658 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5658step0 = (fun i j => raw5658 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5658step0 raw5658; decide +kernel
      have hl : raw5658step0Labels = raw5658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5658 raw5658Labels permutation265 hz
    mixedMoment B raw5658step0 raw5658step0Labels = mixedMoment B raw5658step1 raw5658step1Labels := by
      have ha : raw5658step1 = (fun i j => raw5658step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5658step1 raw5658step0; decide +kernel
      have hl : raw5658step1Labels = raw5658step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5658step0 raw5658step0Labels permutation32 permutation6
    mixedMoment B raw5658step1 raw5658step1Labels = mixedMoment B raw5658step2 raw5658step2Labels := by
      have ha : raw5658step2 = raw5658step1 := by apply Matrix.ext; unfold raw5658step2 raw5658step1; decide +kernel
      have hl : raw5658step1Labels = labelEmbedding9 ∘ raw5658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5658step1 raw5658step1Labels raw5658step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical5684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5684 raw5684Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw5684 raw5684Labels = mixedMoment B raw5684step0 raw5684step0Labels := by
      have hz : ∀ j, raw5684 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5684step0 = (fun i j => raw5684 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5684step0 raw5684; decide +kernel
      have hl : raw5684step0Labels = raw5684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5684 raw5684Labels permutation265 hz
    mixedMoment B raw5684step0 raw5684step0Labels = mixedMoment B raw5684step1 raw5684step1Labels := by
      have ha : raw5684step1 = (fun i j => raw5684step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5684step1 raw5684step0; decide +kernel
      have hl : raw5684step1Labels = raw5684step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5684step0 raw5684step0Labels permutation32 permutation6
    mixedMoment B raw5684step1 raw5684step1Labels = mixedMoment B raw5684step2 raw5684step2Labels := by
      have ha : raw5684step2 = raw5684step1 := by apply Matrix.ext; unfold raw5684step2 raw5684step1; decide +kernel
      have hl : raw5684step1Labels = labelEmbedding9 ∘ raw5684step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5684step1 raw5684step1Labels raw5684step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical5749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5749 raw5749Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw5749 raw5749Labels = mixedMoment B raw5749step0 raw5749step0Labels := by
      have hz : ∀ j, raw5749 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5749step0 = (fun i j => raw5749 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5749step0 raw5749; decide +kernel
      have hl : raw5749step0Labels = raw5749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5749 raw5749Labels permutation265 hz
    mixedMoment B raw5749step0 raw5749step0Labels = mixedMoment B raw5749step1 raw5749step1Labels := by
      have ha : raw5749step1 = (fun i j => raw5749step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5749step1 raw5749step0; decide +kernel
      have hl : raw5749step1Labels = raw5749step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5749step0 raw5749step0Labels permutation48 permutation4
    mixedMoment B raw5749step1 raw5749step1Labels = mixedMoment B raw5749step2 raw5749step2Labels := by
      have ha : raw5749step2 = -raw5749step1 := by apply Matrix.ext; change ∀ i j, raw5749step2 i j = -(raw5749step1 i j); unfold raw5749step2 raw5749step1; decide +kernel
      have hl : raw5749step2Labels = raw5749step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3625 node3625Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5768 raw5768Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw5768 raw5768Labels = mixedMoment B raw5768step0 raw5768step0Labels := by
      have hz : ∀ j, raw5768 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5768step0 = (fun i j => raw5768 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5768step0 raw5768; decide +kernel
      have hl : raw5768step0Labels = raw5768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5768 raw5768Labels permutation265 hz
    mixedMoment B raw5768step0 raw5768step0Labels = mixedMoment B raw5768step1 raw5768step1Labels := by
      have ha : raw5768step1 = (fun i j => raw5768step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5768step1 raw5768step0; decide +kernel
      have hl : raw5768step1Labels = raw5768step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5768step0 raw5768step0Labels permutation44 permutation4
    mixedMoment B raw5768step1 raw5768step1Labels = mixedMoment B raw5768step2 raw5768step2Labels := by
      have ha : raw5768step2 = -raw5768step1 := by apply Matrix.ext; change ∀ i j, raw5768step2 i j = -(raw5768step1 i j); unfold raw5768step2 raw5768step1; decide +kernel
      have hl : raw5768step2Labels = raw5768step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2262 node2262Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6379 raw6379Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw6379 raw6379Labels = mixedMoment B raw6379step0 raw6379step0Labels := by
      have ha : raw6379step0 = (fun i j => raw6379 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6379step0 raw6379; decide +kernel
      have hl : raw6379step0Labels = raw6379Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6379 raw6379Labels permutation152 permutation6
    mixedMoment B raw6379step0 raw6379step0Labels = mixedMoment B raw6379step1 raw6379step1Labels := by
      have ha : raw6379step1 = raw6379step0 := by apply Matrix.ext; unfold raw6379step1 raw6379step0; decide +kernel
      have hl : raw6379step0Labels = labelEmbedding9 ∘ raw6379step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6379step0 raw6379step0Labels raw6379step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical6390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6390 raw6390Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw6390 raw6390Labels = mixedMoment B raw6390step0 raw6390step0Labels := by
      have hz : ∀ j, raw6390 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6390step0 = (fun i j => raw6390 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6390step0 raw6390; decide +kernel
      have hl : raw6390step0Labels = raw6390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6390 raw6390Labels permutation346 hz
    mixedMoment B raw6390step0 raw6390step0Labels = mixedMoment B raw6390step1 raw6390step1Labels := by
      have ha : raw6390step1 = (fun i j => raw6390step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6390step1 raw6390step0; decide +kernel
      have hl : raw6390step1Labels = raw6390step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6390step0 raw6390step0Labels permutation32 permutation6
    mixedMoment B raw6390step1 raw6390step1Labels = mixedMoment B raw6390step2 raw6390step2Labels := by
      have ha : raw6390step2 = raw6390step1 := by apply Matrix.ext; unfold raw6390step2 raw6390step1; decide +kernel
      have hl : raw6390step1Labels = labelEmbedding9 ∘ raw6390step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6390step1 raw6390step1Labels raw6390step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

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

theorem canonical6450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6450 raw6450Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw6450 raw6450Labels = mixedMoment B raw6450step0 raw6450step0Labels := by
      have ha : raw6450step0 = (fun i j => raw6450 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6450step0 raw6450; decide +kernel
      have hl : raw6450step0Labels = raw6450Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6450 raw6450Labels permutation170 permutation4
    mixedMoment B raw6450step0 raw6450step0Labels = mixedMoment B raw6450step1 raw6450step1Labels := by
      have ha : raw6450step1 = -raw6450step0 := by apply Matrix.ext; change ∀ i j, raw6450step1 i j = -(raw6450step0 i j); unfold raw6450step1 raw6450step0; decide +kernel
      have hl : raw6450step1Labels = raw6450step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3539 node3539Labels := by rfl

theorem canonical6456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6456 raw6456Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw6456 raw6456Labels = mixedMoment B raw6456step0 raw6456step0Labels := by
      have hz : ∀ j, raw6456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6456step0 = (fun i j => raw6456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6456step0 raw6456; decide +kernel
      have hl : raw6456step0Labels = raw6456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6456 raw6456Labels permutation346 hz
    mixedMoment B raw6456step0 raw6456step0Labels = mixedMoment B raw6456step1 raw6456step1Labels := by
      have ha : raw6456step1 = (fun i j => raw6456step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6456step1 raw6456step0; decide +kernel
      have hl : raw6456step1Labels = raw6456step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6456step0 raw6456step0Labels permutation32 permutation4
    mixedMoment B raw6456step1 raw6456step1Labels = mixedMoment B raw6456step2 raw6456step2Labels := by
      have ha : raw6456step2 = -raw6456step1 := by apply Matrix.ext; change ∀ i j, raw6456step2 i j = -(raw6456step1 i j); unfold raw6456step2 raw6456step1; decide +kernel
      have hl : raw6456step2Labels = raw6456step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3544 node3544Labels := by rfl

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

theorem canonical6702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6702 raw6702Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw6702 raw6702Labels = mixedMoment B raw6702step0 raw6702step0Labels := by
      have hz : ∀ j, raw6702 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6702step0 = (fun i j => raw6702 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6702step0 raw6702; decide +kernel
      have hl : raw6702step0Labels = raw6702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6702 raw6702Labels permutation346 hz
    mixedMoment B raw6702step0 raw6702step0Labels = mixedMoment B raw6702step1 raw6702step1Labels := by
      have ha : raw6702step1 = (fun i j => raw6702step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6702step1 raw6702step0; decide +kernel
      have hl : raw6702step1Labels = raw6702step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6702step0 raw6702step0Labels permutation38 permutation7
    mixedMoment B raw6702step1 raw6702step1Labels = mixedMoment B raw6702step2 raw6702step2Labels := by
      have ha : raw6702step2 = raw6702step1 := by apply Matrix.ext; unfold raw6702step2 raw6702step1; decide +kernel
      have hl : raw6702step1Labels = labelEmbedding10 ∘ raw6702step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6702step1 raw6702step1Labels raw6702step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical6707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6707 raw6707Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw6707 raw6707Labels = mixedMoment B raw6707step0 raw6707step0Labels := by
      have hz : ∀ j, raw6707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6707step0 = (fun i j => raw6707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6707step0 raw6707; decide +kernel
      have hl : raw6707step0Labels = raw6707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6707 raw6707Labels permutation346 hz
    mixedMoment B raw6707step0 raw6707step0Labels = mixedMoment B raw6707step1 raw6707step1Labels := by
      have hz : ∀ j, raw6707step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6707step1 = (fun i j => raw6707step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6707step1 raw6707step0; decide +kernel
      have hl : raw6707step1Labels = raw6707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6707step0 raw6707step0Labels permutation56 hz
    mixedMoment B raw6707step1 raw6707step1Labels = mixedMoment B raw6707step2 raw6707step2Labels := by
      have ha : raw6707step2 = (fun i j => raw6707step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6707step2 raw6707step1; decide +kernel
      have hl : raw6707step2Labels = raw6707step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6707step1 raw6707step1Labels permutation8 permutation6
    mixedMoment B raw6707step2 raw6707step2Labels = mixedMoment B raw6707step3 raw6707step3Labels := by
      have ha : raw6707step3 = raw6707step2 := by apply Matrix.ext; unfold raw6707step3 raw6707step2; decide +kernel
      have hl : raw6707step2Labels = labelEmbedding9 ∘ raw6707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6707step2 raw6707step2Labels raw6707step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

theorem canonical6710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6710 raw6710Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw6710 raw6710Labels = mixedMoment B raw6710step0 raw6710step0Labels := by
      have ha : raw6710step0 = (fun i j => raw6710 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6710step0 raw6710; decide +kernel
      have hl : raw6710step0Labels = raw6710Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6710 raw6710Labels permutation165 permutation4
    mixedMoment B raw6710step0 raw6710step0Labels = mixedMoment B raw6710step1 raw6710step1Labels := by
      have ha : raw6710step1 = -raw6710step0 := by apply Matrix.ext; change ∀ i j, raw6710step1 i j = -(raw6710step0 i j); unfold raw6710step1 raw6710step0; decide +kernel
      have hl : raw6710step1Labels = raw6710step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6710step1 raw6710step1Labels = mixedMoment B raw6710step2 raw6710step2Labels := by
      have ha : raw6710step2 = raw6710step1 := by apply Matrix.ext; unfold raw6710step2 raw6710step1; decide +kernel
      have hl : raw6710step1Labels = labelEmbedding7 ∘ raw6710step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6710step1 raw6710step1Labels raw6710step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

theorem canonical6711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6711 raw6711Labels = mixedMoment B node5223 node5223Labels := by
  calc
    mixedMoment B raw6711 raw6711Labels = mixedMoment B raw6711step0 raw6711step0Labels := by
      have ha : raw6711step0 = (fun i j => raw6711 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6711step0 raw6711; decide +kernel
      have hl : raw6711step0Labels = raw6711Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6711 raw6711Labels permutation152 permutation6
    mixedMoment B raw6711step0 raw6711step0Labels = mixedMoment B raw6711step1 raw6711step1Labels := by
      have ha : raw6711step1 = raw6711step0 := by apply Matrix.ext; unfold raw6711step1 raw6711step0; decide +kernel
      have hl : raw6711step0Labels = labelEmbedding9 ∘ raw6711step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6711step0 raw6711step0Labels raw6711step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5223 node5223Labels := by rfl

theorem canonical6713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6713 raw6713Labels = mixedMoment B node5253 node5253Labels := by
  calc
    mixedMoment B raw6713 raw6713Labels = mixedMoment B raw6713step0 raw6713step0Labels := by
      have ha : raw6713step0 = (fun i j => raw6713 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6713step0 raw6713; decide +kernel
      have hl : raw6713step0Labels = raw6713Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6713 raw6713Labels permutation152 permutation6
    mixedMoment B raw6713step0 raw6713step0Labels = mixedMoment B raw6713step1 raw6713step1Labels := by
      have ha : raw6713step1 = raw6713step0 := by apply Matrix.ext; unfold raw6713step1 raw6713step0; decide +kernel
      have hl : raw6713step0Labels = labelEmbedding9 ∘ raw6713step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6713step0 raw6713step0Labels raw6713step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5253 node5253Labels := by rfl

theorem canonical6714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6714 raw6714Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw6714 raw6714Labels = mixedMoment B raw6714step0 raw6714step0Labels := by
      have ha : raw6714step0 = (fun i j => raw6714 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6714step0 raw6714; decide +kernel
      have hl : raw6714step0Labels = raw6714Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6714 raw6714Labels permutation152 permutation6
    mixedMoment B raw6714step0 raw6714step0Labels = mixedMoment B raw6714step1 raw6714step1Labels := by
      have ha : raw6714step1 = raw6714step0 := by apply Matrix.ext; unfold raw6714step1 raw6714step0; decide +kernel
      have hl : raw6714step0Labels = labelEmbedding9 ∘ raw6714step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6714step0 raw6714step0Labels raw6714step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5254 node5254Labels := by rfl

theorem canonical6726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6726 raw6726Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw6726 raw6726Labels = mixedMoment B raw6726step0 raw6726step0Labels := by
      have hz : ∀ j, raw6726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6726step0 = (fun i j => raw6726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6726step0 raw6726; decide +kernel
      have hl : raw6726step0Labels = raw6726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6726 raw6726Labels permutation346 hz
    mixedMoment B raw6726step0 raw6726step0Labels = mixedMoment B raw6726step1 raw6726step1Labels := by
      have ha : raw6726step1 = (fun i j => raw6726step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6726step1 raw6726step0; decide +kernel
      have hl : raw6726step1Labels = raw6726step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6726step0 raw6726step0Labels permutation32 permutation6
    mixedMoment B raw6726step1 raw6726step1Labels = mixedMoment B raw6726step2 raw6726step2Labels := by
      have ha : raw6726step2 = raw6726step1 := by apply Matrix.ext; unfold raw6726step2 raw6726step1; decide +kernel
      have hl : raw6726step1Labels = labelEmbedding9 ∘ raw6726step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6726step1 raw6726step1Labels raw6726step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

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

theorem canonical6796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6796 raw6796Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw6796 raw6796Labels = mixedMoment B raw6796step0 raw6796step0Labels := by
      have hz : ∀ j, raw6796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6796step0 = (fun i j => raw6796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6796step0 raw6796; decide +kernel
      have hl : raw6796step0Labels = raw6796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6796 raw6796Labels permutation346 hz
    mixedMoment B raw6796step0 raw6796step0Labels = mixedMoment B raw6796step1 raw6796step1Labels := by
      have hz : ∀ j, raw6796step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6796step1 = (fun i j => raw6796step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6796step1 raw6796step0; decide +kernel
      have hl : raw6796step1Labels = raw6796step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6796step0 raw6796step0Labels permutation56 hz
    mixedMoment B raw6796step1 raw6796step1Labels = mixedMoment B raw6796step2 raw6796step2Labels := by
      have ha : raw6796step2 = (fun i j => raw6796step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6796step2 raw6796step1; decide +kernel
      have hl : raw6796step2Labels = raw6796step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6796step1 raw6796step1Labels permutation10 permutation4
    mixedMoment B raw6796step2 raw6796step2Labels = mixedMoment B raw6796step3 raw6796step3Labels := by
      have ha : raw6796step3 = -raw6796step2 := by apply Matrix.ext; change ∀ i j, raw6796step3 i j = -(raw6796step2 i j); unfold raw6796step3 raw6796step2; decide +kernel
      have hl : raw6796step3Labels = raw6796step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3627 node3627Labels := by rfl

theorem canonical6799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6799 raw6799Labels = mixedMoment B node3377 node3377Labels := by
  calc
    mixedMoment B raw6799 raw6799Labels = mixedMoment B raw6799step0 raw6799step0Labels := by
      have ha : raw6799step0 = (fun i j => raw6799 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6799step0 raw6799; decide +kernel
      have hl : raw6799step0Labels = raw6799Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6799 raw6799Labels permutation165 permutation4
    mixedMoment B raw6799step0 raw6799step0Labels = mixedMoment B raw6799step1 raw6799step1Labels := by
      have ha : raw6799step1 = -raw6799step0 := by apply Matrix.ext; change ∀ i j, raw6799step1 i j = -(raw6799step0 i j); unfold raw6799step1 raw6799step0; decide +kernel
      have hl : raw6799step1Labels = raw6799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3377 node3377Labels := by rfl

theorem canonical6803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6803 raw6803Labels = mixedMoment B node3531 node3531Labels := by
  calc
    mixedMoment B raw6803 raw6803Labels = mixedMoment B raw6803step0 raw6803step0Labels := by
      have ha : raw6803step0 = (fun i j => raw6803 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6803step0 raw6803; decide +kernel
      have hl : raw6803step0Labels = raw6803Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6803 raw6803Labels permutation164 permutation4
    mixedMoment B raw6803step0 raw6803step0Labels = mixedMoment B raw6803step1 raw6803step1Labels := by
      have ha : raw6803step1 = -raw6803step0 := by apply Matrix.ext; change ∀ i j, raw6803step1 i j = -(raw6803step0 i j); unfold raw6803step1 raw6803step0; decide +kernel
      have hl : raw6803step1Labels = raw6803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3531 node3531Labels := by rfl

theorem canonical6804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6804 raw6804Labels = mixedMoment B node3504 node3504Labels := by
  calc
    mixedMoment B raw6804 raw6804Labels = mixedMoment B raw6804step0 raw6804step0Labels := by
      have ha : raw6804step0 = (fun i j => raw6804 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6804step0 raw6804; decide +kernel
      have hl : raw6804step0Labels = raw6804Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6804 raw6804Labels permutation165 permutation4
    mixedMoment B raw6804step0 raw6804step0Labels = mixedMoment B raw6804step1 raw6804step1Labels := by
      have ha : raw6804step1 = -raw6804step0 := by apply Matrix.ext; change ∀ i j, raw6804step1 i j = -(raw6804step0 i j); unfold raw6804step1 raw6804step0; decide +kernel
      have hl : raw6804step1Labels = raw6804step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3504 node3504Labels := by rfl

theorem canonical6811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6811 raw6811Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw6811 raw6811Labels = mixedMoment B raw6811step0 raw6811step0Labels := by
      have hz : ∀ j, raw6811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6811step0 = (fun i j => raw6811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6811step0 raw6811; decide +kernel
      have hl : raw6811step0Labels = raw6811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6811 raw6811Labels permutation346 hz
    mixedMoment B raw6811step0 raw6811step0Labels = mixedMoment B raw6811step1 raw6811step1Labels := by
      have ha : raw6811step1 = (fun i j => raw6811step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6811step1 raw6811step0; decide +kernel
      have hl : raw6811step1Labels = raw6811step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6811step0 raw6811step0Labels permutation34 permutation4
    mixedMoment B raw6811step1 raw6811step1Labels = mixedMoment B raw6811step2 raw6811step2Labels := by
      have ha : raw6811step2 = -raw6811step1 := by apply Matrix.ext; change ∀ i j, raw6811step2 i j = -(raw6811step1 i j); unfold raw6811step2 raw6811step1; decide +kernel
      have hl : raw6811step2Labels = raw6811step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3533 node3533Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7063 raw7063Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw7063 raw7063Labels = mixedMoment B raw7063step0 raw7063step0Labels := by
      have hz : ∀ j, raw7063 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7063step0 = (fun i j => raw7063 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7063step0 raw7063; decide +kernel
      have hl : raw7063step0Labels = raw7063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7063 raw7063Labels permutation346 hz
    mixedMoment B raw7063step0 raw7063step0Labels = mixedMoment B raw7063step1 raw7063step1Labels := by
      have ha : raw7063step1 = (fun i j => raw7063step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7063step1 raw7063step0; decide +kernel
      have hl : raw7063step1Labels = raw7063step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7063step0 raw7063step0Labels permutation32 permutation6
    mixedMoment B raw7063step1 raw7063step1Labels = mixedMoment B raw7063step2 raw7063step2Labels := by
      have ha : raw7063step2 = raw7063step1 := by apply Matrix.ext; unfold raw7063step2 raw7063step1; decide +kernel
      have hl : raw7063step1Labels = labelEmbedding9 ∘ raw7063step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7063step1 raw7063step1Labels raw7063step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7193 raw7193Labels = mixedMoment B node2709 node2709Labels := by
  calc
    _ = mixedMoment B node2709 node2709Labels := by rfl

theorem canonical7194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7194 raw7194Labels = mixedMoment B node3800 node3800Labels := by
  calc
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical7195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7195 raw7195Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw7195 raw7195Labels = mixedMoment B raw7195step0 raw7195step0Labels := by
      have ha : raw7195step0 = (fun i j => raw7195 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7195step0 raw7195; decide +kernel
      have hl : raw7195step0Labels = raw7195Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7195 raw7195Labels permutation176 permutation2
    _ = mixedMoment B node3871 node3871Labels := by rfl

theorem canonical7199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7199 raw7199Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw7199 raw7199Labels = mixedMoment B raw7199step0 raw7199step0Labels := by
      have hz : ∀ j, raw7199 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7199step0 = (fun i j => raw7199 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7199step0 raw7199; decide +kernel
      have hl : raw7199step0Labels = raw7199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7199 raw7199Labels permutation520 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical7200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7200 raw7200Labels = mixedMoment B node1247 node1247Labels := by
  calc
    mixedMoment B raw7200 raw7200Labels = mixedMoment B raw7200step0 raw7200step0Labels := by
      have ha : raw7200step0 = (fun i j => raw7200 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7200step0 raw7200; decide +kernel
      have hl : raw7200step0Labels = raw7200Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7200 raw7200Labels permutation182 permutation2
    _ = mixedMoment B node1247 node1247Labels := by rfl

theorem canonical7201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7201 raw7201Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw7201 raw7201Labels = mixedMoment B raw7201step0 raw7201step0Labels := by
      have ha : raw7201step0 = (fun i j => raw7201 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7201step0 raw7201; decide +kernel
      have hl : raw7201step0Labels = raw7201Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7201 raw7201Labels permutation160 permutation2
    _ = mixedMoment B node1213 node1213Labels := by rfl

theorem canonical7203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7203 raw7203Labels = mixedMoment B node1208 node1208Labels := by
  calc
    _ = mixedMoment B node1208 node1208Labels := by rfl

theorem canonical7205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7205 raw7205Labels = mixedMoment B node2622 node2622Labels := by
  calc
    mixedMoment B raw7205 raw7205Labels = mixedMoment B raw7205step0 raw7205step0Labels := by
      have ha : raw7205step0 = (fun i j => raw7205 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7205step0 raw7205; decide +kernel
      have hl : raw7205step0Labels = raw7205Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7205 raw7205Labels permutation182 permutation2
    _ = mixedMoment B node2622 node2622Labels := by rfl

theorem canonical7206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7206 raw7206Labels = mixedMoment B node2622 node2622Labels := by
  calc
    mixedMoment B raw7206 raw7206Labels = mixedMoment B raw7206step0 raw7206step0Labels := by
      have ha : raw7206step0 = (fun i j => raw7206 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7206step0 raw7206; decide +kernel
      have hl : raw7206step0Labels = raw7206Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7206 raw7206Labels permutation206 permutation2
    _ = mixedMoment B node2622 node2622Labels := by rfl

theorem canonical7207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7207 raw7207Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw7207 raw7207Labels = mixedMoment B raw7207step0 raw7207step0Labels := by
      have hz : ∀ j, raw7207 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7207step0 = (fun i j => raw7207 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7207step0 raw7207; decide +kernel
      have hl : raw7207step0Labels = raw7207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7207 raw7207Labels permutation520 hz
    mixedMoment B raw7207step0 raw7207step0Labels = mixedMoment B raw7207step1 raw7207step1Labels := by
      have ha : raw7207step1 = (fun i j => raw7207step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7207step1 raw7207step0; decide +kernel
      have hl : raw7207step1Labels = raw7207step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7207step0 raw7207step0Labels permutation40 permutation2
    _ = mixedMoment B node2751 node2751Labels := by rfl

theorem canonical7208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7208 raw7208Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw7208 raw7208Labels = mixedMoment B raw7208step0 raw7208step0Labels := by
      have ha : raw7208step0 = (fun i j => raw7208 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7208step0 raw7208; decide +kernel
      have hl : raw7208step0Labels = raw7208Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7208 raw7208Labels permutation182 permutation2
    _ = mixedMoment B node2750 node2750Labels := by rfl

theorem canonical7209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7209 raw7209Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw7209 raw7209Labels = mixedMoment B raw7209step0 raw7209step0Labels := by
      have ha : raw7209step0 = (fun i j => raw7209 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7209step0 raw7209; decide +kernel
      have hl : raw7209step0Labels = raw7209Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7209 raw7209Labels permutation160 permutation2
    _ = mixedMoment B node2480 node2480Labels := by rfl

theorem canonical7210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7210 raw7210Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw7210 raw7210Labels = mixedMoment B raw7210step0 raw7210step0Labels := by
      have ha : raw7210step0 = (fun i j => raw7210 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7210step0 raw7210; decide +kernel
      have hl : raw7210step0Labels = raw7210Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7210 raw7210Labels permutation154 permutation2
    _ = mixedMoment B node2480 node2480Labels := by rfl

theorem canonical7211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7211 raw7211Labels = mixedMoment B node2473 node2473Labels := by
  calc
    _ = mixedMoment B node2473 node2473Labels := by rfl

theorem canonical7212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7212 raw7212Labels = mixedMoment B node2470 node2470Labels := by
  calc
    _ = mixedMoment B node2470 node2470Labels := by rfl

theorem canonical7213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7213 raw7213Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw7213 raw7213Labels = mixedMoment B raw7213step0 raw7213step0Labels := by
      have ha : raw7213step0 = (fun i j => raw7213 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7213step0 raw7213; decide +kernel
      have hl : raw7213step0Labels = raw7213Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7213 raw7213Labels permutation202 permutation2
    _ = mixedMoment B node2615 node2615Labels := by rfl

theorem canonical7214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7214 raw7214Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw7214 raw7214Labels = mixedMoment B raw7214step0 raw7214step0Labels := by
      have hz : ∀ j, raw7214 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7214step0 = (fun i j => raw7214 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7214step0 raw7214; decide +kernel
      have hl : raw7214step0Labels = raw7214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7214 raw7214Labels permutation520 hz
    mixedMoment B raw7214step0 raw7214step0Labels = mixedMoment B raw7214step1 raw7214step1Labels := by
      have ha : raw7214step1 = (fun i j => raw7214step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7214step1 raw7214step0; decide +kernel
      have hl : raw7214step1Labels = raw7214step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7214step0 raw7214step0Labels permutation34 permutation2
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical7215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7215 raw7215Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw7215 raw7215Labels = mixedMoment B raw7215step0 raw7215step0Labels := by
      have ha : raw7215step0 = (fun i j => raw7215 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7215step0 raw7215; decide +kernel
      have hl : raw7215step0Labels = raw7215Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7215 raw7215Labels permutation160 permutation2
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical7216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7216 raw7216Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw7216 raw7216Labels = mixedMoment B raw7216step0 raw7216step0Labels := by
      have ha : raw7216step0 = (fun i j => raw7216 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7216step0 raw7216; decide +kernel
      have hl : raw7216step0Labels = raw7216Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7216 raw7216Labels permutation178 permutation2
    _ = mixedMoment B node2615 node2615Labels := by rfl

theorem canonical7217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7217 raw7217Labels = mixedMoment B node2612 node2612Labels := by
  calc
    mixedMoment B raw7217 raw7217Labels = mixedMoment B raw7217step0 raw7217step0Labels := by
      have ha : raw7217step0 = (fun i j => raw7217 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7217step0 raw7217; decide +kernel
      have hl : raw7217step0Labels = raw7217Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7217 raw7217Labels permutation176 permutation2
    _ = mixedMoment B node2612 node2612Labels := by rfl

theorem canonical7218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7218 raw7218Labels = mixedMoment B node2610 node2610Labels := by
  calc
    mixedMoment B raw7218 raw7218Labels = mixedMoment B raw7218step0 raw7218step0Labels := by
      have ha : raw7218step0 = (fun i j => raw7218 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7218step0 raw7218; decide +kernel
      have hl : raw7218step0Labels = raw7218Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7218 raw7218Labels permutation176 permutation2
    _ = mixedMoment B node2610 node2610Labels := by rfl

theorem canonical7219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7219 raw7219Labels = mixedMoment B node2612 node2612Labels := by
  calc
    mixedMoment B raw7219 raw7219Labels = mixedMoment B raw7219step0 raw7219step0Labels := by
      have ha : raw7219step0 = (fun i j => raw7219 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7219step0 raw7219; decide +kernel
      have hl : raw7219step0Labels = raw7219Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7219 raw7219Labels permutation200 permutation2
    _ = mixedMoment B node2612 node2612Labels := by rfl

theorem canonical7220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7220 raw7220Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw7220 raw7220Labels = mixedMoment B raw7220step0 raw7220step0Labels := by
      have ha : raw7220step0 = (fun i j => raw7220 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7220step0 raw7220; decide +kernel
      have hl : raw7220step0Labels = raw7220Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7220 raw7220Labels permutation153 permutation2
    _ = mixedMoment B node2710 node2710Labels := by rfl

theorem canonical7221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7221 raw7221Labels = mixedMoment B node5244 node5244Labels := by
  calc
    mixedMoment B raw7221 raw7221Labels = mixedMoment B raw7221step0 raw7221step0Labels := by
      have ha : raw7221step0 = (fun i j => raw7221 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7221step0 raw7221; decide +kernel
      have hl : raw7221step0Labels = raw7221Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7221 raw7221Labels permutation182 permutation7
    mixedMoment B raw7221step0 raw7221step0Labels = mixedMoment B raw7221step1 raw7221step1Labels := by
      have ha : raw7221step1 = raw7221step0 := by apply Matrix.ext; unfold raw7221step1 raw7221step0; decide +kernel
      have hl : raw7221step0Labels = labelEmbedding10 ∘ raw7221step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7221step0 raw7221step0Labels raw7221step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5244 node5244Labels := by rfl

theorem canonical7222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7222 raw7222Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw7222 raw7222Labels = mixedMoment B raw7222step0 raw7222step0Labels := by
      have hz : ∀ j, raw7222 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7222step0 = (fun i j => raw7222 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7222step0 raw7222; decide +kernel
      have hl : raw7222step0Labels = raw7222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7222 raw7222Labels permutation434 hz
    mixedMoment B raw7222step0 raw7222step0Labels = mixedMoment B raw7222step1 raw7222step1Labels := by
      have ha : raw7222step1 = (fun i j => raw7222step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7222step1 raw7222step0; decide +kernel
      have hl : raw7222step1Labels = raw7222step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7222step0 raw7222step0Labels permutation38 permutation7
    mixedMoment B raw7222step1 raw7222step1Labels = mixedMoment B raw7222step2 raw7222step2Labels := by
      have ha : raw7222step2 = raw7222step1 := by apply Matrix.ext; unfold raw7222step2 raw7222step1; decide +kernel
      have hl : raw7222step1Labels = labelEmbedding10 ∘ raw7222step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7222step1 raw7222step1Labels raw7222step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical7223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7223 raw7223Labels = mixedMoment B node5242 node5242Labels := by
  calc
    mixedMoment B raw7223 raw7223Labels = mixedMoment B raw7223step0 raw7223step0Labels := by
      have ha : raw7223step0 = (fun i j => raw7223 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7223step0 raw7223; decide +kernel
      have hl : raw7223step0Labels = raw7223Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7223 raw7223Labels permutation182 permutation7
    mixedMoment B raw7223step0 raw7223step0Labels = mixedMoment B raw7223step1 raw7223step1Labels := by
      have ha : raw7223step1 = raw7223step0 := by apply Matrix.ext; unfold raw7223step1 raw7223step0; decide +kernel
      have hl : raw7223step0Labels = labelEmbedding10 ∘ raw7223step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7223step0 raw7223step0Labels raw7223step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5242 node5242Labels := by rfl

theorem canonical7224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7224 raw7224Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw7224 raw7224Labels = mixedMoment B raw7224step0 raw7224step0Labels := by
      have ha : raw7224step0 = (fun i j => raw7224 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7224step0 raw7224; decide +kernel
      have hl : raw7224step0Labels = raw7224Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7224 raw7224Labels permutation182 permutation7
    mixedMoment B raw7224step0 raw7224step0Labels = mixedMoment B raw7224step1 raw7224step1Labels := by
      have ha : raw7224step1 = raw7224step0 := by apply Matrix.ext; unfold raw7224step1 raw7224step0; decide +kernel
      have hl : raw7224step0Labels = labelEmbedding10 ∘ raw7224step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7224step0 raw7224step0Labels raw7224step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

theorem canonical7225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7225 raw7225Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw7225 raw7225Labels = mixedMoment B raw7225step0 raw7225step0Labels := by
      have hz : ∀ j, raw7225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7225step0 = (fun i j => raw7225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7225step0 raw7225; decide +kernel
      have hl : raw7225step0Labels = raw7225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7225 raw7225Labels permutation434 hz
    mixedMoment B raw7225step0 raw7225step0Labels = mixedMoment B raw7225step1 raw7225step1Labels := by
      have hz : ∀ j, raw7225step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7225step1 = (fun i j => raw7225step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7225step1 raw7225step0; decide +kernel
      have hl : raw7225step1Labels = raw7225step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7225step0 raw7225step0Labels permutation56 hz
    mixedMoment B raw7225step1 raw7225step1Labels = mixedMoment B raw7225step2 raw7225step2Labels := by
      have ha : raw7225step2 = (fun i j => raw7225step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7225step2 raw7225step1; decide +kernel
      have hl : raw7225step2Labels = raw7225step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7225step1 raw7225step1Labels permutation8 permutation6
    mixedMoment B raw7225step2 raw7225step2Labels = mixedMoment B raw7225step3 raw7225step3Labels := by
      have ha : raw7225step3 = raw7225step2 := by apply Matrix.ext; unfold raw7225step3 raw7225step2; decide +kernel
      have hl : raw7225step2Labels = labelEmbedding9 ∘ raw7225step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7225step2 raw7225step2Labels raw7225step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

theorem canonical7226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7226 raw7226Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw7226 raw7226Labels = mixedMoment B raw7226step0 raw7226step0Labels := by
      have hz : ∀ j, raw7226 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7226step0 = (fun i j => raw7226 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7226step0 raw7226; decide +kernel
      have hl : raw7226step0Labels = raw7226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7226 raw7226Labels permutation265 hz
    mixedMoment B raw7226step0 raw7226step0Labels = mixedMoment B raw7226step1 raw7226step1Labels := by
      have ha : raw7226step1 = (fun i j => raw7226step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7226step1 raw7226step0; decide +kernel
      have hl : raw7226step1Labels = raw7226step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7226step0 raw7226step0Labels permutation32 permutation6
    mixedMoment B raw7226step1 raw7226step1Labels = mixedMoment B raw7226step2 raw7226step2Labels := by
      have ha : raw7226step2 = raw7226step1 := by apply Matrix.ext; unfold raw7226step2 raw7226step1; decide +kernel
      have hl : raw7226step1Labels = labelEmbedding9 ∘ raw7226step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7226step1 raw7226step1Labels raw7226step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

theorem canonical7227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7227 raw7227Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw7227 raw7227Labels = mixedMoment B raw7227step0 raw7227step0Labels := by
      have ha : raw7227step0 = (fun i j => raw7227 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7227step0 raw7227; decide +kernel
      have hl : raw7227step0Labels = raw7227Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7227 raw7227Labels permutation167 permutation4
    mixedMoment B raw7227step0 raw7227step0Labels = mixedMoment B raw7227step1 raw7227step1Labels := by
      have ha : raw7227step1 = -raw7227step0 := by apply Matrix.ext; change ∀ i j, raw7227step1 i j = -(raw7227step0 i j); unfold raw7227step1 raw7227step0; decide +kernel
      have hl : raw7227step1Labels = raw7227step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7227step1 raw7227step1Labels = mixedMoment B raw7227step2 raw7227step2Labels := by
      have ha : raw7227step2 = raw7227step1 := by apply Matrix.ext; unfold raw7227step2 raw7227step1; decide +kernel
      have hl : raw7227step1Labels = labelEmbedding7 ∘ raw7227step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7227step1 raw7227step1Labels raw7227step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

theorem canonical7228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7228 raw7228Labels = mixedMoment B node5223 node5223Labels := by
  calc
    mixedMoment B raw7228 raw7228Labels = mixedMoment B raw7228step0 raw7228step0Labels := by
      have ha : raw7228step0 = (fun i j => raw7228 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7228step0 raw7228; decide +kernel
      have hl : raw7228step0Labels = raw7228Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7228 raw7228Labels permutation158 permutation6
    mixedMoment B raw7228step0 raw7228step0Labels = mixedMoment B raw7228step1 raw7228step1Labels := by
      have ha : raw7228step1 = raw7228step0 := by apply Matrix.ext; unfold raw7228step1 raw7228step0; decide +kernel
      have hl : raw7228step0Labels = labelEmbedding9 ∘ raw7228step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7228step0 raw7228step0Labels raw7228step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5223 node5223Labels := by rfl

theorem canonical7229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7229 raw7229Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw7229 raw7229Labels = mixedMoment B raw7229step0 raw7229step0Labels := by
      have hz : ∀ j, raw7229 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7229step0 = (fun i j => raw7229 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7229step0 raw7229; decide +kernel
      have hl : raw7229step0Labels = raw7229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7229 raw7229Labels permutation434 hz
    mixedMoment B raw7229step0 raw7229step0Labels = mixedMoment B raw7229step1 raw7229step1Labels := by
      have ha : raw7229step1 = (fun i j => raw7229step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7229step1 raw7229step0; decide +kernel
      have hl : raw7229step1Labels = raw7229step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7229step0 raw7229step0Labels permutation32 permutation6
    mixedMoment B raw7229step1 raw7229step1Labels = mixedMoment B raw7229step2 raw7229step2Labels := by
      have ha : raw7229step2 = raw7229step1 := by apply Matrix.ext; unfold raw7229step2 raw7229step1; decide +kernel
      have hl : raw7229step1Labels = labelEmbedding9 ∘ raw7229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7229step1 raw7229step1Labels raw7229step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical7230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7230 raw7230Labels = mixedMoment B node5253 node5253Labels := by
  calc
    mixedMoment B raw7230 raw7230Labels = mixedMoment B raw7230step0 raw7230step0Labels := by
      have ha : raw7230step0 = (fun i j => raw7230 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7230step0 raw7230; decide +kernel
      have hl : raw7230step0Labels = raw7230Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7230 raw7230Labels permutation158 permutation6
    mixedMoment B raw7230step0 raw7230step0Labels = mixedMoment B raw7230step1 raw7230step1Labels := by
      have ha : raw7230step1 = raw7230step0 := by apply Matrix.ext; unfold raw7230step1 raw7230step0; decide +kernel
      have hl : raw7230step0Labels = labelEmbedding9 ∘ raw7230step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7230step0 raw7230step0Labels raw7230step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5253 node5253Labels := by rfl

theorem canonical7231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7231 raw7231Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw7231 raw7231Labels = mixedMoment B raw7231step0 raw7231step0Labels := by
      have ha : raw7231step0 = (fun i j => raw7231 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7231step0 raw7231; decide +kernel
      have hl : raw7231step0Labels = raw7231Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7231 raw7231Labels permutation158 permutation6
    mixedMoment B raw7231step0 raw7231step0Labels = mixedMoment B raw7231step1 raw7231step1Labels := by
      have ha : raw7231step1 = raw7231step0 := by apply Matrix.ext; unfold raw7231step1 raw7231step0; decide +kernel
      have hl : raw7231step0Labels = labelEmbedding9 ∘ raw7231step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7231step0 raw7231step0Labels raw7231step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5254 node5254Labels := by rfl

theorem canonical7232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7232 raw7232Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw7232 raw7232Labels = mixedMoment B raw7232step0 raw7232step0Labels := by
      have ha : raw7232step0 = (fun i j => raw7232 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7232step0 raw7232; decide +kernel
      have hl : raw7232step0Labels = raw7232Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7232 raw7232Labels permutation152 permutation4
    mixedMoment B raw7232step0 raw7232step0Labels = mixedMoment B raw7232step1 raw7232step1Labels := by
      have ha : raw7232step1 = -raw7232step0 := by apply Matrix.ext; change ∀ i j, raw7232step1 i j = -(raw7232step0 i j); unfold raw7232step1 raw7232step0; decide +kernel
      have hl : raw7232step1Labels = raw7232step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7232step1 raw7232step1Labels = mixedMoment B raw7232step2 raw7232step2Labels := by
      have ha : raw7232step2 = raw7232step1 := by apply Matrix.ext; unfold raw7232step2 raw7232step1; decide +kernel
      have hl : raw7232step1Labels = labelEmbedding7 ∘ raw7232step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7232step1 raw7232step1Labels raw7232step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

theorem canonical7233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7233 raw7233Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw7233 raw7233Labels = mixedMoment B raw7233step0 raw7233step0Labels := by
      have ha : raw7233step0 = (fun i j => raw7233 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7233step0 raw7233; decide +kernel
      have hl : raw7233step0Labels = raw7233Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7233 raw7233Labels permutation152 permutation6
    mixedMoment B raw7233step0 raw7233step0Labels = mixedMoment B raw7233step1 raw7233step1Labels := by
      have ha : raw7233step1 = raw7233step0 := by apply Matrix.ext; unfold raw7233step1 raw7233step0; decide +kernel
      have hl : raw7233step0Labels = labelEmbedding9 ∘ raw7233step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7233step0 raw7233step0Labels raw7233step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

theorem canonical7234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7234 raw7234Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw7234 raw7234Labels = mixedMoment B raw7234step0 raw7234step0Labels := by
      have hz : ∀ j, raw7234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7234step0 = (fun i j => raw7234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7234step0 raw7234; decide +kernel
      have hl : raw7234step0Labels = raw7234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7234 raw7234Labels permutation434 hz
    mixedMoment B raw7234step0 raw7234step0Labels = mixedMoment B raw7234step1 raw7234step1Labels := by
      have ha : raw7234step1 = (fun i j => raw7234step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7234step1 raw7234step0; decide +kernel
      have hl : raw7234step1Labels = raw7234step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7234step0 raw7234step0Labels permutation32 permutation6
    mixedMoment B raw7234step1 raw7234step1Labels = mixedMoment B raw7234step2 raw7234step2Labels := by
      have ha : raw7234step2 = raw7234step1 := by apply Matrix.ext; unfold raw7234step2 raw7234step1; decide +kernel
      have hl : raw7234step1Labels = labelEmbedding9 ∘ raw7234step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7234step1 raw7234step1Labels raw7234step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical7235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7235 raw7235Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw7235 raw7235Labels = mixedMoment B raw7235step0 raw7235step0Labels := by
      have ha : raw7235step0 = (fun i j => raw7235 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7235step0 raw7235; decide +kernel
      have hl : raw7235step0Labels = raw7235Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7235 raw7235Labels permutation164 permutation4
    mixedMoment B raw7235step0 raw7235step0Labels = mixedMoment B raw7235step1 raw7235step1Labels := by
      have ha : raw7235step1 = -raw7235step0 := by apply Matrix.ext; change ∀ i j, raw7235step1 i j = -(raw7235step0 i j); unfold raw7235step1 raw7235step0; decide +kernel
      have hl : raw7235step1Labels = raw7235step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7235step1 raw7235step1Labels = mixedMoment B raw7235step2 raw7235step2Labels := by
      have ha : raw7235step2 = raw7235step1 := by apply Matrix.ext; unfold raw7235step2 raw7235step1; decide +kernel
      have hl : raw7235step1Labels = labelEmbedding7 ∘ raw7235step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7235step1 raw7235step1Labels raw7235step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

theorem canonical7236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7236 raw7236Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw7236 raw7236Labels = mixedMoment B raw7236step0 raw7236step0Labels := by
      have ha : raw7236step0 = (fun i j => raw7236 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7236step0 raw7236; decide +kernel
      have hl : raw7236step0Labels = raw7236Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7236 raw7236Labels permutation152 permutation6
    mixedMoment B raw7236step0 raw7236step0Labels = mixedMoment B raw7236step1 raw7236step1Labels := by
      have ha : raw7236step1 = raw7236step0 := by apply Matrix.ext; unfold raw7236step1 raw7236step0; decide +kernel
      have hl : raw7236step0Labels = labelEmbedding9 ∘ raw7236step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7236step0 raw7236step0Labels raw7236step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

theorem canonical7237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7237 raw7237Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw7237 raw7237Labels = mixedMoment B raw7237step0 raw7237step0Labels := by
      have hz : ∀ j, raw7237 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7237step0 = (fun i j => raw7237 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7237step0 raw7237; decide +kernel
      have hl : raw7237step0Labels = raw7237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7237 raw7237Labels permutation434 hz
    mixedMoment B raw7237step0 raw7237step0Labels = mixedMoment B raw7237step1 raw7237step1Labels := by
      have ha : raw7237step1 = (fun i j => raw7237step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7237step1 raw7237step0; decide +kernel
      have hl : raw7237step1Labels = raw7237step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7237step0 raw7237step0Labels permutation32 permutation6
    mixedMoment B raw7237step1 raw7237step1Labels = mixedMoment B raw7237step2 raw7237step2Labels := by
      have ha : raw7237step2 = raw7237step1 := by apply Matrix.ext; unfold raw7237step2 raw7237step1; decide +kernel
      have hl : raw7237step1Labels = labelEmbedding9 ∘ raw7237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7237step1 raw7237step1Labels raw7237step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical7238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7238 raw7238Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw7238 raw7238Labels = mixedMoment B raw7238step0 raw7238step0Labels := by
      have ha : raw7238step0 = (fun i j => raw7238 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7238step0 raw7238; decide +kernel
      have hl : raw7238step0Labels = raw7238Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7238 raw7238Labels permutation152 permutation6
    mixedMoment B raw7238step0 raw7238step0Labels = mixedMoment B raw7238step1 raw7238step1Labels := by
      have ha : raw7238step1 = raw7238step0 := by apply Matrix.ext; unfold raw7238step1 raw7238step0; decide +kernel
      have hl : raw7238step0Labels = labelEmbedding9 ∘ raw7238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7238step0 raw7238step0Labels raw7238step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

theorem canonical7275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7275 raw7275Labels = mixedMoment B node3497 node3497Labels := by
  calc
    mixedMoment B raw7275 raw7275Labels = mixedMoment B raw7275step0 raw7275step0Labels := by
      have ha : raw7275step0 = (fun i j => raw7275 (permutation185 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7275step0 raw7275; decide +kernel
      have hl : raw7275step0Labels = raw7275Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7275 raw7275Labels permutation185 permutation2
    mixedMoment B raw7275step0 raw7275step0Labels = mixedMoment B raw7275step1 raw7275step1Labels := by
      have ha : raw7275step1 = -raw7275step0 := by apply Matrix.ext; change ∀ i j, raw7275step1 i j = -(raw7275step0 i j); unfold raw7275step1 raw7275step0; decide +kernel
      have hl : raw7275step1Labels = raw7275step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3497 node3497Labels := by rfl

theorem canonical7276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7276 raw7276Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw7276 raw7276Labels = mixedMoment B raw7276step0 raw7276step0Labels := by
      have hz : ∀ j, raw7276 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7276step0 = (fun i j => raw7276 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7276step0 raw7276; decide +kernel
      have hl : raw7276step0Labels = raw7276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7276 raw7276Labels permutation434 hz
    mixedMoment B raw7276step0 raw7276step0Labels = mixedMoment B raw7276step1 raw7276step1Labels := by
      have ha : raw7276step1 = (fun i j => raw7276step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7276step1 raw7276step0; decide +kernel
      have hl : raw7276step1Labels = raw7276step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7276step0 raw7276step0Labels permutation38 permutation2
    mixedMoment B raw7276step1 raw7276step1Labels = mixedMoment B raw7276step2 raw7276step2Labels := by
      have ha : raw7276step2 = -raw7276step1 := by apply Matrix.ext; change ∀ i j, raw7276step2 i j = -(raw7276step1 i j); unfold raw7276step2 raw7276step1; decide +kernel
      have hl : raw7276step2Labels = raw7276step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical7277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7277 raw7277Labels = mixedMoment B node3494 node3494Labels := by
  calc
    mixedMoment B raw7277 raw7277Labels = mixedMoment B raw7277step0 raw7277step0Labels := by
      have ha : raw7277step0 = (fun i j => raw7277 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7277step0 raw7277; decide +kernel
      have hl : raw7277step0Labels = raw7277Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7277 raw7277Labels permutation183 permutation2
    mixedMoment B raw7277step0 raw7277step0Labels = mixedMoment B raw7277step1 raw7277step1Labels := by
      have ha : raw7277step1 = -raw7277step0 := by apply Matrix.ext; change ∀ i j, raw7277step1 i j = -(raw7277step0 i j); unfold raw7277step1 raw7277step0; decide +kernel
      have hl : raw7277step1Labels = raw7277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3494 node3494Labels := by rfl

theorem canonical7278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7278 raw7278Labels = mixedMoment B node3493 node3493Labels := by
  calc
    mixedMoment B raw7278 raw7278Labels = mixedMoment B raw7278step0 raw7278step0Labels := by
      have ha : raw7278step0 = (fun i j => raw7278 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7278step0 raw7278; decide +kernel
      have hl : raw7278step0Labels = raw7278Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7278 raw7278Labels permutation182 permutation2
    mixedMoment B raw7278step0 raw7278step0Labels = mixedMoment B raw7278step1 raw7278step1Labels := by
      have ha : raw7278step1 = -raw7278step0 := by apply Matrix.ext; change ∀ i j, raw7278step1 i j = -(raw7278step0 i j); unfold raw7278step1 raw7278step0; decide +kernel
      have hl : raw7278step1Labels = raw7278step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3493 node3493Labels := by rfl

theorem canonical7279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7279 raw7279Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw7279 raw7279Labels = mixedMoment B raw7279step0 raw7279step0Labels := by
      have ha : raw7279step0 = (fun i j => raw7279 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7279step0 raw7279; decide +kernel
      have hl : raw7279step0Labels = raw7279Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7279 raw7279Labels permutation167 permutation4
    mixedMoment B raw7279step0 raw7279step0Labels = mixedMoment B raw7279step1 raw7279step1Labels := by
      have ha : raw7279step1 = -raw7279step0 := by apply Matrix.ext; change ∀ i j, raw7279step1 i j = -(raw7279step0 i j); unfold raw7279step1 raw7279step0; decide +kernel
      have hl : raw7279step1Labels = raw7279step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2021 node2021Labels := by rfl

theorem canonical7280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7280 raw7280Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw7280 raw7280Labels = mixedMoment B raw7280step0 raw7280step0Labels := by
      have ha : raw7280step0 = (fun i j => raw7280 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7280step0 raw7280; decide +kernel
      have hl : raw7280step0Labels = raw7280Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7280 raw7280Labels permutation152 permutation4
    mixedMoment B raw7280step0 raw7280step0Labels = mixedMoment B raw7280step1 raw7280step1Labels := by
      have ha : raw7280step1 = -raw7280step0 := by apply Matrix.ext; change ∀ i j, raw7280step1 i j = -(raw7280step0 i j); unfold raw7280step1 raw7280step0; decide +kernel
      have hl : raw7280step1Labels = raw7280step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2051 node2051Labels := by rfl

theorem canonical7281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7281 raw7281Labels = mixedMoment B node2019 node2019Labels := by
  calc
    mixedMoment B raw7281 raw7281Labels = mixedMoment B raw7281step0 raw7281step0Labels := by
      have ha : raw7281step0 = (fun i j => raw7281 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7281step0 raw7281; decide +kernel
      have hl : raw7281step0Labels = raw7281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7281 raw7281Labels permutation164 permutation4
    mixedMoment B raw7281step0 raw7281step0Labels = mixedMoment B raw7281step1 raw7281step1Labels := by
      have ha : raw7281step1 = -raw7281step0 := by apply Matrix.ext; change ∀ i j, raw7281step1 i j = -(raw7281step0 i j); unfold raw7281step1 raw7281step0; decide +kernel
      have hl : raw7281step1Labels = raw7281step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2019 node2019Labels := by rfl

theorem canonical7282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7282 raw7282Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw7282 raw7282Labels = mixedMoment B raw7282step0 raw7282step0Labels := by
      have hz : ∀ j, raw7282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7282step0 = (fun i j => raw7282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7282step0 raw7282; decide +kernel
      have hl : raw7282step0Labels = raw7282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7282 raw7282Labels permutation434 hz
    mixedMoment B raw7282step0 raw7282step0Labels = mixedMoment B raw7282step1 raw7282step1Labels := by
      have hz : ∀ j, raw7282step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7282step1 = (fun i j => raw7282step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7282step1 raw7282step0; decide +kernel
      have hl : raw7282step1Labels = raw7282step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7282step0 raw7282step0Labels permutation56 hz
    mixedMoment B raw7282step1 raw7282step1Labels = mixedMoment B raw7282step2 raw7282step2Labels := by
      have ha : raw7282step2 = (fun i j => raw7282step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7282step2 raw7282step1; decide +kernel
      have hl : raw7282step2Labels = raw7282step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7282step1 raw7282step1Labels permutation10 permutation4
    mixedMoment B raw7282step2 raw7282step2Labels = mixedMoment B raw7282step3 raw7282step3Labels := by
      have ha : raw7282step3 = -raw7282step2 := by apply Matrix.ext; change ∀ i j, raw7282step3 i j = -(raw7282step2 i j); unfold raw7282step3 raw7282step2; decide +kernel
      have hl : raw7282step3Labels = raw7282step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3627 node3627Labels := by rfl

theorem canonical7283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7283 raw7283Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw7283 raw7283Labels = mixedMoment B raw7283step0 raw7283step0Labels := by
      have hz : ∀ j, raw7283 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7283step0 = (fun i j => raw7283 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7283step0 raw7283; decide +kernel
      have hl : raw7283step0Labels = raw7283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7283 raw7283Labels permutation265 hz
    mixedMoment B raw7283step0 raw7283step0Labels = mixedMoment B raw7283step1 raw7283step1Labels := by
      have ha : raw7283step1 = (fun i j => raw7283step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7283step1 raw7283step0; decide +kernel
      have hl : raw7283step1Labels = raw7283step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7283step0 raw7283step0Labels permutation44 permutation4
    mixedMoment B raw7283step1 raw7283step1Labels = mixedMoment B raw7283step2 raw7283step2Labels := by
      have ha : raw7283step2 = -raw7283step1 := by apply Matrix.ext; change ∀ i j, raw7283step2 i j = -(raw7283step1 i j); unfold raw7283step2 raw7283step1; decide +kernel
      have hl : raw7283step2Labels = raw7283step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3580 node3580Labels := by rfl

theorem canonical7284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7284 raw7284Labels = mixedMoment B node3377 node3377Labels := by
  calc
    mixedMoment B raw7284 raw7284Labels = mixedMoment B raw7284step0 raw7284step0Labels := by
      have ha : raw7284step0 = (fun i j => raw7284 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7284step0 raw7284; decide +kernel
      have hl : raw7284step0Labels = raw7284Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7284 raw7284Labels permutation167 permutation4
    mixedMoment B raw7284step0 raw7284step0Labels = mixedMoment B raw7284step1 raw7284step1Labels := by
      have ha : raw7284step1 = -raw7284step0 := by apply Matrix.ext; change ∀ i j, raw7284step1 i j = -(raw7284step0 i j); unfold raw7284step1 raw7284step0; decide +kernel
      have hl : raw7284step1Labels = raw7284step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3377 node3377Labels := by rfl

theorem canonical7285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7285 raw7285Labels = mixedMoment B node3388 node3388Labels := by
  calc
    mixedMoment B raw7285 raw7285Labels = mixedMoment B raw7285step0 raw7285step0Labels := by
      have ha : raw7285step0 = (fun i j => raw7285 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7285step0 raw7285; decide +kernel
      have hl : raw7285step0Labels = raw7285Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7285 raw7285Labels permutation152 permutation4
    mixedMoment B raw7285step0 raw7285step0Labels = mixedMoment B raw7285step1 raw7285step1Labels := by
      have ha : raw7285step1 = -raw7285step0 := by apply Matrix.ext; change ∀ i j, raw7285step1 i j = -(raw7285step0 i j); unfold raw7285step1 raw7285step0; decide +kernel
      have hl : raw7285step1Labels = raw7285step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3388 node3388Labels := by rfl

theorem canonical7286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7286 raw7286Labels = mixedMoment B node3375 node3375Labels := by
  calc
    mixedMoment B raw7286 raw7286Labels = mixedMoment B raw7286step0 raw7286step0Labels := by
      have ha : raw7286step0 = (fun i j => raw7286 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7286step0 raw7286; decide +kernel
      have hl : raw7286step0Labels = raw7286Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7286 raw7286Labels permutation164 permutation4
    mixedMoment B raw7286step0 raw7286step0Labels = mixedMoment B raw7286step1 raw7286step1Labels := by
      have ha : raw7286step1 = -raw7286step0 := by apply Matrix.ext; change ∀ i j, raw7286step1 i j = -(raw7286step0 i j); unfold raw7286step1 raw7286step0; decide +kernel
      have hl : raw7286step1Labels = raw7286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3375 node3375Labels := by rfl

theorem canonical7287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7287 raw7287Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw7287 raw7287Labels = mixedMoment B raw7287step0 raw7287step0Labels := by
      have hz : ∀ j, raw7287 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7287step0 = (fun i j => raw7287 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7287step0 raw7287; decide +kernel
      have hl : raw7287step0Labels = raw7287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7287 raw7287Labels permutation434 hz
    mixedMoment B raw7287step0 raw7287step0Labels = mixedMoment B raw7287step1 raw7287step1Labels := by
      have ha : raw7287step1 = (fun i j => raw7287step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7287step1 raw7287step0; decide +kernel
      have hl : raw7287step1Labels = raw7287step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7287step0 raw7287step0Labels permutation32 permutation4
    mixedMoment B raw7287step1 raw7287step1Labels = mixedMoment B raw7287step2 raw7287step2Labels := by
      have ha : raw7287step2 = -raw7287step1 := by apply Matrix.ext; change ∀ i j, raw7287step2 i j = -(raw7287step1 i j); unfold raw7287step2 raw7287step1; decide +kernel
      have hl : raw7287step2Labels = raw7287step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical7288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7288 raw7288Labels = mixedMoment B node3504 node3504Labels := by
  calc
    mixedMoment B raw7288 raw7288Labels = mixedMoment B raw7288step0 raw7288step0Labels := by
      have ha : raw7288step0 = (fun i j => raw7288 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7288step0 raw7288; decide +kernel
      have hl : raw7288step0Labels = raw7288Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7288 raw7288Labels permutation167 permutation4
    mixedMoment B raw7288step0 raw7288step0Labels = mixedMoment B raw7288step1 raw7288step1Labels := by
      have ha : raw7288step1 = -raw7288step0 := by apply Matrix.ext; change ∀ i j, raw7288step1 i j = -(raw7288step0 i j); unfold raw7288step1 raw7288step0; decide +kernel
      have hl : raw7288step1Labels = raw7288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3504 node3504Labels := by rfl

theorem canonical7289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7289 raw7289Labels = mixedMoment B node3502 node3502Labels := by
  calc
    mixedMoment B raw7289 raw7289Labels = mixedMoment B raw7289step0 raw7289step0Labels := by
      have ha : raw7289step0 = (fun i j => raw7289 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7289step0 raw7289; decide +kernel
      have hl : raw7289step0Labels = raw7289Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7289 raw7289Labels permutation164 permutation4
    mixedMoment B raw7289step0 raw7289step0Labels = mixedMoment B raw7289step1 raw7289step1Labels := by
      have ha : raw7289step1 = -raw7289step0 := by apply Matrix.ext; change ∀ i j, raw7289step1 i j = -(raw7289step0 i j); unfold raw7289step1 raw7289step0; decide +kernel
      have hl : raw7289step1Labels = raw7289step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3502 node3502Labels := by rfl

theorem canonical7290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7290 raw7290Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw7290 raw7290Labels = mixedMoment B raw7290step0 raw7290step0Labels := by
      have hz : ∀ j, raw7290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7290step0 = (fun i j => raw7290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7290step0 raw7290; decide +kernel
      have hl : raw7290step0Labels = raw7290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7290 raw7290Labels permutation434 hz
    mixedMoment B raw7290step0 raw7290step0Labels = mixedMoment B raw7290step1 raw7290step1Labels := by
      have ha : raw7290step1 = (fun i j => raw7290step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7290step1 raw7290step0; decide +kernel
      have hl : raw7290step1Labels = raw7290step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7290step0 raw7290step0Labels permutation34 permutation4
    mixedMoment B raw7290step1 raw7290step1Labels = mixedMoment B raw7290step2 raw7290step2Labels := by
      have ha : raw7290step2 = -raw7290step1 := by apply Matrix.ext; change ∀ i j, raw7290step2 i j = -(raw7290step1 i j); unfold raw7290step2 raw7290step1; decide +kernel
      have hl : raw7290step2Labels = raw7290step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3533 node3533Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

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

theorem singleton4831 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4831 node4831Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2051 node2051Labels + mixedMoment B node2191 node2191Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1761 singletonSmall4831
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4831) = raw1761Labels := by decide +kernel
  rw [hl, canonical1761 B hB] at h
  have hc0 : mixedMoment B raw1761 (Fin.cases (0 : Fin 2) singletonSmall4831) =
      mixedMoment B node2051 node2051Labels := by
    have ha : raw1761 = raw1762 := by apply Matrix.ext; unfold raw1761 raw1762; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4831 = raw1762Labels := by decide +kernel
    rw [ha, hj, canonical1762 B hB]
  have hc1 : mixedMoment B raw1761 (Fin.cases (1 : Fin 2) singletonSmall4831) =
      mixedMoment B node2191 node2191Labels := by
    have ha : raw1761 = raw1763 := by apply Matrix.ext; unfold raw1761 raw1763; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4831 = raw1763Labels := by decide +kernel
    rw [ha, hj, canonical1763 B hB]
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

theorem singleton4888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4888 node4888Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2244 node2244Labels + mixedMoment B node2262 node2262Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1815 singletonSmall4888
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4888) = raw1815Labels := by decide +kernel
  rw [hl, canonical1815 B hB] at h
  have hc0 : mixedMoment B raw1815 (Fin.cases (0 : Fin 2) singletonSmall4888) =
      mixedMoment B node2244 node2244Labels := by
    have ha : raw1815 = raw1816 := by apply Matrix.ext; unfold raw1815 raw1816; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4888 = raw1816Labels := by decide +kernel
    rw [ha, hj, canonical1816 B hB]
  have hc1 : mixedMoment B raw1815 (Fin.cases (1 : Fin 2) singletonSmall4888) =
      mixedMoment B node2262 node2262Labels := by
    have ha : raw1815 = raw1817 := by apply Matrix.ext; unfold raw1815 raw1817; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4888 = raw1817Labels := by decide +kernel
    rw [ha, hj, canonical1817 B hB]
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

theorem singleton5241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5241 node5241Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2694 node2694Labels + mixedMoment B node3493 node3493Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2259 singletonSmall5241
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5241) = raw2259Labels := by decide +kernel
  rw [hl, canonical2259 B hB] at h
  have hc0 : mixedMoment B raw2259 (Fin.cases (0 : Fin 2) singletonSmall5241) =
      mixedMoment B node2694 node2694Labels := by
    have ha : raw2259 = raw2260 := by apply Matrix.ext; unfold raw2259 raw2260; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5241 = raw2260Labels := by decide +kernel
    rw [ha, hj, canonical2260 B hB]
  have hc1 : mixedMoment B raw2259 (Fin.cases (1 : Fin 2) singletonSmall5241) =
      mixedMoment B node3493 node3493Labels := by
    have ha : raw2259 = raw2261 := by apply Matrix.ext; unfold raw2259 raw2261; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5241 = raw2261Labels := by decide +kernel
    rw [ha, hj, canonical2261 B hB]
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

theorem singleton5258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5258 node5258Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2722 node2722Labels + mixedMoment B node3533 node3533Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2271 singletonSmall5258
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5258) = raw2271Labels := by decide +kernel
  rw [hl, canonical2271 B hB] at h
  have hc0 : mixedMoment B raw2271 (Fin.cases (0 : Fin 2) singletonSmall5258) =
      mixedMoment B node2722 node2722Labels := by
    have ha : raw2271 = raw2272 := by apply Matrix.ext; unfold raw2271 raw2272; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5258 = raw2272Labels := by decide +kernel
    rw [ha, hj, canonical2272 B hB]
  have hc1 : mixedMoment B raw2271 (Fin.cases (1 : Fin 2) singletonSmall5258) =
      mixedMoment B node3533 node3533Labels := by
    have ha : raw2271 = raw2273 := by apply Matrix.ext; unfold raw2271 raw2273; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5258 = raw2273Labels := by decide +kernel
    rw [ha, hj, canonical2273 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5259 node5259Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2723 node2723Labels + mixedMoment B node3544 node3544Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2274 singletonSmall5259
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5259) = raw2274Labels := by decide +kernel
  rw [hl, canonical2274 B hB] at h
  have hc0 : mixedMoment B raw2274 (Fin.cases (0 : Fin 2) singletonSmall5259) =
      mixedMoment B node2723 node2723Labels := by
    have ha : raw2274 = raw2275 := by apply Matrix.ext; unfold raw2274 raw2275; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5259 = raw2275Labels := by decide +kernel
    rw [ha, hj, canonical2275 B hB]
  have hc1 : mixedMoment B raw2274 (Fin.cases (1 : Fin 2) singletonSmall5259) =
      mixedMoment B node3544 node3544Labels := by
    have ha : raw2274 = raw2276 := by apply Matrix.ext; unfold raw2274 raw2276; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5259 = raw2276Labels := by decide +kernel
    rw [ha, hj, canonical2276 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5293 node5293Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2767 node2767Labels + mixedMoment B node3627 node3627Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2301 singletonSmall5293
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5293) = raw2301Labels := by decide +kernel
  rw [hl, canonical2301 B hB] at h
  have hc0 : mixedMoment B raw2301 (Fin.cases (0 : Fin 2) singletonSmall5293) =
      mixedMoment B node2767 node2767Labels := by
    have ha : raw2301 = raw2302 := by apply Matrix.ext; unfold raw2301 raw2302; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5293 = raw2302Labels := by decide +kernel
    rw [ha, hj, canonical2302 B hB]
  have hc1 : mixedMoment B raw2301 (Fin.cases (1 : Fin 2) singletonSmall5293) =
      mixedMoment B node3627 node3627Labels := by
    have ha : raw2301 = raw2303 := by apply Matrix.ext; unfold raw2301 raw2303; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5293 = raw2303Labels := by decide +kernel
    rw [ha, hj, canonical2303 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1208 node1208Labels = Sparse.eval nodeValue1208 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1208) = mixedMoment B node1208 node1208Labels := rfl
  simpa [nodeValue1208, Sparse.eval] using hc.symm

theorem sound1213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1213 node1213Labels = Sparse.eval nodeValue1213 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1213) = mixedMoment B node1213 node1213Labels := rfl
  simpa [nodeValue1213, Sparse.eval] using hc.symm

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

theorem sound1247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1247 node1247Labels = Sparse.eval nodeValue1247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1247) = mixedMoment B node1247 node1247Labels := rfl
  simpa [nodeValue1247, Sparse.eval] using hc.symm

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

theorem sound2021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2021 node2021Labels = Sparse.eval nodeValue2021 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2021) = mixedMoment B node2021 node2021Labels := rfl
  simpa [nodeValue2021, Sparse.eval] using hc.symm

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

theorem sound2051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2051 node2051Labels = Sparse.eval nodeValue2051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2051) = mixedMoment B node2051 node2051Labels := rfl
  simpa [nodeValue2051, Sparse.eval] using hc.symm

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

theorem sound2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2191 node2191Labels = Sparse.eval nodeValue2191 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2191) = mixedMoment B node2191 node2191Labels := rfl
  simpa [nodeValue2191, Sparse.eval] using hc.symm

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

theorem sound2244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2244 node2244Labels = Sparse.eval nodeValue2244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2244) = mixedMoment B node2244 node2244Labels := rfl
  simpa [nodeValue2244, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

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

theorem sound2470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2470 node2470Labels = Sparse.eval nodeValue2470 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2470) = mixedMoment B node2470 node2470Labels := rfl
  simpa [nodeValue2470, Sparse.eval] using hc.symm

theorem sound2473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2473 node2473Labels = Sparse.eval nodeValue2473 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2473) = mixedMoment B node2473 node2473Labels := rfl
  simpa [nodeValue2473, Sparse.eval] using hc.symm

theorem sound2480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2480 node2480Labels = Sparse.eval nodeValue2480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2480) = mixedMoment B node2480 node2480Labels := rfl
  simpa [nodeValue2480, Sparse.eval] using hc.symm

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

theorem sound2610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2610 node2610Labels = Sparse.eval nodeValue2610 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2610) = mixedMoment B node2610 node2610Labels := rfl
  simpa [nodeValue2610, Sparse.eval] using hc.symm

theorem sound2612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2612 node2612Labels = Sparse.eval nodeValue2612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2612) = mixedMoment B node2612 node2612Labels := rfl
  simpa [nodeValue2612, Sparse.eval] using hc.symm

theorem sound2615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2615 node2615Labels = Sparse.eval nodeValue2615 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2615) = mixedMoment B node2615 node2615Labels := rfl
  simpa [nodeValue2615, Sparse.eval] using hc.symm

theorem sound2622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2622 node2622Labels = Sparse.eval nodeValue2622 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2622) = mixedMoment B node2622 node2622Labels := rfl
  simpa [nodeValue2622, Sparse.eval] using hc.symm

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

theorem sound2694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2694 node2694Labels = Sparse.eval nodeValue2694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2694) = mixedMoment B node2694 node2694Labels := rfl
  simpa [nodeValue2694, Sparse.eval] using hc.symm

theorem sound2709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2709 node2709Labels = Sparse.eval nodeValue2709 (mixedVector B) := by
  simpa only [nodeValue2709, Sparse.eval_nil] using zero2709 B _hB _hF

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

theorem sound2750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2750 node2750Labels = Sparse.eval nodeValue2750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2750) = mixedMoment B node2750 node2750Labels := rfl
  simpa [nodeValue2750, Sparse.eval] using hc.symm

theorem sound2751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2751 node2751Labels = Sparse.eval nodeValue2751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2751) = mixedMoment B node2751 node2751Labels := rfl
  simpa [nodeValue2751, Sparse.eval] using hc.symm

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

theorem sound2767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2767 node2767Labels = Sparse.eval nodeValue2767 (mixedVector B) := by
  have h := singleton2767 B _hB
  rw [sound404 B _hB _hF] at h
  norm_num [nodeValue2767, nodeValue404, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3375 node3375Labels = Sparse.eval nodeValue3375 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3375) = mixedMoment B node3375 node3375Labels := rfl
  simpa [nodeValue3375, Sparse.eval] using hc.symm

theorem sound3377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3377 node3377Labels = Sparse.eval nodeValue3377 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3377) = mixedMoment B node3377 node3377Labels := rfl
  simpa [nodeValue3377, Sparse.eval] using hc.symm

theorem sound3388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3388 node3388Labels = Sparse.eval nodeValue3388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3388) = mixedMoment B node3388 node3388Labels := rfl
  simpa [nodeValue3388, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3494 node3494Labels = 0 := by
  exact mixedMoment_alpha B hF node3494 node3494Labels 1 permutation436
    (by decide +kernel)

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

theorem sound3493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3493 node3493Labels = Sparse.eval nodeValue3493 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3493) = mixedMoment B node3493 node3493Labels := rfl
  simpa [nodeValue3493, Sparse.eval] using hc.symm

theorem sound3494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3494 node3494Labels = Sparse.eval nodeValue3494 (mixedVector B) := by
  simpa only [nodeValue3494, Sparse.eval_nil] using zero3494 B _hB _hF

theorem sound3497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3497 node3497Labels = Sparse.eval nodeValue3497 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3497) = mixedMoment B node3497 node3497Labels := rfl
  simpa [nodeValue3497, Sparse.eval] using hc.symm

theorem sound3502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3502 node3502Labels = Sparse.eval nodeValue3502 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3502) = mixedMoment B node3502 node3502Labels := rfl
  simpa [nodeValue3502, Sparse.eval] using hc.symm

theorem sound3504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3504 node3504Labels = Sparse.eval nodeValue3504 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3504) = mixedMoment B node3504 node3504Labels := rfl
  simpa [nodeValue3504, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3531 node3531Labels = 0 := by
  exact mixedMoment_alpha B hF node3531 node3531Labels 1 permutation437
    (by decide +kernel)

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

theorem sound3531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3531 node3531Labels = Sparse.eval nodeValue3531 (mixedVector B) := by
  simpa only [nodeValue3531, Sparse.eval_nil] using zero3531 B _hB _hF

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3539 node3539Labels = Sparse.eval nodeValue3539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3539) = mixedMoment B node3539 node3539Labels := rfl
  simpa [nodeValue3539, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

theorem sound3580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3580 node3580Labels = Sparse.eval nodeValue3580 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3580) = mixedMoment B node3580 node3580Labels := rfl
  simpa [nodeValue3580, Sparse.eval] using hc.symm

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

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

theorem sound3627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3627 node3627Labels = Sparse.eval nodeValue3627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3627) = mixedMoment B node3627 node3627Labels := rfl
  simpa [nodeValue3627, Sparse.eval] using hc.symm

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

theorem sound3800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3800 node3800Labels = Sparse.eval nodeValue3800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3800) = mixedMoment B node3800 node3800Labels := rfl
  simpa [nodeValue3800, Sparse.eval] using hc.symm

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

theorem sound3871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3871 node3871Labels = Sparse.eval nodeValue3871 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3871) = mixedMoment B node3871 node3871Labels := rfl
  simpa [nodeValue3871, Sparse.eval] using hc.symm

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

theorem sound4803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4803 node4803Labels = Sparse.eval nodeValue4803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4803) = mixedMoment B node4803 node4803Labels := rfl
  simpa [nodeValue4803, Sparse.eval] using hc.symm

theorem sound4831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4831 node4831Labels = Sparse.eval nodeValue4831 (mixedVector B) := by
  have h := singleton4831 B _hB
  rw [sound2051 B _hB _hF, sound2191 B _hB _hF] at h
  norm_num [nodeValue4831, nodeValue2051, nodeValue2191, Sparse.eval] at h ⊢
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

theorem sound4888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4888 node4888Labels = Sparse.eval nodeValue4888 (mixedVector B) := by
  have h := singleton4888 B _hB
  rw [sound2244 B _hB _hF, sound2262 B _hB _hF] at h
  norm_num [nodeValue4888, nodeValue2244, nodeValue2262, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5242 node5242Labels = 0 := by
  exact mixedMoment_alpha B hF node5242 node5242Labels 1 permutation212
    (by decide +kernel)

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

theorem sound5220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5220 node5220Labels = Sparse.eval nodeValue5220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5220) = mixedMoment B node5220 node5220Labels := rfl
  simpa [nodeValue5220, Sparse.eval] using hc.symm

theorem sound5223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5223 node5223Labels = Sparse.eval nodeValue5223 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5223) = mixedMoment B node5223 node5223Labels := rfl
  simpa [nodeValue5223, Sparse.eval] using hc.symm

theorem sound5241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5241 node5241Labels = Sparse.eval nodeValue5241 (mixedVector B) := by
  have h := singleton5241 B _hB
  rw [sound2694 B _hB _hF, sound3493 B _hB _hF] at h
  norm_num [nodeValue5241, nodeValue2694, nodeValue3493, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5242 node5242Labels = Sparse.eval nodeValue5242 (mixedVector B) := by
  simpa only [nodeValue5242, Sparse.eval_nil] using zero5242 B _hB _hF

theorem sound5244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5244 node5244Labels = Sparse.eval nodeValue5244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5244) = mixedMoment B node5244 node5244Labels := rfl
  simpa [nodeValue5244, Sparse.eval] using hc.symm

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

theorem sound5249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5249 node5249Labels = Sparse.eval nodeValue5249 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5249) = mixedMoment B node5249 node5249Labels := rfl
  simpa [nodeValue5249, Sparse.eval] using hc.symm

theorem sound5251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5251 node5251Labels = Sparse.eval nodeValue5251 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5251) = mixedMoment B node5251 node5251Labels := rfl
  simpa [nodeValue5251, Sparse.eval] using hc.symm

theorem sound5253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5253 node5253Labels = Sparse.eval nodeValue5253 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5253) = mixedMoment B node5253 node5253Labels := rfl
  simpa [nodeValue5253, Sparse.eval] using hc.symm

theorem sound5254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5254 node5254Labels = Sparse.eval nodeValue5254 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5254) = mixedMoment B node5254 node5254Labels := rfl
  simpa [nodeValue5254, Sparse.eval] using hc.symm

theorem sound5258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5258 node5258Labels = Sparse.eval nodeValue5258 (mixedVector B) := by
  have h := singleton5258 B _hB
  rw [sound2722 B _hB _hF, sound3533 B _hB _hF] at h
  norm_num [nodeValue5258, nodeValue2722, nodeValue3533, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5259 node5259Labels = Sparse.eval nodeValue5259 (mixedVector B) := by
  have h := singleton5259 B _hB
  rw [sound2723 B _hB _hF, sound3544 B _hB _hF] at h
  norm_num [nodeValue5259, nodeValue2723, nodeValue3544, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5266 node5266Labels = Sparse.eval nodeValue5266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5266) = mixedMoment B node5266 node5266Labels := rfl
  simpa [nodeValue5266, Sparse.eval] using hc.symm

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

theorem sound5293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5293 node5293Labels = Sparse.eval nodeValue5293 (mixedVector B) := by
  have h := singleton5293 B _hB
  rw [sound2767 B _hB _hF, sound3627 B _hB _hF] at h
  norm_num [nodeValue5293, nodeValue2767, nodeValue3627, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources11
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq364 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm364 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA364 + difference 1 0) (sourceB364 + difference 0 1) sourceC364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1247) := by
    have ha : (tripleCharges (sourceA364 + difference 1 0) (sourceB364 + difference 0 1) sourceC364) = raw7200 := by
      apply Matrix.ext; unfold tripleCharges sourceA364 sourceB364 sourceC364 difference raw7200; decide +kernel
    rw [ha]
    exact (canonical7200 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA364 + difference 1 1) (sourceB364 + difference 1 1) sourceC364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA364 + difference 1 1) (sourceB364 + difference 1 1) sourceC364) = raw7193 := by
      apply Matrix.ext; unfold tripleCharges sourceA364 sourceB364 sourceC364 difference raw7193; decide +kernel
    rw [ha]
    exact (canonical7193 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA364 + difference 1 2) (sourceB364 + difference 2 1) sourceC364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2622) := by
    have ha : (tripleCharges (sourceA364 + difference 1 2) (sourceB364 + difference 2 1) sourceC364) = raw7205 := by
      apply Matrix.ext; unfold tripleCharges sourceA364 sourceB364 sourceC364 difference raw7205; decide +kernel
    rw [ha]
    exact (canonical7205 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA364 + difference 1 3) (sourceB364 + difference 3 1) sourceC364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2622) := by
    have ha : (tripleCharges (sourceA364 + difference 1 3) (sourceB364 + difference 3 1) sourceC364) = raw7206 := by
      apply Matrix.ext; unfold tripleCharges sourceA364 sourceB364 sourceC364 difference raw7206; decide +kernel
    rw [ha]
    exact (canonical7206 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA364 + difference 1 4) (sourceB364 + difference 4 1) sourceC364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA364 + difference 1 4) (sourceB364 + difference 4 1) sourceC364) = raw7207 := by
      apply Matrix.ext; unfold tripleCharges sourceA364 sourceB364 sourceC364 difference raw7207; decide +kernel
    rw [ha]
    exact (canonical7207 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA364 + difference 1 5) (sourceB364 + difference 5 1) sourceC364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA364 + difference 1 5) (sourceB364 + difference 5 1) sourceC364) = raw7208 := by
      apply Matrix.ext; unfold tripleCharges sourceA364 sourceB364 sourceC364 difference raw7208; decide +kernel
    rw [ha]
    exact (canonical7208 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA364 + sourceB364) sourceC364) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA364 + sourceB364) sourceC364) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA364 sourceB364 sourceC364 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA364 sourceB364 sourceC364
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm364, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq365 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm365 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA365 + difference 0 1) (sourceB365 + difference 1 0) sourceC365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA365 + difference 0 1) (sourceB365 + difference 1 0) sourceC365) = raw7194 := by
      apply Matrix.ext; unfold tripleCharges sourceA365 sourceB365 sourceC365 difference raw7194; decide +kernel
    rw [ha]
    exact (canonical7194 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA365 + difference 1 1) (sourceB365 + difference 1 1) sourceC365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA365 + difference 1 1) (sourceB365 + difference 1 1) sourceC365) = raw7193 := by
      apply Matrix.ext; unfold tripleCharges sourceA365 sourceB365 sourceC365 difference raw7193; decide +kernel
    rw [ha]
    exact (canonical7193 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA365 + difference 2 1) (sourceB365 + difference 1 2) sourceC365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA365 + difference 2 1) (sourceB365 + difference 1 2) sourceC365) = raw7209 := by
      apply Matrix.ext; unfold tripleCharges sourceA365 sourceB365 sourceC365 difference raw7209; decide +kernel
    rw [ha]
    exact (canonical7209 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA365 + difference 3 1) (sourceB365 + difference 1 3) sourceC365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA365 + difference 3 1) (sourceB365 + difference 1 3) sourceC365) = raw7210 := by
      apply Matrix.ext; unfold tripleCharges sourceA365 sourceB365 sourceC365 difference raw7210; decide +kernel
    rw [ha]
    exact (canonical7210 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA365 + difference 4 1) (sourceB365 + difference 1 4) sourceC365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2473) := by
    have ha : (tripleCharges (sourceA365 + difference 4 1) (sourceB365 + difference 1 4) sourceC365) = raw7211 := by
      apply Matrix.ext; unfold tripleCharges sourceA365 sourceB365 sourceC365 difference raw7211; decide +kernel
    rw [ha]
    exact (canonical7211 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA365 + difference 5 1) (sourceB365 + difference 1 5) sourceC365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2470) := by
    have ha : (tripleCharges (sourceA365 + difference 5 1) (sourceB365 + difference 1 5) sourceC365) = raw7212 := by
      apply Matrix.ext; unfold tripleCharges sourceA365 sourceB365 sourceC365 difference raw7212; decide +kernel
    rw [ha]
    exact (canonical7212 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA365 + sourceB365) sourceC365) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA365 + sourceB365) sourceC365) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA365 sourceB365 sourceC365 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA365 sourceB365 sourceC365
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm365, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq366 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm366 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA366 + difference 2 0) (sourceB366 + difference 0 2) sourceC366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA366 + difference 2 0) (sourceB366 + difference 0 2) sourceC366) = raw7201 := by
      apply Matrix.ext; unfold tripleCharges sourceA366 sourceB366 sourceC366 difference raw7201; decide +kernel
    rw [ha]
    exact (canonical7201 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA366 + difference 2 1) (sourceB366 + difference 1 2) sourceC366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA366 + difference 2 1) (sourceB366 + difference 1 2) sourceC366) = raw7209 := by
      apply Matrix.ext; unfold tripleCharges sourceA366 sourceB366 sourceC366 difference raw7209; decide +kernel
    rw [ha]
    exact (canonical7209 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA366 + difference 2 2) (sourceB366 + difference 2 2) sourceC366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA366 + difference 2 2) (sourceB366 + difference 2 2) sourceC366) = raw7193 := by
      apply Matrix.ext; unfold tripleCharges sourceA366 sourceB366 sourceC366 difference raw7193; decide +kernel
    rw [ha]
    exact (canonical7193 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA366 + difference 2 3) (sourceB366 + difference 3 2) sourceC366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA366 + difference 2 3) (sourceB366 + difference 3 2) sourceC366) = raw7213 := by
      apply Matrix.ext; unfold tripleCharges sourceA366 sourceB366 sourceC366 difference raw7213; decide +kernel
    rw [ha]
    exact (canonical7213 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA366 + difference 2 4) (sourceB366 + difference 4 2) sourceC366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA366 + difference 2 4) (sourceB366 + difference 4 2) sourceC366) = raw7214 := by
      apply Matrix.ext; unfold tripleCharges sourceA366 sourceB366 sourceC366 difference raw7214; decide +kernel
    rw [ha]
    exact (canonical7214 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA366 + difference 2 5) (sourceB366 + difference 5 2) sourceC366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA366 + difference 2 5) (sourceB366 + difference 5 2) sourceC366) = raw7215 := by
      apply Matrix.ext; unfold tripleCharges sourceA366 sourceB366 sourceC366 difference raw7215; decide +kernel
    rw [ha]
    exact (canonical7215 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA366 + sourceB366) sourceC366) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA366 + sourceB366) sourceC366) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA366 sourceB366 sourceC366 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA366 sourceB366 sourceC366
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm366, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq367 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm367 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA367 + difference 0 2) (sourceB367 + difference 2 0) sourceC367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA367 + difference 0 2) (sourceB367 + difference 2 0) sourceC367) = raw7195 := by
      apply Matrix.ext; unfold tripleCharges sourceA367 sourceB367 sourceC367 difference raw7195; decide +kernel
    rw [ha]
    exact (canonical7195 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA367 + difference 1 2) (sourceB367 + difference 2 1) sourceC367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2622) := by
    have ha : (tripleCharges (sourceA367 + difference 1 2) (sourceB367 + difference 2 1) sourceC367) = raw7205 := by
      apply Matrix.ext; unfold tripleCharges sourceA367 sourceB367 sourceC367 difference raw7205; decide +kernel
    rw [ha]
    exact (canonical7205 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA367 + difference 2 2) (sourceB367 + difference 2 2) sourceC367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA367 + difference 2 2) (sourceB367 + difference 2 2) sourceC367) = raw7193 := by
      apply Matrix.ext; unfold tripleCharges sourceA367 sourceB367 sourceC367 difference raw7193; decide +kernel
    rw [ha]
    exact (canonical7193 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA367 + difference 3 2) (sourceB367 + difference 2 3) sourceC367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA367 + difference 3 2) (sourceB367 + difference 2 3) sourceC367) = raw7216 := by
      apply Matrix.ext; unfold tripleCharges sourceA367 sourceB367 sourceC367 difference raw7216; decide +kernel
    rw [ha]
    exact (canonical7216 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA367 + difference 4 2) (sourceB367 + difference 2 4) sourceC367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2612) := by
    have ha : (tripleCharges (sourceA367 + difference 4 2) (sourceB367 + difference 2 4) sourceC367) = raw7217 := by
      apply Matrix.ext; unfold tripleCharges sourceA367 sourceB367 sourceC367 difference raw7217; decide +kernel
    rw [ha]
    exact (canonical7217 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA367 + difference 5 2) (sourceB367 + difference 2 5) sourceC367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2610) := by
    have ha : (tripleCharges (sourceA367 + difference 5 2) (sourceB367 + difference 2 5) sourceC367) = raw7218 := by
      apply Matrix.ext; unfold tripleCharges sourceA367 sourceB367 sourceC367 difference raw7218; decide +kernel
    rw [ha]
    exact (canonical7218 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA367 + sourceB367) sourceC367) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA367 + sourceB367) sourceC367) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA367 sourceB367 sourceC367 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA367 sourceB367 sourceC367
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm367, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq368 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm368 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA368 + difference 4 0) (sourceB368 + difference 0 4) sourceC368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1208) := by
    have ha : (tripleCharges (sourceA368 + difference 4 0) (sourceB368 + difference 0 4) sourceC368) = raw7203 := by
      apply Matrix.ext; unfold tripleCharges sourceA368 sourceB368 sourceC368 difference raw7203; decide +kernel
    rw [ha]
    exact (canonical7203 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA368 + difference 4 1) (sourceB368 + difference 1 4) sourceC368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2473) := by
    have ha : (tripleCharges (sourceA368 + difference 4 1) (sourceB368 + difference 1 4) sourceC368) = raw7211 := by
      apply Matrix.ext; unfold tripleCharges sourceA368 sourceB368 sourceC368 difference raw7211; decide +kernel
    rw [ha]
    exact (canonical7211 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA368 + difference 4 2) (sourceB368 + difference 2 4) sourceC368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2612) := by
    have ha : (tripleCharges (sourceA368 + difference 4 2) (sourceB368 + difference 2 4) sourceC368) = raw7217 := by
      apply Matrix.ext; unfold tripleCharges sourceA368 sourceB368 sourceC368 difference raw7217; decide +kernel
    rw [ha]
    exact (canonical7217 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA368 + difference 4 3) (sourceB368 + difference 3 4) sourceC368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2612) := by
    have ha : (tripleCharges (sourceA368 + difference 4 3) (sourceB368 + difference 3 4) sourceC368) = raw7219 := by
      apply Matrix.ext; unfold tripleCharges sourceA368 sourceB368 sourceC368 difference raw7219; decide +kernel
    rw [ha]
    exact (canonical7219 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA368 + difference 4 4) (sourceB368 + difference 4 4) sourceC368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA368 + difference 4 4) (sourceB368 + difference 4 4) sourceC368) = raw7193 := by
      apply Matrix.ext; unfold tripleCharges sourceA368 sourceB368 sourceC368 difference raw7193; decide +kernel
    rw [ha]
    exact (canonical7193 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA368 + difference 4 5) (sourceB368 + difference 5 4) sourceC368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA368 + difference 4 5) (sourceB368 + difference 5 4) sourceC368) = raw7220 := by
      apply Matrix.ext; unfold tripleCharges sourceA368 sourceB368 sourceC368 difference raw7220; decide +kernel
    rw [ha]
    exact (canonical7220 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA368 + sourceB368) sourceC368) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA368 + sourceB368) sourceC368) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA368 sourceB368 sourceC368 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA368 sourceB368 sourceC368
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm368, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq369 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm369 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA369 + difference 0 1) (sourceB369 + difference 1 0) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5244) := by
    have ha : (tripleCharges (sourceA369 + difference 0 1) (sourceB369 + difference 1 0) sourceC369) = raw7221 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7221; decide +kernel
    rw [ha]
    exact (canonical7221 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA369 + difference 0 2) (sourceB369 + difference 2 0) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA369 + difference 0 2) (sourceB369 + difference 2 0) sourceC369) = raw6702 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6702; decide +kernel
    rw [ha]
    exact (canonical6702 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA369 + difference 0 3) (sourceB369 + difference 3 0) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA369 + difference 0 3) (sourceB369 + difference 3 0) sourceC369) = raw7222 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7222; decide +kernel
    rw [ha]
    exact (canonical7222 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA369 + difference 0 4) (sourceB369 + difference 4 0) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5242) := by
    have ha : (tripleCharges (sourceA369 + difference 0 4) (sourceB369 + difference 4 0) sourceC369) = raw7223 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7223; decide +kernel
    rw [ha]
    exact (canonical7223 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA369 + difference 0 5) (sourceB369 + difference 5 0) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA369 + difference 0 5) (sourceB369 + difference 5 0) sourceC369) = raw7224 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7224; decide +kernel
    rw [ha]
    exact (canonical7224 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA369 + difference 1 0) (sourceB369 + difference 0 1) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA369 + difference 1 0) (sourceB369 + difference 0 1) sourceC369) = raw5684 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw5684; decide +kernel
    rw [ha]
    exact (canonical5684 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA369 + difference 1 2) (sourceB369 + difference 2 1) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA369 + difference 1 2) (sourceB369 + difference 2 1) sourceC369) = raw6707 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6707; decide +kernel
    rw [ha]
    exact (canonical6707 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA369 + difference 1 3) (sourceB369 + difference 3 1) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA369 + difference 1 3) (sourceB369 + difference 3 1) sourceC369) = raw7225 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7225; decide +kernel
    rw [ha]
    exact (canonical7225 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA369 + difference 1 4) (sourceB369 + difference 4 1) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA369 + difference 1 4) (sourceB369 + difference 4 1) sourceC369) = raw7226 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7226; decide +kernel
    rw [ha]
    exact (canonical7226 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA369 + difference 1 5) (sourceB369 + difference 5 1) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA369 + difference 1 5) (sourceB369 + difference 5 1) sourceC369) = raw5658 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw5658; decide +kernel
    rw [ha]
    exact (canonical5658 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA369 + difference 2 0) (sourceB369 + difference 0 2) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA369 + difference 2 0) (sourceB369 + difference 0 2) sourceC369) = raw7227 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7227; decide +kernel
    rw [ha]
    exact (canonical7227 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA369 + difference 2 1) (sourceB369 + difference 1 2) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5223) := by
    have ha : (tripleCharges (sourceA369 + difference 2 1) (sourceB369 + difference 1 2) sourceC369) = raw7228 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7228; decide +kernel
    rw [ha]
    exact (canonical7228 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA369 + difference 2 3) (sourceB369 + difference 3 2) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA369 + difference 2 3) (sourceB369 + difference 3 2) sourceC369) = raw7229 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7229; decide +kernel
    rw [ha]
    exact (canonical7229 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA369 + difference 2 4) (sourceB369 + difference 4 2) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5253) := by
    have ha : (tripleCharges (sourceA369 + difference 2 4) (sourceB369 + difference 4 2) sourceC369) = raw7230 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7230; decide +kernel
    rw [ha]
    exact (canonical7230 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA369 + difference 2 5) (sourceB369 + difference 5 2) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA369 + difference 2 5) (sourceB369 + difference 5 2) sourceC369) = raw7231 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7231; decide +kernel
    rw [ha]
    exact (canonical7231 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA369 + difference 3 0) (sourceB369 + difference 0 3) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA369 + difference 3 0) (sourceB369 + difference 0 3) sourceC369) = raw6710 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6710; decide +kernel
    rw [ha]
    exact (canonical6710 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA369 + difference 3 1) (sourceB369 + difference 1 3) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5223) := by
    have ha : (tripleCharges (sourceA369 + difference 3 1) (sourceB369 + difference 1 3) sourceC369) = raw6711 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6711; decide +kernel
    rw [ha]
    exact (canonical6711 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA369 + difference 3 2) (sourceB369 + difference 2 3) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA369 + difference 3 2) (sourceB369 + difference 2 3) sourceC369) = raw7063 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7063; decide +kernel
    rw [ha]
    exact (canonical7063 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA369 + difference 3 4) (sourceB369 + difference 4 3) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5253) := by
    have ha : (tripleCharges (sourceA369 + difference 3 4) (sourceB369 + difference 4 3) sourceC369) = raw6713 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6713; decide +kernel
    rw [ha]
    exact (canonical6713 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA369 + difference 3 5) (sourceB369 + difference 5 3) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA369 + difference 3 5) (sourceB369 + difference 5 3) sourceC369) = raw6714 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6714; decide +kernel
    rw [ha]
    exact (canonical6714 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA369 + difference 4 0) (sourceB369 + difference 0 4) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA369 + difference 4 0) (sourceB369 + difference 0 4) sourceC369) = raw7232 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7232; decide +kernel
    rw [ha]
    exact (canonical7232 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA369 + difference 4 1) (sourceB369 + difference 1 4) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5220) := by
    have ha : (tripleCharges (sourceA369 + difference 4 1) (sourceB369 + difference 1 4) sourceC369) = raw7233 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7233; decide +kernel
    rw [ha]
    exact (canonical7233 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA369 + difference 4 2) (sourceB369 + difference 2 4) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA369 + difference 4 2) (sourceB369 + difference 2 4) sourceC369) = raw6390 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6390; decide +kernel
    rw [ha]
    exact (canonical6390 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA369 + difference 4 3) (sourceB369 + difference 3 4) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA369 + difference 4 3) (sourceB369 + difference 3 4) sourceC369) = raw7234 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7234; decide +kernel
    rw [ha]
    exact (canonical7234 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA369 + difference 4 5) (sourceB369 + difference 5 4) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA369 + difference 4 5) (sourceB369 + difference 5 4) sourceC369) = raw6379 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6379; decide +kernel
    rw [ha]
    exact (canonical6379 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA369 + difference 5 0) (sourceB369 + difference 0 5) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA369 + difference 5 0) (sourceB369 + difference 0 5) sourceC369) = raw7235 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7235; decide +kernel
    rw [ha]
    exact (canonical7235 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA369 + difference 5 1) (sourceB369 + difference 1 5) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5219) := by
    have ha : (tripleCharges (sourceA369 + difference 5 1) (sourceB369 + difference 1 5) sourceC369) = raw7236 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7236; decide +kernel
    rw [ha]
    exact (canonical7236 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA369 + difference 5 2) (sourceB369 + difference 2 5) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA369 + difference 5 2) (sourceB369 + difference 2 5) sourceC369) = raw6726 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6726; decide +kernel
    rw [ha]
    exact (canonical6726 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA369 + difference 5 3) (sourceB369 + difference 3 5) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA369 + difference 5 3) (sourceB369 + difference 3 5) sourceC369) = raw7237 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7237; decide +kernel
    rw [ha]
    exact (canonical7237 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA369 + difference 5 4) (sourceB369 + difference 4 5) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA369 + difference 5 4) (sourceB369 + difference 4 5) sourceC369) = raw7238 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7238; decide +kernel
    rw [ha]
    exact (canonical7238 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA369 sourceB369 sourceC369
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm369, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq372 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm372 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA372 + difference 0 0) (sourceB372 + difference 0 0) sourceC372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA372 + difference 0 0) (sourceB372 + difference 0 0) sourceC372) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA372 sourceB372 sourceC372 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA372 + difference 0 1) (sourceB372 + difference 1 0) sourceC372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3497) := by
    have ha : (tripleCharges (sourceA372 + difference 0 1) (sourceB372 + difference 1 0) sourceC372) = raw7275 := by
      apply Matrix.ext; unfold tripleCharges sourceA372 sourceB372 sourceC372 difference raw7275; decide +kernel
    rw [ha]
    exact (canonical7275 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA372 + difference 0 2) (sourceB372 + difference 2 0) sourceC372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA372 + difference 0 2) (sourceB372 + difference 2 0) sourceC372) = raw6787 := by
      apply Matrix.ext; unfold tripleCharges sourceA372 sourceB372 sourceC372 difference raw6787; decide +kernel
    rw [ha]
    exact (canonical6787 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA372 + difference 0 3) (sourceB372 + difference 3 0) sourceC372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA372 + difference 0 3) (sourceB372 + difference 3 0) sourceC372) = raw7276 := by
      apply Matrix.ext; unfold tripleCharges sourceA372 sourceB372 sourceC372 difference raw7276; decide +kernel
    rw [ha]
    exact (canonical7276 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA372 + difference 0 4) (sourceB372 + difference 4 0) sourceC372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3494) := by
    have ha : (tripleCharges (sourceA372 + difference 0 4) (sourceB372 + difference 4 0) sourceC372) = raw7277 := by
      apply Matrix.ext; unfold tripleCharges sourceA372 sourceB372 sourceC372 difference raw7277; decide +kernel
    rw [ha]
    exact (canonical7277 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA372 + difference 0 5) (sourceB372 + difference 5 0) sourceC372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3493) := by
    have ha : (tripleCharges (sourceA372 + difference 0 5) (sourceB372 + difference 5 0) sourceC372) = raw7278 := by
      apply Matrix.ext; unfold tripleCharges sourceA372 sourceB372 sourceC372 difference raw7278; decide +kernel
    rw [ha]
    exact (canonical7278 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA372 + sourceB372) sourceC372) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA372 + sourceB372) sourceC372) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA372 sourceB372 sourceC372 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA372 sourceB372 sourceC372
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm372, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq373 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm373 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA373 + difference 0 0) (sourceB373 + difference 0 0) sourceC373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA373 + difference 0 0) (sourceB373 + difference 0 0) sourceC373) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA373 sourceB373 sourceC373 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA373 + difference 1 0) (sourceB373 + difference 0 1) sourceC373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA373 + difference 1 0) (sourceB373 + difference 0 1) sourceC373) = raw5768 := by
      apply Matrix.ext; unfold tripleCharges sourceA373 sourceB373 sourceC373 difference raw5768; decide +kernel
    rw [ha]
    exact (canonical5768 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA373 + difference 2 0) (sourceB373 + difference 0 2) sourceC373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA373 + difference 2 0) (sourceB373 + difference 0 2) sourceC373) = raw7279 := by
      apply Matrix.ext; unfold tripleCharges sourceA373 sourceB373 sourceC373 difference raw7279; decide +kernel
    rw [ha]
    exact (canonical7279 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA373 + difference 3 0) (sourceB373 + difference 0 3) sourceC373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA373 + difference 3 0) (sourceB373 + difference 0 3) sourceC373) = raw6791 := by
      apply Matrix.ext; unfold tripleCharges sourceA373 sourceB373 sourceC373 difference raw6791; decide +kernel
    rw [ha]
    exact (canonical6791 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA373 + difference 4 0) (sourceB373 + difference 0 4) sourceC373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2051) := by
    have ha : (tripleCharges (sourceA373 + difference 4 0) (sourceB373 + difference 0 4) sourceC373) = raw7280 := by
      apply Matrix.ext; unfold tripleCharges sourceA373 sourceB373 sourceC373 difference raw7280; decide +kernel
    rw [ha]
    exact (canonical7280 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA373 + difference 5 0) (sourceB373 + difference 0 5) sourceC373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2019) := by
    have ha : (tripleCharges (sourceA373 + difference 5 0) (sourceB373 + difference 0 5) sourceC373) = raw7281 := by
      apply Matrix.ext; unfold tripleCharges sourceA373 sourceB373 sourceC373 difference raw7281; decide +kernel
    rw [ha]
    exact (canonical7281 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA373 + sourceB373) sourceC373) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA373 + sourceB373) sourceC373) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA373 sourceB373 sourceC373 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA373 sourceB373 sourceC373
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm373, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq374 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm374 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA374 + difference 1 0) (sourceB374 + difference 0 1) sourceC374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA374 + difference 1 0) (sourceB374 + difference 0 1) sourceC374) = raw5768 := by
      apply Matrix.ext; unfold tripleCharges sourceA374 sourceB374 sourceC374 difference raw5768; decide +kernel
    rw [ha]
    exact (canonical5768 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA374 + difference 1 1) (sourceB374 + difference 1 1) sourceC374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA374 + difference 1 1) (sourceB374 + difference 1 1) sourceC374) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA374 sourceB374 sourceC374 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA374 + difference 1 2) (sourceB374 + difference 2 1) sourceC374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA374 + difference 1 2) (sourceB374 + difference 2 1) sourceC374) = raw6796 := by
      apply Matrix.ext; unfold tripleCharges sourceA374 sourceB374 sourceC374 difference raw6796; decide +kernel
    rw [ha]
    exact (canonical6796 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA374 + difference 1 3) (sourceB374 + difference 3 1) sourceC374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA374 + difference 1 3) (sourceB374 + difference 3 1) sourceC374) = raw7282 := by
      apply Matrix.ext; unfold tripleCharges sourceA374 sourceB374 sourceC374 difference raw7282; decide +kernel
    rw [ha]
    exact (canonical7282 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA374 + difference 1 4) (sourceB374 + difference 4 1) sourceC374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA374 + difference 1 4) (sourceB374 + difference 4 1) sourceC374) = raw7283 := by
      apply Matrix.ext; unfold tripleCharges sourceA374 sourceB374 sourceC374 difference raw7283; decide +kernel
    rw [ha]
    exact (canonical7283 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA374 + difference 1 5) (sourceB374 + difference 5 1) sourceC374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA374 + difference 1 5) (sourceB374 + difference 5 1) sourceC374) = raw5749 := by
      apply Matrix.ext; unfold tripleCharges sourceA374 sourceB374 sourceC374 difference raw5749; decide +kernel
    rw [ha]
    exact (canonical5749 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA374 + sourceB374) sourceC374) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA374 + sourceB374) sourceC374) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA374 sourceB374 sourceC374 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA374 sourceB374 sourceC374
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm374, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq375 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm375 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA375 + difference 0 1) (sourceB375 + difference 1 0) sourceC375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3497) := by
    have ha : (tripleCharges (sourceA375 + difference 0 1) (sourceB375 + difference 1 0) sourceC375) = raw7275 := by
      apply Matrix.ext; unfold tripleCharges sourceA375 sourceB375 sourceC375 difference raw7275; decide +kernel
    rw [ha]
    exact (canonical7275 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA375 + difference 1 1) (sourceB375 + difference 1 1) sourceC375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA375 + difference 1 1) (sourceB375 + difference 1 1) sourceC375) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA375 sourceB375 sourceC375 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA375 + difference 2 1) (sourceB375 + difference 1 2) sourceC375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3377) := by
    have ha : (tripleCharges (sourceA375 + difference 2 1) (sourceB375 + difference 1 2) sourceC375) = raw7284 := by
      apply Matrix.ext; unfold tripleCharges sourceA375 sourceB375 sourceC375 difference raw7284; decide +kernel
    rw [ha]
    exact (canonical7284 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA375 + difference 3 1) (sourceB375 + difference 1 3) sourceC375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3377) := by
    have ha : (tripleCharges (sourceA375 + difference 3 1) (sourceB375 + difference 1 3) sourceC375) = raw6799 := by
      apply Matrix.ext; unfold tripleCharges sourceA375 sourceB375 sourceC375 difference raw6799; decide +kernel
    rw [ha]
    exact (canonical6799 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA375 + difference 4 1) (sourceB375 + difference 1 4) sourceC375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3388) := by
    have ha : (tripleCharges (sourceA375 + difference 4 1) (sourceB375 + difference 1 4) sourceC375) = raw7285 := by
      apply Matrix.ext; unfold tripleCharges sourceA375 sourceB375 sourceC375 difference raw7285; decide +kernel
    rw [ha]
    exact (canonical7285 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA375 + difference 5 1) (sourceB375 + difference 1 5) sourceC375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3375) := by
    have ha : (tripleCharges (sourceA375 + difference 5 1) (sourceB375 + difference 1 5) sourceC375) = raw7286 := by
      apply Matrix.ext; unfold tripleCharges sourceA375 sourceB375 sourceC375 difference raw7286; decide +kernel
    rw [ha]
    exact (canonical7286 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA375 + sourceB375) sourceC375) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA375 + sourceB375) sourceC375) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA375 sourceB375 sourceC375 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA375 sourceB375 sourceC375
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm375, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq376 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm376 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA376 + difference 4 0) (sourceB376 + difference 0 4) sourceC376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2051) := by
    have ha : (tripleCharges (sourceA376 + difference 4 0) (sourceB376 + difference 0 4) sourceC376) = raw7280 := by
      apply Matrix.ext; unfold tripleCharges sourceA376 sourceB376 sourceC376 difference raw7280; decide +kernel
    rw [ha]
    exact (canonical7280 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA376 + difference 4 1) (sourceB376 + difference 1 4) sourceC376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3388) := by
    have ha : (tripleCharges (sourceA376 + difference 4 1) (sourceB376 + difference 1 4) sourceC376) = raw7285 := by
      apply Matrix.ext; unfold tripleCharges sourceA376 sourceB376 sourceC376 difference raw7285; decide +kernel
    rw [ha]
    exact (canonical7285 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA376 + difference 4 2) (sourceB376 + difference 2 4) sourceC376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA376 + difference 4 2) (sourceB376 + difference 2 4) sourceC376) = raw6456 := by
      apply Matrix.ext; unfold tripleCharges sourceA376 sourceB376 sourceC376 difference raw6456; decide +kernel
    rw [ha]
    exact (canonical6456 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA376 + difference 4 3) (sourceB376 + difference 3 4) sourceC376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA376 + difference 4 3) (sourceB376 + difference 3 4) sourceC376) = raw7287 := by
      apply Matrix.ext; unfold tripleCharges sourceA376 sourceB376 sourceC376 difference raw7287; decide +kernel
    rw [ha]
    exact (canonical7287 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA376 + difference 4 4) (sourceB376 + difference 4 4) sourceC376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA376 + difference 4 4) (sourceB376 + difference 4 4) sourceC376) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA376 sourceB376 sourceC376 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA376 + difference 4 5) (sourceB376 + difference 5 4) sourceC376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA376 + difference 4 5) (sourceB376 + difference 5 4) sourceC376) = raw6450 := by
      apply Matrix.ext; unfold tripleCharges sourceA376 sourceB376 sourceC376 difference raw6450; decide +kernel
    rw [ha]
    exact (canonical6450 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA376 + sourceB376) sourceC376) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA376 + sourceB376) sourceC376) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA376 sourceB376 sourceC376 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA376 sourceB376 sourceC376
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm376, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq377 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm377 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA377 + difference 0 4) (sourceB377 + difference 4 0) sourceC377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3494) := by
    have ha : (tripleCharges (sourceA377 + difference 0 4) (sourceB377 + difference 4 0) sourceC377) = raw7277 := by
      apply Matrix.ext; unfold tripleCharges sourceA377 sourceB377 sourceC377 difference raw7277; decide +kernel
    rw [ha]
    exact (canonical7277 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA377 + difference 1 4) (sourceB377 + difference 4 1) sourceC377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA377 + difference 1 4) (sourceB377 + difference 4 1) sourceC377) = raw7283 := by
      apply Matrix.ext; unfold tripleCharges sourceA377 sourceB377 sourceC377 difference raw7283; decide +kernel
    rw [ha]
    exact (canonical7283 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA377 + difference 2 4) (sourceB377 + difference 4 2) sourceC377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3504) := by
    have ha : (tripleCharges (sourceA377 + difference 2 4) (sourceB377 + difference 4 2) sourceC377) = raw7288 := by
      apply Matrix.ext; unfold tripleCharges sourceA377 sourceB377 sourceC377 difference raw7288; decide +kernel
    rw [ha]
    exact (canonical7288 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA377 + difference 3 4) (sourceB377 + difference 4 3) sourceC377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3504) := by
    have ha : (tripleCharges (sourceA377 + difference 3 4) (sourceB377 + difference 4 3) sourceC377) = raw6804 := by
      apply Matrix.ext; unfold tripleCharges sourceA377 sourceB377 sourceC377 difference raw6804; decide +kernel
    rw [ha]
    exact (canonical6804 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA377 + difference 4 4) (sourceB377 + difference 4 4) sourceC377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA377 + difference 4 4) (sourceB377 + difference 4 4) sourceC377) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA377 sourceB377 sourceC377 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA377 + difference 5 4) (sourceB377 + difference 4 5) sourceC377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3502) := by
    have ha : (tripleCharges (sourceA377 + difference 5 4) (sourceB377 + difference 4 5) sourceC377) = raw7289 := by
      apply Matrix.ext; unfold tripleCharges sourceA377 sourceB377 sourceC377 difference raw7289; decide +kernel
    rw [ha]
    exact (canonical7289 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA377 + sourceB377) sourceC377) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA377 + sourceB377) sourceC377) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA377 sourceB377 sourceC377 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA377 sourceB377 sourceC377
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm377, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm378 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA378 + difference 5 0) (sourceB378 + difference 0 5) sourceC378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2019) := by
    have ha : (tripleCharges (sourceA378 + difference 5 0) (sourceB378 + difference 0 5) sourceC378) = raw7281 := by
      apply Matrix.ext; unfold tripleCharges sourceA378 sourceB378 sourceC378 difference raw7281; decide +kernel
    rw [ha]
    exact (canonical7281 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA378 + difference 5 1) (sourceB378 + difference 1 5) sourceC378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3375) := by
    have ha : (tripleCharges (sourceA378 + difference 5 1) (sourceB378 + difference 1 5) sourceC378) = raw7286 := by
      apply Matrix.ext; unfold tripleCharges sourceA378 sourceB378 sourceC378 difference raw7286; decide +kernel
    rw [ha]
    exact (canonical7286 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA378 + difference 5 2) (sourceB378 + difference 2 5) sourceC378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA378 + difference 5 2) (sourceB378 + difference 2 5) sourceC378) = raw6811 := by
      apply Matrix.ext; unfold tripleCharges sourceA378 sourceB378 sourceC378 difference raw6811; decide +kernel
    rw [ha]
    exact (canonical6811 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA378 + difference 5 3) (sourceB378 + difference 3 5) sourceC378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA378 + difference 5 3) (sourceB378 + difference 3 5) sourceC378) = raw7290 := by
      apply Matrix.ext; unfold tripleCharges sourceA378 sourceB378 sourceC378 difference raw7290; decide +kernel
    rw [ha]
    exact (canonical7290 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA378 + difference 5 4) (sourceB378 + difference 4 5) sourceC378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3502) := by
    have ha : (tripleCharges (sourceA378 + difference 5 4) (sourceB378 + difference 4 5) sourceC378) = raw7289 := by
      apply Matrix.ext; unfold tripleCharges sourceA378 sourceB378 sourceC378 difference raw7289; decide +kernel
    rw [ha]
    exact (canonical7289 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA378 + difference 5 5) (sourceB378 + difference 5 5) sourceC378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA378 + difference 5 5) (sourceB378 + difference 5 5) sourceC378) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA378 sourceB378 sourceC378 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA378 + sourceB378) sourceC378) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA378 + sourceB378) sourceC378) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA378 sourceB378 sourceC378 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA378 sourceB378 sourceC378
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm378, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck304 : Integer.Sparse.reindex keyMap MixedData.row304 = numericRow304 := by decide +kernel

theorem numericCheck304 (x : Master → ℝ) : Integer.Sparse.eval numericRow304 x =
    (1 : ℝ) * reducedSource304 x := by
  norm_num [numericRow304, reducedSource304, Integer.Sparse.eval, Sparse.eval, nodeValue1247, nodeValue2622, nodeValue2709, nodeValue2750, nodeValue2751, nodeValue4091]

theorem reindexCheck305 : Integer.Sparse.reindex keyMap MixedData.row305 = numericRow305 := by decide +kernel

theorem numericCheck305 (x : Master → ℝ) : Integer.Sparse.eval numericRow305 x =
    (1 : ℝ) * reducedSource305 x := by
  norm_num [numericRow305, reducedSource305, Integer.Sparse.eval, Sparse.eval, nodeValue2470, nodeValue2473, nodeValue2480, nodeValue2709, nodeValue3800, nodeValue4091]

theorem reindexCheck306 : Integer.Sparse.reindex keyMap MixedData.row306 = numericRow306 := by decide +kernel

theorem numericCheck306 (x : Master → ℝ) : Integer.Sparse.eval numericRow306 x =
    (1 : ℝ) * reducedSource306 x := by
  norm_num [numericRow306, reducedSource306, Integer.Sparse.eval, Sparse.eval, nodeValue1213, nodeValue2480, nodeValue2615, nodeValue2709, nodeValue2721, nodeValue2723, nodeValue4091]

theorem reindexCheck307 : Integer.Sparse.reindex keyMap MixedData.row307 = numericRow307 := by decide +kernel

theorem numericCheck307 (x : Master → ℝ) : Integer.Sparse.eval numericRow307 x =
    (1 : ℝ) * reducedSource307 x := by
  norm_num [numericRow307, reducedSource307, Integer.Sparse.eval, Sparse.eval, nodeValue2610, nodeValue2612, nodeValue2615, nodeValue2622, nodeValue2709, nodeValue3871, nodeValue4091]

theorem reindexCheck308 : Integer.Sparse.reindex keyMap MixedData.row308 = numericRow308 := by decide +kernel

theorem numericCheck308 (x : Master → ℝ) : Integer.Sparse.eval numericRow308 x =
    (1 : ℝ) * reducedSource308 x := by
  norm_num [numericRow308, reducedSource308, Integer.Sparse.eval, Sparse.eval, nodeValue1208, nodeValue2473, nodeValue2612, nodeValue2709, nodeValue2710, nodeValue4091]

theorem reindexCheck309 : Integer.Sparse.reindex keyMap MixedData.row309 = numericRow309 := by decide +kernel

theorem numericCheck309 (x : Master → ℝ) : Integer.Sparse.eval numericRow309 x =
    (720 : ℝ) * reducedSource309 x := by
  norm_num [numericRow309, reducedSource309, Integer.Sparse.eval, Sparse.eval, nodeValue4801, nodeValue4803, nodeValue4831, nodeValue4888, nodeValue5219, nodeValue5220, nodeValue5223, nodeValue5241, nodeValue5242, nodeValue5244, nodeValue5249, nodeValue5251, nodeValue5253, nodeValue5254, nodeValue5258, nodeValue5259, nodeValue5266, nodeValue5282, nodeValue5284, nodeValue5293]
  ring

theorem reindexCheck312 : Integer.Sparse.reindex keyMap MixedData.row312 = numericRow312 := by decide +kernel

theorem numericCheck312 (x : Master → ℝ) : Integer.Sparse.eval numericRow312 x =
    (1 : ℝ) * reducedSource312 x := by
  norm_num [numericRow312, reducedSource312, Integer.Sparse.eval, Sparse.eval, nodeValue3493, nodeValue3494, nodeValue3497, nodeValue3531, nodeValue3544, nodeValue4084]

theorem reindexCheck313 : Integer.Sparse.reindex keyMap MixedData.row313 = numericRow313 := by decide +kernel

theorem numericCheck313 (x : Master → ℝ) : Integer.Sparse.eval numericRow313 x =
    (1 : ℝ) * reducedSource313 x := by
  norm_num [numericRow313, reducedSource313, Integer.Sparse.eval, Sparse.eval, nodeValue2019, nodeValue2021, nodeValue2051, nodeValue2262, nodeValue3531, nodeValue4084]

theorem reindexCheck314 : Integer.Sparse.reindex keyMap MixedData.row314 = numericRow314 := by decide +kernel

theorem numericCheck314 (x : Master → ℝ) : Integer.Sparse.eval numericRow314 x =
    (1 : ℝ) * reducedSource314 x := by
  norm_num [numericRow314, reducedSource314, Integer.Sparse.eval, Sparse.eval, nodeValue2262, nodeValue3531, nodeValue3580, nodeValue3625, nodeValue3627, nodeValue4084]

theorem reindexCheck315 : Integer.Sparse.reindex keyMap MixedData.row315 = numericRow315 := by decide +kernel

theorem numericCheck315 (x : Master → ℝ) : Integer.Sparse.eval numericRow315 x =
    (1 : ℝ) * reducedSource315 x := by
  norm_num [numericRow315, reducedSource315, Integer.Sparse.eval, Sparse.eval, nodeValue3375, nodeValue3377, nodeValue3388, nodeValue3497, nodeValue3531, nodeValue4084]

theorem reindexCheck316 : Integer.Sparse.reindex keyMap MixedData.row316 = numericRow316 := by decide +kernel

theorem numericCheck316 (x : Master → ℝ) : Integer.Sparse.eval numericRow316 x =
    (1 : ℝ) * reducedSource316 x := by
  norm_num [numericRow316, reducedSource316, Integer.Sparse.eval, Sparse.eval, nodeValue2051, nodeValue3388, nodeValue3531, nodeValue3539, nodeValue3544, nodeValue4084]

theorem reindexCheck317 : Integer.Sparse.reindex keyMap MixedData.row317 = numericRow317 := by decide +kernel

theorem numericCheck317 (x : Master → ℝ) : Integer.Sparse.eval numericRow317 x =
    (1 : ℝ) * reducedSource317 x := by
  norm_num [numericRow317, reducedSource317, Integer.Sparse.eval, Sparse.eval, nodeValue3494, nodeValue3502, nodeValue3504, nodeValue3531, nodeValue3580, nodeValue4084]

theorem reindexCheck318 : Integer.Sparse.reindex keyMap MixedData.row318 = numericRow318 := by decide +kernel

theorem numericCheck318 (x : Master → ℝ) : Integer.Sparse.eval numericRow318 x =
    (1 : ℝ) * reducedSource318 x := by
  norm_num [numericRow318, reducedSource318, Integer.Sparse.eval, Sparse.eval, nodeValue2019, nodeValue3375, nodeValue3502, nodeValue3531, nodeValue3533, nodeValue4084]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero304 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource304 (mixedVector B) = 0 := by
  have h1247 : mixedVector B (Sum.inr 1247) = Sparse.eval nodeValue1247 (mixedVector B) := by
    change mixedMoment B node1247 node1247Labels = _
    exact sound1247 B hB hF
  have h2622 : mixedVector B (Sum.inr 2622) = Sparse.eval nodeValue2622 (mixedVector B) := by
    change mixedMoment B node2622 node2622Labels = _
    exact sound2622 B hB hF
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm364, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1247, h2622, h2709, h2750, h2751, h4091, reducedSource304] using sourceEq364 B hB

theorem rowSound304 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row304 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck304, numericCheck304, reducedZero304 B hB hF, mul_zero]

theorem reducedZero305 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource305 (mixedVector B) = 0 := by
  have h2470 : mixedVector B (Sum.inr 2470) = Sparse.eval nodeValue2470 (mixedVector B) := by
    change mixedMoment B node2470 node2470Labels = _
    exact sound2470 B hB hF
  have h2473 : mixedVector B (Sum.inr 2473) = Sparse.eval nodeValue2473 (mixedVector B) := by
    change mixedMoment B node2473 node2473Labels = _
    exact sound2473 B hB hF
  have h2480 : mixedVector B (Sum.inr 2480) = Sparse.eval nodeValue2480 (mixedVector B) := by
    change mixedMoment B node2480 node2480Labels = _
    exact sound2480 B hB hF
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm365, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2470, h2473, h2480, h2709, h3800, h4091, reducedSource305] using sourceEq365 B hB

theorem rowSound305 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row305 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck305, numericCheck305, reducedZero305 B hB hF, mul_zero]

theorem reducedZero306 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource306 (mixedVector B) = 0 := by
  have h1213 : mixedVector B (Sum.inr 1213) = Sparse.eval nodeValue1213 (mixedVector B) := by
    change mixedMoment B node1213 node1213Labels = _
    exact sound1213 B hB hF
  have h2480 : mixedVector B (Sum.inr 2480) = Sparse.eval nodeValue2480 (mixedVector B) := by
    change mixedMoment B node2480 node2480Labels = _
    exact sound2480 B hB hF
  have h2615 : mixedVector B (Sum.inr 2615) = Sparse.eval nodeValue2615 (mixedVector B) := by
    change mixedMoment B node2615 node2615Labels = _
    exact sound2615 B hB hF
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm366, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1213, h2480, h2615, h2709, h2721, h2723, h4091, reducedSource306] using sourceEq366 B hB

theorem rowSound306 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row306 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck306, numericCheck306, reducedZero306 B hB hF, mul_zero]

theorem reducedZero307 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource307 (mixedVector B) = 0 := by
  have h2610 : mixedVector B (Sum.inr 2610) = Sparse.eval nodeValue2610 (mixedVector B) := by
    change mixedMoment B node2610 node2610Labels = _
    exact sound2610 B hB hF
  have h2612 : mixedVector B (Sum.inr 2612) = Sparse.eval nodeValue2612 (mixedVector B) := by
    change mixedMoment B node2612 node2612Labels = _
    exact sound2612 B hB hF
  have h2615 : mixedVector B (Sum.inr 2615) = Sparse.eval nodeValue2615 (mixedVector B) := by
    change mixedMoment B node2615 node2615Labels = _
    exact sound2615 B hB hF
  have h2622 : mixedVector B (Sum.inr 2622) = Sparse.eval nodeValue2622 (mixedVector B) := by
    change mixedMoment B node2622 node2622Labels = _
    exact sound2622 B hB hF
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm367, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2610, h2612, h2615, h2622, h2709, h3871, h4091, reducedSource307] using sourceEq367 B hB

theorem rowSound307 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row307 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck307, numericCheck307, reducedZero307 B hB hF, mul_zero]

theorem reducedZero308 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource308 (mixedVector B) = 0 := by
  have h1208 : mixedVector B (Sum.inr 1208) = Sparse.eval nodeValue1208 (mixedVector B) := by
    change mixedMoment B node1208 node1208Labels = _
    exact sound1208 B hB hF
  have h2473 : mixedVector B (Sum.inr 2473) = Sparse.eval nodeValue2473 (mixedVector B) := by
    change mixedMoment B node2473 node2473Labels = _
    exact sound2473 B hB hF
  have h2612 : mixedVector B (Sum.inr 2612) = Sparse.eval nodeValue2612 (mixedVector B) := by
    change mixedMoment B node2612 node2612Labels = _
    exact sound2612 B hB hF
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm368, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1208, h2473, h2612, h2709, h2710, h4091, reducedSource308] using sourceEq368 B hB

theorem rowSound308 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row308 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck308, numericCheck308, reducedZero308 B hB hF, mul_zero]

theorem reducedZero309 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource309 (mixedVector B) = 0 := by
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h4803 : mixedVector B (Sum.inr 4803) = Sparse.eval nodeValue4803 (mixedVector B) := by
    change mixedMoment B node4803 node4803Labels = _
    exact sound4803 B hB hF
  have h4831 : mixedVector B (Sum.inr 4831) = Sparse.eval nodeValue4831 (mixedVector B) := by
    change mixedMoment B node4831 node4831Labels = _
    exact sound4831 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h5219 : mixedVector B (Sum.inr 5219) = Sparse.eval nodeValue5219 (mixedVector B) := by
    change mixedMoment B node5219 node5219Labels = _
    exact sound5219 B hB hF
  have h5220 : mixedVector B (Sum.inr 5220) = Sparse.eval nodeValue5220 (mixedVector B) := by
    change mixedMoment B node5220 node5220Labels = _
    exact sound5220 B hB hF
  have h5223 : mixedVector B (Sum.inr 5223) = Sparse.eval nodeValue5223 (mixedVector B) := by
    change mixedMoment B node5223 node5223Labels = _
    exact sound5223 B hB hF
  have h5241 : mixedVector B (Sum.inr 5241) = Sparse.eval nodeValue5241 (mixedVector B) := by
    change mixedMoment B node5241 node5241Labels = _
    exact sound5241 B hB hF
  have h5242 : mixedVector B (Sum.inr 5242) = Sparse.eval nodeValue5242 (mixedVector B) := by
    change mixedMoment B node5242 node5242Labels = _
    exact sound5242 B hB hF
  have h5244 : mixedVector B (Sum.inr 5244) = Sparse.eval nodeValue5244 (mixedVector B) := by
    change mixedMoment B node5244 node5244Labels = _
    exact sound5244 B hB hF
  have h5249 : mixedVector B (Sum.inr 5249) = Sparse.eval nodeValue5249 (mixedVector B) := by
    change mixedMoment B node5249 node5249Labels = _
    exact sound5249 B hB hF
  have h5251 : mixedVector B (Sum.inr 5251) = Sparse.eval nodeValue5251 (mixedVector B) := by
    change mixedMoment B node5251 node5251Labels = _
    exact sound5251 B hB hF
  have h5253 : mixedVector B (Sum.inr 5253) = Sparse.eval nodeValue5253 (mixedVector B) := by
    change mixedMoment B node5253 node5253Labels = _
    exact sound5253 B hB hF
  have h5254 : mixedVector B (Sum.inr 5254) = Sparse.eval nodeValue5254 (mixedVector B) := by
    change mixedMoment B node5254 node5254Labels = _
    exact sound5254 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5266 : mixedVector B (Sum.inr 5266) = Sparse.eval nodeValue5266 (mixedVector B) := by
    change mixedMoment B node5266 node5266Labels = _
    exact sound5266 B hB hF
  have h5282 : mixedVector B (Sum.inr 5282) = Sparse.eval nodeValue5282 (mixedVector B) := by
    change mixedMoment B node5282 node5282Labels = _
    exact sound5282 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  simpa only [sourceForm369, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4801, h4803, h4831, h4888, h5219, h5220, h5223, h5241, h5242, h5244, h5249, h5251, h5253, h5254, h5258, h5259, h5266, h5282, h5284, h5293, reducedSource309] using sourceEq369 B hB

theorem rowSound309 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row309 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck309, numericCheck309, reducedZero309 B hB hF, mul_zero]

theorem reducedZero312 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource312 (mixedVector B) = 0 := by
  have h3493 : mixedVector B (Sum.inr 3493) = Sparse.eval nodeValue3493 (mixedVector B) := by
    change mixedMoment B node3493 node3493Labels = _
    exact sound3493 B hB hF
  have h3494 : mixedVector B (Sum.inr 3494) = Sparse.eval nodeValue3494 (mixedVector B) := by
    change mixedMoment B node3494 node3494Labels = _
    exact sound3494 B hB hF
  have h3497 : mixedVector B (Sum.inr 3497) = Sparse.eval nodeValue3497 (mixedVector B) := by
    change mixedMoment B node3497 node3497Labels = _
    exact sound3497 B hB hF
  have h3531 : mixedVector B (Sum.inr 3531) = Sparse.eval nodeValue3531 (mixedVector B) := by
    change mixedMoment B node3531 node3531Labels = _
    exact sound3531 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm372, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3493, h3494, h3497, h3531, h3544, h4084, reducedSource312] using sourceEq372 B hB

theorem rowSound312 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row312 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck312, numericCheck312, reducedZero312 B hB hF, mul_zero]

theorem reducedZero313 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource313 (mixedVector B) = 0 := by
  have h2019 : mixedVector B (Sum.inr 2019) = Sparse.eval nodeValue2019 (mixedVector B) := by
    change mixedMoment B node2019 node2019Labels = _
    exact sound2019 B hB hF
  have h2021 : mixedVector B (Sum.inr 2021) = Sparse.eval nodeValue2021 (mixedVector B) := by
    change mixedMoment B node2021 node2021Labels = _
    exact sound2021 B hB hF
  have h2051 : mixedVector B (Sum.inr 2051) = Sparse.eval nodeValue2051 (mixedVector B) := by
    change mixedMoment B node2051 node2051Labels = _
    exact sound2051 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h3531 : mixedVector B (Sum.inr 3531) = Sparse.eval nodeValue3531 (mixedVector B) := by
    change mixedMoment B node3531 node3531Labels = _
    exact sound3531 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm373, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2019, h2021, h2051, h2262, h3531, h4084, reducedSource313] using sourceEq373 B hB

theorem rowSound313 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row313 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck313, numericCheck313, reducedZero313 B hB hF, mul_zero]

theorem reducedZero314 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource314 (mixedVector B) = 0 := by
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h3531 : mixedVector B (Sum.inr 3531) = Sparse.eval nodeValue3531 (mixedVector B) := by
    change mixedMoment B node3531 node3531Labels = _
    exact sound3531 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h3627 : mixedVector B (Sum.inr 3627) = Sparse.eval nodeValue3627 (mixedVector B) := by
    change mixedMoment B node3627 node3627Labels = _
    exact sound3627 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm374, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2262, h3531, h3580, h3625, h3627, h4084, reducedSource314] using sourceEq374 B hB

theorem rowSound314 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row314 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck314, numericCheck314, reducedZero314 B hB hF, mul_zero]

theorem reducedZero315 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource315 (mixedVector B) = 0 := by
  have h3375 : mixedVector B (Sum.inr 3375) = Sparse.eval nodeValue3375 (mixedVector B) := by
    change mixedMoment B node3375 node3375Labels = _
    exact sound3375 B hB hF
  have h3377 : mixedVector B (Sum.inr 3377) = Sparse.eval nodeValue3377 (mixedVector B) := by
    change mixedMoment B node3377 node3377Labels = _
    exact sound3377 B hB hF
  have h3388 : mixedVector B (Sum.inr 3388) = Sparse.eval nodeValue3388 (mixedVector B) := by
    change mixedMoment B node3388 node3388Labels = _
    exact sound3388 B hB hF
  have h3497 : mixedVector B (Sum.inr 3497) = Sparse.eval nodeValue3497 (mixedVector B) := by
    change mixedMoment B node3497 node3497Labels = _
    exact sound3497 B hB hF
  have h3531 : mixedVector B (Sum.inr 3531) = Sparse.eval nodeValue3531 (mixedVector B) := by
    change mixedMoment B node3531 node3531Labels = _
    exact sound3531 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm375, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3375, h3377, h3388, h3497, h3531, h4084, reducedSource315] using sourceEq375 B hB

theorem rowSound315 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row315 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck315, numericCheck315, reducedZero315 B hB hF, mul_zero]

theorem reducedZero316 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource316 (mixedVector B) = 0 := by
  have h2051 : mixedVector B (Sum.inr 2051) = Sparse.eval nodeValue2051 (mixedVector B) := by
    change mixedMoment B node2051 node2051Labels = _
    exact sound2051 B hB hF
  have h3388 : mixedVector B (Sum.inr 3388) = Sparse.eval nodeValue3388 (mixedVector B) := by
    change mixedMoment B node3388 node3388Labels = _
    exact sound3388 B hB hF
  have h3531 : mixedVector B (Sum.inr 3531) = Sparse.eval nodeValue3531 (mixedVector B) := by
    change mixedMoment B node3531 node3531Labels = _
    exact sound3531 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm376, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2051, h3388, h3531, h3539, h3544, h4084, reducedSource316] using sourceEq376 B hB

theorem rowSound316 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row316 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck316, numericCheck316, reducedZero316 B hB hF, mul_zero]

theorem reducedZero317 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource317 (mixedVector B) = 0 := by
  have h3494 : mixedVector B (Sum.inr 3494) = Sparse.eval nodeValue3494 (mixedVector B) := by
    change mixedMoment B node3494 node3494Labels = _
    exact sound3494 B hB hF
  have h3502 : mixedVector B (Sum.inr 3502) = Sparse.eval nodeValue3502 (mixedVector B) := by
    change mixedMoment B node3502 node3502Labels = _
    exact sound3502 B hB hF
  have h3504 : mixedVector B (Sum.inr 3504) = Sparse.eval nodeValue3504 (mixedVector B) := by
    change mixedMoment B node3504 node3504Labels = _
    exact sound3504 B hB hF
  have h3531 : mixedVector B (Sum.inr 3531) = Sparse.eval nodeValue3531 (mixedVector B) := by
    change mixedMoment B node3531 node3531Labels = _
    exact sound3531 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm377, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3494, h3502, h3504, h3531, h3580, h4084, reducedSource317] using sourceEq377 B hB

theorem rowSound317 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row317 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck317, numericCheck317, reducedZero317 B hB hF, mul_zero]

theorem reducedZero318 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource318 (mixedVector B) = 0 := by
  have h2019 : mixedVector B (Sum.inr 2019) = Sparse.eval nodeValue2019 (mixedVector B) := by
    change mixedMoment B node2019 node2019Labels = _
    exact sound2019 B hB hF
  have h3375 : mixedVector B (Sum.inr 3375) = Sparse.eval nodeValue3375 (mixedVector B) := by
    change mixedMoment B node3375 node3375Labels = _
    exact sound3375 B hB hF
  have h3502 : mixedVector B (Sum.inr 3502) = Sparse.eval nodeValue3502 (mixedVector B) := by
    change mixedMoment B node3502 node3502Labels = _
    exact sound3502 B hB hF
  have h3531 : mixedVector B (Sum.inr 3531) = Sparse.eval nodeValue3531 (mixedVector B) := by
    change mixedMoment B node3531 node3531Labels = _
    exact sound3531 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm378, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2019, h3375, h3502, h3531, h3533, h4084, reducedSource318] using sourceEq378 B hB

theorem rowSound318 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row318 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck318, numericCheck318, reducedZero318 B hB hF, mul_zero]

theorem sourceRowsAt304 : MixedData.sourceRows (304 : Fin 2425) =
    MixedData.row304 := by decide +kernel

theorem sourceRowsAt305 : MixedData.sourceRows (305 : Fin 2425) =
    MixedData.row305 := by decide +kernel

theorem sourceRowsAt306 : MixedData.sourceRows (306 : Fin 2425) =
    MixedData.row306 := by decide +kernel

theorem sourceRowsAt307 : MixedData.sourceRows (307 : Fin 2425) =
    MixedData.row307 := by decide +kernel

theorem sourceRowsAt308 : MixedData.sourceRows (308 : Fin 2425) =
    MixedData.row308 := by decide +kernel

theorem sourceRowsAt309 : MixedData.sourceRows (309 : Fin 2425) =
    MixedData.row309 := by decide +kernel

theorem sourceRowsAt310 : MixedData.sourceRows (310 : Fin 2425) =
    MixedData.row310 := by decide +kernel

theorem sourceRowsAt311 : MixedData.sourceRows (311 : Fin 2425) =
    MixedData.row311 := by decide +kernel

theorem sourceRowsAt312 : MixedData.sourceRows (312 : Fin 2425) =
    MixedData.row312 := by decide +kernel

theorem sourceRowsAt313 : MixedData.sourceRows (313 : Fin 2425) =
    MixedData.row313 := by decide +kernel

theorem sourceRowsAt314 : MixedData.sourceRows (314 : Fin 2425) =
    MixedData.row314 := by decide +kernel

theorem sourceRowsAt315 : MixedData.sourceRows (315 : Fin 2425) =
    MixedData.row315 := by decide +kernel

theorem sourceRowsAt316 : MixedData.sourceRows (316 : Fin 2425) =
    MixedData.row316 := by decide +kernel

theorem sourceRowsAt317 : MixedData.sourceRows (317 : Fin 2425) =
    MixedData.row317 := by decide +kernel

theorem sourceRowsAt318 : MixedData.sourceRows (318 : Fin 2425) =
    MixedData.row318 := by decide +kernel

theorem sourceRowsAt319 : MixedData.sourceRows (319 : Fin 2425) =
    MixedData.row319 := by decide +kernel

theorem chunkSound19_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 19) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 304 ∨ k.val = 305 ∨ k.val = 306 ∨ k.val = 307 ∨ k.val = 308 ∨ k.val = 309 ∨ k.val = 310 ∨ k.val = 311 ∨ k.val = 312 ∨ k.val = 313 ∨ k.val = 314 ∨ k.val = 315 ∨ k.val = 316 ∨ k.val = 317 ∨ k.val = 318 ∨ k.val = 319 := by omega
  rcases heq with h304 | h305 | h306 | h307 | h308 | h309 | h310 | h311 | h312 | h313 | h314 | h315 | h316 | h317 | h318 | h319
  · have he : k = (304 : Fin 2425) := Fin.ext h304
    subst k
    rw [sourceRowsAt304]
    exact rowSound304 B hB hF
  · have he : k = (305 : Fin 2425) := Fin.ext h305
    subst k
    rw [sourceRowsAt305]
    exact rowSound305 B hB hF
  · have he : k = (306 : Fin 2425) := Fin.ext h306
    subst k
    rw [sourceRowsAt306]
    exact rowSound306 B hB hF
  · have he : k = (307 : Fin 2425) := Fin.ext h307
    subst k
    rw [sourceRowsAt307]
    exact rowSound307 B hB hF
  · have he : k = (308 : Fin 2425) := Fin.ext h308
    subst k
    rw [sourceRowsAt308]
    exact rowSound308 B hB hF
  · have he : k = (309 : Fin 2425) := Fin.ext h309
    subst k
    rw [sourceRowsAt309]
    exact rowSound309 B hB hF
  · have he : k = (310 : Fin 2425) := Fin.ext h310
    subst k
    rw [sourceRowsAt310]
    exact rowSound310_e B hB hF
  · have he : k = (311 : Fin 2425) := Fin.ext h311
    subst k
    rw [sourceRowsAt311]
    exact rowSound311_e B hB hF
  · have he : k = (312 : Fin 2425) := Fin.ext h312
    subst k
    rw [sourceRowsAt312]
    exact rowSound312 B hB hF
  · have he : k = (313 : Fin 2425) := Fin.ext h313
    subst k
    rw [sourceRowsAt313]
    exact rowSound313 B hB hF
  · have he : k = (314 : Fin 2425) := Fin.ext h314
    subst k
    rw [sourceRowsAt314]
    exact rowSound314 B hB hF
  · have he : k = (315 : Fin 2425) := Fin.ext h315
    subst k
    rw [sourceRowsAt315]
    exact rowSound315 B hB hF
  · have he : k = (316 : Fin 2425) := Fin.ext h316
    subst k
    rw [sourceRowsAt316]
    exact rowSound316 B hB hF
  · have he : k = (317 : Fin 2425) := Fin.ext h317
    subst k
    rw [sourceRowsAt317]
    exact rowSound317 B hB hF
  · have he : k = (318 : Fin 2425) := Fin.ext h318
    subst k
    rw [sourceRowsAt318]
    exact rowSound318 B hB hF
  · have he : k = (319 : Fin 2425) := Fin.ext h319
    subst k
    rw [sourceRowsAt319]
    exact rowSound319_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e_oai
