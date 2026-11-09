-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:49:28.435173+00:00
-- url     : https://prove2.me/submissions/661bcc6f-1fd4-4879-9d91-2b2b7533b841

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E150
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound144_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound151_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound153_e

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

theorem mixedMoment_zero_first_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (hA : ∀ i, A i 0 = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A i j.succ) (fun j => label j.succ) := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  unfold mixedIntegrand
  rw [Fin.prod_univ_succ]
  have hz : (fun i => A i 0) = 0 := funext hA
  rw [hz, rowFourier_zero, one_mul]

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

theorem pattern2_0 {B : Type*} (f : Fin 2 → B)
    (h10 : f 1 = f 0)
    : ∀ i j, family2.label 0 i = family2.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family2, label2, raw2, blocks2, eq_comm]

theorem pattern2_1 {B : Type*} (f : Fin 2 → B)
    (h10 : f 1 ≠ f 0)
    : ∀ i j, family2.label 1 i = family2.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family2, label2, raw2, blocks2, eq_comm]

theorem covers2 {B : Type*} (f : Fin 2 → B) :
    ∃ p, ∀ i j, (family2.label p i = family2.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    refine ⟨0, ?_⟩
    apply pattern2_0 f; simp_all [eq_comm]
  ·
    refine ⟨1, ?_⟩
    apply pattern2_1 f; simp_all [eq_comm]

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

theorem delete_zero_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (σ : Equiv.Perm (Fin (n + 1))) (hz : ∀ i, A i (σ 0) = 0) :
    mixedMoment B A label =
      mixedMoment B (fun i j => A i (σ j.succ)) (fun j => label (σ j.succ)) := by
  rw [← mixedMoment_factor_permutation B A label σ]
  exact mixedMoment_zero_first_factor B _ _ hz

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1280 raw1280Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw1280 raw1280Labels = mixedMoment B raw1280step0 raw1280step0Labels := by
      have ha : raw1280step0 = (fun i j => raw1280 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1280step0 raw1280; decide +kernel
      have hl : raw1280step0Labels = raw1280Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1280 raw1280Labels permutation2 permutation6
    mixedMoment B raw1280step0 raw1280step0Labels = mixedMoment B raw1280step1 raw1280step1Labels := by
      have ha : raw1280step1 = -raw1280step0 := by apply Matrix.ext; change ∀ i j, raw1280step1 i j = -(raw1280step0 i j); unfold raw1280step1 raw1280step0; decide +kernel
      have hl : raw1280step1Labels = raw1280step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1280step1 raw1280step1Labels = mixedMoment B raw1280step2 raw1280step2Labels := by
      have ha : raw1280step2 = raw1280step1 := by apply Matrix.ext; unfold raw1280step2 raw1280step1; decide +kernel
      have hl : raw1280step1Labels = labelEmbedding1 ∘ raw1280step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1280step1 raw1280step1Labels raw1280step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1752 node1752Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1428 raw1428Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw1428 raw1428Labels = mixedMoment B raw1428step0 raw1428step0Labels := by
      have ha : raw1428step0 = (fun i j => raw1428 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1428step0 raw1428; decide +kernel
      have hl : raw1428step0Labels = raw1428Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1428 raw1428Labels permutation8 permutation4
    mixedMoment B raw1428step0 raw1428step0Labels = mixedMoment B raw1428step1 raw1428step1Labels := by
      have ha : raw1428step1 = raw1428step0 := by apply Matrix.ext; unfold raw1428step1 raw1428step0; decide +kernel
      have hl : raw1428step0Labels = labelEmbedding7 ∘ raw1428step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1428step0 raw1428step0Labels raw1428step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical1429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1429 raw1429Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw1429 raw1429Labels = mixedMoment B raw1429step0 raw1429step0Labels := by
      have ha : raw1429step0 = (fun i j => raw1429 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1429step0 raw1429; decide +kernel
      have hl : raw1429step0Labels = raw1429Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1429 raw1429Labels permutation8 permutation4
    _ = mixedMoment B node1239 node1239Labels := by rfl

theorem canonical1430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1430 raw1430Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw1430 raw1430Labels = mixedMoment B raw1430step0 raw1430step0Labels := by
      have ha : raw1430step0 = (fun i j => raw1430 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1430step0 raw1430; decide +kernel
      have hl : raw1430step0Labels = raw1430Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1430 raw1430Labels permutation31 permutation6
    mixedMoment B raw1430step0 raw1430step0Labels = mixedMoment B raw1430step1 raw1430step1Labels := by
      have ha : raw1430step1 = raw1430step0 := by apply Matrix.ext; unfold raw1430step1 raw1430step0; decide +kernel
      have hl : raw1430step0Labels = labelEmbedding1 ∘ raw1430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1430step0 raw1430step0Labels raw1430step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical1446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1446 raw1446Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw1446 raw1446Labels = mixedMoment B raw1446step0 raw1446step0Labels := by
      have ha : raw1446step0 = (fun i j => raw1446 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1446step0 raw1446; decide +kernel
      have hl : raw1446step0Labels = raw1446Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1446 raw1446Labels permutation2 permutation4
    mixedMoment B raw1446step0 raw1446step0Labels = mixedMoment B raw1446step1 raw1446step1Labels := by
      have ha : raw1446step1 = raw1446step0 := by apply Matrix.ext; unfold raw1446step1 raw1446step0; decide +kernel
      have hl : raw1446step0Labels = labelEmbedding7 ∘ raw1446step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1446step0 raw1446step0Labels raw1446step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4621 node4621Labels := by rfl

theorem canonical1447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1447 raw1447Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw1447 raw1447Labels = mixedMoment B raw1447step0 raw1447step0Labels := by
      have ha : raw1447step0 = (fun i j => raw1447 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1447step0 raw1447; decide +kernel
      have hl : raw1447step0Labels = raw1447Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1447 raw1447Labels permutation2 permutation4
    _ = mixedMoment B node1297 node1297Labels := by rfl

theorem canonical1448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1448 raw1448Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw1448 raw1448Labels = mixedMoment B raw1448step0 raw1448step0Labels := by
      have ha : raw1448step0 = (fun i j => raw1448 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1448step0 raw1448; decide +kernel
      have hl : raw1448step0Labels = raw1448Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1448 raw1448Labels permutation7 permutation6
    mixedMoment B raw1448step0 raw1448step0Labels = mixedMoment B raw1448step1 raw1448step1Labels := by
      have ha : raw1448step1 = raw1448step0 := by apply Matrix.ext; unfold raw1448step1 raw1448step0; decide +kernel
      have hl : raw1448step0Labels = labelEmbedding1 ∘ raw1448step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1448step0 raw1448step0Labels raw1448step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2289 node2289Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1737 raw1737Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw1737 raw1737Labels = mixedMoment B raw1737step0 raw1737step0Labels := by
      have ha : raw1737step0 = (fun i j => raw1737 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1737step0 raw1737; decide +kernel
      have hl : raw1737step0Labels = raw1737Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1737 raw1737Labels permutation32 permutation4
    mixedMoment B raw1737step0 raw1737step0Labels = mixedMoment B raw1737step1 raw1737step1Labels := by
      have ha : raw1737step1 = raw1737step0 := by apply Matrix.ext; unfold raw1737step1 raw1737step0; decide +kernel
      have hl : raw1737step0Labels = labelEmbedding7 ∘ raw1737step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1737step0 raw1737step0Labels raw1737step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical1738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1738 raw1738Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw1738 raw1738Labels = mixedMoment B raw1738step0 raw1738step0Labels := by
      have ha : raw1738step0 = (fun i j => raw1738 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1738step0 raw1738; decide +kernel
      have hl : raw1738step0Labels = raw1738Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1738 raw1738Labels permutation32 permutation4
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1739 raw1739Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw1739 raw1739Labels = mixedMoment B raw1739step0 raw1739step0Labels := by
      have ha : raw1739step0 = (fun i j => raw1739 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1739step0 raw1739; decide +kernel
      have hl : raw1739step0Labels = raw1739Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1739 raw1739Labels permutation34 permutation6
    mixedMoment B raw1739step0 raw1739step0Labels = mixedMoment B raw1739step1 raw1739step1Labels := by
      have ha : raw1739step1 = -raw1739step0 := by apply Matrix.ext; change ∀ i j, raw1739step1 i j = -(raw1739step0 i j); unfold raw1739step1 raw1739step0; decide +kernel
      have hl : raw1739step1Labels = raw1739step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1739step1 raw1739step1Labels = mixedMoment B raw1739step2 raw1739step2Labels := by
      have ha : raw1739step2 = raw1739step1 := by apply Matrix.ext; unfold raw1739step2 raw1739step1; decide +kernel
      have hl : raw1739step1Labels = labelEmbedding1 ∘ raw1739step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1739step1 raw1739step1Labels raw1739step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

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

theorem canonical1797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1797 raw1797Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw1797 raw1797Labels = mixedMoment B raw1797step0 raw1797step0Labels := by
      have ha : raw1797step0 = (fun i j => raw1797 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1797step0 raw1797; decide +kernel
      have hl : raw1797step0Labels = raw1797Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1797 raw1797Labels permutation8 permutation4
    mixedMoment B raw1797step0 raw1797step0Labels = mixedMoment B raw1797step1 raw1797step1Labels := by
      have ha : raw1797step1 = raw1797step0 := by apply Matrix.ext; unfold raw1797step1 raw1797step0; decide +kernel
      have hl : raw1797step0Labels = labelEmbedding7 ∘ raw1797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1797step0 raw1797step0Labels raw1797step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical1798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1798 raw1798Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw1798 raw1798Labels = mixedMoment B raw1798step0 raw1798step0Labels := by
      have ha : raw1798step0 = (fun i j => raw1798 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1798step0 raw1798; decide +kernel
      have hl : raw1798step0Labels = raw1798Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1798 raw1798Labels permutation8 permutation4
    _ = mixedMoment B node2109 node2109Labels := by rfl

theorem canonical1799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1799 raw1799Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw1799 raw1799Labels = mixedMoment B raw1799step0 raw1799step0Labels := by
      have ha : raw1799step0 = (fun i j => raw1799 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1799step0 raw1799; decide +kernel
      have hl : raw1799step0Labels = raw1799Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1799 raw1799Labels permutation10 permutation6
    mixedMoment B raw1799step0 raw1799step0Labels = mixedMoment B raw1799step1 raw1799step1Labels := by
      have ha : raw1799step1 = -raw1799step0 := by apply Matrix.ext; change ∀ i j, raw1799step1 i j = -(raw1799step0 i j); unfold raw1799step1 raw1799step0; decide +kernel
      have hl : raw1799step1Labels = raw1799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1799step1 raw1799step1Labels = mixedMoment B raw1799step2 raw1799step2Labels := by
      have ha : raw1799step2 = raw1799step1 := by apply Matrix.ext; unfold raw1799step2 raw1799step1; decide +kernel
      have hl : raw1799step1Labels = labelEmbedding1 ∘ raw1799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1799step1 raw1799step1Labels raw1799step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

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

theorem canonical2283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2283 raw2283Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw2283 raw2283Labels = mixedMoment B raw2283step0 raw2283step0Labels := by
      have ha : raw2283step0 = (fun i j => raw2283 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2283step0 raw2283; decide +kernel
      have hl : raw2283step0Labels = raw2283Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2283 raw2283Labels permutation8 permutation4
    mixedMoment B raw2283step0 raw2283step0Labels = mixedMoment B raw2283step1 raw2283step1Labels := by
      have ha : raw2283step1 = raw2283step0 := by apply Matrix.ext; unfold raw2283step1 raw2283step0; decide +kernel
      have hl : raw2283step0Labels = labelEmbedding7 ∘ raw2283step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2283step0 raw2283step0Labels raw2283step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5272 node5272Labels := by rfl

theorem canonical2284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2284 raw2284Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw2284 raw2284Labels = mixedMoment B raw2284step0 raw2284step0Labels := by
      have ha : raw2284step0 = (fun i j => raw2284 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2284step0 raw2284; decide +kernel
      have hl : raw2284step0Labels = raw2284Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2284 raw2284Labels permutation8 permutation4
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical2285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2285 raw2285Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw2285 raw2285Labels = mixedMoment B raw2285step0 raw2285step0Labels := by
      have ha : raw2285step0 = (fun i j => raw2285 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2285step0 raw2285; decide +kernel
      have hl : raw2285step0Labels = raw2285Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2285 raw2285Labels permutation31 permutation6
    mixedMoment B raw2285step0 raw2285step0Labels = mixedMoment B raw2285step1 raw2285step1Labels := by
      have ha : raw2285step1 = raw2285step0 := by apply Matrix.ext; unfold raw2285step1 raw2285step0; decide +kernel
      have hl : raw2285step0Labels = labelEmbedding1 ∘ raw2285step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2285step0 raw2285step0Labels raw2285step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

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

theorem canonical2319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2319 raw2319Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw2319 raw2319Labels = mixedMoment B raw2319step0 raw2319step0Labels := by
      have ha : raw2319step0 = (fun i j => raw2319 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2319step0 raw2319; decide +kernel
      have hl : raw2319step0Labels = raw2319Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2319 raw2319Labels permutation2 permutation4
    mixedMoment B raw2319step0 raw2319step0Labels = mixedMoment B raw2319step1 raw2319step1Labels := by
      have ha : raw2319step1 = raw2319step0 := by apply Matrix.ext; unfold raw2319step1 raw2319step0; decide +kernel
      have hl : raw2319step0Labels = labelEmbedding7 ∘ raw2319step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2319step0 raw2319step0Labels raw2319step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5305 node5305Labels := by rfl

theorem canonical2320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2320 raw2320Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw2320 raw2320Labels = mixedMoment B raw2320step0 raw2320step0Labels := by
      have ha : raw2320step0 = (fun i j => raw2320 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2320step0 raw2320; decide +kernel
      have hl : raw2320step0Labels = raw2320Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2320 raw2320Labels permutation2 permutation4
    _ = mixedMoment B node2783 node2783Labels := by rfl

theorem canonical2321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2321 raw2321Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw2321 raw2321Labels = mixedMoment B raw2321step0 raw2321step0Labels := by
      have ha : raw2321step0 = (fun i j => raw2321 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2321step0 raw2321; decide +kernel
      have hl : raw2321step0Labels = raw2321Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2321 raw2321Labels permutation7 permutation6
    mixedMoment B raw2321step0 raw2321step0Labels = mixedMoment B raw2321step1 raw2321step1Labels := by
      have ha : raw2321step1 = raw2321step0 := by apply Matrix.ext; unfold raw2321step1 raw2321step0; decide +kernel
      have hl : raw2321step0Labels = labelEmbedding1 ∘ raw2321step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2321step0 raw2321step0Labels raw2321step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2783 node2783Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2914 raw2914Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2914 raw2914Labels = mixedMoment B raw2914step0 raw2914step0Labels := by
      have hz : ∀ j, raw2914 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2914step0 = (fun i j => raw2914 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2914step0 raw2914; decide +kernel
      have hl : raw2914step0Labels = raw2914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2914 raw2914Labels permutation520 hz
    mixedMoment B raw2914step0 raw2914step0Labels = mixedMoment B raw2914step1 raw2914step1Labels := by
      have hz : ∀ j, raw2914step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2914step1 = (fun i j => raw2914step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2914step1 raw2914step0; decide +kernel
      have hl : raw2914step1Labels = raw2914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2914step0 raw2914step0Labels permutation104 hz
    mixedMoment B raw2914step1 raw2914step1Labels = mixedMoment B raw2914step2 raw2914step2Labels := by
      have hz : ∀ j, raw2914step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2914step2 = (fun i j => raw2914step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2914step2 raw2914step1; decide +kernel
      have hl : raw2914step2Labels = raw2914step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2914step1 raw2914step1Labels permutation20 hz
    mixedMoment B raw2914step2 raw2914step2Labels = mixedMoment B raw2914step3 raw2914step3Labels := by
      have hz : ∀ i, raw2914step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2914step3 = (fun i j => raw2914step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2914step3 raw2914step2; decide +kernel
      have hl : raw2914step3Labels = (fun j => raw2914step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2914step2 raw2914step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2919 raw2919Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2919 raw2919Labels = mixedMoment B raw2919step0 raw2919step0Labels := by
      have hz : ∀ j, raw2919 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2919step0 = (fun i j => raw2919 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2919step0 raw2919; decide +kernel
      have hl : raw2919step0Labels = raw2919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2919 raw2919Labels permutation520 hz
    mixedMoment B raw2919step0 raw2919step0Labels = mixedMoment B raw2919step1 raw2919step1Labels := by
      have hz : ∀ j, raw2919step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2919step1 = (fun i j => raw2919step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2919step1 raw2919step0; decide +kernel
      have hl : raw2919step1Labels = raw2919step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2919step0 raw2919step0Labels permutation104 hz
    mixedMoment B raw2919step1 raw2919step1Labels = mixedMoment B raw2919step2 raw2919step2Labels := by
      have hz : ∀ j, raw2919step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2919step2 = (fun i j => raw2919step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2919step2 raw2919step1; decide +kernel
      have hl : raw2919step2Labels = raw2919step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2919step1 raw2919step1Labels permutation14 hz
    mixedMoment B raw2919step2 raw2919step2Labels = mixedMoment B raw2919step3 raw2919step3Labels := by
      have hz : ∀ i, raw2919step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2919step3 = (fun i j => raw2919step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2919step3 raw2919step2; decide +kernel
      have hl : raw2919step3Labels = (fun j => raw2919step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2919step2 raw2919step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2924 raw2924Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2924 raw2924Labels = mixedMoment B raw2924step0 raw2924step0Labels := by
      have hz : ∀ j, raw2924 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2924step0 = (fun i j => raw2924 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2924step0 raw2924; decide +kernel
      have hl : raw2924step0Labels = raw2924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924 raw2924Labels permutation520 hz
    mixedMoment B raw2924step0 raw2924step0Labels = mixedMoment B raw2924step1 raw2924step1Labels := by
      have hz : ∀ j, raw2924step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2924step1 = (fun i j => raw2924step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2924step1 raw2924step0; decide +kernel
      have hl : raw2924step1Labels = raw2924step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924step0 raw2924step0Labels permutation80 hz
    mixedMoment B raw2924step1 raw2924step1Labels = mixedMoment B raw2924step2 raw2924step2Labels := by
      have hz : ∀ j, raw2924step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2924step2 = (fun i j => raw2924step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2924step2 raw2924step1; decide +kernel
      have hl : raw2924step2Labels = raw2924step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924step1 raw2924step1Labels permutation14 hz
    mixedMoment B raw2924step2 raw2924step2Labels = mixedMoment B raw2924step3 raw2924step3Labels := by
      have hz : ∀ i, raw2924step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2924step3 = (fun i j => raw2924step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2924step3 raw2924step2; decide +kernel
      have hl : raw2924step3Labels = (fun j => raw2924step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2924step2 raw2924step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2929 raw2929Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2929 raw2929Labels = mixedMoment B raw2929step0 raw2929step0Labels := by
      have hz : ∀ j, raw2929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2929step0 = (fun i j => raw2929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2929step0 raw2929; decide +kernel
      have hl : raw2929step0Labels = raw2929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929 raw2929Labels permutation434 hz
    mixedMoment B raw2929step0 raw2929step0Labels = mixedMoment B raw2929step1 raw2929step1Labels := by
      have hz : ∀ j, raw2929step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2929step1 = (fun i j => raw2929step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2929step1 raw2929step0; decide +kernel
      have hl : raw2929step1Labels = raw2929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929step0 raw2929step0Labels permutation80 hz
    mixedMoment B raw2929step1 raw2929step1Labels = mixedMoment B raw2929step2 raw2929step2Labels := by
      have hz : ∀ j, raw2929step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2929step2 = (fun i j => raw2929step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2929step2 raw2929step1; decide +kernel
      have hl : raw2929step2Labels = raw2929step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929step1 raw2929step1Labels permutation14 hz
    mixedMoment B raw2929step2 raw2929step2Labels = mixedMoment B raw2929step3 raw2929step3Labels := by
      have hz : ∀ i, raw2929step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2929step3 = (fun i j => raw2929step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2929step3 raw2929step2; decide +kernel
      have hl : raw2929step3Labels = (fun j => raw2929step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2929step2 raw2929step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2935 raw2935Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2935 raw2935Labels = mixedMoment B raw2935step0 raw2935step0Labels := by
      have hz : ∀ j, raw2935 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2935step0 = (fun i j => raw2935 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2935step0 raw2935; decide +kernel
      have hl : raw2935step0Labels = raw2935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2935 raw2935Labels permutation520 hz
    mixedMoment B raw2935step0 raw2935step0Labels = mixedMoment B raw2935step1 raw2935step1Labels := by
      have hz : ∀ j, raw2935step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2935step1 = (fun i j => raw2935step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2935step1 raw2935step0; decide +kernel
      have hl : raw2935step1Labels = raw2935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2935step0 raw2935step0Labels permutation104 hz
    mixedMoment B raw2935step1 raw2935step1Labels = mixedMoment B raw2935step2 raw2935step2Labels := by
      have hz : ∀ j, raw2935step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2935step2 = (fun i j => raw2935step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2935step2 raw2935step1; decide +kernel
      have hl : raw2935step2Labels = raw2935step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2935step1 raw2935step1Labels permutation20 hz
    mixedMoment B raw2935step2 raw2935step2Labels = mixedMoment B raw2935step3 raw2935step3Labels := by
      have hz : ∀ i, raw2935step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2935step3 = (fun i j => raw2935step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2935step3 raw2935step2; decide +kernel
      have hl : raw2935step3Labels = (fun j => raw2935step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2935step2 raw2935step2Labels permutation6 hz
    mixedMoment B raw2935step3 raw2935step3Labels = mixedMoment B raw2935step4 raw2935step4Labels := by
      have ha : raw2935step4 = (fun i j => raw2935step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2935step4 raw2935step3; decide +kernel
      have hl : raw2935step4Labels = raw2935step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2935step3 raw2935step3Labels permutation7 permutation0
    mixedMoment B raw2935step4 raw2935step4Labels = mixedMoment B raw2935step5 raw2935step5Labels := by
      have ha : raw2935step5 = -raw2935step4 := by apply Matrix.ext; change ∀ i j, raw2935step5 i j = -(raw2935step4 i j); unfold raw2935step5 raw2935step4; decide +kernel
      have hl : raw2935step5Labels = raw2935step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2936 raw2936Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2936 raw2936Labels = mixedMoment B raw2936step0 raw2936step0Labels := by
      have hz : ∀ j, raw2936 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2936step0 = (fun i j => raw2936 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2936step0 raw2936; decide +kernel
      have hl : raw2936step0Labels = raw2936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2936 raw2936Labels permutation520 hz
    mixedMoment B raw2936step0 raw2936step0Labels = mixedMoment B raw2936step1 raw2936step1Labels := by
      have hz : ∀ j, raw2936step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2936step1 = (fun i j => raw2936step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2936step1 raw2936step0; decide +kernel
      have hl : raw2936step1Labels = raw2936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2936step0 raw2936step0Labels permutation104 hz
    mixedMoment B raw2936step1 raw2936step1Labels = mixedMoment B raw2936step2 raw2936step2Labels := by
      have hz : ∀ j, raw2936step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2936step2 = (fun i j => raw2936step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2936step2 raw2936step1; decide +kernel
      have hl : raw2936step2Labels = raw2936step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2936step1 raw2936step1Labels permutation14 hz
    mixedMoment B raw2936step2 raw2936step2Labels = mixedMoment B raw2936step3 raw2936step3Labels := by
      have hz : ∀ i, raw2936step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2936step3 = (fun i j => raw2936step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2936step3 raw2936step2; decide +kernel
      have hl : raw2936step3Labels = (fun j => raw2936step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2936step2 raw2936step2Labels permutation6 hz
    mixedMoment B raw2936step3 raw2936step3Labels = mixedMoment B raw2936step4 raw2936step4Labels := by
      have ha : raw2936step4 = (fun i j => raw2936step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2936step4 raw2936step3; decide +kernel
      have hl : raw2936step4Labels = raw2936step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2936step3 raw2936step3Labels permutation7 permutation0
    mixedMoment B raw2936step4 raw2936step4Labels = mixedMoment B raw2936step5 raw2936step5Labels := by
      have ha : raw2936step5 = -raw2936step4 := by apply Matrix.ext; change ∀ i j, raw2936step5 i j = -(raw2936step4 i j); unfold raw2936step5 raw2936step4; decide +kernel
      have hl : raw2936step5Labels = raw2936step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2937 raw2937Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2937 raw2937Labels = mixedMoment B raw2937step0 raw2937step0Labels := by
      have hz : ∀ j, raw2937 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2937step0 = (fun i j => raw2937 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2937step0 raw2937; decide +kernel
      have hl : raw2937step0Labels = raw2937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2937 raw2937Labels permutation520 hz
    mixedMoment B raw2937step0 raw2937step0Labels = mixedMoment B raw2937step1 raw2937step1Labels := by
      have hz : ∀ j, raw2937step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2937step1 = (fun i j => raw2937step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2937step1 raw2937step0; decide +kernel
      have hl : raw2937step1Labels = raw2937step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2937step0 raw2937step0Labels permutation80 hz
    mixedMoment B raw2937step1 raw2937step1Labels = mixedMoment B raw2937step2 raw2937step2Labels := by
      have hz : ∀ j, raw2937step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2937step2 = (fun i j => raw2937step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2937step2 raw2937step1; decide +kernel
      have hl : raw2937step2Labels = raw2937step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2937step1 raw2937step1Labels permutation14 hz
    mixedMoment B raw2937step2 raw2937step2Labels = mixedMoment B raw2937step3 raw2937step3Labels := by
      have hz : ∀ i, raw2937step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2937step3 = (fun i j => raw2937step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2937step3 raw2937step2; decide +kernel
      have hl : raw2937step3Labels = (fun j => raw2937step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2937step2 raw2937step2Labels permutation6 hz
    mixedMoment B raw2937step3 raw2937step3Labels = mixedMoment B raw2937step4 raw2937step4Labels := by
      have ha : raw2937step4 = (fun i j => raw2937step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2937step4 raw2937step3; decide +kernel
      have hl : raw2937step4Labels = raw2937step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2937step3 raw2937step3Labels permutation7 permutation0
    mixedMoment B raw2937step4 raw2937step4Labels = mixedMoment B raw2937step5 raw2937step5Labels := by
      have ha : raw2937step5 = -raw2937step4 := by apply Matrix.ext; change ∀ i j, raw2937step5 i j = -(raw2937step4 i j); unfold raw2937step5 raw2937step4; decide +kernel
      have hl : raw2937step5Labels = raw2937step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2938 raw2938Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2938 raw2938Labels = mixedMoment B raw2938step0 raw2938step0Labels := by
      have hz : ∀ j, raw2938 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2938step0 = (fun i j => raw2938 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2938step0 raw2938; decide +kernel
      have hl : raw2938step0Labels = raw2938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2938 raw2938Labels permutation434 hz
    mixedMoment B raw2938step0 raw2938step0Labels = mixedMoment B raw2938step1 raw2938step1Labels := by
      have hz : ∀ j, raw2938step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2938step1 = (fun i j => raw2938step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2938step1 raw2938step0; decide +kernel
      have hl : raw2938step1Labels = raw2938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2938step0 raw2938step0Labels permutation80 hz
    mixedMoment B raw2938step1 raw2938step1Labels = mixedMoment B raw2938step2 raw2938step2Labels := by
      have hz : ∀ j, raw2938step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2938step2 = (fun i j => raw2938step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2938step2 raw2938step1; decide +kernel
      have hl : raw2938step2Labels = raw2938step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2938step1 raw2938step1Labels permutation14 hz
    mixedMoment B raw2938step2 raw2938step2Labels = mixedMoment B raw2938step3 raw2938step3Labels := by
      have hz : ∀ i, raw2938step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2938step3 = (fun i j => raw2938step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2938step3 raw2938step2; decide +kernel
      have hl : raw2938step3Labels = (fun j => raw2938step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2938step2 raw2938step2Labels permutation6 hz
    mixedMoment B raw2938step3 raw2938step3Labels = mixedMoment B raw2938step4 raw2938step4Labels := by
      have ha : raw2938step4 = (fun i j => raw2938step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2938step4 raw2938step3; decide +kernel
      have hl : raw2938step4Labels = raw2938step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2938step3 raw2938step3Labels permutation7 permutation0
    mixedMoment B raw2938step4 raw2938step4Labels = mixedMoment B raw2938step5 raw2938step5Labels := by
      have ha : raw2938step5 = -raw2938step4 := by apply Matrix.ext; change ∀ i j, raw2938step5 i j = -(raw2938step4 i j); unfold raw2938step5 raw2938step4; decide +kernel
      have hl : raw2938step5Labels = raw2938step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3340 raw3340Labels = mixedMoment B node4094 node4094Labels := by
  calc
    mixedMoment B raw3340 raw3340Labels = mixedMoment B raw3340step0 raw3340step0Labels := by
      have hz : ∀ j, raw3340 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3340step0 = (fun i j => raw3340 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3340step0 raw3340; decide +kernel
      have hl : raw3340step0Labels = raw3340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3340 raw3340Labels permutation520 hz
    mixedMoment B raw3340step0 raw3340step0Labels = mixedMoment B raw3340step1 raw3340step1Labels := by
      have hz : ∀ j, raw3340step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3340step1 = (fun i j => raw3340step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3340step1 raw3340step0; decide +kernel
      have hl : raw3340step1Labels = raw3340step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3340step0 raw3340step0Labels permutation104 hz
    mixedMoment B raw3340step1 raw3340step1Labels = mixedMoment B raw3340step2 raw3340step2Labels := by
      have hz : ∀ j, raw3340step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3340step2 = (fun i j => raw3340step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3340step2 raw3340step1; decide +kernel
      have hl : raw3340step2Labels = raw3340step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3340step1 raw3340step1Labels permutation20 hz
    mixedMoment B raw3340step2 raw3340step2Labels = mixedMoment B raw3340step3 raw3340step3Labels := by
      have hz : ∀ j, raw3340step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3340step3 = (fun i j => raw3340step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3340step3 raw3340step2; decide +kernel
      have hl : raw3340step3Labels = raw3340step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3340step2 raw3340step2Labels permutation4 hz
    mixedMoment B raw3340step3 raw3340step3Labels = mixedMoment B raw3340step4 raw3340step4Labels := by
      have hz : ∀ i, raw3340step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3340step4 = (fun i j => raw3340step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3340step4 raw3340step3; decide +kernel
      have hl : raw3340step4Labels = (fun j => raw3340step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3340step3 raw3340step3Labels permutation6 hz
    _ = mixedMoment B node4094 node4094Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5101 raw5101Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw5101 raw5101Labels = mixedMoment B raw5101step0 raw5101step0Labels := by
      have hz : ∀ j, raw5101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5101step0 = (fun i j => raw5101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5101step0 raw5101; decide +kernel
      have hl : raw5101step0Labels = raw5101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5101 raw5101Labels permutation434 hz
    mixedMoment B raw5101step0 raw5101step0Labels = mixedMoment B raw5101step1 raw5101step1Labels := by
      have hz : ∀ j, raw5101step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5101step1 = (fun i j => raw5101step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5101step1 raw5101step0; decide +kernel
      have hl : raw5101step1Labels = raw5101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5101step0 raw5101step0Labels permutation80 hz
    mixedMoment B raw5101step1 raw5101step1Labels = mixedMoment B raw5101step2 raw5101step2Labels := by
      have ha : raw5101step2 = (fun i j => raw5101step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5101step2 raw5101step1; decide +kernel
      have hl : raw5101step2Labels = raw5101step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5101step1 raw5101step1Labels permutation31 permutation2
    mixedMoment B raw5101step2 raw5101step2Labels = mixedMoment B raw5101step3 raw5101step3Labels := by
      have ha : raw5101step3 = -raw5101step2 := by apply Matrix.ext; change ∀ i j, raw5101step3 i j = -(raw5101step2 i j); unfold raw5101step3 raw5101step2; decide +kernel
      have hl : raw5101step3Labels = raw5101step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4894 node4894Labels := by rfl

theorem canonical5102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5102 raw5102Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw5102 raw5102Labels = mixedMoment B raw5102step0 raw5102step0Labels := by
      have hz : ∀ j, raw5102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5102step0 = (fun i j => raw5102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5102step0 raw5102; decide +kernel
      have hl : raw5102step0Labels = raw5102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5102 raw5102Labels permutation434 hz
    mixedMoment B raw5102step0 raw5102step0Labels = mixedMoment B raw5102step1 raw5102step1Labels := by
      have hz : ∀ j, raw5102step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5102step1 = (fun i j => raw5102step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5102step1 raw5102step0; decide +kernel
      have hl : raw5102step1Labels = raw5102step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5102step0 raw5102step0Labels permutation56 hz
    mixedMoment B raw5102step1 raw5102step1Labels = mixedMoment B raw5102step2 raw5102step2Labels := by
      have ha : raw5102step2 = (fun i j => raw5102step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5102step2 raw5102step1; decide +kernel
      have hl : raw5102step2Labels = raw5102step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5102step1 raw5102step1Labels permutation31 permutation2
    mixedMoment B raw5102step2 raw5102step2Labels = mixedMoment B raw5102step3 raw5102step3Labels := by
      have ha : raw5102step3 = -raw5102step2 := by apply Matrix.ext; change ∀ i j, raw5102step3 i j = -(raw5102step2 i j); unfold raw5102step3 raw5102step2; decide +kernel
      have hl : raw5102step3Labels = raw5102step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4894 node4894Labels := by rfl

theorem canonical5103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5103 raw5103Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw5103 raw5103Labels = mixedMoment B raw5103step0 raw5103step0Labels := by
      have hz : ∀ j, raw5103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5103step0 = (fun i j => raw5103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5103step0 raw5103; decide +kernel
      have hl : raw5103step0Labels = raw5103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5103 raw5103Labels permutation346 hz
    mixedMoment B raw5103step0 raw5103step0Labels = mixedMoment B raw5103step1 raw5103step1Labels := by
      have hz : ∀ j, raw5103step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5103step1 = (fun i j => raw5103step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5103step1 raw5103step0; decide +kernel
      have hl : raw5103step1Labels = raw5103step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5103step0 raw5103step0Labels permutation56 hz
    mixedMoment B raw5103step1 raw5103step1Labels = mixedMoment B raw5103step2 raw5103step2Labels := by
      have ha : raw5103step2 = (fun i j => raw5103step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5103step2 raw5103step1; decide +kernel
      have hl : raw5103step2Labels = raw5103step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5103step1 raw5103step1Labels permutation31 permutation2
    mixedMoment B raw5103step2 raw5103step2Labels = mixedMoment B raw5103step3 raw5103step3Labels := by
      have ha : raw5103step3 = -raw5103step2 := by apply Matrix.ext; change ∀ i j, raw5103step3 i j = -(raw5103step2 i j); unfold raw5103step3 raw5103step2; decide +kernel
      have hl : raw5103step3Labels = raw5103step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4894 node4894Labels := by rfl

theorem canonical5104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5104 raw5104Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5104 raw5104Labels = mixedMoment B raw5104step0 raw5104step0Labels := by
      have hz : ∀ j, raw5104 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5104step0 = (fun i j => raw5104 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5104step0 raw5104; decide +kernel
      have hl : raw5104step0Labels = raw5104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5104 raw5104Labels permutation434 hz
    mixedMoment B raw5104step0 raw5104step0Labels = mixedMoment B raw5104step1 raw5104step1Labels := by
      have hz : ∀ j, raw5104step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5104step1 = (fun i j => raw5104step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5104step1 raw5104step0; decide +kernel
      have hl : raw5104step1Labels = raw5104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5104step0 raw5104step0Labels permutation80 hz
    mixedMoment B raw5104step1 raw5104step1Labels = mixedMoment B raw5104step2 raw5104step2Labels := by
      have hz : ∀ j, raw5104step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5104step2 = (fun i j => raw5104step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5104step2 raw5104step1; decide +kernel
      have hl : raw5104step2Labels = raw5104step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5104step1 raw5104step1Labels permutation14 hz
    mixedMoment B raw5104step2 raw5104step2Labels = mixedMoment B raw5104step3 raw5104step3Labels := by
      have hz : ∀ i, raw5104step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw5104step3 = (fun i j => raw5104step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw5104step3 raw5104step2; decide +kernel
      have hl : raw5104step3Labels = (fun j => raw5104step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5104step2 raw5104step2Labels permutation4 hz
    mixedMoment B raw5104step3 raw5104step3Labels = mixedMoment B raw5104step4 raw5104step4Labels := by
      have ha : raw5104step4 = (fun i j => raw5104step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5104step4 raw5104step3; decide +kernel
      have hl : raw5104step4Labels = raw5104step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5104step3 raw5104step3Labels permutation7 permutation0
    mixedMoment B raw5104step4 raw5104step4Labels = mixedMoment B raw5104step5 raw5104step5Labels := by
      have ha : raw5104step5 = -raw5104step4 := by apply Matrix.ext; change ∀ i j, raw5104step5 i j = -(raw5104step4 i j); unfold raw5104step5 raw5104step4; decide +kernel
      have hl : raw5104step5Labels = raw5104step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5104step5 raw5104step5Labels = mixedMoment B raw5104step6 raw5104step6Labels := by
      have ha : raw5104step6 = raw5104step5 := by apply Matrix.ext; unfold raw5104step6 raw5104step5; decide +kernel
      have hl : raw5104step5Labels = labelEmbedding2 ∘ raw5104step6Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5104step5 raw5104step5Labels raw5104step6Labels labelEmbedding2 hl
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical5105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5105 raw5105Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw5105 raw5105Labels = mixedMoment B raw5105step0 raw5105step0Labels := by
      have hz : ∀ j, raw5105 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5105step0 = (fun i j => raw5105 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5105step0 raw5105; decide +kernel
      have hl : raw5105step0Labels = raw5105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5105 raw5105Labels permutation434 hz
    mixedMoment B raw5105step0 raw5105step0Labels = mixedMoment B raw5105step1 raw5105step1Labels := by
      have hz : ∀ j, raw5105step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5105step1 = (fun i j => raw5105step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5105step1 raw5105step0; decide +kernel
      have hl : raw5105step1Labels = raw5105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5105step0 raw5105step0Labels permutation80 hz
    mixedMoment B raw5105step1 raw5105step1Labels = mixedMoment B raw5105step2 raw5105step2Labels := by
      have hz : ∀ j, raw5105step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5105step2 = (fun i j => raw5105step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5105step2 raw5105step1; decide +kernel
      have hl : raw5105step2Labels = raw5105step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5105step1 raw5105step1Labels permutation14 hz
    mixedMoment B raw5105step2 raw5105step2Labels = mixedMoment B raw5105step3 raw5105step3Labels := by
      have ha : raw5105step3 = (fun i j => raw5105step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5105step3 raw5105step2; decide +kernel
      have hl : raw5105step3Labels = raw5105step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5105step2 raw5105step2Labels permutation7 permutation7
    mixedMoment B raw5105step3 raw5105step3Labels = mixedMoment B raw5105step4 raw5105step4Labels := by
      have ha : raw5105step4 = raw5105step3 := by apply Matrix.ext; unfold raw5105step4 raw5105step3; decide +kernel
      have hl : raw5105step3Labels = labelEmbedding10 ∘ raw5105step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5105step3 raw5105step3Labels raw5105step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5308 node5308Labels := by rfl

theorem canonical5106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5106 raw5106Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw5106 raw5106Labels = mixedMoment B raw5106step0 raw5106step0Labels := by
      have hz : ∀ j, raw5106 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5106step0 = (fun i j => raw5106 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5106step0 raw5106; decide +kernel
      have hl : raw5106step0Labels = raw5106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5106 raw5106Labels permutation434 hz
    mixedMoment B raw5106step0 raw5106step0Labels = mixedMoment B raw5106step1 raw5106step1Labels := by
      have hz : ∀ j, raw5106step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5106step1 = (fun i j => raw5106step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5106step1 raw5106step0; decide +kernel
      have hl : raw5106step1Labels = raw5106step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5106step0 raw5106step0Labels permutation80 hz
    mixedMoment B raw5106step1 raw5106step1Labels = mixedMoment B raw5106step2 raw5106step2Labels := by
      have ha : raw5106step2 = (fun i j => raw5106step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5106step2 raw5106step1; decide +kernel
      have hl : raw5106step2Labels = raw5106step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5106step1 raw5106step1Labels permutation10 permutation2
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical5107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5107 raw5107Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw5107 raw5107Labels = mixedMoment B raw5107step0 raw5107step0Labels := by
      have hz : ∀ j, raw5107 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5107step0 = (fun i j => raw5107 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5107step0 raw5107; decide +kernel
      have hl : raw5107step0Labels = raw5107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5107 raw5107Labels permutation434 hz
    mixedMoment B raw5107step0 raw5107step0Labels = mixedMoment B raw5107step1 raw5107step1Labels := by
      have ha : raw5107step1 = (fun i j => raw5107step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5107step1 raw5107step0; decide +kernel
      have hl : raw5107step1Labels = raw5107step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5107step0 raw5107step0Labels permutation139 permutation2
    mixedMoment B raw5107step1 raw5107step1Labels = mixedMoment B raw5107step2 raw5107step2Labels := by
      have ha : raw5107step2 = -raw5107step1 := by apply Matrix.ext; change ∀ i j, raw5107step2 i j = -(raw5107step1 i j); unfold raw5107step2 raw5107step1; decide +kernel
      have hl : raw5107step2Labels = raw5107step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical5108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5108 raw5108Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw5108 raw5108Labels = mixedMoment B raw5108step0 raw5108step0Labels := by
      have hz : ∀ j, raw5108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5108step0 = (fun i j => raw5108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5108step0 raw5108; decide +kernel
      have hl : raw5108step0Labels = raw5108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5108 raw5108Labels permutation346 hz
    mixedMoment B raw5108step0 raw5108step0Labels = mixedMoment B raw5108step1 raw5108step1Labels := by
      have ha : raw5108step1 = (fun i j => raw5108step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5108step1 raw5108step0; decide +kernel
      have hl : raw5108step1Labels = raw5108step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5108step0 raw5108step0Labels permutation139 permutation2
    mixedMoment B raw5108step1 raw5108step1Labels = mixedMoment B raw5108step2 raw5108step2Labels := by
      have ha : raw5108step2 = -raw5108step1 := by apply Matrix.ext; change ∀ i j, raw5108step2 i j = -(raw5108step1 i j); unfold raw5108step2 raw5108step1; decide +kernel
      have hl : raw5108step2Labels = raw5108step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical5109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5109 raw5109Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw5109 raw5109Labels = mixedMoment B raw5109step0 raw5109step0Labels := by
      have hz : ∀ j, raw5109 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5109step0 = (fun i j => raw5109 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5109step0 raw5109; decide +kernel
      have hl : raw5109step0Labels = raw5109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5109 raw5109Labels permutation434 hz
    mixedMoment B raw5109step0 raw5109step0Labels = mixedMoment B raw5109step1 raw5109step1Labels := by
      have hz : ∀ j, raw5109step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5109step1 = (fun i j => raw5109step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5109step1 raw5109step0; decide +kernel
      have hl : raw5109step1Labels = raw5109step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5109step0 raw5109step0Labels permutation80 hz
    mixedMoment B raw5109step1 raw5109step1Labels = mixedMoment B raw5109step2 raw5109step2Labels := by
      have ha : raw5109step2 = (fun i j => raw5109step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5109step2 raw5109step1; decide +kernel
      have hl : raw5109step2Labels = raw5109step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5109step1 raw5109step1Labels permutation29 permutation2
    mixedMoment B raw5109step2 raw5109step2Labels = mixedMoment B raw5109step3 raw5109step3Labels := by
      have ha : raw5109step3 = -raw5109step2 := by apply Matrix.ext; change ∀ i j, raw5109step3 i j = -(raw5109step2 i j); unfold raw5109step3 raw5109step2; decide +kernel
      have hl : raw5109step3Labels = raw5109step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4841 node4841Labels := by rfl

theorem canonical5110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5110 raw5110Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw5110 raw5110Labels = mixedMoment B raw5110step0 raw5110step0Labels := by
      have hz : ∀ j, raw5110 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5110step0 = (fun i j => raw5110 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5110step0 raw5110; decide +kernel
      have hl : raw5110step0Labels = raw5110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5110 raw5110Labels permutation434 hz
    mixedMoment B raw5110step0 raw5110step0Labels = mixedMoment B raw5110step1 raw5110step1Labels := by
      have hz : ∀ j, raw5110step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5110step1 = (fun i j => raw5110step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5110step1 raw5110step0; decide +kernel
      have hl : raw5110step1Labels = raw5110step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5110step0 raw5110step0Labels permutation80 hz
    mixedMoment B raw5110step1 raw5110step1Labels = mixedMoment B raw5110step2 raw5110step2Labels := by
      have ha : raw5110step2 = (fun i j => raw5110step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5110step2 raw5110step1; decide +kernel
      have hl : raw5110step2Labels = raw5110step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5110step1 raw5110step1Labels permutation10 permutation2
    _ = mixedMoment B node5272 node5272Labels := by rfl

theorem canonical5111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5111 raw5111Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw5111 raw5111Labels = mixedMoment B raw5111step0 raw5111step0Labels := by
      have hz : ∀ j, raw5111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5111step0 = (fun i j => raw5111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5111step0 raw5111; decide +kernel
      have hl : raw5111step0Labels = raw5111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5111 raw5111Labels permutation434 hz
    mixedMoment B raw5111step0 raw5111step0Labels = mixedMoment B raw5111step1 raw5111step1Labels := by
      have hz : ∀ j, raw5111step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5111step1 = (fun i j => raw5111step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5111step1 raw5111step0; decide +kernel
      have hl : raw5111step1Labels = raw5111step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5111step0 raw5111step0Labels permutation56 hz
    mixedMoment B raw5111step1 raw5111step1Labels = mixedMoment B raw5111step2 raw5111step2Labels := by
      have ha : raw5111step2 = (fun i j => raw5111step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5111step2 raw5111step1; decide +kernel
      have hl : raw5111step2Labels = raw5111step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5111step1 raw5111step1Labels permutation10 permutation2
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical5112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5112 raw5112Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw5112 raw5112Labels = mixedMoment B raw5112step0 raw5112step0Labels := by
      have hz : ∀ j, raw5112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5112step0 = (fun i j => raw5112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5112step0 raw5112; decide +kernel
      have hl : raw5112step0Labels = raw5112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5112 raw5112Labels permutation434 hz
    mixedMoment B raw5112step0 raw5112step0Labels = mixedMoment B raw5112step1 raw5112step1Labels := by
      have ha : raw5112step1 = (fun i j => raw5112step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5112step1 raw5112step0; decide +kernel
      have hl : raw5112step1Labels = raw5112step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5112step0 raw5112step0Labels permutation145 permutation2
    mixedMoment B raw5112step1 raw5112step1Labels = mixedMoment B raw5112step2 raw5112step2Labels := by
      have ha : raw5112step2 = -raw5112step1 := by apply Matrix.ext; change ∀ i j, raw5112step2 i j = -(raw5112step1 i j); unfold raw5112step2 raw5112step1; decide +kernel
      have hl : raw5112step2Labels = raw5112step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical5113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5113 raw5113Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw5113 raw5113Labels = mixedMoment B raw5113step0 raw5113step0Labels := by
      have hz : ∀ j, raw5113 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5113step0 = (fun i j => raw5113 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5113step0 raw5113; decide +kernel
      have hl : raw5113step0Labels = raw5113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5113 raw5113Labels permutation265 hz
    mixedMoment B raw5113step0 raw5113step0Labels = mixedMoment B raw5113step1 raw5113step1Labels := by
      have ha : raw5113step1 = (fun i j => raw5113step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5113step1 raw5113step0; decide +kernel
      have hl : raw5113step1Labels = raw5113step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5113step0 raw5113step0Labels permutation139 permutation2
    mixedMoment B raw5113step1 raw5113step1Labels = mixedMoment B raw5113step2 raw5113step2Labels := by
      have ha : raw5113step2 = -raw5113step1 := by apply Matrix.ext; change ∀ i j, raw5113step2 i j = -(raw5113step1 i j); unfold raw5113step2 raw5113step1; decide +kernel
      have hl : raw5113step2Labels = raw5113step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical5114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5114 raw5114Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw5114 raw5114Labels = mixedMoment B raw5114step0 raw5114step0Labels := by
      have hz : ∀ j, raw5114 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5114step0 = (fun i j => raw5114 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5114step0 raw5114; decide +kernel
      have hl : raw5114step0Labels = raw5114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5114 raw5114Labels permutation434 hz
    mixedMoment B raw5114step0 raw5114step0Labels = mixedMoment B raw5114step1 raw5114step1Labels := by
      have hz : ∀ j, raw5114step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5114step1 = (fun i j => raw5114step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5114step1 raw5114step0; decide +kernel
      have hl : raw5114step1Labels = raw5114step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5114step0 raw5114step0Labels permutation56 hz
    mixedMoment B raw5114step1 raw5114step1Labels = mixedMoment B raw5114step2 raw5114step2Labels := by
      have ha : raw5114step2 = (fun i j => raw5114step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5114step2 raw5114step1; decide +kernel
      have hl : raw5114step2Labels = raw5114step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5114step1 raw5114step1Labels permutation29 permutation2
    mixedMoment B raw5114step2 raw5114step2Labels = mixedMoment B raw5114step3 raw5114step3Labels := by
      have ha : raw5114step3 = -raw5114step2 := by apply Matrix.ext; change ∀ i j, raw5114step3 i j = -(raw5114step2 i j); unfold raw5114step3 raw5114step2; decide +kernel
      have hl : raw5114step3Labels = raw5114step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4841 node4841Labels := by rfl

theorem canonical5115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5115 raw5115Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw5115 raw5115Labels = mixedMoment B raw5115step0 raw5115step0Labels := by
      have hz : ∀ j, raw5115 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5115step0 = (fun i j => raw5115 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5115step0 raw5115; decide +kernel
      have hl : raw5115step0Labels = raw5115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5115 raw5115Labels permutation434 hz
    mixedMoment B raw5115step0 raw5115step0Labels = mixedMoment B raw5115step1 raw5115step1Labels := by
      have hz : ∀ j, raw5115step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5115step1 = (fun i j => raw5115step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5115step1 raw5115step0; decide +kernel
      have hl : raw5115step1Labels = raw5115step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5115step0 raw5115step0Labels permutation56 hz
    mixedMoment B raw5115step1 raw5115step1Labels = mixedMoment B raw5115step2 raw5115step2Labels := by
      have ha : raw5115step2 = (fun i j => raw5115step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5115step2 raw5115step1; decide +kernel
      have hl : raw5115step2Labels = raw5115step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5115step1 raw5115step1Labels permutation10 permutation2
    _ = mixedMoment B node5272 node5272Labels := by rfl

theorem canonical5116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5116 raw5116Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw5116 raw5116Labels = mixedMoment B raw5116step0 raw5116step0Labels := by
      have hz : ∀ j, raw5116 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5116step0 = (fun i j => raw5116 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5116step0 raw5116; decide +kernel
      have hl : raw5116step0Labels = raw5116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5116 raw5116Labels permutation346 hz
    mixedMoment B raw5116step0 raw5116step0Labels = mixedMoment B raw5116step1 raw5116step1Labels := by
      have hz : ∀ j, raw5116step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5116step1 = (fun i j => raw5116step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5116step1 raw5116step0; decide +kernel
      have hl : raw5116step1Labels = raw5116step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5116step0 raw5116step0Labels permutation56 hz
    mixedMoment B raw5116step1 raw5116step1Labels = mixedMoment B raw5116step2 raw5116step2Labels := by
      have ha : raw5116step2 = (fun i j => raw5116step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5116step2 raw5116step1; decide +kernel
      have hl : raw5116step2Labels = raw5116step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5116step1 raw5116step1Labels permutation10 permutation2
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical5117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5117 raw5117Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw5117 raw5117Labels = mixedMoment B raw5117step0 raw5117step0Labels := by
      have hz : ∀ j, raw5117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5117step0 = (fun i j => raw5117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5117step0 raw5117; decide +kernel
      have hl : raw5117step0Labels = raw5117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5117 raw5117Labels permutation346 hz
    mixedMoment B raw5117step0 raw5117step0Labels = mixedMoment B raw5117step1 raw5117step1Labels := by
      have ha : raw5117step1 = (fun i j => raw5117step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5117step1 raw5117step0; decide +kernel
      have hl : raw5117step1Labels = raw5117step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5117step0 raw5117step0Labels permutation145 permutation2
    mixedMoment B raw5117step1 raw5117step1Labels = mixedMoment B raw5117step2 raw5117step2Labels := by
      have ha : raw5117step2 = -raw5117step1 := by apply Matrix.ext; change ∀ i j, raw5117step2 i j = -(raw5117step1 i j); unfold raw5117step2 raw5117step1; decide +kernel
      have hl : raw5117step2Labels = raw5117step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical5118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5118 raw5118Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw5118 raw5118Labels = mixedMoment B raw5118step0 raw5118step0Labels := by
      have hz : ∀ j, raw5118 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5118step0 = (fun i j => raw5118 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5118step0 raw5118; decide +kernel
      have hl : raw5118step0Labels = raw5118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5118 raw5118Labels permutation265 hz
    mixedMoment B raw5118step0 raw5118step0Labels = mixedMoment B raw5118step1 raw5118step1Labels := by
      have ha : raw5118step1 = (fun i j => raw5118step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5118step1 raw5118step0; decide +kernel
      have hl : raw5118step1Labels = raw5118step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5118step0 raw5118step0Labels permutation145 permutation2
    mixedMoment B raw5118step1 raw5118step1Labels = mixedMoment B raw5118step2 raw5118step2Labels := by
      have ha : raw5118step2 = -raw5118step1 := by apply Matrix.ext; change ∀ i j, raw5118step2 i j = -(raw5118step1 i j); unfold raw5118step2 raw5118step1; decide +kernel
      have hl : raw5118step2Labels = raw5118step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical5119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5119 raw5119Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw5119 raw5119Labels = mixedMoment B raw5119step0 raw5119step0Labels := by
      have hz : ∀ j, raw5119 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5119step0 = (fun i j => raw5119 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5119step0 raw5119; decide +kernel
      have hl : raw5119step0Labels = raw5119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5119 raw5119Labels permutation346 hz
    mixedMoment B raw5119step0 raw5119step0Labels = mixedMoment B raw5119step1 raw5119step1Labels := by
      have hz : ∀ j, raw5119step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5119step1 = (fun i j => raw5119step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5119step1 raw5119step0; decide +kernel
      have hl : raw5119step1Labels = raw5119step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5119step0 raw5119step0Labels permutation56 hz
    mixedMoment B raw5119step1 raw5119step1Labels = mixedMoment B raw5119step2 raw5119step2Labels := by
      have ha : raw5119step2 = (fun i j => raw5119step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5119step2 raw5119step1; decide +kernel
      have hl : raw5119step2Labels = raw5119step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5119step1 raw5119step1Labels permutation29 permutation2
    mixedMoment B raw5119step2 raw5119step2Labels = mixedMoment B raw5119step3 raw5119step3Labels := by
      have ha : raw5119step3 = -raw5119step2 := by apply Matrix.ext; change ∀ i j, raw5119step3 i j = -(raw5119step2 i j); unfold raw5119step3 raw5119step2; decide +kernel
      have hl : raw5119step3Labels = raw5119step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4841 node4841Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5120 raw5120Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw5120 raw5120Labels = mixedMoment B raw5120step0 raw5120step0Labels := by
      have hz : ∀ j, raw5120 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5120step0 = (fun i j => raw5120 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5120step0 raw5120; decide +kernel
      have hl : raw5120step0Labels = raw5120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5120 raw5120Labels permutation346 hz
    mixedMoment B raw5120step0 raw5120step0Labels = mixedMoment B raw5120step1 raw5120step1Labels := by
      have hz : ∀ j, raw5120step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5120step1 = (fun i j => raw5120step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5120step1 raw5120step0; decide +kernel
      have hl : raw5120step1Labels = raw5120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5120step0 raw5120step0Labels permutation56 hz
    mixedMoment B raw5120step1 raw5120step1Labels = mixedMoment B raw5120step2 raw5120step2Labels := by
      have ha : raw5120step2 = (fun i j => raw5120step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5120step2 raw5120step1; decide +kernel
      have hl : raw5120step2Labels = raw5120step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5120step1 raw5120step1Labels permutation10 permutation2
    _ = mixedMoment B node5272 node5272Labels := by rfl

theorem canonical5121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5121 raw5121Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw5121 raw5121Labels = mixedMoment B raw5121step0 raw5121step0Labels := by
      have hz : ∀ j, raw5121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5121step0 = (fun i j => raw5121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5121step0 raw5121; decide +kernel
      have hl : raw5121step0Labels = raw5121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5121 raw5121Labels permutation434 hz
    mixedMoment B raw5121step0 raw5121step0Labels = mixedMoment B raw5121step1 raw5121step1Labels := by
      have hz : ∀ j, raw5121step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5121step1 = (fun i j => raw5121step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5121step1 raw5121step0; decide +kernel
      have hl : raw5121step1Labels = raw5121step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5121step0 raw5121step0Labels permutation80 hz
    mixedMoment B raw5121step1 raw5121step1Labels = mixedMoment B raw5121step2 raw5121step2Labels := by
      have hz : ∀ j, raw5121step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5121step2 = (fun i j => raw5121step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5121step2 raw5121step1; decide +kernel
      have hl : raw5121step2Labels = raw5121step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5121step1 raw5121step1Labels permutation14 hz
    _ = mixedMoment B node4621 node4621Labels := by rfl

theorem canonical5122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5122 raw5122Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw5122 raw5122Labels = mixedMoment B raw5122step0 raw5122step0Labels := by
      have hz : ∀ j, raw5122 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5122step0 = (fun i j => raw5122 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5122step0 raw5122; decide +kernel
      have hl : raw5122step0Labels = raw5122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5122 raw5122Labels permutation434 hz
    mixedMoment B raw5122step0 raw5122step0Labels = mixedMoment B raw5122step1 raw5122step1Labels := by
      have hz : ∀ j, raw5122step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5122step1 = (fun i j => raw5122step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5122step1 raw5122step0; decide +kernel
      have hl : raw5122step1Labels = raw5122step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5122step0 raw5122step0Labels permutation80 hz
    mixedMoment B raw5122step1 raw5122step1Labels = mixedMoment B raw5122step2 raw5122step2Labels := by
      have ha : raw5122step2 = (fun i j => raw5122step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5122step2 raw5122step1; decide +kernel
      have hl : raw5122step2Labels = raw5122step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5122step1 raw5122step1Labels permutation31 permutation2
    mixedMoment B raw5122step2 raw5122step2Labels = mixedMoment B raw5122step3 raw5122step3Labels := by
      have ha : raw5122step3 = -raw5122step2 := by apply Matrix.ext; change ∀ i j, raw5122step3 i j = -(raw5122step2 i j); unfold raw5122step3 raw5122step2; decide +kernel
      have hl : raw5122step3Labels = raw5122step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical5123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5123 raw5123Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw5123 raw5123Labels = mixedMoment B raw5123step0 raw5123step0Labels := by
      have hz : ∀ j, raw5123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5123step0 = (fun i j => raw5123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5123step0 raw5123; decide +kernel
      have hl : raw5123step0Labels = raw5123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5123 raw5123Labels permutation434 hz
    mixedMoment B raw5123step0 raw5123step0Labels = mixedMoment B raw5123step1 raw5123step1Labels := by
      have hz : ∀ j, raw5123step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5123step1 = (fun i j => raw5123step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5123step1 raw5123step0; decide +kernel
      have hl : raw5123step1Labels = raw5123step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5123step0 raw5123step0Labels permutation56 hz
    mixedMoment B raw5123step1 raw5123step1Labels = mixedMoment B raw5123step2 raw5123step2Labels := by
      have ha : raw5123step2 = (fun i j => raw5123step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5123step2 raw5123step1; decide +kernel
      have hl : raw5123step2Labels = raw5123step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5123step1 raw5123step1Labels permutation31 permutation2
    mixedMoment B raw5123step2 raw5123step2Labels = mixedMoment B raw5123step3 raw5123step3Labels := by
      have ha : raw5123step3 = -raw5123step2 := by apply Matrix.ext; change ∀ i j, raw5123step3 i j = -(raw5123step2 i j); unfold raw5123step3 raw5123step2; decide +kernel
      have hl : raw5123step3Labels = raw5123step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical5124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5124 raw5124Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw5124 raw5124Labels = mixedMoment B raw5124step0 raw5124step0Labels := by
      have hz : ∀ j, raw5124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5124step0 = (fun i j => raw5124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5124step0 raw5124; decide +kernel
      have hl : raw5124step0Labels = raw5124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5124 raw5124Labels permutation346 hz
    mixedMoment B raw5124step0 raw5124step0Labels = mixedMoment B raw5124step1 raw5124step1Labels := by
      have hz : ∀ j, raw5124step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5124step1 = (fun i j => raw5124step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5124step1 raw5124step0; decide +kernel
      have hl : raw5124step1Labels = raw5124step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5124step0 raw5124step0Labels permutation56 hz
    mixedMoment B raw5124step1 raw5124step1Labels = mixedMoment B raw5124step2 raw5124step2Labels := by
      have ha : raw5124step2 = (fun i j => raw5124step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5124step2 raw5124step1; decide +kernel
      have hl : raw5124step2Labels = raw5124step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5124step1 raw5124step1Labels permutation31 permutation2
    mixedMoment B raw5124step2 raw5124step2Labels = mixedMoment B raw5124step3 raw5124step3Labels := by
      have ha : raw5124step3 = -raw5124step2 := by apply Matrix.ext; change ∀ i j, raw5124step3 i j = -(raw5124step2 i j); unfold raw5124step3 raw5124step2; decide +kernel
      have hl : raw5124step3Labels = raw5124step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical5125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5125 raw5125Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw5125 raw5125Labels = mixedMoment B raw5125step0 raw5125step0Labels := by
      have hz : ∀ j, raw5125 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5125step0 = (fun i j => raw5125 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5125step0 raw5125; decide +kernel
      have hl : raw5125step0Labels = raw5125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5125 raw5125Labels permutation434 hz
    mixedMoment B raw5125step0 raw5125step0Labels = mixedMoment B raw5125step1 raw5125step1Labels := by
      have hz : ∀ j, raw5125step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5125step1 = (fun i j => raw5125step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5125step1 raw5125step0; decide +kernel
      have hl : raw5125step1Labels = raw5125step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5125step0 raw5125step0Labels permutation80 hz
    mixedMoment B raw5125step1 raw5125step1Labels = mixedMoment B raw5125step2 raw5125step2Labels := by
      have hz : ∀ j, raw5125step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5125step2 = (fun i j => raw5125step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5125step2 raw5125step1; decide +kernel
      have hl : raw5125step2Labels = raw5125step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5125step1 raw5125step1Labels permutation14 hz
    _ = mixedMoment B node5305 node5305Labels := by rfl

theorem canonical5126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5126 raw5126Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw5126 raw5126Labels = mixedMoment B raw5126step0 raw5126step0Labels := by
      have hz : ∀ j, raw5126 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5126step0 = (fun i j => raw5126 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5126step0 raw5126; decide +kernel
      have hl : raw5126step0Labels = raw5126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5126 raw5126Labels permutation434 hz
    mixedMoment B raw5126step0 raw5126step0Labels = mixedMoment B raw5126step1 raw5126step1Labels := by
      have hz : ∀ j, raw5126step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5126step1 = (fun i j => raw5126step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5126step1 raw5126step0; decide +kernel
      have hl : raw5126step1Labels = raw5126step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5126step0 raw5126step0Labels permutation80 hz
    mixedMoment B raw5126step1 raw5126step1Labels = mixedMoment B raw5126step2 raw5126step2Labels := by
      have hz : ∀ j, raw5126step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5126step2 = (fun i j => raw5126step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5126step2 raw5126step1; decide +kernel
      have hl : raw5126step2Labels = raw5126step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5126step1 raw5126step1Labels permutation14 hz
    mixedMoment B raw5126step2 raw5126step2Labels = mixedMoment B raw5126step3 raw5126step3Labels := by
      have ha : raw5126step3 = (fun i j => raw5126step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5126step3 raw5126step2; decide +kernel
      have hl : raw5126step3Labels = raw5126step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5126step2 raw5126step2Labels permutation7 permutation2
    mixedMoment B raw5126step3 raw5126step3Labels = mixedMoment B raw5126step4 raw5126step4Labels := by
      have ha : raw5126step4 = -raw5126step3 := by apply Matrix.ext; change ∀ i j, raw5126step4 i j = -(raw5126step3 i j); unfold raw5126step4 raw5126step3; decide +kernel
      have hl : raw5126step4Labels = raw5126step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical5127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5127 raw5127Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw5127 raw5127Labels = mixedMoment B raw5127step0 raw5127step0Labels := by
      have hz : ∀ j, raw5127 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5127step0 = (fun i j => raw5127 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5127step0 raw5127; decide +kernel
      have hl : raw5127step0Labels = raw5127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5127 raw5127Labels permutation434 hz
    mixedMoment B raw5127step0 raw5127step0Labels = mixedMoment B raw5127step1 raw5127step1Labels := by
      have hz : ∀ j, raw5127step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5127step1 = (fun i j => raw5127step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5127step1 raw5127step0; decide +kernel
      have hl : raw5127step1Labels = raw5127step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5127step0 raw5127step0Labels permutation80 hz
    mixedMoment B raw5127step1 raw5127step1Labels = mixedMoment B raw5127step2 raw5127step2Labels := by
      have ha : raw5127step2 = (fun i j => raw5127step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5127step2 raw5127step1; decide +kernel
      have hl : raw5127step2Labels = raw5127step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5127step1 raw5127step1Labels permutation31 permutation2
    mixedMoment B raw5127step2 raw5127step2Labels = mixedMoment B raw5127step3 raw5127step3Labels := by
      have ha : raw5127step3 = -raw5127step2 := by apply Matrix.ext; change ∀ i j, raw5127step3 i j = -(raw5127step2 i j); unfold raw5127step3 raw5127step2; decide +kernel
      have hl : raw5127step3Labels = raw5127step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical5128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5128 raw5128Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw5128 raw5128Labels = mixedMoment B raw5128step0 raw5128step0Labels := by
      have hz : ∀ j, raw5128 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5128step0 = (fun i j => raw5128 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5128step0 raw5128; decide +kernel
      have hl : raw5128step0Labels = raw5128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5128 raw5128Labels permutation434 hz
    mixedMoment B raw5128step0 raw5128step0Labels = mixedMoment B raw5128step1 raw5128step1Labels := by
      have hz : ∀ j, raw5128step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5128step1 = (fun i j => raw5128step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5128step1 raw5128step0; decide +kernel
      have hl : raw5128step1Labels = raw5128step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5128step0 raw5128step0Labels permutation56 hz
    mixedMoment B raw5128step1 raw5128step1Labels = mixedMoment B raw5128step2 raw5128step2Labels := by
      have ha : raw5128step2 = (fun i j => raw5128step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5128step2 raw5128step1; decide +kernel
      have hl : raw5128step2Labels = raw5128step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5128step1 raw5128step1Labels permutation31 permutation2
    mixedMoment B raw5128step2 raw5128step2Labels = mixedMoment B raw5128step3 raw5128step3Labels := by
      have ha : raw5128step3 = -raw5128step2 := by apply Matrix.ext; change ∀ i j, raw5128step3 i j = -(raw5128step2 i j); unfold raw5128step3 raw5128step2; decide +kernel
      have hl : raw5128step3Labels = raw5128step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical5129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5129 raw5129Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw5129 raw5129Labels = mixedMoment B raw5129step0 raw5129step0Labels := by
      have hz : ∀ j, raw5129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5129step0 = (fun i j => raw5129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5129step0 raw5129; decide +kernel
      have hl : raw5129step0Labels = raw5129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5129 raw5129Labels permutation346 hz
    mixedMoment B raw5129step0 raw5129step0Labels = mixedMoment B raw5129step1 raw5129step1Labels := by
      have hz : ∀ j, raw5129step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5129step1 = (fun i j => raw5129step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5129step1 raw5129step0; decide +kernel
      have hl : raw5129step1Labels = raw5129step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5129step0 raw5129step0Labels permutation56 hz
    mixedMoment B raw5129step1 raw5129step1Labels = mixedMoment B raw5129step2 raw5129step2Labels := by
      have ha : raw5129step2 = (fun i j => raw5129step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5129step2 raw5129step1; decide +kernel
      have hl : raw5129step2Labels = raw5129step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5129step1 raw5129step1Labels permutation31 permutation2
    mixedMoment B raw5129step2 raw5129step2Labels = mixedMoment B raw5129step3 raw5129step3Labels := by
      have ha : raw5129step3 = -raw5129step2 := by apply Matrix.ext; change ∀ i j, raw5129step3 i j = -(raw5129step2 i j); unfold raw5129step3 raw5129step2; decide +kernel
      have hl : raw5129step3Labels = raw5129step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical5130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5130 raw5130Labels = mixedMoment B node4505 node4505Labels := by
  calc
    mixedMoment B raw5130 raw5130Labels = mixedMoment B raw5130step0 raw5130step0Labels := by
      have hz : ∀ j, raw5130 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5130step0 = (fun i j => raw5130 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5130step0 raw5130; decide +kernel
      have hl : raw5130step0Labels = raw5130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5130 raw5130Labels permutation434 hz
    mixedMoment B raw5130step0 raw5130step0Labels = mixedMoment B raw5130step1 raw5130step1Labels := by
      have hz : ∀ j, raw5130step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5130step1 = (fun i j => raw5130step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5130step1 raw5130step0; decide +kernel
      have hl : raw5130step1Labels = raw5130step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5130step0 raw5130step0Labels permutation80 hz
    mixedMoment B raw5130step1 raw5130step1Labels = mixedMoment B raw5130step2 raw5130step2Labels := by
      have hz : ∀ j, raw5130step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5130step2 = (fun i j => raw5130step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5130step2 raw5130step1; decide +kernel
      have hl : raw5130step2Labels = raw5130step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5130step1 raw5130step1Labels permutation14 hz
    mixedMoment B raw5130step2 raw5130step2Labels = mixedMoment B raw5130step3 raw5130step3Labels := by
      have ha : raw5130step3 = (fun i j => raw5130step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5130step3 raw5130step2; decide +kernel
      have hl : raw5130step3Labels = raw5130step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5130step2 raw5130step2Labels permutation7 permutation2
    mixedMoment B raw5130step3 raw5130step3Labels = mixedMoment B raw5130step4 raw5130step4Labels := by
      have ha : raw5130step4 = -raw5130step3 := by apply Matrix.ext; change ∀ i j, raw5130step4 i j = -(raw5130step3 i j); unfold raw5130step4 raw5130step3; decide +kernel
      have hl : raw5130step4Labels = raw5130step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4505 node4505Labels := by rfl

theorem canonical5131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5131 raw5131Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw5131 raw5131Labels = mixedMoment B raw5131step0 raw5131step0Labels := by
      have hz : ∀ j, raw5131 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5131step0 = (fun i j => raw5131 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5131step0 raw5131; decide +kernel
      have hl : raw5131step0Labels = raw5131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5131 raw5131Labels permutation434 hz
    mixedMoment B raw5131step0 raw5131step0Labels = mixedMoment B raw5131step1 raw5131step1Labels := by
      have hz : ∀ j, raw5131step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5131step1 = (fun i j => raw5131step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5131step1 raw5131step0; decide +kernel
      have hl : raw5131step1Labels = raw5131step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5131step0 raw5131step0Labels permutation80 hz
    mixedMoment B raw5131step1 raw5131step1Labels = mixedMoment B raw5131step2 raw5131step2Labels := by
      have ha : raw5131step2 = (fun i j => raw5131step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5131step2 raw5131step1; decide +kernel
      have hl : raw5131step2Labels = raw5131step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5131step1 raw5131step1Labels permutation29 permutation7
    mixedMoment B raw5131step2 raw5131step2Labels = mixedMoment B raw5131step3 raw5131step3Labels := by
      have ha : raw5131step3 = raw5131step2 := by apply Matrix.ext; unfold raw5131step3 raw5131step2; decide +kernel
      have hl : raw5131step2Labels = labelEmbedding1 ∘ raw5131step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5131step2 raw5131step2Labels raw5131step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical5132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5132 raw5132Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw5132 raw5132Labels = mixedMoment B raw5132step0 raw5132step0Labels := by
      have hz : ∀ j, raw5132 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5132step0 = (fun i j => raw5132 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5132step0 raw5132; decide +kernel
      have hl : raw5132step0Labels = raw5132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5132 raw5132Labels permutation434 hz
    mixedMoment B raw5132step0 raw5132step0Labels = mixedMoment B raw5132step1 raw5132step1Labels := by
      have hz : ∀ j, raw5132step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5132step1 = (fun i j => raw5132step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5132step1 raw5132step0; decide +kernel
      have hl : raw5132step1Labels = raw5132step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5132step0 raw5132step0Labels permutation56 hz
    mixedMoment B raw5132step1 raw5132step1Labels = mixedMoment B raw5132step2 raw5132step2Labels := by
      have ha : raw5132step2 = (fun i j => raw5132step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5132step2 raw5132step1; decide +kernel
      have hl : raw5132step2Labels = raw5132step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5132step1 raw5132step1Labels permutation29 permutation7
    mixedMoment B raw5132step2 raw5132step2Labels = mixedMoment B raw5132step3 raw5132step3Labels := by
      have ha : raw5132step3 = raw5132step2 := by apply Matrix.ext; unfold raw5132step3 raw5132step2; decide +kernel
      have hl : raw5132step2Labels = labelEmbedding1 ∘ raw5132step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5132step2 raw5132step2Labels raw5132step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical5133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5133 raw5133Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw5133 raw5133Labels = mixedMoment B raw5133step0 raw5133step0Labels := by
      have hz : ∀ j, raw5133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5133step0 = (fun i j => raw5133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5133step0 raw5133; decide +kernel
      have hl : raw5133step0Labels = raw5133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5133 raw5133Labels permutation346 hz
    mixedMoment B raw5133step0 raw5133step0Labels = mixedMoment B raw5133step1 raw5133step1Labels := by
      have hz : ∀ j, raw5133step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5133step1 = (fun i j => raw5133step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5133step1 raw5133step0; decide +kernel
      have hl : raw5133step1Labels = raw5133step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5133step0 raw5133step0Labels permutation56 hz
    mixedMoment B raw5133step1 raw5133step1Labels = mixedMoment B raw5133step2 raw5133step2Labels := by
      have ha : raw5133step2 = (fun i j => raw5133step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5133step2 raw5133step1; decide +kernel
      have hl : raw5133step2Labels = raw5133step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5133step1 raw5133step1Labels permutation29 permutation7
    mixedMoment B raw5133step2 raw5133step2Labels = mixedMoment B raw5133step3 raw5133step3Labels := by
      have ha : raw5133step3 = raw5133step2 := by apply Matrix.ext; unfold raw5133step3 raw5133step2; decide +kernel
      have hl : raw5133step2Labels = labelEmbedding1 ∘ raw5133step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5133step2 raw5133step2Labels raw5133step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical5134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5134 raw5134Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5134 raw5134Labels = mixedMoment B raw5134step0 raw5134step0Labels := by
      have hz : ∀ j, raw5134 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5134step0 = (fun i j => raw5134 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5134step0 raw5134; decide +kernel
      have hl : raw5134step0Labels = raw5134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5134 raw5134Labels permutation434 hz
    mixedMoment B raw5134step0 raw5134step0Labels = mixedMoment B raw5134step1 raw5134step1Labels := by
      have hz : ∀ j, raw5134step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5134step1 = (fun i j => raw5134step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5134step1 raw5134step0; decide +kernel
      have hl : raw5134step1Labels = raw5134step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5134step0 raw5134step0Labels permutation80 hz
    mixedMoment B raw5134step1 raw5134step1Labels = mixedMoment B raw5134step2 raw5134step2Labels := by
      have hz : ∀ j, raw5134step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5134step2 = (fun i j => raw5134step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5134step2 raw5134step1; decide +kernel
      have hl : raw5134step2Labels = raw5134step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5134step1 raw5134step1Labels permutation14 hz
    mixedMoment B raw5134step2 raw5134step2Labels = mixedMoment B raw5134step3 raw5134step3Labels := by
      have hz : ∀ i, raw5134step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw5134step3 = (fun i j => raw5134step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw5134step3 raw5134step2; decide +kernel
      have hl : raw5134step3Labels = (fun j => raw5134step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5134step2 raw5134step2Labels permutation4 hz
    mixedMoment B raw5134step3 raw5134step3Labels = mixedMoment B raw5134step4 raw5134step4Labels := by
      have ha : raw5134step4 = (fun i j => raw5134step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5134step4 raw5134step3; decide +kernel
      have hl : raw5134step4Labels = raw5134step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5134step3 raw5134step3Labels permutation7 permutation0
    mixedMoment B raw5134step4 raw5134step4Labels = mixedMoment B raw5134step5 raw5134step5Labels := by
      have ha : raw5134step5 = -raw5134step4 := by apply Matrix.ext; change ∀ i j, raw5134step5 i j = -(raw5134step4 i j); unfold raw5134step5 raw5134step4; decide +kernel
      have hl : raw5134step5Labels = raw5134step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical5135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5135 raw5135Labels = mixedMoment B node2786 node2786Labels := by
  calc
    mixedMoment B raw5135 raw5135Labels = mixedMoment B raw5135step0 raw5135step0Labels := by
      have hz : ∀ j, raw5135 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5135step0 = (fun i j => raw5135 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5135step0 raw5135; decide +kernel
      have hl : raw5135step0Labels = raw5135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5135 raw5135Labels permutation434 hz
    mixedMoment B raw5135step0 raw5135step0Labels = mixedMoment B raw5135step1 raw5135step1Labels := by
      have hz : ∀ j, raw5135step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5135step1 = (fun i j => raw5135step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5135step1 raw5135step0; decide +kernel
      have hl : raw5135step1Labels = raw5135step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5135step0 raw5135step0Labels permutation80 hz
    mixedMoment B raw5135step1 raw5135step1Labels = mixedMoment B raw5135step2 raw5135step2Labels := by
      have hz : ∀ j, raw5135step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5135step2 = (fun i j => raw5135step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5135step2 raw5135step1; decide +kernel
      have hl : raw5135step2Labels = raw5135step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5135step1 raw5135step1Labels permutation14 hz
    mixedMoment B raw5135step2 raw5135step2Labels = mixedMoment B raw5135step3 raw5135step3Labels := by
      have ha : raw5135step3 = (fun i j => raw5135step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5135step3 raw5135step2; decide +kernel
      have hl : raw5135step3Labels = raw5135step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5135step2 raw5135step2Labels permutation7 permutation7
    mixedMoment B raw5135step3 raw5135step3Labels = mixedMoment B raw5135step4 raw5135step4Labels := by
      have ha : raw5135step4 = raw5135step3 := by apply Matrix.ext; unfold raw5135step4 raw5135step3; decide +kernel
      have hl : raw5135step3Labels = labelEmbedding1 ∘ raw5135step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5135step3 raw5135step3Labels raw5135step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2786 node2786Labels := by rfl

theorem canonical5136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5136 raw5136Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw5136 raw5136Labels = mixedMoment B raw5136step0 raw5136step0Labels := by
      have hz : ∀ j, raw5136 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5136step0 = (fun i j => raw5136 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5136step0 raw5136; decide +kernel
      have hl : raw5136step0Labels = raw5136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5136 raw5136Labels permutation434 hz
    mixedMoment B raw5136step0 raw5136step0Labels = mixedMoment B raw5136step1 raw5136step1Labels := by
      have hz : ∀ j, raw5136step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5136step1 = (fun i j => raw5136step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5136step1 raw5136step0; decide +kernel
      have hl : raw5136step1Labels = raw5136step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5136step0 raw5136step0Labels permutation80 hz
    mixedMoment B raw5136step1 raw5136step1Labels = mixedMoment B raw5136step2 raw5136step2Labels := by
      have ha : raw5136step2 = (fun i j => raw5136step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5136step2 raw5136step1; decide +kernel
      have hl : raw5136step2Labels = raw5136step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5136step1 raw5136step1Labels permutation29 permutation7
    mixedMoment B raw5136step2 raw5136step2Labels = mixedMoment B raw5136step3 raw5136step3Labels := by
      have ha : raw5136step3 = raw5136step2 := by apply Matrix.ext; unfold raw5136step3 raw5136step2; decide +kernel
      have hl : raw5136step2Labels = labelEmbedding1 ∘ raw5136step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5136step2 raw5136step2Labels raw5136step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical5137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5137 raw5137Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw5137 raw5137Labels = mixedMoment B raw5137step0 raw5137step0Labels := by
      have hz : ∀ j, raw5137 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5137step0 = (fun i j => raw5137 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5137step0 raw5137; decide +kernel
      have hl : raw5137step0Labels = raw5137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5137 raw5137Labels permutation434 hz
    mixedMoment B raw5137step0 raw5137step0Labels = mixedMoment B raw5137step1 raw5137step1Labels := by
      have ha : raw5137step1 = (fun i j => raw5137step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5137step1 raw5137step0; decide +kernel
      have hl : raw5137step1Labels = raw5137step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5137step0 raw5137step0Labels permutation137 permutation7
    mixedMoment B raw5137step1 raw5137step1Labels = mixedMoment B raw5137step2 raw5137step2Labels := by
      have ha : raw5137step2 = raw5137step1 := by apply Matrix.ext; unfold raw5137step2 raw5137step1; decide +kernel
      have hl : raw5137step1Labels = labelEmbedding1 ∘ raw5137step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5137step1 raw5137step1Labels raw5137step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical5138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5138 raw5138Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw5138 raw5138Labels = mixedMoment B raw5138step0 raw5138step0Labels := by
      have hz : ∀ j, raw5138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5138step0 = (fun i j => raw5138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5138step0 raw5138; decide +kernel
      have hl : raw5138step0Labels = raw5138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5138 raw5138Labels permutation346 hz
    mixedMoment B raw5138step0 raw5138step0Labels = mixedMoment B raw5138step1 raw5138step1Labels := by
      have ha : raw5138step1 = (fun i j => raw5138step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5138step1 raw5138step0; decide +kernel
      have hl : raw5138step1Labels = raw5138step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5138step0 raw5138step0Labels permutation137 permutation7
    mixedMoment B raw5138step1 raw5138step1Labels = mixedMoment B raw5138step2 raw5138step2Labels := by
      have ha : raw5138step2 = raw5138step1 := by apply Matrix.ext; unfold raw5138step2 raw5138step1; decide +kernel
      have hl : raw5138step1Labels = labelEmbedding1 ∘ raw5138step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5138step1 raw5138step1Labels raw5138step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical5139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5139 raw5139Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw5139 raw5139Labels = mixedMoment B raw5139step0 raw5139step0Labels := by
      have hz : ∀ j, raw5139 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5139step0 = (fun i j => raw5139 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5139step0 raw5139; decide +kernel
      have hl : raw5139step0Labels = raw5139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5139 raw5139Labels permutation434 hz
    mixedMoment B raw5139step0 raw5139step0Labels = mixedMoment B raw5139step1 raw5139step1Labels := by
      have hz : ∀ j, raw5139step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5139step1 = (fun i j => raw5139step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5139step1 raw5139step0; decide +kernel
      have hl : raw5139step1Labels = raw5139step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5139step0 raw5139step0Labels permutation80 hz
    mixedMoment B raw5139step1 raw5139step1Labels = mixedMoment B raw5139step2 raw5139step2Labels := by
      have ha : raw5139step2 = (fun i j => raw5139step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5139step2 raw5139step1; decide +kernel
      have hl : raw5139step2Labels = raw5139step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5139step1 raw5139step1Labels permutation29 permutation7
    mixedMoment B raw5139step2 raw5139step2Labels = mixedMoment B raw5139step3 raw5139step3Labels := by
      have ha : raw5139step3 = raw5139step2 := by apply Matrix.ext; unfold raw5139step3 raw5139step2; decide +kernel
      have hl : raw5139step2Labels = labelEmbedding1 ∘ raw5139step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5139step2 raw5139step2Labels raw5139step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

theorem canonical5140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5140 raw5140Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw5140 raw5140Labels = mixedMoment B raw5140step0 raw5140step0Labels := by
      have hz : ∀ j, raw5140 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5140step0 = (fun i j => raw5140 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5140step0 raw5140; decide +kernel
      have hl : raw5140step0Labels = raw5140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5140 raw5140Labels permutation434 hz
    mixedMoment B raw5140step0 raw5140step0Labels = mixedMoment B raw5140step1 raw5140step1Labels := by
      have hz : ∀ j, raw5140step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5140step1 = (fun i j => raw5140step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5140step1 raw5140step0; decide +kernel
      have hl : raw5140step1Labels = raw5140step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5140step0 raw5140step0Labels permutation80 hz
    mixedMoment B raw5140step1 raw5140step1Labels = mixedMoment B raw5140step2 raw5140step2Labels := by
      have ha : raw5140step2 = (fun i j => raw5140step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5140step2 raw5140step1; decide +kernel
      have hl : raw5140step2Labels = raw5140step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5140step1 raw5140step1Labels permutation29 permutation7
    mixedMoment B raw5140step2 raw5140step2Labels = mixedMoment B raw5140step3 raw5140step3Labels := by
      have ha : raw5140step3 = raw5140step2 := by apply Matrix.ext; unfold raw5140step3 raw5140step2; decide +kernel
      have hl : raw5140step2Labels = labelEmbedding1 ∘ raw5140step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5140step2 raw5140step2Labels raw5140step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical5141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5141 raw5141Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw5141 raw5141Labels = mixedMoment B raw5141step0 raw5141step0Labels := by
      have hz : ∀ j, raw5141 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5141step0 = (fun i j => raw5141 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5141step0 raw5141; decide +kernel
      have hl : raw5141step0Labels = raw5141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5141 raw5141Labels permutation434 hz
    mixedMoment B raw5141step0 raw5141step0Labels = mixedMoment B raw5141step1 raw5141step1Labels := by
      have hz : ∀ j, raw5141step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5141step1 = (fun i j => raw5141step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5141step1 raw5141step0; decide +kernel
      have hl : raw5141step1Labels = raw5141step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5141step0 raw5141step0Labels permutation56 hz
    mixedMoment B raw5141step1 raw5141step1Labels = mixedMoment B raw5141step2 raw5141step2Labels := by
      have ha : raw5141step2 = (fun i j => raw5141step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5141step2 raw5141step1; decide +kernel
      have hl : raw5141step2Labels = raw5141step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5141step1 raw5141step1Labels permutation29 permutation7
    mixedMoment B raw5141step2 raw5141step2Labels = mixedMoment B raw5141step3 raw5141step3Labels := by
      have ha : raw5141step3 = raw5141step2 := by apply Matrix.ext; unfold raw5141step3 raw5141step2; decide +kernel
      have hl : raw5141step2Labels = labelEmbedding1 ∘ raw5141step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5141step2 raw5141step2Labels raw5141step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical5142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5142 raw5142Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw5142 raw5142Labels = mixedMoment B raw5142step0 raw5142step0Labels := by
      have hz : ∀ j, raw5142 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5142step0 = (fun i j => raw5142 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5142step0 raw5142; decide +kernel
      have hl : raw5142step0Labels = raw5142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5142 raw5142Labels permutation434 hz
    mixedMoment B raw5142step0 raw5142step0Labels = mixedMoment B raw5142step1 raw5142step1Labels := by
      have ha : raw5142step1 = (fun i j => raw5142step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5142step1 raw5142step0; decide +kernel
      have hl : raw5142step1Labels = raw5142step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5142step0 raw5142step0Labels permutation143 permutation7
    mixedMoment B raw5142step1 raw5142step1Labels = mixedMoment B raw5142step2 raw5142step2Labels := by
      have ha : raw5142step2 = raw5142step1 := by apply Matrix.ext; unfold raw5142step2 raw5142step1; decide +kernel
      have hl : raw5142step1Labels = labelEmbedding1 ∘ raw5142step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5142step1 raw5142step1Labels raw5142step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical5143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5143 raw5143Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw5143 raw5143Labels = mixedMoment B raw5143step0 raw5143step0Labels := by
      have hz : ∀ j, raw5143 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5143step0 = (fun i j => raw5143 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5143step0 raw5143; decide +kernel
      have hl : raw5143step0Labels = raw5143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5143 raw5143Labels permutation265 hz
    mixedMoment B raw5143step0 raw5143step0Labels = mixedMoment B raw5143step1 raw5143step1Labels := by
      have ha : raw5143step1 = (fun i j => raw5143step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5143step1 raw5143step0; decide +kernel
      have hl : raw5143step1Labels = raw5143step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5143step0 raw5143step0Labels permutation137 permutation7
    mixedMoment B raw5143step1 raw5143step1Labels = mixedMoment B raw5143step2 raw5143step2Labels := by
      have ha : raw5143step2 = raw5143step1 := by apply Matrix.ext; unfold raw5143step2 raw5143step1; decide +kernel
      have hl : raw5143step1Labels = labelEmbedding1 ∘ raw5143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5143step1 raw5143step1Labels raw5143step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical5144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5144 raw5144Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw5144 raw5144Labels = mixedMoment B raw5144step0 raw5144step0Labels := by
      have hz : ∀ j, raw5144 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5144step0 = (fun i j => raw5144 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5144step0 raw5144; decide +kernel
      have hl : raw5144step0Labels = raw5144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5144 raw5144Labels permutation434 hz
    mixedMoment B raw5144step0 raw5144step0Labels = mixedMoment B raw5144step1 raw5144step1Labels := by
      have hz : ∀ j, raw5144step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5144step1 = (fun i j => raw5144step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5144step1 raw5144step0; decide +kernel
      have hl : raw5144step1Labels = raw5144step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5144step0 raw5144step0Labels permutation56 hz
    mixedMoment B raw5144step1 raw5144step1Labels = mixedMoment B raw5144step2 raw5144step2Labels := by
      have ha : raw5144step2 = (fun i j => raw5144step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5144step2 raw5144step1; decide +kernel
      have hl : raw5144step2Labels = raw5144step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5144step1 raw5144step1Labels permutation29 permutation7
    mixedMoment B raw5144step2 raw5144step2Labels = mixedMoment B raw5144step3 raw5144step3Labels := by
      have ha : raw5144step3 = raw5144step2 := by apply Matrix.ext; unfold raw5144step3 raw5144step2; decide +kernel
      have hl : raw5144step2Labels = labelEmbedding1 ∘ raw5144step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5144step2 raw5144step2Labels raw5144step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

theorem canonical5145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5145 raw5145Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw5145 raw5145Labels = mixedMoment B raw5145step0 raw5145step0Labels := by
      have hz : ∀ j, raw5145 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5145step0 = (fun i j => raw5145 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5145step0 raw5145; decide +kernel
      have hl : raw5145step0Labels = raw5145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5145 raw5145Labels permutation434 hz
    mixedMoment B raw5145step0 raw5145step0Labels = mixedMoment B raw5145step1 raw5145step1Labels := by
      have hz : ∀ j, raw5145step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5145step1 = (fun i j => raw5145step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5145step1 raw5145step0; decide +kernel
      have hl : raw5145step1Labels = raw5145step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5145step0 raw5145step0Labels permutation56 hz
    mixedMoment B raw5145step1 raw5145step1Labels = mixedMoment B raw5145step2 raw5145step2Labels := by
      have ha : raw5145step2 = (fun i j => raw5145step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5145step2 raw5145step1; decide +kernel
      have hl : raw5145step2Labels = raw5145step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5145step1 raw5145step1Labels permutation29 permutation7
    mixedMoment B raw5145step2 raw5145step2Labels = mixedMoment B raw5145step3 raw5145step3Labels := by
      have ha : raw5145step3 = raw5145step2 := by apply Matrix.ext; unfold raw5145step3 raw5145step2; decide +kernel
      have hl : raw5145step2Labels = labelEmbedding1 ∘ raw5145step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5145step2 raw5145step2Labels raw5145step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical5146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5146 raw5146Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw5146 raw5146Labels = mixedMoment B raw5146step0 raw5146step0Labels := by
      have hz : ∀ j, raw5146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5146step0 = (fun i j => raw5146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5146step0 raw5146; decide +kernel
      have hl : raw5146step0Labels = raw5146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5146 raw5146Labels permutation346 hz
    mixedMoment B raw5146step0 raw5146step0Labels = mixedMoment B raw5146step1 raw5146step1Labels := by
      have hz : ∀ j, raw5146step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5146step1 = (fun i j => raw5146step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5146step1 raw5146step0; decide +kernel
      have hl : raw5146step1Labels = raw5146step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5146step0 raw5146step0Labels permutation56 hz
    mixedMoment B raw5146step1 raw5146step1Labels = mixedMoment B raw5146step2 raw5146step2Labels := by
      have ha : raw5146step2 = (fun i j => raw5146step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5146step2 raw5146step1; decide +kernel
      have hl : raw5146step2Labels = raw5146step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5146step1 raw5146step1Labels permutation29 permutation7
    mixedMoment B raw5146step2 raw5146step2Labels = mixedMoment B raw5146step3 raw5146step3Labels := by
      have ha : raw5146step3 = raw5146step2 := by apply Matrix.ext; unfold raw5146step3 raw5146step2; decide +kernel
      have hl : raw5146step2Labels = labelEmbedding1 ∘ raw5146step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5146step2 raw5146step2Labels raw5146step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical5147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5147 raw5147Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw5147 raw5147Labels = mixedMoment B raw5147step0 raw5147step0Labels := by
      have hz : ∀ j, raw5147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5147step0 = (fun i j => raw5147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5147step0 raw5147; decide +kernel
      have hl : raw5147step0Labels = raw5147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5147 raw5147Labels permutation346 hz
    mixedMoment B raw5147step0 raw5147step0Labels = mixedMoment B raw5147step1 raw5147step1Labels := by
      have ha : raw5147step1 = (fun i j => raw5147step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5147step1 raw5147step0; decide +kernel
      have hl : raw5147step1Labels = raw5147step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5147step0 raw5147step0Labels permutation143 permutation7
    mixedMoment B raw5147step1 raw5147step1Labels = mixedMoment B raw5147step2 raw5147step2Labels := by
      have ha : raw5147step2 = raw5147step1 := by apply Matrix.ext; unfold raw5147step2 raw5147step1; decide +kernel
      have hl : raw5147step1Labels = labelEmbedding1 ∘ raw5147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5147step1 raw5147step1Labels raw5147step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical5148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5148 raw5148Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw5148 raw5148Labels = mixedMoment B raw5148step0 raw5148step0Labels := by
      have hz : ∀ j, raw5148 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5148step0 = (fun i j => raw5148 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5148step0 raw5148; decide +kernel
      have hl : raw5148step0Labels = raw5148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5148 raw5148Labels permutation265 hz
    mixedMoment B raw5148step0 raw5148step0Labels = mixedMoment B raw5148step1 raw5148step1Labels := by
      have ha : raw5148step1 = (fun i j => raw5148step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5148step1 raw5148step0; decide +kernel
      have hl : raw5148step1Labels = raw5148step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5148step0 raw5148step0Labels permutation143 permutation7
    mixedMoment B raw5148step1 raw5148step1Labels = mixedMoment B raw5148step2 raw5148step2Labels := by
      have ha : raw5148step2 = raw5148step1 := by apply Matrix.ext; unfold raw5148step2 raw5148step1; decide +kernel
      have hl : raw5148step1Labels = labelEmbedding1 ∘ raw5148step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5148step1 raw5148step1Labels raw5148step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical5149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5149 raw5149Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw5149 raw5149Labels = mixedMoment B raw5149step0 raw5149step0Labels := by
      have hz : ∀ j, raw5149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5149step0 = (fun i j => raw5149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5149step0 raw5149; decide +kernel
      have hl : raw5149step0Labels = raw5149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5149 raw5149Labels permutation346 hz
    mixedMoment B raw5149step0 raw5149step0Labels = mixedMoment B raw5149step1 raw5149step1Labels := by
      have hz : ∀ j, raw5149step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5149step1 = (fun i j => raw5149step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5149step1 raw5149step0; decide +kernel
      have hl : raw5149step1Labels = raw5149step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5149step0 raw5149step0Labels permutation56 hz
    mixedMoment B raw5149step1 raw5149step1Labels = mixedMoment B raw5149step2 raw5149step2Labels := by
      have ha : raw5149step2 = (fun i j => raw5149step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5149step2 raw5149step1; decide +kernel
      have hl : raw5149step2Labels = raw5149step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5149step1 raw5149step1Labels permutation29 permutation7
    mixedMoment B raw5149step2 raw5149step2Labels = mixedMoment B raw5149step3 raw5149step3Labels := by
      have ha : raw5149step3 = raw5149step2 := by apply Matrix.ext; unfold raw5149step3 raw5149step2; decide +kernel
      have hl : raw5149step2Labels = labelEmbedding1 ∘ raw5149step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5149step2 raw5149step2Labels raw5149step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

theorem canonical5150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5150 raw5150Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw5150 raw5150Labels = mixedMoment B raw5150step0 raw5150step0Labels := by
      have hz : ∀ j, raw5150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5150step0 = (fun i j => raw5150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5150step0 raw5150; decide +kernel
      have hl : raw5150step0Labels = raw5150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5150 raw5150Labels permutation346 hz
    mixedMoment B raw5150step0 raw5150step0Labels = mixedMoment B raw5150step1 raw5150step1Labels := by
      have hz : ∀ j, raw5150step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5150step1 = (fun i j => raw5150step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5150step1 raw5150step0; decide +kernel
      have hl : raw5150step1Labels = raw5150step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5150step0 raw5150step0Labels permutation56 hz
    mixedMoment B raw5150step1 raw5150step1Labels = mixedMoment B raw5150step2 raw5150step2Labels := by
      have ha : raw5150step2 = (fun i j => raw5150step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5150step2 raw5150step1; decide +kernel
      have hl : raw5150step2Labels = raw5150step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5150step1 raw5150step1Labels permutation29 permutation7
    mixedMoment B raw5150step2 raw5150step2Labels = mixedMoment B raw5150step3 raw5150step3Labels := by
      have ha : raw5150step3 = raw5150step2 := by apply Matrix.ext; unfold raw5150step3 raw5150step2; decide +kernel
      have hl : raw5150step2Labels = labelEmbedding1 ∘ raw5150step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5150step2 raw5150step2Labels raw5150step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical5151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5151 raw5151Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw5151 raw5151Labels = mixedMoment B raw5151step0 raw5151step0Labels := by
      have hz : ∀ j, raw5151 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5151step0 = (fun i j => raw5151 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5151step0 raw5151; decide +kernel
      have hl : raw5151step0Labels = raw5151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5151 raw5151Labels permutation434 hz
    mixedMoment B raw5151step0 raw5151step0Labels = mixedMoment B raw5151step1 raw5151step1Labels := by
      have hz : ∀ j, raw5151step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5151step1 = (fun i j => raw5151step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5151step1 raw5151step0; decide +kernel
      have hl : raw5151step1Labels = raw5151step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5151step0 raw5151step0Labels permutation80 hz
    mixedMoment B raw5151step1 raw5151step1Labels = mixedMoment B raw5151step2 raw5151step2Labels := by
      have hz : ∀ j, raw5151step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5151step2 = (fun i j => raw5151step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5151step2 raw5151step1; decide +kernel
      have hl : raw5151step2Labels = raw5151step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5151step1 raw5151step1Labels permutation14 hz
    mixedMoment B raw5151step2 raw5151step2Labels = mixedMoment B raw5151step3 raw5151step3Labels := by
      have ha : raw5151step3 = (fun i j => raw5151step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5151step3 raw5151step2; decide +kernel
      have hl : raw5151step3Labels = raw5151step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5151step2 raw5151step2Labels permutation7 permutation7
    mixedMoment B raw5151step3 raw5151step3Labels = mixedMoment B raw5151step4 raw5151step4Labels := by
      have ha : raw5151step4 = raw5151step3 := by apply Matrix.ext; unfold raw5151step4 raw5151step3; decide +kernel
      have hl : raw5151step3Labels = labelEmbedding1 ∘ raw5151step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5151step3 raw5151step3Labels raw5151step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2289 node2289Labels := by rfl

theorem canonical5152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5152 raw5152Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw5152 raw5152Labels = mixedMoment B raw5152step0 raw5152step0Labels := by
      have hz : ∀ j, raw5152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5152step0 = (fun i j => raw5152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5152step0 raw5152; decide +kernel
      have hl : raw5152step0Labels = raw5152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5152 raw5152Labels permutation434 hz
    mixedMoment B raw5152step0 raw5152step0Labels = mixedMoment B raw5152step1 raw5152step1Labels := by
      have hz : ∀ j, raw5152step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5152step1 = (fun i j => raw5152step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5152step1 raw5152step0; decide +kernel
      have hl : raw5152step1Labels = raw5152step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5152step0 raw5152step0Labels permutation80 hz
    mixedMoment B raw5152step1 raw5152step1Labels = mixedMoment B raw5152step2 raw5152step2Labels := by
      have ha : raw5152step2 = (fun i j => raw5152step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5152step2 raw5152step1; decide +kernel
      have hl : raw5152step2Labels = raw5152step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5152step1 raw5152step1Labels permutation29 permutation7
    mixedMoment B raw5152step2 raw5152step2Labels = mixedMoment B raw5152step3 raw5152step3Labels := by
      have ha : raw5152step3 = raw5152step2 := by apply Matrix.ext; unfold raw5152step3 raw5152step2; decide +kernel
      have hl : raw5152step2Labels = labelEmbedding1 ∘ raw5152step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5152step2 raw5152step2Labels raw5152step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical5153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5153 raw5153Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw5153 raw5153Labels = mixedMoment B raw5153step0 raw5153step0Labels := by
      have hz : ∀ j, raw5153 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5153step0 = (fun i j => raw5153 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5153step0 raw5153; decide +kernel
      have hl : raw5153step0Labels = raw5153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5153 raw5153Labels permutation434 hz
    mixedMoment B raw5153step0 raw5153step0Labels = mixedMoment B raw5153step1 raw5153step1Labels := by
      have hz : ∀ j, raw5153step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5153step1 = (fun i j => raw5153step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5153step1 raw5153step0; decide +kernel
      have hl : raw5153step1Labels = raw5153step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5153step0 raw5153step0Labels permutation56 hz
    mixedMoment B raw5153step1 raw5153step1Labels = mixedMoment B raw5153step2 raw5153step2Labels := by
      have ha : raw5153step2 = (fun i j => raw5153step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5153step2 raw5153step1; decide +kernel
      have hl : raw5153step2Labels = raw5153step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5153step1 raw5153step1Labels permutation29 permutation7
    mixedMoment B raw5153step2 raw5153step2Labels = mixedMoment B raw5153step3 raw5153step3Labels := by
      have ha : raw5153step3 = raw5153step2 := by apply Matrix.ext; unfold raw5153step3 raw5153step2; decide +kernel
      have hl : raw5153step2Labels = labelEmbedding1 ∘ raw5153step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5153step2 raw5153step2Labels raw5153step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical5154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5154 raw5154Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw5154 raw5154Labels = mixedMoment B raw5154step0 raw5154step0Labels := by
      have hz : ∀ j, raw5154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5154step0 = (fun i j => raw5154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5154step0 raw5154; decide +kernel
      have hl : raw5154step0Labels = raw5154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5154 raw5154Labels permutation346 hz
    mixedMoment B raw5154step0 raw5154step0Labels = mixedMoment B raw5154step1 raw5154step1Labels := by
      have hz : ∀ j, raw5154step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5154step1 = (fun i j => raw5154step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5154step1 raw5154step0; decide +kernel
      have hl : raw5154step1Labels = raw5154step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5154step0 raw5154step0Labels permutation56 hz
    mixedMoment B raw5154step1 raw5154step1Labels = mixedMoment B raw5154step2 raw5154step2Labels := by
      have ha : raw5154step2 = (fun i j => raw5154step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5154step2 raw5154step1; decide +kernel
      have hl : raw5154step2Labels = raw5154step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5154step1 raw5154step1Labels permutation29 permutation7
    mixedMoment B raw5154step2 raw5154step2Labels = mixedMoment B raw5154step3 raw5154step3Labels := by
      have ha : raw5154step3 = raw5154step2 := by apply Matrix.ext; unfold raw5154step3 raw5154step2; decide +kernel
      have hl : raw5154step2Labels = labelEmbedding1 ∘ raw5154step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5154step2 raw5154step2Labels raw5154step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical5155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5155 raw5155Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw5155 raw5155Labels = mixedMoment B raw5155step0 raw5155step0Labels := by
      have hz : ∀ j, raw5155 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5155step0 = (fun i j => raw5155 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5155step0 raw5155; decide +kernel
      have hl : raw5155step0Labels = raw5155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5155 raw5155Labels permutation434 hz
    mixedMoment B raw5155step0 raw5155step0Labels = mixedMoment B raw5155step1 raw5155step1Labels := by
      have hz : ∀ j, raw5155step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5155step1 = (fun i j => raw5155step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5155step1 raw5155step0; decide +kernel
      have hl : raw5155step1Labels = raw5155step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5155step0 raw5155step0Labels permutation80 hz
    mixedMoment B raw5155step1 raw5155step1Labels = mixedMoment B raw5155step2 raw5155step2Labels := by
      have hz : ∀ j, raw5155step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5155step2 = (fun i j => raw5155step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5155step2 raw5155step1; decide +kernel
      have hl : raw5155step2Labels = raw5155step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5155step1 raw5155step1Labels permutation14 hz
    mixedMoment B raw5155step2 raw5155step2Labels = mixedMoment B raw5155step3 raw5155step3Labels := by
      have ha : raw5155step3 = (fun i j => raw5155step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5155step3 raw5155step2; decide +kernel
      have hl : raw5155step3Labels = raw5155step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5155step2 raw5155step2Labels permutation7 permutation7
    mixedMoment B raw5155step3 raw5155step3Labels = mixedMoment B raw5155step4 raw5155step4Labels := by
      have ha : raw5155step4 = raw5155step3 := by apply Matrix.ext; unfold raw5155step4 raw5155step3; decide +kernel
      have hl : raw5155step3Labels = labelEmbedding1 ∘ raw5155step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5155step3 raw5155step3Labels raw5155step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2783 node2783Labels := by rfl

theorem canonical5156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5156 raw5156Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw5156 raw5156Labels = mixedMoment B raw5156step0 raw5156step0Labels := by
      have hz : ∀ j, raw5156 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5156step0 = (fun i j => raw5156 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5156step0 raw5156; decide +kernel
      have hl : raw5156step0Labels = raw5156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5156 raw5156Labels permutation434 hz
    mixedMoment B raw5156step0 raw5156step0Labels = mixedMoment B raw5156step1 raw5156step1Labels := by
      have hz : ∀ j, raw5156step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5156step1 = (fun i j => raw5156step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5156step1 raw5156step0; decide +kernel
      have hl : raw5156step1Labels = raw5156step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5156step0 raw5156step0Labels permutation80 hz
    mixedMoment B raw5156step1 raw5156step1Labels = mixedMoment B raw5156step2 raw5156step2Labels := by
      have hz : ∀ j, raw5156step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5156step2 = (fun i j => raw5156step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5156step2 raw5156step1; decide +kernel
      have hl : raw5156step2Labels = raw5156step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5156step1 raw5156step1Labels permutation14 hz
    mixedMoment B raw5156step2 raw5156step2Labels = mixedMoment B raw5156step3 raw5156step3Labels := by
      have ha : raw5156step3 = (fun i j => raw5156step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5156step3 raw5156step2; decide +kernel
      have hl : raw5156step3Labels = raw5156step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5156step2 raw5156step2Labels permutation7 permutation7
    mixedMoment B raw5156step3 raw5156step3Labels = mixedMoment B raw5156step4 raw5156step4Labels := by
      have ha : raw5156step4 = raw5156step3 := by apply Matrix.ext; unfold raw5156step4 raw5156step3; decide +kernel
      have hl : raw5156step3Labels = labelEmbedding1 ∘ raw5156step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5156step3 raw5156step3Labels raw5156step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1752 node1752Labels := by rfl

theorem canonical5157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5157 raw5157Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw5157 raw5157Labels = mixedMoment B raw5157step0 raw5157step0Labels := by
      have hz : ∀ j, raw5157 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5157step0 = (fun i j => raw5157 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5157step0 raw5157; decide +kernel
      have hl : raw5157step0Labels = raw5157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5157 raw5157Labels permutation434 hz
    mixedMoment B raw5157step0 raw5157step0Labels = mixedMoment B raw5157step1 raw5157step1Labels := by
      have hz : ∀ j, raw5157step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5157step1 = (fun i j => raw5157step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5157step1 raw5157step0; decide +kernel
      have hl : raw5157step1Labels = raw5157step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5157step0 raw5157step0Labels permutation80 hz
    mixedMoment B raw5157step1 raw5157step1Labels = mixedMoment B raw5157step2 raw5157step2Labels := by
      have ha : raw5157step2 = (fun i j => raw5157step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5157step2 raw5157step1; decide +kernel
      have hl : raw5157step2Labels = raw5157step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5157step1 raw5157step1Labels permutation29 permutation7
    mixedMoment B raw5157step2 raw5157step2Labels = mixedMoment B raw5157step3 raw5157step3Labels := by
      have ha : raw5157step3 = raw5157step2 := by apply Matrix.ext; unfold raw5157step3 raw5157step2; decide +kernel
      have hl : raw5157step2Labels = labelEmbedding1 ∘ raw5157step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5157step2 raw5157step2Labels raw5157step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical5158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5158 raw5158Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw5158 raw5158Labels = mixedMoment B raw5158step0 raw5158step0Labels := by
      have hz : ∀ j, raw5158 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5158step0 = (fun i j => raw5158 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5158step0 raw5158; decide +kernel
      have hl : raw5158step0Labels = raw5158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5158 raw5158Labels permutation434 hz
    mixedMoment B raw5158step0 raw5158step0Labels = mixedMoment B raw5158step1 raw5158step1Labels := by
      have hz : ∀ j, raw5158step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5158step1 = (fun i j => raw5158step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5158step1 raw5158step0; decide +kernel
      have hl : raw5158step1Labels = raw5158step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5158step0 raw5158step0Labels permutation56 hz
    mixedMoment B raw5158step1 raw5158step1Labels = mixedMoment B raw5158step2 raw5158step2Labels := by
      have ha : raw5158step2 = (fun i j => raw5158step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5158step2 raw5158step1; decide +kernel
      have hl : raw5158step2Labels = raw5158step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5158step1 raw5158step1Labels permutation29 permutation7
    mixedMoment B raw5158step2 raw5158step2Labels = mixedMoment B raw5158step3 raw5158step3Labels := by
      have ha : raw5158step3 = raw5158step2 := by apply Matrix.ext; unfold raw5158step3 raw5158step2; decide +kernel
      have hl : raw5158step2Labels = labelEmbedding1 ∘ raw5158step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5158step2 raw5158step2Labels raw5158step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical5159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5159 raw5159Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw5159 raw5159Labels = mixedMoment B raw5159step0 raw5159step0Labels := by
      have hz : ∀ j, raw5159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5159step0 = (fun i j => raw5159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5159step0 raw5159; decide +kernel
      have hl : raw5159step0Labels = raw5159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5159 raw5159Labels permutation346 hz
    mixedMoment B raw5159step0 raw5159step0Labels = mixedMoment B raw5159step1 raw5159step1Labels := by
      have hz : ∀ j, raw5159step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5159step1 = (fun i j => raw5159step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5159step1 raw5159step0; decide +kernel
      have hl : raw5159step1Labels = raw5159step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5159step0 raw5159step0Labels permutation56 hz
    mixedMoment B raw5159step1 raw5159step1Labels = mixedMoment B raw5159step2 raw5159step2Labels := by
      have ha : raw5159step2 = (fun i j => raw5159step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5159step2 raw5159step1; decide +kernel
      have hl : raw5159step2Labels = raw5159step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5159step1 raw5159step1Labels permutation29 permutation7
    mixedMoment B raw5159step2 raw5159step2Labels = mixedMoment B raw5159step3 raw5159step3Labels := by
      have ha : raw5159step3 = raw5159step2 := by apply Matrix.ext; unfold raw5159step3 raw5159step2; decide +kernel
      have hl : raw5159step2Labels = labelEmbedding1 ∘ raw5159step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5159step2 raw5159step2Labels raw5159step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical5160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5160 raw5160Labels = mixedMoment B node1754 node1754Labels := by
  calc
    mixedMoment B raw5160 raw5160Labels = mixedMoment B raw5160step0 raw5160step0Labels := by
      have hz : ∀ j, raw5160 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5160step0 = (fun i j => raw5160 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5160step0 raw5160; decide +kernel
      have hl : raw5160step0Labels = raw5160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5160 raw5160Labels permutation434 hz
    mixedMoment B raw5160step0 raw5160step0Labels = mixedMoment B raw5160step1 raw5160step1Labels := by
      have hz : ∀ j, raw5160step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5160step1 = (fun i j => raw5160step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5160step1 raw5160step0; decide +kernel
      have hl : raw5160step1Labels = raw5160step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5160step0 raw5160step0Labels permutation80 hz
    mixedMoment B raw5160step1 raw5160step1Labels = mixedMoment B raw5160step2 raw5160step2Labels := by
      have hz : ∀ j, raw5160step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5160step2 = (fun i j => raw5160step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5160step2 raw5160step1; decide +kernel
      have hl : raw5160step2Labels = raw5160step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5160step1 raw5160step1Labels permutation14 hz
    mixedMoment B raw5160step2 raw5160step2Labels = mixedMoment B raw5160step3 raw5160step3Labels := by
      have ha : raw5160step3 = (fun i j => raw5160step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5160step3 raw5160step2; decide +kernel
      have hl : raw5160step3Labels = raw5160step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5160step2 raw5160step2Labels permutation7 permutation7
    mixedMoment B raw5160step3 raw5160step3Labels = mixedMoment B raw5160step4 raw5160step4Labels := by
      have ha : raw5160step4 = raw5160step3 := by apply Matrix.ext; unfold raw5160step4 raw5160step3; decide +kernel
      have hl : raw5160step3Labels = labelEmbedding1 ∘ raw5160step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5160step3 raw5160step3Labels raw5160step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1754 node1754Labels := by rfl

theorem canonical5161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5161 raw5161Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw5161 raw5161Labels = mixedMoment B raw5161step0 raw5161step0Labels := by
      have hz : ∀ j, raw5161 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5161step0 = (fun i j => raw5161 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5161step0 raw5161; decide +kernel
      have hl : raw5161step0Labels = raw5161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5161 raw5161Labels permutation434 hz
    mixedMoment B raw5161step0 raw5161step0Labels = mixedMoment B raw5161step1 raw5161step1Labels := by
      have hz : ∀ j, raw5161step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5161step1 = (fun i j => raw5161step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5161step1 raw5161step0; decide +kernel
      have hl : raw5161step1Labels = raw5161step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5161step0 raw5161step0Labels permutation80 hz
    mixedMoment B raw5161step1 raw5161step1Labels = mixedMoment B raw5161step2 raw5161step2Labels := by
      have hz : ∀ j, raw5161step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5161step2 = (fun i j => raw5161step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5161step2 raw5161step1; decide +kernel
      have hl : raw5161step2Labels = raw5161step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5161step1 raw5161step1Labels permutation14 hz
    mixedMoment B raw5161step2 raw5161step2Labels = mixedMoment B raw5161step3 raw5161step3Labels := by
      have ha : raw5161step3 = (fun i j => raw5161step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5161step3 raw5161step2; decide +kernel
      have hl : raw5161step3Labels = raw5161step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5161step2 raw5161step2Labels permutation7 permutation2
    mixedMoment B raw5161step3 raw5161step3Labels = mixedMoment B raw5161step4 raw5161step4Labels := by
      have ha : raw5161step4 = -raw5161step3 := by apply Matrix.ext; change ∀ i j, raw5161step4 i j = -(raw5161step3 i j); unfold raw5161step4 raw5161step3; decide +kernel
      have hl : raw5161step4Labels = raw5161step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2268 node2268Labels := by rfl

theorem canonical5162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5162 raw5162Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw5162 raw5162Labels = mixedMoment B raw5162step0 raw5162step0Labels := by
      have hz : ∀ j, raw5162 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5162step0 = (fun i j => raw5162 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5162step0 raw5162; decide +kernel
      have hl : raw5162step0Labels = raw5162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5162 raw5162Labels permutation434 hz
    mixedMoment B raw5162step0 raw5162step0Labels = mixedMoment B raw5162step1 raw5162step1Labels := by
      have hz : ∀ j, raw5162step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5162step1 = (fun i j => raw5162step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5162step1 raw5162step0; decide +kernel
      have hl : raw5162step1Labels = raw5162step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5162step0 raw5162step0Labels permutation80 hz
    mixedMoment B raw5162step1 raw5162step1Labels = mixedMoment B raw5162step2 raw5162step2Labels := by
      have ha : raw5162step2 = (fun i j => raw5162step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5162step2 raw5162step1; decide +kernel
      have hl : raw5162step2Labels = raw5162step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5162step1 raw5162step1Labels permutation10 permutation2
    _ = mixedMoment B node1239 node1239Labels := by rfl

theorem canonical5163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5163 raw5163Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw5163 raw5163Labels = mixedMoment B raw5163step0 raw5163step0Labels := by
      have hz : ∀ j, raw5163 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5163step0 = (fun i j => raw5163 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5163step0 raw5163; decide +kernel
      have hl : raw5163step0Labels = raw5163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5163 raw5163Labels permutation434 hz
    mixedMoment B raw5163step0 raw5163step0Labels = mixedMoment B raw5163step1 raw5163step1Labels := by
      have hz : ∀ j, raw5163step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5163step1 = (fun i j => raw5163step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5163step1 raw5163step0; decide +kernel
      have hl : raw5163step1Labels = raw5163step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5163step0 raw5163step0Labels permutation56 hz
    mixedMoment B raw5163step1 raw5163step1Labels = mixedMoment B raw5163step2 raw5163step2Labels := by
      have ha : raw5163step2 = (fun i j => raw5163step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5163step2 raw5163step1; decide +kernel
      have hl : raw5163step2Labels = raw5163step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5163step1 raw5163step1Labels permutation10 permutation2
    _ = mixedMoment B node1239 node1239Labels := by rfl

theorem canonical5164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5164 raw5164Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw5164 raw5164Labels = mixedMoment B raw5164step0 raw5164step0Labels := by
      have hz : ∀ j, raw5164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5164step0 = (fun i j => raw5164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5164step0 raw5164; decide +kernel
      have hl : raw5164step0Labels = raw5164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5164 raw5164Labels permutation346 hz
    mixedMoment B raw5164step0 raw5164step0Labels = mixedMoment B raw5164step1 raw5164step1Labels := by
      have hz : ∀ j, raw5164step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5164step1 = (fun i j => raw5164step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5164step1 raw5164step0; decide +kernel
      have hl : raw5164step1Labels = raw5164step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5164step0 raw5164step0Labels permutation56 hz
    mixedMoment B raw5164step1 raw5164step1Labels = mixedMoment B raw5164step2 raw5164step2Labels := by
      have ha : raw5164step2 = (fun i j => raw5164step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5164step2 raw5164step1; decide +kernel
      have hl : raw5164step2Labels = raw5164step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5164step1 raw5164step1Labels permutation10 permutation2
    _ = mixedMoment B node1239 node1239Labels := by rfl

theorem canonical5165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5165 raw5165Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw5165 raw5165Labels = mixedMoment B raw5165step0 raw5165step0Labels := by
      have hz : ∀ j, raw5165 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5165step0 = (fun i j => raw5165 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5165step0 raw5165; decide +kernel
      have hl : raw5165step0Labels = raw5165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5165 raw5165Labels permutation434 hz
    mixedMoment B raw5165step0 raw5165step0Labels = mixedMoment B raw5165step1 raw5165step1Labels := by
      have hz : ∀ j, raw5165step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5165step1 = (fun i j => raw5165step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5165step1 raw5165step0; decide +kernel
      have hl : raw5165step1Labels = raw5165step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5165step0 raw5165step0Labels permutation80 hz
    mixedMoment B raw5165step1 raw5165step1Labels = mixedMoment B raw5165step2 raw5165step2Labels := by
      have hz : ∀ j, raw5165step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5165step2 = (fun i j => raw5165step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5165step2 raw5165step1; decide +kernel
      have hl : raw5165step2Labels = raw5165step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5165step1 raw5165step1Labels permutation14 hz
    _ = mixedMoment B node1297 node1297Labels := by rfl

theorem canonical5166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5166 raw5166Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw5166 raw5166Labels = mixedMoment B raw5166step0 raw5166step0Labels := by
      have hz : ∀ j, raw5166 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5166step0 = (fun i j => raw5166 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5166step0 raw5166; decide +kernel
      have hl : raw5166step0Labels = raw5166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5166 raw5166Labels permutation434 hz
    mixedMoment B raw5166step0 raw5166step0Labels = mixedMoment B raw5166step1 raw5166step1Labels := by
      have hz : ∀ j, raw5166step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5166step1 = (fun i j => raw5166step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5166step1 raw5166step0; decide +kernel
      have hl : raw5166step1Labels = raw5166step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5166step0 raw5166step0Labels permutation80 hz
    mixedMoment B raw5166step1 raw5166step1Labels = mixedMoment B raw5166step2 raw5166step2Labels := by
      have hz : ∀ j, raw5166step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5166step2 = (fun i j => raw5166step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5166step2 raw5166step1; decide +kernel
      have hl : raw5166step2Labels = raw5166step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5166step1 raw5166step1Labels permutation14 hz
    mixedMoment B raw5166step2 raw5166step2Labels = mixedMoment B raw5166step3 raw5166step3Labels := by
      have ha : raw5166step3 = (fun i j => raw5166step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5166step3 raw5166step2; decide +kernel
      have hl : raw5166step3Labels = raw5166step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5166step2 raw5166step2Labels permutation7 permutation2
    mixedMoment B raw5166step3 raw5166step3Labels = mixedMoment B raw5166step4 raw5166step4Labels := by
      have ha : raw5166step4 = -raw5166step3 := by apply Matrix.ext; change ∀ i j, raw5166step4 i j = -(raw5166step3 i j); unfold raw5166step4 raw5166step3; decide +kernel
      have hl : raw5166step4Labels = raw5166step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1051 node1051Labels := by rfl

theorem canonical5167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5167 raw5167Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5167 raw5167Labels = mixedMoment B raw5167step0 raw5167step0Labels := by
      have hz : ∀ j, raw5167 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5167step0 = (fun i j => raw5167 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5167step0 raw5167; decide +kernel
      have hl : raw5167step0Labels = raw5167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5167 raw5167Labels permutation434 hz
    mixedMoment B raw5167step0 raw5167step0Labels = mixedMoment B raw5167step1 raw5167step1Labels := by
      have hz : ∀ j, raw5167step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5167step1 = (fun i j => raw5167step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5167step1 raw5167step0; decide +kernel
      have hl : raw5167step1Labels = raw5167step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5167step0 raw5167step0Labels permutation80 hz
    mixedMoment B raw5167step1 raw5167step1Labels = mixedMoment B raw5167step2 raw5167step2Labels := by
      have hz : ∀ j, raw5167step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5167step2 = (fun i j => raw5167step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5167step2 raw5167step1; decide +kernel
      have hl : raw5167step2Labels = raw5167step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5167step1 raw5167step1Labels permutation14 hz
    mixedMoment B raw5167step2 raw5167step2Labels = mixedMoment B raw5167step3 raw5167step3Labels := by
      have ha : raw5167step3 = (fun i j => raw5167step2 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5167step3 raw5167step2; decide +kernel
      have hl : raw5167step3Labels = raw5167step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5167step2 raw5167step2Labels permutation7 permutation0
    mixedMoment B raw5167step3 raw5167step3Labels = mixedMoment B raw5167step4 raw5167step4Labels := by
      have ha : raw5167step4 = -raw5167step3 := by apply Matrix.ext; change ∀ i j, raw5167step4 i j = -(raw5167step3 i j); unfold raw5167step4 raw5167step3; decide +kernel
      have hl : raw5167step4Labels = raw5167step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical5168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5168 raw5168Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw5168 raw5168Labels = mixedMoment B raw5168step0 raw5168step0Labels := by
      have hz : ∀ j, raw5168 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5168step0 = (fun i j => raw5168 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5168step0 raw5168; decide +kernel
      have hl : raw5168step0Labels = raw5168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5168 raw5168Labels permutation434 hz
    mixedMoment B raw5168step0 raw5168step0Labels = mixedMoment B raw5168step1 raw5168step1Labels := by
      have ha : raw5168step1 = (fun i j => raw5168step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5168step1 raw5168step0; decide +kernel
      have hl : raw5168step1Labels = raw5168step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5168step0 raw5168step0Labels permutation139 permutation2
    mixedMoment B raw5168step1 raw5168step1Labels = mixedMoment B raw5168step2 raw5168step2Labels := by
      have ha : raw5168step2 = -raw5168step1 := by apply Matrix.ext; change ∀ i j, raw5168step2 i j = -(raw5168step1 i j); unfold raw5168step2 raw5168step1; decide +kernel
      have hl : raw5168step2Labels = raw5168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical5169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5169 raw5169Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw5169 raw5169Labels = mixedMoment B raw5169step0 raw5169step0Labels := by
      have hz : ∀ j, raw5169 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5169step0 = (fun i j => raw5169 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5169step0 raw5169; decide +kernel
      have hl : raw5169step0Labels = raw5169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5169 raw5169Labels permutation346 hz
    mixedMoment B raw5169step0 raw5169step0Labels = mixedMoment B raw5169step1 raw5169step1Labels := by
      have ha : raw5169step1 = (fun i j => raw5169step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5169step1 raw5169step0; decide +kernel
      have hl : raw5169step1Labels = raw5169step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5169step0 raw5169step0Labels permutation139 permutation2
    mixedMoment B raw5169step1 raw5169step1Labels = mixedMoment B raw5169step2 raw5169step2Labels := by
      have ha : raw5169step2 = -raw5169step1 := by apply Matrix.ext; change ∀ i j, raw5169step2 i j = -(raw5169step1 i j); unfold raw5169step2 raw5169step1; decide +kernel
      have hl : raw5169step2Labels = raw5169step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical5170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5170 raw5170Labels = mixedMoment B node2060 node2060Labels := by
  calc
    mixedMoment B raw5170 raw5170Labels = mixedMoment B raw5170step0 raw5170step0Labels := by
      have hz : ∀ j, raw5170 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5170step0 = (fun i j => raw5170 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5170step0 raw5170; decide +kernel
      have hl : raw5170step0Labels = raw5170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5170 raw5170Labels permutation434 hz
    mixedMoment B raw5170step0 raw5170step0Labels = mixedMoment B raw5170step1 raw5170step1Labels := by
      have hz : ∀ j, raw5170step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5170step1 = (fun i j => raw5170step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5170step1 raw5170step0; decide +kernel
      have hl : raw5170step1Labels = raw5170step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5170step0 raw5170step0Labels permutation80 hz
    mixedMoment B raw5170step1 raw5170step1Labels = mixedMoment B raw5170step2 raw5170step2Labels := by
      have ha : raw5170step2 = (fun i j => raw5170step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5170step2 raw5170step1; decide +kernel
      have hl : raw5170step2Labels = raw5170step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5170step1 raw5170step1Labels permutation29 permutation2
    mixedMoment B raw5170step2 raw5170step2Labels = mixedMoment B raw5170step3 raw5170step3Labels := by
      have ha : raw5170step3 = -raw5170step2 := by apply Matrix.ext; change ∀ i j, raw5170step3 i j = -(raw5170step2 i j); unfold raw5170step3 raw5170step2; decide +kernel
      have hl : raw5170step3Labels = raw5170step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2060 node2060Labels := by rfl

theorem canonical5171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5171 raw5171Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw5171 raw5171Labels = mixedMoment B raw5171step0 raw5171step0Labels := by
      have hz : ∀ j, raw5171 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5171step0 = (fun i j => raw5171 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5171step0 raw5171; decide +kernel
      have hl : raw5171step0Labels = raw5171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5171 raw5171Labels permutation434 hz
    mixedMoment B raw5171step0 raw5171step0Labels = mixedMoment B raw5171step1 raw5171step1Labels := by
      have hz : ∀ j, raw5171step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5171step1 = (fun i j => raw5171step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5171step1 raw5171step0; decide +kernel
      have hl : raw5171step1Labels = raw5171step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5171step0 raw5171step0Labels permutation80 hz
    mixedMoment B raw5171step1 raw5171step1Labels = mixedMoment B raw5171step2 raw5171step2Labels := by
      have ha : raw5171step2 = (fun i j => raw5171step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5171step2 raw5171step1; decide +kernel
      have hl : raw5171step2Labels = raw5171step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5171step1 raw5171step1Labels permutation10 permutation2
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical5172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5172 raw5172Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw5172 raw5172Labels = mixedMoment B raw5172step0 raw5172step0Labels := by
      have hz : ∀ j, raw5172 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5172step0 = (fun i j => raw5172 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5172step0 raw5172; decide +kernel
      have hl : raw5172step0Labels = raw5172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5172 raw5172Labels permutation434 hz
    mixedMoment B raw5172step0 raw5172step0Labels = mixedMoment B raw5172step1 raw5172step1Labels := by
      have hz : ∀ j, raw5172step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5172step1 = (fun i j => raw5172step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5172step1 raw5172step0; decide +kernel
      have hl : raw5172step1Labels = raw5172step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5172step0 raw5172step0Labels permutation80 hz
    mixedMoment B raw5172step1 raw5172step1Labels = mixedMoment B raw5172step2 raw5172step2Labels := by
      have ha : raw5172step2 = (fun i j => raw5172step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5172step2 raw5172step1; decide +kernel
      have hl : raw5172step2Labels = raw5172step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5172step1 raw5172step1Labels permutation31 permutation2
    mixedMoment B raw5172step2 raw5172step2Labels = mixedMoment B raw5172step3 raw5172step3Labels := by
      have ha : raw5172step3 = -raw5172step2 := by apply Matrix.ext; change ∀ i j, raw5172step3 i j = -(raw5172step2 i j); unfold raw5172step3 raw5172step2; decide +kernel
      have hl : raw5172step3Labels = raw5172step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical5173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5173 raw5173Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw5173 raw5173Labels = mixedMoment B raw5173step0 raw5173step0Labels := by
      have hz : ∀ j, raw5173 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5173step0 = (fun i j => raw5173 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5173step0 raw5173; decide +kernel
      have hl : raw5173step0Labels = raw5173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5173 raw5173Labels permutation434 hz
    mixedMoment B raw5173step0 raw5173step0Labels = mixedMoment B raw5173step1 raw5173step1Labels := by
      have ha : raw5173step1 = (fun i j => raw5173step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5173step1 raw5173step0; decide +kernel
      have hl : raw5173step1Labels = raw5173step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5173step0 raw5173step0Labels permutation145 permutation2
    mixedMoment B raw5173step1 raw5173step1Labels = mixedMoment B raw5173step2 raw5173step2Labels := by
      have ha : raw5173step2 = -raw5173step1 := by apply Matrix.ext; change ∀ i j, raw5173step2 i j = -(raw5173step1 i j); unfold raw5173step2 raw5173step1; decide +kernel
      have hl : raw5173step2Labels = raw5173step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical5174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5174 raw5174Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw5174 raw5174Labels = mixedMoment B raw5174step0 raw5174step0Labels := by
      have hz : ∀ j, raw5174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5174step0 = (fun i j => raw5174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5174step0 raw5174; decide +kernel
      have hl : raw5174step0Labels = raw5174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5174 raw5174Labels permutation346 hz
    mixedMoment B raw5174step0 raw5174step0Labels = mixedMoment B raw5174step1 raw5174step1Labels := by
      have ha : raw5174step1 = (fun i j => raw5174step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5174step1 raw5174step0; decide +kernel
      have hl : raw5174step1Labels = raw5174step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5174step0 raw5174step0Labels permutation145 permutation2
    mixedMoment B raw5174step1 raw5174step1Labels = mixedMoment B raw5174step2 raw5174step2Labels := by
      have ha : raw5174step2 = -raw5174step1 := by apply Matrix.ext; change ∀ i j, raw5174step2 i j = -(raw5174step1 i j); unfold raw5174step2 raw5174step1; decide +kernel
      have hl : raw5174step2Labels = raw5174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical5175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5175 raw5175Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw5175 raw5175Labels = mixedMoment B raw5175step0 raw5175step0Labels := by
      have hz : ∀ j, raw5175 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5175step0 = (fun i j => raw5175 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5175step0 raw5175; decide +kernel
      have hl : raw5175step0Labels = raw5175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5175 raw5175Labels permutation434 hz
    mixedMoment B raw5175step0 raw5175step0Labels = mixedMoment B raw5175step1 raw5175step1Labels := by
      have hz : ∀ j, raw5175step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5175step1 = (fun i j => raw5175step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5175step1 raw5175step0; decide +kernel
      have hl : raw5175step1Labels = raw5175step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5175step0 raw5175step0Labels permutation80 hz
    mixedMoment B raw5175step1 raw5175step1Labels = mixedMoment B raw5175step2 raw5175step2Labels := by
      have ha : raw5175step2 = (fun i j => raw5175step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5175step2 raw5175step1; decide +kernel
      have hl : raw5175step2Labels = raw5175step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5175step1 raw5175step1Labels permutation31 permutation2
    mixedMoment B raw5175step2 raw5175step2Labels = mixedMoment B raw5175step3 raw5175step3Labels := by
      have ha : raw5175step3 = -raw5175step2 := by apply Matrix.ext; change ∀ i j, raw5175step3 i j = -(raw5175step2 i j); unfold raw5175step3 raw5175step2; decide +kernel
      have hl : raw5175step3Labels = raw5175step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2109 node2109Labels := by rfl

theorem canonical5176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5176 raw5176Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw5176 raw5176Labels = mixedMoment B raw5176step0 raw5176step0Labels := by
      have hz : ∀ j, raw5176 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5176step0 = (fun i j => raw5176 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5176step0 raw5176; decide +kernel
      have hl : raw5176step0Labels = raw5176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5176 raw5176Labels permutation434 hz
    mixedMoment B raw5176step0 raw5176step0Labels = mixedMoment B raw5176step1 raw5176step1Labels := by
      have hz : ∀ j, raw5176step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5176step1 = (fun i j => raw5176step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5176step1 raw5176step0; decide +kernel
      have hl : raw5176step1Labels = raw5176step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5176step0 raw5176step0Labels permutation80 hz
    mixedMoment B raw5176step1 raw5176step1Labels = mixedMoment B raw5176step2 raw5176step2Labels := by
      have ha : raw5176step2 = (fun i j => raw5176step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5176step2 raw5176step1; decide +kernel
      have hl : raw5176step2Labels = raw5176step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5176step1 raw5176step1Labels permutation31 permutation2
    mixedMoment B raw5176step2 raw5176step2Labels = mixedMoment B raw5176step3 raw5176step3Labels := by
      have ha : raw5176step3 = -raw5176step2 := by apply Matrix.ext; change ∀ i j, raw5176step3 i j = -(raw5176step2 i j); unfold raw5176step3 raw5176step2; decide +kernel
      have hl : raw5176step3Labels = raw5176step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1043 node1043Labels := by rfl

theorem canonical5177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5177 raw5177Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw5177 raw5177Labels = mixedMoment B raw5177step0 raw5177step0Labels := by
      have hz : ∀ j, raw5177 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5177step0 = (fun i j => raw5177 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5177step0 raw5177; decide +kernel
      have hl : raw5177step0Labels = raw5177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5177 raw5177Labels permutation434 hz
    mixedMoment B raw5177step0 raw5177step0Labels = mixedMoment B raw5177step1 raw5177step1Labels := by
      have hz : ∀ j, raw5177step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5177step1 = (fun i j => raw5177step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5177step1 raw5177step0; decide +kernel
      have hl : raw5177step1Labels = raw5177step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5177step0 raw5177step0Labels permutation56 hz
    mixedMoment B raw5177step1 raw5177step1Labels = mixedMoment B raw5177step2 raw5177step2Labels := by
      have ha : raw5177step2 = (fun i j => raw5177step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5177step2 raw5177step1; decide +kernel
      have hl : raw5177step2Labels = raw5177step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5177step1 raw5177step1Labels permutation31 permutation2
    mixedMoment B raw5177step2 raw5177step2Labels = mixedMoment B raw5177step3 raw5177step3Labels := by
      have ha : raw5177step3 = -raw5177step2 := by apply Matrix.ext; change ∀ i j, raw5177step3 i j = -(raw5177step2 i j); unfold raw5177step3 raw5177step2; decide +kernel
      have hl : raw5177step3Labels = raw5177step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2109 node2109Labels := by rfl

theorem canonical5178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5178 raw5178Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw5178 raw5178Labels = mixedMoment B raw5178step0 raw5178step0Labels := by
      have hz : ∀ j, raw5178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5178step0 = (fun i j => raw5178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5178step0 raw5178; decide +kernel
      have hl : raw5178step0Labels = raw5178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5178 raw5178Labels permutation346 hz
    mixedMoment B raw5178step0 raw5178step0Labels = mixedMoment B raw5178step1 raw5178step1Labels := by
      have hz : ∀ j, raw5178step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5178step1 = (fun i j => raw5178step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5178step1 raw5178step0; decide +kernel
      have hl : raw5178step1Labels = raw5178step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5178step0 raw5178step0Labels permutation56 hz
    mixedMoment B raw5178step1 raw5178step1Labels = mixedMoment B raw5178step2 raw5178step2Labels := by
      have ha : raw5178step2 = (fun i j => raw5178step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5178step2 raw5178step1; decide +kernel
      have hl : raw5178step2Labels = raw5178step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5178step1 raw5178step1Labels permutation31 permutation2
    mixedMoment B raw5178step2 raw5178step2Labels = mixedMoment B raw5178step3 raw5178step3Labels := by
      have ha : raw5178step3 = -raw5178step2 := by apply Matrix.ext; change ∀ i j, raw5178step3 i j = -(raw5178step2 i j); unfold raw5178step3 raw5178step2; decide +kernel
      have hl : raw5178step3Labels = raw5178step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2109 node2109Labels := by rfl

theorem canonical5179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5179 raw5179Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw5179 raw5179Labels = mixedMoment B raw5179step0 raw5179step0Labels := by
      have hz : ∀ j, raw5179 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5179step0 = (fun i j => raw5179 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5179step0 raw5179; decide +kernel
      have hl : raw5179step0Labels = raw5179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5179 raw5179Labels permutation434 hz
    mixedMoment B raw5179step0 raw5179step0Labels = mixedMoment B raw5179step1 raw5179step1Labels := by
      have hz : ∀ j, raw5179step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5179step1 = (fun i j => raw5179step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5179step1 raw5179step0; decide +kernel
      have hl : raw5179step1Labels = raw5179step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5179step0 raw5179step0Labels permutation80 hz
    mixedMoment B raw5179step1 raw5179step1Labels = mixedMoment B raw5179step2 raw5179step2Labels := by
      have hz : ∀ j, raw5179step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5179step2 = (fun i j => raw5179step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5179step2 raw5179step1; decide +kernel
      have hl : raw5179step2Labels = raw5179step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5179step1 raw5179step1Labels permutation14 hz
    _ = mixedMoment B node2783 node2783Labels := by rfl

theorem canonical5197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5197 raw5197Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5197 raw5197Labels = mixedMoment B raw5197step0 raw5197step0Labels := by
      have hz : ∀ j, raw5197 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5197step0 = (fun i j => raw5197 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5197step0 raw5197; decide +kernel
      have hl : raw5197step0Labels = raw5197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5197 raw5197Labels permutation520 hz
    mixedMoment B raw5197step0 raw5197step0Labels = mixedMoment B raw5197step1 raw5197step1Labels := by
      have hz : ∀ j, raw5197step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5197step1 = (fun i j => raw5197step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5197step1 raw5197step0; decide +kernel
      have hl : raw5197step1Labels = raw5197step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5197step0 raw5197step0Labels permutation104 hz
    mixedMoment B raw5197step1 raw5197step1Labels = mixedMoment B raw5197step2 raw5197step2Labels := by
      have hz : ∀ j, raw5197step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5197step2 = (fun i j => raw5197step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5197step2 raw5197step1; decide +kernel
      have hl : raw5197step2Labels = raw5197step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5197step1 raw5197step1Labels permutation20 hz
    mixedMoment B raw5197step2 raw5197step2Labels = mixedMoment B raw5197step3 raw5197step3Labels := by
      have hz : ∀ i, raw5197step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5197step3 = (fun i j => raw5197step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5197step3 raw5197step2; decide +kernel
      have hl : raw5197step3Labels = (fun j => raw5197step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5197step2 raw5197step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5198 raw5198Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5198 raw5198Labels = mixedMoment B raw5198step0 raw5198step0Labels := by
      have hz : ∀ j, raw5198 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5198step0 = (fun i j => raw5198 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5198step0 raw5198; decide +kernel
      have hl : raw5198step0Labels = raw5198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5198 raw5198Labels permutation520 hz
    mixedMoment B raw5198step0 raw5198step0Labels = mixedMoment B raw5198step1 raw5198step1Labels := by
      have hz : ∀ j, raw5198step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5198step1 = (fun i j => raw5198step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5198step1 raw5198step0; decide +kernel
      have hl : raw5198step1Labels = raw5198step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5198step0 raw5198step0Labels permutation104 hz
    mixedMoment B raw5198step1 raw5198step1Labels = mixedMoment B raw5198step2 raw5198step2Labels := by
      have hz : ∀ i, raw5198step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5198step2 = (fun i j => raw5198step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5198step2 raw5198step1; decide +kernel
      have hl : raw5198step2Labels = (fun j => raw5198step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5198step1 raw5198step1Labels permutation6 hz
    mixedMoment B raw5198step2 raw5198step2Labels = mixedMoment B raw5198step3 raw5198step3Labels := by
      have ha : raw5198step3 = (fun i j => raw5198step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5198step3 raw5198step2; decide +kernel
      have hl : raw5198step3Labels = raw5198step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5198step2 raw5198step2Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5199 raw5199Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5199 raw5199Labels = mixedMoment B raw5199step0 raw5199step0Labels := by
      have hz : ∀ j, raw5199 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5199step0 = (fun i j => raw5199 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5199step0 raw5199; decide +kernel
      have hl : raw5199step0Labels = raw5199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5199 raw5199Labels permutation520 hz
    mixedMoment B raw5199step0 raw5199step0Labels = mixedMoment B raw5199step1 raw5199step1Labels := by
      have hz : ∀ j, raw5199step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5199step1 = (fun i j => raw5199step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5199step1 raw5199step0; decide +kernel
      have hl : raw5199step1Labels = raw5199step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5199step0 raw5199step0Labels permutation80 hz
    mixedMoment B raw5199step1 raw5199step1Labels = mixedMoment B raw5199step2 raw5199step2Labels := by
      have hz : ∀ i, raw5199step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5199step2 = (fun i j => raw5199step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5199step2 raw5199step1; decide +kernel
      have hl : raw5199step2Labels = (fun j => raw5199step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5199step1 raw5199step1Labels permutation6 hz
    mixedMoment B raw5199step2 raw5199step2Labels = mixedMoment B raw5199step3 raw5199step3Labels := by
      have ha : raw5199step3 = (fun i j => raw5199step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5199step3 raw5199step2; decide +kernel
      have hl : raw5199step3Labels = raw5199step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5199step2 raw5199step2Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5200 raw5200Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5200 raw5200Labels = mixedMoment B raw5200step0 raw5200step0Labels := by
      have hz : ∀ j, raw5200 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5200step0 = (fun i j => raw5200 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5200step0 raw5200; decide +kernel
      have hl : raw5200step0Labels = raw5200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5200 raw5200Labels permutation434 hz
    mixedMoment B raw5200step0 raw5200step0Labels = mixedMoment B raw5200step1 raw5200step1Labels := by
      have hz : ∀ j, raw5200step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5200step1 = (fun i j => raw5200step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5200step1 raw5200step0; decide +kernel
      have hl : raw5200step1Labels = raw5200step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5200step0 raw5200step0Labels permutation80 hz
    mixedMoment B raw5200step1 raw5200step1Labels = mixedMoment B raw5200step2 raw5200step2Labels := by
      have hz : ∀ i, raw5200step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5200step2 = (fun i j => raw5200step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5200step2 raw5200step1; decide +kernel
      have hl : raw5200step2Labels = (fun j => raw5200step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5200step1 raw5200step1Labels permutation6 hz
    mixedMoment B raw5200step2 raw5200step2Labels = mixedMoment B raw5200step3 raw5200step3Labels := by
      have ha : raw5200step3 = (fun i j => raw5200step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5200step3 raw5200step2; decide +kernel
      have hl : raw5200step3Labels = raw5200step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5200step2 raw5200step2Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5201 raw5201Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5201 raw5201Labels = mixedMoment B raw5201step0 raw5201step0Labels := by
      have hz : ∀ j, raw5201 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5201step0 = (fun i j => raw5201 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5201step0 raw5201; decide +kernel
      have hl : raw5201step0Labels = raw5201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5201 raw5201Labels permutation520 hz
    mixedMoment B raw5201step0 raw5201step0Labels = mixedMoment B raw5201step1 raw5201step1Labels := by
      have hz : ∀ j, raw5201step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5201step1 = (fun i j => raw5201step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5201step1 raw5201step0; decide +kernel
      have hl : raw5201step1Labels = raw5201step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5201step0 raw5201step0Labels permutation104 hz
    mixedMoment B raw5201step1 raw5201step1Labels = mixedMoment B raw5201step2 raw5201step2Labels := by
      have hz : ∀ j, raw5201step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5201step2 = (fun i j => raw5201step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5201step2 raw5201step1; decide +kernel
      have hl : raw5201step2Labels = raw5201step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5201step1 raw5201step1Labels permutation14 hz
    mixedMoment B raw5201step2 raw5201step2Labels = mixedMoment B raw5201step3 raw5201step3Labels := by
      have hz : ∀ i, raw5201step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5201step3 = (fun i j => raw5201step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5201step3 raw5201step2; decide +kernel
      have hl : raw5201step3Labels = (fun j => raw5201step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5201step2 raw5201step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5202 raw5202Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5202 raw5202Labels = mixedMoment B raw5202step0 raw5202step0Labels := by
      have hz : ∀ j, raw5202 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5202step0 = (fun i j => raw5202 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5202step0 raw5202; decide +kernel
      have hl : raw5202step0Labels = raw5202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5202 raw5202Labels permutation520 hz
    mixedMoment B raw5202step0 raw5202step0Labels = mixedMoment B raw5202step1 raw5202step1Labels := by
      have hz : ∀ j, raw5202step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5202step1 = (fun i j => raw5202step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5202step1 raw5202step0; decide +kernel
      have hl : raw5202step1Labels = raw5202step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5202step0 raw5202step0Labels permutation104 hz
    mixedMoment B raw5202step1 raw5202step1Labels = mixedMoment B raw5202step2 raw5202step2Labels := by
      have hz : ∀ i, raw5202step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5202step2 = (fun i j => raw5202step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5202step2 raw5202step1; decide +kernel
      have hl : raw5202step2Labels = (fun j => raw5202step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5202step1 raw5202step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5203 raw5203Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5203 raw5203Labels = mixedMoment B raw5203step0 raw5203step0Labels := by
      have hz : ∀ j, raw5203 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5203step0 = (fun i j => raw5203 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5203step0 raw5203; decide +kernel
      have hl : raw5203step0Labels = raw5203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5203 raw5203Labels permutation520 hz
    mixedMoment B raw5203step0 raw5203step0Labels = mixedMoment B raw5203step1 raw5203step1Labels := by
      have hz : ∀ j, raw5203step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5203step1 = (fun i j => raw5203step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5203step1 raw5203step0; decide +kernel
      have hl : raw5203step1Labels = raw5203step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5203step0 raw5203step0Labels permutation56 hz
    mixedMoment B raw5203step1 raw5203step1Labels = mixedMoment B raw5203step2 raw5203step2Labels := by
      have hz : ∀ i, raw5203step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5203step2 = (fun i j => raw5203step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5203step2 raw5203step1; decide +kernel
      have hl : raw5203step2Labels = (fun j => raw5203step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5203step1 raw5203step1Labels permutation6 hz
    mixedMoment B raw5203step2 raw5203step2Labels = mixedMoment B raw5203step3 raw5203step3Labels := by
      have ha : raw5203step3 = (fun i j => raw5203step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5203step3 raw5203step2; decide +kernel
      have hl : raw5203step3Labels = raw5203step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5203step2 raw5203step2Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5204 raw5204Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5204 raw5204Labels = mixedMoment B raw5204step0 raw5204step0Labels := by
      have hz : ∀ j, raw5204 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5204step0 = (fun i j => raw5204 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5204step0 raw5204; decide +kernel
      have hl : raw5204step0Labels = raw5204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5204 raw5204Labels permutation434 hz
    mixedMoment B raw5204step0 raw5204step0Labels = mixedMoment B raw5204step1 raw5204step1Labels := by
      have hz : ∀ j, raw5204step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5204step1 = (fun i j => raw5204step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5204step1 raw5204step0; decide +kernel
      have hl : raw5204step1Labels = raw5204step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5204step0 raw5204step0Labels permutation56 hz
    mixedMoment B raw5204step1 raw5204step1Labels = mixedMoment B raw5204step2 raw5204step2Labels := by
      have hz : ∀ i, raw5204step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5204step2 = (fun i j => raw5204step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5204step2 raw5204step1; decide +kernel
      have hl : raw5204step2Labels = (fun j => raw5204step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5204step1 raw5204step1Labels permutation6 hz
    mixedMoment B raw5204step2 raw5204step2Labels = mixedMoment B raw5204step3 raw5204step3Labels := by
      have ha : raw5204step3 = (fun i j => raw5204step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5204step3 raw5204step2; decide +kernel
      have hl : raw5204step3Labels = raw5204step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5204step2 raw5204step2Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5205 raw5205Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5205 raw5205Labels = mixedMoment B raw5205step0 raw5205step0Labels := by
      have hz : ∀ j, raw5205 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5205step0 = (fun i j => raw5205 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5205step0 raw5205; decide +kernel
      have hl : raw5205step0Labels = raw5205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5205 raw5205Labels permutation520 hz
    mixedMoment B raw5205step0 raw5205step0Labels = mixedMoment B raw5205step1 raw5205step1Labels := by
      have hz : ∀ j, raw5205step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5205step1 = (fun i j => raw5205step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5205step1 raw5205step0; decide +kernel
      have hl : raw5205step1Labels = raw5205step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5205step0 raw5205step0Labels permutation80 hz
    mixedMoment B raw5205step1 raw5205step1Labels = mixedMoment B raw5205step2 raw5205step2Labels := by
      have hz : ∀ j, raw5205step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5205step2 = (fun i j => raw5205step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5205step2 raw5205step1; decide +kernel
      have hl : raw5205step2Labels = raw5205step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5205step1 raw5205step1Labels permutation14 hz
    mixedMoment B raw5205step2 raw5205step2Labels = mixedMoment B raw5205step3 raw5205step3Labels := by
      have hz : ∀ i, raw5205step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5205step3 = (fun i j => raw5205step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5205step3 raw5205step2; decide +kernel
      have hl : raw5205step3Labels = (fun j => raw5205step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5205step2 raw5205step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5206 raw5206Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5206 raw5206Labels = mixedMoment B raw5206step0 raw5206step0Labels := by
      have hz : ∀ j, raw5206 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5206step0 = (fun i j => raw5206 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5206step0 raw5206; decide +kernel
      have hl : raw5206step0Labels = raw5206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5206 raw5206Labels permutation520 hz
    mixedMoment B raw5206step0 raw5206step0Labels = mixedMoment B raw5206step1 raw5206step1Labels := by
      have hz : ∀ j, raw5206step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5206step1 = (fun i j => raw5206step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5206step1 raw5206step0; decide +kernel
      have hl : raw5206step1Labels = raw5206step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5206step0 raw5206step0Labels permutation80 hz
    mixedMoment B raw5206step1 raw5206step1Labels = mixedMoment B raw5206step2 raw5206step2Labels := by
      have hz : ∀ i, raw5206step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5206step2 = (fun i j => raw5206step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5206step2 raw5206step1; decide +kernel
      have hl : raw5206step2Labels = (fun j => raw5206step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5206step1 raw5206step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5207 raw5207Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5207 raw5207Labels = mixedMoment B raw5207step0 raw5207step0Labels := by
      have hz : ∀ j, raw5207 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5207step0 = (fun i j => raw5207 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5207step0 raw5207; decide +kernel
      have hl : raw5207step0Labels = raw5207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5207 raw5207Labels permutation520 hz
    mixedMoment B raw5207step0 raw5207step0Labels = mixedMoment B raw5207step1 raw5207step1Labels := by
      have hz : ∀ j, raw5207step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5207step1 = (fun i j => raw5207step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5207step1 raw5207step0; decide +kernel
      have hl : raw5207step1Labels = raw5207step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5207step0 raw5207step0Labels permutation56 hz
    mixedMoment B raw5207step1 raw5207step1Labels = mixedMoment B raw5207step2 raw5207step2Labels := by
      have hz : ∀ i, raw5207step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5207step2 = (fun i j => raw5207step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5207step2 raw5207step1; decide +kernel
      have hl : raw5207step2Labels = (fun j => raw5207step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5207step1 raw5207step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5208 raw5208Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5208 raw5208Labels = mixedMoment B raw5208step0 raw5208step0Labels := by
      have hz : ∀ j, raw5208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5208step0 = (fun i j => raw5208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5208step0 raw5208; decide +kernel
      have hl : raw5208step0Labels = raw5208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5208 raw5208Labels permutation346 hz
    mixedMoment B raw5208step0 raw5208step0Labels = mixedMoment B raw5208step1 raw5208step1Labels := by
      have hz : ∀ j, raw5208step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5208step1 = (fun i j => raw5208step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5208step1 raw5208step0; decide +kernel
      have hl : raw5208step1Labels = raw5208step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5208step0 raw5208step0Labels permutation56 hz
    mixedMoment B raw5208step1 raw5208step1Labels = mixedMoment B raw5208step2 raw5208step2Labels := by
      have hz : ∀ i, raw5208step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5208step2 = (fun i j => raw5208step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5208step2 raw5208step1; decide +kernel
      have hl : raw5208step2Labels = (fun j => raw5208step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5208step1 raw5208step1Labels permutation6 hz
    mixedMoment B raw5208step2 raw5208step2Labels = mixedMoment B raw5208step3 raw5208step3Labels := by
      have ha : raw5208step3 = (fun i j => raw5208step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5208step3 raw5208step2; decide +kernel
      have hl : raw5208step3Labels = raw5208step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5208step2 raw5208step2Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5209 raw5209Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5209 raw5209Labels = mixedMoment B raw5209step0 raw5209step0Labels := by
      have hz : ∀ j, raw5209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5209step0 = (fun i j => raw5209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5209step0 raw5209; decide +kernel
      have hl : raw5209step0Labels = raw5209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5209 raw5209Labels permutation434 hz
    mixedMoment B raw5209step0 raw5209step0Labels = mixedMoment B raw5209step1 raw5209step1Labels := by
      have hz : ∀ j, raw5209step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5209step1 = (fun i j => raw5209step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5209step1 raw5209step0; decide +kernel
      have hl : raw5209step1Labels = raw5209step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5209step0 raw5209step0Labels permutation80 hz
    mixedMoment B raw5209step1 raw5209step1Labels = mixedMoment B raw5209step2 raw5209step2Labels := by
      have hz : ∀ j, raw5209step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5209step2 = (fun i j => raw5209step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5209step2 raw5209step1; decide +kernel
      have hl : raw5209step2Labels = raw5209step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5209step1 raw5209step1Labels permutation14 hz
    mixedMoment B raw5209step2 raw5209step2Labels = mixedMoment B raw5209step3 raw5209step3Labels := by
      have hz : ∀ i, raw5209step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5209step3 = (fun i j => raw5209step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5209step3 raw5209step2; decide +kernel
      have hl : raw5209step3Labels = (fun j => raw5209step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5209step2 raw5209step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5210 raw5210Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5210 raw5210Labels = mixedMoment B raw5210step0 raw5210step0Labels := by
      have hz : ∀ j, raw5210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5210step0 = (fun i j => raw5210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5210step0 raw5210; decide +kernel
      have hl : raw5210step0Labels = raw5210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5210 raw5210Labels permutation434 hz
    mixedMoment B raw5210step0 raw5210step0Labels = mixedMoment B raw5210step1 raw5210step1Labels := by
      have hz : ∀ j, raw5210step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5210step1 = (fun i j => raw5210step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5210step1 raw5210step0; decide +kernel
      have hl : raw5210step1Labels = raw5210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5210step0 raw5210step0Labels permutation80 hz
    mixedMoment B raw5210step1 raw5210step1Labels = mixedMoment B raw5210step2 raw5210step2Labels := by
      have hz : ∀ i, raw5210step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5210step2 = (fun i j => raw5210step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5210step2 raw5210step1; decide +kernel
      have hl : raw5210step2Labels = (fun j => raw5210step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5210step1 raw5210step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5211 raw5211Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5211 raw5211Labels = mixedMoment B raw5211step0 raw5211step0Labels := by
      have hz : ∀ j, raw5211 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5211step0 = (fun i j => raw5211 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5211step0 raw5211; decide +kernel
      have hl : raw5211step0Labels = raw5211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5211 raw5211Labels permutation434 hz
    mixedMoment B raw5211step0 raw5211step0Labels = mixedMoment B raw5211step1 raw5211step1Labels := by
      have hz : ∀ j, raw5211step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5211step1 = (fun i j => raw5211step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5211step1 raw5211step0; decide +kernel
      have hl : raw5211step1Labels = raw5211step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5211step0 raw5211step0Labels permutation56 hz
    mixedMoment B raw5211step1 raw5211step1Labels = mixedMoment B raw5211step2 raw5211step2Labels := by
      have hz : ∀ i, raw5211step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5211step2 = (fun i j => raw5211step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5211step2 raw5211step1; decide +kernel
      have hl : raw5211step2Labels = (fun j => raw5211step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5211step1 raw5211step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5212 raw5212Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5212 raw5212Labels = mixedMoment B raw5212step0 raw5212step0Labels := by
      have hz : ∀ j, raw5212 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5212step0 = (fun i j => raw5212 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5212step0 raw5212; decide +kernel
      have hl : raw5212step0Labels = raw5212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5212 raw5212Labels permutation346 hz
    mixedMoment B raw5212step0 raw5212step0Labels = mixedMoment B raw5212step1 raw5212step1Labels := by
      have hz : ∀ j, raw5212step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5212step1 = (fun i j => raw5212step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5212step1 raw5212step0; decide +kernel
      have hl : raw5212step1Labels = raw5212step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5212step0 raw5212step0Labels permutation56 hz
    mixedMoment B raw5212step1 raw5212step1Labels = mixedMoment B raw5212step2 raw5212step2Labels := by
      have hz : ∀ i, raw5212step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5212step2 = (fun i j => raw5212step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5212step2 raw5212step1; decide +kernel
      have hl : raw5212step2Labels = (fun j => raw5212step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5212step1 raw5212step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5213 raw5213Labels = mixedMoment B node4072 node4072Labels := by
  calc
    mixedMoment B raw5213 raw5213Labels = mixedMoment B raw5213step0 raw5213step0Labels := by
      have hz : ∀ j, raw5213 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5213step0 = (fun i j => raw5213 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5213step0 raw5213; decide +kernel
      have hl : raw5213step0Labels = raw5213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5213 raw5213Labels permutation520 hz
    mixedMoment B raw5213step0 raw5213step0Labels = mixedMoment B raw5213step1 raw5213step1Labels := by
      have hz : ∀ j, raw5213step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5213step1 = (fun i j => raw5213step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5213step1 raw5213step0; decide +kernel
      have hl : raw5213step1Labels = raw5213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5213step0 raw5213step0Labels permutation104 hz
    mixedMoment B raw5213step1 raw5213step1Labels = mixedMoment B raw5213step2 raw5213step2Labels := by
      have hz : ∀ j, raw5213step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5213step2 = (fun i j => raw5213step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5213step2 raw5213step1; decide +kernel
      have hl : raw5213step2Labels = raw5213step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5213step1 raw5213step1Labels permutation20 hz
    mixedMoment B raw5213step2 raw5213step2Labels = mixedMoment B raw5213step3 raw5213step3Labels := by
      have hz : ∀ j, raw5213step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw5213step3 = (fun i j => raw5213step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw5213step3 raw5213step2; decide +kernel
      have hl : raw5213step3Labels = raw5213step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5213step2 raw5213step2Labels permutation4 hz
    mixedMoment B raw5213step3 raw5213step3Labels = mixedMoment B raw5213step4 raw5213step4Labels := by
      have hz : ∀ i, raw5213step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5213step4 = (fun i j => raw5213step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5213step4 raw5213step3; decide +kernel
      have hl : raw5213step4Labels = (fun j => raw5213step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5213step3 raw5213step3Labels permutation6 hz
    _ = mixedMoment B node4072 node4072Labels := by rfl

theorem canonical5214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5214 raw5214Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5214 raw5214Labels = mixedMoment B raw5214step0 raw5214step0Labels := by
      have hz : ∀ j, raw5214 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5214step0 = (fun i j => raw5214 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5214step0 raw5214; decide +kernel
      have hl : raw5214step0Labels = raw5214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5214 raw5214Labels permutation520 hz
    mixedMoment B raw5214step0 raw5214step0Labels = mixedMoment B raw5214step1 raw5214step1Labels := by
      have hz : ∀ j, raw5214step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5214step1 = (fun i j => raw5214step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5214step1 raw5214step0; decide +kernel
      have hl : raw5214step1Labels = raw5214step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5214step0 raw5214step0Labels permutation104 hz
    mixedMoment B raw5214step1 raw5214step1Labels = mixedMoment B raw5214step2 raw5214step2Labels := by
      have hz : ∀ j, raw5214step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5214step2 = (fun i j => raw5214step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5214step2 raw5214step1; decide +kernel
      have hl : raw5214step2Labels = raw5214step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5214step1 raw5214step1Labels permutation20 hz
    mixedMoment B raw5214step2 raw5214step2Labels = mixedMoment B raw5214step3 raw5214step3Labels := by
      have hz : ∀ i, raw5214step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5214step3 = (fun i j => raw5214step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5214step3 raw5214step2; decide +kernel
      have hl : raw5214step3Labels = (fun j => raw5214step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5214step2 raw5214step2Labels permutation6 hz
    mixedMoment B raw5214step3 raw5214step3Labels = mixedMoment B raw5214step4 raw5214step4Labels := by
      have ha : raw5214step4 = (fun i j => raw5214step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5214step4 raw5214step3; decide +kernel
      have hl : raw5214step4Labels = raw5214step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5214step3 raw5214step3Labels permutation7 permutation0
    mixedMoment B raw5214step4 raw5214step4Labels = mixedMoment B raw5214step5 raw5214step5Labels := by
      have ha : raw5214step5 = -raw5214step4 := by apply Matrix.ext; change ∀ i j, raw5214step5 i j = -(raw5214step4 i j); unfold raw5214step5 raw5214step4; decide +kernel
      have hl : raw5214step5Labels = raw5214step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5215 raw5215Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5215 raw5215Labels = mixedMoment B raw5215step0 raw5215step0Labels := by
      have hz : ∀ j, raw5215 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5215step0 = (fun i j => raw5215 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5215step0 raw5215; decide +kernel
      have hl : raw5215step0Labels = raw5215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5215 raw5215Labels permutation520 hz
    mixedMoment B raw5215step0 raw5215step0Labels = mixedMoment B raw5215step1 raw5215step1Labels := by
      have hz : ∀ j, raw5215step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5215step1 = (fun i j => raw5215step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5215step1 raw5215step0; decide +kernel
      have hl : raw5215step1Labels = raw5215step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5215step0 raw5215step0Labels permutation104 hz
    mixedMoment B raw5215step1 raw5215step1Labels = mixedMoment B raw5215step2 raw5215step2Labels := by
      have hz : ∀ j, raw5215step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5215step2 = (fun i j => raw5215step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5215step2 raw5215step1; decide +kernel
      have hl : raw5215step2Labels = raw5215step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5215step1 raw5215step1Labels permutation14 hz
    mixedMoment B raw5215step2 raw5215step2Labels = mixedMoment B raw5215step3 raw5215step3Labels := by
      have hz : ∀ i, raw5215step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5215step3 = (fun i j => raw5215step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5215step3 raw5215step2; decide +kernel
      have hl : raw5215step3Labels = (fun j => raw5215step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5215step2 raw5215step2Labels permutation6 hz
    mixedMoment B raw5215step3 raw5215step3Labels = mixedMoment B raw5215step4 raw5215step4Labels := by
      have ha : raw5215step4 = (fun i j => raw5215step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5215step4 raw5215step3; decide +kernel
      have hl : raw5215step4Labels = raw5215step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5215step3 raw5215step3Labels permutation7 permutation0
    mixedMoment B raw5215step4 raw5215step4Labels = mixedMoment B raw5215step5 raw5215step5Labels := by
      have ha : raw5215step5 = -raw5215step4 := by apply Matrix.ext; change ∀ i j, raw5215step5 i j = -(raw5215step4 i j); unfold raw5215step5 raw5215step4; decide +kernel
      have hl : raw5215step5Labels = raw5215step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5216 raw5216Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5216 raw5216Labels = mixedMoment B raw5216step0 raw5216step0Labels := by
      have hz : ∀ j, raw5216 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5216step0 = (fun i j => raw5216 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5216step0 raw5216; decide +kernel
      have hl : raw5216step0Labels = raw5216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5216 raw5216Labels permutation520 hz
    mixedMoment B raw5216step0 raw5216step0Labels = mixedMoment B raw5216step1 raw5216step1Labels := by
      have hz : ∀ j, raw5216step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5216step1 = (fun i j => raw5216step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5216step1 raw5216step0; decide +kernel
      have hl : raw5216step1Labels = raw5216step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5216step0 raw5216step0Labels permutation80 hz
    mixedMoment B raw5216step1 raw5216step1Labels = mixedMoment B raw5216step2 raw5216step2Labels := by
      have hz : ∀ j, raw5216step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5216step2 = (fun i j => raw5216step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5216step2 raw5216step1; decide +kernel
      have hl : raw5216step2Labels = raw5216step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5216step1 raw5216step1Labels permutation14 hz
    mixedMoment B raw5216step2 raw5216step2Labels = mixedMoment B raw5216step3 raw5216step3Labels := by
      have hz : ∀ i, raw5216step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5216step3 = (fun i j => raw5216step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5216step3 raw5216step2; decide +kernel
      have hl : raw5216step3Labels = (fun j => raw5216step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5216step2 raw5216step2Labels permutation6 hz
    mixedMoment B raw5216step3 raw5216step3Labels = mixedMoment B raw5216step4 raw5216step4Labels := by
      have ha : raw5216step4 = (fun i j => raw5216step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5216step4 raw5216step3; decide +kernel
      have hl : raw5216step4Labels = raw5216step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5216step3 raw5216step3Labels permutation7 permutation0
    mixedMoment B raw5216step4 raw5216step4Labels = mixedMoment B raw5216step5 raw5216step5Labels := by
      have ha : raw5216step5 = -raw5216step4 := by apply Matrix.ext; change ∀ i j, raw5216step5 i j = -(raw5216step4 i j); unfold raw5216step5 raw5216step4; decide +kernel
      have hl : raw5216step5Labels = raw5216step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5217 raw5217Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5217 raw5217Labels = mixedMoment B raw5217step0 raw5217step0Labels := by
      have hz : ∀ j, raw5217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5217step0 = (fun i j => raw5217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5217step0 raw5217; decide +kernel
      have hl : raw5217step0Labels = raw5217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5217 raw5217Labels permutation434 hz
    mixedMoment B raw5217step0 raw5217step0Labels = mixedMoment B raw5217step1 raw5217step1Labels := by
      have hz : ∀ j, raw5217step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5217step1 = (fun i j => raw5217step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5217step1 raw5217step0; decide +kernel
      have hl : raw5217step1Labels = raw5217step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5217step0 raw5217step0Labels permutation80 hz
    mixedMoment B raw5217step1 raw5217step1Labels = mixedMoment B raw5217step2 raw5217step2Labels := by
      have hz : ∀ j, raw5217step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5217step2 = (fun i j => raw5217step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5217step2 raw5217step1; decide +kernel
      have hl : raw5217step2Labels = raw5217step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5217step1 raw5217step1Labels permutation14 hz
    mixedMoment B raw5217step2 raw5217step2Labels = mixedMoment B raw5217step3 raw5217step3Labels := by
      have hz : ∀ i, raw5217step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5217step3 = (fun i j => raw5217step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5217step3 raw5217step2; decide +kernel
      have hl : raw5217step3Labels = (fun j => raw5217step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5217step2 raw5217step2Labels permutation6 hz
    mixedMoment B raw5217step3 raw5217step3Labels = mixedMoment B raw5217step4 raw5217step4Labels := by
      have ha : raw5217step4 = (fun i j => raw5217step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5217step4 raw5217step3; decide +kernel
      have hl : raw5217step4Labels = raw5217step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5217step3 raw5217step3Labels permutation7 permutation0
    mixedMoment B raw5217step4 raw5217step4Labels = mixedMoment B raw5217step5 raw5217step5Labels := by
      have ha : raw5217step5 = -raw5217step4 := by apply Matrix.ext; change ∀ i j, raw5217step5 i j = -(raw5217step4 i j); unfold raw5217step5 raw5217step4; decide +kernel
      have hl : raw5217step5Labels = raw5217step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5308 raw5308Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw5308 raw5308Labels = mixedMoment B raw5308step0 raw5308step0Labels := by
      have hz : ∀ j, raw5308 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5308step0 = (fun i j => raw5308 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5308step0 raw5308; decide +kernel
      have hl : raw5308step0Labels = raw5308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5308 raw5308Labels permutation265 hz
    _ = mixedMoment B node2253 node2253Labels := by rfl

theorem canonical5309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5309 raw5309Labels = mixedMoment B node3528 node3528Labels := by
  calc
    _ = mixedMoment B node3528 node3528Labels := by rfl

theorem canonical5310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5310 raw5310Labels = mixedMoment B node3577 node3577Labels := by
  calc
    mixedMoment B raw5310 raw5310Labels = mixedMoment B raw5310step0 raw5310step0Labels := by
      have hz : ∀ j, raw5310 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5310step0 = (fun i j => raw5310 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5310step0 raw5310; decide +kernel
      have hl : raw5310step0Labels = raw5310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5310 raw5310Labels permutation265 hz
    _ = mixedMoment B node3577 node3577Labels := by rfl

theorem canonical5311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5311 raw5311Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw5311 raw5311Labels = mixedMoment B raw5311step0 raw5311step0Labels := by
      have hz : ∀ j, raw5311 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5311step0 = (fun i j => raw5311 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5311step0 raw5311; decide +kernel
      have hl : raw5311step0Labels = raw5311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5311 raw5311Labels permutation265 hz
    mixedMoment B raw5311step0 raw5311step0Labels = mixedMoment B raw5311step1 raw5311step1Labels := by
      have ha : raw5311step1 = (fun i j => raw5311step0 (permutation88 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5311step1 raw5311step0; decide +kernel
      have hl : raw5311step1Labels = raw5311step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5311step0 raw5311step0Labels permutation88 permutation4
    mixedMoment B raw5311step1 raw5311step1Labels = mixedMoment B raw5311step2 raw5311step2Labels := by
      have ha : raw5311step2 = -raw5311step1 := by apply Matrix.ext; change ∀ i j, raw5311step2 i j = -(raw5311step1 i j); unfold raw5311step2 raw5311step1; decide +kernel
      have hl : raw5311step2Labels = raw5311step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2513 node2513Labels := by rfl

theorem canonical5312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5312 raw5312Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw5312 raw5312Labels = mixedMoment B raw5312step0 raw5312step0Labels := by
      have hz : ∀ j, raw5312 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5312step0 = (fun i j => raw5312 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5312step0 raw5312; decide +kernel
      have hl : raw5312step0Labels = raw5312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5312 raw5312Labels permutation520 hz
    mixedMoment B raw5312step0 raw5312step0Labels = mixedMoment B raw5312step1 raw5312step1Labels := by
      have hz : ∀ j, raw5312step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5312step1 = (fun i j => raw5312step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5312step1 raw5312step0; decide +kernel
      have hl : raw5312step1Labels = raw5312step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5312step0 raw5312step0Labels permutation56 hz
    _ = mixedMoment B node3626 node3626Labels := by rfl

theorem canonical5313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5313 raw5313Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw5313 raw5313Labels = mixedMoment B raw5313step0 raw5313step0Labels := by
      have hz : ∀ j, raw5313 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5313step0 = (fun i j => raw5313 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5313step0 raw5313; decide +kernel
      have hl : raw5313step0Labels = raw5313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5313 raw5313Labels permutation265 hz
    _ = mixedMoment B node3625 node3625Labels := by rfl

theorem canonical5314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5314 raw5314Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5314 raw5314Labels = mixedMoment B raw5314step0 raw5314step0Labels := by
      have hz : ∀ j, raw5314 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw5314step0 = (fun i j => raw5314 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw5314step0 raw5314; decide +kernel
      have hl : raw5314step0Labels = raw5314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5314 raw5314Labels permutation590 hz
    mixedMoment B raw5314step0 raw5314step0Labels = mixedMoment B raw5314step1 raw5314step1Labels := by
      have hz : ∀ j, raw5314step0 (permutation128 0) j = 0 := by decide +kernel
      have ha : raw5314step1 = (fun i j => raw5314step0 (permutation128 i.succ) j) := by apply Matrix.ext; unfold raw5314step1 raw5314step0; decide +kernel
      have hl : raw5314step1Labels = raw5314step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5314step0 raw5314step0Labels permutation128 hz
    mixedMoment B raw5314step1 raw5314step1Labels = mixedMoment B raw5314step2 raw5314step2Labels := by
      have hz : ∀ j, raw5314step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5314step2 = (fun i j => raw5314step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5314step2 raw5314step1; decide +kernel
      have hl : raw5314step2Labels = raw5314step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5314step1 raw5314step1Labels permutation14 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical5315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5315 raw5315Labels = mixedMoment B node1028 node1028Labels := by
  calc
    mixedMoment B raw5315 raw5315Labels = mixedMoment B raw5315step0 raw5315step0Labels := by
      have ha : raw5315step0 = (fun i j => raw5315 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5315step0 raw5315; decide +kernel
      have hl : raw5315step0Labels = raw5315Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5315 raw5315Labels permutation182 permutation2
    _ = mixedMoment B node1028 node1028Labels := by rfl

theorem canonical5316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5316 raw5316Labels = mixedMoment B node1058 node1058Labels := by
  calc
    mixedMoment B raw5316 raw5316Labels = mixedMoment B raw5316step0 raw5316step0Labels := by
      have hz : ∀ j, raw5316 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5316step0 = (fun i j => raw5316 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5316step0 raw5316; decide +kernel
      have hl : raw5316step0Labels = raw5316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5316 raw5316Labels permutation265 hz
    mixedMoment B raw5316step0 raw5316step0Labels = mixedMoment B raw5316step1 raw5316step1Labels := by
      have ha : raw5316step1 = (fun i j => raw5316step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5316step1 raw5316step0; decide +kernel
      have hl : raw5316step1Labels = raw5316step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5316step0 raw5316step0Labels permutation40 permutation2
    _ = mixedMoment B node1058 node1058Labels := by rfl

theorem canonical5317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5317 raw5317Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw5317 raw5317Labels = mixedMoment B raw5317step0 raw5317step0Labels := by
      have hz : ∀ j, raw5317 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5317step0 = (fun i j => raw5317 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5317step0 raw5317; decide +kernel
      have hl : raw5317step0Labels = raw5317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5317 raw5317Labels permutation265 hz
    mixedMoment B raw5317step0 raw5317step0Labels = mixedMoment B raw5317step1 raw5317step1Labels := by
      have ha : raw5317step1 = (fun i j => raw5317step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5317step1 raw5317step0; decide +kernel
      have hl : raw5317step1Labels = raw5317step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5317step0 raw5317step0Labels permutation34 permutation2
    _ = mixedMoment B node1042 node1042Labels := by rfl

theorem canonical5318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5318 raw5318Labels = mixedMoment B node1030 node1030Labels := by
  calc
    mixedMoment B raw5318 raw5318Labels = mixedMoment B raw5318step0 raw5318step0Labels := by
      have hz : ∀ j, raw5318 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5318step0 = (fun i j => raw5318 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5318step0 raw5318; decide +kernel
      have hl : raw5318step0Labels = raw5318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5318 raw5318Labels permutation265 hz
    _ = mixedMoment B node1030 node1030Labels := by rfl

theorem canonical5319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5319 raw5319Labels = mixedMoment B node1029 node1029Labels := by
  calc
    mixedMoment B raw5319 raw5319Labels = mixedMoment B raw5319step0 raw5319step0Labels := by
      have hz : ∀ j, raw5319 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5319step0 = (fun i j => raw5319 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5319step0 raw5319; decide +kernel
      have hl : raw5319step0Labels = raw5319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5319 raw5319Labels permutation265 hz
    _ = mixedMoment B node1029 node1029Labels := by rfl

theorem canonical5320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5320 raw5320Labels = mixedMoment B node2095 node2095Labels := by
  calc
    mixedMoment B raw5320 raw5320Labels = mixedMoment B raw5320step0 raw5320step0Labels := by
      have ha : raw5320step0 = (fun i j => raw5320 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5320step0 raw5320; decide +kernel
      have hl : raw5320step0Labels = raw5320Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5320 raw5320Labels permutation182 permutation2
    _ = mixedMoment B node2095 node2095Labels := by rfl

theorem canonical5321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5321 raw5321Labels = mixedMoment B node2124 node2124Labels := by
  calc
    mixedMoment B raw5321 raw5321Labels = mixedMoment B raw5321step0 raw5321step0Labels := by
      have ha : raw5321step0 = (fun i j => raw5321 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5321step0 raw5321; decide +kernel
      have hl : raw5321step0Labels = raw5321Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5321 raw5321Labels permutation206 permutation2
    _ = mixedMoment B node2124 node2124Labels := by rfl

theorem canonical5322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5322 raw5322Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw5322 raw5322Labels = mixedMoment B raw5322step0 raw5322step0Labels := by
      have hz : ∀ j, raw5322 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5322step0 = (fun i j => raw5322 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5322step0 raw5322; decide +kernel
      have hl : raw5322step0Labels = raw5322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5322 raw5322Labels permutation520 hz
    mixedMoment B raw5322step0 raw5322step0Labels = mixedMoment B raw5322step1 raw5322step1Labels := by
      have ha : raw5322step1 = (fun i j => raw5322step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5322step1 raw5322step0; decide +kernel
      have hl : raw5322step1Labels = raw5322step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5322step0 raw5322step0Labels permutation40 permutation2
    _ = mixedMoment B node2253 node2253Labels := by rfl

theorem canonical5323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5323 raw5323Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw5323 raw5323Labels = mixedMoment B raw5323step0 raw5323step0Labels := by
      have ha : raw5323step0 = (fun i j => raw5323 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5323step0 raw5323; decide +kernel
      have hl : raw5323step0Labels = raw5323Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5323 raw5323Labels permutation182 permutation2
    _ = mixedMoment B node2252 node2252Labels := by rfl

theorem canonical5324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5324 raw5324Labels = mixedMoment B node2034 node2034Labels := by
  calc
    mixedMoment B raw5324 raw5324Labels = mixedMoment B raw5324step0 raw5324step0Labels := by
      have ha : raw5324step0 = (fun i j => raw5324 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5324step0 raw5324; decide +kernel
      have hl : raw5324step0Labels = raw5324Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5324 raw5324Labels permutation160 permutation2
    _ = mixedMoment B node2034 node2034Labels := by rfl

theorem canonical5325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5325 raw5325Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw5325 raw5325Labels = mixedMoment B raw5325step0 raw5325step0Labels := by
      have ha : raw5325step0 = (fun i j => raw5325 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5325step0 raw5325; decide +kernel
      have hl : raw5325step0Labels = raw5325Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5325 raw5325Labels permutation154 permutation2
    _ = mixedMoment B node2021 node2021Labels := by rfl

theorem canonical5326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5326 raw5326Labels = mixedMoment B node2014 node2014Labels := by
  calc
    _ = mixedMoment B node2014 node2014Labels := by rfl

theorem canonical5327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5327 raw5327Labels = mixedMoment B node2013 node2013Labels := by
  calc
    _ = mixedMoment B node2013 node2013Labels := by rfl

theorem canonical5328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5328 raw5328Labels = mixedMoment B node2133 node2133Labels := by
  calc
    mixedMoment B raw5328 raw5328Labels = mixedMoment B raw5328step0 raw5328step0Labels := by
      have hz : ∀ j, raw5328 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5328step0 = (fun i j => raw5328 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5328step0 raw5328; decide +kernel
      have hl : raw5328step0Labels = raw5328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5328 raw5328Labels permutation265 hz
    mixedMoment B raw5328step0 raw5328step0Labels = mixedMoment B raw5328step1 raw5328step1Labels := by
      have ha : raw5328step1 = (fun i j => raw5328step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5328step1 raw5328step0; decide +kernel
      have hl : raw5328step1Labels = raw5328step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5328step0 raw5328step0Labels permutation40 permutation2
    _ = mixedMoment B node2133 node2133Labels := by rfl

theorem canonical5329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5329 raw5329Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw5329 raw5329Labels = mixedMoment B raw5329step0 raw5329step0Labels := by
      have hz : ∀ j, raw5329 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5329step0 = (fun i j => raw5329 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5329step0 raw5329; decide +kernel
      have hl : raw5329step0Labels = raw5329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5329 raw5329Labels permutation520 hz
    mixedMoment B raw5329step0 raw5329step0Labels = mixedMoment B raw5329step1 raw5329step1Labels := by
      have hz : ∀ j, raw5329step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5329step1 = (fun i j => raw5329step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5329step1 raw5329step0; decide +kernel
      have hl : raw5329step1Labels = raw5329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5329step0 raw5329step0Labels permutation56 hz
    mixedMoment B raw5329step1 raw5329step1Labels = mixedMoment B raw5329step2 raw5329step2Labels := by
      have ha : raw5329step2 = (fun i j => raw5329step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5329step2 raw5329step1; decide +kernel
      have hl : raw5329step2Labels = raw5329step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5329step1 raw5329step1Labels permutation10 permutation2
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical5330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5330 raw5330Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw5330 raw5330Labels = mixedMoment B raw5330step0 raw5330step0Labels := by
      have hz : ∀ j, raw5330 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5330step0 = (fun i j => raw5330 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5330step0 raw5330; decide +kernel
      have hl : raw5330step0Labels = raw5330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5330 raw5330Labels permutation265 hz
    mixedMoment B raw5330step0 raw5330step0Labels = mixedMoment B raw5330step1 raw5330step1Labels := by
      have ha : raw5330step1 = (fun i j => raw5330step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5330step1 raw5330step0; decide +kernel
      have hl : raw5330step1Labels = raw5330step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5330step0 raw5330step0Labels permutation41 permutation2
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical5331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5331 raw5331Labels = mixedMoment B node2108 node2108Labels := by
  calc
    mixedMoment B raw5331 raw5331Labels = mixedMoment B raw5331step0 raw5331step0Labels := by
      have hz : ∀ j, raw5331 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5331step0 = (fun i j => raw5331 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5331step0 raw5331; decide +kernel
      have hl : raw5331step0Labels = raw5331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5331 raw5331Labels permutation265 hz
    mixedMoment B raw5331step0 raw5331step0Labels = mixedMoment B raw5331step1 raw5331step1Labels := by
      have ha : raw5331step1 = (fun i j => raw5331step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5331step1 raw5331step0; decide +kernel
      have hl : raw5331step1Labels = raw5331step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5331step0 raw5331step0Labels permutation34 permutation2
    _ = mixedMoment B node2108 node2108Labels := by rfl

theorem canonical5332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5332 raw5332Labels = mixedMoment B node2097 node2097Labels := by
  calc
    mixedMoment B raw5332 raw5332Labels = mixedMoment B raw5332step0 raw5332step0Labels := by
      have hz : ∀ j, raw5332 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5332step0 = (fun i j => raw5332 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5332step0 raw5332; decide +kernel
      have hl : raw5332step0Labels = raw5332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5332 raw5332Labels permutation265 hz
    _ = mixedMoment B node2097 node2097Labels := by rfl

theorem canonical5333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5333 raw5333Labels = mixedMoment B node2096 node2096Labels := by
  calc
    mixedMoment B raw5333 raw5333Labels = mixedMoment B raw5333step0 raw5333step0Labels := by
      have hz : ∀ j, raw5333 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5333step0 = (fun i j => raw5333 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5333step0 raw5333; decide +kernel
      have hl : raw5333step0Labels = raw5333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5333 raw5333Labels permutation265 hz
    _ = mixedMoment B node2096 node2096Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw662 raw662Labels = mixedMoment B node4094 node4094Labels := by
  calc
    _ = mixedMoment B node4094 node4094Labels := by rfl

theorem canonical663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw663 raw663Labels = mixedMoment B node6 node6Labels := by
  calc
    _ = mixedMoment B node6 node6Labels := by rfl

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

theorem canonical1263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1263 raw1263Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw1263 raw1263Labels = mixedMoment B raw1263step0 raw1263step0Labels := by
      have ha : raw1263step0 = (fun i j => raw1263 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1263step0 raw1263; decide +kernel
      have hl : raw1263step0Labels = raw1263Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1263 raw1263Labels permutation8 permutation4
    mixedMoment B raw1263step0 raw1263step0Labels = mixedMoment B raw1263step1 raw1263step1Labels := by
      have ha : raw1263step1 = raw1263step0 := by apply Matrix.ext; unfold raw1263step1 raw1263step0; decide +kernel
      have hl : raw1263step0Labels = labelEmbedding7 ∘ raw1263step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1263step0 raw1263step0Labels raw1263step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical1264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1264 raw1264Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw1264 raw1264Labels = mixedMoment B raw1264step0 raw1264step0Labels := by
      have ha : raw1264step0 = (fun i j => raw1264 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1264step0 raw1264; decide +kernel
      have hl : raw1264step0Labels = raw1264Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1264 raw1264Labels permutation8 permutation4
    _ = mixedMoment B node1043 node1043Labels := by rfl

theorem canonical1265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1265 raw1265Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw1265 raw1265Labels = mixedMoment B raw1265step0 raw1265step0Labels := by
      have ha : raw1265step0 = (fun i j => raw1265 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1265step0 raw1265; decide +kernel
      have hl : raw1265step0Labels = raw1265Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1265 raw1265Labels permutation10 permutation6
    mixedMoment B raw1265step0 raw1265step0Labels = mixedMoment B raw1265step1 raw1265step1Labels := by
      have ha : raw1265step1 = -raw1265step0 := by apply Matrix.ext; change ∀ i j, raw1265step1 i j = -(raw1265step0 i j); unfold raw1265step1 raw1265step0; decide +kernel
      have hl : raw1265step1Labels = raw1265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1265step1 raw1265step1Labels = mixedMoment B raw1265step2 raw1265step2Labels := by
      have ha : raw1265step2 = raw1265step1 := by apply Matrix.ext; unfold raw1265step2 raw1265step1; decide +kernel
      have hl : raw1265step1Labels = labelEmbedding1 ∘ raw1265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1265step1 raw1265step1Labels raw1265step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical1278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1278 raw1278Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw1278 raw1278Labels = mixedMoment B raw1278step0 raw1278step0Labels := by
      have ha : raw1278step0 = (fun i j => raw1278 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1278step0 raw1278; decide +kernel
      have hl : raw1278step0Labels = raw1278Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1278 raw1278Labels permutation2 permutation4
    mixedMoment B raw1278step0 raw1278step0Labels = mixedMoment B raw1278step1 raw1278step1Labels := by
      have ha : raw1278step1 = raw1278step0 := by apply Matrix.ext; unfold raw1278step1 raw1278step0; decide +kernel
      have hl : raw1278step0Labels = labelEmbedding7 ∘ raw1278step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1278step0 raw1278step0Labels raw1278step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical1279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1279 raw1279Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw1279 raw1279Labels = mixedMoment B raw1279step0 raw1279step0Labels := by
      have ha : raw1279step0 = (fun i j => raw1279 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1279step0 raw1279; decide +kernel
      have hl : raw1279step0Labels = raw1279Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1279 raw1279Labels permutation2 permutation4
    _ = mixedMoment B node1051 node1051Labels := by rfl

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

theorem sum_fin_two {R : Type*} [AddCommMonoid R] (f : Fin 2 → R) :
    ∑ i, f i = f 0 + f 1 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

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

theorem groupedColumns_family2_0 {p : ℕ} (A : Matrix (Fin p) (Fin 2) ℤ) :
    groupedColumns A (EqualityPatterns.family2.label 0) =
      (fun i (_ : Fin 1) => A i 0 + A i 1) := by
  change groupedColumns A (fun _ : Fin 2 => (0 : Fin 1)) = _
  ext i b
  have hb : b = 0 := Subsingleton.elim _ _
  subst b
  simp [groupedColumns, Fin.sum_univ_succ]

theorem groupedColumns_family2_1 {p : ℕ} (A : Matrix (Fin p) (Fin 2) ℤ) :
    groupedColumns A (EqualityPatterns.family2.label 1) = A := by
  change groupedColumns A (fun j : Fin 2 => j) = _
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

/-- The two equality patterns for the sampled column indices. -/
theorem single_label_two {p : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin 2) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      (1 / 6 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family2.label 0)) +
      (5 / 6 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family2.label 1)) := by
  have h := mixedMoment_single_label_partition B hB A
    EqualityPatterns.family2 EqualityPatterns.covers2
  rw [sum_fin_two] at h
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family2,
    EqualityPatterns.blocks2, Nat.descFactorial] at h
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

theorem canonical7978 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7978 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7978 = injectiveMoment H raw7978step0 := by
      have hz : ∀ j, raw7978 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7978step0 = (fun i j => raw7978 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7978 permutation2 hz
    injectiveMoment H raw7978step0 = injectiveMoment H raw7978step1 := by
      have hz : ∀ j, raw7978step0 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7978step1 = (fun i j => raw7978step0 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7978step0 permutation0 hz
    injectiveMoment H raw7978step1 = injectiveMoment H raw7978step2 := by
      have hz : ∀ i, raw7978step1 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7978step2 = (fun i j => raw7978step1 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7978step1 permutation0 hz
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

theorem sound4 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node4 = Sparse.eval value4 (momentVector H) := by
  have hc : momentVector H 1 = injectiveMoment H node4 := rfl
  simp [value4, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node6 node6Labels = Sparse.eval singlePairValue6 (familyPairVector B) := by
  have hp := single_label_two B hB node6
  have hl : node6Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node6 (EqualityPatterns.family2.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node6 (EqualityPatterns.family2.label 0) = PairSemantics.raw7978 := by
      rw [groupedColumns_family2_0]
      apply Matrix.ext; unfold node6 PairSemantics.raw7978; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7978 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node6 (EqualityPatterns.family2.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node6 (EqualityPatterns.family2.label 1) = PairSemantics.raw5210 := by
      rw [groupedColumns_family2_1]
      apply Matrix.ext; unfold node6 PairSemantics.raw5210; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5210 hH).trans (PairSemantics.sound4 hH)
  rw [hm0, hm1] at hp
  norm_num [singlePairValue6, PairSemantics.value0, PairSemantics.value4, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4094 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4094 node4094Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node6 node6Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw662 singletonSmall4094
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4094) = raw662Labels := by decide +kernel
  rw [hl, canonical662 B hB] at h
  have hc0 : mixedMoment B raw662 (Fin.cases (0 : Fin 1) singletonSmall4094) =
      mixedMoment B node6 node6Labels := by
    have ha : raw662 = raw663 := by apply Matrix.ext; unfold raw662 raw663; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4094 = raw663Labels := by decide +kernel
    rw [ha, hj, canonical663 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem singleton4460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4460 node4460Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1043 node1043Labels + mixedMoment B node1725 node1725Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1263 singletonSmall4460
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4460) = raw1263Labels := by decide +kernel
  rw [hl, canonical1263 B hB] at h
  have hc0 : mixedMoment B raw1263 (Fin.cases (0 : Fin 2) singletonSmall4460) =
      mixedMoment B node1043 node1043Labels := by
    have ha : raw1263 = raw1264 := by apply Matrix.ext; unfold raw1263 raw1264; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4460 = raw1264Labels := by decide +kernel
    rw [ha, hj, canonical1264 B hB]
  have hc1 : mixedMoment B raw1263 (Fin.cases (1 : Fin 2) singletonSmall4460) =
      mixedMoment B node1725 node1725Labels := by
    have ha : raw1263 = raw1265 := by apply Matrix.ext; unfold raw1263 raw1265; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4460 = raw1265Labels := by decide +kernel
    rw [ha, hj, canonical1265 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4468 node4468Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1051 node1051Labels + mixedMoment B node1752 node1752Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1278 singletonSmall4468
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4468) = raw1278Labels := by decide +kernel
  rw [hl, canonical1278 B hB] at h
  have hc0 : mixedMoment B raw1278 (Fin.cases (0 : Fin 2) singletonSmall4468) =
      mixedMoment B node1051 node1051Labels := by
    have ha : raw1278 = raw1279 := by apply Matrix.ext; unfold raw1278 raw1279; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4468 = raw1279Labels := by decide +kernel
    rw [ha, hj, canonical1279 B hB]
  have hc1 : mixedMoment B raw1278 (Fin.cases (1 : Fin 2) singletonSmall4468) =
      mixedMoment B node1752 node1752Labels := by
    have ha : raw1278 = raw1280 := by apply Matrix.ext; unfold raw1278 raw1280; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4468 = raw1280Labels := by decide +kernel
    rw [ha, hj, canonical1280 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4605 node4605Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1239 node1239Labels + mixedMoment B node2226 node2226Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1428 singletonSmall4605
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4605) = raw1428Labels := by decide +kernel
  rw [hl, canonical1428 B hB] at h
  have hc0 : mixedMoment B raw1428 (Fin.cases (0 : Fin 2) singletonSmall4605) =
      mixedMoment B node1239 node1239Labels := by
    have ha : raw1428 = raw1429 := by apply Matrix.ext; unfold raw1428 raw1429; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4605 = raw1429Labels := by decide +kernel
    rw [ha, hj, canonical1429 B hB]
  have hc1 : mixedMoment B raw1428 (Fin.cases (1 : Fin 2) singletonSmall4605) =
      mixedMoment B node2226 node2226Labels := by
    have ha : raw1428 = raw1430 := by apply Matrix.ext; unfold raw1428 raw1430; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4605 = raw1430Labels := by decide +kernel
    rw [ha, hj, canonical1430 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4621 node4621Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1297 node1297Labels + mixedMoment B node2289 node2289Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1446 singletonSmall4621
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4621) = raw1446Labels := by decide +kernel
  rw [hl, canonical1446 B hB] at h
  have hc0 : mixedMoment B raw1446 (Fin.cases (0 : Fin 2) singletonSmall4621) =
      mixedMoment B node1297 node1297Labels := by
    have ha : raw1446 = raw1447 := by apply Matrix.ext; unfold raw1446 raw1447; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4621 = raw1447Labels := by decide +kernel
    rw [ha, hj, canonical1447 B hB]
  have hc1 : mixedMoment B raw1446 (Fin.cases (1 : Fin 2) singletonSmall4621) =
      mixedMoment B node2289 node2289Labels := by
    have ha : raw1446 = raw1448 := by apply Matrix.ext; unfold raw1446 raw1448; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4621 = raw1448Labels := by decide +kernel
    rw [ha, hj, canonical1448 B hB]
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

theorem singleton4804 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4804 node4804Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2022 node2022Labels + mixedMoment B node2203 node2203Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1737 singletonSmall4804
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4804) = raw1737Labels := by decide +kernel
  rw [hl, canonical1737 B hB] at h
  have hc0 : mixedMoment B raw1737 (Fin.cases (0 : Fin 2) singletonSmall4804) =
      mixedMoment B node2022 node2022Labels := by
    have ha : raw1737 = raw1738 := by apply Matrix.ext; unfold raw1737 raw1738; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4804 = raw1738Labels := by decide +kernel
    rw [ha, hj, canonical1738 B hB]
  have hc1 : mixedMoment B raw1737 (Fin.cases (1 : Fin 2) singletonSmall4804) =
      mixedMoment B node2203 node2203Labels := by
    have ha : raw1737 = raw1739 := by apply Matrix.ext; unfold raw1737 raw1739; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4804 = raw1739Labels := by decide +kernel
    rw [ha, hj, canonical1739 B hB]
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

theorem singleton4868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4868 node4868Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2109 node2109Labels + mixedMoment B node2261 node2261Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1797 singletonSmall4868
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4868) = raw1797Labels := by decide +kernel
  rw [hl, canonical1797 B hB] at h
  have hc0 : mixedMoment B raw1797 (Fin.cases (0 : Fin 2) singletonSmall4868) =
      mixedMoment B node2109 node2109Labels := by
    have ha : raw1797 = raw1798 := by apply Matrix.ext; unfold raw1797 raw1798; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4868 = raw1798Labels := by decide +kernel
    rw [ha, hj, canonical1798 B hB]
  have hc1 : mixedMoment B raw1797 (Fin.cases (1 : Fin 2) singletonSmall4868) =
      mixedMoment B node2261 node2261Labels := by
    have ha : raw1797 = raw1799 := by apply Matrix.ext; unfold raw1797 raw1799; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4868 = raw1799Labels := by decide +kernel
    rw [ha, hj, canonical1799 B hB]
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

theorem singleton5272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5272 node5272Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2740 node2740Labels + mixedMoment B node2740 node2740Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2283 singletonSmall5272
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5272) = raw2283Labels := by decide +kernel
  rw [hl, canonical2283 B hB] at h
  have hc0 : mixedMoment B raw2283 (Fin.cases (0 : Fin 2) singletonSmall5272) =
      mixedMoment B node2740 node2740Labels := by
    have ha : raw2283 = raw2284 := by apply Matrix.ext; unfold raw2283 raw2284; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5272 = raw2284Labels := by decide +kernel
    rw [ha, hj, canonical2284 B hB]
  have hc1 : mixedMoment B raw2283 (Fin.cases (1 : Fin 2) singletonSmall5272) =
      mixedMoment B node2740 node2740Labels := by
    have ha : raw2283 = raw2285 := by apply Matrix.ext; unfold raw2283 raw2285; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5272 = raw2285Labels := by decide +kernel
    rw [ha, hj, canonical2285 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5305 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5305 node5305Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2783 node2783Labels + mixedMoment B node2783 node2783Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2319 singletonSmall5305
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5305) = raw2319Labels := by decide +kernel
  rw [hl, canonical2319 B hB] at h
  have hc0 : mixedMoment B raw2319 (Fin.cases (0 : Fin 2) singletonSmall5305) =
      mixedMoment B node2783 node2783Labels := by
    have ha : raw2319 = raw2320 := by apply Matrix.ext; unfold raw2319 raw2320; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5305 = raw2320Labels := by decide +kernel
    rw [ha, hj, canonical2320 B hB]
  have hc1 : mixedMoment B raw2319 (Fin.cases (1 : Fin 2) singletonSmall5305) =
      mixedMoment B node2783 node2783Labels := by
    have ha : raw2319 = raw2321 := by apply Matrix.ext; unfold raw2319 raw2321; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5305 = raw2321Labels := by decide +kernel
    rw [ha, hj, canonical2321 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
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

theorem sound2279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2279 node2279Labels = Sparse.eval nodeValue2279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2279) = mixedMoment B node2279 node2279Labels := rfl
  simpa [nodeValue2279, Sparse.eval] using hc.symm

theorem sound3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3626 node3626Labels = Sparse.eval nodeValue3626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3626) = mixedMoment B node3626 node3626Labels := rfl
  simpa [nodeValue3626, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound6 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node6 node6Labels = Sparse.eval nodeValue6 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue6 (familyPairVector B) := singlePair6 B _hB
    _ = _ := by norm_num [singlePairValue6, nodeValue6, Sparse.eval, mixedVector]

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

theorem sound1028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1028 node1028Labels = Sparse.eval nodeValue1028 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1028) = mixedMoment B node1028 node1028Labels := rfl
  simpa [nodeValue1028, Sparse.eval] using hc.symm

theorem sound1029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1029 node1029Labels = Sparse.eval nodeValue1029 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1029) = mixedMoment B node1029 node1029Labels := rfl
  simpa [nodeValue1029, Sparse.eval] using hc.symm

theorem sound1030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1030 node1030Labels = Sparse.eval nodeValue1030 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1030) = mixedMoment B node1030 node1030Labels := rfl
  simpa [nodeValue1030, Sparse.eval] using hc.symm

theorem sound1042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1042 node1042Labels = Sparse.eval nodeValue1042 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1042) = mixedMoment B node1042 node1042Labels := rfl
  simpa [nodeValue1042, Sparse.eval] using hc.symm

theorem sound1043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1043 node1043Labels = Sparse.eval nodeValue1043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1043) = mixedMoment B node1043 node1043Labels := rfl
  simpa [nodeValue1043, Sparse.eval] using hc.symm

theorem sound1051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1051 node1051Labels = Sparse.eval nodeValue1051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1051) = mixedMoment B node1051 node1051Labels := rfl
  simpa [nodeValue1051, Sparse.eval] using hc.symm

theorem sound1058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1058 node1058Labels = Sparse.eval nodeValue1058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1058) = mixedMoment B node1058 node1058Labels := rfl
  simpa [nodeValue1058, Sparse.eval] using hc.symm

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

theorem sound1239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1239 node1239Labels = Sparse.eval nodeValue1239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1239) = mixedMoment B node1239 node1239Labels := rfl
  simpa [nodeValue1239, Sparse.eval] using hc.symm

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

theorem sound1297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1297 node1297Labels = Sparse.eval nodeValue1297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1297) = mixedMoment B node1297 node1297Labels := rfl
  simpa [nodeValue1297, Sparse.eval] using hc.symm

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

theorem sound1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1725 node1725Labels = Sparse.eval nodeValue1725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1725) = mixedMoment B node1725 node1725Labels := rfl
  simpa [nodeValue1725, Sparse.eval] using hc.symm

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

theorem zero1754 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1754 node1754Labels = 0 := by
  exact mixedMoment_order_one B hB node1754 node1754Labels 1
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

theorem sound1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1752 node1752Labels = Sparse.eval nodeValue1752 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1752) = mixedMoment B node1752 node1752Labels := rfl
  simpa [nodeValue1752, Sparse.eval] using hc.symm

theorem sound1754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1754 node1754Labels = Sparse.eval nodeValue1754 (mixedVector B) := by
  simpa only [nodeValue1754, Sparse.eval_nil] using zero1754 B _hB _hF

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

theorem sound2013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2013 node2013Labels = Sparse.eval nodeValue2013 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2013) = mixedMoment B node2013 node2013Labels := rfl
  simpa [nodeValue2013, Sparse.eval] using hc.symm

theorem sound2014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2014 node2014Labels = Sparse.eval nodeValue2014 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2014) = mixedMoment B node2014 node2014Labels := rfl
  simpa [nodeValue2014, Sparse.eval] using hc.symm

theorem sound2021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2021 node2021Labels = Sparse.eval nodeValue2021 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2021) = mixedMoment B node2021 node2021Labels := rfl
  simpa [nodeValue2021, Sparse.eval] using hc.symm

theorem sound2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2022 node2022Labels = Sparse.eval nodeValue2022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2022) = mixedMoment B node2022 node2022Labels := rfl
  simpa [nodeValue2022, Sparse.eval] using hc.symm

theorem sound2034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2034 node2034Labels = Sparse.eval nodeValue2034 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2034) = mixedMoment B node2034 node2034Labels := rfl
  simpa [nodeValue2034, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2060 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2060 node2060Labels = 0 := by
  exact mixedMoment_order_one B hB node2060 node2060Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2060 node2060Labels = Sparse.eval nodeValue2060 (mixedVector B) := by
  simpa only [nodeValue2060, Sparse.eval_nil] using zero2060 B _hB _hF

theorem sound2095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2095 node2095Labels = Sparse.eval nodeValue2095 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2095) = mixedMoment B node2095 node2095Labels := rfl
  simpa [nodeValue2095, Sparse.eval] using hc.symm

theorem sound2096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2096 node2096Labels = Sparse.eval nodeValue2096 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2096) = mixedMoment B node2096 node2096Labels := rfl
  simpa [nodeValue2096, Sparse.eval] using hc.symm

theorem sound2097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2097 node2097Labels = Sparse.eval nodeValue2097 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2097) = mixedMoment B node2097 node2097Labels := rfl
  simpa [nodeValue2097, Sparse.eval] using hc.symm

theorem sound2108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2108 node2108Labels = Sparse.eval nodeValue2108 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2108) = mixedMoment B node2108 node2108Labels := rfl
  simpa [nodeValue2108, Sparse.eval] using hc.symm

theorem sound2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2109 node2109Labels = Sparse.eval nodeValue2109 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2109) = mixedMoment B node2109 node2109Labels := rfl
  simpa [nodeValue2109, Sparse.eval] using hc.symm

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

theorem sound2124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2124 node2124Labels = Sparse.eval nodeValue2124 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2124) = mixedMoment B node2124 node2124Labels := rfl
  simpa [nodeValue2124, Sparse.eval] using hc.symm

theorem sound2133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2133 node2133Labels = Sparse.eval nodeValue2133 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2133) = mixedMoment B node2133 node2133Labels := rfl
  simpa [nodeValue2133, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2228 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2228 node2228Labels = 0 := by
  exact mixedMoment_order_one B hB node2228 node2228Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2226 node2226Labels = Sparse.eval nodeValue2226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2226) = mixedMoment B node2226 node2226Labels := rfl
  simpa [nodeValue2226, Sparse.eval] using hc.symm

theorem sound2228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2228 node2228Labels = Sparse.eval nodeValue2228 (mixedVector B) := by
  simpa only [nodeValue2228, Sparse.eval_nil] using zero2228 B _hB _hF

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

theorem zero2264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = 0 := by
  exact mixedMoment_order_one B hB node2264 node2264Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2268 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2268 node2268Labels = 0 := by
  exact mixedMoment_order_one B hB node2268 node2268Labels 1
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

theorem sound2252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2252 node2252Labels = Sparse.eval nodeValue2252 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2252) = mixedMoment B node2252 node2252Labels := rfl
  simpa [nodeValue2252, Sparse.eval] using hc.symm

theorem sound2253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2253 node2253Labels = Sparse.eval nodeValue2253 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2253) = mixedMoment B node2253 node2253Labels := rfl
  simpa [nodeValue2253, Sparse.eval] using hc.symm

theorem sound2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2261 node2261Labels = Sparse.eval nodeValue2261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2261) = mixedMoment B node2261 node2261Labels := rfl
  simpa [nodeValue2261, Sparse.eval] using hc.symm

theorem sound2264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = Sparse.eval nodeValue2264 (mixedVector B) := by
  simpa only [nodeValue2264, Sparse.eval_nil] using zero2264 B _hB _hF

theorem sound2268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2268 node2268Labels = Sparse.eval nodeValue2268 (mixedVector B) := by
  simpa only [nodeValue2268, Sparse.eval_nil] using zero2268 B _hB _hF

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

theorem sound2289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2289 node2289Labels = Sparse.eval nodeValue2289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2289) = mixedMoment B node2289 node2289Labels := rfl
  simpa [nodeValue2289, Sparse.eval] using hc.symm

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

theorem sound2740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2740 node2740Labels = Sparse.eval nodeValue2740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2740) = mixedMoment B node2740 node2740Labels := rfl
  simpa [nodeValue2740, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2786 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2786 node2786Labels = 0 := by
  exact mixedMoment_order_one B hB node2786 node2786Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2783 node2783Labels = Sparse.eval nodeValue2783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2783) = mixedMoment B node2783 node2783Labels := rfl
  simpa [nodeValue2783, Sparse.eval] using hc.symm

theorem sound2786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2786 node2786Labels = Sparse.eval nodeValue2786 (mixedVector B) := by
  simpa only [nodeValue2786, Sparse.eval_nil] using zero2786 B _hB _hF

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

theorem sound3528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3528 node3528Labels = Sparse.eval nodeValue3528 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3528) = mixedMoment B node3528 node3528Labels := rfl
  simpa [nodeValue3528, Sparse.eval] using hc.symm

theorem sound3577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3577 node3577Labels = Sparse.eval nodeValue3577 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3577) = mixedMoment B node3577 node3577Labels := rfl
  simpa [nodeValue3577, Sparse.eval] using hc.symm

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

theorem sound4070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4070 node4070Labels = Sparse.eval nodeValue4070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4070) = mixedMoment B node4070 node4070Labels := rfl
  simpa [nodeValue4070, Sparse.eval] using hc.symm

theorem sound4072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4072 node4072Labels = Sparse.eval nodeValue4072 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4072) = mixedMoment B node4072 node4072Labels := rfl
  simpa [nodeValue4072, Sparse.eval] using hc.symm

theorem sound4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4081 node4081Labels = Sparse.eval nodeValue4081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4081) = mixedMoment B node4081 node4081Labels := rfl
  simpa [nodeValue4081, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4094 node4094Labels = Sparse.eval nodeValue4094 (mixedVector B) := by
  have h := singleton4094 B _hB
  rw [sound6 B _hB _hF] at h
  norm_num [nodeValue4094, nodeValue6, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4460 node4460Labels = Sparse.eval nodeValue4460 (mixedVector B) := by
  have h := singleton4460 B _hB
  rw [sound1043 B _hB _hF, sound1725 B _hB _hF] at h
  norm_num [nodeValue4460, nodeValue1043, nodeValue1725, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4468 node4468Labels = Sparse.eval nodeValue4468 (mixedVector B) := by
  have h := singleton4468 B _hB
  rw [sound1051 B _hB _hF, sound1752 B _hB _hF] at h
  norm_num [nodeValue4468, nodeValue1051, nodeValue1752, Sparse.eval] at h ⊢
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

theorem zero4505 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4505 node4505Labels = 0 := by
  exact mixedMoment_order_one B hB node4505 node4505Labels 1
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

theorem sound4505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4505 node4505Labels = Sparse.eval nodeValue4505 (mixedVector B) := by
  simpa only [nodeValue4505, Sparse.eval_nil] using zero4505 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4605 node4605Labels = Sparse.eval nodeValue4605 (mixedVector B) := by
  have h := singleton4605 B _hB
  rw [sound1239 B _hB _hF, sound2226 B _hB _hF] at h
  norm_num [nodeValue4605, nodeValue1239, nodeValue2226, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4621 node4621Labels = Sparse.eval nodeValue4621 (mixedVector B) := by
  have h := singleton4621 B _hB
  rw [sound1297 B _hB _hF, sound2289 B _hB _hF] at h
  norm_num [nodeValue4621, nodeValue1297, nodeValue2289, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = 0 := by
  exact mixedMoment_order_one B hB node4841 node4841Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4804 node4804Labels = Sparse.eval nodeValue4804 (mixedVector B) := by
  have h := singleton4804 B _hB
  rw [sound2022 B _hB _hF, sound2203 B _hB _hF] at h
  norm_num [nodeValue4804, nodeValue2022, nodeValue2203, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = Sparse.eval nodeValue4841 (mixedVector B) := by
  simpa only [nodeValue4841, Sparse.eval_nil] using zero4841 B _hB _hF

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

theorem zero4894 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4894 node4894Labels = 0 := by
  exact mixedMoment_order_one B hB node4894 node4894Labels 1
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

theorem sound4868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4868 node4868Labels = Sparse.eval nodeValue4868 (mixedVector B) := by
  have h := singleton4868 B _hB
  rw [sound2109 B _hB _hF, sound2261 B _hB _hF] at h
  norm_num [nodeValue4868, nodeValue2109, nodeValue2261, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4894 node4894Labels = Sparse.eval nodeValue4894 (mixedVector B) := by
  simpa only [nodeValue4894, Sparse.eval_nil] using zero4894 B _hB _hF

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

theorem zero5308 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5308 node5308Labels = 0 := by
  exact mixedMoment_order_one B hB node5308 node5308Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5272 node5272Labels = Sparse.eval nodeValue5272 (mixedVector B) := by
  have h := singleton5272 B _hB
  rw [sound2740 B _hB _hF] at h
  norm_num [nodeValue5272, nodeValue2740, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5305 node5305Labels = Sparse.eval nodeValue5305 (mixedVector B) := by
  have h := singleton5305 B _hB
  rw [sound2783 B _hB _hF] at h
  norm_num [nodeValue5305, nodeValue2783, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5308 node5308Labels = Sparse.eval nodeValue5308 (mixedVector B) := by
  simpa only [nodeValue5308, Sparse.eval_nil] using zero5308 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources5
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq165 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm165 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA165 + difference 0 1) (sourceB165 + difference 1 0) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA165 + difference 0 1) (sourceB165 + difference 1 0) sourceC165) = raw5101 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5101; decide +kernel
    rw [ha]
    exact (canonical5101 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA165 + difference 0 2) (sourceB165 + difference 2 0) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA165 + difference 0 2) (sourceB165 + difference 2 0) sourceC165) = raw5102 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5102; decide +kernel
    rw [ha]
    exact (canonical5102 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA165 + difference 0 3) (sourceB165 + difference 3 0) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA165 + difference 0 3) (sourceB165 + difference 3 0) sourceC165) = raw5103 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5103; decide +kernel
    rw [ha]
    exact (canonical5103 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA165 + difference 0 4) (sourceB165 + difference 4 0) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA165 + difference 0 4) (sourceB165 + difference 4 0) sourceC165) = raw5104 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5104; decide +kernel
    rw [ha]
    exact (canonical5104 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA165 + difference 0 5) (sourceB165 + difference 5 0) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA165 + difference 0 5) (sourceB165 + difference 5 0) sourceC165) = raw5105 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5105; decide +kernel
    rw [ha]
    exact (canonical5105 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA165 + difference 1 0) (sourceB165 + difference 0 1) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA165 + difference 1 0) (sourceB165 + difference 0 1) sourceC165) = raw5106 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5106; decide +kernel
    rw [ha]
    exact (canonical5106 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA165 + difference 1 2) (sourceB165 + difference 2 1) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA165 + difference 1 2) (sourceB165 + difference 2 1) sourceC165) = raw5107 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5107; decide +kernel
    rw [ha]
    exact (canonical5107 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA165 + difference 1 3) (sourceB165 + difference 3 1) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA165 + difference 1 3) (sourceB165 + difference 3 1) sourceC165) = raw5108 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5108; decide +kernel
    rw [ha]
    exact (canonical5108 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA165 + difference 1 4) (sourceB165 + difference 4 1) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA165 + difference 1 4) (sourceB165 + difference 4 1) sourceC165) = raw5109 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5109; decide +kernel
    rw [ha]
    exact (canonical5109 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA165 + difference 1 5) (sourceB165 + difference 5 1) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA165 + difference 1 5) (sourceB165 + difference 5 1) sourceC165) = raw5110 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5110; decide +kernel
    rw [ha]
    exact (canonical5110 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA165 + difference 2 0) (sourceB165 + difference 0 2) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA165 + difference 2 0) (sourceB165 + difference 0 2) sourceC165) = raw5111 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5111; decide +kernel
    rw [ha]
    exact (canonical5111 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA165 + difference 2 1) (sourceB165 + difference 1 2) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA165 + difference 2 1) (sourceB165 + difference 1 2) sourceC165) = raw5112 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5112; decide +kernel
    rw [ha]
    exact (canonical5112 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA165 + difference 2 3) (sourceB165 + difference 3 2) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA165 + difference 2 3) (sourceB165 + difference 3 2) sourceC165) = raw5113 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5113; decide +kernel
    rw [ha]
    exact (canonical5113 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA165 + difference 2 4) (sourceB165 + difference 4 2) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA165 + difference 2 4) (sourceB165 + difference 4 2) sourceC165) = raw5114 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5114; decide +kernel
    rw [ha]
    exact (canonical5114 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA165 + difference 2 5) (sourceB165 + difference 5 2) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA165 + difference 2 5) (sourceB165 + difference 5 2) sourceC165) = raw5115 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5115; decide +kernel
    rw [ha]
    exact (canonical5115 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA165 + difference 3 0) (sourceB165 + difference 0 3) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA165 + difference 3 0) (sourceB165 + difference 0 3) sourceC165) = raw5116 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5116; decide +kernel
    rw [ha]
    exact (canonical5116 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA165 + difference 3 1) (sourceB165 + difference 1 3) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA165 + difference 3 1) (sourceB165 + difference 1 3) sourceC165) = raw5117 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5117; decide +kernel
    rw [ha]
    exact (canonical5117 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA165 + difference 3 2) (sourceB165 + difference 2 3) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA165 + difference 3 2) (sourceB165 + difference 2 3) sourceC165) = raw5118 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5118; decide +kernel
    rw [ha]
    exact (canonical5118 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA165 + difference 3 4) (sourceB165 + difference 4 3) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA165 + difference 3 4) (sourceB165 + difference 4 3) sourceC165) = raw5119 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5119; decide +kernel
    rw [ha]
    exact (canonical5119 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA165 + difference 3 5) (sourceB165 + difference 5 3) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA165 + difference 3 5) (sourceB165 + difference 5 3) sourceC165) = raw5120 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5120; decide +kernel
    rw [ha]
    exact (canonical5120 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA165 + difference 4 0) (sourceB165 + difference 0 4) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA165 + difference 4 0) (sourceB165 + difference 0 4) sourceC165) = raw5121 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5121; decide +kernel
    rw [ha]
    exact (canonical5121 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA165 + difference 4 1) (sourceB165 + difference 1 4) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA165 + difference 4 1) (sourceB165 + difference 1 4) sourceC165) = raw5122 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5122; decide +kernel
    rw [ha]
    exact (canonical5122 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA165 + difference 4 2) (sourceB165 + difference 2 4) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA165 + difference 4 2) (sourceB165 + difference 2 4) sourceC165) = raw5123 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5123; decide +kernel
    rw [ha]
    exact (canonical5123 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA165 + difference 4 3) (sourceB165 + difference 3 4) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA165 + difference 4 3) (sourceB165 + difference 3 4) sourceC165) = raw5124 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5124; decide +kernel
    rw [ha]
    exact (canonical5124 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA165 + difference 4 5) (sourceB165 + difference 5 4) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5305) := by
    have ha : (tripleCharges (sourceA165 + difference 4 5) (sourceB165 + difference 5 4) sourceC165) = raw5125 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5125; decide +kernel
    rw [ha]
    exact (canonical5125 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA165 + difference 5 0) (sourceB165 + difference 0 5) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA165 + difference 5 0) (sourceB165 + difference 0 5) sourceC165) = raw5126 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5126; decide +kernel
    rw [ha]
    exact (canonical5126 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA165 + difference 5 1) (sourceB165 + difference 1 5) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA165 + difference 5 1) (sourceB165 + difference 1 5) sourceC165) = raw5127 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5127; decide +kernel
    rw [ha]
    exact (canonical5127 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA165 + difference 5 2) (sourceB165 + difference 2 5) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA165 + difference 5 2) (sourceB165 + difference 2 5) sourceC165) = raw5128 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5128; decide +kernel
    rw [ha]
    exact (canonical5128 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA165 + difference 5 3) (sourceB165 + difference 3 5) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA165 + difference 5 3) (sourceB165 + difference 3 5) sourceC165) = raw5129 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5129; decide +kernel
    rw [ha]
    exact (canonical5129 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA165 + difference 5 4) (sourceB165 + difference 4 5) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA165 + difference 5 4) (sourceB165 + difference 4 5) sourceC165) = raw5130 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5130; decide +kernel
    rw [ha]
    exact (canonical5130 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA165 sourceB165 sourceC165
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm165, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq166 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm166 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA166 + difference 0 1) (sourceB166 + difference 1 0) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA166 + difference 0 1) (sourceB166 + difference 1 0) sourceC166) = raw5131 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5131; decide +kernel
    rw [ha]
    exact (canonical5131 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA166 + difference 0 2) (sourceB166 + difference 2 0) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA166 + difference 0 2) (sourceB166 + difference 2 0) sourceC166) = raw5132 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5132; decide +kernel
    rw [ha]
    exact (canonical5132 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA166 + difference 0 3) (sourceB166 + difference 3 0) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA166 + difference 0 3) (sourceB166 + difference 3 0) sourceC166) = raw5133 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5133; decide +kernel
    rw [ha]
    exact (canonical5133 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA166 + difference 0 4) (sourceB166 + difference 4 0) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA166 + difference 0 4) (sourceB166 + difference 4 0) sourceC166) = raw5134 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5134; decide +kernel
    rw [ha]
    exact (canonical5134 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA166 + difference 0 5) (sourceB166 + difference 5 0) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2786) := by
    have ha : (tripleCharges (sourceA166 + difference 0 5) (sourceB166 + difference 5 0) sourceC166) = raw5135 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5135; decide +kernel
    rw [ha]
    exact (canonical5135 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA166 + difference 1 0) (sourceB166 + difference 0 1) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA166 + difference 1 0) (sourceB166 + difference 0 1) sourceC166) = raw5136 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5136; decide +kernel
    rw [ha]
    exact (canonical5136 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA166 + difference 1 2) (sourceB166 + difference 2 1) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA166 + difference 1 2) (sourceB166 + difference 2 1) sourceC166) = raw5137 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5137; decide +kernel
    rw [ha]
    exact (canonical5137 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA166 + difference 1 3) (sourceB166 + difference 3 1) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA166 + difference 1 3) (sourceB166 + difference 3 1) sourceC166) = raw5138 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5138; decide +kernel
    rw [ha]
    exact (canonical5138 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA166 + difference 1 4) (sourceB166 + difference 4 1) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA166 + difference 1 4) (sourceB166 + difference 4 1) sourceC166) = raw5139 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5139; decide +kernel
    rw [ha]
    exact (canonical5139 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA166 + difference 1 5) (sourceB166 + difference 5 1) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA166 + difference 1 5) (sourceB166 + difference 5 1) sourceC166) = raw5140 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5140; decide +kernel
    rw [ha]
    exact (canonical5140 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA166 + difference 2 0) (sourceB166 + difference 0 2) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA166 + difference 2 0) (sourceB166 + difference 0 2) sourceC166) = raw5141 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5141; decide +kernel
    rw [ha]
    exact (canonical5141 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA166 + difference 2 1) (sourceB166 + difference 1 2) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA166 + difference 2 1) (sourceB166 + difference 1 2) sourceC166) = raw5142 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5142; decide +kernel
    rw [ha]
    exact (canonical5142 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA166 + difference 2 3) (sourceB166 + difference 3 2) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA166 + difference 2 3) (sourceB166 + difference 3 2) sourceC166) = raw5143 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5143; decide +kernel
    rw [ha]
    exact (canonical5143 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA166 + difference 2 4) (sourceB166 + difference 4 2) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA166 + difference 2 4) (sourceB166 + difference 4 2) sourceC166) = raw5144 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5144; decide +kernel
    rw [ha]
    exact (canonical5144 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA166 + difference 2 5) (sourceB166 + difference 5 2) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA166 + difference 2 5) (sourceB166 + difference 5 2) sourceC166) = raw5145 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5145; decide +kernel
    rw [ha]
    exact (canonical5145 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA166 + difference 3 0) (sourceB166 + difference 0 3) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA166 + difference 3 0) (sourceB166 + difference 0 3) sourceC166) = raw5146 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5146; decide +kernel
    rw [ha]
    exact (canonical5146 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA166 + difference 3 1) (sourceB166 + difference 1 3) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA166 + difference 3 1) (sourceB166 + difference 1 3) sourceC166) = raw5147 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5147; decide +kernel
    rw [ha]
    exact (canonical5147 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA166 + difference 3 2) (sourceB166 + difference 2 3) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA166 + difference 3 2) (sourceB166 + difference 2 3) sourceC166) = raw5148 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5148; decide +kernel
    rw [ha]
    exact (canonical5148 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA166 + difference 3 4) (sourceB166 + difference 4 3) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA166 + difference 3 4) (sourceB166 + difference 4 3) sourceC166) = raw5149 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5149; decide +kernel
    rw [ha]
    exact (canonical5149 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA166 + difference 3 5) (sourceB166 + difference 5 3) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA166 + difference 3 5) (sourceB166 + difference 5 3) sourceC166) = raw5150 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5150; decide +kernel
    rw [ha]
    exact (canonical5150 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA166 + difference 4 0) (sourceB166 + difference 0 4) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA166 + difference 4 0) (sourceB166 + difference 0 4) sourceC166) = raw5151 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5151; decide +kernel
    rw [ha]
    exact (canonical5151 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA166 + difference 4 1) (sourceB166 + difference 1 4) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA166 + difference 4 1) (sourceB166 + difference 1 4) sourceC166) = raw5152 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5152; decide +kernel
    rw [ha]
    exact (canonical5152 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA166 + difference 4 2) (sourceB166 + difference 2 4) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA166 + difference 4 2) (sourceB166 + difference 2 4) sourceC166) = raw5153 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5153; decide +kernel
    rw [ha]
    exact (canonical5153 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA166 + difference 4 3) (sourceB166 + difference 3 4) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA166 + difference 4 3) (sourceB166 + difference 3 4) sourceC166) = raw5154 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5154; decide +kernel
    rw [ha]
    exact (canonical5154 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA166 + difference 4 5) (sourceB166 + difference 5 4) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA166 + difference 4 5) (sourceB166 + difference 5 4) sourceC166) = raw5155 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5155; decide +kernel
    rw [ha]
    exact (canonical5155 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA166 + difference 5 0) (sourceB166 + difference 0 5) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA166 + difference 5 0) (sourceB166 + difference 0 5) sourceC166) = raw5156 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5156; decide +kernel
    rw [ha]
    exact (canonical5156 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA166 + difference 5 1) (sourceB166 + difference 1 5) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA166 + difference 5 1) (sourceB166 + difference 1 5) sourceC166) = raw5157 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5157; decide +kernel
    rw [ha]
    exact (canonical5157 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA166 + difference 5 2) (sourceB166 + difference 2 5) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA166 + difference 5 2) (sourceB166 + difference 2 5) sourceC166) = raw5158 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5158; decide +kernel
    rw [ha]
    exact (canonical5158 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA166 + difference 5 3) (sourceB166 + difference 3 5) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA166 + difference 5 3) (sourceB166 + difference 3 5) sourceC166) = raw5159 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5159; decide +kernel
    rw [ha]
    exact (canonical5159 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA166 + difference 5 4) (sourceB166 + difference 4 5) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA166 + difference 5 4) (sourceB166 + difference 4 5) sourceC166) = raw5160 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5160; decide +kernel
    rw [ha]
    exact (canonical5160 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA166 sourceB166 sourceC166
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm166, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq167 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm167 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA167 + difference 0 0) (sourceB167 + difference 0 0) sourceC167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA167 + difference 0 0) (sourceB167 + difference 0 0) sourceC167) = raw5161 := by
      apply Matrix.ext; unfold tripleCharges sourceA167 sourceB167 sourceC167 difference raw5161; decide +kernel
    rw [ha]
    exact (canonical5161 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA167 + difference 1 0) (sourceB167 + difference 0 1) sourceC167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA167 + difference 1 0) (sourceB167 + difference 0 1) sourceC167) = raw5162 := by
      apply Matrix.ext; unfold tripleCharges sourceA167 sourceB167 sourceC167 difference raw5162; decide +kernel
    rw [ha]
    exact (canonical5162 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA167 + difference 2 0) (sourceB167 + difference 0 2) sourceC167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA167 + difference 2 0) (sourceB167 + difference 0 2) sourceC167) = raw5163 := by
      apply Matrix.ext; unfold tripleCharges sourceA167 sourceB167 sourceC167 difference raw5163; decide +kernel
    rw [ha]
    exact (canonical5163 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA167 + difference 3 0) (sourceB167 + difference 0 3) sourceC167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA167 + difference 3 0) (sourceB167 + difference 0 3) sourceC167) = raw5164 := by
      apply Matrix.ext; unfold tripleCharges sourceA167 sourceB167 sourceC167 difference raw5164; decide +kernel
    rw [ha]
    exact (canonical5164 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA167 + difference 4 0) (sourceB167 + difference 0 4) sourceC167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA167 + difference 4 0) (sourceB167 + difference 0 4) sourceC167) = raw5165 := by
      apply Matrix.ext; unfold tripleCharges sourceA167 sourceB167 sourceC167 difference raw5165; decide +kernel
    rw [ha]
    exact (canonical5165 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA167 + difference 5 0) (sourceB167 + difference 0 5) sourceC167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA167 + difference 5 0) (sourceB167 + difference 0 5) sourceC167) = raw5166 := by
      apply Matrix.ext; unfold tripleCharges sourceA167 sourceB167 sourceC167 difference raw5166; decide +kernel
    rw [ha]
    exact (canonical5166 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA167 + sourceB167) sourceC167) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA167 + sourceB167) sourceC167) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA167 sourceB167 sourceC167 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA167 sourceB167 sourceC167
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm167, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq168 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm168 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA168 + difference 1 0) (sourceB168 + difference 0 1) sourceC168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA168 + difference 1 0) (sourceB168 + difference 0 1) sourceC168) = raw5162 := by
      apply Matrix.ext; unfold tripleCharges sourceA168 sourceB168 sourceC168 difference raw5162; decide +kernel
    rw [ha]
    exact (canonical5162 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA168 + difference 1 1) (sourceB168 + difference 1 1) sourceC168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA168 + difference 1 1) (sourceB168 + difference 1 1) sourceC168) = raw5161 := by
      apply Matrix.ext; unfold tripleCharges sourceA168 sourceB168 sourceC168 difference raw5161; decide +kernel
    rw [ha]
    exact (canonical5161 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA168 + difference 1 2) (sourceB168 + difference 2 1) sourceC168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA168 + difference 1 2) (sourceB168 + difference 2 1) sourceC168) = raw5168 := by
      apply Matrix.ext; unfold tripleCharges sourceA168 sourceB168 sourceC168 difference raw5168; decide +kernel
    rw [ha]
    exact (canonical5168 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA168 + difference 1 3) (sourceB168 + difference 3 1) sourceC168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA168 + difference 1 3) (sourceB168 + difference 3 1) sourceC168) = raw5169 := by
      apply Matrix.ext; unfold tripleCharges sourceA168 sourceB168 sourceC168 difference raw5169; decide +kernel
    rw [ha]
    exact (canonical5169 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA168 + difference 1 4) (sourceB168 + difference 4 1) sourceC168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2060) := by
    have ha : (tripleCharges (sourceA168 + difference 1 4) (sourceB168 + difference 4 1) sourceC168) = raw5170 := by
      apply Matrix.ext; unfold tripleCharges sourceA168 sourceB168 sourceC168 difference raw5170; decide +kernel
    rw [ha]
    exact (canonical5170 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA168 + difference 1 5) (sourceB168 + difference 5 1) sourceC168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA168 + difference 1 5) (sourceB168 + difference 5 1) sourceC168) = raw5171 := by
      apply Matrix.ext; unfold tripleCharges sourceA168 sourceB168 sourceC168 difference raw5171; decide +kernel
    rw [ha]
    exact (canonical5171 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA168 + sourceB168) sourceC168) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA168 + sourceB168) sourceC168) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA168 sourceB168 sourceC168 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA168 sourceB168 sourceC168
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm168, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq169 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm169 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA169 + difference 0 1) (sourceB169 + difference 1 0) sourceC169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA169 + difference 0 1) (sourceB169 + difference 1 0) sourceC169) = raw5172 := by
      apply Matrix.ext; unfold tripleCharges sourceA169 sourceB169 sourceC169 difference raw5172; decide +kernel
    rw [ha]
    exact (canonical5172 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA169 + difference 1 1) (sourceB169 + difference 1 1) sourceC169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA169 + difference 1 1) (sourceB169 + difference 1 1) sourceC169) = raw5161 := by
      apply Matrix.ext; unfold tripleCharges sourceA169 sourceB169 sourceC169 difference raw5161; decide +kernel
    rw [ha]
    exact (canonical5161 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA169 + difference 2 1) (sourceB169 + difference 1 2) sourceC169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA169 + difference 2 1) (sourceB169 + difference 1 2) sourceC169) = raw5173 := by
      apply Matrix.ext; unfold tripleCharges sourceA169 sourceB169 sourceC169 difference raw5173; decide +kernel
    rw [ha]
    exact (canonical5173 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA169 + difference 3 1) (sourceB169 + difference 1 3) sourceC169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA169 + difference 3 1) (sourceB169 + difference 1 3) sourceC169) = raw5174 := by
      apply Matrix.ext; unfold tripleCharges sourceA169 sourceB169 sourceC169 difference raw5174; decide +kernel
    rw [ha]
    exact (canonical5174 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA169 + difference 4 1) (sourceB169 + difference 1 4) sourceC169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA169 + difference 4 1) (sourceB169 + difference 1 4) sourceC169) = raw5175 := by
      apply Matrix.ext; unfold tripleCharges sourceA169 sourceB169 sourceC169 difference raw5175; decide +kernel
    rw [ha]
    exact (canonical5175 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA169 + difference 5 1) (sourceB169 + difference 1 5) sourceC169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA169 + difference 5 1) (sourceB169 + difference 1 5) sourceC169) = raw5176 := by
      apply Matrix.ext; unfold tripleCharges sourceA169 sourceB169 sourceC169 difference raw5176; decide +kernel
    rw [ha]
    exact (canonical5176 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA169 + sourceB169) sourceC169) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA169 + sourceB169) sourceC169) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA169 sourceB169 sourceC169 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA169 sourceB169 sourceC169
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm169, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm170 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA170 + difference 4 0) (sourceB170 + difference 0 4) sourceC170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA170 + difference 4 0) (sourceB170 + difference 0 4) sourceC170) = raw5165 := by
      apply Matrix.ext; unfold tripleCharges sourceA170 sourceB170 sourceC170 difference raw5165; decide +kernel
    rw [ha]
    exact (canonical5165 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA170 + difference 4 1) (sourceB170 + difference 1 4) sourceC170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA170 + difference 4 1) (sourceB170 + difference 1 4) sourceC170) = raw5175 := by
      apply Matrix.ext; unfold tripleCharges sourceA170 sourceB170 sourceC170 difference raw5175; decide +kernel
    rw [ha]
    exact (canonical5175 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA170 + difference 4 2) (sourceB170 + difference 2 4) sourceC170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA170 + difference 4 2) (sourceB170 + difference 2 4) sourceC170) = raw5177 := by
      apply Matrix.ext; unfold tripleCharges sourceA170 sourceB170 sourceC170 difference raw5177; decide +kernel
    rw [ha]
    exact (canonical5177 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA170 + difference 4 3) (sourceB170 + difference 3 4) sourceC170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA170 + difference 4 3) (sourceB170 + difference 3 4) sourceC170) = raw5178 := by
      apply Matrix.ext; unfold tripleCharges sourceA170 sourceB170 sourceC170 difference raw5178; decide +kernel
    rw [ha]
    exact (canonical5178 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA170 + difference 4 4) (sourceB170 + difference 4 4) sourceC170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA170 + difference 4 4) (sourceB170 + difference 4 4) sourceC170) = raw5161 := by
      apply Matrix.ext; unfold tripleCharges sourceA170 sourceB170 sourceC170 difference raw5161; decide +kernel
    rw [ha]
    exact (canonical5161 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA170 + difference 4 5) (sourceB170 + difference 5 4) sourceC170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA170 + difference 4 5) (sourceB170 + difference 5 4) sourceC170) = raw5179 := by
      apply Matrix.ext; unfold tripleCharges sourceA170 sourceB170 sourceC170 difference raw5179; decide +kernel
    rw [ha]
    exact (canonical5179 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA170 + sourceB170) sourceC170) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA170 + sourceB170) sourceC170) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA170 sourceB170 sourceC170 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA170 sourceB170 sourceC170
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm170, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm172 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA172 + difference 0 1) (sourceB172 + difference 1 0) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA172 + difference 0 1) (sourceB172 + difference 1 0) sourceC172) = raw2935 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw2935; decide +kernel
    rw [ha]
    exact (canonical2935 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA172 + difference 0 2) (sourceB172 + difference 2 0) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA172 + difference 0 2) (sourceB172 + difference 2 0) sourceC172) = raw2936 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw2936; decide +kernel
    rw [ha]
    exact (canonical2936 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA172 + difference 0 3) (sourceB172 + difference 3 0) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA172 + difference 0 3) (sourceB172 + difference 3 0) sourceC172) = raw2937 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw2937; decide +kernel
    rw [ha]
    exact (canonical2937 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA172 + difference 0 4) (sourceB172 + difference 4 0) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA172 + difference 0 4) (sourceB172 + difference 4 0) sourceC172) = raw2938 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw2938; decide +kernel
    rw [ha]
    exact (canonical2938 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA172 + difference 0 5) (sourceB172 + difference 5 0) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4094) := by
    have ha : (tripleCharges (sourceA172 + difference 0 5) (sourceB172 + difference 5 0) sourceC172) = raw3340 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw3340; decide +kernel
    rw [ha]
    exact (canonical3340 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA172 + difference 1 0) (sourceB172 + difference 0 1) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA172 + difference 1 0) (sourceB172 + difference 0 1) sourceC172) = raw5197 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5197; decide +kernel
    rw [ha]
    exact (canonical5197 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA172 + difference 1 2) (sourceB172 + difference 2 1) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 1 2) (sourceB172 + difference 2 1) sourceC172) = raw5198 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5198; decide +kernel
    rw [ha]
    exact (canonical5198 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA172 + difference 1 3) (sourceB172 + difference 3 1) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 1 3) (sourceB172 + difference 3 1) sourceC172) = raw5199 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5199; decide +kernel
    rw [ha]
    exact (canonical5199 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA172 + difference 1 4) (sourceB172 + difference 4 1) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 1 4) (sourceB172 + difference 4 1) sourceC172) = raw5200 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5200; decide +kernel
    rw [ha]
    exact (canonical5200 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA172 + difference 1 5) (sourceB172 + difference 5 1) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA172 + difference 1 5) (sourceB172 + difference 5 1) sourceC172) = raw2914 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw2914; decide +kernel
    rw [ha]
    exact (canonical2914 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA172 + difference 2 0) (sourceB172 + difference 0 2) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA172 + difference 2 0) (sourceB172 + difference 0 2) sourceC172) = raw5201 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5201; decide +kernel
    rw [ha]
    exact (canonical5201 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA172 + difference 2 1) (sourceB172 + difference 1 2) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 2 1) (sourceB172 + difference 1 2) sourceC172) = raw5202 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5202; decide +kernel
    rw [ha]
    exact (canonical5202 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA172 + difference 2 3) (sourceB172 + difference 3 2) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 2 3) (sourceB172 + difference 3 2) sourceC172) = raw5203 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5203; decide +kernel
    rw [ha]
    exact (canonical5203 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA172 + difference 2 4) (sourceB172 + difference 4 2) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 2 4) (sourceB172 + difference 4 2) sourceC172) = raw5204 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5204; decide +kernel
    rw [ha]
    exact (canonical5204 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA172 + difference 2 5) (sourceB172 + difference 5 2) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA172 + difference 2 5) (sourceB172 + difference 5 2) sourceC172) = raw2919 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw2919; decide +kernel
    rw [ha]
    exact (canonical2919 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA172 + difference 3 0) (sourceB172 + difference 0 3) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA172 + difference 3 0) (sourceB172 + difference 0 3) sourceC172) = raw5205 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5205; decide +kernel
    rw [ha]
    exact (canonical5205 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA172 + difference 3 1) (sourceB172 + difference 1 3) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 3 1) (sourceB172 + difference 1 3) sourceC172) = raw5206 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5206; decide +kernel
    rw [ha]
    exact (canonical5206 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA172 + difference 3 2) (sourceB172 + difference 2 3) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 3 2) (sourceB172 + difference 2 3) sourceC172) = raw5207 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5207; decide +kernel
    rw [ha]
    exact (canonical5207 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA172 + difference 3 4) (sourceB172 + difference 4 3) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 3 4) (sourceB172 + difference 4 3) sourceC172) = raw5208 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5208; decide +kernel
    rw [ha]
    exact (canonical5208 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA172 + difference 3 5) (sourceB172 + difference 5 3) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA172 + difference 3 5) (sourceB172 + difference 5 3) sourceC172) = raw2924 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw2924; decide +kernel
    rw [ha]
    exact (canonical2924 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA172 + difference 4 0) (sourceB172 + difference 0 4) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA172 + difference 4 0) (sourceB172 + difference 0 4) sourceC172) = raw5209 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5209; decide +kernel
    rw [ha]
    exact (canonical5209 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA172 + difference 4 1) (sourceB172 + difference 1 4) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 4 1) (sourceB172 + difference 1 4) sourceC172) = raw5210 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5210; decide +kernel
    rw [ha]
    exact (canonical5210 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA172 + difference 4 2) (sourceB172 + difference 2 4) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 4 2) (sourceB172 + difference 2 4) sourceC172) = raw5211 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5211; decide +kernel
    rw [ha]
    exact (canonical5211 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA172 + difference 4 3) (sourceB172 + difference 3 4) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 4 3) (sourceB172 + difference 3 4) sourceC172) = raw5212 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5212; decide +kernel
    rw [ha]
    exact (canonical5212 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA172 + difference 4 5) (sourceB172 + difference 5 4) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA172 + difference 4 5) (sourceB172 + difference 5 4) sourceC172) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA172 + difference 5 0) (sourceB172 + difference 0 5) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (tripleCharges (sourceA172 + difference 5 0) (sourceB172 + difference 0 5) sourceC172) = raw5213 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5213; decide +kernel
    rw [ha]
    exact (canonical5213 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA172 + difference 5 1) (sourceB172 + difference 1 5) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA172 + difference 5 1) (sourceB172 + difference 1 5) sourceC172) = raw5214 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5214; decide +kernel
    rw [ha]
    exact (canonical5214 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA172 + difference 5 2) (sourceB172 + difference 2 5) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA172 + difference 5 2) (sourceB172 + difference 2 5) sourceC172) = raw5215 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5215; decide +kernel
    rw [ha]
    exact (canonical5215 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA172 + difference 5 3) (sourceB172 + difference 3 5) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA172 + difference 5 3) (sourceB172 + difference 3 5) sourceC172) = raw5216 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5216; decide +kernel
    rw [ha]
    exact (canonical5216 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA172 + difference 5 4) (sourceB172 + difference 4 5) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA172 + difference 5 4) (sourceB172 + difference 4 5) sourceC172) = raw5217 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5217; decide +kernel
    rw [ha]
    exact (canonical5217 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA172 sourceB172 sourceC172
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm172, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm176 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA176 + difference 0 0) (sourceB176 + difference 0 0) sourceC176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA176 + difference 0 0) (sourceB176 + difference 0 0) sourceC176) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA176 sourceB176 sourceC176 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA176 + difference 0 1) (sourceB176 + difference 1 0) sourceC176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA176 + difference 0 1) (sourceB176 + difference 1 0) sourceC176) = raw5309 := by
      apply Matrix.ext; unfold tripleCharges sourceA176 sourceB176 sourceC176 difference raw5309; decide +kernel
    rw [ha]
    exact (canonical5309 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA176 + difference 0 2) (sourceB176 + difference 2 0) sourceC176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3577) := by
    have ha : (tripleCharges (sourceA176 + difference 0 2) (sourceB176 + difference 2 0) sourceC176) = raw5310 := by
      apply Matrix.ext; unfold tripleCharges sourceA176 sourceB176 sourceC176 difference raw5310; decide +kernel
    rw [ha]
    exact (canonical5310 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA176 + difference 0 3) (sourceB176 + difference 3 0) sourceC176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA176 + difference 0 3) (sourceB176 + difference 3 0) sourceC176) = raw5311 := by
      apply Matrix.ext; unfold tripleCharges sourceA176 sourceB176 sourceC176 difference raw5311; decide +kernel
    rw [ha]
    exact (canonical5311 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA176 + difference 0 4) (sourceB176 + difference 4 0) sourceC176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA176 + difference 0 4) (sourceB176 + difference 4 0) sourceC176) = raw5312 := by
      apply Matrix.ext; unfold tripleCharges sourceA176 sourceB176 sourceC176 difference raw5312; decide +kernel
    rw [ha]
    exact (canonical5312 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA176 + difference 0 5) (sourceB176 + difference 5 0) sourceC176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA176 + difference 0 5) (sourceB176 + difference 5 0) sourceC176) = raw5313 := by
      apply Matrix.ext; unfold tripleCharges sourceA176 sourceB176 sourceC176 difference raw5313; decide +kernel
    rw [ha]
    exact (canonical5313 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA176 + sourceB176) sourceC176) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA176 + sourceB176) sourceC176) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA176 sourceB176 sourceC176 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA176 sourceB176 sourceC176
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm176, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm177 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA177 + difference 0 0) (sourceB177 + difference 0 0) sourceC177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA177 + difference 0 0) (sourceB177 + difference 0 0) sourceC177) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA177 sourceB177 sourceC177 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA177 + difference 1 0) (sourceB177 + difference 0 1) sourceC177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1028) := by
    have ha : (tripleCharges (sourceA177 + difference 1 0) (sourceB177 + difference 0 1) sourceC177) = raw5315 := by
      apply Matrix.ext; unfold tripleCharges sourceA177 sourceB177 sourceC177 difference raw5315; decide +kernel
    rw [ha]
    exact (canonical5315 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA177 + difference 2 0) (sourceB177 + difference 0 2) sourceC177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1058) := by
    have ha : (tripleCharges (sourceA177 + difference 2 0) (sourceB177 + difference 0 2) sourceC177) = raw5316 := by
      apply Matrix.ext; unfold tripleCharges sourceA177 sourceB177 sourceC177 difference raw5316; decide +kernel
    rw [ha]
    exact (canonical5316 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA177 + difference 3 0) (sourceB177 + difference 0 3) sourceC177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA177 + difference 3 0) (sourceB177 + difference 0 3) sourceC177) = raw5317 := by
      apply Matrix.ext; unfold tripleCharges sourceA177 sourceB177 sourceC177 difference raw5317; decide +kernel
    rw [ha]
    exact (canonical5317 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA177 + difference 4 0) (sourceB177 + difference 0 4) sourceC177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1030) := by
    have ha : (tripleCharges (sourceA177 + difference 4 0) (sourceB177 + difference 0 4) sourceC177) = raw5318 := by
      apply Matrix.ext; unfold tripleCharges sourceA177 sourceB177 sourceC177 difference raw5318; decide +kernel
    rw [ha]
    exact (canonical5318 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA177 + difference 5 0) (sourceB177 + difference 0 5) sourceC177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1029) := by
    have ha : (tripleCharges (sourceA177 + difference 5 0) (sourceB177 + difference 0 5) sourceC177) = raw5319 := by
      apply Matrix.ext; unfold tripleCharges sourceA177 sourceB177 sourceC177 difference raw5319; decide +kernel
    rw [ha]
    exact (canonical5319 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA177 + sourceB177) sourceC177) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA177 + sourceB177) sourceC177) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA177 sourceB177 sourceC177 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA177 sourceB177 sourceC177
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm177, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq178 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm178 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA178 + difference 1 0) (sourceB178 + difference 0 1) sourceC178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1028) := by
    have ha : (tripleCharges (sourceA178 + difference 1 0) (sourceB178 + difference 0 1) sourceC178) = raw5315 := by
      apply Matrix.ext; unfold tripleCharges sourceA178 sourceB178 sourceC178 difference raw5315; decide +kernel
    rw [ha]
    exact (canonical5315 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA178 + difference 1 1) (sourceB178 + difference 1 1) sourceC178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA178 + difference 1 1) (sourceB178 + difference 1 1) sourceC178) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA178 sourceB178 sourceC178 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA178 + difference 1 2) (sourceB178 + difference 2 1) sourceC178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2095) := by
    have ha : (tripleCharges (sourceA178 + difference 1 2) (sourceB178 + difference 2 1) sourceC178) = raw5320 := by
      apply Matrix.ext; unfold tripleCharges sourceA178 sourceB178 sourceC178 difference raw5320; decide +kernel
    rw [ha]
    exact (canonical5320 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA178 + difference 1 3) (sourceB178 + difference 3 1) sourceC178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2124) := by
    have ha : (tripleCharges (sourceA178 + difference 1 3) (sourceB178 + difference 3 1) sourceC178) = raw5321 := by
      apply Matrix.ext; unfold tripleCharges sourceA178 sourceB178 sourceC178 difference raw5321; decide +kernel
    rw [ha]
    exact (canonical5321 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA178 + difference 1 4) (sourceB178 + difference 4 1) sourceC178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA178 + difference 1 4) (sourceB178 + difference 4 1) sourceC178) = raw5322 := by
      apply Matrix.ext; unfold tripleCharges sourceA178 sourceB178 sourceC178 difference raw5322; decide +kernel
    rw [ha]
    exact (canonical5322 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA178 + difference 1 5) (sourceB178 + difference 5 1) sourceC178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA178 + difference 1 5) (sourceB178 + difference 5 1) sourceC178) = raw5323 := by
      apply Matrix.ext; unfold tripleCharges sourceA178 sourceB178 sourceC178 difference raw5323; decide +kernel
    rw [ha]
    exact (canonical5323 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA178 + sourceB178) sourceC178) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA178 + sourceB178) sourceC178) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA178 sourceB178 sourceC178 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA178 sourceB178 sourceC178
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm178, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq179 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm179 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA179 + difference 0 1) (sourceB179 + difference 1 0) sourceC179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA179 + difference 0 1) (sourceB179 + difference 1 0) sourceC179) = raw5309 := by
      apply Matrix.ext; unfold tripleCharges sourceA179 sourceB179 sourceC179 difference raw5309; decide +kernel
    rw [ha]
    exact (canonical5309 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA179 + difference 1 1) (sourceB179 + difference 1 1) sourceC179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA179 + difference 1 1) (sourceB179 + difference 1 1) sourceC179) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA179 sourceB179 sourceC179 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA179 + difference 2 1) (sourceB179 + difference 1 2) sourceC179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2034) := by
    have ha : (tripleCharges (sourceA179 + difference 2 1) (sourceB179 + difference 1 2) sourceC179) = raw5324 := by
      apply Matrix.ext; unfold tripleCharges sourceA179 sourceB179 sourceC179 difference raw5324; decide +kernel
    rw [ha]
    exact (canonical5324 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA179 + difference 3 1) (sourceB179 + difference 1 3) sourceC179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA179 + difference 3 1) (sourceB179 + difference 1 3) sourceC179) = raw5325 := by
      apply Matrix.ext; unfold tripleCharges sourceA179 sourceB179 sourceC179 difference raw5325; decide +kernel
    rw [ha]
    exact (canonical5325 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA179 + difference 4 1) (sourceB179 + difference 1 4) sourceC179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2014) := by
    have ha : (tripleCharges (sourceA179 + difference 4 1) (sourceB179 + difference 1 4) sourceC179) = raw5326 := by
      apply Matrix.ext; unfold tripleCharges sourceA179 sourceB179 sourceC179 difference raw5326; decide +kernel
    rw [ha]
    exact (canonical5326 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA179 + difference 5 1) (sourceB179 + difference 1 5) sourceC179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2013) := by
    have ha : (tripleCharges (sourceA179 + difference 5 1) (sourceB179 + difference 1 5) sourceC179) = raw5327 := by
      apply Matrix.ext; unfold tripleCharges sourceA179 sourceB179 sourceC179 difference raw5327; decide +kernel
    rw [ha]
    exact (canonical5327 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA179 + sourceB179) sourceC179) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA179 + sourceB179) sourceC179) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA179 sourceB179 sourceC179 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA179 sourceB179 sourceC179
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm179, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq180 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm180 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA180 + difference 2 0) (sourceB180 + difference 0 2) sourceC180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1058) := by
    have ha : (tripleCharges (sourceA180 + difference 2 0) (sourceB180 + difference 0 2) sourceC180) = raw5316 := by
      apply Matrix.ext; unfold tripleCharges sourceA180 sourceB180 sourceC180 difference raw5316; decide +kernel
    rw [ha]
    exact (canonical5316 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA180 + difference 2 1) (sourceB180 + difference 1 2) sourceC180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2034) := by
    have ha : (tripleCharges (sourceA180 + difference 2 1) (sourceB180 + difference 1 2) sourceC180) = raw5324 := by
      apply Matrix.ext; unfold tripleCharges sourceA180 sourceB180 sourceC180 difference raw5324; decide +kernel
    rw [ha]
    exact (canonical5324 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA180 + difference 2 2) (sourceB180 + difference 2 2) sourceC180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA180 + difference 2 2) (sourceB180 + difference 2 2) sourceC180) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA180 sourceB180 sourceC180 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA180 + difference 2 3) (sourceB180 + difference 3 2) sourceC180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA180 + difference 2 3) (sourceB180 + difference 3 2) sourceC180) = raw5328 := by
      apply Matrix.ext; unfold tripleCharges sourceA180 sourceB180 sourceC180 difference raw5328; decide +kernel
    rw [ha]
    exact (canonical5328 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA180 + difference 2 4) (sourceB180 + difference 4 2) sourceC180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA180 + difference 2 4) (sourceB180 + difference 4 2) sourceC180) = raw5329 := by
      apply Matrix.ext; unfold tripleCharges sourceA180 sourceB180 sourceC180 difference raw5329; decide +kernel
    rw [ha]
    exact (canonical5329 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA180 + difference 2 5) (sourceB180 + difference 5 2) sourceC180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA180 + difference 2 5) (sourceB180 + difference 5 2) sourceC180) = raw5330 := by
      apply Matrix.ext; unfold tripleCharges sourceA180 sourceB180 sourceC180 difference raw5330; decide +kernel
    rw [ha]
    exact (canonical5330 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA180 + sourceB180) sourceC180) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA180 + sourceB180) sourceC180) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA180 sourceB180 sourceC180 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA180 sourceB180 sourceC180
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm180, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq181 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm181 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA181 + difference 0 2) (sourceB181 + difference 2 0) sourceC181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3577) := by
    have ha : (tripleCharges (sourceA181 + difference 0 2) (sourceB181 + difference 2 0) sourceC181) = raw5310 := by
      apply Matrix.ext; unfold tripleCharges sourceA181 sourceB181 sourceC181 difference raw5310; decide +kernel
    rw [ha]
    exact (canonical5310 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA181 + difference 1 2) (sourceB181 + difference 2 1) sourceC181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2095) := by
    have ha : (tripleCharges (sourceA181 + difference 1 2) (sourceB181 + difference 2 1) sourceC181) = raw5320 := by
      apply Matrix.ext; unfold tripleCharges sourceA181 sourceB181 sourceC181 difference raw5320; decide +kernel
    rw [ha]
    exact (canonical5320 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA181 + difference 2 2) (sourceB181 + difference 2 2) sourceC181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA181 + difference 2 2) (sourceB181 + difference 2 2) sourceC181) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA181 sourceB181 sourceC181 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA181 + difference 3 2) (sourceB181 + difference 2 3) sourceC181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA181 + difference 3 2) (sourceB181 + difference 2 3) sourceC181) = raw5331 := by
      apply Matrix.ext; unfold tripleCharges sourceA181 sourceB181 sourceC181 difference raw5331; decide +kernel
    rw [ha]
    exact (canonical5331 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA181 + difference 4 2) (sourceB181 + difference 2 4) sourceC181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2097) := by
    have ha : (tripleCharges (sourceA181 + difference 4 2) (sourceB181 + difference 2 4) sourceC181) = raw5332 := by
      apply Matrix.ext; unfold tripleCharges sourceA181 sourceB181 sourceC181 difference raw5332; decide +kernel
    rw [ha]
    exact (canonical5332 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA181 + difference 5 2) (sourceB181 + difference 2 5) sourceC181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2096) := by
    have ha : (tripleCharges (sourceA181 + difference 5 2) (sourceB181 + difference 2 5) sourceC181) = raw5333 := by
      apply Matrix.ext; unfold tripleCharges sourceA181 sourceB181 sourceC181 difference raw5333; decide +kernel
    rw [ha]
    exact (canonical5333 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA181 + sourceB181) sourceC181) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA181 + sourceB181) sourceC181) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA181 sourceB181 sourceC181 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA181 sourceB181 sourceC181
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm181, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck145 : Integer.Sparse.reindex keyMap MixedData.row145 = numericRow145 := by decide +kernel

theorem numericCheck145 (x : Master → ℝ) : Integer.Sparse.eval numericRow145 x =
    (4 : ℝ) * reducedSource145 x := by
  norm_num [numericRow145, reducedSource145, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4460, nodeValue4468, nodeValue4505, nodeValue4605, nodeValue4621, nodeValue4804, nodeValue4841, nodeValue4868, nodeValue4894, nodeValue5272, nodeValue5305, nodeValue5308]
  ring

theorem reindexCheck146 : Integer.Sparse.reindex keyMap MixedData.row146 = numericRow146 := by decide +kernel

theorem numericCheck146 (x : Master → ℝ) : Integer.Sparse.eval numericRow146 x =
    (1 : ℝ) * reducedSource146 x := by
  norm_num [numericRow146, reducedSource146, Integer.Sparse.eval, Sparse.eval, nodeValue1725, nodeValue1752, nodeValue1754, nodeValue2203, nodeValue2226, nodeValue2228, nodeValue2261, nodeValue2264, nodeValue2289, nodeValue2740, nodeValue2783, nodeValue2786, nodeValue4084]

theorem reindexCheck147 : Integer.Sparse.reindex keyMap MixedData.row147 = numericRow147 := by decide +kernel

theorem numericCheck147 (x : Master → ℝ) : Integer.Sparse.eval numericRow147 x =
    (1 : ℝ) * reducedSource147 x := by
  norm_num [numericRow147, reducedSource147, Integer.Sparse.eval, Sparse.eval, nodeValue1051, nodeValue1239, nodeValue1297, nodeValue2268, nodeValue4084]

theorem reindexCheck148 : Integer.Sparse.reindex keyMap MixedData.row148 = numericRow148 := by decide +kernel

theorem numericCheck148 (x : Master → ℝ) : Integer.Sparse.eval numericRow148 x =
    (1 : ℝ) * reducedSource148 x := by
  norm_num [numericRow148, reducedSource148, Integer.Sparse.eval, Sparse.eval, nodeValue1239, nodeValue2022, nodeValue2060, nodeValue2268, nodeValue2740, nodeValue4084]

theorem reindexCheck149 : Integer.Sparse.reindex keyMap MixedData.row149 = numericRow149 := by decide +kernel

theorem numericCheck149 (x : Master → ℝ) : Integer.Sparse.eval numericRow149 x =
    (1 : ℝ) * reducedSource149 x := by
  norm_num [numericRow149, reducedSource149, Integer.Sparse.eval, Sparse.eval, nodeValue1043, nodeValue2022, nodeValue2109, nodeValue2264, nodeValue2268, nodeValue4084]

theorem reindexCheck150 : Integer.Sparse.reindex keyMap MixedData.row150 = numericRow150 := by decide +kernel

theorem numericCheck150 (x : Master → ℝ) : Integer.Sparse.eval numericRow150 x =
    (1 : ℝ) * reducedSource150 x := by
  norm_num [numericRow150, reducedSource150, Integer.Sparse.eval, Sparse.eval, nodeValue1297, nodeValue2109, nodeValue2268, nodeValue2783, nodeValue4084]

theorem reindexCheck152 : Integer.Sparse.reindex keyMap MixedData.row152 = numericRow152 := by decide +kernel

theorem numericCheck152 (x : Master → ℝ) : Integer.Sparse.eval numericRow152 x =
    (30 : ℝ) * reducedSource152 x := by
  norm_num [numericRow152, reducedSource152, Integer.Sparse.eval, Sparse.eval, nodeValue4070, nodeValue4072, nodeValue4081, nodeValue4084, nodeValue4094]
  ring

theorem reindexCheck154 : Integer.Sparse.reindex keyMap MixedData.row154 = numericRow154 := by decide +kernel

theorem numericCheck154 (x : Master → ℝ) : Integer.Sparse.eval numericRow154 x =
    (1 : ℝ) * reducedSource154 x := by
  norm_num [numericRow154, reducedSource154, Integer.Sparse.eval, Sparse.eval, nodeValue2253, nodeValue2513, nodeValue3528, nodeValue3577, nodeValue3625, nodeValue3626, nodeValue4084]

theorem reindexCheck155 : Integer.Sparse.reindex keyMap MixedData.row155 = numericRow155 := by decide +kernel

theorem numericCheck155 (x : Master → ℝ) : Integer.Sparse.eval numericRow155 x =
    (1 : ℝ) * reducedSource155 x := by
  norm_num [numericRow155, reducedSource155, Integer.Sparse.eval, Sparse.eval, nodeValue1028, nodeValue1029, nodeValue1030, nodeValue1042, nodeValue1058, nodeValue2253, nodeValue4084]

theorem reindexCheck156 : Integer.Sparse.reindex keyMap MixedData.row156 = numericRow156 := by decide +kernel

theorem numericCheck156 (x : Master → ℝ) : Integer.Sparse.eval numericRow156 x =
    (1 : ℝ) * reducedSource156 x := by
  norm_num [numericRow156, reducedSource156, Integer.Sparse.eval, Sparse.eval, nodeValue1028, nodeValue2095, nodeValue2124, nodeValue2252, nodeValue2253, nodeValue4084]

theorem reindexCheck157 : Integer.Sparse.reindex keyMap MixedData.row157 = numericRow157 := by decide +kernel

theorem numericCheck157 (x : Master → ℝ) : Integer.Sparse.eval numericRow157 x =
    (1 : ℝ) * reducedSource157 x := by
  norm_num [numericRow157, reducedSource157, Integer.Sparse.eval, Sparse.eval, nodeValue2013, nodeValue2014, nodeValue2021, nodeValue2034, nodeValue2253, nodeValue3528, nodeValue4084]

theorem reindexCheck158 : Integer.Sparse.reindex keyMap MixedData.row158 = numericRow158 := by decide +kernel

theorem numericCheck158 (x : Master → ℝ) : Integer.Sparse.eval numericRow158 x =
    (1 : ℝ) * reducedSource158 x := by
  norm_num [numericRow158, reducedSource158, Integer.Sparse.eval, Sparse.eval, nodeValue1058, nodeValue2034, nodeValue2133, nodeValue2253, nodeValue2277, nodeValue2279, nodeValue4084]

theorem reindexCheck159 : Integer.Sparse.reindex keyMap MixedData.row159 = numericRow159 := by decide +kernel

theorem numericCheck159 (x : Master → ℝ) : Integer.Sparse.eval numericRow159 x =
    (1 : ℝ) * reducedSource159 x := by
  norm_num [numericRow159, reducedSource159, Integer.Sparse.eval, Sparse.eval, nodeValue2095, nodeValue2096, nodeValue2097, nodeValue2108, nodeValue2253, nodeValue3577, nodeValue4084]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero145 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource145 (mixedVector B) = 0 := by
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4505 : mixedVector B (Sum.inr 4505) = Sparse.eval nodeValue4505 (mixedVector B) := by
    change mixedMoment B node4505 node4505Labels = _
    exact sound4505 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4621 : mixedVector B (Sum.inr 4621) = Sparse.eval nodeValue4621 (mixedVector B) := by
    change mixedMoment B node4621 node4621Labels = _
    exact sound4621 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4894 : mixedVector B (Sum.inr 4894) = Sparse.eval nodeValue4894 (mixedVector B) := by
    change mixedMoment B node4894 node4894Labels = _
    exact sound4894 B hB hF
  have h5272 : mixedVector B (Sum.inr 5272) = Sparse.eval nodeValue5272 (mixedVector B) := by
    change mixedMoment B node5272 node5272Labels = _
    exact sound5272 B hB hF
  have h5305 : mixedVector B (Sum.inr 5305) = Sparse.eval nodeValue5305 (mixedVector B) := by
    change mixedMoment B node5305 node5305Labels = _
    exact sound5305 B hB hF
  have h5308 : mixedVector B (Sum.inr 5308) = Sparse.eval nodeValue5308 (mixedVector B) := by
    change mixedMoment B node5308 node5308Labels = _
    exact sound5308 B hB hF
  simpa only [sourceForm165, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4084, h4460, h4468, h4505, h4605, h4621, h4804, h4841, h4868, h4894, h5272, h5305, h5308, reducedSource145] using sourceEq165 B hB

theorem rowSound145 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row145 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck145, numericCheck145, reducedZero145 B hB hF, mul_zero]

theorem reducedZero146 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource146 (mixedVector B) = 0 := by
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  have h2786 : mixedVector B (Sum.inr 2786) = Sparse.eval nodeValue2786 (mixedVector B) := by
    change mixedMoment B node2786 node2786Labels = _
    exact sound2786 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm166, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1725, h1752, h1754, h2203, h2226, h2228, h2261, h2264, h2289, h2740, h2783, h2786, h4084, reducedSource146] using sourceEq166 B hB

theorem rowSound146 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row146 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck146, numericCheck146, reducedZero146 B hB hF, mul_zero]

theorem reducedZero147 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource147 (mixedVector B) = 0 := by
  have h1051 : mixedVector B (Sum.inr 1051) = Sparse.eval nodeValue1051 (mixedVector B) := by
    change mixedMoment B node1051 node1051Labels = _
    exact sound1051 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm167, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1051, h1239, h1297, h2268, h4084, reducedSource147] using sourceEq167 B hB

theorem rowSound147 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row147 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck147, numericCheck147, reducedZero147 B hB hF, mul_zero]

theorem reducedZero148 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource148 (mixedVector B) = 0 := by
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h2060 : mixedVector B (Sum.inr 2060) = Sparse.eval nodeValue2060 (mixedVector B) := by
    change mixedMoment B node2060 node2060Labels = _
    exact sound2060 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm168, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1239, h2022, h2060, h2268, h2740, h4084, reducedSource148] using sourceEq168 B hB

theorem rowSound148 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row148 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck148, numericCheck148, reducedZero148 B hB hF, mul_zero]

theorem reducedZero149 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource149 (mixedVector B) = 0 := by
  have h1043 : mixedVector B (Sum.inr 1043) = Sparse.eval nodeValue1043 (mixedVector B) := by
    change mixedMoment B node1043 node1043Labels = _
    exact sound1043 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h2109 : mixedVector B (Sum.inr 2109) = Sparse.eval nodeValue2109 (mixedVector B) := by
    change mixedMoment B node2109 node2109Labels = _
    exact sound2109 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm169, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1043, h2022, h2109, h2264, h2268, h4084, reducedSource149] using sourceEq169 B hB

theorem rowSound149 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row149 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck149, numericCheck149, reducedZero149 B hB hF, mul_zero]

theorem reducedZero150 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource150 (mixedVector B) = 0 := by
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h2109 : mixedVector B (Sum.inr 2109) = Sparse.eval nodeValue2109 (mixedVector B) := by
    change mixedMoment B node2109 node2109Labels = _
    exact sound2109 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm170, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1297, h2109, h2268, h2783, h4084, reducedSource150] using sourceEq170 B hB

theorem rowSound150 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row150 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck150, numericCheck150, reducedZero150 B hB hF, mul_zero]

theorem reducedZero152 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource152 (mixedVector B) = 0 := by
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4094 : mixedVector B (Sum.inr 4094) = Sparse.eval nodeValue4094 (mixedVector B) := by
    change mixedMoment B node4094 node4094Labels = _
    exact sound4094 B hB hF
  simpa only [sourceForm172, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4070, h4072, h4081, h4084, h4094, reducedSource152] using sourceEq172 B hB

theorem rowSound152 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row152 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck152, numericCheck152, reducedZero152 B hB hF, mul_zero]

theorem reducedZero154 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource154 (mixedVector B) = 0 := by
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h2513 : mixedVector B (Sum.inr 2513) = Sparse.eval nodeValue2513 (mixedVector B) := by
    change mixedMoment B node2513 node2513Labels = _
    exact sound2513 B hB hF
  have h3528 : mixedVector B (Sum.inr 3528) = Sparse.eval nodeValue3528 (mixedVector B) := by
    change mixedMoment B node3528 node3528Labels = _
    exact sound3528 B hB hF
  have h3577 : mixedVector B (Sum.inr 3577) = Sparse.eval nodeValue3577 (mixedVector B) := by
    change mixedMoment B node3577 node3577Labels = _
    exact sound3577 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm176, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2253, h2513, h3528, h3577, h3625, h3626, h4084, reducedSource154] using sourceEq176 B hB

theorem rowSound154 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row154 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck154, numericCheck154, reducedZero154 B hB hF, mul_zero]

theorem reducedZero155 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource155 (mixedVector B) = 0 := by
  have h1028 : mixedVector B (Sum.inr 1028) = Sparse.eval nodeValue1028 (mixedVector B) := by
    change mixedMoment B node1028 node1028Labels = _
    exact sound1028 B hB hF
  have h1029 : mixedVector B (Sum.inr 1029) = Sparse.eval nodeValue1029 (mixedVector B) := by
    change mixedMoment B node1029 node1029Labels = _
    exact sound1029 B hB hF
  have h1030 : mixedVector B (Sum.inr 1030) = Sparse.eval nodeValue1030 (mixedVector B) := by
    change mixedMoment B node1030 node1030Labels = _
    exact sound1030 B hB hF
  have h1042 : mixedVector B (Sum.inr 1042) = Sparse.eval nodeValue1042 (mixedVector B) := by
    change mixedMoment B node1042 node1042Labels = _
    exact sound1042 B hB hF
  have h1058 : mixedVector B (Sum.inr 1058) = Sparse.eval nodeValue1058 (mixedVector B) := by
    change mixedMoment B node1058 node1058Labels = _
    exact sound1058 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm177, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1028, h1029, h1030, h1042, h1058, h2253, h4084, reducedSource155] using sourceEq177 B hB

theorem rowSound155 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row155 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck155, numericCheck155, reducedZero155 B hB hF, mul_zero]

theorem reducedZero156 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource156 (mixedVector B) = 0 := by
  have h1028 : mixedVector B (Sum.inr 1028) = Sparse.eval nodeValue1028 (mixedVector B) := by
    change mixedMoment B node1028 node1028Labels = _
    exact sound1028 B hB hF
  have h2095 : mixedVector B (Sum.inr 2095) = Sparse.eval nodeValue2095 (mixedVector B) := by
    change mixedMoment B node2095 node2095Labels = _
    exact sound2095 B hB hF
  have h2124 : mixedVector B (Sum.inr 2124) = Sparse.eval nodeValue2124 (mixedVector B) := by
    change mixedMoment B node2124 node2124Labels = _
    exact sound2124 B hB hF
  have h2252 : mixedVector B (Sum.inr 2252) = Sparse.eval nodeValue2252 (mixedVector B) := by
    change mixedMoment B node2252 node2252Labels = _
    exact sound2252 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm178, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1028, h2095, h2124, h2252, h2253, h4084, reducedSource156] using sourceEq178 B hB

theorem rowSound156 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row156 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck156, numericCheck156, reducedZero156 B hB hF, mul_zero]

theorem reducedZero157 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource157 (mixedVector B) = 0 := by
  have h2013 : mixedVector B (Sum.inr 2013) = Sparse.eval nodeValue2013 (mixedVector B) := by
    change mixedMoment B node2013 node2013Labels = _
    exact sound2013 B hB hF
  have h2014 : mixedVector B (Sum.inr 2014) = Sparse.eval nodeValue2014 (mixedVector B) := by
    change mixedMoment B node2014 node2014Labels = _
    exact sound2014 B hB hF
  have h2021 : mixedVector B (Sum.inr 2021) = Sparse.eval nodeValue2021 (mixedVector B) := by
    change mixedMoment B node2021 node2021Labels = _
    exact sound2021 B hB hF
  have h2034 : mixedVector B (Sum.inr 2034) = Sparse.eval nodeValue2034 (mixedVector B) := by
    change mixedMoment B node2034 node2034Labels = _
    exact sound2034 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h3528 : mixedVector B (Sum.inr 3528) = Sparse.eval nodeValue3528 (mixedVector B) := by
    change mixedMoment B node3528 node3528Labels = _
    exact sound3528 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm179, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2013, h2014, h2021, h2034, h2253, h3528, h4084, reducedSource157] using sourceEq179 B hB

theorem rowSound157 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row157 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck157, numericCheck157, reducedZero157 B hB hF, mul_zero]

theorem reducedZero158 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource158 (mixedVector B) = 0 := by
  have h1058 : mixedVector B (Sum.inr 1058) = Sparse.eval nodeValue1058 (mixedVector B) := by
    change mixedMoment B node1058 node1058Labels = _
    exact sound1058 B hB hF
  have h2034 : mixedVector B (Sum.inr 2034) = Sparse.eval nodeValue2034 (mixedVector B) := by
    change mixedMoment B node2034 node2034Labels = _
    exact sound2034 B hB hF
  have h2133 : mixedVector B (Sum.inr 2133) = Sparse.eval nodeValue2133 (mixedVector B) := by
    change mixedMoment B node2133 node2133Labels = _
    exact sound2133 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm180, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1058, h2034, h2133, h2253, h2277, h2279, h4084, reducedSource158] using sourceEq180 B hB

theorem rowSound158 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row158 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck158, numericCheck158, reducedZero158 B hB hF, mul_zero]

theorem reducedZero159 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource159 (mixedVector B) = 0 := by
  have h2095 : mixedVector B (Sum.inr 2095) = Sparse.eval nodeValue2095 (mixedVector B) := by
    change mixedMoment B node2095 node2095Labels = _
    exact sound2095 B hB hF
  have h2096 : mixedVector B (Sum.inr 2096) = Sparse.eval nodeValue2096 (mixedVector B) := by
    change mixedMoment B node2096 node2096Labels = _
    exact sound2096 B hB hF
  have h2097 : mixedVector B (Sum.inr 2097) = Sparse.eval nodeValue2097 (mixedVector B) := by
    change mixedMoment B node2097 node2097Labels = _
    exact sound2097 B hB hF
  have h2108 : mixedVector B (Sum.inr 2108) = Sparse.eval nodeValue2108 (mixedVector B) := by
    change mixedMoment B node2108 node2108Labels = _
    exact sound2108 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h3577 : mixedVector B (Sum.inr 3577) = Sparse.eval nodeValue3577 (mixedVector B) := by
    change mixedMoment B node3577 node3577Labels = _
    exact sound3577 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm181, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2095, h2096, h2097, h2108, h2253, h3577, h4084, reducedSource159] using sourceEq181 B hB

theorem rowSound159 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row159 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck159, numericCheck159, reducedZero159 B hB hF, mul_zero]

theorem sourceRowsAt144 : MixedData.sourceRows (144 : Fin 2425) =
    MixedData.row144 := by decide +kernel

theorem sourceRowsAt145 : MixedData.sourceRows (145 : Fin 2425) =
    MixedData.row145 := by decide +kernel

theorem sourceRowsAt146 : MixedData.sourceRows (146 : Fin 2425) =
    MixedData.row146 := by decide +kernel

theorem sourceRowsAt147 : MixedData.sourceRows (147 : Fin 2425) =
    MixedData.row147 := by decide +kernel

theorem sourceRowsAt148 : MixedData.sourceRows (148 : Fin 2425) =
    MixedData.row148 := by decide +kernel

theorem sourceRowsAt149 : MixedData.sourceRows (149 : Fin 2425) =
    MixedData.row149 := by decide +kernel

theorem sourceRowsAt150 : MixedData.sourceRows (150 : Fin 2425) =
    MixedData.row150 := by decide +kernel

theorem sourceRowsAt151 : MixedData.sourceRows (151 : Fin 2425) =
    MixedData.row151 := by decide +kernel

theorem sourceRowsAt152 : MixedData.sourceRows (152 : Fin 2425) =
    MixedData.row152 := by decide +kernel

theorem sourceRowsAt153 : MixedData.sourceRows (153 : Fin 2425) =
    MixedData.row153 := by decide +kernel

theorem sourceRowsAt154 : MixedData.sourceRows (154 : Fin 2425) =
    MixedData.row154 := by decide +kernel

theorem sourceRowsAt155 : MixedData.sourceRows (155 : Fin 2425) =
    MixedData.row155 := by decide +kernel

theorem sourceRowsAt156 : MixedData.sourceRows (156 : Fin 2425) =
    MixedData.row156 := by decide +kernel

theorem sourceRowsAt157 : MixedData.sourceRows (157 : Fin 2425) =
    MixedData.row157 := by decide +kernel

theorem sourceRowsAt158 : MixedData.sourceRows (158 : Fin 2425) =
    MixedData.row158 := by decide +kernel

theorem sourceRowsAt159 : MixedData.sourceRows (159 : Fin 2425) =
    MixedData.row159 := by decide +kernel

theorem chunkSound9_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 9) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 144 ∨ k.val = 145 ∨ k.val = 146 ∨ k.val = 147 ∨ k.val = 148 ∨ k.val = 149 ∨ k.val = 150 ∨ k.val = 151 ∨ k.val = 152 ∨ k.val = 153 ∨ k.val = 154 ∨ k.val = 155 ∨ k.val = 156 ∨ k.val = 157 ∨ k.val = 158 ∨ k.val = 159 := by omega
  rcases heq with h144 | h145 | h146 | h147 | h148 | h149 | h150 | h151 | h152 | h153 | h154 | h155 | h156 | h157 | h158 | h159
  · have he : k = (144 : Fin 2425) := Fin.ext h144
    subst k
    rw [sourceRowsAt144]
    exact rowSound144_e B hB hF
  · have he : k = (145 : Fin 2425) := Fin.ext h145
    subst k
    rw [sourceRowsAt145]
    exact rowSound145 B hB hF
  · have he : k = (146 : Fin 2425) := Fin.ext h146
    subst k
    rw [sourceRowsAt146]
    exact rowSound146 B hB hF
  · have he : k = (147 : Fin 2425) := Fin.ext h147
    subst k
    rw [sourceRowsAt147]
    exact rowSound147 B hB hF
  · have he : k = (148 : Fin 2425) := Fin.ext h148
    subst k
    rw [sourceRowsAt148]
    exact rowSound148 B hB hF
  · have he : k = (149 : Fin 2425) := Fin.ext h149
    subst k
    rw [sourceRowsAt149]
    exact rowSound149 B hB hF
  · have he : k = (150 : Fin 2425) := Fin.ext h150
    subst k
    rw [sourceRowsAt150]
    exact rowSound150 B hB hF
  · have he : k = (151 : Fin 2425) := Fin.ext h151
    subst k
    rw [sourceRowsAt151]
    exact rowSound151_e B hB hF
  · have he : k = (152 : Fin 2425) := Fin.ext h152
    subst k
    rw [sourceRowsAt152]
    exact rowSound152 B hB hF
  · have he : k = (153 : Fin 2425) := Fin.ext h153
    subst k
    rw [sourceRowsAt153]
    exact rowSound153_e B hB hF
  · have he : k = (154 : Fin 2425) := Fin.ext h154
    subst k
    rw [sourceRowsAt154]
    exact rowSound154 B hB hF
  · have he : k = (155 : Fin 2425) := Fin.ext h155
    subst k
    rw [sourceRowsAt155]
    exact rowSound155 B hB hF
  · have he : k = (156 : Fin 2425) := Fin.ext h156
    subst k
    rw [sourceRowsAt156]
    exact rowSound156 B hB hF
  · have he : k = (157 : Fin 2425) := Fin.ext h157
    subst k
    rw [sourceRowsAt157]
    exact rowSound157 B hB hF
  · have he : k = (158 : Fin 2425) := Fin.ext h158
    subst k
    rw [sourceRowsAt158]
    exact rowSound158 B hB hF
  · have he : k = (159 : Fin 2425) := Fin.ext h159
    subst k
    rw [sourceRowsAt159]
    exact rowSound159 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e_oai
