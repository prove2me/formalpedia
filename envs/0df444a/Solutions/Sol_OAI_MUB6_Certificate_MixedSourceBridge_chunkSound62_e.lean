-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:26:43.108872+00:00
-- url     : https://prove2.me/submissions/06cafb5c-183c-46b2-a7f6-5e54e5a081af

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E129
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E150
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1007_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound992_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18338 raw18338Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw18338 raw18338Labels = mixedMoment B raw18338step0 raw18338step0Labels := by
      have hz : ∀ i, raw18338 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18338step0 = (fun i j => raw18338 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18338step0 raw18338; decide +kernel
      have hl : raw18338step0Labels = (fun j => raw18338Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18338 raw18338Labels permutation6 hz
    _ = mixedMoment B node4090 node4090Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19364 raw19364Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19364 raw19364Labels = mixedMoment B raw19364step0 raw19364step0Labels := by
      have hz : ∀ i, raw19364 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19364step0 = (fun i j => raw19364 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19364step0 raw19364; decide +kernel
      have hl : raw19364step0Labels = (fun j => raw19364Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19364 raw19364Labels permutation6 hz
    mixedMoment B raw19364step0 raw19364step0Labels = mixedMoment B raw19364step1 raw19364step1Labels := by
      have ha : raw19364step1 = (fun i j => raw19364step0 (permutation155 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19364step1 raw19364step0; decide +kernel
      have hl : raw19364step1Labels = raw19364step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19364step0 raw19364step0Labels permutation155 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical19368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19368 raw19368Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19368 raw19368Labels = mixedMoment B raw19368step0 raw19368step0Labels := by
      have hz : ∀ i, raw19368 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19368step0 = (fun i j => raw19368 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19368step0 raw19368; decide +kernel
      have hl : raw19368step0Labels = (fun j => raw19368Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19368 raw19368Labels permutation6 hz
    mixedMoment B raw19368step0 raw19368step0Labels = mixedMoment B raw19368step1 raw19368step1Labels := by
      have ha : raw19368step1 = (fun i j => raw19368step0 (permutation153 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19368step1 raw19368step0; decide +kernel
      have hl : raw19368step1Labels = raw19368step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19368step0 raw19368step0Labels permutation153 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical19390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19390 raw19390Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19390 raw19390Labels = mixedMoment B raw19390step0 raw19390step0Labels := by
      have hz : ∀ j, raw19390 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw19390step0 = (fun i j => raw19390 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw19390step0 raw19390; decide +kernel
      have hl : raw19390step0Labels = raw19390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19390 raw19390Labels permutation152 hz
    mixedMoment B raw19390step0 raw19390step0Labels = mixedMoment B raw19390step1 raw19390step1Labels := by
      have hz : ∀ i, raw19390step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19390step1 = (fun i j => raw19390step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19390step1 raw19390step0; decide +kernel
      have hl : raw19390step1Labels = (fun j => raw19390step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19390step0 raw19390step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical19391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19391 raw19391Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19391 raw19391Labels = mixedMoment B raw19391step0 raw19391step0Labels := by
      have hz : ∀ j, raw19391 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw19391step0 = (fun i j => raw19391 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw19391step0 raw19391; decide +kernel
      have hl : raw19391step0Labels = raw19391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19391 raw19391Labels permutation152 hz
    mixedMoment B raw19391step0 raw19391step0Labels = mixedMoment B raw19391step1 raw19391step1Labels := by
      have hz : ∀ i, raw19391step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19391step1 = (fun i j => raw19391step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19391step1 raw19391step0; decide +kernel
      have hl : raw19391step1Labels = (fun j => raw19391step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19391step0 raw19391step0Labels permutation6 hz
    mixedMoment B raw19391step1 raw19391step1Labels = mixedMoment B raw19391step2 raw19391step2Labels := by
      have ha : raw19391step2 = (fun i j => raw19391step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19391step2 raw19391step1; decide +kernel
      have hl : raw19391step2Labels = raw19391step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19391step1 raw19391step1Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical19392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19392 raw19392Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw19392 raw19392Labels = mixedMoment B raw19392step0 raw19392step0Labels := by
      have hz : ∀ j, raw19392 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19392step0 = (fun i j => raw19392 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19392step0 raw19392; decide +kernel
      have hl : raw19392step0Labels = raw19392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19392 raw19392Labels permutation520 hz
    mixedMoment B raw19392step0 raw19392step0Labels = mixedMoment B raw19392step1 raw19392step1Labels := by
      have hz : ∀ j, raw19392step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw19392step1 = (fun i j => raw19392step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw19392step1 raw19392step0; decide +kernel
      have hl : raw19392step1Labels = raw19392step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19392step0 raw19392step0Labels permutation32 hz
    mixedMoment B raw19392step1 raw19392step1Labels = mixedMoment B raw19392step2 raw19392step2Labels := by
      have hz : ∀ i, raw19392step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19392step2 = (fun i j => raw19392step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19392step2 raw19392step1; decide +kernel
      have hl : raw19392step2Labels = (fun j => raw19392step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19392step1 raw19392step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical19393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19393 raw19393Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw19393 raw19393Labels = mixedMoment B raw19393step0 raw19393step0Labels := by
      have hz : ∀ j, raw19393 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19393step0 = (fun i j => raw19393 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19393step0 raw19393; decide +kernel
      have hl : raw19393step0Labels = raw19393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19393 raw19393Labels permutation590 hz
    mixedMoment B raw19393step0 raw19393step0Labels = mixedMoment B raw19393step1 raw19393step1Labels := by
      have hz : ∀ j, raw19393step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw19393step1 = (fun i j => raw19393step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw19393step1 raw19393step0; decide +kernel
      have hl : raw19393step1Labels = raw19393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19393step0 raw19393step0Labels permutation32 hz
    mixedMoment B raw19393step1 raw19393step1Labels = mixedMoment B raw19393step2 raw19393step2Labels := by
      have hz : ∀ i, raw19393step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19393step2 = (fun i j => raw19393step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19393step2 raw19393step1; decide +kernel
      have hl : raw19393step2Labels = (fun j => raw19393step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19393step1 raw19393step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical19394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19394 raw19394Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19394 raw19394Labels = mixedMoment B raw19394step0 raw19394step0Labels := by
      have hz : ∀ j, raw19394 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19394step0 = (fun i j => raw19394 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19394step0 raw19394; decide +kernel
      have hl : raw19394step0Labels = raw19394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19394 raw19394Labels permutation265 hz
    mixedMoment B raw19394step0 raw19394step0Labels = mixedMoment B raw19394step1 raw19394step1Labels := by
      have hz : ∀ i, raw19394step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19394step1 = (fun i j => raw19394step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19394step1 raw19394step0; decide +kernel
      have hl : raw19394step1Labels = (fun j => raw19394step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19394step0 raw19394step0Labels permutation6 hz
    mixedMoment B raw19394step1 raw19394step1Labels = mixedMoment B raw19394step2 raw19394step2Labels := by
      have ha : raw19394step2 = (fun i j => raw19394step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19394step2 raw19394step1; decide +kernel
      have hl : raw19394step2Labels = raw19394step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19394step1 raw19394step1Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical19395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19395 raw19395Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw19395 raw19395Labels = mixedMoment B raw19395step0 raw19395step0Labels := by
      have hz : ∀ j, raw19395 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19395step0 = (fun i j => raw19395 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19395step0 raw19395; decide +kernel
      have hl : raw19395step0Labels = raw19395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19395 raw19395Labels permutation520 hz
    mixedMoment B raw19395step0 raw19395step0Labels = mixedMoment B raw19395step1 raw19395step1Labels := by
      have hz : ∀ j, raw19395step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19395step1 = (fun i j => raw19395step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19395step1 raw19395step0; decide +kernel
      have hl : raw19395step1Labels = raw19395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19395step0 raw19395step0Labels permutation56 hz
    mixedMoment B raw19395step1 raw19395step1Labels = mixedMoment B raw19395step2 raw19395step2Labels := by
      have hz : ∀ i, raw19395step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19395step2 = (fun i j => raw19395step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19395step2 raw19395step1; decide +kernel
      have hl : raw19395step2Labels = (fun j => raw19395step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19395step1 raw19395step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical19396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19396 raw19396Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw19396 raw19396Labels = mixedMoment B raw19396step0 raw19396step0Labels := by
      have hz : ∀ j, raw19396 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19396step0 = (fun i j => raw19396 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19396step0 raw19396; decide +kernel
      have hl : raw19396step0Labels = raw19396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19396 raw19396Labels permutation590 hz
    mixedMoment B raw19396step0 raw19396step0Labels = mixedMoment B raw19396step1 raw19396step1Labels := by
      have hz : ∀ j, raw19396step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19396step1 = (fun i j => raw19396step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19396step1 raw19396step0; decide +kernel
      have hl : raw19396step1Labels = raw19396step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19396step0 raw19396step0Labels permutation56 hz
    mixedMoment B raw19396step1 raw19396step1Labels = mixedMoment B raw19396step2 raw19396step2Labels := by
      have hz : ∀ i, raw19396step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19396step2 = (fun i j => raw19396step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19396step2 raw19396step1; decide +kernel
      have hl : raw19396step2Labels = (fun j => raw19396step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19396step1 raw19396step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical19397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19397 raw19397Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19397 raw19397Labels = mixedMoment B raw19397step0 raw19397step0Labels := by
      have hz : ∀ i, raw19397 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19397step0 = (fun i j => raw19397 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19397step0 raw19397; decide +kernel
      have hl : raw19397step0Labels = (fun j => raw19397Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19397 raw19397Labels permutation6 hz
    mixedMoment B raw19397step0 raw19397step0Labels = mixedMoment B raw19397step1 raw19397step1Labels := by
      have ha : raw19397step1 = (fun i j => raw19397step0 (permutation268 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19397step1 raw19397step0; decide +kernel
      have hl : raw19397step1Labels = raw19397step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19397step0 raw19397step0Labels permutation268 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical19398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19398 raw19398Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19398 raw19398Labels = mixedMoment B raw19398step0 raw19398step0Labels := by
      have hz : ∀ i, raw19398 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19398step0 = (fun i j => raw19398 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19398step0 raw19398; decide +kernel
      have hl : raw19398step0Labels = (fun j => raw19398Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19398 raw19398Labels permutation6 hz
    mixedMoment B raw19398step0 raw19398step0Labels = mixedMoment B raw19398step1 raw19398step1Labels := by
      have ha : raw19398step1 = (fun i j => raw19398step0 (permutation349 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19398step1 raw19398step0; decide +kernel
      have hl : raw19398step1Labels = raw19398step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19398step0 raw19398step0Labels permutation349 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical19399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19399 raw19399Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19399 raw19399Labels = mixedMoment B raw19399step0 raw19399step0Labels := by
      have hz : ∀ j, raw19399 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19399step0 = (fun i j => raw19399 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19399step0 raw19399; decide +kernel
      have hl : raw19399step0Labels = raw19399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19399 raw19399Labels permutation520 hz
    mixedMoment B raw19399step0 raw19399step0Labels = mixedMoment B raw19399step1 raw19399step1Labels := by
      have hz : ∀ i, raw19399step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19399step1 = (fun i j => raw19399step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19399step1 raw19399step0; decide +kernel
      have hl : raw19399step1Labels = (fun j => raw19399step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19399step0 raw19399step0Labels permutation6 hz
    mixedMoment B raw19399step1 raw19399step1Labels = mixedMoment B raw19399step2 raw19399step2Labels := by
      have ha : raw19399step2 = (fun i j => raw19399step1 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19399step2 raw19399step1; decide +kernel
      have hl : raw19399step2Labels = raw19399step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19399step1 raw19399step1Labels permutation122 permutation0
    mixedMoment B raw19399step2 raw19399step2Labels = mixedMoment B raw19399step3 raw19399step3Labels := by
      have ha : raw19399step3 = -raw19399step2 := by apply Matrix.ext; change ∀ i j, raw19399step3 i j = -(raw19399step2 i j); unfold raw19399step3 raw19399step2; decide +kernel
      have hl : raw19399step3Labels = raw19399step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical19400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19400 raw19400Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19400 raw19400Labels = mixedMoment B raw19400step0 raw19400step0Labels := by
      have hz : ∀ j, raw19400 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19400step0 = (fun i j => raw19400 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19400step0 raw19400; decide +kernel
      have hl : raw19400step0Labels = raw19400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19400 raw19400Labels permutation590 hz
    mixedMoment B raw19400step0 raw19400step0Labels = mixedMoment B raw19400step1 raw19400step1Labels := by
      have hz : ∀ i, raw19400step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19400step1 = (fun i j => raw19400step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19400step1 raw19400step0; decide +kernel
      have hl : raw19400step1Labels = (fun j => raw19400step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19400step0 raw19400step0Labels permutation6 hz
    mixedMoment B raw19400step1 raw19400step1Labels = mixedMoment B raw19400step2 raw19400step2Labels := by
      have ha : raw19400step2 = (fun i j => raw19400step1 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19400step2 raw19400step1; decide +kernel
      have hl : raw19400step2Labels = raw19400step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19400step1 raw19400step1Labels permutation122 permutation0
    mixedMoment B raw19400step2 raw19400step2Labels = mixedMoment B raw19400step3 raw19400step3Labels := by
      have ha : raw19400step3 = -raw19400step2 := by apply Matrix.ext; change ∀ i j, raw19400step3 i j = -(raw19400step2 i j); unfold raw19400step3 raw19400step2; decide +kernel
      have hl : raw19400step3Labels = raw19400step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical19401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19401 raw19401Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19401 raw19401Labels = mixedMoment B raw19401step0 raw19401step0Labels := by
      have hz : ∀ i, raw19401 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19401step0 = (fun i j => raw19401 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19401step0 raw19401; decide +kernel
      have hl : raw19401step0Labels = (fun j => raw19401Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19401 raw19401Labels permutation6 hz
    mixedMoment B raw19401step0 raw19401step0Labels = mixedMoment B raw19401step1 raw19401step1Labels := by
      have ha : raw19401step1 = (fun i j => raw19401step0 (permutation266 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19401step1 raw19401step0; decide +kernel
      have hl : raw19401step1Labels = raw19401step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19401step0 raw19401step0Labels permutation266 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical19402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19402 raw19402Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19402 raw19402Labels = mixedMoment B raw19402step0 raw19402step0Labels := by
      have hz : ∀ i, raw19402 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19402step0 = (fun i j => raw19402 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19402step0 raw19402; decide +kernel
      have hl : raw19402step0Labels = (fun j => raw19402Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19402 raw19402Labels permutation6 hz
    mixedMoment B raw19402step0 raw19402step0Labels = mixedMoment B raw19402step1 raw19402step1Labels := by
      have ha : raw19402step1 = (fun i j => raw19402step0 (permutation347 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19402step1 raw19402step0; decide +kernel
      have hl : raw19402step1Labels = raw19402step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19402step0 raw19402step0Labels permutation347 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical19403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19403 raw19403Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19403 raw19403Labels = mixedMoment B raw19403step0 raw19403step0Labels := by
      have hz : ∀ j, raw19403 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19403step0 = (fun i j => raw19403 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19403step0 raw19403; decide +kernel
      have hl : raw19403step0Labels = raw19403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19403 raw19403Labels permutation590 hz
    mixedMoment B raw19403step0 raw19403step0Labels = mixedMoment B raw19403step1 raw19403step1Labels := by
      have hz : ∀ i, raw19403step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19403step1 = (fun i j => raw19403step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19403step1 raw19403step0; decide +kernel
      have hl : raw19403step1Labels = (fun j => raw19403step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19403step0 raw19403step0Labels permutation6 hz
    mixedMoment B raw19403step1 raw19403step1Labels = mixedMoment B raw19403step2 raw19403step2Labels := by
      have ha : raw19403step2 = (fun i j => raw19403step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19403step2 raw19403step1; decide +kernel
      have hl : raw19403step2Labels = raw19403step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19403step1 raw19403step1Labels permutation146 permutation0
    mixedMoment B raw19403step2 raw19403step2Labels = mixedMoment B raw19403step3 raw19403step3Labels := by
      have ha : raw19403step3 = -raw19403step2 := by apply Matrix.ext; change ∀ i j, raw19403step3 i j = -(raw19403step2 i j); unfold raw19403step3 raw19403step2; decide +kernel
      have hl : raw19403step3Labels = raw19403step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical19404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19404 raw19404Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19404 raw19404Labels = mixedMoment B raw19404step0 raw19404step0Labels := by
      have hz : ∀ i, raw19404 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19404step0 = (fun i j => raw19404 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19404step0 raw19404; decide +kernel
      have hl : raw19404step0Labels = (fun j => raw19404Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19404 raw19404Labels permutation6 hz
    mixedMoment B raw19404step0 raw19404step0Labels = mixedMoment B raw19404step1 raw19404step1Labels := by
      have ha : raw19404step1 = (fun i j => raw19404step0 (permutation265 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19404step1 raw19404step0; decide +kernel
      have hl : raw19404step1Labels = raw19404step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19404step0 raw19404step0Labels permutation265 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical19405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19405 raw19405Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19405 raw19405Labels = mixedMoment B raw19405step0 raw19405step0Labels := by
      have hz : ∀ i, raw19405 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19405step0 = (fun i j => raw19405 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19405step0 raw19405; decide +kernel
      have hl : raw19405step0Labels = (fun j => raw19405Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19405 raw19405Labels permutation6 hz
    mixedMoment B raw19405step0 raw19405step0Labels = mixedMoment B raw19405step1 raw19405step1Labels := by
      have ha : raw19405step1 = (fun i j => raw19405step0 (permutation346 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19405step1 raw19405step0; decide +kernel
      have hl : raw19405step1Labels = raw19405step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19405step0 raw19405step0Labels permutation346 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical19406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19406 raw19406Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19406 raw19406Labels = mixedMoment B raw19406step0 raw19406step0Labels := by
      have hz : ∀ j, raw19406 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19406step0 = (fun i j => raw19406 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19406step0 raw19406; decide +kernel
      have hl : raw19406step0Labels = raw19406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19406 raw19406Labels permutation520 hz
    mixedMoment B raw19406step0 raw19406step0Labels = mixedMoment B raw19406step1 raw19406step1Labels := by
      have hz : ∀ i, raw19406step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19406step1 = (fun i j => raw19406step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19406step1 raw19406step0; decide +kernel
      have hl : raw19406step1Labels = (fun j => raw19406step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19406step0 raw19406step0Labels permutation6 hz
    mixedMoment B raw19406step1 raw19406step1Labels = mixedMoment B raw19406step2 raw19406step2Labels := by
      have ha : raw19406step2 = (fun i j => raw19406step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19406step2 raw19406step1; decide +kernel
      have hl : raw19406step2Labels = raw19406step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19406step1 raw19406step1Labels permutation146 permutation0
    mixedMoment B raw19406step2 raw19406step2Labels = mixedMoment B raw19406step3 raw19406step3Labels := by
      have ha : raw19406step3 = -raw19406step2 := by apply Matrix.ext; change ∀ i j, raw19406step3 i j = -(raw19406step2 i j); unfold raw19406step3 raw19406step2; decide +kernel
      have hl : raw19406step3Labels = raw19406step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical19407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19407 raw19407Labels = mixedMoment B node617 node617Labels := by
  calc
    mixedMoment B raw19407 raw19407Labels = mixedMoment B raw19407step0 raw19407step0Labels := by
      have hz : ∀ j, raw19407 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19407step0 = (fun i j => raw19407 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19407step0 raw19407; decide +kernel
      have hl : raw19407step0Labels = raw19407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19407 raw19407Labels permutation434 hz
    mixedMoment B raw19407step0 raw19407step0Labels = mixedMoment B raw19407step1 raw19407step1Labels := by
      have hz : ∀ j, raw19407step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19407step1 = (fun i j => raw19407step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19407step1 raw19407step0; decide +kernel
      have hl : raw19407step1Labels = raw19407step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19407step0 raw19407step0Labels permutation80 hz
    mixedMoment B raw19407step1 raw19407step1Labels = mixedMoment B raw19407step2 raw19407step2Labels := by
      have hz : ∀ j, raw19407step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19407step2 = (fun i j => raw19407step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19407step2 raw19407step1; decide +kernel
      have hl : raw19407step2Labels = raw19407step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19407step1 raw19407step1Labels permutation14 hz
    _ = mixedMoment B node617 node617Labels := by rfl

theorem canonical19408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19408 raw19408Labels = mixedMoment B node936 node936Labels := by
  calc
    mixedMoment B raw19408 raw19408Labels = mixedMoment B raw19408step0 raw19408step0Labels := by
      have hz : ∀ j, raw19408 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19408step0 = (fun i j => raw19408 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19408step0 raw19408; decide +kernel
      have hl : raw19408step0Labels = raw19408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19408 raw19408Labels permutation434 hz
    mixedMoment B raw19408step0 raw19408step0Labels = mixedMoment B raw19408step1 raw19408step1Labels := by
      have hz : ∀ j, raw19408step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19408step1 = (fun i j => raw19408step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19408step1 raw19408step0; decide +kernel
      have hl : raw19408step1Labels = raw19408step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19408step0 raw19408step0Labels permutation80 hz
    _ = mixedMoment B node936 node936Labels := by rfl

theorem canonical19409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19409 raw19409Labels = mixedMoment B node936 node936Labels := by
  calc
    mixedMoment B raw19409 raw19409Labels = mixedMoment B raw19409step0 raw19409step0Labels := by
      have hz : ∀ j, raw19409 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19409step0 = (fun i j => raw19409 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19409step0 raw19409; decide +kernel
      have hl : raw19409step0Labels = raw19409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19409 raw19409Labels permutation434 hz
    mixedMoment B raw19409step0 raw19409step0Labels = mixedMoment B raw19409step1 raw19409step1Labels := by
      have hz : ∀ j, raw19409step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19409step1 = (fun i j => raw19409step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19409step1 raw19409step0; decide +kernel
      have hl : raw19409step1Labels = raw19409step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19409step0 raw19409step0Labels permutation56 hz
    _ = mixedMoment B node936 node936Labels := by rfl

theorem canonical19410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19410 raw19410Labels = mixedMoment B node936 node936Labels := by
  calc
    mixedMoment B raw19410 raw19410Labels = mixedMoment B raw19410step0 raw19410step0Labels := by
      have hz : ∀ j, raw19410 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19410step0 = (fun i j => raw19410 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19410step0 raw19410; decide +kernel
      have hl : raw19410step0Labels = raw19410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19410 raw19410Labels permutation346 hz
    mixedMoment B raw19410step0 raw19410step0Labels = mixedMoment B raw19410step1 raw19410step1Labels := by
      have hz : ∀ j, raw19410step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19410step1 = (fun i j => raw19410step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19410step1 raw19410step0; decide +kernel
      have hl : raw19410step1Labels = raw19410step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19410step0 raw19410step0Labels permutation56 hz
    _ = mixedMoment B node936 node936Labels := by rfl

theorem canonical19411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19411 raw19411Labels = mixedMoment B node1064 node1064Labels := by
  calc
    mixedMoment B raw19411 raw19411Labels = mixedMoment B raw19411step0 raw19411step0Labels := by
      have hz : ∀ j, raw19411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19411step0 = (fun i j => raw19411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19411step0 raw19411; decide +kernel
      have hl : raw19411step0Labels = raw19411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19411 raw19411Labels permutation434 hz
    mixedMoment B raw19411step0 raw19411step0Labels = mixedMoment B raw19411step1 raw19411step1Labels := by
      have hz : ∀ j, raw19411step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19411step1 = (fun i j => raw19411step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19411step1 raw19411step0; decide +kernel
      have hl : raw19411step1Labels = raw19411step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19411step0 raw19411step0Labels permutation80 hz
    mixedMoment B raw19411step1 raw19411step1Labels = mixedMoment B raw19411step2 raw19411step2Labels := by
      have hz : ∀ j, raw19411step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19411step2 = (fun i j => raw19411step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19411step2 raw19411step1; decide +kernel
      have hl : raw19411step2Labels = raw19411step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19411step1 raw19411step1Labels permutation14 hz
    _ = mixedMoment B node1064 node1064Labels := by rfl

theorem canonical19412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19412 raw19412Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw19412 raw19412Labels = mixedMoment B raw19412step0 raw19412step0Labels := by
      have hz : ∀ j, raw19412 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19412step0 = (fun i j => raw19412 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19412step0 raw19412; decide +kernel
      have hl : raw19412step0Labels = raw19412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19412 raw19412Labels permutation434 hz
    mixedMoment B raw19412step0 raw19412step0Labels = mixedMoment B raw19412step1 raw19412step1Labels := by
      have hz : ∀ j, raw19412step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19412step1 = (fun i j => raw19412step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19412step1 raw19412step0; decide +kernel
      have hl : raw19412step1Labels = raw19412step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19412step0 raw19412step0Labels permutation80 hz
    mixedMoment B raw19412step1 raw19412step1Labels = mixedMoment B raw19412step2 raw19412step2Labels := by
      have hz : ∀ j, raw19412step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19412step2 = (fun i j => raw19412step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19412step2 raw19412step1; decide +kernel
      have hl : raw19412step2Labels = raw19412step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19412step1 raw19412step1Labels permutation14 hz
    _ = mixedMoment B node1091 node1091Labels := by rfl

theorem canonical19413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19413 raw19413Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw19413 raw19413Labels = mixedMoment B raw19413step0 raw19413step0Labels := by
      have hz : ∀ j, raw19413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19413step0 = (fun i j => raw19413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19413step0 raw19413; decide +kernel
      have hl : raw19413step0Labels = raw19413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19413 raw19413Labels permutation434 hz
    mixedMoment B raw19413step0 raw19413step0Labels = mixedMoment B raw19413step1 raw19413step1Labels := by
      have hz : ∀ j, raw19413step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19413step1 = (fun i j => raw19413step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19413step1 raw19413step0; decide +kernel
      have hl : raw19413step1Labels = raw19413step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19413step0 raw19413step0Labels permutation80 hz
    mixedMoment B raw19413step1 raw19413step1Labels = mixedMoment B raw19413step2 raw19413step2Labels := by
      have hz : ∀ j, raw19413step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19413step2 = (fun i j => raw19413step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19413step2 raw19413step1; decide +kernel
      have hl : raw19413step2Labels = raw19413step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19413step1 raw19413step1Labels permutation14 hz
    mixedMoment B raw19413step2 raw19413step2Labels = mixedMoment B raw19413step3 raw19413step3Labels := by
      have ha : raw19413step3 = (fun i j => raw19413step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19413step3 raw19413step2; decide +kernel
      have hl : raw19413step3Labels = raw19413step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19413step2 raw19413step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical19414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19414 raw19414Labels = mixedMoment B node1757 node1757Labels := by
  calc
    mixedMoment B raw19414 raw19414Labels = mixedMoment B raw19414step0 raw19414step0Labels := by
      have hz : ∀ j, raw19414 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19414step0 = (fun i j => raw19414 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19414step0 raw19414; decide +kernel
      have hl : raw19414step0Labels = raw19414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19414 raw19414Labels permutation434 hz
    mixedMoment B raw19414step0 raw19414step0Labels = mixedMoment B raw19414step1 raw19414step1Labels := by
      have hz : ∀ j, raw19414step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19414step1 = (fun i j => raw19414step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19414step1 raw19414step0; decide +kernel
      have hl : raw19414step1Labels = raw19414step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19414step0 raw19414step0Labels permutation80 hz
    mixedMoment B raw19414step1 raw19414step1Labels = mixedMoment B raw19414step2 raw19414step2Labels := by
      have hz : ∀ j, raw19414step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19414step2 = (fun i j => raw19414step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19414step2 raw19414step1; decide +kernel
      have hl : raw19414step2Labels = raw19414step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19414step1 raw19414step1Labels permutation14 hz
    mixedMoment B raw19414step2 raw19414step2Labels = mixedMoment B raw19414step3 raw19414step3Labels := by
      have ha : raw19414step3 = (fun i j => raw19414step2 (permutation6 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19414step3 raw19414step2; decide +kernel
      have hl : raw19414step3Labels = raw19414step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19414step2 raw19414step2Labels permutation6 permutation2
    _ = mixedMoment B node1757 node1757Labels := by rfl

theorem canonical19415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19415 raw19415Labels = mixedMoment B node1629 node1629Labels := by
  calc
    mixedMoment B raw19415 raw19415Labels = mixedMoment B raw19415step0 raw19415step0Labels := by
      have hz : ∀ j, raw19415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19415step0 = (fun i j => raw19415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19415step0 raw19415; decide +kernel
      have hl : raw19415step0Labels = raw19415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19415 raw19415Labels permutation434 hz
    mixedMoment B raw19415step0 raw19415step0Labels = mixedMoment B raw19415step1 raw19415step1Labels := by
      have hz : ∀ j, raw19415step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19415step1 = (fun i j => raw19415step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19415step1 raw19415step0; decide +kernel
      have hl : raw19415step1Labels = raw19415step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19415step0 raw19415step0Labels permutation80 hz
    mixedMoment B raw19415step1 raw19415step1Labels = mixedMoment B raw19415step2 raw19415step2Labels := by
      have ha : raw19415step2 = (fun i j => raw19415step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19415step2 raw19415step1; decide +kernel
      have hl : raw19415step2Labels = raw19415step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19415step1 raw19415step1Labels permutation29 permutation2
    _ = mixedMoment B node1629 node1629Labels := by rfl

theorem canonical19416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19416 raw19416Labels = mixedMoment B node1629 node1629Labels := by
  calc
    mixedMoment B raw19416 raw19416Labels = mixedMoment B raw19416step0 raw19416step0Labels := by
      have hz : ∀ j, raw19416 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19416step0 = (fun i j => raw19416 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19416step0 raw19416; decide +kernel
      have hl : raw19416step0Labels = raw19416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19416 raw19416Labels permutation434 hz
    mixedMoment B raw19416step0 raw19416step0Labels = mixedMoment B raw19416step1 raw19416step1Labels := by
      have hz : ∀ j, raw19416step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19416step1 = (fun i j => raw19416step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19416step1 raw19416step0; decide +kernel
      have hl : raw19416step1Labels = raw19416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19416step0 raw19416step0Labels permutation56 hz
    mixedMoment B raw19416step1 raw19416step1Labels = mixedMoment B raw19416step2 raw19416step2Labels := by
      have ha : raw19416step2 = (fun i j => raw19416step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19416step2 raw19416step1; decide +kernel
      have hl : raw19416step2Labels = raw19416step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19416step1 raw19416step1Labels permutation29 permutation2
    _ = mixedMoment B node1629 node1629Labels := by rfl

theorem canonical19417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19417 raw19417Labels = mixedMoment B node1629 node1629Labels := by
  calc
    mixedMoment B raw19417 raw19417Labels = mixedMoment B raw19417step0 raw19417step0Labels := by
      have hz : ∀ j, raw19417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19417step0 = (fun i j => raw19417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19417step0 raw19417; decide +kernel
      have hl : raw19417step0Labels = raw19417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19417 raw19417Labels permutation346 hz
    mixedMoment B raw19417step0 raw19417step0Labels = mixedMoment B raw19417step1 raw19417step1Labels := by
      have hz : ∀ j, raw19417step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19417step1 = (fun i j => raw19417step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19417step1 raw19417step0; decide +kernel
      have hl : raw19417step1Labels = raw19417step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19417step0 raw19417step0Labels permutation56 hz
    mixedMoment B raw19417step1 raw19417step1Labels = mixedMoment B raw19417step2 raw19417step2Labels := by
      have ha : raw19417step2 = (fun i j => raw19417step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19417step2 raw19417step1; decide +kernel
      have hl : raw19417step2Labels = raw19417step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19417step1 raw19417step1Labels permutation29 permutation2
    _ = mixedMoment B node1629 node1629Labels := by rfl

theorem canonical19418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19418 raw19418Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw19418 raw19418Labels = mixedMoment B raw19418step0 raw19418step0Labels := by
      have hz : ∀ j, raw19418 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19418step0 = (fun i j => raw19418 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19418step0 raw19418; decide +kernel
      have hl : raw19418step0Labels = raw19418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19418 raw19418Labels permutation434 hz
    mixedMoment B raw19418step0 raw19418step0Labels = mixedMoment B raw19418step1 raw19418step1Labels := by
      have hz : ∀ j, raw19418step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19418step1 = (fun i j => raw19418step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19418step1 raw19418step0; decide +kernel
      have hl : raw19418step1Labels = raw19418step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19418step0 raw19418step0Labels permutation80 hz
    mixedMoment B raw19418step1 raw19418step1Labels = mixedMoment B raw19418step2 raw19418step2Labels := by
      have hz : ∀ j, raw19418step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19418step2 = (fun i j => raw19418step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19418step2 raw19418step1; decide +kernel
      have hl : raw19418step2Labels = raw19418step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19418step1 raw19418step1Labels permutation14 hz
    mixedMoment B raw19418step2 raw19418step2Labels = mixedMoment B raw19418step3 raw19418step3Labels := by
      have ha : raw19418step3 = (fun i j => raw19418step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19418step3 raw19418step2; decide +kernel
      have hl : raw19418step3Labels = raw19418step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19418step2 raw19418step2Labels permutation7 permutation2
    _ = mixedMoment B node1752 node1752Labels := by rfl

theorem canonical19419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19419 raw19419Labels = mixedMoment B node862 node862Labels := by
  calc
    mixedMoment B raw19419 raw19419Labels = mixedMoment B raw19419step0 raw19419step0Labels := by
      have hz : ∀ j, raw19419 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19419step0 = (fun i j => raw19419 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19419step0 raw19419; decide +kernel
      have hl : raw19419step0Labels = raw19419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19419 raw19419Labels permutation434 hz
    mixedMoment B raw19419step0 raw19419step0Labels = mixedMoment B raw19419step1 raw19419step1Labels := by
      have hz : ∀ j, raw19419step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19419step1 = (fun i j => raw19419step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19419step1 raw19419step0; decide +kernel
      have hl : raw19419step1Labels = raw19419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19419step0 raw19419step0Labels permutation80 hz
    mixedMoment B raw19419step1 raw19419step1Labels = mixedMoment B raw19419step2 raw19419step2Labels := by
      have hz : ∀ j, raw19419step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19419step2 = (fun i j => raw19419step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19419step2 raw19419step1; decide +kernel
      have hl : raw19419step2Labels = raw19419step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19419step1 raw19419step1Labels permutation14 hz
    mixedMoment B raw19419step2 raw19419step2Labels = mixedMoment B raw19419step3 raw19419step3Labels := by
      have ha : raw19419step3 = (fun i j => raw19419step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19419step3 raw19419step2; decide +kernel
      have hl : raw19419step3Labels = raw19419step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19419step2 raw19419step2Labels permutation7 permutation2
    _ = mixedMoment B node862 node862Labels := by rfl

theorem canonical19420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19420 raw19420Labels = mixedMoment B node4072 node4072Labels := by
  calc
    mixedMoment B raw19420 raw19420Labels = mixedMoment B raw19420step0 raw19420step0Labels := by
      have hz : ∀ j, raw19420 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19420step0 = (fun i j => raw19420 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19420step0 raw19420; decide +kernel
      have hl : raw19420step0Labels = raw19420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19420 raw19420Labels permutation520 hz
    mixedMoment B raw19420step0 raw19420step0Labels = mixedMoment B raw19420step1 raw19420step1Labels := by
      have hz : ∀ j, raw19420step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19420step1 = (fun i j => raw19420step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19420step1 raw19420step0; decide +kernel
      have hl : raw19420step1Labels = raw19420step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19420step0 raw19420step0Labels permutation104 hz
    mixedMoment B raw19420step1 raw19420step1Labels = mixedMoment B raw19420step2 raw19420step2Labels := by
      have hz : ∀ j, raw19420step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19420step2 = (fun i j => raw19420step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19420step2 raw19420step1; decide +kernel
      have hl : raw19420step2Labels = raw19420step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19420step1 raw19420step1Labels permutation20 hz
    mixedMoment B raw19420step2 raw19420step2Labels = mixedMoment B raw19420step3 raw19420step3Labels := by
      have hz : ∀ j, raw19420step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19420step3 = (fun i j => raw19420step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19420step3 raw19420step2; decide +kernel
      have hl : raw19420step3Labels = raw19420step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19420step2 raw19420step2Labels permutation4 hz
    mixedMoment B raw19420step3 raw19420step3Labels = mixedMoment B raw19420step4 raw19420step4Labels := by
      have ha : raw19420step4 = (fun i j => raw19420step3 (permutation1 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19420step4 raw19420step3; decide +kernel
      have hl : raw19420step4Labels = raw19420step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19420step3 raw19420step3Labels permutation1 permutation0
    _ = mixedMoment B node4072 node4072Labels := by rfl

theorem canonical19426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19426 raw19426Labels = mixedMoment B node1749 node1749Labels := by
  calc
    mixedMoment B raw19426 raw19426Labels = mixedMoment B raw19426step0 raw19426step0Labels := by
      have hz : ∀ j, raw19426 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19426step0 = (fun i j => raw19426 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19426step0 raw19426; decide +kernel
      have hl : raw19426step0Labels = raw19426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19426 raw19426Labels permutation434 hz
    mixedMoment B raw19426step0 raw19426step0Labels = mixedMoment B raw19426step1 raw19426step1Labels := by
      have hz : ∀ j, raw19426step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19426step1 = (fun i j => raw19426step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19426step1 raw19426step0; decide +kernel
      have hl : raw19426step1Labels = raw19426step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19426step0 raw19426step0Labels permutation80 hz
    mixedMoment B raw19426step1 raw19426step1Labels = mixedMoment B raw19426step2 raw19426step2Labels := by
      have ha : raw19426step2 = (fun i j => raw19426step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19426step2 raw19426step1; decide +kernel
      have hl : raw19426step2Labels = raw19426step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19426step1 raw19426step1Labels permutation29 permutation2
    _ = mixedMoment B node1749 node1749Labels := by rfl

theorem canonical19427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19427 raw19427Labels = mixedMoment B node1749 node1749Labels := by
  calc
    mixedMoment B raw19427 raw19427Labels = mixedMoment B raw19427step0 raw19427step0Labels := by
      have hz : ∀ j, raw19427 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19427step0 = (fun i j => raw19427 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19427step0 raw19427; decide +kernel
      have hl : raw19427step0Labels = raw19427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19427 raw19427Labels permutation434 hz
    mixedMoment B raw19427step0 raw19427step0Labels = mixedMoment B raw19427step1 raw19427step1Labels := by
      have hz : ∀ j, raw19427step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19427step1 = (fun i j => raw19427step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19427step1 raw19427step0; decide +kernel
      have hl : raw19427step1Labels = raw19427step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19427step0 raw19427step0Labels permutation56 hz
    mixedMoment B raw19427step1 raw19427step1Labels = mixedMoment B raw19427step2 raw19427step2Labels := by
      have ha : raw19427step2 = (fun i j => raw19427step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19427step2 raw19427step1; decide +kernel
      have hl : raw19427step2Labels = raw19427step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19427step1 raw19427step1Labels permutation29 permutation2
    _ = mixedMoment B node1749 node1749Labels := by rfl

theorem canonical19428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19428 raw19428Labels = mixedMoment B node1749 node1749Labels := by
  calc
    mixedMoment B raw19428 raw19428Labels = mixedMoment B raw19428step0 raw19428step0Labels := by
      have hz : ∀ j, raw19428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19428step0 = (fun i j => raw19428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19428step0 raw19428; decide +kernel
      have hl : raw19428step0Labels = raw19428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19428 raw19428Labels permutation346 hz
    mixedMoment B raw19428step0 raw19428step0Labels = mixedMoment B raw19428step1 raw19428step1Labels := by
      have hz : ∀ j, raw19428step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19428step1 = (fun i j => raw19428step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19428step1 raw19428step0; decide +kernel
      have hl : raw19428step1Labels = raw19428step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19428step0 raw19428step0Labels permutation56 hz
    mixedMoment B raw19428step1 raw19428step1Labels = mixedMoment B raw19428step2 raw19428step2Labels := by
      have ha : raw19428step2 = (fun i j => raw19428step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19428step2 raw19428step1; decide +kernel
      have hl : raw19428step2Labels = raw19428step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19428step1 raw19428step1Labels permutation29 permutation2
    _ = mixedMoment B node1749 node1749Labels := by rfl

theorem canonical19429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19429 raw19429Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw19429 raw19429Labels = mixedMoment B raw19429step0 raw19429step0Labels := by
      have hz : ∀ j, raw19429 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19429step0 = (fun i j => raw19429 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19429step0 raw19429; decide +kernel
      have hl : raw19429step0Labels = raw19429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19429 raw19429Labels permutation434 hz
    mixedMoment B raw19429step0 raw19429step0Labels = mixedMoment B raw19429step1 raw19429step1Labels := by
      have hz : ∀ j, raw19429step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19429step1 = (fun i j => raw19429step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19429step1 raw19429step0; decide +kernel
      have hl : raw19429step1Labels = raw19429step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19429step0 raw19429step0Labels permutation80 hz
    mixedMoment B raw19429step1 raw19429step1Labels = mixedMoment B raw19429step2 raw19429step2Labels := by
      have hz : ∀ j, raw19429step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19429step2 = (fun i j => raw19429step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19429step2 raw19429step1; decide +kernel
      have hl : raw19429step2Labels = raw19429step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19429step1 raw19429step1Labels permutation14 hz
    mixedMoment B raw19429step2 raw19429step2Labels = mixedMoment B raw19429step3 raw19429step3Labels := by
      have ha : raw19429step3 = (fun i j => raw19429step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19429step3 raw19429step2; decide +kernel
      have hl : raw19429step3Labels = raw19429step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19429step2 raw19429step2Labels permutation2 permutation4
    mixedMoment B raw19429step3 raw19429step3Labels = mixedMoment B raw19429step4 raw19429step4Labels := by
      have ha : raw19429step4 = -raw19429step3 := by apply Matrix.ext; change ∀ i j, raw19429step4 i j = -(raw19429step3 i j); unfold raw19429step4 raw19429step3; decide +kernel
      have hl : raw19429step4Labels = raw19429step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1752 node1752Labels := by rfl

theorem canonical19437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19437 raw19437Labels = mixedMoment B node587 node587Labels := by
  calc
    mixedMoment B raw19437 raw19437Labels = mixedMoment B raw19437step0 raw19437step0Labels := by
      have hz : ∀ j, raw19437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19437step0 = (fun i j => raw19437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19437step0 raw19437; decide +kernel
      have hl : raw19437step0Labels = raw19437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19437 raw19437Labels permutation346 hz
    mixedMoment B raw19437step0 raw19437step0Labels = mixedMoment B raw19437step1 raw19437step1Labels := by
      have hz : ∀ j, raw19437step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19437step1 = (fun i j => raw19437step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19437step1 raw19437step0; decide +kernel
      have hl : raw19437step1Labels = raw19437step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19437step0 raw19437step0Labels permutation56 hz
    mixedMoment B raw19437step1 raw19437step1Labels = mixedMoment B raw19437step2 raw19437step2Labels := by
      have ha : raw19437step2 = (fun i j => raw19437step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19437step2 raw19437step1; decide +kernel
      have hl : raw19437step2Labels = raw19437step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19437step1 raw19437step1Labels permutation10 permutation2
    _ = mixedMoment B node587 node587Labels := by rfl

theorem canonical19438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19438 raw19438Labels = mixedMoment B node911 node911Labels := by
  calc
    mixedMoment B raw19438 raw19438Labels = mixedMoment B raw19438step0 raw19438step0Labels := by
      have hz : ∀ j, raw19438 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19438step0 = (fun i j => raw19438 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19438step0 raw19438; decide +kernel
      have hl : raw19438step0Labels = raw19438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19438 raw19438Labels permutation346 hz
    mixedMoment B raw19438step0 raw19438step0Labels = mixedMoment B raw19438step1 raw19438step1Labels := by
      have ha : raw19438step1 = (fun i j => raw19438step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19438step1 raw19438step0; decide +kernel
      have hl : raw19438step1Labels = raw19438step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19438step0 raw19438step0Labels permutation34 permutation2
    _ = mixedMoment B node911 node911Labels := by rfl

theorem canonical19439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19439 raw19439Labels = mixedMoment B node911 node911Labels := by
  calc
    mixedMoment B raw19439 raw19439Labels = mixedMoment B raw19439step0 raw19439step0Labels := by
      have hz : ∀ j, raw19439 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19439step0 = (fun i j => raw19439 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19439step0 raw19439; decide +kernel
      have hl : raw19439step0Labels = raw19439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19439 raw19439Labels permutation265 hz
    mixedMoment B raw19439step0 raw19439step0Labels = mixedMoment B raw19439step1 raw19439step1Labels := by
      have ha : raw19439step1 = (fun i j => raw19439step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19439step1 raw19439step0; decide +kernel
      have hl : raw19439step1Labels = raw19439step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19439step0 raw19439step0Labels permutation34 permutation2
    _ = mixedMoment B node911 node911Labels := by rfl

theorem canonical19440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19440 raw19440Labels = mixedMoment B node1027 node1027Labels := by
  calc
    mixedMoment B raw19440 raw19440Labels = mixedMoment B raw19440step0 raw19440step0Labels := by
      have hz : ∀ j, raw19440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19440step0 = (fun i j => raw19440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19440step0 raw19440; decide +kernel
      have hl : raw19440step0Labels = raw19440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19440 raw19440Labels permutation346 hz
    mixedMoment B raw19440step0 raw19440step0Labels = mixedMoment B raw19440step1 raw19440step1Labels := by
      have hz : ∀ j, raw19440step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19440step1 = (fun i j => raw19440step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19440step1 raw19440step0; decide +kernel
      have hl : raw19440step1Labels = raw19440step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19440step0 raw19440step0Labels permutation56 hz
    _ = mixedMoment B node1027 node1027Labels := by rfl

theorem canonical19441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19441 raw19441Labels = mixedMoment B node951 node951Labels := by
  calc
    mixedMoment B raw19441 raw19441Labels = mixedMoment B raw19441step0 raw19441step0Labels := by
      have hz : ∀ j, raw19441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19441step0 = (fun i j => raw19441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19441step0 raw19441; decide +kernel
      have hl : raw19441step0Labels = raw19441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19441 raw19441Labels permutation346 hz
    mixedMoment B raw19441step0 raw19441step0Labels = mixedMoment B raw19441step1 raw19441step1Labels := by
      have hz : ∀ j, raw19441step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19441step1 = (fun i j => raw19441step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19441step1 raw19441step0; decide +kernel
      have hl : raw19441step1Labels = raw19441step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19441step0 raw19441step0Labels permutation56 hz
    mixedMoment B raw19441step1 raw19441step1Labels = mixedMoment B raw19441step2 raw19441step2Labels := by
      have ha : raw19441step2 = (fun i j => raw19441step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19441step2 raw19441step1; decide +kernel
      have hl : raw19441step2Labels = raw19441step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19441step1 raw19441step1Labels permutation10 permutation2
    _ = mixedMoment B node951 node951Labels := by rfl

theorem canonical19442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19442 raw19442Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw19442 raw19442Labels = mixedMoment B raw19442step0 raw19442step0Labels := by
      have hz : ∀ j, raw19442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19442step0 = (fun i j => raw19442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19442step0 raw19442; decide +kernel
      have hl : raw19442step0Labels = raw19442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19442 raw19442Labels permutation346 hz
    mixedMoment B raw19442step0 raw19442step0Labels = mixedMoment B raw19442step1 raw19442step1Labels := by
      have hz : ∀ j, raw19442step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19442step1 = (fun i j => raw19442step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19442step1 raw19442step0; decide +kernel
      have hl : raw19442step1Labels = raw19442step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19442step0 raw19442step0Labels permutation56 hz
    mixedMoment B raw19442step1 raw19442step1Labels = mixedMoment B raw19442step2 raw19442step2Labels := by
      have ha : raw19442step2 = (fun i j => raw19442step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19442step2 raw19442step1; decide +kernel
      have hl : raw19442step2Labels = raw19442step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19442step1 raw19442step1Labels permutation10 permutation2
    _ = mixedMoment B node1046 node1046Labels := by rfl

theorem canonical19443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19443 raw19443Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw19443 raw19443Labels = mixedMoment B raw19443step0 raw19443step0Labels := by
      have hz : ∀ j, raw19443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19443step0 = (fun i j => raw19443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19443step0 raw19443; decide +kernel
      have hl : raw19443step0Labels = raw19443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19443 raw19443Labels permutation346 hz
    mixedMoment B raw19443step0 raw19443step0Labels = mixedMoment B raw19443step1 raw19443step1Labels := by
      have hz : ∀ j, raw19443step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19443step1 = (fun i j => raw19443step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19443step1 raw19443step0; decide +kernel
      have hl : raw19443step1Labels = raw19443step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19443step0 raw19443step0Labels permutation56 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical19444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19444 raw19444Labels = mixedMoment B node1615 node1615Labels := by
  calc
    mixedMoment B raw19444 raw19444Labels = mixedMoment B raw19444step0 raw19444step0Labels := by
      have hz : ∀ j, raw19444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19444step0 = (fun i j => raw19444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19444step0 raw19444; decide +kernel
      have hl : raw19444step0Labels = raw19444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19444 raw19444Labels permutation346 hz
    mixedMoment B raw19444step0 raw19444step0Labels = mixedMoment B raw19444step1 raw19444step1Labels := by
      have ha : raw19444step1 = (fun i j => raw19444step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19444step1 raw19444step0; decide +kernel
      have hl : raw19444step1Labels = raw19444step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19444step0 raw19444step0Labels permutation137 permutation2
    _ = mixedMoment B node1615 node1615Labels := by rfl

theorem canonical19445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19445 raw19445Labels = mixedMoment B node1615 node1615Labels := by
  calc
    mixedMoment B raw19445 raw19445Labels = mixedMoment B raw19445step0 raw19445step0Labels := by
      have hz : ∀ j, raw19445 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19445step0 = (fun i j => raw19445 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19445step0 raw19445; decide +kernel
      have hl : raw19445step0Labels = raw19445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19445 raw19445Labels permutation265 hz
    mixedMoment B raw19445step0 raw19445step0Labels = mixedMoment B raw19445step1 raw19445step1Labels := by
      have ha : raw19445step1 = (fun i j => raw19445step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19445step1 raw19445step0; decide +kernel
      have hl : raw19445step1Labels = raw19445step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19445step0 raw19445step0Labels permutation137 permutation2
    _ = mixedMoment B node1615 node1615Labels := by rfl

theorem canonical19446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19446 raw19446Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw19446 raw19446Labels = mixedMoment B raw19446step0 raw19446step0Labels := by
      have hz : ∀ j, raw19446 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19446step0 = (fun i j => raw19446 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19446step0 raw19446; decide +kernel
      have hl : raw19446step0Labels = raw19446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19446 raw19446Labels permutation520 hz
    mixedMoment B raw19446step0 raw19446step0Labels = mixedMoment B raw19446step1 raw19446step1Labels := by
      have hz : ∀ j, raw19446step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19446step1 = (fun i j => raw19446step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19446step1 raw19446step0; decide +kernel
      have hl : raw19446step1Labels = raw19446step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19446step0 raw19446step0Labels permutation80 hz
    mixedMoment B raw19446step1 raw19446step1Labels = mixedMoment B raw19446step2 raw19446step2Labels := by
      have hz : ∀ j, raw19446step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19446step2 = (fun i j => raw19446step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19446step2 raw19446step1; decide +kernel
      have hl : raw19446step2Labels = raw19446step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19446step1 raw19446step1Labels permutation14 hz
    mixedMoment B raw19446step2 raw19446step2Labels = mixedMoment B raw19446step3 raw19446step3Labels := by
      have ha : raw19446step3 = (fun i j => raw19446step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19446step3 raw19446step2; decide +kernel
      have hl : raw19446step3Labels = raw19446step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19446step2 raw19446step2Labels permutation7 permutation2
    _ = mixedMoment B node1752 node1752Labels := by rfl

theorem canonical19447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19447 raw19447Labels = mixedMoment B node849 node849Labels := by
  calc
    mixedMoment B raw19447 raw19447Labels = mixedMoment B raw19447step0 raw19447step0Labels := by
      have hz : ∀ j, raw19447 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19447step0 = (fun i j => raw19447 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19447step0 raw19447; decide +kernel
      have hl : raw19447step0Labels = raw19447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19447 raw19447Labels permutation346 hz
    mixedMoment B raw19447step0 raw19447step0Labels = mixedMoment B raw19447step1 raw19447step1Labels := by
      have hz : ∀ j, raw19447step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19447step1 = (fun i j => raw19447step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19447step1 raw19447step0; decide +kernel
      have hl : raw19447step1Labels = raw19447step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19447step0 raw19447step0Labels permutation56 hz
    mixedMoment B raw19447step1 raw19447step1Labels = mixedMoment B raw19447step2 raw19447step2Labels := by
      have ha : raw19447step2 = (fun i j => raw19447step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19447step2 raw19447step1; decide +kernel
      have hl : raw19447step2Labels = raw19447step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19447step1 raw19447step1Labels permutation29 permutation2
    _ = mixedMoment B node849 node849Labels := by rfl

theorem canonical19452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19452 raw19452Labels = mixedMoment B node797 node797Labels := by
  calc
    mixedMoment B raw19452 raw19452Labels = mixedMoment B raw19452step0 raw19452step0Labels := by
      have hz : ∀ j, raw19452 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19452step0 = (fun i j => raw19452 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19452step0 raw19452; decide +kernel
      have hl : raw19452step0Labels = raw19452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19452 raw19452Labels permutation346 hz
    mixedMoment B raw19452step0 raw19452step0Labels = mixedMoment B raw19452step1 raw19452step1Labels := by
      have hz : ∀ j, raw19452step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19452step1 = (fun i j => raw19452step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19452step1 raw19452step0; decide +kernel
      have hl : raw19452step1Labels = raw19452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19452step0 raw19452step0Labels permutation56 hz
    mixedMoment B raw19452step1 raw19452step1Labels = mixedMoment B raw19452step2 raw19452step2Labels := by
      have ha : raw19452step2 = (fun i j => raw19452step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19452step2 raw19452step1; decide +kernel
      have hl : raw19452step2Labels = raw19452step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19452step1 raw19452step1Labels permutation29 permutation2
    mixedMoment B raw19452step2 raw19452step2Labels = mixedMoment B raw19452step3 raw19452step3Labels := by
      have ha : raw19452step3 = -raw19452step2 := by apply Matrix.ext; change ∀ i j, raw19452step3 i j = -(raw19452step2 i j); unfold raw19452step3 raw19452step2; decide +kernel
      have hl : raw19452step3Labels = raw19452step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node797 node797Labels := by rfl

theorem canonical19453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19453 raw19453Labels = mixedMoment B node794 node794Labels := by
  calc
    mixedMoment B raw19453 raw19453Labels = mixedMoment B raw19453step0 raw19453step0Labels := by
      have hz : ∀ j, raw19453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19453step0 = (fun i j => raw19453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19453step0 raw19453; decide +kernel
      have hl : raw19453step0Labels = raw19453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19453 raw19453Labels permutation346 hz
    mixedMoment B raw19453step0 raw19453step0Labels = mixedMoment B raw19453step1 raw19453step1Labels := by
      have ha : raw19453step1 = (fun i j => raw19453step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19453step1 raw19453step0; decide +kernel
      have hl : raw19453step1Labels = raw19453step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19453step0 raw19453step0Labels permutation145 permutation2
    mixedMoment B raw19453step1 raw19453step1Labels = mixedMoment B raw19453step2 raw19453step2Labels := by
      have ha : raw19453step2 = -raw19453step1 := by apply Matrix.ext; change ∀ i j, raw19453step2 i j = -(raw19453step1 i j); unfold raw19453step2 raw19453step1; decide +kernel
      have hl : raw19453step2Labels = raw19453step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node794 node794Labels := by rfl

theorem canonical19454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19454 raw19454Labels = mixedMoment B node794 node794Labels := by
  calc
    mixedMoment B raw19454 raw19454Labels = mixedMoment B raw19454step0 raw19454step0Labels := by
      have hz : ∀ j, raw19454 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19454step0 = (fun i j => raw19454 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19454step0 raw19454; decide +kernel
      have hl : raw19454step0Labels = raw19454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19454 raw19454Labels permutation265 hz
    mixedMoment B raw19454step0 raw19454step0Labels = mixedMoment B raw19454step1 raw19454step1Labels := by
      have ha : raw19454step1 = (fun i j => raw19454step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19454step1 raw19454step0; decide +kernel
      have hl : raw19454step1Labels = raw19454step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19454step0 raw19454step0Labels permutation145 permutation2
    mixedMoment B raw19454step1 raw19454step1Labels = mixedMoment B raw19454step2 raw19454step2Labels := by
      have ha : raw19454step2 = -raw19454step1 := by apply Matrix.ext; change ∀ i j, raw19454step2 i j = -(raw19454step1 i j); unfold raw19454step2 raw19454step1; decide +kernel
      have hl : raw19454step2Labels = raw19454step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node794 node794Labels := by rfl

theorem canonical19455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19455 raw19455Labels = mixedMoment B node828 node828Labels := by
  calc
    mixedMoment B raw19455 raw19455Labels = mixedMoment B raw19455step0 raw19455step0Labels := by
      have hz : ∀ j, raw19455 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19455step0 = (fun i j => raw19455 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19455step0 raw19455; decide +kernel
      have hl : raw19455step0Labels = raw19455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19455 raw19455Labels permutation346 hz
    mixedMoment B raw19455step0 raw19455step0Labels = mixedMoment B raw19455step1 raw19455step1Labels := by
      have hz : ∀ j, raw19455step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19455step1 = (fun i j => raw19455step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19455step1 raw19455step0; decide +kernel
      have hl : raw19455step1Labels = raw19455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19455step0 raw19455step0Labels permutation56 hz
    mixedMoment B raw19455step1 raw19455step1Labels = mixedMoment B raw19455step2 raw19455step2Labels := by
      have ha : raw19455step2 = (fun i j => raw19455step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19455step2 raw19455step1; decide +kernel
      have hl : raw19455step2Labels = raw19455step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19455step1 raw19455step1Labels permutation31 permutation2
    mixedMoment B raw19455step2 raw19455step2Labels = mixedMoment B raw19455step3 raw19455step3Labels := by
      have ha : raw19455step3 = -raw19455step2 := by apply Matrix.ext; change ∀ i j, raw19455step3 i j = -(raw19455step2 i j); unfold raw19455step3 raw19455step2; decide +kernel
      have hl : raw19455step3Labels = raw19455step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node828 node828Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical152
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19456 raw19456Labels = mixedMoment B node813 node813Labels := by
  calc
    mixedMoment B raw19456 raw19456Labels = mixedMoment B raw19456step0 raw19456step0Labels := by
      have hz : ∀ j, raw19456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19456step0 = (fun i j => raw19456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19456step0 raw19456; decide +kernel
      have hl : raw19456step0Labels = raw19456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19456 raw19456Labels permutation346 hz
    mixedMoment B raw19456step0 raw19456step0Labels = mixedMoment B raw19456step1 raw19456step1Labels := by
      have hz : ∀ j, raw19456step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19456step1 = (fun i j => raw19456step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19456step1 raw19456step0; decide +kernel
      have hl : raw19456step1Labels = raw19456step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19456step0 raw19456step0Labels permutation56 hz
    mixedMoment B raw19456step1 raw19456step1Labels = mixedMoment B raw19456step2 raw19456step2Labels := by
      have ha : raw19456step2 = (fun i j => raw19456step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19456step2 raw19456step1; decide +kernel
      have hl : raw19456step2Labels = raw19456step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19456step1 raw19456step1Labels permutation29 permutation2
    mixedMoment B raw19456step2 raw19456step2Labels = mixedMoment B raw19456step3 raw19456step3Labels := by
      have ha : raw19456step3 = -raw19456step2 := by apply Matrix.ext; change ∀ i j, raw19456step3 i j = -(raw19456step2 i j); unfold raw19456step3 raw19456step2; decide +kernel
      have hl : raw19456step3Labels = raw19456step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node813 node813Labels := by rfl

theorem canonical19457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19457 raw19457Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw19457 raw19457Labels = mixedMoment B raw19457step0 raw19457step0Labels := by
      have hz : ∀ j, raw19457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19457step0 = (fun i j => raw19457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19457step0 raw19457; decide +kernel
      have hl : raw19457step0Labels = raw19457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19457 raw19457Labels permutation346 hz
    mixedMoment B raw19457step0 raw19457step0Labels = mixedMoment B raw19457step1 raw19457step1Labels := by
      have hz : ∀ j, raw19457step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19457step1 = (fun i j => raw19457step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19457step1 raw19457step0; decide +kernel
      have hl : raw19457step1Labels = raw19457step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19457step0 raw19457step0Labels permutation56 hz
    mixedMoment B raw19457step1 raw19457step1Labels = mixedMoment B raw19457step2 raw19457step2Labels := by
      have ha : raw19457step2 = (fun i j => raw19457step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19457step2 raw19457step1; decide +kernel
      have hl : raw19457step2Labels = raw19457step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19457step1 raw19457step1Labels permutation29 permutation2
    mixedMoment B raw19457step2 raw19457step2Labels = mixedMoment B raw19457step3 raw19457step3Labels := by
      have ha : raw19457step3 = -raw19457step2 := by apply Matrix.ext; change ∀ i j, raw19457step3 i j = -(raw19457step2 i j); unfold raw19457step3 raw19457step2; decide +kernel
      have hl : raw19457step3Labels = raw19457step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1716 node1716Labels := by rfl

theorem canonical19458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19458 raw19458Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw19458 raw19458Labels = mixedMoment B raw19458step0 raw19458step0Labels := by
      have hz : ∀ j, raw19458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19458step0 = (fun i j => raw19458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19458step0 raw19458; decide +kernel
      have hl : raw19458step0Labels = raw19458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19458 raw19458Labels permutation346 hz
    mixedMoment B raw19458step0 raw19458step0Labels = mixedMoment B raw19458step1 raw19458step1Labels := by
      have hz : ∀ j, raw19458step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19458step1 = (fun i j => raw19458step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19458step1 raw19458step0; decide +kernel
      have hl : raw19458step1Labels = raw19458step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19458step0 raw19458step0Labels permutation56 hz
    mixedMoment B raw19458step1 raw19458step1Labels = mixedMoment B raw19458step2 raw19458step2Labels := by
      have ha : raw19458step2 = (fun i j => raw19458step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19458step2 raw19458step1; decide +kernel
      have hl : raw19458step2Labels = raw19458step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19458step1 raw19458step1Labels permutation26 permutation0
    mixedMoment B raw19458step2 raw19458step2Labels = mixedMoment B raw19458step3 raw19458step3Labels := by
      have ha : raw19458step3 = -raw19458step2 := by apply Matrix.ext; change ∀ i j, raw19458step3 i j = -(raw19458step2 i j); unfold raw19458step3 raw19458step2; decide +kernel
      have hl : raw19458step3Labels = raw19458step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical19466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19466 raw19466Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw19466 raw19466Labels = mixedMoment B raw19466step0 raw19466step0Labels := by
      have hz : ∀ j, raw19466 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19466step0 = (fun i j => raw19466 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19466step0 raw19466; decide +kernel
      have hl : raw19466step0Labels = raw19466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19466 raw19466Labels permutation434 hz
    mixedMoment B raw19466step0 raw19466step0Labels = mixedMoment B raw19466step1 raw19466step1Labels := by
      have hz : ∀ j, raw19466step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19466step1 = (fun i j => raw19466step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19466step1 raw19466step0; decide +kernel
      have hl : raw19466step1Labels = raw19466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19466step0 raw19466step0Labels permutation80 hz
    mixedMoment B raw19466step1 raw19466step1Labels = mixedMoment B raw19466step2 raw19466step2Labels := by
      have ha : raw19466step2 = (fun i j => raw19466step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19466step2 raw19466step1; decide +kernel
      have hl : raw19466step2Labels = raw19466step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19466step1 raw19466step1Labels permutation31 permutation2
    mixedMoment B raw19466step2 raw19466step2Labels = mixedMoment B raw19466step3 raw19466step3Labels := by
      have ha : raw19466step3 = -raw19466step2 := by apply Matrix.ext; change ∀ i j, raw19466step3 i j = -(raw19466step2 i j); unfold raw19466step3 raw19466step2; decide +kernel
      have hl : raw19466step3Labels = raw19466step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1242 node1242Labels := by rfl

theorem canonical19467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19467 raw19467Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw19467 raw19467Labels = mixedMoment B raw19467step0 raw19467step0Labels := by
      have hz : ∀ j, raw19467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19467step0 = (fun i j => raw19467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19467step0 raw19467; decide +kernel
      have hl : raw19467step0Labels = raw19467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19467 raw19467Labels permutation434 hz
    mixedMoment B raw19467step0 raw19467step0Labels = mixedMoment B raw19467step1 raw19467step1Labels := by
      have hz : ∀ j, raw19467step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19467step1 = (fun i j => raw19467step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19467step1 raw19467step0; decide +kernel
      have hl : raw19467step1Labels = raw19467step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19467step0 raw19467step0Labels permutation80 hz
    _ = mixedMoment B node1221 node1221Labels := by rfl

theorem canonical19468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19468 raw19468Labels = mixedMoment B node1115 node1115Labels := by
  calc
    mixedMoment B raw19468 raw19468Labels = mixedMoment B raw19468step0 raw19468step0Labels := by
      have hz : ∀ j, raw19468 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19468step0 = (fun i j => raw19468 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19468step0 raw19468; decide +kernel
      have hl : raw19468step0Labels = raw19468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19468 raw19468Labels permutation434 hz
    mixedMoment B raw19468step0 raw19468step0Labels = mixedMoment B raw19468step1 raw19468step1Labels := by
      have ha : raw19468step1 = (fun i j => raw19468step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19468step1 raw19468step0; decide +kernel
      have hl : raw19468step1Labels = raw19468step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19468step0 raw19468step0Labels permutation34 permutation2
    _ = mixedMoment B node1115 node1115Labels := by rfl

theorem canonical19469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19469 raw19469Labels = mixedMoment B node1115 node1115Labels := by
  calc
    mixedMoment B raw19469 raw19469Labels = mixedMoment B raw19469step0 raw19469step0Labels := by
      have hz : ∀ j, raw19469 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19469step0 = (fun i j => raw19469 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19469step0 raw19469; decide +kernel
      have hl : raw19469step0Labels = raw19469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19469 raw19469Labels permutation346 hz
    mixedMoment B raw19469step0 raw19469step0Labels = mixedMoment B raw19469step1 raw19469step1Labels := by
      have ha : raw19469step1 = (fun i j => raw19469step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19469step1 raw19469step0; decide +kernel
      have hl : raw19469step1Labels = raw19469step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19469step0 raw19469step0Labels permutation34 permutation2
    _ = mixedMoment B node1115 node1115Labels := by rfl

theorem canonical19470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19470 raw19470Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw19470 raw19470Labels = mixedMoment B raw19470step0 raw19470step0Labels := by
      have hz : ∀ j, raw19470 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19470step0 = (fun i j => raw19470 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19470step0 raw19470; decide +kernel
      have hl : raw19470step0Labels = raw19470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19470 raw19470Labels permutation434 hz
    mixedMoment B raw19470step0 raw19470step0Labels = mixedMoment B raw19470step1 raw19470step1Labels := by
      have hz : ∀ j, raw19470step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19470step1 = (fun i j => raw19470step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19470step1 raw19470step0; decide +kernel
      have hl : raw19470step1Labels = raw19470step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19470step0 raw19470step0Labels permutation80 hz
    _ = mixedMoment B node1140 node1140Labels := by rfl

theorem canonical19471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19471 raw19471Labels = mixedMoment B node633 node633Labels := by
  calc
    mixedMoment B raw19471 raw19471Labels = mixedMoment B raw19471step0 raw19471step0Labels := by
      have hz : ∀ j, raw19471 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19471step0 = (fun i j => raw19471 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19471step0 raw19471; decide +kernel
      have hl : raw19471step0Labels = raw19471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19471 raw19471Labels permutation434 hz
    mixedMoment B raw19471step0 raw19471step0Labels = mixedMoment B raw19471step1 raw19471step1Labels := by
      have hz : ∀ j, raw19471step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19471step1 = (fun i j => raw19471step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19471step1 raw19471step0; decide +kernel
      have hl : raw19471step1Labels = raw19471step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19471step0 raw19471step0Labels permutation80 hz
    mixedMoment B raw19471step1 raw19471step1Labels = mixedMoment B raw19471step2 raw19471step2Labels := by
      have ha : raw19471step2 = (fun i j => raw19471step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19471step2 raw19471step1; decide +kernel
      have hl : raw19471step2Labels = raw19471step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19471step1 raw19471step1Labels permutation31 permutation2
    mixedMoment B raw19471step2 raw19471step2Labels = mixedMoment B raw19471step3 raw19471step3Labels := by
      have ha : raw19471step3 = -raw19471step2 := by apply Matrix.ext; change ∀ i j, raw19471step3 i j = -(raw19471step2 i j); unfold raw19471step3 raw19471step2; decide +kernel
      have hl : raw19471step3Labels = raw19471step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node633 node633Labels := by rfl

theorem canonical19472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19472 raw19472Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw19472 raw19472Labels = mixedMoment B raw19472step0 raw19472step0Labels := by
      have hz : ∀ j, raw19472 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19472step0 = (fun i j => raw19472 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19472step0 raw19472; decide +kernel
      have hl : raw19472step0Labels = raw19472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19472 raw19472Labels permutation434 hz
    mixedMoment B raw19472step0 raw19472step0Labels = mixedMoment B raw19472step1 raw19472step1Labels := by
      have hz : ∀ j, raw19472step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19472step1 = (fun i j => raw19472step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19472step1 raw19472step0; decide +kernel
      have hl : raw19472step1Labels = raw19472step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19472step0 raw19472step0Labels permutation80 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical19473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19473 raw19473Labels = mixedMoment B node3298 node3298Labels := by
  calc
    mixedMoment B raw19473 raw19473Labels = mixedMoment B raw19473step0 raw19473step0Labels := by
      have hz : ∀ j, raw19473 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19473step0 = (fun i j => raw19473 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19473step0 raw19473; decide +kernel
      have hl : raw19473step0Labels = raw19473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19473 raw19473Labels permutation434 hz
    mixedMoment B raw19473step0 raw19473step0Labels = mixedMoment B raw19473step1 raw19473step1Labels := by
      have hz : ∀ j, raw19473step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19473step1 = (fun i j => raw19473step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19473step1 raw19473step0; decide +kernel
      have hl : raw19473step1Labels = raw19473step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19473step0 raw19473step0Labels permutation80 hz
    mixedMoment B raw19473step1 raw19473step1Labels = mixedMoment B raw19473step2 raw19473step2Labels := by
      have ha : raw19473step2 = (fun i j => raw19473step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19473step2 raw19473step1; decide +kernel
      have hl : raw19473step2Labels = raw19473step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19473step1 raw19473step1Labels permutation29 permutation2
    _ = mixedMoment B node3298 node3298Labels := by rfl

theorem canonical19474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19474 raw19474Labels = mixedMoment B node1629 node1629Labels := by
  calc
    mixedMoment B raw19474 raw19474Labels = mixedMoment B raw19474step0 raw19474step0Labels := by
      have hz : ∀ j, raw19474 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19474step0 = (fun i j => raw19474 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19474step0 raw19474; decide +kernel
      have hl : raw19474step0Labels = raw19474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19474 raw19474Labels permutation434 hz
    mixedMoment B raw19474step0 raw19474step0Labels = mixedMoment B raw19474step1 raw19474step1Labels := by
      have hz : ∀ j, raw19474step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19474step1 = (fun i j => raw19474step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19474step1 raw19474step0; decide +kernel
      have hl : raw19474step1Labels = raw19474step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19474step0 raw19474step0Labels permutation80 hz
    mixedMoment B raw19474step1 raw19474step1Labels = mixedMoment B raw19474step2 raw19474step2Labels := by
      have ha : raw19474step2 = (fun i j => raw19474step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19474step2 raw19474step1; decide +kernel
      have hl : raw19474step2Labels = raw19474step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19474step1 raw19474step1Labels permutation10 permutation2
    mixedMoment B raw19474step2 raw19474step2Labels = mixedMoment B raw19474step3 raw19474step3Labels := by
      have ha : raw19474step3 = -raw19474step2 := by apply Matrix.ext; change ∀ i j, raw19474step3 i j = -(raw19474step2 i j); unfold raw19474step3 raw19474step2; decide +kernel
      have hl : raw19474step3Labels = raw19474step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1629 node1629Labels := by rfl

theorem canonical19475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19475 raw19475Labels = mixedMoment B node1615 node1615Labels := by
  calc
    mixedMoment B raw19475 raw19475Labels = mixedMoment B raw19475step0 raw19475step0Labels := by
      have hz : ∀ j, raw19475 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19475step0 = (fun i j => raw19475 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19475step0 raw19475; decide +kernel
      have hl : raw19475step0Labels = raw19475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19475 raw19475Labels permutation434 hz
    mixedMoment B raw19475step0 raw19475step0Labels = mixedMoment B raw19475step1 raw19475step1Labels := by
      have ha : raw19475step1 = (fun i j => raw19475step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19475step1 raw19475step0; decide +kernel
      have hl : raw19475step1Labels = raw19475step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19475step0 raw19475step0Labels permutation44 permutation2
    mixedMoment B raw19475step1 raw19475step1Labels = mixedMoment B raw19475step2 raw19475step2Labels := by
      have ha : raw19475step2 = -raw19475step1 := by apply Matrix.ext; change ∀ i j, raw19475step2 i j = -(raw19475step1 i j); unfold raw19475step2 raw19475step1; decide +kernel
      have hl : raw19475step2Labels = raw19475step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1615 node1615Labels := by rfl

theorem canonical19476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19476 raw19476Labels = mixedMoment B node1615 node1615Labels := by
  calc
    mixedMoment B raw19476 raw19476Labels = mixedMoment B raw19476step0 raw19476step0Labels := by
      have hz : ∀ j, raw19476 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19476step0 = (fun i j => raw19476 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19476step0 raw19476; decide +kernel
      have hl : raw19476step0Labels = raw19476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19476 raw19476Labels permutation346 hz
    mixedMoment B raw19476step0 raw19476step0Labels = mixedMoment B raw19476step1 raw19476step1Labels := by
      have ha : raw19476step1 = (fun i j => raw19476step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19476step1 raw19476step0; decide +kernel
      have hl : raw19476step1Labels = raw19476step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19476step0 raw19476step0Labels permutation44 permutation2
    mixedMoment B raw19476step1 raw19476step1Labels = mixedMoment B raw19476step2 raw19476step2Labels := by
      have ha : raw19476step2 = -raw19476step1 := by apply Matrix.ext; change ∀ i j, raw19476step2 i j = -(raw19476step1 i j); unfold raw19476step2 raw19476step1; decide +kernel
      have hl : raw19476step2Labels = raw19476step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1615 node1615Labels := by rfl

theorem canonical19477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19477 raw19477Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw19477 raw19477Labels = mixedMoment B raw19477step0 raw19477step0Labels := by
      have hz : ∀ j, raw19477 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19477step0 = (fun i j => raw19477 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19477step0 raw19477; decide +kernel
      have hl : raw19477step0Labels = raw19477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19477 raw19477Labels permutation520 hz
    mixedMoment B raw19477step0 raw19477step0Labels = mixedMoment B raw19477step1 raw19477step1Labels := by
      have hz : ∀ j, raw19477step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19477step1 = (fun i j => raw19477step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19477step1 raw19477step0; decide +kernel
      have hl : raw19477step1Labels = raw19477step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19477step0 raw19477step0Labels permutation104 hz
    mixedMoment B raw19477step1 raw19477step1Labels = mixedMoment B raw19477step2 raw19477step2Labels := by
      have hz : ∀ j, raw19477step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19477step2 = (fun i j => raw19477step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19477step2 raw19477step1; decide +kernel
      have hl : raw19477step2Labels = raw19477step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19477step1 raw19477step1Labels permutation20 hz
    mixedMoment B raw19477step2 raw19477step2Labels = mixedMoment B raw19477step3 raw19477step3Labels := by
      have ha : raw19477step3 = -raw19477step2 := by apply Matrix.ext; change ∀ i j, raw19477step3 i j = -(raw19477step2 i j); unfold raw19477step3 raw19477step2; decide +kernel
      have hl : raw19477step3Labels = raw19477step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1752 node1752Labels := by rfl

theorem canonical19478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19478 raw19478Labels = mixedMoment B node1620 node1620Labels := by
  calc
    mixedMoment B raw19478 raw19478Labels = mixedMoment B raw19478step0 raw19478step0Labels := by
      have hz : ∀ j, raw19478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19478step0 = (fun i j => raw19478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19478step0 raw19478; decide +kernel
      have hl : raw19478step0Labels = raw19478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19478 raw19478Labels permutation434 hz
    mixedMoment B raw19478step0 raw19478step0Labels = mixedMoment B raw19478step1 raw19478step1Labels := by
      have hz : ∀ j, raw19478step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19478step1 = (fun i j => raw19478step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19478step1 raw19478step0; decide +kernel
      have hl : raw19478step1Labels = raw19478step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19478step0 raw19478step0Labels permutation80 hz
    mixedMoment B raw19478step1 raw19478step1Labels = mixedMoment B raw19478step2 raw19478step2Labels := by
      have ha : raw19478step2 = (fun i j => raw19478step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19478step2 raw19478step1; decide +kernel
      have hl : raw19478step2Labels = raw19478step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19478step1 raw19478step1Labels permutation29 permutation2
    _ = mixedMoment B node1620 node1620Labels := by rfl

theorem canonical19479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19479 raw19479Labels = mixedMoment B node3298 node3298Labels := by
  calc
    mixedMoment B raw19479 raw19479Labels = mixedMoment B raw19479step0 raw19479step0Labels := by
      have hz : ∀ j, raw19479 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19479step0 = (fun i j => raw19479 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19479step0 raw19479; decide +kernel
      have hl : raw19479step0Labels = raw19479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19479 raw19479Labels permutation434 hz
    mixedMoment B raw19479step0 raw19479step0Labels = mixedMoment B raw19479step1 raw19479step1Labels := by
      have hz : ∀ j, raw19479step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19479step1 = (fun i j => raw19479step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19479step1 raw19479step0; decide +kernel
      have hl : raw19479step1Labels = raw19479step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19479step0 raw19479step0Labels permutation56 hz
    mixedMoment B raw19479step1 raw19479step1Labels = mixedMoment B raw19479step2 raw19479step2Labels := by
      have ha : raw19479step2 = (fun i j => raw19479step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19479step2 raw19479step1; decide +kernel
      have hl : raw19479step2Labels = raw19479step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19479step1 raw19479step1Labels permutation29 permutation2
    _ = mixedMoment B node3298 node3298Labels := by rfl

theorem canonical19480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19480 raw19480Labels = mixedMoment B node3298 node3298Labels := by
  calc
    mixedMoment B raw19480 raw19480Labels = mixedMoment B raw19480step0 raw19480step0Labels := by
      have hz : ∀ j, raw19480 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19480step0 = (fun i j => raw19480 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19480step0 raw19480; decide +kernel
      have hl : raw19480step0Labels = raw19480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19480 raw19480Labels permutation346 hz
    mixedMoment B raw19480step0 raw19480step0Labels = mixedMoment B raw19480step1 raw19480step1Labels := by
      have hz : ∀ j, raw19480step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19480step1 = (fun i j => raw19480step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19480step1 raw19480step0; decide +kernel
      have hl : raw19480step1Labels = raw19480step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19480step0 raw19480step0Labels permutation56 hz
    mixedMoment B raw19480step1 raw19480step1Labels = mixedMoment B raw19480step2 raw19480step2Labels := by
      have ha : raw19480step2 = (fun i j => raw19480step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19480step2 raw19480step1; decide +kernel
      have hl : raw19480step2Labels = raw19480step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19480step1 raw19480step1Labels permutation29 permutation2
    _ = mixedMoment B node3298 node3298Labels := by rfl

theorem canonical19481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19481 raw19481Labels = mixedMoment B node3313 node3313Labels := by
  calc
    mixedMoment B raw19481 raw19481Labels = mixedMoment B raw19481step0 raw19481step0Labels := by
      have hz : ∀ j, raw19481 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19481step0 = (fun i j => raw19481 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19481step0 raw19481; decide +kernel
      have hl : raw19481step0Labels = raw19481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19481 raw19481Labels permutation520 hz
    mixedMoment B raw19481step0 raw19481step0Labels = mixedMoment B raw19481step1 raw19481step1Labels := by
      have hz : ∀ j, raw19481step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19481step1 = (fun i j => raw19481step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19481step1 raw19481step0; decide +kernel
      have hl : raw19481step1Labels = raw19481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19481step0 raw19481step0Labels permutation104 hz
    mixedMoment B raw19481step1 raw19481step1Labels = mixedMoment B raw19481step2 raw19481step2Labels := by
      have hz : ∀ j, raw19481step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19481step2 = (fun i j => raw19481step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19481step2 raw19481step1; decide +kernel
      have hl : raw19481step2Labels = raw19481step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19481step1 raw19481step1Labels permutation20 hz
    mixedMoment B raw19481step2 raw19481step2Labels = mixedMoment B raw19481step3 raw19481step3Labels := by
      have hz : ∀ j, raw19481step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19481step3 = (fun i j => raw19481step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19481step3 raw19481step2; decide +kernel
      have hl : raw19481step3Labels = raw19481step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19481step2 raw19481step2Labels permutation4 hz
    mixedMoment B raw19481step3 raw19481step3Labels = mixedMoment B raw19481step4 raw19481step4Labels := by
      have ha : raw19481step4 = (fun i j => raw19481step3 (permutation1 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19481step4 raw19481step3; decide +kernel
      have hl : raw19481step4Labels = raw19481step3Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19481step3 raw19481step3Labels permutation1 permutation2
    _ = mixedMoment B node3313 node3313Labels := by rfl

theorem canonical19482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19482 raw19482Labels = mixedMoment B node994 node994Labels := by
  calc
    mixedMoment B raw19482 raw19482Labels = mixedMoment B raw19482step0 raw19482step0Labels := by
      have hz : ∀ j, raw19482 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19482step0 = (fun i j => raw19482 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19482step0 raw19482; decide +kernel
      have hl : raw19482step0Labels = raw19482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19482 raw19482Labels permutation434 hz
    mixedMoment B raw19482step0 raw19482step0Labels = mixedMoment B raw19482step1 raw19482step1Labels := by
      have hz : ∀ j, raw19482step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19482step1 = (fun i j => raw19482step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19482step1 raw19482step0; decide +kernel
      have hl : raw19482step1Labels = raw19482step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19482step0 raw19482step0Labels permutation80 hz
    mixedMoment B raw19482step1 raw19482step1Labels = mixedMoment B raw19482step2 raw19482step2Labels := by
      have ha : raw19482step2 = (fun i j => raw19482step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19482step2 raw19482step1; decide +kernel
      have hl : raw19482step2Labels = raw19482step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19482step1 raw19482step1Labels permutation29 permutation2
    mixedMoment B raw19482step2 raw19482step2Labels = mixedMoment B raw19482step3 raw19482step3Labels := by
      have ha : raw19482step3 = -raw19482step2 := by apply Matrix.ext; change ∀ i j, raw19482step3 i j = -(raw19482step2 i j); unfold raw19482step3 raw19482step2; decide +kernel
      have hl : raw19482step3Labels = raw19482step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node994 node994Labels := by rfl

theorem canonical19483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19483 raw19483Labels = mixedMoment B node1055 node1055Labels := by
  calc
    mixedMoment B raw19483 raw19483Labels = mixedMoment B raw19483step0 raw19483step0Labels := by
      have hz : ∀ j, raw19483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19483step0 = (fun i j => raw19483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19483step0 raw19483; decide +kernel
      have hl : raw19483step0Labels = raw19483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19483 raw19483Labels permutation434 hz
    mixedMoment B raw19483step0 raw19483step0Labels = mixedMoment B raw19483step1 raw19483step1Labels := by
      have hz : ∀ j, raw19483step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19483step1 = (fun i j => raw19483step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19483step1 raw19483step0; decide +kernel
      have hl : raw19483step1Labels = raw19483step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19483step0 raw19483step0Labels permutation80 hz
    mixedMoment B raw19483step1 raw19483step1Labels = mixedMoment B raw19483step2 raw19483step2Labels := by
      have ha : raw19483step2 = (fun i j => raw19483step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19483step2 raw19483step1; decide +kernel
      have hl : raw19483step2Labels = raw19483step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19483step1 raw19483step1Labels permutation31 permutation2
    mixedMoment B raw19483step2 raw19483step2Labels = mixedMoment B raw19483step3 raw19483step3Labels := by
      have ha : raw19483step3 = -raw19483step2 := by apply Matrix.ext; change ∀ i j, raw19483step3 i j = -(raw19483step2 i j); unfold raw19483step3 raw19483step2; decide +kernel
      have hl : raw19483step3Labels = raw19483step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1055 node1055Labels := by rfl

theorem canonical19484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19484 raw19484Labels = mixedMoment B node989 node989Labels := by
  calc
    mixedMoment B raw19484 raw19484Labels = mixedMoment B raw19484step0 raw19484step0Labels := by
      have hz : ∀ j, raw19484 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19484step0 = (fun i j => raw19484 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19484step0 raw19484; decide +kernel
      have hl : raw19484step0Labels = raw19484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19484 raw19484Labels permutation434 hz
    mixedMoment B raw19484step0 raw19484step0Labels = mixedMoment B raw19484step1 raw19484step1Labels := by
      have ha : raw19484step1 = (fun i j => raw19484step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19484step1 raw19484step0; decide +kernel
      have hl : raw19484step1Labels = raw19484step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19484step0 raw19484step0Labels permutation139 permutation2
    mixedMoment B raw19484step1 raw19484step1Labels = mixedMoment B raw19484step2 raw19484step2Labels := by
      have ha : raw19484step2 = -raw19484step1 := by apply Matrix.ext; change ∀ i j, raw19484step2 i j = -(raw19484step1 i j); unfold raw19484step2 raw19484step1; decide +kernel
      have hl : raw19484step2Labels = raw19484step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node989 node989Labels := by rfl

theorem canonical19485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19485 raw19485Labels = mixedMoment B node989 node989Labels := by
  calc
    mixedMoment B raw19485 raw19485Labels = mixedMoment B raw19485step0 raw19485step0Labels := by
      have hz : ∀ j, raw19485 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19485step0 = (fun i j => raw19485 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19485step0 raw19485; decide +kernel
      have hl : raw19485step0Labels = raw19485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19485 raw19485Labels permutation346 hz
    mixedMoment B raw19485step0 raw19485step0Labels = mixedMoment B raw19485step1 raw19485step1Labels := by
      have ha : raw19485step1 = (fun i j => raw19485step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19485step1 raw19485step0; decide +kernel
      have hl : raw19485step1Labels = raw19485step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19485step0 raw19485step0Labels permutation139 permutation2
    mixedMoment B raw19485step1 raw19485step1Labels = mixedMoment B raw19485step2 raw19485step2Labels := by
      have ha : raw19485step2 = -raw19485step1 := by apply Matrix.ext; change ∀ i j, raw19485step2 i j = -(raw19485step1 i j); unfold raw19485step2 raw19485step1; decide +kernel
      have hl : raw19485step2Labels = raw19485step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node989 node989Labels := by rfl

theorem canonical19486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19486 raw19486Labels = mixedMoment B node1009 node1009Labels := by
  calc
    mixedMoment B raw19486 raw19486Labels = mixedMoment B raw19486step0 raw19486step0Labels := by
      have hz : ∀ j, raw19486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19486step0 = (fun i j => raw19486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19486step0 raw19486; decide +kernel
      have hl : raw19486step0Labels = raw19486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19486 raw19486Labels permutation434 hz
    mixedMoment B raw19486step0 raw19486step0Labels = mixedMoment B raw19486step1 raw19486step1Labels := by
      have hz : ∀ j, raw19486step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19486step1 = (fun i j => raw19486step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19486step1 raw19486step0; decide +kernel
      have hl : raw19486step1Labels = raw19486step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19486step0 raw19486step0Labels permutation80 hz
    mixedMoment B raw19486step1 raw19486step1Labels = mixedMoment B raw19486step2 raw19486step2Labels := by
      have ha : raw19486step2 = (fun i j => raw19486step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19486step2 raw19486step1; decide +kernel
      have hl : raw19486step2Labels = raw19486step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19486step1 raw19486step1Labels permutation29 permutation2
    mixedMoment B raw19486step2 raw19486step2Labels = mixedMoment B raw19486step3 raw19486step3Labels := by
      have ha : raw19486step3 = -raw19486step2 := by apply Matrix.ext; change ∀ i j, raw19486step3 i j = -(raw19486step2 i j); unfold raw19486step3 raw19486step2; decide +kernel
      have hl : raw19486step3Labels = raw19486step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1009 node1009Labels := by rfl

theorem canonical19487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19487 raw19487Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw19487 raw19487Labels = mixedMoment B raw19487step0 raw19487step0Labels := by
      have hz : ∀ j, raw19487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19487step0 = (fun i j => raw19487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19487step0 raw19487; decide +kernel
      have hl : raw19487step0Labels = raw19487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19487 raw19487Labels permutation434 hz
    mixedMoment B raw19487step0 raw19487step0Labels = mixedMoment B raw19487step1 raw19487step1Labels := by
      have hz : ∀ j, raw19487step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19487step1 = (fun i j => raw19487step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19487step1 raw19487step0; decide +kernel
      have hl : raw19487step1Labels = raw19487step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19487step0 raw19487step0Labels permutation80 hz
    mixedMoment B raw19487step1 raw19487step1Labels = mixedMoment B raw19487step2 raw19487step2Labels := by
      have ha : raw19487step2 = (fun i j => raw19487step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19487step2 raw19487step1; decide +kernel
      have hl : raw19487step2Labels = raw19487step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19487step1 raw19487step1Labels permutation29 permutation2
    mixedMoment B raw19487step2 raw19487step2Labels = mixedMoment B raw19487step3 raw19487step3Labels := by
      have ha : raw19487step3 = -raw19487step2 := by apply Matrix.ext; change ∀ i j, raw19487step3 i j = -(raw19487step2 i j); unfold raw19487step3 raw19487step2; decide +kernel
      have hl : raw19487step3Labels = raw19487step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2218 node2218Labels := by rfl

theorem canonical19488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19488 raw19488Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw19488 raw19488Labels = mixedMoment B raw19488step0 raw19488step0Labels := by
      have hz : ∀ j, raw19488 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19488step0 = (fun i j => raw19488 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19488step0 raw19488; decide +kernel
      have hl : raw19488step0Labels = raw19488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19488 raw19488Labels permutation434 hz
    mixedMoment B raw19488step0 raw19488step0Labels = mixedMoment B raw19488step1 raw19488step1Labels := by
      have hz : ∀ j, raw19488step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19488step1 = (fun i j => raw19488step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19488step1 raw19488step0; decide +kernel
      have hl : raw19488step1Labels = raw19488step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19488step0 raw19488step0Labels permutation80 hz
    mixedMoment B raw19488step1 raw19488step1Labels = mixedMoment B raw19488step2 raw19488step2Labels := by
      have ha : raw19488step2 = (fun i j => raw19488step1 (permutation28 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19488step2 raw19488step1; decide +kernel
      have hl : raw19488step2Labels = raw19488step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19488step1 raw19488step1Labels permutation28 permutation0
    mixedMoment B raw19488step2 raw19488step2Labels = mixedMoment B raw19488step3 raw19488step3Labels := by
      have ha : raw19488step3 = -raw19488step2 := by apply Matrix.ext; change ∀ i j, raw19488step3 i j = -(raw19488step2 i j); unfold raw19488step3 raw19488step2; decide +kernel
      have hl : raw19488step3Labels = raw19488step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical19489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19489 raw19489Labels = mixedMoment B node1190 node1190Labels := by
  calc
    mixedMoment B raw19489 raw19489Labels = mixedMoment B raw19489step0 raw19489step0Labels := by
      have hz : ∀ j, raw19489 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19489step0 = (fun i j => raw19489 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19489step0 raw19489; decide +kernel
      have hl : raw19489step0Labels = raw19489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19489 raw19489Labels permutation434 hz
    mixedMoment B raw19489step0 raw19489step0Labels = mixedMoment B raw19489step1 raw19489step1Labels := by
      have hz : ∀ j, raw19489step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19489step1 = (fun i j => raw19489step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19489step1 raw19489step0; decide +kernel
      have hl : raw19489step1Labels = raw19489step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19489step0 raw19489step0Labels permutation80 hz
    mixedMoment B raw19489step1 raw19489step1Labels = mixedMoment B raw19489step2 raw19489step2Labels := by
      have ha : raw19489step2 = (fun i j => raw19489step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19489step2 raw19489step1; decide +kernel
      have hl : raw19489step2Labels = raw19489step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19489step1 raw19489step1Labels permutation10 permutation2
    _ = mixedMoment B node1190 node1190Labels := by rfl

theorem canonical19490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19490 raw19490Labels = mixedMoment B node1179 node1179Labels := by
  calc
    mixedMoment B raw19490 raw19490Labels = mixedMoment B raw19490step0 raw19490step0Labels := by
      have hz : ∀ j, raw19490 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19490step0 = (fun i j => raw19490 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19490step0 raw19490; decide +kernel
      have hl : raw19490step0Labels = raw19490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19490 raw19490Labels permutation434 hz
    mixedMoment B raw19490step0 raw19490step0Labels = mixedMoment B raw19490step1 raw19490step1Labels := by
      have ha : raw19490step1 = (fun i j => raw19490step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19490step1 raw19490step0; decide +kernel
      have hl : raw19490step1Labels = raw19490step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19490step0 raw19490step0Labels permutation44 permutation2
    _ = mixedMoment B node1179 node1179Labels := by rfl

theorem canonical19491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19491 raw19491Labels = mixedMoment B node1179 node1179Labels := by
  calc
    mixedMoment B raw19491 raw19491Labels = mixedMoment B raw19491step0 raw19491step0Labels := by
      have hz : ∀ j, raw19491 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19491step0 = (fun i j => raw19491 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19491step0 raw19491; decide +kernel
      have hl : raw19491step0Labels = raw19491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19491 raw19491Labels permutation346 hz
    mixedMoment B raw19491step0 raw19491step0Labels = mixedMoment B raw19491step1 raw19491step1Labels := by
      have ha : raw19491step1 = (fun i j => raw19491step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19491step1 raw19491step0; decide +kernel
      have hl : raw19491step1Labels = raw19491step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19491step0 raw19491step0Labels permutation44 permutation2
    _ = mixedMoment B node1179 node1179Labels := by rfl

theorem canonical19492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19492 raw19492Labels = mixedMoment B node1258 node1258Labels := by
  calc
    mixedMoment B raw19492 raw19492Labels = mixedMoment B raw19492step0 raw19492step0Labels := by
      have hz : ∀ j, raw19492 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19492step0 = (fun i j => raw19492 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19492step0 raw19492; decide +kernel
      have hl : raw19492step0Labels = raw19492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19492 raw19492Labels permutation434 hz
    mixedMoment B raw19492step0 raw19492step0Labels = mixedMoment B raw19492step1 raw19492step1Labels := by
      have hz : ∀ j, raw19492step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19492step1 = (fun i j => raw19492step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19492step1 raw19492step0; decide +kernel
      have hl : raw19492step1Labels = raw19492step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19492step0 raw19492step0Labels permutation80 hz
    _ = mixedMoment B node1258 node1258Labels := by rfl

theorem canonical19493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19493 raw19493Labels = mixedMoment B node975 node975Labels := by
  calc
    mixedMoment B raw19493 raw19493Labels = mixedMoment B raw19493step0 raw19493step0Labels := by
      have hz : ∀ j, raw19493 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19493step0 = (fun i j => raw19493 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19493step0 raw19493; decide +kernel
      have hl : raw19493step0Labels = raw19493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19493 raw19493Labels permutation346 hz
    mixedMoment B raw19493step0 raw19493step0Labels = mixedMoment B raw19493step1 raw19493step1Labels := by
      have ha : raw19493step1 = (fun i j => raw19493step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19493step1 raw19493step0; decide +kernel
      have hl : raw19493step1Labels = raw19493step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19493step0 raw19493step0Labels permutation137 permutation2
    mixedMoment B raw19493step1 raw19493step1Labels = mixedMoment B raw19493step2 raw19493step2Labels := by
      have ha : raw19493step2 = -raw19493step1 := by apply Matrix.ext; change ∀ i j, raw19493step2 i j = -(raw19493step1 i j); unfold raw19493step2 raw19493step1; decide +kernel
      have hl : raw19493step2Labels = raw19493step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node975 node975Labels := by rfl

theorem canonical19494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19494 raw19494Labels = mixedMoment B node1019 node1019Labels := by
  calc
    mixedMoment B raw19494 raw19494Labels = mixedMoment B raw19494step0 raw19494step0Labels := by
      have hz : ∀ j, raw19494 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19494step0 = (fun i j => raw19494 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19494step0 raw19494; decide +kernel
      have hl : raw19494step0Labels = raw19494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19494 raw19494Labels permutation346 hz
    mixedMoment B raw19494step0 raw19494step0Labels = mixedMoment B raw19494step1 raw19494step1Labels := by
      have ha : raw19494step1 = (fun i j => raw19494step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19494step1 raw19494step0; decide +kernel
      have hl : raw19494step1Labels = raw19494step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19494step0 raw19494step0Labels permutation145 permutation2
    mixedMoment B raw19494step1 raw19494step1Labels = mixedMoment B raw19494step2 raw19494step2Labels := by
      have ha : raw19494step2 = -raw19494step1 := by apply Matrix.ext; change ∀ i j, raw19494step2 i j = -(raw19494step1 i j); unfold raw19494step2 raw19494step1; decide +kernel
      have hl : raw19494step2Labels = raw19494step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1019 node1019Labels := by rfl

theorem canonical19495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19495 raw19495Labels = mixedMoment B node971 node971Labels := by
  calc
    mixedMoment B raw19495 raw19495Labels = mixedMoment B raw19495step0 raw19495step0Labels := by
      have ha : raw19495step0 = (fun i j => raw19495 (permutation616 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19495step0 raw19495; decide +kernel
      have hl : raw19495step0Labels = raw19495Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19495 raw19495Labels permutation616 permutation2
    mixedMoment B raw19495step0 raw19495step0Labels = mixedMoment B raw19495step1 raw19495step1Labels := by
      have ha : raw19495step1 = -raw19495step0 := by apply Matrix.ext; change ∀ i j, raw19495step1 i j = -(raw19495step0 i j); unfold raw19495step1 raw19495step0; decide +kernel
      have hl : raw19495step1Labels = raw19495step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node971 node971Labels := by rfl

theorem canonical19496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19496 raw19496Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw19496 raw19496Labels = mixedMoment B raw19496step0 raw19496step0Labels := by
      have hz : ∀ j, raw19496 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19496step0 = (fun i j => raw19496 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19496step0 raw19496; decide +kernel
      have hl : raw19496step0Labels = raw19496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19496 raw19496Labels permutation346 hz
    mixedMoment B raw19496step0 raw19496step0Labels = mixedMoment B raw19496step1 raw19496step1Labels := by
      have ha : raw19496step1 = (fun i j => raw19496step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19496step1 raw19496step0; decide +kernel
      have hl : raw19496step1Labels = raw19496step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19496step0 raw19496step0Labels permutation139 permutation2
    mixedMoment B raw19496step1 raw19496step1Labels = mixedMoment B raw19496step2 raw19496step2Labels := by
      have ha : raw19496step2 = -raw19496step1 := by apply Matrix.ext; change ∀ i j, raw19496step2 i j = -(raw19496step1 i j); unfold raw19496step2 raw19496step1; decide +kernel
      have hl : raw19496step2Labels = raw19496step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node982 node982Labels := by rfl

theorem canonical19497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19497 raw19497Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw19497 raw19497Labels = mixedMoment B raw19497step0 raw19497step0Labels := by
      have hz : ∀ j, raw19497 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19497step0 = (fun i j => raw19497 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19497step0 raw19497; decide +kernel
      have hl : raw19497step0Labels = raw19497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19497 raw19497Labels permutation346 hz
    mixedMoment B raw19497step0 raw19497step0Labels = mixedMoment B raw19497step1 raw19497step1Labels := by
      have ha : raw19497step1 = (fun i j => raw19497step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19497step1 raw19497step0; decide +kernel
      have hl : raw19497step1Labels = raw19497step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19497step0 raw19497step0Labels permutation137 permutation2
    mixedMoment B raw19497step1 raw19497step1Labels = mixedMoment B raw19497step2 raw19497step2Labels := by
      have ha : raw19497step2 = -raw19497step1 := by apply Matrix.ext; change ∀ i j, raw19497step2 i j = -(raw19497step1 i j); unfold raw19497step2 raw19497step1; decide +kernel
      have hl : raw19497step2Labels = raw19497step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node982 node982Labels := by rfl

theorem canonical19498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19498 raw19498Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw19498 raw19498Labels = mixedMoment B raw19498step0 raw19498step0Labels := by
      have hz : ∀ j, raw19498 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19498step0 = (fun i j => raw19498 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19498step0 raw19498; decide +kernel
      have hl : raw19498step0Labels = raw19498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19498 raw19498Labels permutation346 hz
    mixedMoment B raw19498step0 raw19498step0Labels = mixedMoment B raw19498step1 raw19498step1Labels := by
      have ha : raw19498step1 = (fun i j => raw19498step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19498step1 raw19498step0; decide +kernel
      have hl : raw19498step1Labels = raw19498step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19498step0 raw19498step0Labels permutation137 permutation2
    mixedMoment B raw19498step1 raw19498step1Labels = mixedMoment B raw19498step2 raw19498step2Labels := by
      have ha : raw19498step2 = -raw19498step1 := by apply Matrix.ext; change ∀ i j, raw19498step2 i j = -(raw19498step1 i j); unfold raw19498step2 raw19498step1; decide +kernel
      have hl : raw19498step2Labels = raw19498step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2193 node2193Labels := by rfl

theorem canonical19499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19499 raw19499Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw19499 raw19499Labels = mixedMoment B raw19499step0 raw19499step0Labels := by
      have hz : ∀ j, raw19499 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19499step0 = (fun i j => raw19499 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19499step0 raw19499; decide +kernel
      have hl : raw19499step0Labels = raw19499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19499 raw19499Labels permutation346 hz
    mixedMoment B raw19499step0 raw19499step0Labels = mixedMoment B raw19499step1 raw19499step1Labels := by
      have ha : raw19499step1 = (fun i j => raw19499step0 (permutation137 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19499step1 raw19499step0; decide +kernel
      have hl : raw19499step1Labels = raw19499step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19499step0 raw19499step0Labels permutation137 permutation0
    mixedMoment B raw19499step1 raw19499step1Labels = mixedMoment B raw19499step2 raw19499step2Labels := by
      have ha : raw19499step2 = -raw19499step1 := by apply Matrix.ext; change ∀ i j, raw19499step2 i j = -(raw19499step1 i j); unfold raw19499step2 raw19499step1; decide +kernel
      have hl : raw19499step2Labels = raw19499step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical19500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19500 raw19500Labels = mixedMoment B node1202 node1202Labels := by
  calc
    mixedMoment B raw19500 raw19500Labels = mixedMoment B raw19500step0 raw19500step0Labels := by
      have hz : ∀ j, raw19500 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19500step0 = (fun i j => raw19500 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19500step0 raw19500; decide +kernel
      have hl : raw19500step0Labels = raw19500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19500 raw19500Labels permutation346 hz
    mixedMoment B raw19500step0 raw19500step0Labels = mixedMoment B raw19500step1 raw19500step1Labels := by
      have ha : raw19500step1 = (fun i j => raw19500step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19500step1 raw19500step0; decide +kernel
      have hl : raw19500step1Labels = raw19500step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19500step0 raw19500step0Labels permutation40 permutation2
    _ = mixedMoment B node1202 node1202Labels := by rfl

theorem canonical19501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19501 raw19501Labels = mixedMoment B node1194 node1194Labels := by
  calc
    mixedMoment B raw19501 raw19501Labels = mixedMoment B raw19501step0 raw19501step0Labels := by
      have ha : raw19501step0 = (fun i j => raw19501 (permutation212 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19501step0 raw19501; decide +kernel
      have hl : raw19501step0Labels = raw19501Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19501 raw19501Labels permutation212 permutation2
    _ = mixedMoment B node1194 node1194Labels := by rfl

theorem canonical19502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19502 raw19502Labels = mixedMoment B node1211 node1211Labels := by
  calc
    mixedMoment B raw19502 raw19502Labels = mixedMoment B raw19502step0 raw19502step0Labels := by
      have hz : ∀ j, raw19502 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19502step0 = (fun i j => raw19502 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19502step0 raw19502; decide +kernel
      have hl : raw19502step0Labels = raw19502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19502 raw19502Labels permutation346 hz
    mixedMoment B raw19502step0 raw19502step0Labels = mixedMoment B raw19502step1 raw19502step1Labels := by
      have ha : raw19502step1 = (fun i j => raw19502step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19502step1 raw19502step0; decide +kernel
      have hl : raw19502step1Labels = raw19502step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19502step0 raw19502step0Labels permutation44 permutation2
    _ = mixedMoment B node1211 node1211Labels := by rfl

theorem canonical19503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19503 raw19503Labels = mixedMoment B node1211 node1211Labels := by
  calc
    mixedMoment B raw19503 raw19503Labels = mixedMoment B raw19503step0 raw19503step0Labels := by
      have hz : ∀ j, raw19503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19503step0 = (fun i j => raw19503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19503step0 raw19503; decide +kernel
      have hl : raw19503step0Labels = raw19503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19503 raw19503Labels permutation346 hz
    mixedMoment B raw19503step0 raw19503step0Labels = mixedMoment B raw19503step1 raw19503step1Labels := by
      have ha : raw19503step1 = (fun i j => raw19503step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19503step1 raw19503step0; decide +kernel
      have hl : raw19503step1Labels = raw19503step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19503step0 raw19503step0Labels permutation38 permutation2
    _ = mixedMoment B node1211 node1211Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3319 raw3319Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3319 raw3319Labels = mixedMoment B raw3319step0 raw3319step0Labels := by
      have hz : ∀ j, raw3319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3319step0 = (fun i j => raw3319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3319step0 raw3319; decide +kernel
      have hl : raw3319step0Labels = raw3319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3319 raw3319Labels permutation434 hz
    mixedMoment B raw3319step0 raw3319step0Labels = mixedMoment B raw3319step1 raw3319step1Labels := by
      have hz : ∀ j, raw3319step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3319step1 = (fun i j => raw3319step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3319step1 raw3319step0; decide +kernel
      have hl : raw3319step1Labels = raw3319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3319step0 raw3319step0Labels permutation80 hz
    mixedMoment B raw3319step1 raw3319step1Labels = mixedMoment B raw3319step2 raw3319step2Labels := by
      have hz : ∀ i, raw3319step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3319step2 = (fun i j => raw3319step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3319step2 raw3319step1; decide +kernel
      have hl : raw3319step2Labels = (fun j => raw3319step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3319step1 raw3319step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical3320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3320 raw3320Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3320 raw3320Labels = mixedMoment B raw3320step0 raw3320step0Labels := by
      have hz : ∀ j, raw3320 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3320step0 = (fun i j => raw3320 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3320step0 raw3320; decide +kernel
      have hl : raw3320step0Labels = raw3320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3320 raw3320Labels permutation434 hz
    mixedMoment B raw3320step0 raw3320step0Labels = mixedMoment B raw3320step1 raw3320step1Labels := by
      have hz : ∀ j, raw3320step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3320step1 = (fun i j => raw3320step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3320step1 raw3320step0; decide +kernel
      have hl : raw3320step1Labels = raw3320step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3320step0 raw3320step0Labels permutation56 hz
    mixedMoment B raw3320step1 raw3320step1Labels = mixedMoment B raw3320step2 raw3320step2Labels := by
      have hz : ∀ i, raw3320step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3320step2 = (fun i j => raw3320step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3320step2 raw3320step1; decide +kernel
      have hl : raw3320step2Labels = (fun j => raw3320step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3320step1 raw3320step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

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

theorem canonical3332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3332 raw3332Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3332 raw3332Labels = mixedMoment B raw3332step0 raw3332step0Labels := by
      have hz : ∀ j, raw3332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3332step0 = (fun i j => raw3332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3332step0 raw3332; decide +kernel
      have hl : raw3332step0Labels = raw3332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3332 raw3332Labels permutation346 hz
    mixedMoment B raw3332step0 raw3332step0Labels = mixedMoment B raw3332step1 raw3332step1Labels := by
      have hz : ∀ i, raw3332step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3332step1 = (fun i j => raw3332step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3332step1 raw3332step0; decide +kernel
      have hl : raw3332step1Labels = (fun j => raw3332step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3332step0 raw3332step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3333 raw3333Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3333 raw3333Labels = mixedMoment B raw3333step0 raw3333step0Labels := by
      have hz : ∀ j, raw3333 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3333step0 = (fun i j => raw3333 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3333step0 raw3333; decide +kernel
      have hl : raw3333step0Labels = raw3333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3333 raw3333Labels permutation265 hz
    mixedMoment B raw3333step0 raw3333step0Labels = mixedMoment B raw3333step1 raw3333step1Labels := by
      have hz : ∀ i, raw3333step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3333step1 = (fun i j => raw3333step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3333step1 raw3333step0; decide +kernel
      have hl : raw3333step1Labels = (fun j => raw3333step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3333step0 raw3333step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3432 raw3432Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3432 raw3432Labels = mixedMoment B raw3432step0 raw3432step0Labels := by
      have hz : ∀ j, raw3432 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3432step0 = (fun i j => raw3432 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3432step0 raw3432; decide +kernel
      have hl : raw3432step0Labels = raw3432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3432 raw3432Labels permutation434 hz
    mixedMoment B raw3432step0 raw3432step0Labels = mixedMoment B raw3432step1 raw3432step1Labels := by
      have hz : ∀ j, raw3432step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw3432step1 = (fun i j => raw3432step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw3432step1 raw3432step0; decide +kernel
      have hl : raw3432step1Labels = raw3432step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3432step0 raw3432step0Labels permutation32 hz
    mixedMoment B raw3432step1 raw3432step1Labels = mixedMoment B raw3432step2 raw3432step2Labels := by
      have hz : ∀ i, raw3432step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3432step2 = (fun i j => raw3432step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3432step2 raw3432step1; decide +kernel
      have hl : raw3432step2Labels = (fun j => raw3432step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3432step1 raw3432step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical3440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3440 raw3440Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3440 raw3440Labels = mixedMoment B raw3440step0 raw3440step0Labels := by
      have hz : ∀ j, raw3440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3440step0 = (fun i j => raw3440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3440step0 raw3440; decide +kernel
      have hl : raw3440step0Labels = raw3440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3440 raw3440Labels permutation346 hz
    mixedMoment B raw3440step0 raw3440step0Labels = mixedMoment B raw3440step1 raw3440step1Labels := by
      have hz : ∀ i, raw3440step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3440step1 = (fun i j => raw3440step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3440step1 raw3440step0; decide +kernel
      have hl : raw3440step1Labels = (fun j => raw3440step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3440step0 raw3440step0Labels permutation6 hz
    mixedMoment B raw3440step1 raw3440step1Labels = mixedMoment B raw3440step2 raw3440step2Labels := by
      have ha : raw3440step2 = (fun i j => raw3440step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3440step2 raw3440step1; decide +kernel
      have hl : raw3440step2Labels = raw3440step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3440step1 raw3440step1Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3442 raw3442Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3442 raw3442Labels = mixedMoment B raw3442step0 raw3442step0Labels := by
      have hz : ∀ j, raw3442 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3442step0 = (fun i j => raw3442 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3442step0 raw3442; decide +kernel
      have hl : raw3442step0Labels = raw3442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3442 raw3442Labels permutation520 hz
    mixedMoment B raw3442step0 raw3442step0Labels = mixedMoment B raw3442step1 raw3442step1Labels := by
      have hz : ∀ j, raw3442step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3442step1 = (fun i j => raw3442step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3442step1 raw3442step0; decide +kernel
      have hl : raw3442step1Labels = raw3442step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3442step0 raw3442step0Labels permutation80 hz
    mixedMoment B raw3442step1 raw3442step1Labels = mixedMoment B raw3442step2 raw3442step2Labels := by
      have hz : ∀ i, raw3442step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3442step2 = (fun i j => raw3442step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3442step2 raw3442step1; decide +kernel
      have hl : raw3442step2Labels = (fun j => raw3442step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3442step1 raw3442step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical3443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3443 raw3443Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3443 raw3443Labels = mixedMoment B raw3443step0 raw3443step0Labels := by
      have hz : ∀ j, raw3443 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3443step0 = (fun i j => raw3443 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3443step0 raw3443; decide +kernel
      have hl : raw3443step0Labels = raw3443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3443 raw3443Labels permutation590 hz
    mixedMoment B raw3443step0 raw3443step0Labels = mixedMoment B raw3443step1 raw3443step1Labels := by
      have hz : ∀ j, raw3443step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3443step1 = (fun i j => raw3443step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3443step1 raw3443step0; decide +kernel
      have hl : raw3443step1Labels = raw3443step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3443step0 raw3443step0Labels permutation80 hz
    mixedMoment B raw3443step1 raw3443step1Labels = mixedMoment B raw3443step2 raw3443step2Labels := by
      have hz : ∀ i, raw3443step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3443step2 = (fun i j => raw3443step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3443step2 raw3443step1; decide +kernel
      have hl : raw3443step2Labels = (fun j => raw3443step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3443step1 raw3443step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical3445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3445 raw3445Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3445 raw3445Labels = mixedMoment B raw3445step0 raw3445step0Labels := by
      have hz : ∀ j, raw3445 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3445step0 = (fun i j => raw3445 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3445step0 raw3445; decide +kernel
      have hl : raw3445step0Labels = raw3445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3445 raw3445Labels permutation434 hz
    mixedMoment B raw3445step0 raw3445step0Labels = mixedMoment B raw3445step1 raw3445step1Labels := by
      have hz : ∀ i, raw3445step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3445step1 = (fun i j => raw3445step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3445step1 raw3445step0; decide +kernel
      have hl : raw3445step1Labels = (fun j => raw3445step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3445step0 raw3445step0Labels permutation6 hz
    mixedMoment B raw3445step1 raw3445step1Labels = mixedMoment B raw3445step2 raw3445step2Labels := by
      have ha : raw3445step2 = (fun i j => raw3445step1 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3445step2 raw3445step1; decide +kernel
      have hl : raw3445step2Labels = raw3445step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3445step1 raw3445step1Labels permutation122 permutation0
    mixedMoment B raw3445step2 raw3445step2Labels = mixedMoment B raw3445step3 raw3445step3Labels := by
      have ha : raw3445step3 = -raw3445step2 := by apply Matrix.ext; change ∀ i j, raw3445step3 i j = -(raw3445step2 i j); unfold raw3445step3 raw3445step2; decide +kernel
      have hl : raw3445step3Labels = raw3445step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3449 raw3449Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3449 raw3449Labels = mixedMoment B raw3449step0 raw3449step0Labels := by
      have hz : ∀ j, raw3449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3449step0 = (fun i j => raw3449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3449step0 raw3449; decide +kernel
      have hl : raw3449step0Labels = raw3449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3449 raw3449Labels permutation434 hz
    mixedMoment B raw3449step0 raw3449step0Labels = mixedMoment B raw3449step1 raw3449step1Labels := by
      have hz : ∀ i, raw3449step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3449step1 = (fun i j => raw3449step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3449step1 raw3449step0; decide +kernel
      have hl : raw3449step1Labels = (fun j => raw3449step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3449step0 raw3449step0Labels permutation6 hz
    mixedMoment B raw3449step1 raw3449step1Labels = mixedMoment B raw3449step2 raw3449step2Labels := by
      have ha : raw3449step2 = (fun i j => raw3449step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3449step2 raw3449step1; decide +kernel
      have hl : raw3449step2Labels = raw3449step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3449step1 raw3449step1Labels permutation146 permutation0
    mixedMoment B raw3449step2 raw3449step2Labels = mixedMoment B raw3449step3 raw3449step3Labels := by
      have ha : raw3449step3 = -raw3449step2 := by apply Matrix.ext; change ∀ i j, raw3449step3 i j = -(raw3449step2 i j); unfold raw3449step3 raw3449step2; decide +kernel
      have hl : raw3449step3Labels = raw3449step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

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

theorem canonical664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw664 raw664Labels = mixedMoment B node4096 node4096Labels := by
  calc
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw665 raw665Labels = mixedMoment B node7 node7Labels := by
  calc
    _ = mixedMoment B node7 node7Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node7 node7Labels = Sparse.eval singlePairValue7 (familyPairVector B) := by
  have hp := single_label_two B hB node7
  have hl : node7Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node7 (EqualityPatterns.family2.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node7 (EqualityPatterns.family2.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family2_0]
      apply Matrix.ext; unfold node7 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node7 (EqualityPatterns.family2.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node7 (EqualityPatterns.family2.label 1) = PairSemantics.raw7678 := by
      rw [groupedColumns_family2_1]
      apply Matrix.ext; unfold node7 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  rw [hm0, hm1] at hp
  norm_num [singlePairValue7, PairSemantics.value0, PairSemantics.value65, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4096 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4096 node4096Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node7 node7Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw664 singletonSmall4096
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4096) = raw664Labels := by decide +kernel
  rw [hl, canonical664 B hB] at h
  have hc0 : mixedMoment B raw664 (Fin.cases (0 : Fin 1) singletonSmall4096) =
      mixedMoment B node7 node7Labels := by
    have ha : raw664 = raw665 := by apply Matrix.ext; unfold raw664 raw665; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4096 = raw665Labels := by decide +kernel
    rw [ha, hj, canonical665 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem sound7 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node7 node7Labels = Sparse.eval nodeValue7 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue7 (familyPairVector B) := singlePair7 B _hB
    _ = _ := by norm_num [singlePairValue7, nodeValue7, Sparse.eval, mixedVector]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node794 node794Labels = Sparse.eval nodeValue794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 794) = mixedMoment B node794 node794Labels := rfl
  simpa [nodeValue794, Sparse.eval] using hc.symm

theorem sound797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node797 node797Labels = Sparse.eval nodeValue797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 797) = mixedMoment B node797 node797Labels := rfl
  simpa [nodeValue797, Sparse.eval] using hc.symm

theorem sound813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node813 node813Labels = Sparse.eval nodeValue813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 813) = mixedMoment B node813 node813Labels := rfl
  simpa [nodeValue813, Sparse.eval] using hc.symm

theorem sound828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node828 node828Labels = Sparse.eval nodeValue828 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 828) = mixedMoment B node828 node828Labels := rfl
  simpa [nodeValue828, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node849 node849Labels = Sparse.eval nodeValue849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 849) = mixedMoment B node849 node849Labels := rfl
  simpa [nodeValue849, Sparse.eval] using hc.symm

theorem sound862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node862 node862Labels = Sparse.eval nodeValue862 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 862) = mixedMoment B node862 node862Labels := rfl
  simpa [nodeValue862, Sparse.eval] using hc.symm

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

theorem sound911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node911 node911Labels = Sparse.eval nodeValue911 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 911) = mixedMoment B node911 node911Labels := rfl
  simpa [nodeValue911, Sparse.eval] using hc.symm

theorem sound936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node936 node936Labels = Sparse.eval nodeValue936 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 936) = mixedMoment B node936 node936Labels := rfl
  simpa [nodeValue936, Sparse.eval] using hc.symm

theorem sound951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node951 node951Labels = Sparse.eval nodeValue951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 951) = mixedMoment B node951 node951Labels := rfl
  simpa [nodeValue951, Sparse.eval] using hc.symm

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

theorem sound975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node975 node975Labels = Sparse.eval nodeValue975 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 975) = mixedMoment B node975 node975Labels := rfl
  simpa [nodeValue975, Sparse.eval] using hc.symm

theorem sound982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node982 node982Labels = Sparse.eval nodeValue982 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 982) = mixedMoment B node982 node982Labels := rfl
  simpa [nodeValue982, Sparse.eval] using hc.symm

theorem sound989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node989 node989Labels = Sparse.eval nodeValue989 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 989) = mixedMoment B node989 node989Labels := rfl
  simpa [nodeValue989, Sparse.eval] using hc.symm

theorem sound994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node994 node994Labels = Sparse.eval nodeValue994 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 994) = mixedMoment B node994 node994Labels := rfl
  simpa [nodeValue994, Sparse.eval] using hc.symm

theorem sound1009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1009 node1009Labels = Sparse.eval nodeValue1009 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1009) = mixedMoment B node1009 node1009Labels := rfl
  simpa [nodeValue1009, Sparse.eval] using hc.symm

theorem sound1019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1019 node1019Labels = Sparse.eval nodeValue1019 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1019) = mixedMoment B node1019 node1019Labels := rfl
  simpa [nodeValue1019, Sparse.eval] using hc.symm

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

theorem sound1027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1027 node1027Labels = Sparse.eval nodeValue1027 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1027) = mixedMoment B node1027 node1027Labels := rfl
  simpa [nodeValue1027, Sparse.eval] using hc.symm

theorem sound1046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1046 node1046Labels = Sparse.eval nodeValue1046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1046) = mixedMoment B node1046 node1046Labels := rfl
  simpa [nodeValue1046, Sparse.eval] using hc.symm

theorem sound1055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1055 node1055Labels = Sparse.eval nodeValue1055 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1055) = mixedMoment B node1055 node1055Labels := rfl
  simpa [nodeValue1055, Sparse.eval] using hc.symm

theorem sound1064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1064 node1064Labels = Sparse.eval nodeValue1064 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1064) = mixedMoment B node1064 node1064Labels := rfl
  simpa [nodeValue1064, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1091 node1091Labels = Sparse.eval nodeValue1091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1091) = mixedMoment B node1091 node1091Labels := rfl
  simpa [nodeValue1091, Sparse.eval] using hc.symm

theorem sound1115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1115 node1115Labels = Sparse.eval nodeValue1115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1115) = mixedMoment B node1115 node1115Labels := rfl
  simpa [nodeValue1115, Sparse.eval] using hc.symm

theorem sound1140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1140 node1140Labels = Sparse.eval nodeValue1140 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1140) = mixedMoment B node1140 node1140Labels := rfl
  simpa [nodeValue1140, Sparse.eval] using hc.symm

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

theorem sound1179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1179 node1179Labels = Sparse.eval nodeValue1179 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1179) = mixedMoment B node1179 node1179Labels := rfl
  simpa [nodeValue1179, Sparse.eval] using hc.symm

theorem sound1190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1190 node1190Labels = Sparse.eval nodeValue1190 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1190) = mixedMoment B node1190 node1190Labels := rfl
  simpa [nodeValue1190, Sparse.eval] using hc.symm

theorem sound1194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1194 node1194Labels = Sparse.eval nodeValue1194 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1194) = mixedMoment B node1194 node1194Labels := rfl
  simpa [nodeValue1194, Sparse.eval] using hc.symm

theorem sound1202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1202 node1202Labels = Sparse.eval nodeValue1202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1202) = mixedMoment B node1202 node1202Labels := rfl
  simpa [nodeValue1202, Sparse.eval] using hc.symm

theorem sound1211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1211 node1211Labels = Sparse.eval nodeValue1211 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1211) = mixedMoment B node1211 node1211Labels := rfl
  simpa [nodeValue1211, Sparse.eval] using hc.symm

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

theorem sound1221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1221 node1221Labels = Sparse.eval nodeValue1221 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1221) = mixedMoment B node1221 node1221Labels := rfl
  simpa [nodeValue1221, Sparse.eval] using hc.symm

theorem sound1242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1242 node1242Labels = Sparse.eval nodeValue1242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1242) = mixedMoment B node1242 node1242Labels := rfl
  simpa [nodeValue1242, Sparse.eval] using hc.symm

theorem sound1258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1258 node1258Labels = Sparse.eval nodeValue1258 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1258) = mixedMoment B node1258 node1258Labels := rfl
  simpa [nodeValue1258, Sparse.eval] using hc.symm

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

theorem sound1615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1615 node1615Labels = Sparse.eval nodeValue1615 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1615) = mixedMoment B node1615 node1615Labels := rfl
  simpa [nodeValue1615, Sparse.eval] using hc.symm

theorem sound1620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1620 node1620Labels = Sparse.eval nodeValue1620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1620) = mixedMoment B node1620 node1620Labels := rfl
  simpa [nodeValue1620, Sparse.eval] using hc.symm

theorem sound1629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1629 node1629Labels = Sparse.eval nodeValue1629 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1629) = mixedMoment B node1629 node1629Labels := rfl
  simpa [nodeValue1629, Sparse.eval] using hc.symm

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

theorem sound1716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1716 node1716Labels = Sparse.eval nodeValue1716 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1716) = mixedMoment B node1716 node1716Labels := rfl
  simpa [nodeValue1716, Sparse.eval] using hc.symm

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

theorem sound1749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1749 node1749Labels = Sparse.eval nodeValue1749 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1749) = mixedMoment B node1749 node1749Labels := rfl
  simpa [nodeValue1749, Sparse.eval] using hc.symm

theorem sound1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1752 node1752Labels = Sparse.eval nodeValue1752 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1752) = mixedMoment B node1752 node1752Labels := rfl
  simpa [nodeValue1752, Sparse.eval] using hc.symm

theorem sound1757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1757 node1757Labels = Sparse.eval nodeValue1757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1757) = mixedMoment B node1757 node1757Labels := rfl
  simpa [nodeValue1757, Sparse.eval] using hc.symm

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

theorem sound2193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2193 node2193Labels = Sparse.eval nodeValue2193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2193) = mixedMoment B node2193 node2193Labels := rfl
  simpa [nodeValue2193, Sparse.eval] using hc.symm

theorem sound2218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2218 node2218Labels = Sparse.eval nodeValue2218 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2218) = mixedMoment B node2218 node2218Labels := rfl
  simpa [nodeValue2218, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3298 node3298Labels = Sparse.eval nodeValue3298 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3298) = mixedMoment B node3298 node3298Labels := rfl
  simpa [nodeValue3298, Sparse.eval] using hc.symm

theorem sound3313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3313 node3313Labels = Sparse.eval nodeValue3313 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3313) = mixedMoment B node3313 node3313Labels := rfl
  simpa [nodeValue3313, Sparse.eval] using hc.symm

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

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

theorem sound4072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4072 node4072Labels = Sparse.eval nodeValue4072 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4072) = mixedMoment B node4072 node4072Labels := rfl
  simpa [nodeValue4072, Sparse.eval] using hc.symm

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4090 node4090Labels = Sparse.eval nodeValue4090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4090) = mixedMoment B node4090 node4090Labels := rfl
  simpa [nodeValue4090, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node587 node587Labels = Sparse.eval nodeValue587 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 587) = mixedMoment B node587 node587Labels := rfl
  simpa [nodeValue587, Sparse.eval] using hc.symm

theorem sound617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node617 node617Labels = Sparse.eval nodeValue617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 617) = mixedMoment B node617 node617Labels := rfl
  simpa [nodeValue617, Sparse.eval] using hc.symm

theorem sound633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node633 node633Labels = Sparse.eval nodeValue633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 633) = mixedMoment B node633 node633Labels := rfl
  simpa [nodeValue633, Sparse.eval] using hc.symm

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

theorem sound4096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4096 node4096Labels = Sparse.eval nodeValue4096 (mixedVector B) := by
  have h := singleton4096 B _hB
  rw [sound7 B _hB _hF] at h
  norm_num [nodeValue4096, nodeValue7, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources35
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1141 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1141 + difference 0 1) (sourceB1141 + difference 1 0) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 0 1) (sourceB1141 + difference 1 0) sourceC1141) = raw19390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19390; decide +kernel
    rw [ha]
    exact (canonical19390 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1141 + difference 0 2) (sourceB1141 + difference 2 0) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 0 2) (sourceB1141 + difference 2 0) sourceC1141) = raw19391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19391; decide +kernel
    rw [ha]
    exact (canonical19391 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1141 + difference 0 3) (sourceB1141 + difference 3 0) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 0 3) (sourceB1141 + difference 3 0) sourceC1141) = raw3432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3432; decide +kernel
    rw [ha]
    exact (canonical3432 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1141 + difference 0 4) (sourceB1141 + difference 4 0) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 0 4) (sourceB1141 + difference 4 0) sourceC1141) = raw19392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19392; decide +kernel
    rw [ha]
    exact (canonical19392 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1141 + difference 0 5) (sourceB1141 + difference 5 0) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 0 5) (sourceB1141 + difference 5 0) sourceC1141) = raw19393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19393; decide +kernel
    rw [ha]
    exact (canonical19393 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1141 + difference 1 0) (sourceB1141 + difference 0 1) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 1 0) (sourceB1141 + difference 0 1) sourceC1141) = raw3333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3333; decide +kernel
    rw [ha]
    exact (canonical3333 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1141 + difference 1 2) (sourceB1141 + difference 2 1) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 1 2) (sourceB1141 + difference 2 1) sourceC1141) = raw19394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19394; decide +kernel
    rw [ha]
    exact (canonical19394 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1141 + difference 1 3) (sourceB1141 + difference 3 1) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 1 3) (sourceB1141 + difference 3 1) sourceC1141) = raw3320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3320; decide +kernel
    rw [ha]
    exact (canonical3320 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1141 + difference 1 4) (sourceB1141 + difference 4 1) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 1 4) (sourceB1141 + difference 4 1) sourceC1141) = raw19395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19395; decide +kernel
    rw [ha]
    exact (canonical19395 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1141 + difference 1 5) (sourceB1141 + difference 5 1) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 1 5) (sourceB1141 + difference 5 1) sourceC1141) = raw19396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19396; decide +kernel
    rw [ha]
    exact (canonical19396 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1141 + difference 2 0) (sourceB1141 + difference 0 2) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 2 0) (sourceB1141 + difference 0 2) sourceC1141) = raw3332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3332; decide +kernel
    rw [ha]
    exact (canonical3332 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1141 + difference 2 1) (sourceB1141 + difference 1 2) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 2 1) (sourceB1141 + difference 1 2) sourceC1141) = raw3440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3440; decide +kernel
    rw [ha]
    exact (canonical3440 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1141 + difference 2 3) (sourceB1141 + difference 3 2) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 2 3) (sourceB1141 + difference 3 2) sourceC1141) = raw3319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3319; decide +kernel
    rw [ha]
    exact (canonical3319 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1141 + difference 2 4) (sourceB1141 + difference 4 2) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 2 4) (sourceB1141 + difference 4 2) sourceC1141) = raw3442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3442; decide +kernel
    rw [ha]
    exact (canonical3442 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1141 + difference 2 5) (sourceB1141 + difference 5 2) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 2 5) (sourceB1141 + difference 5 2) sourceC1141) = raw3443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3443; decide +kernel
    rw [ha]
    exact (canonical3443 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1141 + difference 3 0) (sourceB1141 + difference 0 3) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 3 0) (sourceB1141 + difference 0 3) sourceC1141) = raw19364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19364; decide +kernel
    rw [ha]
    exact (canonical19364 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1141 + difference 3 1) (sourceB1141 + difference 1 3) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 3 1) (sourceB1141 + difference 1 3) sourceC1141) = raw19397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19397; decide +kernel
    rw [ha]
    exact (canonical19397 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1141 + difference 3 2) (sourceB1141 + difference 2 3) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 3 2) (sourceB1141 + difference 2 3) sourceC1141) = raw19398 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19398; decide +kernel
    rw [ha]
    exact (canonical19398 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1141 + difference 3 4) (sourceB1141 + difference 4 3) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 3 4) (sourceB1141 + difference 4 3) sourceC1141) = raw19399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19399; decide +kernel
    rw [ha]
    exact (canonical19399 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1141 + difference 3 5) (sourceB1141 + difference 5 3) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 3 5) (sourceB1141 + difference 5 3) sourceC1141) = raw19400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19400; decide +kernel
    rw [ha]
    exact (canonical19400 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1141 + difference 4 0) (sourceB1141 + difference 0 4) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 4 0) (sourceB1141 + difference 0 4) sourceC1141) = raw19368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19368; decide +kernel
    rw [ha]
    exact (canonical19368 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1141 + difference 4 1) (sourceB1141 + difference 1 4) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 4 1) (sourceB1141 + difference 1 4) sourceC1141) = raw19401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19401; decide +kernel
    rw [ha]
    exact (canonical19401 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1141 + difference 4 2) (sourceB1141 + difference 2 4) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 4 2) (sourceB1141 + difference 2 4) sourceC1141) = raw19402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19402; decide +kernel
    rw [ha]
    exact (canonical19402 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1141 + difference 4 3) (sourceB1141 + difference 3 4) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 4 3) (sourceB1141 + difference 3 4) sourceC1141) = raw3445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3445; decide +kernel
    rw [ha]
    exact (canonical3445 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1141 + difference 4 5) (sourceB1141 + difference 5 4) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 4 5) (sourceB1141 + difference 5 4) sourceC1141) = raw19403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19403; decide +kernel
    rw [ha]
    exact (canonical19403 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1141 + difference 5 0) (sourceB1141 + difference 0 5) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 5 0) (sourceB1141 + difference 0 5) sourceC1141) = raw18338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw18338; decide +kernel
    rw [ha]
    exact (canonical18338 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1141 + difference 5 1) (sourceB1141 + difference 1 5) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 5 1) (sourceB1141 + difference 1 5) sourceC1141) = raw19404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19404; decide +kernel
    rw [ha]
    exact (canonical19404 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1141 + difference 5 2) (sourceB1141 + difference 2 5) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 5 2) (sourceB1141 + difference 2 5) sourceC1141) = raw19405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19405; decide +kernel
    rw [ha]
    exact (canonical19405 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1141 + difference 5 3) (sourceB1141 + difference 3 5) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 5 3) (sourceB1141 + difference 3 5) sourceC1141) = raw3449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3449; decide +kernel
    rw [ha]
    exact (canonical3449 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1141 + difference 5 4) (sourceB1141 + difference 4 5) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 5 4) (sourceB1141 + difference 4 5) sourceC1141) = raw19406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19406; decide +kernel
    rw [ha]
    exact (canonical19406 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1141 sourceB1141 sourceC1141
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1141, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1142 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1142 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1142 + difference 4 0) (sourceB1142 + difference 0 4) sourceC1142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 617) := by
    have ha : (tripleCharges (sourceA1142 + difference 4 0) (sourceB1142 + difference 0 4) sourceC1142) = raw19407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1142 sourceB1142 sourceC1142 difference raw19407; decide +kernel
    rw [ha]
    exact (canonical19407 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1142 + difference 4 1) (sourceB1142 + difference 1 4) sourceC1142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 936) := by
    have ha : (tripleCharges (sourceA1142 + difference 4 1) (sourceB1142 + difference 1 4) sourceC1142) = raw19408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1142 sourceB1142 sourceC1142 difference raw19408; decide +kernel
    rw [ha]
    exact (canonical19408 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1142 + difference 4 2) (sourceB1142 + difference 2 4) sourceC1142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 936) := by
    have ha : (tripleCharges (sourceA1142 + difference 4 2) (sourceB1142 + difference 2 4) sourceC1142) = raw19409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1142 sourceB1142 sourceC1142 difference raw19409; decide +kernel
    rw [ha]
    exact (canonical19409 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1142 + difference 4 3) (sourceB1142 + difference 3 4) sourceC1142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 936) := by
    have ha : (tripleCharges (sourceA1142 + difference 4 3) (sourceB1142 + difference 3 4) sourceC1142) = raw19410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1142 sourceB1142 sourceC1142 difference raw19410; decide +kernel
    rw [ha]
    exact (canonical19410 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1142 + difference 4 4) (sourceB1142 + difference 4 4) sourceC1142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1064) := by
    have ha : (tripleCharges (sourceA1142 + difference 4 4) (sourceB1142 + difference 4 4) sourceC1142) = raw19411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1142 sourceB1142 sourceC1142 difference raw19411; decide +kernel
    rw [ha]
    exact (canonical19411 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1142 + difference 4 5) (sourceB1142 + difference 5 4) sourceC1142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA1142 + difference 4 5) (sourceB1142 + difference 5 4) sourceC1142) = raw19412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1142 sourceB1142 sourceC1142 difference raw19412; decide +kernel
    rw [ha]
    exact (canonical19412 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1142 + sourceB1142) sourceC1142) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1142 + sourceB1142) sourceC1142) = raw19413 := by
      apply Matrix.ext; unfold doubleCharges sourceA1142 sourceB1142 sourceC1142 raw19413; decide +kernel
    rw [ha]
    exact (canonical19413 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1142 sourceB1142 sourceC1142
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1142, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1143 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1143 + difference 0 0) (sourceB1143 + difference 0 0) sourceC1143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1757) := by
    have ha : (tripleCharges (sourceA1143 + difference 0 0) (sourceB1143 + difference 0 0) sourceC1143) = raw19414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1143 sourceB1143 sourceC1143 difference raw19414; decide +kernel
    rw [ha]
    exact (canonical19414 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1143 + difference 0 1) (sourceB1143 + difference 1 0) sourceC1143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1629) := by
    have ha : (tripleCharges (sourceA1143 + difference 0 1) (sourceB1143 + difference 1 0) sourceC1143) = raw19415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1143 sourceB1143 sourceC1143 difference raw19415; decide +kernel
    rw [ha]
    exact (canonical19415 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1143 + difference 0 2) (sourceB1143 + difference 2 0) sourceC1143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1629) := by
    have ha : (tripleCharges (sourceA1143 + difference 0 2) (sourceB1143 + difference 2 0) sourceC1143) = raw19416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1143 sourceB1143 sourceC1143 difference raw19416; decide +kernel
    rw [ha]
    exact (canonical19416 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1143 + difference 0 3) (sourceB1143 + difference 3 0) sourceC1143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1629) := by
    have ha : (tripleCharges (sourceA1143 + difference 0 3) (sourceB1143 + difference 3 0) sourceC1143) = raw19417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1143 sourceB1143 sourceC1143 difference raw19417; decide +kernel
    rw [ha]
    exact (canonical19417 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1143 + difference 0 4) (sourceB1143 + difference 4 0) sourceC1143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1143 + difference 0 4) (sourceB1143 + difference 4 0) sourceC1143) = raw19418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1143 sourceB1143 sourceC1143 difference raw19418; decide +kernel
    rw [ha]
    exact (canonical19418 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1143 + difference 0 5) (sourceB1143 + difference 5 0) sourceC1143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 862) := by
    have ha : (tripleCharges (sourceA1143 + difference 0 5) (sourceB1143 + difference 5 0) sourceC1143) = raw19419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1143 sourceB1143 sourceC1143 difference raw19419; decide +kernel
    rw [ha]
    exact (canonical19419 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1143 + sourceB1143) sourceC1143) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1143 + sourceB1143) sourceC1143) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1143 sourceB1143 sourceC1143 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1143 sourceB1143 sourceC1143
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1143, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1145 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1145 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1145 + difference 0 4) (sourceB1145 + difference 4 0) sourceC1145) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1145 + difference 0 4) (sourceB1145 + difference 4 0) sourceC1145) = raw19418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1145 sourceB1145 sourceC1145 difference raw19418; decide +kernel
    rw [ha]
    exact (canonical19418 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1145 + difference 1 4) (sourceB1145 + difference 4 1) sourceC1145) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1749) := by
    have ha : (tripleCharges (sourceA1145 + difference 1 4) (sourceB1145 + difference 4 1) sourceC1145) = raw19426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1145 sourceB1145 sourceC1145 difference raw19426; decide +kernel
    rw [ha]
    exact (canonical19426 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1145 + difference 2 4) (sourceB1145 + difference 4 2) sourceC1145) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1749) := by
    have ha : (tripleCharges (sourceA1145 + difference 2 4) (sourceB1145 + difference 4 2) sourceC1145) = raw19427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1145 sourceB1145 sourceC1145 difference raw19427; decide +kernel
    rw [ha]
    exact (canonical19427 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1145 + difference 3 4) (sourceB1145 + difference 4 3) sourceC1145) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1749) := by
    have ha : (tripleCharges (sourceA1145 + difference 3 4) (sourceB1145 + difference 4 3) sourceC1145) = raw19428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1145 sourceB1145 sourceC1145 difference raw19428; decide +kernel
    rw [ha]
    exact (canonical19428 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1145 + difference 4 4) (sourceB1145 + difference 4 4) sourceC1145) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1757) := by
    have ha : (tripleCharges (sourceA1145 + difference 4 4) (sourceB1145 + difference 4 4) sourceC1145) = raw19414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1145 sourceB1145 sourceC1145 difference raw19414; decide +kernel
    rw [ha]
    exact (canonical19414 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1145 + difference 5 4) (sourceB1145 + difference 4 5) sourceC1145) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1145 + difference 5 4) (sourceB1145 + difference 4 5) sourceC1145) = raw19429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1145 sourceB1145 sourceC1145 difference raw19429; decide +kernel
    rw [ha]
    exact (canonical19429 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1145 + sourceB1145) sourceC1145) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1145 + sourceB1145) sourceC1145) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1145 sourceB1145 sourceC1145 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1145 sourceB1145 sourceC1145
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1145, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1147 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1147 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1147 + difference 3 0) (sourceB1147 + difference 0 3) sourceC1147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 587) := by
    have ha : (tripleCharges (sourceA1147 + difference 3 0) (sourceB1147 + difference 0 3) sourceC1147) = raw19437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1147 sourceB1147 sourceC1147 difference raw19437; decide +kernel
    rw [ha]
    exact (canonical19437 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1147 + difference 3 1) (sourceB1147 + difference 1 3) sourceC1147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 911) := by
    have ha : (tripleCharges (sourceA1147 + difference 3 1) (sourceB1147 + difference 1 3) sourceC1147) = raw19438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1147 sourceB1147 sourceC1147 difference raw19438; decide +kernel
    rw [ha]
    exact (canonical19438 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1147 + difference 3 2) (sourceB1147 + difference 2 3) sourceC1147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 911) := by
    have ha : (tripleCharges (sourceA1147 + difference 3 2) (sourceB1147 + difference 2 3) sourceC1147) = raw19439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1147 sourceB1147 sourceC1147 difference raw19439; decide +kernel
    rw [ha]
    exact (canonical19439 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1147 + difference 3 3) (sourceB1147 + difference 3 3) sourceC1147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1027) := by
    have ha : (tripleCharges (sourceA1147 + difference 3 3) (sourceB1147 + difference 3 3) sourceC1147) = raw19440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1147 sourceB1147 sourceC1147 difference raw19440; decide +kernel
    rw [ha]
    exact (canonical19440 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1147 + difference 3 4) (sourceB1147 + difference 4 3) sourceC1147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 951) := by
    have ha : (tripleCharges (sourceA1147 + difference 3 4) (sourceB1147 + difference 4 3) sourceC1147) = raw19441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1147 sourceB1147 sourceC1147 difference raw19441; decide +kernel
    rw [ha]
    exact (canonical19441 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1147 + difference 3 5) (sourceB1147 + difference 5 3) sourceC1147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1147 + difference 3 5) (sourceB1147 + difference 5 3) sourceC1147) = raw19442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1147 sourceB1147 sourceC1147 difference raw19442; decide +kernel
    rw [ha]
    exact (canonical19442 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1147 + sourceB1147) sourceC1147) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1147 + sourceB1147) sourceC1147) = raw19443 := by
      apply Matrix.ext; unfold doubleCharges sourceA1147 sourceB1147 sourceC1147 raw19443; decide +kernel
    rw [ha]
    exact (canonical19443 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1147 sourceB1147 sourceC1147
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1147, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1148 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1148 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1148 + difference 0 0) (sourceB1148 + difference 0 0) sourceC1148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1749) := by
    have ha : (tripleCharges (sourceA1148 + difference 0 0) (sourceB1148 + difference 0 0) sourceC1148) = raw19428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1148 sourceB1148 sourceC1148 difference raw19428; decide +kernel
    rw [ha]
    exact (canonical19428 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1148 + difference 0 1) (sourceB1148 + difference 1 0) sourceC1148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1615) := by
    have ha : (tripleCharges (sourceA1148 + difference 0 1) (sourceB1148 + difference 1 0) sourceC1148) = raw19444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1148 sourceB1148 sourceC1148 difference raw19444; decide +kernel
    rw [ha]
    exact (canonical19444 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1148 + difference 0 2) (sourceB1148 + difference 2 0) sourceC1148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1615) := by
    have ha : (tripleCharges (sourceA1148 + difference 0 2) (sourceB1148 + difference 2 0) sourceC1148) = raw19445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1148 sourceB1148 sourceC1148 difference raw19445; decide +kernel
    rw [ha]
    exact (canonical19445 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1148 + difference 0 3) (sourceB1148 + difference 3 0) sourceC1148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1148 + difference 0 3) (sourceB1148 + difference 3 0) sourceC1148) = raw19418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1148 sourceB1148 sourceC1148 difference raw19418; decide +kernel
    rw [ha]
    exact (canonical19418 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1148 + difference 0 4) (sourceB1148 + difference 4 0) sourceC1148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1148 + difference 0 4) (sourceB1148 + difference 4 0) sourceC1148) = raw19446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1148 sourceB1148 sourceC1148 difference raw19446; decide +kernel
    rw [ha]
    exact (canonical19446 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1148 + difference 0 5) (sourceB1148 + difference 5 0) sourceC1148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 849) := by
    have ha : (tripleCharges (sourceA1148 + difference 0 5) (sourceB1148 + difference 5 0) sourceC1148) = raw19447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1148 sourceB1148 sourceC1148 difference raw19447; decide +kernel
    rw [ha]
    exact (canonical19447 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1148 + sourceB1148) sourceC1148) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1148 + sourceB1148) sourceC1148) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1148 sourceB1148 sourceC1148 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1148 sourceB1148 sourceC1148
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1148, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1150 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1150 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1150 + difference 0 0) (sourceB1150 + difference 0 0) sourceC1150) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 797) := by
    have ha : (tripleCharges (sourceA1150 + difference 0 0) (sourceB1150 + difference 0 0) sourceC1150) = raw19452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1150 sourceB1150 sourceC1150 difference raw19452; decide +kernel
    rw [ha]
    exact (canonical19452 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1150 + difference 0 1) (sourceB1150 + difference 1 0) sourceC1150) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 794) := by
    have ha : (tripleCharges (sourceA1150 + difference 0 1) (sourceB1150 + difference 1 0) sourceC1150) = raw19453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1150 sourceB1150 sourceC1150 difference raw19453; decide +kernel
    rw [ha]
    exact (canonical19453 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1150 + difference 0 2) (sourceB1150 + difference 2 0) sourceC1150) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 794) := by
    have ha : (tripleCharges (sourceA1150 + difference 0 2) (sourceB1150 + difference 2 0) sourceC1150) = raw19454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1150 sourceB1150 sourceC1150 difference raw19454; decide +kernel
    rw [ha]
    exact (canonical19454 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1150 + difference 0 3) (sourceB1150 + difference 3 0) sourceC1150) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 828) := by
    have ha : (tripleCharges (sourceA1150 + difference 0 3) (sourceB1150 + difference 3 0) sourceC1150) = raw19455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1150 sourceB1150 sourceC1150 difference raw19455; decide +kernel
    rw [ha]
    exact (canonical19455 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1150 + difference 0 4) (sourceB1150 + difference 4 0) sourceC1150) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 813) := by
    have ha : (tripleCharges (sourceA1150 + difference 0 4) (sourceB1150 + difference 4 0) sourceC1150) = raw19456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1150 sourceB1150 sourceC1150 difference raw19456; decide +kernel
    rw [ha]
    exact (canonical19456 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1150 + difference 0 5) (sourceB1150 + difference 5 0) sourceC1150) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1150 + difference 0 5) (sourceB1150 + difference 5 0) sourceC1150) = raw19457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1150 sourceB1150 sourceC1150 difference raw19457; decide +kernel
    rw [ha]
    exact (canonical19457 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1150 + sourceB1150) sourceC1150) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1150 + sourceB1150) sourceC1150) = raw19458 := by
      apply Matrix.ext; unfold doubleCharges sourceA1150 sourceB1150 sourceC1150 raw19458; decide +kernel
    rw [ha]
    exact (canonical19458 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1150 sourceB1150 sourceC1150
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1150, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources36
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1152 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1152 + difference 0 1) (sourceB1152 + difference 1 0) sourceC1152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1152 + difference 0 1) (sourceB1152 + difference 1 0) sourceC1152) = raw19466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1152 sourceB1152 sourceC1152 difference raw19466; decide +kernel
    rw [ha]
    exact (canonical19466 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1152 + difference 1 1) (sourceB1152 + difference 1 1) sourceC1152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1152 + difference 1 1) (sourceB1152 + difference 1 1) sourceC1152) = raw19467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1152 sourceB1152 sourceC1152 difference raw19467; decide +kernel
    rw [ha]
    exact (canonical19467 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1152 + difference 2 1) (sourceB1152 + difference 1 2) sourceC1152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1115) := by
    have ha : (tripleCharges (sourceA1152 + difference 2 1) (sourceB1152 + difference 1 2) sourceC1152) = raw19468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1152 sourceB1152 sourceC1152 difference raw19468; decide +kernel
    rw [ha]
    exact (canonical19468 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1152 + difference 3 1) (sourceB1152 + difference 1 3) sourceC1152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1115) := by
    have ha : (tripleCharges (sourceA1152 + difference 3 1) (sourceB1152 + difference 1 3) sourceC1152) = raw19469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1152 sourceB1152 sourceC1152 difference raw19469; decide +kernel
    rw [ha]
    exact (canonical19469 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1152 + difference 4 1) (sourceB1152 + difference 1 4) sourceC1152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1152 + difference 4 1) (sourceB1152 + difference 1 4) sourceC1152) = raw19470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1152 sourceB1152 sourceC1152 difference raw19470; decide +kernel
    rw [ha]
    exact (canonical19470 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1152 + difference 5 1) (sourceB1152 + difference 1 5) sourceC1152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 633) := by
    have ha : (tripleCharges (sourceA1152 + difference 5 1) (sourceB1152 + difference 1 5) sourceC1152) = raw19471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1152 sourceB1152 sourceC1152 difference raw19471; decide +kernel
    rw [ha]
    exact (canonical19471 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1152 + sourceB1152) sourceC1152) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1152 + sourceB1152) sourceC1152) = raw19472 := by
      apply Matrix.ext; unfold doubleCharges sourceA1152 sourceB1152 sourceC1152 raw19472; decide +kernel
    rw [ha]
    exact (canonical19472 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1152 sourceB1152 sourceC1152
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1152, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1153 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1153 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1153 + difference 0 0) (sourceB1153 + difference 0 0) sourceC1153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3298) := by
    have ha : (tripleCharges (sourceA1153 + difference 0 0) (sourceB1153 + difference 0 0) sourceC1153) = raw19473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1153 sourceB1153 sourceC1153 difference raw19473; decide +kernel
    rw [ha]
    exact (canonical19473 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1153 + difference 0 1) (sourceB1153 + difference 1 0) sourceC1153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1629) := by
    have ha : (tripleCharges (sourceA1153 + difference 0 1) (sourceB1153 + difference 1 0) sourceC1153) = raw19474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1153 sourceB1153 sourceC1153 difference raw19474; decide +kernel
    rw [ha]
    exact (canonical19474 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1153 + difference 0 2) (sourceB1153 + difference 2 0) sourceC1153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1615) := by
    have ha : (tripleCharges (sourceA1153 + difference 0 2) (sourceB1153 + difference 2 0) sourceC1153) = raw19475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1153 sourceB1153 sourceC1153 difference raw19475; decide +kernel
    rw [ha]
    exact (canonical19475 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1153 + difference 0 3) (sourceB1153 + difference 3 0) sourceC1153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1615) := by
    have ha : (tripleCharges (sourceA1153 + difference 0 3) (sourceB1153 + difference 3 0) sourceC1153) = raw19476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1153 sourceB1153 sourceC1153 difference raw19476; decide +kernel
    rw [ha]
    exact (canonical19476 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1153 + difference 0 4) (sourceB1153 + difference 4 0) sourceC1153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1153 + difference 0 4) (sourceB1153 + difference 4 0) sourceC1153) = raw19477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1153 sourceB1153 sourceC1153 difference raw19477; decide +kernel
    rw [ha]
    exact (canonical19477 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1153 + difference 0 5) (sourceB1153 + difference 5 0) sourceC1153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1620) := by
    have ha : (tripleCharges (sourceA1153 + difference 0 5) (sourceB1153 + difference 5 0) sourceC1153) = raw19478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1153 sourceB1153 sourceC1153 difference raw19478; decide +kernel
    rw [ha]
    exact (canonical19478 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1153 + sourceB1153) sourceC1153) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1153 + sourceB1153) sourceC1153) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1153 sourceB1153 sourceC1153 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1153 sourceB1153 sourceC1153
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1153, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1154 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1154 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1154 + difference 1 0) (sourceB1154 + difference 0 1) sourceC1154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1154 + difference 1 0) (sourceB1154 + difference 0 1) sourceC1154) = raw19429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1154 sourceB1154 sourceC1154 difference raw19429; decide +kernel
    rw [ha]
    exact (canonical19429 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1154 + difference 1 1) (sourceB1154 + difference 1 1) sourceC1154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3298) := by
    have ha : (tripleCharges (sourceA1154 + difference 1 1) (sourceB1154 + difference 1 1) sourceC1154) = raw19473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1154 sourceB1154 sourceC1154 difference raw19473; decide +kernel
    rw [ha]
    exact (canonical19473 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1154 + difference 1 2) (sourceB1154 + difference 2 1) sourceC1154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3298) := by
    have ha : (tripleCharges (sourceA1154 + difference 1 2) (sourceB1154 + difference 2 1) sourceC1154) = raw19479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1154 sourceB1154 sourceC1154 difference raw19479; decide +kernel
    rw [ha]
    exact (canonical19479 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1154 + difference 1 3) (sourceB1154 + difference 3 1) sourceC1154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3298) := by
    have ha : (tripleCharges (sourceA1154 + difference 1 3) (sourceB1154 + difference 3 1) sourceC1154) = raw19480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1154 sourceB1154 sourceC1154 difference raw19480; decide +kernel
    rw [ha]
    exact (canonical19480 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1154 + difference 1 4) (sourceB1154 + difference 4 1) sourceC1154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3313) := by
    have ha : (tripleCharges (sourceA1154 + difference 1 4) (sourceB1154 + difference 4 1) sourceC1154) = raw19481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1154 sourceB1154 sourceC1154 difference raw19481; decide +kernel
    rw [ha]
    exact (canonical19481 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1154 + difference 1 5) (sourceB1154 + difference 5 1) sourceC1154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1154 + difference 1 5) (sourceB1154 + difference 5 1) sourceC1154) = raw19418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1154 sourceB1154 sourceC1154 difference raw19418; decide +kernel
    rw [ha]
    exact (canonical19418 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1154 + sourceB1154) sourceC1154) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1154 + sourceB1154) sourceC1154) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1154 sourceB1154 sourceC1154 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1154 sourceB1154 sourceC1154
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1154, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1155 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1155 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1155 + difference 0 0) (sourceB1155 + difference 0 0) sourceC1155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 994) := by
    have ha : (tripleCharges (sourceA1155 + difference 0 0) (sourceB1155 + difference 0 0) sourceC1155) = raw19482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1155 sourceB1155 sourceC1155 difference raw19482; decide +kernel
    rw [ha]
    exact (canonical19482 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1155 + difference 0 1) (sourceB1155 + difference 1 0) sourceC1155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1055) := by
    have ha : (tripleCharges (sourceA1155 + difference 0 1) (sourceB1155 + difference 1 0) sourceC1155) = raw19483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1155 sourceB1155 sourceC1155 difference raw19483; decide +kernel
    rw [ha]
    exact (canonical19483 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1155 + difference 0 2) (sourceB1155 + difference 2 0) sourceC1155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 989) := by
    have ha : (tripleCharges (sourceA1155 + difference 0 2) (sourceB1155 + difference 2 0) sourceC1155) = raw19484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1155 sourceB1155 sourceC1155 difference raw19484; decide +kernel
    rw [ha]
    exact (canonical19484 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1155 + difference 0 3) (sourceB1155 + difference 3 0) sourceC1155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 989) := by
    have ha : (tripleCharges (sourceA1155 + difference 0 3) (sourceB1155 + difference 3 0) sourceC1155) = raw19485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1155 sourceB1155 sourceC1155 difference raw19485; decide +kernel
    rw [ha]
    exact (canonical19485 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1155 + difference 0 4) (sourceB1155 + difference 4 0) sourceC1155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1009) := by
    have ha : (tripleCharges (sourceA1155 + difference 0 4) (sourceB1155 + difference 4 0) sourceC1155) = raw19486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1155 sourceB1155 sourceC1155 difference raw19486; decide +kernel
    rw [ha]
    exact (canonical19486 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1155 + difference 0 5) (sourceB1155 + difference 5 0) sourceC1155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1155 + difference 0 5) (sourceB1155 + difference 5 0) sourceC1155) = raw19487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1155 sourceB1155 sourceC1155 difference raw19487; decide +kernel
    rw [ha]
    exact (canonical19487 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1155 + sourceB1155) sourceC1155) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1155 + sourceB1155) sourceC1155) = raw19488 := by
      apply Matrix.ext; unfold doubleCharges sourceA1155 sourceB1155 sourceC1155 raw19488; decide +kernel
    rw [ha]
    exact (canonical19488 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1155 sourceB1155 sourceC1155
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1155, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1156 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1156 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1156 + difference 0 5) (sourceB1156 + difference 5 0) sourceC1156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1156 + difference 0 5) (sourceB1156 + difference 5 0) sourceC1156) = raw19487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1156 sourceB1156 sourceC1156 difference raw19487; decide +kernel
    rw [ha]
    exact (canonical19487 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1156 + difference 1 5) (sourceB1156 + difference 5 1) sourceC1156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA1156 + difference 1 5) (sourceB1156 + difference 5 1) sourceC1156) = raw19489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1156 sourceB1156 sourceC1156 difference raw19489; decide +kernel
    rw [ha]
    exact (canonical19489 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1156 + difference 2 5) (sourceB1156 + difference 5 2) sourceC1156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1179) := by
    have ha : (tripleCharges (sourceA1156 + difference 2 5) (sourceB1156 + difference 5 2) sourceC1156) = raw19490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1156 sourceB1156 sourceC1156 difference raw19490; decide +kernel
    rw [ha]
    exact (canonical19490 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1156 + difference 3 5) (sourceB1156 + difference 5 3) sourceC1156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1179) := by
    have ha : (tripleCharges (sourceA1156 + difference 3 5) (sourceB1156 + difference 5 3) sourceC1156) = raw19491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1156 sourceB1156 sourceC1156 difference raw19491; decide +kernel
    rw [ha]
    exact (canonical19491 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1156 + difference 4 5) (sourceB1156 + difference 5 4) sourceC1156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1258) := by
    have ha : (tripleCharges (sourceA1156 + difference 4 5) (sourceB1156 + difference 5 4) sourceC1156) = raw19492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1156 sourceB1156 sourceC1156 difference raw19492; decide +kernel
    rw [ha]
    exact (canonical19492 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1156 + difference 5 5) (sourceB1156 + difference 5 5) sourceC1156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 994) := by
    have ha : (tripleCharges (sourceA1156 + difference 5 5) (sourceB1156 + difference 5 5) sourceC1156) = raw19482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1156 sourceB1156 sourceC1156 difference raw19482; decide +kernel
    rw [ha]
    exact (canonical19482 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1156 + sourceB1156) sourceC1156) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1156 + sourceB1156) sourceC1156) = raw19488 := by
      apply Matrix.ext; unfold doubleCharges sourceA1156 sourceB1156 sourceC1156 raw19488; decide +kernel
    rw [ha]
    exact (canonical19488 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1156 sourceB1156 sourceC1156
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1156, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1157 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1157 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1157 + difference 0 0) (sourceB1157 + difference 0 0) sourceC1157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 975) := by
    have ha : (tripleCharges (sourceA1157 + difference 0 0) (sourceB1157 + difference 0 0) sourceC1157) = raw19493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1157 sourceB1157 sourceC1157 difference raw19493; decide +kernel
    rw [ha]
    exact (canonical19493 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1157 + difference 0 1) (sourceB1157 + difference 1 0) sourceC1157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1019) := by
    have ha : (tripleCharges (sourceA1157 + difference 0 1) (sourceB1157 + difference 1 0) sourceC1157) = raw19494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1157 sourceB1157 sourceC1157 difference raw19494; decide +kernel
    rw [ha]
    exact (canonical19494 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1157 + difference 0 2) (sourceB1157 + difference 2 0) sourceC1157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 971) := by
    have ha : (tripleCharges (sourceA1157 + difference 0 2) (sourceB1157 + difference 2 0) sourceC1157) = raw19495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1157 sourceB1157 sourceC1157 difference raw19495; decide +kernel
    rw [ha]
    exact (canonical19495 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1157 + difference 0 3) (sourceB1157 + difference 3 0) sourceC1157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1157 + difference 0 3) (sourceB1157 + difference 3 0) sourceC1157) = raw19496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1157 sourceB1157 sourceC1157 difference raw19496; decide +kernel
    rw [ha]
    exact (canonical19496 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1157 + difference 0 4) (sourceB1157 + difference 4 0) sourceC1157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1157 + difference 0 4) (sourceB1157 + difference 4 0) sourceC1157) = raw19497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1157 sourceB1157 sourceC1157 difference raw19497; decide +kernel
    rw [ha]
    exact (canonical19497 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1157 + difference 0 5) (sourceB1157 + difference 5 0) sourceC1157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1157 + difference 0 5) (sourceB1157 + difference 5 0) sourceC1157) = raw19498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1157 sourceB1157 sourceC1157 difference raw19498; decide +kernel
    rw [ha]
    exact (canonical19498 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1157 + sourceB1157) sourceC1157) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1157 + sourceB1157) sourceC1157) = raw19499 := by
      apply Matrix.ext; unfold doubleCharges sourceA1157 sourceB1157 sourceC1157 raw19499; decide +kernel
    rw [ha]
    exact (canonical19499 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1157 sourceB1157 sourceC1157
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1157, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1158 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1158 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1158 + difference 0 5) (sourceB1158 + difference 5 0) sourceC1158) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1158 + difference 0 5) (sourceB1158 + difference 5 0) sourceC1158) = raw19498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1158 sourceB1158 sourceC1158 difference raw19498; decide +kernel
    rw [ha]
    exact (canonical19498 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1158 + difference 1 5) (sourceB1158 + difference 5 1) sourceC1158) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1202) := by
    have ha : (tripleCharges (sourceA1158 + difference 1 5) (sourceB1158 + difference 5 1) sourceC1158) = raw19500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1158 sourceB1158 sourceC1158 difference raw19500; decide +kernel
    rw [ha]
    exact (canonical19500 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1158 + difference 2 5) (sourceB1158 + difference 5 2) sourceC1158) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1194) := by
    have ha : (tripleCharges (sourceA1158 + difference 2 5) (sourceB1158 + difference 5 2) sourceC1158) = raw19501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1158 sourceB1158 sourceC1158 difference raw19501; decide +kernel
    rw [ha]
    exact (canonical19501 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1158 + difference 3 5) (sourceB1158 + difference 5 3) sourceC1158) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1211) := by
    have ha : (tripleCharges (sourceA1158 + difference 3 5) (sourceB1158 + difference 5 3) sourceC1158) = raw19502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1158 sourceB1158 sourceC1158 difference raw19502; decide +kernel
    rw [ha]
    exact (canonical19502 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1158 + difference 4 5) (sourceB1158 + difference 5 4) sourceC1158) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1211) := by
    have ha : (tripleCharges (sourceA1158 + difference 4 5) (sourceB1158 + difference 5 4) sourceC1158) = raw19503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1158 sourceB1158 sourceC1158 difference raw19503; decide +kernel
    rw [ha]
    exact (canonical19503 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1158 + difference 5 5) (sourceB1158 + difference 5 5) sourceC1158) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 975) := by
    have ha : (tripleCharges (sourceA1158 + difference 5 5) (sourceB1158 + difference 5 5) sourceC1158) = raw19493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1158 sourceB1158 sourceC1158 difference raw19493; decide +kernel
    rw [ha]
    exact (canonical19493 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1158 + sourceB1158) sourceC1158) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1158 + sourceB1158) sourceC1158) = raw19499 := by
      apply Matrix.ext; unfold doubleCharges sourceA1158 sourceB1158 sourceC1158 raw19499; decide +kernel
    rw [ha]
    exact (canonical19499 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1158 sourceB1158 sourceC1158
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1158, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck993 : Integer.Sparse.reindex keyMap MixedData.row993 = numericRow993 := by decide +kernel

theorem numericCheck993 (x : Master → ℝ) : Integer.Sparse.eval numericRow993 x =
    (40 : ℝ) * reducedSource993 x := by
  norm_num [numericRow993, reducedSource993, Integer.Sparse.eval, Sparse.eval, nodeValue4090, nodeValue4091, nodeValue4096]
  ring

theorem reindexCheck994 : Integer.Sparse.reindex keyMap MixedData.row994 = numericRow994 := by decide +kernel

theorem numericCheck994 (x : Master → ℝ) : Integer.Sparse.eval numericRow994 x =
    (1 : ℝ) * reducedSource994 x := by
  norm_num [numericRow994, reducedSource994, Integer.Sparse.eval, Sparse.eval, nodeValue617, nodeValue936, nodeValue1064, nodeValue1091, nodeValue4084]

theorem reindexCheck995 : Integer.Sparse.reindex keyMap MixedData.row995 = numericRow995 := by decide +kernel

theorem numericCheck995 (x : Master → ℝ) : Integer.Sparse.eval numericRow995 x =
    (1 : ℝ) * reducedSource995 x := by
  norm_num [numericRow995, reducedSource995, Integer.Sparse.eval, Sparse.eval, nodeValue862, nodeValue1629, nodeValue1752, nodeValue1757, nodeValue4072]

theorem reindexCheck996 : Integer.Sparse.reindex keyMap MixedData.row996 = numericRow996 := by decide +kernel

theorem numericCheck996 (x : Master → ℝ) : Integer.Sparse.eval numericRow996 x =
    (1 : ℝ) * reducedSource996 x := by
  norm_num [numericRow996, reducedSource996, Integer.Sparse.eval, Sparse.eval, nodeValue1749, nodeValue1752, nodeValue1757, nodeValue4072]

theorem reindexCheck997 : Integer.Sparse.reindex keyMap MixedData.row997 = numericRow997 := by decide +kernel

theorem numericCheck997 (x : Master → ℝ) : Integer.Sparse.eval numericRow997 x =
    (1 : ℝ) * reducedSource997 x := by
  norm_num [numericRow997, reducedSource997, Integer.Sparse.eval, Sparse.eval, nodeValue587, nodeValue911, nodeValue951, nodeValue1027, nodeValue1046, nodeValue4083]

theorem reindexCheck998 : Integer.Sparse.reindex keyMap MixedData.row998 = numericRow998 := by decide +kernel

theorem numericCheck998 (x : Master → ℝ) : Integer.Sparse.eval numericRow998 x =
    (1 : ℝ) * reducedSource998 x := by
  norm_num [numericRow998, reducedSource998, Integer.Sparse.eval, Sparse.eval, nodeValue849, nodeValue1615, nodeValue1749, nodeValue1752, nodeValue4072]

theorem reindexCheck999 : Integer.Sparse.reindex keyMap MixedData.row999 = numericRow999 := by decide +kernel

theorem numericCheck999 (x : Master → ℝ) : Integer.Sparse.eval numericRow999 x =
    (1 : ℝ) * reducedSource999 x := by
  norm_num [numericRow999, reducedSource999, Integer.Sparse.eval, Sparse.eval, nodeValue794, nodeValue797, nodeValue813, nodeValue828, nodeValue1716, nodeValue4069]

theorem reindexCheck1000 : Integer.Sparse.reindex keyMap MixedData.row1000 = numericRow1000 := by decide +kernel

theorem numericCheck1000 (x : Master → ℝ) : Integer.Sparse.eval numericRow1000 x =
    (1 : ℝ) * reducedSource1000 x := by
  norm_num [numericRow1000, reducedSource1000, Integer.Sparse.eval, Sparse.eval, nodeValue633, nodeValue1115, nodeValue1140, nodeValue1221, nodeValue1242, nodeValue4092]

theorem reindexCheck1001 : Integer.Sparse.reindex keyMap MixedData.row1001 = numericRow1001 := by decide +kernel

theorem numericCheck1001 (x : Master → ℝ) : Integer.Sparse.eval numericRow1001 x =
    (1 : ℝ) * reducedSource1001 x := by
  norm_num [numericRow1001, reducedSource1001, Integer.Sparse.eval, Sparse.eval, nodeValue1615, nodeValue1620, nodeValue1629, nodeValue1752, nodeValue3298, nodeValue4072]

theorem reindexCheck1002 : Integer.Sparse.reindex keyMap MixedData.row1002 = numericRow1002 := by decide +kernel

theorem numericCheck1002 (x : Master → ℝ) : Integer.Sparse.eval numericRow1002 x =
    (1 : ℝ) * reducedSource1002 x := by
  norm_num [numericRow1002, reducedSource1002, Integer.Sparse.eval, Sparse.eval, nodeValue1752, nodeValue3298, nodeValue3313, nodeValue4072]

theorem reindexCheck1003 : Integer.Sparse.reindex keyMap MixedData.row1003 = numericRow1003 := by decide +kernel

theorem numericCheck1003 (x : Master → ℝ) : Integer.Sparse.eval numericRow1003 x =
    (1 : ℝ) * reducedSource1003 x := by
  norm_num [numericRow1003, reducedSource1003, Integer.Sparse.eval, Sparse.eval, nodeValue989, nodeValue994, nodeValue1009, nodeValue1055, nodeValue2218, nodeValue4082]

theorem reindexCheck1004 : Integer.Sparse.reindex keyMap MixedData.row1004 = numericRow1004 := by decide +kernel

theorem numericCheck1004 (x : Master → ℝ) : Integer.Sparse.eval numericRow1004 x =
    (1 : ℝ) * reducedSource1004 x := by
  norm_num [numericRow1004, reducedSource1004, Integer.Sparse.eval, Sparse.eval, nodeValue994, nodeValue1179, nodeValue1190, nodeValue1258, nodeValue2218, nodeValue4082]

theorem reindexCheck1005 : Integer.Sparse.reindex keyMap MixedData.row1005 = numericRow1005 := by decide +kernel

theorem numericCheck1005 (x : Master → ℝ) : Integer.Sparse.eval numericRow1005 x =
    (1 : ℝ) * reducedSource1005 x := by
  norm_num [numericRow1005, reducedSource1005, Integer.Sparse.eval, Sparse.eval, nodeValue971, nodeValue975, nodeValue982, nodeValue1019, nodeValue2193, nodeValue4080]

theorem reindexCheck1006 : Integer.Sparse.reindex keyMap MixedData.row1006 = numericRow1006 := by decide +kernel

theorem numericCheck1006 (x : Master → ℝ) : Integer.Sparse.eval numericRow1006 x =
    (1 : ℝ) * reducedSource1006 x := by
  norm_num [numericRow1006, reducedSource1006, Integer.Sparse.eval, Sparse.eval, nodeValue975, nodeValue1194, nodeValue1202, nodeValue1211, nodeValue2193, nodeValue4080]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero993 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource993 (mixedVector B) = 0 := by
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  have h4096 : mixedVector B (Sum.inr 4096) = Sparse.eval nodeValue4096 (mixedVector B) := by
    change mixedMoment B node4096 node4096Labels = _
    exact sound4096 B hB hF
  simpa only [sourceForm1141, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4090, h4091, h4096, reducedSource993] using sourceEq1141 B hB

theorem rowSound993 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row993 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck993, numericCheck993, reducedZero993 B hB hF, mul_zero]

theorem reducedZero994 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource994 (mixedVector B) = 0 := by
  have h617 : mixedVector B (Sum.inr 617) = Sparse.eval nodeValue617 (mixedVector B) := by
    change mixedMoment B node617 node617Labels = _
    exact sound617 B hB hF
  have h936 : mixedVector B (Sum.inr 936) = Sparse.eval nodeValue936 (mixedVector B) := by
    change mixedMoment B node936 node936Labels = _
    exact sound936 B hB hF
  have h1064 : mixedVector B (Sum.inr 1064) = Sparse.eval nodeValue1064 (mixedVector B) := by
    change mixedMoment B node1064 node1064Labels = _
    exact sound1064 B hB hF
  have h1091 : mixedVector B (Sum.inr 1091) = Sparse.eval nodeValue1091 (mixedVector B) := by
    change mixedMoment B node1091 node1091Labels = _
    exact sound1091 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1142, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h617, h936, h1064, h1091, h4084, reducedSource994] using sourceEq1142 B hB

theorem rowSound994 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row994 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck994, numericCheck994, reducedZero994 B hB hF, mul_zero]

theorem reducedZero995 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource995 (mixedVector B) = 0 := by
  have h862 : mixedVector B (Sum.inr 862) = Sparse.eval nodeValue862 (mixedVector B) := by
    change mixedMoment B node862 node862Labels = _
    exact sound862 B hB hF
  have h1629 : mixedVector B (Sum.inr 1629) = Sparse.eval nodeValue1629 (mixedVector B) := by
    change mixedMoment B node1629 node1629Labels = _
    exact sound1629 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h1757 : mixedVector B (Sum.inr 1757) = Sparse.eval nodeValue1757 (mixedVector B) := by
    change mixedMoment B node1757 node1757Labels = _
    exact sound1757 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  simpa only [sourceForm1143, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h862, h1629, h1752, h1757, h4072, reducedSource995] using sourceEq1143 B hB

theorem rowSound995 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row995 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck995, numericCheck995, reducedZero995 B hB hF, mul_zero]

theorem reducedZero996 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource996 (mixedVector B) = 0 := by
  have h1749 : mixedVector B (Sum.inr 1749) = Sparse.eval nodeValue1749 (mixedVector B) := by
    change mixedMoment B node1749 node1749Labels = _
    exact sound1749 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h1757 : mixedVector B (Sum.inr 1757) = Sparse.eval nodeValue1757 (mixedVector B) := by
    change mixedMoment B node1757 node1757Labels = _
    exact sound1757 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  simpa only [sourceForm1145, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1749, h1752, h1757, h4072, reducedSource996] using sourceEq1145 B hB

theorem rowSound996 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row996 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck996, numericCheck996, reducedZero996 B hB hF, mul_zero]

theorem reducedZero997 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource997 (mixedVector B) = 0 := by
  have h587 : mixedVector B (Sum.inr 587) = Sparse.eval nodeValue587 (mixedVector B) := by
    change mixedMoment B node587 node587Labels = _
    exact sound587 B hB hF
  have h911 : mixedVector B (Sum.inr 911) = Sparse.eval nodeValue911 (mixedVector B) := by
    change mixedMoment B node911 node911Labels = _
    exact sound911 B hB hF
  have h951 : mixedVector B (Sum.inr 951) = Sparse.eval nodeValue951 (mixedVector B) := by
    change mixedMoment B node951 node951Labels = _
    exact sound951 B hB hF
  have h1027 : mixedVector B (Sum.inr 1027) = Sparse.eval nodeValue1027 (mixedVector B) := by
    change mixedMoment B node1027 node1027Labels = _
    exact sound1027 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1147, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h587, h911, h951, h1027, h1046, h4083, reducedSource997] using sourceEq1147 B hB

theorem rowSound997 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row997 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck997, numericCheck997, reducedZero997 B hB hF, mul_zero]

theorem reducedZero998 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource998 (mixedVector B) = 0 := by
  have h849 : mixedVector B (Sum.inr 849) = Sparse.eval nodeValue849 (mixedVector B) := by
    change mixedMoment B node849 node849Labels = _
    exact sound849 B hB hF
  have h1615 : mixedVector B (Sum.inr 1615) = Sparse.eval nodeValue1615 (mixedVector B) := by
    change mixedMoment B node1615 node1615Labels = _
    exact sound1615 B hB hF
  have h1749 : mixedVector B (Sum.inr 1749) = Sparse.eval nodeValue1749 (mixedVector B) := by
    change mixedMoment B node1749 node1749Labels = _
    exact sound1749 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  simpa only [sourceForm1148, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h849, h1615, h1749, h1752, h4072, reducedSource998] using sourceEq1148 B hB

theorem rowSound998 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row998 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck998, numericCheck998, reducedZero998 B hB hF, mul_zero]

theorem reducedZero999 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource999 (mixedVector B) = 0 := by
  have h794 : mixedVector B (Sum.inr 794) = Sparse.eval nodeValue794 (mixedVector B) := by
    change mixedMoment B node794 node794Labels = _
    exact sound794 B hB hF
  have h797 : mixedVector B (Sum.inr 797) = Sparse.eval nodeValue797 (mixedVector B) := by
    change mixedMoment B node797 node797Labels = _
    exact sound797 B hB hF
  have h813 : mixedVector B (Sum.inr 813) = Sparse.eval nodeValue813 (mixedVector B) := by
    change mixedMoment B node813 node813Labels = _
    exact sound813 B hB hF
  have h828 : mixedVector B (Sum.inr 828) = Sparse.eval nodeValue828 (mixedVector B) := by
    change mixedMoment B node828 node828Labels = _
    exact sound828 B hB hF
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1150, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h794, h797, h813, h828, h1716, h4069, reducedSource999] using sourceEq1150 B hB

theorem rowSound999 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row999 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck999, numericCheck999, reducedZero999 B hB hF, mul_zero]

theorem reducedZero1000 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1000 (mixedVector B) = 0 := by
  have h633 : mixedVector B (Sum.inr 633) = Sparse.eval nodeValue633 (mixedVector B) := by
    change mixedMoment B node633 node633Labels = _
    exact sound633 B hB hF
  have h1115 : mixedVector B (Sum.inr 1115) = Sparse.eval nodeValue1115 (mixedVector B) := by
    change mixedMoment B node1115 node1115Labels = _
    exact sound1115 B hB hF
  have h1140 : mixedVector B (Sum.inr 1140) = Sparse.eval nodeValue1140 (mixedVector B) := by
    change mixedMoment B node1140 node1140Labels = _
    exact sound1140 B hB hF
  have h1221 : mixedVector B (Sum.inr 1221) = Sparse.eval nodeValue1221 (mixedVector B) := by
    change mixedMoment B node1221 node1221Labels = _
    exact sound1221 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1152, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h633, h1115, h1140, h1221, h1242, h4092, reducedSource1000] using sourceEq1152 B hB

theorem rowSound1000 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1000 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1000, numericCheck1000, reducedZero1000 B hB hF, mul_zero]

theorem reducedZero1001 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1001 (mixedVector B) = 0 := by
  have h1615 : mixedVector B (Sum.inr 1615) = Sparse.eval nodeValue1615 (mixedVector B) := by
    change mixedMoment B node1615 node1615Labels = _
    exact sound1615 B hB hF
  have h1620 : mixedVector B (Sum.inr 1620) = Sparse.eval nodeValue1620 (mixedVector B) := by
    change mixedMoment B node1620 node1620Labels = _
    exact sound1620 B hB hF
  have h1629 : mixedVector B (Sum.inr 1629) = Sparse.eval nodeValue1629 (mixedVector B) := by
    change mixedMoment B node1629 node1629Labels = _
    exact sound1629 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h3298 : mixedVector B (Sum.inr 3298) = Sparse.eval nodeValue3298 (mixedVector B) := by
    change mixedMoment B node3298 node3298Labels = _
    exact sound3298 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  simpa only [sourceForm1153, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1615, h1620, h1629, h1752, h3298, h4072, reducedSource1001] using sourceEq1153 B hB

theorem rowSound1001 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1001 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1001, numericCheck1001, reducedZero1001 B hB hF, mul_zero]

theorem reducedZero1002 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1002 (mixedVector B) = 0 := by
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h3298 : mixedVector B (Sum.inr 3298) = Sparse.eval nodeValue3298 (mixedVector B) := by
    change mixedMoment B node3298 node3298Labels = _
    exact sound3298 B hB hF
  have h3313 : mixedVector B (Sum.inr 3313) = Sparse.eval nodeValue3313 (mixedVector B) := by
    change mixedMoment B node3313 node3313Labels = _
    exact sound3313 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  simpa only [sourceForm1154, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1752, h3298, h3313, h4072, reducedSource1002] using sourceEq1154 B hB

theorem rowSound1002 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1002 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1002, numericCheck1002, reducedZero1002 B hB hF, mul_zero]

theorem reducedZero1003 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1003 (mixedVector B) = 0 := by
  have h989 : mixedVector B (Sum.inr 989) = Sparse.eval nodeValue989 (mixedVector B) := by
    change mixedMoment B node989 node989Labels = _
    exact sound989 B hB hF
  have h994 : mixedVector B (Sum.inr 994) = Sparse.eval nodeValue994 (mixedVector B) := by
    change mixedMoment B node994 node994Labels = _
    exact sound994 B hB hF
  have h1009 : mixedVector B (Sum.inr 1009) = Sparse.eval nodeValue1009 (mixedVector B) := by
    change mixedMoment B node1009 node1009Labels = _
    exact sound1009 B hB hF
  have h1055 : mixedVector B (Sum.inr 1055) = Sparse.eval nodeValue1055 (mixedVector B) := by
    change mixedMoment B node1055 node1055Labels = _
    exact sound1055 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1155, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h989, h994, h1009, h1055, h2218, h4082, reducedSource1003] using sourceEq1155 B hB

theorem rowSound1003 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1003 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1003, numericCheck1003, reducedZero1003 B hB hF, mul_zero]

theorem reducedZero1004 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1004 (mixedVector B) = 0 := by
  have h994 : mixedVector B (Sum.inr 994) = Sparse.eval nodeValue994 (mixedVector B) := by
    change mixedMoment B node994 node994Labels = _
    exact sound994 B hB hF
  have h1179 : mixedVector B (Sum.inr 1179) = Sparse.eval nodeValue1179 (mixedVector B) := by
    change mixedMoment B node1179 node1179Labels = _
    exact sound1179 B hB hF
  have h1190 : mixedVector B (Sum.inr 1190) = Sparse.eval nodeValue1190 (mixedVector B) := by
    change mixedMoment B node1190 node1190Labels = _
    exact sound1190 B hB hF
  have h1258 : mixedVector B (Sum.inr 1258) = Sparse.eval nodeValue1258 (mixedVector B) := by
    change mixedMoment B node1258 node1258Labels = _
    exact sound1258 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1156, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h994, h1179, h1190, h1258, h2218, h4082, reducedSource1004] using sourceEq1156 B hB

theorem rowSound1004 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1004 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1004, numericCheck1004, reducedZero1004 B hB hF, mul_zero]

theorem reducedZero1005 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1005 (mixedVector B) = 0 := by
  have h971 : mixedVector B (Sum.inr 971) = Sparse.eval nodeValue971 (mixedVector B) := by
    change mixedMoment B node971 node971Labels = _
    exact sound971 B hB hF
  have h975 : mixedVector B (Sum.inr 975) = Sparse.eval nodeValue975 (mixedVector B) := by
    change mixedMoment B node975 node975Labels = _
    exact sound975 B hB hF
  have h982 : mixedVector B (Sum.inr 982) = Sparse.eval nodeValue982 (mixedVector B) := by
    change mixedMoment B node982 node982Labels = _
    exact sound982 B hB hF
  have h1019 : mixedVector B (Sum.inr 1019) = Sparse.eval nodeValue1019 (mixedVector B) := by
    change mixedMoment B node1019 node1019Labels = _
    exact sound1019 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1157, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h971, h975, h982, h1019, h2193, h4080, reducedSource1005] using sourceEq1157 B hB

theorem rowSound1005 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1005 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1005, numericCheck1005, reducedZero1005 B hB hF, mul_zero]

theorem reducedZero1006 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1006 (mixedVector B) = 0 := by
  have h975 : mixedVector B (Sum.inr 975) = Sparse.eval nodeValue975 (mixedVector B) := by
    change mixedMoment B node975 node975Labels = _
    exact sound975 B hB hF
  have h1194 : mixedVector B (Sum.inr 1194) = Sparse.eval nodeValue1194 (mixedVector B) := by
    change mixedMoment B node1194 node1194Labels = _
    exact sound1194 B hB hF
  have h1202 : mixedVector B (Sum.inr 1202) = Sparse.eval nodeValue1202 (mixedVector B) := by
    change mixedMoment B node1202 node1202Labels = _
    exact sound1202 B hB hF
  have h1211 : mixedVector B (Sum.inr 1211) = Sparse.eval nodeValue1211 (mixedVector B) := by
    change mixedMoment B node1211 node1211Labels = _
    exact sound1211 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1158, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h975, h1194, h1202, h1211, h2193, h4080, reducedSource1006] using sourceEq1158 B hB

theorem rowSound1006 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1006 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1006, numericCheck1006, reducedZero1006 B hB hF, mul_zero]

theorem sourceRowsAt992 : MixedData.sourceRows (992 : Fin 2425) =
    MixedData.row992 := by decide +kernel

theorem sourceRowsAt993 : MixedData.sourceRows (993 : Fin 2425) =
    MixedData.row993 := by decide +kernel

theorem sourceRowsAt994 : MixedData.sourceRows (994 : Fin 2425) =
    MixedData.row994 := by decide +kernel

theorem sourceRowsAt995 : MixedData.sourceRows (995 : Fin 2425) =
    MixedData.row995 := by decide +kernel

theorem sourceRowsAt996 : MixedData.sourceRows (996 : Fin 2425) =
    MixedData.row996 := by decide +kernel

theorem sourceRowsAt997 : MixedData.sourceRows (997 : Fin 2425) =
    MixedData.row997 := by decide +kernel

theorem sourceRowsAt998 : MixedData.sourceRows (998 : Fin 2425) =
    MixedData.row998 := by decide +kernel

theorem sourceRowsAt999 : MixedData.sourceRows (999 : Fin 2425) =
    MixedData.row999 := by decide +kernel

theorem sourceRowsAt1000 : MixedData.sourceRows (1000 : Fin 2425) =
    MixedData.row1000 := by decide +kernel

theorem sourceRowsAt1001 : MixedData.sourceRows (1001 : Fin 2425) =
    MixedData.row1001 := by decide +kernel

theorem sourceRowsAt1002 : MixedData.sourceRows (1002 : Fin 2425) =
    MixedData.row1002 := by decide +kernel

theorem sourceRowsAt1003 : MixedData.sourceRows (1003 : Fin 2425) =
    MixedData.row1003 := by decide +kernel

theorem sourceRowsAt1004 : MixedData.sourceRows (1004 : Fin 2425) =
    MixedData.row1004 := by decide +kernel

theorem sourceRowsAt1005 : MixedData.sourceRows (1005 : Fin 2425) =
    MixedData.row1005 := by decide +kernel

theorem sourceRowsAt1006 : MixedData.sourceRows (1006 : Fin 2425) =
    MixedData.row1006 := by decide +kernel

theorem sourceRowsAt1007 : MixedData.sourceRows (1007 : Fin 2425) =
    MixedData.row1007 := by decide +kernel

theorem chunkSound62_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 62) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 992 ∨ k.val = 993 ∨ k.val = 994 ∨ k.val = 995 ∨ k.val = 996 ∨ k.val = 997 ∨ k.val = 998 ∨ k.val = 999 ∨ k.val = 1000 ∨ k.val = 1001 ∨ k.val = 1002 ∨ k.val = 1003 ∨ k.val = 1004 ∨ k.val = 1005 ∨ k.val = 1006 ∨ k.val = 1007 := by omega
  rcases heq with h992 | h993 | h994 | h995 | h996 | h997 | h998 | h999 | h1000 | h1001 | h1002 | h1003 | h1004 | h1005 | h1006 | h1007
  · have he : k = (992 : Fin 2425) := Fin.ext h992
    subst k
    rw [sourceRowsAt992]
    exact rowSound992_e B hB hF
  · have he : k = (993 : Fin 2425) := Fin.ext h993
    subst k
    rw [sourceRowsAt993]
    exact rowSound993 B hB hF
  · have he : k = (994 : Fin 2425) := Fin.ext h994
    subst k
    rw [sourceRowsAt994]
    exact rowSound994 B hB hF
  · have he : k = (995 : Fin 2425) := Fin.ext h995
    subst k
    rw [sourceRowsAt995]
    exact rowSound995 B hB hF
  · have he : k = (996 : Fin 2425) := Fin.ext h996
    subst k
    rw [sourceRowsAt996]
    exact rowSound996 B hB hF
  · have he : k = (997 : Fin 2425) := Fin.ext h997
    subst k
    rw [sourceRowsAt997]
    exact rowSound997 B hB hF
  · have he : k = (998 : Fin 2425) := Fin.ext h998
    subst k
    rw [sourceRowsAt998]
    exact rowSound998 B hB hF
  · have he : k = (999 : Fin 2425) := Fin.ext h999
    subst k
    rw [sourceRowsAt999]
    exact rowSound999 B hB hF
  · have he : k = (1000 : Fin 2425) := Fin.ext h1000
    subst k
    rw [sourceRowsAt1000]
    exact rowSound1000 B hB hF
  · have he : k = (1001 : Fin 2425) := Fin.ext h1001
    subst k
    rw [sourceRowsAt1001]
    exact rowSound1001 B hB hF
  · have he : k = (1002 : Fin 2425) := Fin.ext h1002
    subst k
    rw [sourceRowsAt1002]
    exact rowSound1002 B hB hF
  · have he : k = (1003 : Fin 2425) := Fin.ext h1003
    subst k
    rw [sourceRowsAt1003]
    exact rowSound1003 B hB hF
  · have he : k = (1004 : Fin 2425) := Fin.ext h1004
    subst k
    rw [sourceRowsAt1004]
    exact rowSound1004 B hB hF
  · have he : k = (1005 : Fin 2425) := Fin.ext h1005
    subst k
    rw [sourceRowsAt1005]
    exact rowSound1005 B hB hF
  · have he : k = (1006 : Fin 2425) := Fin.ext h1006
    subst k
    rw [sourceRowsAt1006]
    exact rowSound1006 B hB hF
  · have he : k = (1007 : Fin 2425) := Fin.ext h1007
    subst k
    rw [sourceRowsAt1007]
    exact rowSound1007_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e_oai
