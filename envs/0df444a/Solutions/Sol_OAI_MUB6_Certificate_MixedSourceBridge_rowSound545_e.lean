-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T01:51:44.300422+00:00
-- url     : https://prove2.me/submissions/2f3ad5ce-b6ce-4386-acde-57f605bab475

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
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

theorem canonical1665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1665 raw1665Labels = mixedMoment B node4746 node4746Labels := by
  calc
    mixedMoment B raw1665 raw1665Labels = mixedMoment B raw1665step0 raw1665step0Labels := by
      have ha : raw1665step0 = (fun i j => raw1665 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1665step0 raw1665; decide +kernel
      have hl : raw1665step0Labels = raw1665Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1665 raw1665Labels permutation152 permutation4
    mixedMoment B raw1665step0 raw1665step0Labels = mixedMoment B raw1665step1 raw1665step1Labels := by
      have ha : raw1665step1 = raw1665step0 := by apply Matrix.ext; unfold raw1665step1 raw1665step0; decide +kernel
      have hl : raw1665step0Labels = labelEmbedding7 ∘ raw1665step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1665step0 raw1665step0Labels raw1665step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4746 node4746Labels := by rfl

theorem canonical1666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1666 raw1666Labels = mixedMoment B node1925 node1925Labels := by
  calc
    mixedMoment B raw1666 raw1666Labels = mixedMoment B raw1666step0 raw1666step0Labels := by
      have ha : raw1666step0 = (fun i j => raw1666 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1666step0 raw1666; decide +kernel
      have hl : raw1666step0Labels = raw1666Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1666 raw1666Labels permutation152 permutation4
    _ = mixedMoment B node1925 node1925Labels := by rfl

theorem canonical1667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1667 raw1667Labels = mixedMoment B node1925 node1925Labels := by
  calc
    mixedMoment B raw1667 raw1667Labels = mixedMoment B raw1667step0 raw1667step0Labels := by
      have ha : raw1667step0 = (fun i j => raw1667 (permutation173 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1667step0 raw1667; decide +kernel
      have hl : raw1667step0Labels = raw1667Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1667 raw1667Labels permutation173 permutation6
    mixedMoment B raw1667step0 raw1667step0Labels = mixedMoment B raw1667step1 raw1667step1Labels := by
      have ha : raw1667step1 = -raw1667step0 := by apply Matrix.ext; change ∀ i j, raw1667step1 i j = -(raw1667step0 i j); unfold raw1667step1 raw1667step0; decide +kernel
      have hl : raw1667step1Labels = raw1667step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1667step1 raw1667step1Labels = mixedMoment B raw1667step2 raw1667step2Labels := by
      have ha : raw1667step2 = raw1667step1 := by apply Matrix.ext; unfold raw1667step2 raw1667step1; decide +kernel
      have hl : raw1667step1Labels = labelEmbedding1 ∘ raw1667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1667step1 raw1667step1Labels raw1667step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1925 node1925Labels := by rfl

theorem canonical1668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1668 raw1668Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw1668 raw1668Labels = mixedMoment B raw1668step0 raw1668step0Labels := by
      have ha : raw1668step0 = (fun i j => raw1668 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1668step0 raw1668; decide +kernel
      have hl : raw1668step0Labels = raw1668Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1668 raw1668Labels permutation32 permutation4
    mixedMoment B raw1668step0 raw1668step0Labels = mixedMoment B raw1668step1 raw1668step1Labels := by
      have ha : raw1668step1 = raw1668step0 := by apply Matrix.ext; unfold raw1668step1 raw1668step0; decide +kernel
      have hl : raw1668step0Labels = labelEmbedding7 ∘ raw1668step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1668step0 raw1668step0Labels raw1668step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

theorem canonical1669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1669 raw1669Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw1669 raw1669Labels = mixedMoment B raw1669step0 raw1669step0Labels := by
      have ha : raw1669step0 = (fun i j => raw1669 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1669step0 raw1669; decide +kernel
      have hl : raw1669step0Labels = raw1669Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1669 raw1669Labels permutation32 permutation4
    _ = mixedMoment B node1926 node1926Labels := by rfl

theorem canonical1670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1670 raw1670Labels = mixedMoment B node1948 node1948Labels := by
  calc
    mixedMoment B raw1670 raw1670Labels = mixedMoment B raw1670step0 raw1670step0Labels := by
      have ha : raw1670step0 = (fun i j => raw1670 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1670step0 raw1670; decide +kernel
      have hl : raw1670step0Labels = raw1670Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1670 raw1670Labels permutation35 permutation6
    mixedMoment B raw1670step0 raw1670step0Labels = mixedMoment B raw1670step1 raw1670step1Labels := by
      have ha : raw1670step1 = -raw1670step0 := by apply Matrix.ext; change ∀ i j, raw1670step1 i j = -(raw1670step0 i j); unfold raw1670step1 raw1670step0; decide +kernel
      have hl : raw1670step1Labels = raw1670step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1670step1 raw1670step1Labels = mixedMoment B raw1670step2 raw1670step2Labels := by
      have ha : raw1670step2 = raw1670step1 := by apply Matrix.ext; unfold raw1670step2 raw1670step1; decide +kernel
      have hl : raw1670step1Labels = labelEmbedding1 ∘ raw1670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1670step1 raw1670step1Labels raw1670step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1948 node1948Labels := by rfl

theorem canonical1671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1671 raw1671Labels = mixedMoment B node4749 node4749Labels := by
  calc
    mixedMoment B raw1671 raw1671Labels = mixedMoment B raw1671step0 raw1671step0Labels := by
      have ha : raw1671step0 = (fun i j => raw1671 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1671step0 raw1671; decide +kernel
      have hl : raw1671step0Labels = raw1671Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1671 raw1671Labels permutation32 permutation4
    mixedMoment B raw1671step0 raw1671step0Labels = mixedMoment B raw1671step1 raw1671step1Labels := by
      have ha : raw1671step1 = raw1671step0 := by apply Matrix.ext; unfold raw1671step1 raw1671step0; decide +kernel
      have hl : raw1671step0Labels = labelEmbedding7 ∘ raw1671step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1671step0 raw1671step0Labels raw1671step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4749 node4749Labels := by rfl

theorem canonical1672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1672 raw1672Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw1672 raw1672Labels = mixedMoment B raw1672step0 raw1672step0Labels := by
      have ha : raw1672step0 = (fun i j => raw1672 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1672step0 raw1672; decide +kernel
      have hl : raw1672step0Labels = raw1672Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1672 raw1672Labels permutation32 permutation4
    _ = mixedMoment B node1928 node1928Labels := by rfl

theorem canonical1673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1673 raw1673Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw1673 raw1673Labels = mixedMoment B raw1673step0 raw1673step0Labels := by
      have ha : raw1673step0 = (fun i j => raw1673 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1673step0 raw1673; decide +kernel
      have hl : raw1673step0Labels = raw1673Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1673 raw1673Labels permutation34 permutation6
    mixedMoment B raw1673step0 raw1673step0Labels = mixedMoment B raw1673step1 raw1673step1Labels := by
      have ha : raw1673step1 = -raw1673step0 := by apply Matrix.ext; change ∀ i j, raw1673step1 i j = -(raw1673step0 i j); unfold raw1673step1 raw1673step0; decide +kernel
      have hl : raw1673step1Labels = raw1673step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1673step1 raw1673step1Labels = mixedMoment B raw1673step2 raw1673step2Labels := by
      have ha : raw1673step2 = raw1673step1 := by apply Matrix.ext; unfold raw1673step2 raw1673step1; decide +kernel
      have hl : raw1673step1Labels = labelEmbedding1 ∘ raw1673step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1673step1 raw1673step1Labels raw1673step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1928 node1928Labels := by rfl

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

theorem canonical1800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1800 raw1800Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw1800 raw1800Labels = mixedMoment B raw1800step0 raw1800step0Labels := by
      have ha : raw1800step0 = (fun i j => raw1800 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1800step0 raw1800; decide +kernel
      have hl : raw1800step0Labels = raw1800Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1800 raw1800Labels permutation32 permutation4
    mixedMoment B raw1800step0 raw1800step0Labels = mixedMoment B raw1800step1 raw1800step1Labels := by
      have ha : raw1800step1 = raw1800step0 := by apply Matrix.ext; unfold raw1800step1 raw1800step0; decide +kernel
      have hl : raw1800step0Labels = labelEmbedding7 ∘ raw1800step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1800step0 raw1800step0Labels raw1800step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical1801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1801 raw1801Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw1801 raw1801Labels = mixedMoment B raw1801step0 raw1801step0Labels := by
      have ha : raw1801step0 = (fun i j => raw1801 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1801step0 raw1801; decide +kernel
      have hl : raw1801step0Labels = raw1801Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1801 raw1801Labels permutation32 permutation4
    _ = mixedMoment B node2110 node2110Labels := by rfl

theorem canonical1802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1802 raw1802Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw1802 raw1802Labels = mixedMoment B raw1802step0 raw1802step0Labels := by
      have ha : raw1802step0 = (fun i j => raw1802 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1802step0 raw1802; decide +kernel
      have hl : raw1802step0Labels = raw1802Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1802 raw1802Labels permutation50 permutation6
    mixedMoment B raw1802step0 raw1802step0Labels = mixedMoment B raw1802step1 raw1802step1Labels := by
      have ha : raw1802step1 = -raw1802step0 := by apply Matrix.ext; change ∀ i j, raw1802step1 i j = -(raw1802step0 i j); unfold raw1802step1 raw1802step0; decide +kernel
      have hl : raw1802step1Labels = raw1802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1802step1 raw1802step1Labels = mixedMoment B raw1802step2 raw1802step2Labels := by
      have ha : raw1802step2 = raw1802step1 := by apply Matrix.ext; unfold raw1802step2 raw1802step1; decide +kernel
      have hl : raw1802step1Labels = labelEmbedding1 ∘ raw1802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1802step1 raw1802step1Labels raw1802step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

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

theorem canonical1806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1806 raw1806Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw1806 raw1806Labels = mixedMoment B raw1806step0 raw1806step0Labels := by
      have ha : raw1806step0 = (fun i j => raw1806 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1806step0 raw1806; decide +kernel
      have hl : raw1806step0Labels = raw1806Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1806 raw1806Labels permutation8 permutation4
    mixedMoment B raw1806step0 raw1806step0Labels = mixedMoment B raw1806step1 raw1806step1Labels := by
      have ha : raw1806step1 = raw1806step0 := by apply Matrix.ext; unfold raw1806step1 raw1806step0; decide +kernel
      have hl : raw1806step0Labels = labelEmbedding7 ∘ raw1806step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1806step0 raw1806step0Labels raw1806step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

theorem canonical1807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1807 raw1807Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw1807 raw1807Labels = mixedMoment B raw1807step0 raw1807step0Labels := by
      have ha : raw1807step0 = (fun i j => raw1807 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1807step0 raw1807; decide +kernel
      have hl : raw1807step0Labels = raw1807Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1807 raw1807Labels permutation8 permutation4
    _ = mixedMoment B node2115 node2115Labels := by rfl

theorem canonical1808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1808 raw1808Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw1808 raw1808Labels = mixedMoment B raw1808step0 raw1808step0Labels := by
      have ha : raw1808step0 = (fun i j => raw1808 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1808step0 raw1808; decide +kernel
      have hl : raw1808step0Labels = raw1808Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1808 raw1808Labels permutation10 permutation6
    mixedMoment B raw1808step0 raw1808step0Labels = mixedMoment B raw1808step1 raw1808step1Labels := by
      have ha : raw1808step1 = -raw1808step0 := by apply Matrix.ext; change ∀ i j, raw1808step1 i j = -(raw1808step0 i j); unfold raw1808step1 raw1808step0; decide +kernel
      have hl : raw1808step1Labels = raw1808step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1808step1 raw1808step1Labels = mixedMoment B raw1808step2 raw1808step2Labels := by
      have ha : raw1808step2 = raw1808step1 := by apply Matrix.ext; unfold raw1808step2 raw1808step1; decide +kernel
      have hl : raw1808step1Labels = labelEmbedding1 ∘ raw1808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1808step1 raw1808step1Labels raw1808step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2276 node2276Labels := by rfl

theorem canonical1827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1827 raw1827Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw1827 raw1827Labels = mixedMoment B raw1827step0 raw1827step0Labels := by
      have ha : raw1827step0 = (fun i j => raw1827 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1827step0 raw1827; decide +kernel
      have hl : raw1827step0Labels = raw1827Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1827 raw1827Labels permutation8 permutation4
    mixedMoment B raw1827step0 raw1827step0Labels = mixedMoment B raw1827step1 raw1827step1Labels := by
      have ha : raw1827step1 = raw1827step0 := by apply Matrix.ext; unfold raw1827step1 raw1827step0; decide +kernel
      have hl : raw1827step0Labels = labelEmbedding7 ∘ raw1827step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1827step0 raw1827step0Labels raw1827step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

theorem canonical1828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1828 raw1828Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw1828 raw1828Labels = mixedMoment B raw1828step0 raw1828step0Labels := by
      have ha : raw1828step0 = (fun i j => raw1828 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1828step0 raw1828; decide +kernel
      have hl : raw1828step0Labels = raw1828Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1828 raw1828Labels permutation8 permutation4
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical1829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1829 raw1829Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw1829 raw1829Labels = mixedMoment B raw1829step0 raw1829step0Labels := by
      have ha : raw1829step0 = (fun i j => raw1829 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1829step0 raw1829; decide +kernel
      have hl : raw1829step0Labels = raw1829Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1829 raw1829Labels permutation13 permutation6
    mixedMoment B raw1829step0 raw1829step0Labels = mixedMoment B raw1829step1 raw1829step1Labels := by
      have ha : raw1829step1 = -raw1829step0 := by apply Matrix.ext; change ∀ i j, raw1829step1 i j = -(raw1829step0 i j); unfold raw1829step1 raw1829step0; decide +kernel
      have hl : raw1829step1Labels = raw1829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1829step1 raw1829step1Labels = mixedMoment B raw1829step2 raw1829step2Labels := by
      have ha : raw1829step2 = raw1829step1 := by apply Matrix.ext; unfold raw1829step2 raw1829step1; decide +kernel
      have hl : raw1829step1Labels = labelEmbedding1 ∘ raw1829step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1829step1 raw1829step1Labels raw1829step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical1830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1830 raw1830Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw1830 raw1830Labels = mixedMoment B raw1830step0 raw1830step0Labels := by
      have ha : raw1830step0 = (fun i j => raw1830 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1830step0 raw1830; decide +kernel
      have hl : raw1830step0Labels = raw1830Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1830 raw1830Labels permutation2 permutation4
    mixedMoment B raw1830step0 raw1830step0Labels = mixedMoment B raw1830step1 raw1830step1Labels := by
      have ha : raw1830step1 = raw1830step0 := by apply Matrix.ext; unfold raw1830step1 raw1830step0; decide +kernel
      have hl : raw1830step0Labels = labelEmbedding7 ∘ raw1830step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1830step0 raw1830step0Labels raw1830step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

theorem canonical1831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1831 raw1831Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw1831 raw1831Labels = mixedMoment B raw1831step0 raw1831step0Labels := by
      have ha : raw1831step0 = (fun i j => raw1831 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1831step0 raw1831; decide +kernel
      have hl : raw1831step0Labels = raw1831Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1831 raw1831Labels permutation2 permutation4
    _ = mixedMoment B node2281 node2281Labels := by rfl

theorem canonical1832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1832 raw1832Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw1832 raw1832Labels = mixedMoment B raw1832step0 raw1832step0Labels := by
      have ha : raw1832step0 = (fun i j => raw1832 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1832step0 raw1832; decide +kernel
      have hl : raw1832step0Labels = raw1832Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1832 raw1832Labels permutation3 permutation6
    mixedMoment B raw1832step0 raw1832step0Labels = mixedMoment B raw1832step1 raw1832step1Labels := by
      have ha : raw1832step1 = -raw1832step0 := by apply Matrix.ext; change ∀ i j, raw1832step1 i j = -(raw1832step0 i j); unfold raw1832step1 raw1832step0; decide +kernel
      have hl : raw1832step1Labels = raw1832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1832step1 raw1832step1Labels = mixedMoment B raw1832step2 raw1832step2Labels := by
      have ha : raw1832step2 = raw1832step1 := by apply Matrix.ext; unfold raw1832step2 raw1832step1; decide +kernel
      have hl : raw1832step1Labels = labelEmbedding1 ∘ raw1832step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1832step1 raw1832step1Labels raw1832step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2294 node2294Labels := by rfl

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

theorem canonical2493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2493 raw2493Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw2493 raw2493Labels = mixedMoment B raw2493step0 raw2493step0Labels := by
      have ha : raw2493step0 = (fun i j => raw2493 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2493step0 raw2493; decide +kernel
      have hl : raw2493step0Labels = raw2493Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2493 raw2493Labels permutation32 permutation4
    mixedMoment B raw2493step0 raw2493step0Labels = mixedMoment B raw2493step1 raw2493step1Labels := by
      have ha : raw2493step1 = raw2493step0 := by apply Matrix.ext; unfold raw2493step1 raw2493step0; decide +kernel
      have hl : raw2493step0Labels = labelEmbedding7 ∘ raw2493step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2493step0 raw2493step0Labels raw2493step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical2494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2494 raw2494Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw2494 raw2494Labels = mixedMoment B raw2494step0 raw2494step0Labels := by
      have ha : raw2494step0 = (fun i j => raw2494 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2494step0 raw2494; decide +kernel
      have hl : raw2494step0Labels = raw2494Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2494 raw2494Labels permutation32 permutation4
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical2495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2495 raw2495Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw2495 raw2495Labels = mixedMoment B raw2495step0 raw2495step0Labels := by
      have ha : raw2495step0 = (fun i j => raw2495 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2495step0 raw2495; decide +kernel
      have hl : raw2495step0Labels = raw2495Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2495 raw2495Labels permutation37 permutation6
    mixedMoment B raw2495step0 raw2495step0Labels = mixedMoment B raw2495step1 raw2495step1Labels := by
      have ha : raw2495step1 = -raw2495step0 := by apply Matrix.ext; change ∀ i j, raw2495step1 i j = -(raw2495step0 i j); unfold raw2495step1 raw2495step0; decide +kernel
      have hl : raw2495step1Labels = raw2495step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2495step1 raw2495step1Labels = mixedMoment B raw2495step2 raw2495step2Labels := by
      have ha : raw2495step2 = raw2495step1 := by apply Matrix.ext; unfold raw2495step2 raw2495step1; decide +kernel
      have hl : raw2495step1Labels = labelEmbedding1 ∘ raw2495step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2495step1 raw2495step1Labels raw2495step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical2544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2544 raw2544Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2544 raw2544Labels = mixedMoment B raw2544step0 raw2544step0Labels := by
      have ha : raw2544step0 = (fun i j => raw2544 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2544step0 raw2544; decide +kernel
      have hl : raw2544step0Labels = raw2544Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2544 raw2544Labels permutation8 permutation4
    mixedMoment B raw2544step0 raw2544step0Labels = mixedMoment B raw2544step1 raw2544step1Labels := by
      have ha : raw2544step1 = raw2544step0 := by apply Matrix.ext; unfold raw2544step1 raw2544step0; decide +kernel
      have hl : raw2544step0Labels = labelEmbedding7 ∘ raw2544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2544step0 raw2544step0Labels raw2544step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

theorem canonical2545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2545 raw2545Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw2545 raw2545Labels = mixedMoment B raw2545step0 raw2545step0Labels := by
      have ha : raw2545step0 = (fun i j => raw2545 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2545step0 raw2545; decide +kernel
      have hl : raw2545step0Labels = raw2545Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2545 raw2545Labels permutation8 permutation4
    _ = mixedMoment B node3862 node3862Labels := by rfl

theorem canonical2546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2546 raw2546Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw2546 raw2546Labels = mixedMoment B raw2546step0 raw2546step0Labels := by
      have ha : raw2546step0 = (fun i j => raw2546 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2546step0 raw2546; decide +kernel
      have hl : raw2546step0Labels = raw2546Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2546 raw2546Labels permutation9 permutation6
    mixedMoment B raw2546step0 raw2546step0Labels = mixedMoment B raw2546step1 raw2546step1Labels := by
      have ha : raw2546step1 = -raw2546step0 := by apply Matrix.ext; change ∀ i j, raw2546step1 i j = -(raw2546step0 i j); unfold raw2546step1 raw2546step0; decide +kernel
      have hl : raw2546step1Labels = raw2546step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2546step1 raw2546step1Labels = mixedMoment B raw2546step2 raw2546step2Labels := by
      have ha : raw2546step2 = raw2546step1 := by apply Matrix.ext; unfold raw2546step2 raw2546step1; decide +kernel
      have hl : raw2546step1Labels = labelEmbedding1 ∘ raw2546step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2546step1 raw2546step1Labels raw2546step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3907 node3907Labels := by rfl

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

theorem canonical2568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2568 raw2568Labels = mixedMoment B node5456 node5456Labels := by
  calc
    _ = mixedMoment B node5456 node5456Labels := by rfl

theorem canonical2569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2569 raw2569Labels = mixedMoment B node3916 node3916Labels := by
  calc
    _ = mixedMoment B node3916 node3916Labels := by rfl

theorem canonical2570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2570 raw2570Labels = mixedMoment B node3916 node3916Labels := by
  calc
    mixedMoment B raw2570 raw2570Labels = mixedMoment B raw2570step0 raw2570step0Labels := by
      have ha : raw2570step0 = (fun i j => raw2570 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2570step0 raw2570; decide +kernel
      have hl : raw2570step0Labels = raw2570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2570 raw2570Labels permutation7 permutation3
    mixedMoment B raw2570step0 raw2570step0Labels = mixedMoment B raw2570step1 raw2570step1Labels := by
      have ha : raw2570step1 = -raw2570step0 := by apply Matrix.ext; change ∀ i j, raw2570step1 i j = -(raw2570step0 i j); unfold raw2570step1 raw2570step0; decide +kernel
      have hl : raw2570step1Labels = raw2570step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2570step1 raw2570step1Labels = mixedMoment B raw2570step2 raw2570step2Labels := by
      have ha : raw2570step2 = raw2570step1 := by apply Matrix.ext; unfold raw2570step2 raw2570step1; decide +kernel
      have hl : raw2570step1Labels = labelEmbedding1 ∘ raw2570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2570step1 raw2570step1Labels raw2570step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3916 node3916Labels := by rfl

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

theorem canonical536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw536 raw536Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw536 raw536Labels = mixedMoment B raw536step0 raw536step0Labels := by
      have ha : raw536step0 = (fun i j => raw536 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw536step0 raw536; decide +kernel
      have hl : raw536step0Labels = raw536Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw536 raw536Labels permutation8 permutation5
    mixedMoment B raw536step0 raw536step0Labels = mixedMoment B raw536step1 raw536step1Labels := by
      have ha : raw536step1 = raw536step0 := by apply Matrix.ext; unfold raw536step1 raw536step0; decide +kernel
      have hl : raw536step0Labels = labelEmbedding1 ∘ raw536step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw536step0 raw536step0Labels raw536step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

theorem canonical537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw537 raw537Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw537 raw537Labels = mixedMoment B raw537step0 raw537step0Labels := by
      have ha : raw537step0 = (fun i j => raw537 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw537step0 raw537; decide +kernel
      have hl : raw537step0Labels = raw537Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw537 raw537Labels permutation8 permutation5
    _ = mixedMoment B node496 node496Labels := by rfl

theorem canonical554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw554 raw554Labels = mixedMoment B node3916 node3916Labels := by
  calc
    mixedMoment B raw554 raw554Labels = mixedMoment B raw554step0 raw554step0Labels := by
      have ha : raw554step0 = (fun i j => raw554 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw554step0 raw554; decide +kernel
      have hl : raw554step0Labels = raw554Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw554 raw554Labels permutation2 permutation5
    mixedMoment B raw554step0 raw554step0Labels = mixedMoment B raw554step1 raw554step1Labels := by
      have ha : raw554step1 = raw554step0 := by apply Matrix.ext; unfold raw554step1 raw554step0; decide +kernel
      have hl : raw554step0Labels = labelEmbedding1 ∘ raw554step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw554step0 raw554step0Labels raw554step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3916 node3916Labels := by rfl

theorem canonical555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw555 raw555Labels = mixedMoment B node507 node507Labels := by
  calc
    mixedMoment B raw555 raw555Labels = mixedMoment B raw555step0 raw555step0Labels := by
      have ha : raw555step0 = (fun i j => raw555 (permutation5 i) (permutation2 j)) := by apply Matrix.ext; unfold raw555step0 raw555; decide +kernel
      have hl : raw555step0Labels = raw555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw555 raw555Labels permutation5 permutation2
    _ = mixedMoment B node507 node507Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1002 raw1002Labels = mixedMoment B node4275 node4275Labels := by
  calc
    mixedMoment B raw1002 raw1002Labels = mixedMoment B raw1002step0 raw1002step0Labels := by
      have ha : raw1002step0 = (fun i j => raw1002 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1002step0 raw1002; decide +kernel
      have hl : raw1002step0Labels = raw1002Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1002 raw1002Labels permutation32 permutation4
    mixedMoment B raw1002step0 raw1002step0Labels = mixedMoment B raw1002step1 raw1002step1Labels := by
      have ha : raw1002step1 = raw1002step0 := by apply Matrix.ext; unfold raw1002step1 raw1002step0; decide +kernel
      have hl : raw1002step0Labels = labelEmbedding7 ∘ raw1002step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1002step0 raw1002step0Labels raw1002step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4275 node4275Labels := by rfl

theorem canonical1003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1003 raw1003Labels = mixedMoment B node827 node827Labels := by
  calc
    mixedMoment B raw1003 raw1003Labels = mixedMoment B raw1003step0 raw1003step0Labels := by
      have ha : raw1003step0 = (fun i j => raw1003 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1003step0 raw1003; decide +kernel
      have hl : raw1003step0Labels = raw1003Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1003 raw1003Labels permutation32 permutation4
    _ = mixedMoment B node827 node827Labels := by rfl

theorem canonical1004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1004 raw1004Labels = mixedMoment B node827 node827Labels := by
  calc
    mixedMoment B raw1004 raw1004Labels = mixedMoment B raw1004step0 raw1004step0Labels := by
      have ha : raw1004step0 = (fun i j => raw1004 (permutation53 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1004step0 raw1004; decide +kernel
      have hl : raw1004step0Labels = raw1004Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1004 raw1004Labels permutation53 permutation6
    mixedMoment B raw1004step0 raw1004step0Labels = mixedMoment B raw1004step1 raw1004step1Labels := by
      have ha : raw1004step1 = -raw1004step0 := by apply Matrix.ext; change ∀ i j, raw1004step1 i j = -(raw1004step0 i j); unfold raw1004step1 raw1004step0; decide +kernel
      have hl : raw1004step1Labels = raw1004step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1004step1 raw1004step1Labels = mixedMoment B raw1004step2 raw1004step2Labels := by
      have ha : raw1004step2 = raw1004step1 := by apply Matrix.ext; unfold raw1004step2 raw1004step1; decide +kernel
      have hl : raw1004step1Labels = labelEmbedding1 ∘ raw1004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1004step1 raw1004step1Labels raw1004step2Labels labelEmbedding1 hl
    _ = mixedMoment B node827 node827Labels := by rfl

theorem canonical1005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1005 raw1005Labels = mixedMoment B node4276 node4276Labels := by
  calc
    mixedMoment B raw1005 raw1005Labels = mixedMoment B raw1005step0 raw1005step0Labels := by
      have ha : raw1005step0 = (fun i j => raw1005 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1005step0 raw1005; decide +kernel
      have hl : raw1005step0Labels = raw1005Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1005 raw1005Labels permutation8 permutation4
    mixedMoment B raw1005step0 raw1005step0Labels = mixedMoment B raw1005step1 raw1005step1Labels := by
      have ha : raw1005step1 = raw1005step0 := by apply Matrix.ext; unfold raw1005step1 raw1005step0; decide +kernel
      have hl : raw1005step0Labels = labelEmbedding7 ∘ raw1005step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1005step0 raw1005step0Labels raw1005step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4276 node4276Labels := by rfl

theorem canonical1006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1006 raw1006Labels = mixedMoment B node828 node828Labels := by
  calc
    mixedMoment B raw1006 raw1006Labels = mixedMoment B raw1006step0 raw1006step0Labels := by
      have ha : raw1006step0 = (fun i j => raw1006 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1006step0 raw1006; decide +kernel
      have hl : raw1006step0Labels = raw1006Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1006 raw1006Labels permutation8 permutation4
    _ = mixedMoment B node828 node828Labels := by rfl

theorem canonical1007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1007 raw1007Labels = mixedMoment B node857 node857Labels := by
  calc
    mixedMoment B raw1007 raw1007Labels = mixedMoment B raw1007step0 raw1007step0Labels := by
      have ha : raw1007step0 = (fun i j => raw1007 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1007step0 raw1007; decide +kernel
      have hl : raw1007step0Labels = raw1007Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1007 raw1007Labels permutation11 permutation6
    mixedMoment B raw1007step0 raw1007step0Labels = mixedMoment B raw1007step1 raw1007step1Labels := by
      have ha : raw1007step1 = -raw1007step0 := by apply Matrix.ext; change ∀ i j, raw1007step1 i j = -(raw1007step0 i j); unfold raw1007step1 raw1007step0; decide +kernel
      have hl : raw1007step1Labels = raw1007step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1007step1 raw1007step1Labels = mixedMoment B raw1007step2 raw1007step2Labels := by
      have ha : raw1007step2 = raw1007step1 := by apply Matrix.ext; unfold raw1007step2 raw1007step1; decide +kernel
      have hl : raw1007step1Labels = labelEmbedding1 ∘ raw1007step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1007step1 raw1007step1Labels raw1007step2Labels labelEmbedding1 hl
    _ = mixedMoment B node857 node857Labels := by rfl

theorem canonical1008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1008 raw1008Labels = mixedMoment B node4278 node4278Labels := by
  calc
    mixedMoment B raw1008 raw1008Labels = mixedMoment B raw1008step0 raw1008step0Labels := by
      have ha : raw1008step0 = (fun i j => raw1008 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1008step0 raw1008; decide +kernel
      have hl : raw1008step0Labels = raw1008Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1008 raw1008Labels permutation8 permutation4
    mixedMoment B raw1008step0 raw1008step0Labels = mixedMoment B raw1008step1 raw1008step1Labels := by
      have ha : raw1008step1 = raw1008step0 := by apply Matrix.ext; unfold raw1008step1 raw1008step0; decide +kernel
      have hl : raw1008step0Labels = labelEmbedding7 ∘ raw1008step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1008step0 raw1008step0Labels raw1008step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4278 node4278Labels := by rfl

theorem canonical1009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1009 raw1009Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw1009 raw1009Labels = mixedMoment B raw1009step0 raw1009step0Labels := by
      have ha : raw1009step0 = (fun i j => raw1009 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1009step0 raw1009; decide +kernel
      have hl : raw1009step0Labels = raw1009Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1009 raw1009Labels permutation8 permutation4
    _ = mixedMoment B node830 node830Labels := by rfl

theorem canonical1010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1010 raw1010Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw1010 raw1010Labels = mixedMoment B raw1010step0 raw1010step0Labels := by
      have ha : raw1010step0 = (fun i j => raw1010 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1010step0 raw1010; decide +kernel
      have hl : raw1010step0Labels = raw1010Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1010 raw1010Labels permutation10 permutation6
    mixedMoment B raw1010step0 raw1010step0Labels = mixedMoment B raw1010step1 raw1010step1Labels := by
      have ha : raw1010step1 = -raw1010step0 := by apply Matrix.ext; change ∀ i j, raw1010step1 i j = -(raw1010step0 i j); unfold raw1010step1 raw1010step0; decide +kernel
      have hl : raw1010step1Labels = raw1010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1010step1 raw1010step1Labels = mixedMoment B raw1010step2 raw1010step2Labels := by
      have ha : raw1010step2 = raw1010step1 := by apply Matrix.ext; unfold raw1010step2 raw1010step1; decide +kernel
      have hl : raw1010step1Labels = labelEmbedding1 ∘ raw1010step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1010step1 raw1010step1Labels raw1010step2Labels labelEmbedding1 hl
    _ = mixedMoment B node830 node830Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10769 raw10769Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw10769 raw10769Labels = mixedMoment B raw10769step0 raw10769step0Labels := by
      have hz : ∀ j, raw10769 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10769step0 = (fun i j => raw10769 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10769step0 raw10769; decide +kernel
      have hl : raw10769step0Labels = raw10769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10769 raw10769Labels permutation434 hz
    mixedMoment B raw10769step0 raw10769step0Labels = mixedMoment B raw10769step1 raw10769step1Labels := by
      have hz : ∀ j, raw10769step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10769step1 = (fun i j => raw10769step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10769step1 raw10769step0; decide +kernel
      have hl : raw10769step1Labels = raw10769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10769step0 raw10769step0Labels permutation80 hz
    mixedMoment B raw10769step1 raw10769step1Labels = mixedMoment B raw10769step2 raw10769step2Labels := by
      have ha : raw10769step2 = (fun i j => raw10769step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10769step2 raw10769step1; decide +kernel
      have hl : raw10769step2Labels = raw10769step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10769step1 raw10769step1Labels permutation31 permutation2
    mixedMoment B raw10769step2 raw10769step2Labels = mixedMoment B raw10769step3 raw10769step3Labels := by
      have ha : raw10769step3 = -raw10769step2 := by apply Matrix.ext; change ∀ i j, raw10769step3 i j = -(raw10769step2 i j); unfold raw10769step3 raw10769step2; decide +kernel
      have hl : raw10769step3Labels = raw10769step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5443 node5443Labels := by rfl

theorem canonical10770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10770 raw10770Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw10770 raw10770Labels = mixedMoment B raw10770step0 raw10770step0Labels := by
      have hz : ∀ j, raw10770 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10770step0 = (fun i j => raw10770 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10770step0 raw10770; decide +kernel
      have hl : raw10770step0Labels = raw10770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10770 raw10770Labels permutation434 hz
    mixedMoment B raw10770step0 raw10770step0Labels = mixedMoment B raw10770step1 raw10770step1Labels := by
      have ha : raw10770step1 = (fun i j => raw10770step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10770step1 raw10770step0; decide +kernel
      have hl : raw10770step1Labels = raw10770step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10770step0 raw10770step0Labels permutation38 permutation3
    mixedMoment B raw10770step1 raw10770step1Labels = mixedMoment B raw10770step2 raw10770step2Labels := by
      have ha : raw10770step2 = raw10770step1 := by apply Matrix.ext; unfold raw10770step2 raw10770step1; decide +kernel
      have hl : raw10770step1Labels = labelEmbedding6 ∘ raw10770step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10770step1 raw10770step1Labels raw10770step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical10771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10771 raw10771Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw10771 raw10771Labels = mixedMoment B raw10771step0 raw10771step0Labels := by
      have hz : ∀ j, raw10771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10771step0 = (fun i j => raw10771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10771step0 raw10771; decide +kernel
      have hl : raw10771step0Labels = raw10771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10771 raw10771Labels permutation346 hz
    mixedMoment B raw10771step0 raw10771step0Labels = mixedMoment B raw10771step1 raw10771step1Labels := by
      have ha : raw10771step1 = (fun i j => raw10771step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10771step1 raw10771step0; decide +kernel
      have hl : raw10771step1Labels = raw10771step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10771step0 raw10771step0Labels permutation38 permutation3
    mixedMoment B raw10771step1 raw10771step1Labels = mixedMoment B raw10771step2 raw10771step2Labels := by
      have ha : raw10771step2 = raw10771step1 := by apply Matrix.ext; unfold raw10771step2 raw10771step1; decide +kernel
      have hl : raw10771step1Labels = labelEmbedding6 ∘ raw10771step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10771step1 raw10771step1Labels raw10771step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical10772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10772 raw10772Labels = mixedMoment B node5456 node5456Labels := by
  calc
    mixedMoment B raw10772 raw10772Labels = mixedMoment B raw10772step0 raw10772step0Labels := by
      have hz : ∀ j, raw10772 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10772step0 = (fun i j => raw10772 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10772step0 raw10772; decide +kernel
      have hl : raw10772step0Labels = raw10772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10772 raw10772Labels permutation520 hz
    mixedMoment B raw10772step0 raw10772step0Labels = mixedMoment B raw10772step1 raw10772step1Labels := by
      have hz : ∀ j, raw10772step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10772step1 = (fun i j => raw10772step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10772step1 raw10772step0; decide +kernel
      have hl : raw10772step1Labels = raw10772step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10772step0 raw10772step0Labels permutation104 hz
    mixedMoment B raw10772step1 raw10772step1Labels = mixedMoment B raw10772step2 raw10772step2Labels := by
      have hz : ∀ j, raw10772step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10772step2 = (fun i j => raw10772step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10772step2 raw10772step1; decide +kernel
      have hl : raw10772step2Labels = raw10772step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10772step1 raw10772step1Labels permutation20 hz
    mixedMoment B raw10772step2 raw10772step2Labels = mixedMoment B raw10772step3 raw10772step3Labels := by
      have ha : raw10772step3 = (fun i j => raw10772step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10772step3 raw10772step2; decide +kernel
      have hl : raw10772step3Labels = raw10772step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10772step2 raw10772step2Labels permutation7 permutation2
    mixedMoment B raw10772step3 raw10772step3Labels = mixedMoment B raw10772step4 raw10772step4Labels := by
      have ha : raw10772step4 = -raw10772step3 := by apply Matrix.ext; change ∀ i j, raw10772step4 i j = -(raw10772step3 i j); unfold raw10772step4 raw10772step3; decide +kernel
      have hl : raw10772step4Labels = raw10772step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5456 node5456Labels := by rfl

theorem canonical10773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10773 raw10773Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw10773 raw10773Labels = mixedMoment B raw10773step0 raw10773step0Labels := by
      have hz : ∀ j, raw10773 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10773step0 = (fun i j => raw10773 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10773step0 raw10773; decide +kernel
      have hl : raw10773step0Labels = raw10773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10773 raw10773Labels permutation434 hz
    mixedMoment B raw10773step0 raw10773step0Labels = mixedMoment B raw10773step1 raw10773step1Labels := by
      have hz : ∀ j, raw10773step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10773step1 = (fun i j => raw10773step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10773step1 raw10773step0; decide +kernel
      have hl : raw10773step1Labels = raw10773step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10773step0 raw10773step0Labels permutation80 hz
    mixedMoment B raw10773step1 raw10773step1Labels = mixedMoment B raw10773step2 raw10773step2Labels := by
      have ha : raw10773step2 = (fun i j => raw10773step1 (permutation17 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10773step2 raw10773step1; decide +kernel
      have hl : raw10773step2Labels = raw10773step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10773step1 raw10773step1Labels permutation17 permutation4
    mixedMoment B raw10773step2 raw10773step2Labels = mixedMoment B raw10773step3 raw10773step3Labels := by
      have ha : raw10773step3 = raw10773step2 := by apply Matrix.ext; unfold raw10773step3 raw10773step2; decide +kernel
      have hl : raw10773step2Labels = labelEmbedding7 ∘ raw10773step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10773step2 raw10773step2Labels raw10773step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

theorem canonical10774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10774 raw10774Labels = mixedMoment B node4276 node4276Labels := by
  calc
    mixedMoment B raw10774 raw10774Labels = mixedMoment B raw10774step0 raw10774step0Labels := by
      have hz : ∀ j, raw10774 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10774step0 = (fun i j => raw10774 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10774step0 raw10774; decide +kernel
      have hl : raw10774step0Labels = raw10774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10774 raw10774Labels permutation434 hz
    mixedMoment B raw10774step0 raw10774step0Labels = mixedMoment B raw10774step1 raw10774step1Labels := by
      have hz : ∀ j, raw10774step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10774step1 = (fun i j => raw10774step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10774step1 raw10774step0; decide +kernel
      have hl : raw10774step1Labels = raw10774step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10774step0 raw10774step0Labels permutation80 hz
    mixedMoment B raw10774step1 raw10774step1Labels = mixedMoment B raw10774step2 raw10774step2Labels := by
      have ha : raw10774step2 = (fun i j => raw10774step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10774step2 raw10774step1; decide +kernel
      have hl : raw10774step2Labels = raw10774step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10774step1 raw10774step1Labels permutation13 permutation5
    mixedMoment B raw10774step2 raw10774step2Labels = mixedMoment B raw10774step3 raw10774step3Labels := by
      have ha : raw10774step3 = -raw10774step2 := by apply Matrix.ext; change ∀ i j, raw10774step3 i j = -(raw10774step2 i j); unfold raw10774step3 raw10774step2; decide +kernel
      have hl : raw10774step3Labels = raw10774step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10774step3 raw10774step3Labels = mixedMoment B raw10774step4 raw10774step4Labels := by
      have ha : raw10774step4 = raw10774step3 := by apply Matrix.ext; unfold raw10774step4 raw10774step3; decide +kernel
      have hl : raw10774step3Labels = labelEmbedding8 ∘ raw10774step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10774step3 raw10774step3Labels raw10774step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4276 node4276Labels := by rfl

theorem canonical10775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10775 raw10775Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw10775 raw10775Labels = mixedMoment B raw10775step0 raw10775step0Labels := by
      have hz : ∀ j, raw10775 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10775step0 = (fun i j => raw10775 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10775step0 raw10775; decide +kernel
      have hl : raw10775step0Labels = raw10775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10775 raw10775Labels permutation434 hz
    mixedMoment B raw10775step0 raw10775step0Labels = mixedMoment B raw10775step1 raw10775step1Labels := by
      have ha : raw10775step1 = (fun i j => raw10775step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10775step1 raw10775step0; decide +kernel
      have hl : raw10775step1Labels = raw10775step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10775step0 raw10775step0Labels permutation43 permutation5
    mixedMoment B raw10775step1 raw10775step1Labels = mixedMoment B raw10775step2 raw10775step2Labels := by
      have ha : raw10775step2 = -raw10775step1 := by apply Matrix.ext; change ∀ i j, raw10775step2 i j = -(raw10775step1 i j); unfold raw10775step2 raw10775step1; decide +kernel
      have hl : raw10775step2Labels = raw10775step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10775step2 raw10775step2Labels = mixedMoment B raw10775step3 raw10775step3Labels := by
      have ha : raw10775step3 = raw10775step2 := by apply Matrix.ext; unfold raw10775step3 raw10775step2; decide +kernel
      have hl : raw10775step2Labels = labelEmbedding8 ∘ raw10775step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10775step2 raw10775step2Labels raw10775step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

theorem canonical10776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10776 raw10776Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw10776 raw10776Labels = mixedMoment B raw10776step0 raw10776step0Labels := by
      have hz : ∀ j, raw10776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10776step0 = (fun i j => raw10776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10776step0 raw10776; decide +kernel
      have hl : raw10776step0Labels = raw10776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10776 raw10776Labels permutation346 hz
    mixedMoment B raw10776step0 raw10776step0Labels = mixedMoment B raw10776step1 raw10776step1Labels := by
      have ha : raw10776step1 = (fun i j => raw10776step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10776step1 raw10776step0; decide +kernel
      have hl : raw10776step1Labels = raw10776step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10776step0 raw10776step0Labels permutation43 permutation5
    mixedMoment B raw10776step1 raw10776step1Labels = mixedMoment B raw10776step2 raw10776step2Labels := by
      have ha : raw10776step2 = -raw10776step1 := by apply Matrix.ext; change ∀ i j, raw10776step2 i j = -(raw10776step1 i j); unfold raw10776step2 raw10776step1; decide +kernel
      have hl : raw10776step2Labels = raw10776step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10776step2 raw10776step2Labels = mixedMoment B raw10776step3 raw10776step3Labels := by
      have ha : raw10776step3 = raw10776step2 := by apply Matrix.ext; unfold raw10776step3 raw10776step2; decide +kernel
      have hl : raw10776step2Labels = labelEmbedding8 ∘ raw10776step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10776step2 raw10776step2Labels raw10776step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

theorem canonical10777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10777 raw10777Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw10777 raw10777Labels = mixedMoment B raw10777step0 raw10777step0Labels := by
      have hz : ∀ j, raw10777 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10777step0 = (fun i j => raw10777 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10777step0 raw10777; decide +kernel
      have hl : raw10777step0Labels = raw10777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10777 raw10777Labels permutation520 hz
    mixedMoment B raw10777step0 raw10777step0Labels = mixedMoment B raw10777step1 raw10777step1Labels := by
      have hz : ∀ j, raw10777step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10777step1 = (fun i j => raw10777step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10777step1 raw10777step0; decide +kernel
      have hl : raw10777step1Labels = raw10777step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10777step0 raw10777step0Labels permutation104 hz
    mixedMoment B raw10777step1 raw10777step1Labels = mixedMoment B raw10777step2 raw10777step2Labels := by
      have hz : ∀ j, raw10777step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10777step2 = (fun i j => raw10777step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10777step2 raw10777step1; decide +kernel
      have hl : raw10777step2Labels = raw10777step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10777step1 raw10777step1Labels permutation20 hz
    mixedMoment B raw10777step2 raw10777step2Labels = mixedMoment B raw10777step3 raw10777step3Labels := by
      have ha : raw10777step3 = (fun i j => raw10777step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10777step3 raw10777step2; decide +kernel
      have hl : raw10777step3Labels = raw10777step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10777step2 raw10777step2Labels permutation3 permutation5
    mixedMoment B raw10777step3 raw10777step3Labels = mixedMoment B raw10777step4 raw10777step4Labels := by
      have ha : raw10777step4 = -raw10777step3 := by apply Matrix.ext; change ∀ i j, raw10777step4 i j = -(raw10777step3 i j); unfold raw10777step4 raw10777step3; decide +kernel
      have hl : raw10777step4Labels = raw10777step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10777step4 raw10777step4Labels = mixedMoment B raw10777step5 raw10777step5Labels := by
      have ha : raw10777step5 = raw10777step4 := by apply Matrix.ext; unfold raw10777step5 raw10777step4; decide +kernel
      have hl : raw10777step4Labels = labelEmbedding8 ∘ raw10777step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10777step4 raw10777step4Labels raw10777step5Labels labelEmbedding8 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

theorem canonical10778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10778 raw10778Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw10778 raw10778Labels = mixedMoment B raw10778step0 raw10778step0Labels := by
      have hz : ∀ j, raw10778 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10778step0 = (fun i j => raw10778 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10778step0 raw10778; decide +kernel
      have hl : raw10778step0Labels = raw10778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10778 raw10778Labels permutation434 hz
    mixedMoment B raw10778step0 raw10778step0Labels = mixedMoment B raw10778step1 raw10778step1Labels := by
      have hz : ∀ j, raw10778step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10778step1 = (fun i j => raw10778step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10778step1 raw10778step0; decide +kernel
      have hl : raw10778step1Labels = raw10778step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10778step0 raw10778step0Labels permutation80 hz
    mixedMoment B raw10778step1 raw10778step1Labels = mixedMoment B raw10778step2 raw10778step2Labels := by
      have ha : raw10778step2 = (fun i j => raw10778step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10778step2 raw10778step1; decide +kernel
      have hl : raw10778step2Labels = raw10778step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10778step1 raw10778step1Labels permutation13 permutation5
    mixedMoment B raw10778step2 raw10778step2Labels = mixedMoment B raw10778step3 raw10778step3Labels := by
      have ha : raw10778step3 = -raw10778step2 := by apply Matrix.ext; change ∀ i j, raw10778step3 i j = -(raw10778step2 i j); unfold raw10778step3 raw10778step2; decide +kernel
      have hl : raw10778step3Labels = raw10778step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10778step3 raw10778step3Labels = mixedMoment B raw10778step4 raw10778step4Labels := by
      have ha : raw10778step4 = raw10778step3 := by apply Matrix.ext; unfold raw10778step4 raw10778step3; decide +kernel
      have hl : raw10778step3Labels = labelEmbedding8 ∘ raw10778step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10778step3 raw10778step3Labels raw10778step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

theorem canonical10779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10779 raw10779Labels = mixedMoment B node4275 node4275Labels := by
  calc
    mixedMoment B raw10779 raw10779Labels = mixedMoment B raw10779step0 raw10779step0Labels := by
      have hz : ∀ j, raw10779 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10779step0 = (fun i j => raw10779 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10779step0 raw10779; decide +kernel
      have hl : raw10779step0Labels = raw10779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10779 raw10779Labels permutation434 hz
    mixedMoment B raw10779step0 raw10779step0Labels = mixedMoment B raw10779step1 raw10779step1Labels := by
      have ha : raw10779step1 = (fun i j => raw10779step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10779step1 raw10779step0; decide +kernel
      have hl : raw10779step1Labels = raw10779step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10779step0 raw10779step0Labels permutation32 permutation3
    mixedMoment B raw10779step1 raw10779step1Labels = mixedMoment B raw10779step2 raw10779step2Labels := by
      have ha : raw10779step2 = raw10779step1 := by apply Matrix.ext; unfold raw10779step2 raw10779step1; decide +kernel
      have hl : raw10779step1Labels = labelEmbedding6 ∘ raw10779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10779step1 raw10779step1Labels raw10779step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4275 node4275Labels := by rfl

theorem canonical10780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10780 raw10780Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw10780 raw10780Labels = mixedMoment B raw10780step0 raw10780step0Labels := by
      have hz : ∀ j, raw10780 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10780step0 = (fun i j => raw10780 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10780step0 raw10780; decide +kernel
      have hl : raw10780step0Labels = raw10780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10780 raw10780Labels permutation434 hz
    mixedMoment B raw10780step0 raw10780step0Labels = mixedMoment B raw10780step1 raw10780step1Labels := by
      have ha : raw10780step1 = (fun i j => raw10780step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10780step1 raw10780step0; decide +kernel
      have hl : raw10780step1Labels = raw10780step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10780step0 raw10780step0Labels permutation32 permutation3
    mixedMoment B raw10780step1 raw10780step1Labels = mixedMoment B raw10780step2 raw10780step2Labels := by
      have ha : raw10780step2 = raw10780step1 := by apply Matrix.ext; unfold raw10780step2 raw10780step1; decide +kernel
      have hl : raw10780step1Labels = labelEmbedding6 ∘ raw10780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10780step1 raw10780step1Labels raw10780step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical10781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10781 raw10781Labels = mixedMoment B node4746 node4746Labels := by
  calc
    mixedMoment B raw10781 raw10781Labels = mixedMoment B raw10781step0 raw10781step0Labels := by
      have ha : raw10781step0 = (fun i j => raw10781 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10781step0 raw10781; decide +kernel
      have hl : raw10781step0Labels = raw10781Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10781 raw10781Labels permutation200 permutation3
    mixedMoment B raw10781step0 raw10781step0Labels = mixedMoment B raw10781step1 raw10781step1Labels := by
      have ha : raw10781step1 = raw10781step0 := by apply Matrix.ext; unfold raw10781step1 raw10781step0; decide +kernel
      have hl : raw10781step0Labels = labelEmbedding6 ∘ raw10781step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10781step0 raw10781step0Labels raw10781step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4746 node4746Labels := by rfl

theorem canonical10782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10782 raw10782Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw10782 raw10782Labels = mixedMoment B raw10782step0 raw10782step0Labels := by
      have hz : ∀ j, raw10782 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10782step0 = (fun i j => raw10782 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10782step0 raw10782; decide +kernel
      have hl : raw10782step0Labels = raw10782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10782 raw10782Labels permutation520 hz
    mixedMoment B raw10782step0 raw10782step0Labels = mixedMoment B raw10782step1 raw10782step1Labels := by
      have hz : ∀ j, raw10782step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10782step1 = (fun i j => raw10782step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10782step1 raw10782step0; decide +kernel
      have hl : raw10782step1Labels = raw10782step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10782step0 raw10782step0Labels permutation104 hz
    mixedMoment B raw10782step1 raw10782step1Labels = mixedMoment B raw10782step2 raw10782step2Labels := by
      have ha : raw10782step2 = (fun i j => raw10782step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10782step2 raw10782step1; decide +kernel
      have hl : raw10782step2Labels = raw10782step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10782step1 raw10782step1Labels permutation8 permutation3
    mixedMoment B raw10782step2 raw10782step2Labels = mixedMoment B raw10782step3 raw10782step3Labels := by
      have ha : raw10782step3 = raw10782step2 := by apply Matrix.ext; unfold raw10782step3 raw10782step2; decide +kernel
      have hl : raw10782step2Labels = labelEmbedding6 ∘ raw10782step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10782step2 raw10782step2Labels raw10782step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

theorem canonical10783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10783 raw10783Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw10783 raw10783Labels = mixedMoment B raw10783step0 raw10783step0Labels := by
      have hz : ∀ j, raw10783 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10783step0 = (fun i j => raw10783 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10783step0 raw10783; decide +kernel
      have hl : raw10783step0Labels = raw10783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10783 raw10783Labels permutation434 hz
    mixedMoment B raw10783step0 raw10783step0Labels = mixedMoment B raw10783step1 raw10783step1Labels := by
      have ha : raw10783step1 = (fun i j => raw10783step0 (permutation53 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10783step1 raw10783step0; decide +kernel
      have hl : raw10783step1Labels = raw10783step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10783step0 raw10783step0Labels permutation53 permutation5
    mixedMoment B raw10783step1 raw10783step1Labels = mixedMoment B raw10783step2 raw10783step2Labels := by
      have ha : raw10783step2 = -raw10783step1 := by apply Matrix.ext; change ∀ i j, raw10783step2 i j = -(raw10783step1 i j); unfold raw10783step2 raw10783step1; decide +kernel
      have hl : raw10783step2Labels = raw10783step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10783step2 raw10783step2Labels = mixedMoment B raw10783step3 raw10783step3Labels := by
      have ha : raw10783step3 = raw10783step2 := by apply Matrix.ext; unfold raw10783step3 raw10783step2; decide +kernel
      have hl : raw10783step2Labels = labelEmbedding8 ∘ raw10783step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10783step2 raw10783step2Labels raw10783step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical10784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10784 raw10784Labels = mixedMoment B node4275 node4275Labels := by
  calc
    mixedMoment B raw10784 raw10784Labels = mixedMoment B raw10784step0 raw10784step0Labels := by
      have hz : ∀ j, raw10784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10784step0 = (fun i j => raw10784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10784step0 raw10784; decide +kernel
      have hl : raw10784step0Labels = raw10784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10784 raw10784Labels permutation346 hz
    mixedMoment B raw10784step0 raw10784step0Labels = mixedMoment B raw10784step1 raw10784step1Labels := by
      have ha : raw10784step1 = (fun i j => raw10784step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10784step1 raw10784step0; decide +kernel
      have hl : raw10784step1Labels = raw10784step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10784step0 raw10784step0Labels permutation32 permutation3
    mixedMoment B raw10784step1 raw10784step1Labels = mixedMoment B raw10784step2 raw10784step2Labels := by
      have ha : raw10784step2 = raw10784step1 := by apply Matrix.ext; unfold raw10784step2 raw10784step1; decide +kernel
      have hl : raw10784step1Labels = labelEmbedding6 ∘ raw10784step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10784step1 raw10784step1Labels raw10784step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4275 node4275Labels := by rfl

theorem canonical10785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10785 raw10785Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw10785 raw10785Labels = mixedMoment B raw10785step0 raw10785step0Labels := by
      have hz : ∀ j, raw10785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10785step0 = (fun i j => raw10785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10785step0 raw10785; decide +kernel
      have hl : raw10785step0Labels = raw10785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10785 raw10785Labels permutation346 hz
    mixedMoment B raw10785step0 raw10785step0Labels = mixedMoment B raw10785step1 raw10785step1Labels := by
      have ha : raw10785step1 = (fun i j => raw10785step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10785step1 raw10785step0; decide +kernel
      have hl : raw10785step1Labels = raw10785step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10785step0 raw10785step0Labels permutation32 permutation3
    mixedMoment B raw10785step1 raw10785step1Labels = mixedMoment B raw10785step2 raw10785step2Labels := by
      have ha : raw10785step2 = raw10785step1 := by apply Matrix.ext; unfold raw10785step2 raw10785step1; decide +kernel
      have hl : raw10785step1Labels = labelEmbedding6 ∘ raw10785step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10785step1 raw10785step1Labels raw10785step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical10786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10786 raw10786Labels = mixedMoment B node4746 node4746Labels := by
  calc
    mixedMoment B raw10786 raw10786Labels = mixedMoment B raw10786step0 raw10786step0Labels := by
      have ha : raw10786step0 = (fun i j => raw10786 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10786step0 raw10786; decide +kernel
      have hl : raw10786step0Labels = raw10786Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10786 raw10786Labels permutation176 permutation3
    mixedMoment B raw10786step0 raw10786step0Labels = mixedMoment B raw10786step1 raw10786step1Labels := by
      have ha : raw10786step1 = raw10786step0 := by apply Matrix.ext; unfold raw10786step1 raw10786step0; decide +kernel
      have hl : raw10786step0Labels = labelEmbedding6 ∘ raw10786step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10786step0 raw10786step0Labels raw10786step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4746 node4746Labels := by rfl

theorem canonical10787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10787 raw10787Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw10787 raw10787Labels = mixedMoment B raw10787step0 raw10787step0Labels := by
      have hz : ∀ j, raw10787 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10787step0 = (fun i j => raw10787 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10787step0 raw10787; decide +kernel
      have hl : raw10787step0Labels = raw10787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10787 raw10787Labels permutation520 hz
    mixedMoment B raw10787step0 raw10787step0Labels = mixedMoment B raw10787step1 raw10787step1Labels := by
      have hz : ∀ j, raw10787step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10787step1 = (fun i j => raw10787step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10787step1 raw10787step0; decide +kernel
      have hl : raw10787step1Labels = raw10787step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10787step0 raw10787step0Labels permutation80 hz
    mixedMoment B raw10787step1 raw10787step1Labels = mixedMoment B raw10787step2 raw10787step2Labels := by
      have ha : raw10787step2 = (fun i j => raw10787step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10787step2 raw10787step1; decide +kernel
      have hl : raw10787step2Labels = raw10787step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10787step1 raw10787step1Labels permutation8 permutation3
    mixedMoment B raw10787step2 raw10787step2Labels = mixedMoment B raw10787step3 raw10787step3Labels := by
      have ha : raw10787step3 = raw10787step2 := by apply Matrix.ext; unfold raw10787step3 raw10787step2; decide +kernel
      have hl : raw10787step2Labels = labelEmbedding6 ∘ raw10787step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10787step2 raw10787step2Labels raw10787step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

theorem canonical10788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10788 raw10788Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw10788 raw10788Labels = mixedMoment B raw10788step0 raw10788step0Labels := by
      have hz : ∀ j, raw10788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10788step0 = (fun i j => raw10788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10788step0 raw10788; decide +kernel
      have hl : raw10788step0Labels = raw10788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10788 raw10788Labels permutation346 hz
    mixedMoment B raw10788step0 raw10788step0Labels = mixedMoment B raw10788step1 raw10788step1Labels := by
      have ha : raw10788step1 = (fun i j => raw10788step0 (permutation53 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10788step1 raw10788step0; decide +kernel
      have hl : raw10788step1Labels = raw10788step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10788step0 raw10788step0Labels permutation53 permutation5
    mixedMoment B raw10788step1 raw10788step1Labels = mixedMoment B raw10788step2 raw10788step2Labels := by
      have ha : raw10788step2 = -raw10788step1 := by apply Matrix.ext; change ∀ i j, raw10788step2 i j = -(raw10788step1 i j); unfold raw10788step2 raw10788step1; decide +kernel
      have hl : raw10788step2Labels = raw10788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10788step2 raw10788step2Labels = mixedMoment B raw10788step3 raw10788step3Labels := by
      have ha : raw10788step3 = raw10788step2 := by apply Matrix.ext; unfold raw10788step3 raw10788step2; decide +kernel
      have hl : raw10788step2Labels = labelEmbedding8 ∘ raw10788step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10788step2 raw10788step2Labels raw10788step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical10789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10789 raw10789Labels = mixedMoment B node4278 node4278Labels := by
  calc
    mixedMoment B raw10789 raw10789Labels = mixedMoment B raw10789step0 raw10789step0Labels := by
      have hz : ∀ j, raw10789 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10789step0 = (fun i j => raw10789 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10789step0 raw10789; decide +kernel
      have hl : raw10789step0Labels = raw10789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10789 raw10789Labels permutation434 hz
    mixedMoment B raw10789step0 raw10789step0Labels = mixedMoment B raw10789step1 raw10789step1Labels := by
      have hz : ∀ j, raw10789step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10789step1 = (fun i j => raw10789step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10789step1 raw10789step0; decide +kernel
      have hl : raw10789step1Labels = raw10789step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10789step0 raw10789step0Labels permutation80 hz
    mixedMoment B raw10789step1 raw10789step1Labels = mixedMoment B raw10789step2 raw10789step2Labels := by
      have ha : raw10789step2 = (fun i j => raw10789step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10789step2 raw10789step1; decide +kernel
      have hl : raw10789step2Labels = raw10789step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10789step1 raw10789step1Labels permutation9 permutation3
    mixedMoment B raw10789step2 raw10789step2Labels = mixedMoment B raw10789step3 raw10789step3Labels := by
      have ha : raw10789step3 = raw10789step2 := by apply Matrix.ext; unfold raw10789step3 raw10789step2; decide +kernel
      have hl : raw10789step2Labels = labelEmbedding6 ∘ raw10789step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10789step2 raw10789step2Labels raw10789step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4278 node4278Labels := by rfl

theorem canonical10790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10790 raw10790Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw10790 raw10790Labels = mixedMoment B raw10790step0 raw10790step0Labels := by
      have hz : ∀ j, raw10790 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10790step0 = (fun i j => raw10790 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10790step0 raw10790; decide +kernel
      have hl : raw10790step0Labels = raw10790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10790 raw10790Labels permutation434 hz
    mixedMoment B raw10790step0 raw10790step0Labels = mixedMoment B raw10790step1 raw10790step1Labels := by
      have hz : ∀ j, raw10790step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10790step1 = (fun i j => raw10790step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10790step1 raw10790step0; decide +kernel
      have hl : raw10790step1Labels = raw10790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10790step0 raw10790step0Labels permutation80 hz
    mixedMoment B raw10790step1 raw10790step1Labels = mixedMoment B raw10790step2 raw10790step2Labels := by
      have ha : raw10790step2 = (fun i j => raw10790step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10790step2 raw10790step1; decide +kernel
      have hl : raw10790step2Labels = raw10790step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10790step1 raw10790step1Labels permutation9 permutation3
    mixedMoment B raw10790step2 raw10790step2Labels = mixedMoment B raw10790step3 raw10790step3Labels := by
      have ha : raw10790step3 = raw10790step2 := by apply Matrix.ext; unfold raw10790step3 raw10790step2; decide +kernel
      have hl : raw10790step2Labels = labelEmbedding6 ∘ raw10790step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10790step2 raw10790step2Labels raw10790step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

theorem canonical10791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10791 raw10791Labels = mixedMoment B node4749 node4749Labels := by
  calc
    mixedMoment B raw10791 raw10791Labels = mixedMoment B raw10791step0 raw10791step0Labels := by
      have hz : ∀ j, raw10791 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10791step0 = (fun i j => raw10791 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10791step0 raw10791; decide +kernel
      have hl : raw10791step0Labels = raw10791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10791 raw10791Labels permutation434 hz
    mixedMoment B raw10791step0 raw10791step0Labels = mixedMoment B raw10791step1 raw10791step1Labels := by
      have ha : raw10791step1 = (fun i j => raw10791step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10791step1 raw10791step0; decide +kernel
      have hl : raw10791step1Labels = raw10791step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10791step0 raw10791step0Labels permutation39 permutation3
    mixedMoment B raw10791step1 raw10791step1Labels = mixedMoment B raw10791step2 raw10791step2Labels := by
      have ha : raw10791step2 = raw10791step1 := by apply Matrix.ext; unfold raw10791step2 raw10791step1; decide +kernel
      have hl : raw10791step1Labels = labelEmbedding6 ∘ raw10791step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10791step1 raw10791step1Labels raw10791step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4749 node4749Labels := by rfl

theorem canonical10792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10792 raw10792Labels = mixedMoment B node4749 node4749Labels := by
  calc
    mixedMoment B raw10792 raw10792Labels = mixedMoment B raw10792step0 raw10792step0Labels := by
      have hz : ∀ j, raw10792 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10792step0 = (fun i j => raw10792 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10792step0 raw10792; decide +kernel
      have hl : raw10792step0Labels = raw10792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10792 raw10792Labels permutation346 hz
    mixedMoment B raw10792step0 raw10792step0Labels = mixedMoment B raw10792step1 raw10792step1Labels := by
      have ha : raw10792step1 = (fun i j => raw10792step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10792step1 raw10792step0; decide +kernel
      have hl : raw10792step1Labels = raw10792step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10792step0 raw10792step0Labels permutation39 permutation3
    mixedMoment B raw10792step1 raw10792step1Labels = mixedMoment B raw10792step2 raw10792step2Labels := by
      have ha : raw10792step2 = raw10792step1 := by apply Matrix.ext; unfold raw10792step2 raw10792step1; decide +kernel
      have hl : raw10792step1Labels = labelEmbedding6 ∘ raw10792step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10792step1 raw10792step1Labels raw10792step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4749 node4749Labels := by rfl

theorem canonical10793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10793 raw10793Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw10793 raw10793Labels = mixedMoment B raw10793step0 raw10793step0Labels := by
      have hz : ∀ j, raw10793 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10793step0 = (fun i j => raw10793 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10793step0 raw10793; decide +kernel
      have hl : raw10793step0Labels = raw10793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10793 raw10793Labels permutation434 hz
    mixedMoment B raw10793step0 raw10793step0Labels = mixedMoment B raw10793step1 raw10793step1Labels := by
      have hz : ∀ j, raw10793step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10793step1 = (fun i j => raw10793step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10793step1 raw10793step0; decide +kernel
      have hl : raw10793step1Labels = raw10793step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10793step0 raw10793step0Labels permutation80 hz
    mixedMoment B raw10793step1 raw10793step1Labels = mixedMoment B raw10793step2 raw10793step2Labels := by
      have ha : raw10793step2 = (fun i j => raw10793step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10793step2 raw10793step1; decide +kernel
      have hl : raw10793step2Labels = raw10793step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10793step1 raw10793step1Labels permutation12 permutation5
    mixedMoment B raw10793step2 raw10793step2Labels = mixedMoment B raw10793step3 raw10793step3Labels := by
      have ha : raw10793step3 = -raw10793step2 := by apply Matrix.ext; change ∀ i j, raw10793step3 i j = -(raw10793step2 i j); unfold raw10793step3 raw10793step2; decide +kernel
      have hl : raw10793step3Labels = raw10793step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10793step3 raw10793step3Labels = mixedMoment B raw10793step4 raw10793step4Labels := by
      have ha : raw10793step4 = raw10793step3 := by apply Matrix.ext; unfold raw10793step4 raw10793step3; decide +kernel
      have hl : raw10793step3Labels = labelEmbedding8 ∘ raw10793step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10793step3 raw10793step3Labels raw10793step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

theorem canonical10794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10794 raw10794Labels = mixedMoment B node4276 node4276Labels := by
  calc
    mixedMoment B raw10794 raw10794Labels = mixedMoment B raw10794step0 raw10794step0Labels := by
      have hz : ∀ j, raw10794 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10794step0 = (fun i j => raw10794 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10794step0 raw10794; decide +kernel
      have hl : raw10794step0Labels = raw10794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10794 raw10794Labels permutation434 hz
    mixedMoment B raw10794step0 raw10794step0Labels = mixedMoment B raw10794step1 raw10794step1Labels := by
      have hz : ∀ j, raw10794step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10794step1 = (fun i j => raw10794step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10794step1 raw10794step0; decide +kernel
      have hl : raw10794step1Labels = raw10794step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10794step0 raw10794step0Labels permutation80 hz
    mixedMoment B raw10794step1 raw10794step1Labels = mixedMoment B raw10794step2 raw10794step2Labels := by
      have ha : raw10794step2 = (fun i j => raw10794step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10794step2 raw10794step1; decide +kernel
      have hl : raw10794step2Labels = raw10794step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10794step1 raw10794step1Labels permutation8 permutation3
    mixedMoment B raw10794step2 raw10794step2Labels = mixedMoment B raw10794step3 raw10794step3Labels := by
      have ha : raw10794step3 = raw10794step2 := by apply Matrix.ext; unfold raw10794step3 raw10794step2; decide +kernel
      have hl : raw10794step2Labels = labelEmbedding6 ∘ raw10794step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10794step2 raw10794step2Labels raw10794step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4276 node4276Labels := by rfl

theorem canonical10795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10795 raw10795Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw10795 raw10795Labels = mixedMoment B raw10795step0 raw10795step0Labels := by
      have hz : ∀ j, raw10795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10795step0 = (fun i j => raw10795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10795step0 raw10795; decide +kernel
      have hl : raw10795step0Labels = raw10795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10795 raw10795Labels permutation434 hz
    mixedMoment B raw10795step0 raw10795step0Labels = mixedMoment B raw10795step1 raw10795step1Labels := by
      have hz : ∀ j, raw10795step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10795step1 = (fun i j => raw10795step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10795step1 raw10795step0; decide +kernel
      have hl : raw10795step1Labels = raw10795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10795step0 raw10795step0Labels permutation80 hz
    mixedMoment B raw10795step1 raw10795step1Labels = mixedMoment B raw10795step2 raw10795step2Labels := by
      have ha : raw10795step2 = (fun i j => raw10795step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10795step2 raw10795step1; decide +kernel
      have hl : raw10795step2Labels = raw10795step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10795step1 raw10795step1Labels permutation8 permutation3
    mixedMoment B raw10795step2 raw10795step2Labels = mixedMoment B raw10795step3 raw10795step3Labels := by
      have ha : raw10795step3 = raw10795step2 := by apply Matrix.ext; unfold raw10795step3 raw10795step2; decide +kernel
      have hl : raw10795step2Labels = labelEmbedding6 ∘ raw10795step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10795step2 raw10795step2Labels raw10795step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

theorem canonical10796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10796 raw10796Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw10796 raw10796Labels = mixedMoment B raw10796step0 raw10796step0Labels := by
      have hz : ∀ j, raw10796 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10796step0 = (fun i j => raw10796 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10796step0 raw10796; decide +kernel
      have hl : raw10796step0Labels = raw10796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10796 raw10796Labels permutation434 hz
    mixedMoment B raw10796step0 raw10796step0Labels = mixedMoment B raw10796step1 raw10796step1Labels := by
      have ha : raw10796step1 = (fun i j => raw10796step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10796step1 raw10796step0; decide +kernel
      have hl : raw10796step1Labels = raw10796step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10796step0 raw10796step0Labels permutation38 permutation3
    mixedMoment B raw10796step1 raw10796step1Labels = mixedMoment B raw10796step2 raw10796step2Labels := by
      have ha : raw10796step2 = raw10796step1 := by apply Matrix.ext; unfold raw10796step2 raw10796step1; decide +kernel
      have hl : raw10796step1Labels = labelEmbedding6 ∘ raw10796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10796step1 raw10796step1Labels raw10796step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

theorem canonical10797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10797 raw10797Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw10797 raw10797Labels = mixedMoment B raw10797step0 raw10797step0Labels := by
      have hz : ∀ j, raw10797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10797step0 = (fun i j => raw10797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10797step0 raw10797; decide +kernel
      have hl : raw10797step0Labels = raw10797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10797 raw10797Labels permutation346 hz
    mixedMoment B raw10797step0 raw10797step0Labels = mixedMoment B raw10797step1 raw10797step1Labels := by
      have ha : raw10797step1 = (fun i j => raw10797step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10797step1 raw10797step0; decide +kernel
      have hl : raw10797step1Labels = raw10797step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10797step0 raw10797step0Labels permutation38 permutation3
    mixedMoment B raw10797step1 raw10797step1Labels = mixedMoment B raw10797step2 raw10797step2Labels := by
      have ha : raw10797step2 = raw10797step1 := by apply Matrix.ext; unfold raw10797step2 raw10797step1; decide +kernel
      have hl : raw10797step1Labels = labelEmbedding6 ∘ raw10797step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10797step1 raw10797step1Labels raw10797step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

theorem canonical10798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10798 raw10798Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw10798 raw10798Labels = mixedMoment B raw10798step0 raw10798step0Labels := by
      have hz : ∀ j, raw10798 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10798step0 = (fun i j => raw10798 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10798step0 raw10798; decide +kernel
      have hl : raw10798step0Labels = raw10798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10798 raw10798Labels permutation520 hz
    mixedMoment B raw10798step0 raw10798step0Labels = mixedMoment B raw10798step1 raw10798step1Labels := by
      have hz : ∀ j, raw10798step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10798step1 = (fun i j => raw10798step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10798step1 raw10798step0; decide +kernel
      have hl : raw10798step1Labels = raw10798step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10798step0 raw10798step0Labels permutation104 hz
    mixedMoment B raw10798step1 raw10798step1Labels = mixedMoment B raw10798step2 raw10798step2Labels := by
      have hz : ∀ j, raw10798step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10798step2 = (fun i j => raw10798step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10798step2 raw10798step1; decide +kernel
      have hl : raw10798step2Labels = raw10798step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10798step1 raw10798step1Labels permutation20 hz
    mixedMoment B raw10798step2 raw10798step2Labels = mixedMoment B raw10798step3 raw10798step3Labels := by
      have ha : raw10798step3 = (fun i j => raw10798step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10798step3 raw10798step2; decide +kernel
      have hl : raw10798step3Labels = raw10798step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10798step2 raw10798step2Labels permutation2 permutation3
    mixedMoment B raw10798step3 raw10798step3Labels = mixedMoment B raw10798step4 raw10798step4Labels := by
      have ha : raw10798step4 = raw10798step3 := by apply Matrix.ext; unfold raw10798step4 raw10798step3; decide +kernel
      have hl : raw10798step3Labels = labelEmbedding6 ∘ raw10798step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10798step3 raw10798step3Labels raw10798step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

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

theorem canonical5214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5214 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5214 = injectiveMoment H raw5214step0 := by
      have hz : ∀ j, raw5214 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw5214step0 = (fun i j => raw5214 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5214 permutation7 hz
    _ = injectiveMoment H node4 := by rfl

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

theorem canonical7979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7979 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7979 = injectiveMoment H raw7979step0 := by
      have hz : ∀ j, raw7979 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7979step0 = (fun i j => raw7979 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979 permutation7 hz
    injectiveMoment H raw7979step0 = injectiveMoment H raw7979step1 := by
      have hz : ∀ j, raw7979step0 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7979step1 = (fun i j => raw7979step0 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step0 permutation2 hz
    injectiveMoment H raw7979step1 = injectiveMoment H raw7979step2 := by
      have hz : ∀ j, raw7979step1 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7979step2 = (fun i j => raw7979step1 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step1 permutation0 hz
    injectiveMoment H raw7979step2 = injectiveMoment H raw7979step3 := by
      have hz : ∀ i, raw7979step2 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7979step3 = (fun i j => raw7979step2 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7979step2 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical280
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8985 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8985 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8985 = injectiveMoment H raw8985step0 := by
      have hz : ∀ j, raw8985 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8985step0 = (fun i j => raw8985 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8985 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node507 node507Labels = Sparse.eval singlePairValue507 (familyPairVector B) := by
  have hp := single_label_three B hB node507
  have hl : node507Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node507 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 1) = PairSemantics.raw5214 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node507 PairSemantics.raw5214; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5214 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 2) = PairSemantics.raw8985 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node507 PairSemantics.raw8985; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8985 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 3) = PairSemantics.raw5183 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node507 PairSemantics.raw5183; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5183 hH).trans (PairSemantics.sound4 hH)
  have hm4 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value41 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 4) = PairSemantics.raw4141 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node507 PairSemantics.raw4141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4141 hH).trans (PairSemantics.sound41 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue507, PairSemantics.value0, PairSemantics.value4, PairSemantics.value41, Sparse.eval] at hp ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3862 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3862 node3862Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node496 node496Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw536 singletonSmall3862
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3862) = raw536Labels := by decide +kernel
  rw [hl, canonical536 B hB] at h
  have hc0 : mixedMoment B raw536 (Fin.cases (0 : Fin 1) singletonSmall3862) =
      mixedMoment B node496 node496Labels := by
    have ha : raw536 = raw537 := by apply Matrix.ext; unfold raw536 raw537; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3862 = raw537Labels := by decide +kernel
    rw [ha, hj, canonical537 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3916 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3916 node3916Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node507 node507Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw554 singletonSmall3916
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3916) = raw554Labels := by decide +kernel
  rw [hl, canonical554 B hB] at h
  have hc0 : mixedMoment B raw554 (Fin.cases (0 : Fin 1) singletonSmall3916) =
      mixedMoment B node507 node507Labels := by
    have ha : raw554 = raw555 := by apply Matrix.ext; unfold raw554 raw555; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3916 = raw555Labels := by decide +kernel
    rw [ha, hj, canonical555 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4275 node4275Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node827 node827Labels + mixedMoment B node827 node827Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1002 singletonSmall4275
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4275) = raw1002Labels := by decide +kernel
  rw [hl, canonical1002 B hB] at h
  have hc0 : mixedMoment B raw1002 (Fin.cases (0 : Fin 2) singletonSmall4275) =
      mixedMoment B node827 node827Labels := by
    have ha : raw1002 = raw1003 := by apply Matrix.ext; unfold raw1002 raw1003; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4275 = raw1003Labels := by decide +kernel
    rw [ha, hj, canonical1003 B hB]
  have hc1 : mixedMoment B raw1002 (Fin.cases (1 : Fin 2) singletonSmall4275) =
      mixedMoment B node827 node827Labels := by
    have ha : raw1002 = raw1004 := by apply Matrix.ext; unfold raw1002 raw1004; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4275 = raw1004Labels := by decide +kernel
    rw [ha, hj, canonical1004 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4276 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4276 node4276Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node828 node828Labels + mixedMoment B node857 node857Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1005 singletonSmall4276
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4276) = raw1005Labels := by decide +kernel
  rw [hl, canonical1005 B hB] at h
  have hc0 : mixedMoment B raw1005 (Fin.cases (0 : Fin 2) singletonSmall4276) =
      mixedMoment B node828 node828Labels := by
    have ha : raw1005 = raw1006 := by apply Matrix.ext; unfold raw1005 raw1006; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4276 = raw1006Labels := by decide +kernel
    rw [ha, hj, canonical1006 B hB]
  have hc1 : mixedMoment B raw1005 (Fin.cases (1 : Fin 2) singletonSmall4276) =
      mixedMoment B node857 node857Labels := by
    have ha : raw1005 = raw1007 := by apply Matrix.ext; unfold raw1005 raw1007; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4276 = raw1007Labels := by decide +kernel
    rw [ha, hj, canonical1007 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4278 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4278 node4278Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node830 node830Labels + mixedMoment B node830 node830Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1008 singletonSmall4278
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4278) = raw1008Labels := by decide +kernel
  rw [hl, canonical1008 B hB] at h
  have hc0 : mixedMoment B raw1008 (Fin.cases (0 : Fin 2) singletonSmall4278) =
      mixedMoment B node830 node830Labels := by
    have ha : raw1008 = raw1009 := by apply Matrix.ext; unfold raw1008 raw1009; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4278 = raw1009Labels := by decide +kernel
    rw [ha, hj, canonical1009 B hB]
  have hc1 : mixedMoment B raw1008 (Fin.cases (1 : Fin 2) singletonSmall4278) =
      mixedMoment B node830 node830Labels := by
    have ha : raw1008 = raw1010 := by apply Matrix.ext; unfold raw1008 raw1010; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4278 = raw1010Labels := by decide +kernel
    rw [ha, hj, canonical1010 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4746 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4746 node4746Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1925 node1925Labels + mixedMoment B node1925 node1925Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1665 singletonSmall4746
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4746) = raw1665Labels := by decide +kernel
  rw [hl, canonical1665 B hB] at h
  have hc0 : mixedMoment B raw1665 (Fin.cases (0 : Fin 2) singletonSmall4746) =
      mixedMoment B node1925 node1925Labels := by
    have ha : raw1665 = raw1666 := by apply Matrix.ext; unfold raw1665 raw1666; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4746 = raw1666Labels := by decide +kernel
    rw [ha, hj, canonical1666 B hB]
  have hc1 : mixedMoment B raw1665 (Fin.cases (1 : Fin 2) singletonSmall4746) =
      mixedMoment B node1925 node1925Labels := by
    have ha : raw1665 = raw1667 := by apply Matrix.ext; unfold raw1665 raw1667; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4746 = raw1667Labels := by decide +kernel
    rw [ha, hj, canonical1667 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4747 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4747 node4747Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1926 node1926Labels + mixedMoment B node1948 node1948Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1668 singletonSmall4747
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4747) = raw1668Labels := by decide +kernel
  rw [hl, canonical1668 B hB] at h
  have hc0 : mixedMoment B raw1668 (Fin.cases (0 : Fin 2) singletonSmall4747) =
      mixedMoment B node1926 node1926Labels := by
    have ha : raw1668 = raw1669 := by apply Matrix.ext; unfold raw1668 raw1669; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4747 = raw1669Labels := by decide +kernel
    rw [ha, hj, canonical1669 B hB]
  have hc1 : mixedMoment B raw1668 (Fin.cases (1 : Fin 2) singletonSmall4747) =
      mixedMoment B node1948 node1948Labels := by
    have ha : raw1668 = raw1670 := by apply Matrix.ext; unfold raw1668 raw1670; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4747 = raw1670Labels := by decide +kernel
    rw [ha, hj, canonical1670 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4749 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4749 node4749Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1928 node1928Labels + mixedMoment B node1928 node1928Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1671 singletonSmall4749
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4749) = raw1671Labels := by decide +kernel
  rw [hl, canonical1671 B hB] at h
  have hc0 : mixedMoment B raw1671 (Fin.cases (0 : Fin 2) singletonSmall4749) =
      mixedMoment B node1928 node1928Labels := by
    have ha : raw1671 = raw1672 := by apply Matrix.ext; unfold raw1671 raw1672; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4749 = raw1672Labels := by decide +kernel
    rw [ha, hj, canonical1672 B hB]
  have hc1 : mixedMoment B raw1671 (Fin.cases (1 : Fin 2) singletonSmall4749) =
      mixedMoment B node1928 node1928Labels := by
    have ha : raw1671 = raw1673 := by apply Matrix.ext; unfold raw1671 raw1673; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4749 = raw1673Labels := by decide +kernel
    rw [ha, hj, canonical1673 B hB]
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

theorem singleton4869 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4869 node4869Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2110 node2110Labels + mixedMoment B node2275 node2275Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1800 singletonSmall4869
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4869) = raw1800Labels := by decide +kernel
  rw [hl, canonical1800 B hB] at h
  have hc0 : mixedMoment B raw1800 (Fin.cases (0 : Fin 2) singletonSmall4869) =
      mixedMoment B node2110 node2110Labels := by
    have ha : raw1800 = raw1801 := by apply Matrix.ext; unfold raw1800 raw1801; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4869 = raw1801Labels := by decide +kernel
    rw [ha, hj, canonical1801 B hB]
  have hc1 : mixedMoment B raw1800 (Fin.cases (1 : Fin 2) singletonSmall4869) =
      mixedMoment B node2275 node2275Labels := by
    have ha : raw1800 = raw1802 := by apply Matrix.ext; unfold raw1800 raw1802; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4869 = raw1802Labels := by decide +kernel
    rw [ha, hj, canonical1802 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4874 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4874 node4874Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2115 node2115Labels + mixedMoment B node2276 node2276Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1806 singletonSmall4874
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4874) = raw1806Labels := by decide +kernel
  rw [hl, canonical1806 B hB] at h
  have hc0 : mixedMoment B raw1806 (Fin.cases (0 : Fin 2) singletonSmall4874) =
      mixedMoment B node2115 node2115Labels := by
    have ha : raw1806 = raw1807 := by apply Matrix.ext; unfold raw1806 raw1807; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4874 = raw1807Labels := by decide +kernel
    rw [ha, hj, canonical1807 B hB]
  have hc1 : mixedMoment B raw1806 (Fin.cases (1 : Fin 2) singletonSmall4874) =
      mixedMoment B node2276 node2276Labels := by
    have ha : raw1806 = raw1808 := by apply Matrix.ext; unfold raw1806 raw1808; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4874 = raw1808Labels := by decide +kernel
    rw [ha, hj, canonical1808 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4898 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4898 node4898Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2279 node2279Labels + mixedMoment B node2279 node2279Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1827 singletonSmall4898
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4898) = raw1827Labels := by decide +kernel
  rw [hl, canonical1827 B hB] at h
  have hc0 : mixedMoment B raw1827 (Fin.cases (0 : Fin 2) singletonSmall4898) =
      mixedMoment B node2279 node2279Labels := by
    have ha : raw1827 = raw1828 := by apply Matrix.ext; unfold raw1827 raw1828; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4898 = raw1828Labels := by decide +kernel
    rw [ha, hj, canonical1828 B hB]
  have hc1 : mixedMoment B raw1827 (Fin.cases (1 : Fin 2) singletonSmall4898) =
      mixedMoment B node2279 node2279Labels := by
    have ha : raw1827 = raw1829 := by apply Matrix.ext; unfold raw1827 raw1829; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4898 = raw1829Labels := by decide +kernel
    rw [ha, hj, canonical1829 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4899 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4899 node4899Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2281 node2281Labels + mixedMoment B node2294 node2294Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1830 singletonSmall4899
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4899) = raw1830Labels := by decide +kernel
  rw [hl, canonical1830 B hB] at h
  have hc0 : mixedMoment B raw1830 (Fin.cases (0 : Fin 2) singletonSmall4899) =
      mixedMoment B node2281 node2281Labels := by
    have ha : raw1830 = raw1831 := by apply Matrix.ext; unfold raw1830 raw1831; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4899 = raw1831Labels := by decide +kernel
    rw [ha, hj, canonical1831 B hB]
  have hc1 : mixedMoment B raw1830 (Fin.cases (1 : Fin 2) singletonSmall4899) =
      mixedMoment B node2294 node2294Labels := by
    have ha : raw1830 = raw1832 := by apply Matrix.ext; unfold raw1830 raw1832; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4899 = raw1832Labels := by decide +kernel
    rw [ha, hj, canonical1832 B hB]
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

theorem singleton5412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5412 node5412Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3814 node3814Labels + mixedMoment B node3814 node3814Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2493 singletonSmall5412
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5412) = raw2493Labels := by decide +kernel
  rw [hl, canonical2493 B hB] at h
  have hc0 : mixedMoment B raw2493 (Fin.cases (0 : Fin 2) singletonSmall5412) =
      mixedMoment B node3814 node3814Labels := by
    have ha : raw2493 = raw2494 := by apply Matrix.ext; unfold raw2493 raw2494; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5412 = raw2494Labels := by decide +kernel
    rw [ha, hj, canonical2494 B hB]
  have hc1 : mixedMoment B raw2493 (Fin.cases (1 : Fin 2) singletonSmall5412) =
      mixedMoment B node3814 node3814Labels := by
    have ha : raw2493 = raw2495 := by apply Matrix.ext; unfold raw2493 raw2495; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5412 = raw2495Labels := by decide +kernel
    rw [ha, hj, canonical2495 B hB]
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

theorem singleton5443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5443 node5443Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3862 node3862Labels + mixedMoment B node3907 node3907Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2544 singletonSmall5443
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5443) = raw2544Labels := by decide +kernel
  rw [hl, canonical2544 B hB] at h
  have hc0 : mixedMoment B raw2544 (Fin.cases (0 : Fin 2) singletonSmall5443) =
      mixedMoment B node3862 node3862Labels := by
    have ha : raw2544 = raw2545 := by apply Matrix.ext; unfold raw2544 raw2545; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5443 = raw2545Labels := by decide +kernel
    rw [ha, hj, canonical2545 B hB]
  have hc1 : mixedMoment B raw2544 (Fin.cases (1 : Fin 2) singletonSmall5443) =
      mixedMoment B node3907 node3907Labels := by
    have ha : raw2544 = raw2546 := by apply Matrix.ext; unfold raw2544 raw2546; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5443 = raw2546Labels := by decide +kernel
    rw [ha, hj, canonical2546 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5456 node5456Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3916 node3916Labels + mixedMoment B node3916 node3916Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2568 singletonSmall5456
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5456) = raw2568Labels := by decide +kernel
  rw [hl, canonical2568 B hB] at h
  have hc0 : mixedMoment B raw2568 (Fin.cases (0 : Fin 2) singletonSmall5456) =
      mixedMoment B node3916 node3916Labels := by
    have ha : raw2568 = raw2569 := by apply Matrix.ext; unfold raw2568 raw2569; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5456 = raw2569Labels := by decide +kernel
    rw [ha, hj, canonical2569 B hB]
  have hc1 : mixedMoment B raw2568 (Fin.cases (1 : Fin 2) singletonSmall5456) =
      mixedMoment B node3916 node3916Labels := by
    have ha : raw2568 = raw2570 := by apply Matrix.ext; unfold raw2568 raw2570; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5456 = raw2570Labels := by decide +kernel
    rw [ha, hj, canonical2570 B hB]
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

theorem sound2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2281 node2281Labels = Sparse.eval nodeValue2281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2281) = mixedMoment B node2281 node2281Labels := rfl
  simpa [nodeValue2281, Sparse.eval] using hc.symm

theorem sound2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2294 node2294Labels = Sparse.eval nodeValue2294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2294) = mixedMoment B node2294 node2294Labels := rfl
  simpa [nodeValue2294, Sparse.eval] using hc.symm

theorem sound3814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3814 node3814Labels = Sparse.eval nodeValue3814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3814) = mixedMoment B node3814 node3814Labels := rfl
  simpa [nodeValue3814, Sparse.eval] using hc.symm

theorem sound3862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3862 node3862Labels = Sparse.eval nodeValue3862 (mixedVector B) := by
  have h := singleton3862 B _hB
  rw [sound496 B _hB _hF] at h
  norm_num [nodeValue3862, nodeValue496, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3907 node3907Labels = Sparse.eval nodeValue3907 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3907) = mixedMoment B node3907 node3907Labels := rfl
  simpa [nodeValue3907, Sparse.eval] using hc.symm

theorem sound4898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4898 node4898Labels = Sparse.eval nodeValue4898 (mixedVector B) := by
  have h := singleton4898 B _hB
  rw [sound2279 B _hB _hF] at h
  norm_num [nodeValue4898, nodeValue2279, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4899 node4899Labels = Sparse.eval nodeValue4899 (mixedVector B) := by
  have h := singleton4899 B _hB
  rw [sound2281 B _hB _hF, sound2294 B _hB _hF] at h
  norm_num [nodeValue4899, nodeValue2281, nodeValue2294, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5412 node5412Labels = Sparse.eval nodeValue5412 (mixedVector B) := by
  have h := singleton5412 B _hB
  rw [sound3814 B _hB _hF] at h
  norm_num [nodeValue5412, nodeValue3814, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5443 node5443Labels = Sparse.eval nodeValue5443 (mixedVector B) := by
  have h := singleton5443 B _hB
  rw [sound3862 B _hB _hF, sound3907 B _hB _hF] at h
  norm_num [nodeValue5443, nodeValue3862, nodeValue3907, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node827 node827Labels = Sparse.eval nodeValue827 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 827) = mixedMoment B node827 node827Labels := rfl
  simpa [nodeValue827, Sparse.eval] using hc.symm

theorem sound828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node828 node828Labels = Sparse.eval nodeValue828 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 828) = mixedMoment B node828 node828Labels := rfl
  simpa [nodeValue828, Sparse.eval] using hc.symm

theorem sound830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node830 node830Labels = Sparse.eval nodeValue830 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 830) = mixedMoment B node830 node830Labels := rfl
  simpa [nodeValue830, Sparse.eval] using hc.symm

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

theorem sound857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node857 node857Labels = Sparse.eval nodeValue857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 857) = mixedMoment B node857 node857Labels := rfl
  simpa [nodeValue857, Sparse.eval] using hc.symm

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

theorem sound1925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1925 node1925Labels = Sparse.eval nodeValue1925 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1925) = mixedMoment B node1925 node1925Labels := rfl
  simpa [nodeValue1925, Sparse.eval] using hc.symm

theorem sound1926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1926 node1926Labels = Sparse.eval nodeValue1926 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1926) = mixedMoment B node1926 node1926Labels := rfl
  simpa [nodeValue1926, Sparse.eval] using hc.symm

theorem sound1928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1928 node1928Labels = Sparse.eval nodeValue1928 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1928) = mixedMoment B node1928 node1928Labels := rfl
  simpa [nodeValue1928, Sparse.eval] using hc.symm

theorem sound1948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1948 node1948Labels = Sparse.eval nodeValue1948 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1948) = mixedMoment B node1948 node1948Labels := rfl
  simpa [nodeValue1948, Sparse.eval] using hc.symm

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

theorem sound2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2110 node2110Labels = Sparse.eval nodeValue2110 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2110) = mixedMoment B node2110 node2110Labels := rfl
  simpa [nodeValue2110, Sparse.eval] using hc.symm

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

theorem sound2115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2115 node2115Labels = Sparse.eval nodeValue2115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2115) = mixedMoment B node2115 node2115Labels := rfl
  simpa [nodeValue2115, Sparse.eval] using hc.symm

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

theorem sound2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2275 node2275Labels = Sparse.eval nodeValue2275 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2275) = mixedMoment B node2275 node2275Labels := rfl
  simpa [nodeValue2275, Sparse.eval] using hc.symm

theorem sound2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2276 node2276Labels = Sparse.eval nodeValue2276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2276) = mixedMoment B node2276 node2276Labels := rfl
  simpa [nodeValue2276, Sparse.eval] using hc.symm

theorem sound2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2287 node2287Labels = Sparse.eval nodeValue2287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2287) = mixedMoment B node2287 node2287Labels := rfl
  simpa [nodeValue2287, Sparse.eval] using hc.symm

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

theorem sound507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node507 node507Labels = Sparse.eval nodeValue507 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue507 (familyPairVector B) := singlePair507 B _hB
    _ = _ := by norm_num [singlePairValue507, nodeValue507, Sparse.eval, mixedVector] <;> ring

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

theorem sound3916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3916 node3916Labels = Sparse.eval nodeValue3916 (mixedVector B) := by
  have h := singleton3916 B _hB
  rw [sound507 B _hB _hF] at h
  norm_num [nodeValue3916, nodeValue507, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4275 node4275Labels = Sparse.eval nodeValue4275 (mixedVector B) := by
  have h := singleton4275 B _hB
  rw [sound827 B _hB _hF] at h
  norm_num [nodeValue4275, nodeValue827, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4276 node4276Labels = Sparse.eval nodeValue4276 (mixedVector B) := by
  have h := singleton4276 B _hB
  rw [sound828 B _hB _hF, sound857 B _hB _hF] at h
  norm_num [nodeValue4276, nodeValue828, nodeValue857, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4278 node4278Labels = Sparse.eval nodeValue4278 (mixedVector B) := by
  have h := singleton4278 B _hB
  rw [sound830 B _hB _hF] at h
  norm_num [nodeValue4278, nodeValue830, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4746 node4746Labels = Sparse.eval nodeValue4746 (mixedVector B) := by
  have h := singleton4746 B _hB
  rw [sound1925 B _hB _hF] at h
  norm_num [nodeValue4746, nodeValue1925, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4747 node4747Labels = Sparse.eval nodeValue4747 (mixedVector B) := by
  have h := singleton4747 B _hB
  rw [sound1926 B _hB _hF, sound1948 B _hB _hF] at h
  norm_num [nodeValue4747, nodeValue1926, nodeValue1948, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4749 node4749Labels = Sparse.eval nodeValue4749 (mixedVector B) := by
  have h := singleton4749 B _hB
  rw [sound1928 B _hB _hF] at h
  norm_num [nodeValue4749, nodeValue1928, Sparse.eval] at h ⊢
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

theorem sound4869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4869 node4869Labels = Sparse.eval nodeValue4869 (mixedVector B) := by
  have h := singleton4869 B _hB
  rw [sound2110 B _hB _hF, sound2275 B _hB _hF] at h
  norm_num [nodeValue4869, nodeValue2110, nodeValue2275, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4871 node4871Labels = Sparse.eval nodeValue4871 (mixedVector B) := by
  have h := singleton4871 B _hB
  rw [sound2112 B _hB _hF, sound2287 B _hB _hF] at h
  norm_num [nodeValue4871, nodeValue2112, nodeValue2287, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4874 node4874Labels = Sparse.eval nodeValue4874 (mixedVector B) := by
  have h := singleton4874 B _hB
  rw [sound2115 B _hB _hF, sound2276 B _hB _hF] at h
  norm_num [nodeValue4874, nodeValue2115, nodeValue2276, Sparse.eval] at h ⊢
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

theorem sound5456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5456 node5456Labels = Sparse.eval nodeValue5456 (mixedVector B) := by
  have h := singleton5456 B _hB
  rw [sound3916 B _hB _hF] at h
  norm_num [nodeValue5456, nodeValue3916, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources19
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq636 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm636 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA636 + difference 0 1) (sourceB636 + difference 1 0) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA636 + difference 0 1) (sourceB636 + difference 1 0) sourceC636) = raw10769 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10769; decide +kernel
    rw [ha]
    exact (canonical10769 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA636 + difference 0 2) (sourceB636 + difference 2 0) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA636 + difference 0 2) (sourceB636 + difference 2 0) sourceC636) = raw10770 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10770; decide +kernel
    rw [ha]
    exact (canonical10770 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA636 + difference 0 3) (sourceB636 + difference 3 0) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA636 + difference 0 3) (sourceB636 + difference 3 0) sourceC636) = raw10771 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10771; decide +kernel
    rw [ha]
    exact (canonical10771 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA636 + difference 0 4) (sourceB636 + difference 4 0) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5456) := by
    have ha : (tripleCharges (sourceA636 + difference 0 4) (sourceB636 + difference 4 0) sourceC636) = raw10772 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10772; decide +kernel
    rw [ha]
    exact (canonical10772 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA636 + difference 0 5) (sourceB636 + difference 5 0) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA636 + difference 0 5) (sourceB636 + difference 5 0) sourceC636) = raw10773 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10773; decide +kernel
    rw [ha]
    exact (canonical10773 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA636 + difference 1 0) (sourceB636 + difference 0 1) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4276) := by
    have ha : (tripleCharges (sourceA636 + difference 1 0) (sourceB636 + difference 0 1) sourceC636) = raw10774 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10774; decide +kernel
    rw [ha]
    exact (canonical10774 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA636 + difference 1 2) (sourceB636 + difference 2 1) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA636 + difference 1 2) (sourceB636 + difference 2 1) sourceC636) = raw10775 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10775; decide +kernel
    rw [ha]
    exact (canonical10775 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA636 + difference 1 3) (sourceB636 + difference 3 1) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA636 + difference 1 3) (sourceB636 + difference 3 1) sourceC636) = raw10776 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10776; decide +kernel
    rw [ha]
    exact (canonical10776 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA636 + difference 1 4) (sourceB636 + difference 4 1) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA636 + difference 1 4) (sourceB636 + difference 4 1) sourceC636) = raw10777 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10777; decide +kernel
    rw [ha]
    exact (canonical10777 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA636 + difference 1 5) (sourceB636 + difference 5 1) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA636 + difference 1 5) (sourceB636 + difference 5 1) sourceC636) = raw10778 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10778; decide +kernel
    rw [ha]
    exact (canonical10778 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA636 + difference 2 0) (sourceB636 + difference 0 2) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4275) := by
    have ha : (tripleCharges (sourceA636 + difference 2 0) (sourceB636 + difference 0 2) sourceC636) = raw10779 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10779; decide +kernel
    rw [ha]
    exact (canonical10779 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA636 + difference 2 1) (sourceB636 + difference 1 2) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA636 + difference 2 1) (sourceB636 + difference 1 2) sourceC636) = raw10780 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10780; decide +kernel
    rw [ha]
    exact (canonical10780 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA636 + difference 2 3) (sourceB636 + difference 3 2) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4746) := by
    have ha : (tripleCharges (sourceA636 + difference 2 3) (sourceB636 + difference 3 2) sourceC636) = raw10781 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10781; decide +kernel
    rw [ha]
    exact (canonical10781 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA636 + difference 2 4) (sourceB636 + difference 4 2) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA636 + difference 2 4) (sourceB636 + difference 4 2) sourceC636) = raw10782 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10782; decide +kernel
    rw [ha]
    exact (canonical10782 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA636 + difference 2 5) (sourceB636 + difference 5 2) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA636 + difference 2 5) (sourceB636 + difference 5 2) sourceC636) = raw10783 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10783; decide +kernel
    rw [ha]
    exact (canonical10783 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA636 + difference 3 0) (sourceB636 + difference 0 3) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4275) := by
    have ha : (tripleCharges (sourceA636 + difference 3 0) (sourceB636 + difference 0 3) sourceC636) = raw10784 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10784; decide +kernel
    rw [ha]
    exact (canonical10784 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA636 + difference 3 1) (sourceB636 + difference 1 3) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA636 + difference 3 1) (sourceB636 + difference 1 3) sourceC636) = raw10785 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10785; decide +kernel
    rw [ha]
    exact (canonical10785 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA636 + difference 3 2) (sourceB636 + difference 2 3) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4746) := by
    have ha : (tripleCharges (sourceA636 + difference 3 2) (sourceB636 + difference 2 3) sourceC636) = raw10786 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10786; decide +kernel
    rw [ha]
    exact (canonical10786 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA636 + difference 3 4) (sourceB636 + difference 4 3) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA636 + difference 3 4) (sourceB636 + difference 4 3) sourceC636) = raw10787 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10787; decide +kernel
    rw [ha]
    exact (canonical10787 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA636 + difference 3 5) (sourceB636 + difference 5 3) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA636 + difference 3 5) (sourceB636 + difference 5 3) sourceC636) = raw10788 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10788; decide +kernel
    rw [ha]
    exact (canonical10788 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA636 + difference 4 0) (sourceB636 + difference 0 4) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4278) := by
    have ha : (tripleCharges (sourceA636 + difference 4 0) (sourceB636 + difference 0 4) sourceC636) = raw10789 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10789; decide +kernel
    rw [ha]
    exact (canonical10789 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA636 + difference 4 1) (sourceB636 + difference 1 4) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA636 + difference 4 1) (sourceB636 + difference 1 4) sourceC636) = raw10790 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10790; decide +kernel
    rw [ha]
    exact (canonical10790 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA636 + difference 4 2) (sourceB636 + difference 2 4) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4749) := by
    have ha : (tripleCharges (sourceA636 + difference 4 2) (sourceB636 + difference 2 4) sourceC636) = raw10791 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10791; decide +kernel
    rw [ha]
    exact (canonical10791 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA636 + difference 4 3) (sourceB636 + difference 3 4) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4749) := by
    have ha : (tripleCharges (sourceA636 + difference 4 3) (sourceB636 + difference 3 4) sourceC636) = raw10792 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10792; decide +kernel
    rw [ha]
    exact (canonical10792 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA636 + difference 4 5) (sourceB636 + difference 5 4) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA636 + difference 4 5) (sourceB636 + difference 5 4) sourceC636) = raw10793 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10793; decide +kernel
    rw [ha]
    exact (canonical10793 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA636 + difference 5 0) (sourceB636 + difference 0 5) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4276) := by
    have ha : (tripleCharges (sourceA636 + difference 5 0) (sourceB636 + difference 0 5) sourceC636) = raw10794 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10794; decide +kernel
    rw [ha]
    exact (canonical10794 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA636 + difference 5 1) (sourceB636 + difference 1 5) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA636 + difference 5 1) (sourceB636 + difference 1 5) sourceC636) = raw10795 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10795; decide +kernel
    rw [ha]
    exact (canonical10795 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA636 + difference 5 2) (sourceB636 + difference 2 5) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA636 + difference 5 2) (sourceB636 + difference 2 5) sourceC636) = raw10796 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10796; decide +kernel
    rw [ha]
    exact (canonical10796 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA636 + difference 5 3) (sourceB636 + difference 3 5) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA636 + difference 5 3) (sourceB636 + difference 3 5) sourceC636) = raw10797 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10797; decide +kernel
    rw [ha]
    exact (canonical10797 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA636 + difference 5 4) (sourceB636 + difference 4 5) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA636 + difference 5 4) (sourceB636 + difference 4 5) sourceC636) = raw10798 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10798; decide +kernel
    rw [ha]
    exact (canonical10798 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA636 sourceB636 sourceC636
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm636, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck545 : Integer.Sparse.reindex keyMap MixedData.row545 = numericRow545 := by decide +kernel

theorem numericCheck545 (x : Master → ℝ) : Integer.Sparse.eval numericRow545 x =
    (4320 : ℝ) * reducedSource545 x := by
  norm_num [numericRow545, reducedSource545, Integer.Sparse.eval, Sparse.eval, nodeValue4275, nodeValue4276, nodeValue4278, nodeValue4746, nodeValue4747, nodeValue4749, nodeValue4869, nodeValue4871, nodeValue4874, nodeValue4898, nodeValue4899, nodeValue5412, nodeValue5443, nodeValue5456]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero545 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource545 (mixedVector B) = 0 := by
  have h4275 : mixedVector B (Sum.inr 4275) = Sparse.eval nodeValue4275 (mixedVector B) := by
    change mixedMoment B node4275 node4275Labels = _
    exact sound4275 B hB hF
  have h4276 : mixedVector B (Sum.inr 4276) = Sparse.eval nodeValue4276 (mixedVector B) := by
    change mixedMoment B node4276 node4276Labels = _
    exact sound4276 B hB hF
  have h4278 : mixedVector B (Sum.inr 4278) = Sparse.eval nodeValue4278 (mixedVector B) := by
    change mixedMoment B node4278 node4278Labels = _
    exact sound4278 B hB hF
  have h4746 : mixedVector B (Sum.inr 4746) = Sparse.eval nodeValue4746 (mixedVector B) := by
    change mixedMoment B node4746 node4746Labels = _
    exact sound4746 B hB hF
  have h4747 : mixedVector B (Sum.inr 4747) = Sparse.eval nodeValue4747 (mixedVector B) := by
    change mixedMoment B node4747 node4747Labels = _
    exact sound4747 B hB hF
  have h4749 : mixedVector B (Sum.inr 4749) = Sparse.eval nodeValue4749 (mixedVector B) := by
    change mixedMoment B node4749 node4749Labels = _
    exact sound4749 B hB hF
  have h4869 : mixedVector B (Sum.inr 4869) = Sparse.eval nodeValue4869 (mixedVector B) := by
    change mixedMoment B node4869 node4869Labels = _
    exact sound4869 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h4874 : mixedVector B (Sum.inr 4874) = Sparse.eval nodeValue4874 (mixedVector B) := by
    change mixedMoment B node4874 node4874Labels = _
    exact sound4874 B hB hF
  have h4898 : mixedVector B (Sum.inr 4898) = Sparse.eval nodeValue4898 (mixedVector B) := by
    change mixedMoment B node4898 node4898Labels = _
    exact sound4898 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  have h5412 : mixedVector B (Sum.inr 5412) = Sparse.eval nodeValue5412 (mixedVector B) := by
    change mixedMoment B node5412 node5412Labels = _
    exact sound5412 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  have h5456 : mixedVector B (Sum.inr 5456) = Sparse.eval nodeValue5456 (mixedVector B) := by
    change mixedMoment B node5456 node5456Labels = _
    exact sound5456 B hB hF
  simpa only [sourceForm636, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4275, h4276, h4278, h4746, h4747, h4749, h4869, h4871, h4874, h4898, h4899, h5412, h5443, h5456, reducedSource545] using sourceEq636 B hB

theorem rowSound545_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row545 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck545, numericCheck545, reducedZero545 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e_oai
