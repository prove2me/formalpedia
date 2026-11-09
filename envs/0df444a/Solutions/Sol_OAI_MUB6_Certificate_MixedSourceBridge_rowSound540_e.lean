-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T01:50:17.814465+00:00
-- url     : https://prove2.me/submissions/5cef205d-ff9f-4eea-ab6d-fd9532ebe5f7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E110
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw380 raw380Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw380 raw380Labels = mixedMoment B raw380step0 raw380step0Labels := by
      have ha : raw380step0 = (fun i j => raw380 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw380step0 raw380; decide +kernel
      have hl : raw380step0Labels = raw380Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw380 raw380Labels permutation8 permutation5
    mixedMoment B raw380step0 raw380step0Labels = mixedMoment B raw380step1 raw380step1Labels := by
      have ha : raw380step1 = raw380step0 := by apply Matrix.ext; unfold raw380step1 raw380step0; decide +kernel
      have hl : raw380step0Labels = labelEmbedding1 ∘ raw380step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw380step0 raw380step0Labels raw380step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3101 node3101Labels := by rfl

theorem canonical381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw381 raw381Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw381 raw381Labels = mixedMoment B raw381step0 raw381step0Labels := by
      have ha : raw381step0 = (fun i j => raw381 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw381step0 raw381; decide +kernel
      have hl : raw381step0Labels = raw381Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw381 raw381Labels permutation8 permutation4
    _ = mixedMoment B node405 node405Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10642 raw10642Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw10642 raw10642Labels = mixedMoment B raw10642step0 raw10642step0Labels := by
      have hz : ∀ j, raw10642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10642step0 = (fun i j => raw10642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10642step0 raw10642; decide +kernel
      have hl : raw10642step0Labels = raw10642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10642 raw10642Labels permutation346 hz
    mixedMoment B raw10642step0 raw10642step0Labels = mixedMoment B raw10642step1 raw10642step1Labels := by
      have ha : raw10642step1 = (fun i j => raw10642step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10642step1 raw10642step0; decide +kernel
      have hl : raw10642step1Labels = raw10642step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10642step0 raw10642step0Labels permutation149 permutation7
    mixedMoment B raw10642step1 raw10642step1Labels = mixedMoment B raw10642step2 raw10642step2Labels := by
      have ha : raw10642step2 = raw10642step1 := by apply Matrix.ext; unfold raw10642step2 raw10642step1; decide +kernel
      have hl : raw10642step1Labels = labelEmbedding1 ∘ raw10642step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10642step1 raw10642step1Labels raw10642step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical10643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10643 raw10643Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw10643 raw10643Labels = mixedMoment B raw10643step0 raw10643step0Labels := by
      have hz : ∀ j, raw10643 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10643step0 = (fun i j => raw10643 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10643step0 raw10643; decide +kernel
      have hl : raw10643step0Labels = raw10643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10643 raw10643Labels permutation265 hz
    mixedMoment B raw10643step0 raw10643step0Labels = mixedMoment B raw10643step1 raw10643step1Labels := by
      have ha : raw10643step1 = (fun i j => raw10643step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10643step1 raw10643step0; decide +kernel
      have hl : raw10643step1Labels = raw10643step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10643step0 raw10643step0Labels permutation149 permutation7
    mixedMoment B raw10643step1 raw10643step1Labels = mixedMoment B raw10643step2 raw10643step2Labels := by
      have ha : raw10643step2 = raw10643step1 := by apply Matrix.ext; unfold raw10643step2 raw10643step1; decide +kernel
      have hl : raw10643step1Labels = labelEmbedding1 ∘ raw10643step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10643step1 raw10643step1Labels raw10643step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical10644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10644 raw10644Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw10644 raw10644Labels = mixedMoment B raw10644step0 raw10644step0Labels := by
      have hz : ∀ j, raw10644 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10644step0 = (fun i j => raw10644 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10644step0 raw10644; decide +kernel
      have hl : raw10644step0Labels = raw10644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10644 raw10644Labels permutation346 hz
    mixedMoment B raw10644step0 raw10644step0Labels = mixedMoment B raw10644step1 raw10644step1Labels := by
      have hz : ∀ j, raw10644step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10644step1 = (fun i j => raw10644step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10644step1 raw10644step0; decide +kernel
      have hl : raw10644step1Labels = raw10644step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10644step0 raw10644step0Labels permutation56 hz
    mixedMoment B raw10644step1 raw10644step1Labels = mixedMoment B raw10644step2 raw10644step2Labels := by
      have ha : raw10644step2 = (fun i j => raw10644step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10644step2 raw10644step1; decide +kernel
      have hl : raw10644step2Labels = raw10644step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10644step1 raw10644step1Labels permutation31 permutation7
    mixedMoment B raw10644step2 raw10644step2Labels = mixedMoment B raw10644step3 raw10644step3Labels := by
      have ha : raw10644step3 = raw10644step2 := by apply Matrix.ext; unfold raw10644step3 raw10644step2; decide +kernel
      have hl : raw10644step2Labels = labelEmbedding1 ∘ raw10644step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10644step2 raw10644step2Labels raw10644step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

theorem canonical10645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10645 raw10645Labels = mixedMoment B node2786 node2786Labels := by
  calc
    mixedMoment B raw10645 raw10645Labels = mixedMoment B raw10645step0 raw10645step0Labels := by
      have hz : ∀ j, raw10645 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10645step0 = (fun i j => raw10645 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10645step0 raw10645; decide +kernel
      have hl : raw10645step0Labels = raw10645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10645 raw10645Labels permutation520 hz
    mixedMoment B raw10645step0 raw10645step0Labels = mixedMoment B raw10645step1 raw10645step1Labels := by
      have hz : ∀ j, raw10645step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10645step1 = (fun i j => raw10645step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10645step1 raw10645step0; decide +kernel
      have hl : raw10645step1Labels = raw10645step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10645step0 raw10645step0Labels permutation80 hz
    mixedMoment B raw10645step1 raw10645step1Labels = mixedMoment B raw10645step2 raw10645step2Labels := by
      have hz : ∀ j, raw10645step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10645step2 = (fun i j => raw10645step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10645step2 raw10645step1; decide +kernel
      have hl : raw10645step2Labels = raw10645step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10645step1 raw10645step1Labels permutation14 hz
    mixedMoment B raw10645step2 raw10645step2Labels = mixedMoment B raw10645step3 raw10645step3Labels := by
      have ha : raw10645step3 = (fun i j => raw10645step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10645step3 raw10645step2; decide +kernel
      have hl : raw10645step3Labels = raw10645step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10645step2 raw10645step2Labels permutation7 permutation7
    mixedMoment B raw10645step3 raw10645step3Labels = mixedMoment B raw10645step4 raw10645step4Labels := by
      have ha : raw10645step4 = raw10645step3 := by apply Matrix.ext; unfold raw10645step4 raw10645step3; decide +kernel
      have hl : raw10645step3Labels = labelEmbedding1 ∘ raw10645step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10645step3 raw10645step3Labels raw10645step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2786 node2786Labels := by rfl

theorem canonical10646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10646 raw10646Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw10646 raw10646Labels = mixedMoment B raw10646step0 raw10646step0Labels := by
      have hz : ∀ j, raw10646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10646step0 = (fun i j => raw10646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10646step0 raw10646; decide +kernel
      have hl : raw10646step0Labels = raw10646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10646 raw10646Labels permutation346 hz
    mixedMoment B raw10646step0 raw10646step0Labels = mixedMoment B raw10646step1 raw10646step1Labels := by
      have hz : ∀ j, raw10646step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10646step1 = (fun i j => raw10646step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10646step1 raw10646step0; decide +kernel
      have hl : raw10646step1Labels = raw10646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10646step0 raw10646step0Labels permutation56 hz
    mixedMoment B raw10646step1 raw10646step1Labels = mixedMoment B raw10646step2 raw10646step2Labels := by
      have ha : raw10646step2 = (fun i j => raw10646step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10646step2 raw10646step1; decide +kernel
      have hl : raw10646step2Labels = raw10646step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10646step1 raw10646step1Labels permutation31 permutation7
    mixedMoment B raw10646step2 raw10646step2Labels = mixedMoment B raw10646step3 raw10646step3Labels := by
      have ha : raw10646step3 = raw10646step2 := by apply Matrix.ext; unfold raw10646step3 raw10646step2; decide +kernel
      have hl : raw10646step2Labels = labelEmbedding1 ∘ raw10646step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10646step2 raw10646step2Labels raw10646step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3101 node3101Labels := by rfl

theorem canonical10647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10647 raw10647Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw10647 raw10647Labels = mixedMoment B raw10647step0 raw10647step0Labels := by
      have hz : ∀ j, raw10647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10647step0 = (fun i j => raw10647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10647step0 raw10647; decide +kernel
      have hl : raw10647step0Labels = raw10647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10647 raw10647Labels permutation346 hz
    mixedMoment B raw10647step0 raw10647step0Labels = mixedMoment B raw10647step1 raw10647step1Labels := by
      have ha : raw10647step1 = (fun i j => raw10647step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10647step1 raw10647step0; decide +kernel
      have hl : raw10647step1Labels = raw10647step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10647step0 raw10647step0Labels permutation139 permutation7
    mixedMoment B raw10647step1 raw10647step1Labels = mixedMoment B raw10647step2 raw10647step2Labels := by
      have ha : raw10647step2 = raw10647step1 := by apply Matrix.ext; unfold raw10647step2 raw10647step1; decide +kernel
      have hl : raw10647step1Labels = labelEmbedding1 ∘ raw10647step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10647step1 raw10647step1Labels raw10647step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

theorem canonical10648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10648 raw10648Labels = mixedMoment B node2693 node2693Labels := by
  calc
    mixedMoment B raw10648 raw10648Labels = mixedMoment B raw10648step0 raw10648step0Labels := by
      have ha : raw10648step0 = (fun i j => raw10648 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10648step0 raw10648; decide +kernel
      have hl : raw10648step0Labels = raw10648Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10648 raw10648Labels permutation620 permutation7
    mixedMoment B raw10648step0 raw10648step0Labels = mixedMoment B raw10648step1 raw10648step1Labels := by
      have ha : raw10648step1 = raw10648step0 := by apply Matrix.ext; unfold raw10648step1 raw10648step0; decide +kernel
      have hl : raw10648step0Labels = labelEmbedding1 ∘ raw10648step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10648step0 raw10648step0Labels raw10648step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2693 node2693Labels := by rfl

theorem canonical10649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10649 raw10649Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw10649 raw10649Labels = mixedMoment B raw10649step0 raw10649step0Labels := by
      have hz : ∀ j, raw10649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10649step0 = (fun i j => raw10649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10649step0 raw10649; decide +kernel
      have hl : raw10649step0Labels = raw10649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10649 raw10649Labels permutation346 hz
    mixedMoment B raw10649step0 raw10649step0Labels = mixedMoment B raw10649step1 raw10649step1Labels := by
      have ha : raw10649step1 = (fun i j => raw10649step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10649step1 raw10649step0; decide +kernel
      have hl : raw10649step1Labels = raw10649step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10649step0 raw10649step0Labels permutation139 permutation7
    mixedMoment B raw10649step1 raw10649step1Labels = mixedMoment B raw10649step2 raw10649step2Labels := by
      have ha : raw10649step2 = raw10649step1 := by apply Matrix.ext; unfold raw10649step2 raw10649step1; decide +kernel
      have hl : raw10649step1Labels = labelEmbedding1 ∘ raw10649step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10649step1 raw10649step1Labels raw10649step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

theorem canonical10650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10650 raw10650Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw10650 raw10650Labels = mixedMoment B raw10650step0 raw10650step0Labels := by
      have hz : ∀ j, raw10650 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10650step0 = (fun i j => raw10650 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10650step0 raw10650; decide +kernel
      have hl : raw10650step0Labels = raw10650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10650 raw10650Labels permutation520 hz
    mixedMoment B raw10650step0 raw10650step0Labels = mixedMoment B raw10650step1 raw10650step1Labels := by
      have hz : ∀ j, raw10650step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10650step1 = (fun i j => raw10650step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10650step1 raw10650step0; decide +kernel
      have hl : raw10650step1Labels = raw10650step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10650step0 raw10650step0Labels permutation80 hz
    mixedMoment B raw10650step1 raw10650step1Labels = mixedMoment B raw10650step2 raw10650step2Labels := by
      have ha : raw10650step2 = (fun i j => raw10650step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10650step2 raw10650step1; decide +kernel
      have hl : raw10650step2Labels = raw10650step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10650step1 raw10650step1Labels permutation29 permutation7
    mixedMoment B raw10650step2 raw10650step2Labels = mixedMoment B raw10650step3 raw10650step3Labels := by
      have ha : raw10650step3 = raw10650step2 := by apply Matrix.ext; unfold raw10650step3 raw10650step2; decide +kernel
      have hl : raw10650step2Labels = labelEmbedding1 ∘ raw10650step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10650step2 raw10650step2Labels raw10650step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical10651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10651 raw10651Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw10651 raw10651Labels = mixedMoment B raw10651step0 raw10651step0Labels := by
      have hz : ∀ j, raw10651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10651step0 = (fun i j => raw10651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10651step0 raw10651; decide +kernel
      have hl : raw10651step0Labels = raw10651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10651 raw10651Labels permutation346 hz
    mixedMoment B raw10651step0 raw10651step0Labels = mixedMoment B raw10651step1 raw10651step1Labels := by
      have ha : raw10651step1 = (fun i j => raw10651step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10651step1 raw10651step0; decide +kernel
      have hl : raw10651step1Labels = raw10651step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10651step0 raw10651step0Labels permutation139 permutation7
    mixedMoment B raw10651step1 raw10651step1Labels = mixedMoment B raw10651step2 raw10651step2Labels := by
      have ha : raw10651step2 = raw10651step1 := by apply Matrix.ext; unfold raw10651step2 raw10651step1; decide +kernel
      have hl : raw10651step1Labels = labelEmbedding1 ∘ raw10651step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10651step1 raw10651step1Labels raw10651step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

theorem canonical10652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10652 raw10652Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw10652 raw10652Labels = mixedMoment B raw10652step0 raw10652step0Labels := by
      have hz : ∀ j, raw10652 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10652step0 = (fun i j => raw10652 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10652step0 raw10652; decide +kernel
      have hl : raw10652step0Labels = raw10652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10652 raw10652Labels permutation265 hz
    mixedMoment B raw10652step0 raw10652step0Labels = mixedMoment B raw10652step1 raw10652step1Labels := by
      have ha : raw10652step1 = (fun i j => raw10652step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10652step1 raw10652step0; decide +kernel
      have hl : raw10652step1Labels = raw10652step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10652step0 raw10652step0Labels permutation139 permutation7
    mixedMoment B raw10652step1 raw10652step1Labels = mixedMoment B raw10652step2 raw10652step2Labels := by
      have ha : raw10652step2 = raw10652step1 := by apply Matrix.ext; unfold raw10652step2 raw10652step1; decide +kernel
      have hl : raw10652step1Labels = labelEmbedding1 ∘ raw10652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10652step1 raw10652step1Labels raw10652step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

theorem canonical10653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10653 raw10653Labels = mixedMoment B node2693 node2693Labels := by
  calc
    mixedMoment B raw10653 raw10653Labels = mixedMoment B raw10653step0 raw10653step0Labels := by
      have ha : raw10653step0 = (fun i j => raw10653 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10653step0 raw10653; decide +kernel
      have hl : raw10653step0Labels = raw10653Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10653 raw10653Labels permutation644 permutation7
    mixedMoment B raw10653step0 raw10653step0Labels = mixedMoment B raw10653step1 raw10653step1Labels := by
      have ha : raw10653step1 = raw10653step0 := by apply Matrix.ext; unfold raw10653step1 raw10653step0; decide +kernel
      have hl : raw10653step0Labels = labelEmbedding1 ∘ raw10653step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10653step0 raw10653step0Labels raw10653step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2693 node2693Labels := by rfl

theorem canonical10654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10654 raw10654Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw10654 raw10654Labels = mixedMoment B raw10654step0 raw10654step0Labels := by
      have hz : ∀ j, raw10654 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10654step0 = (fun i j => raw10654 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10654step0 raw10654; decide +kernel
      have hl : raw10654step0Labels = raw10654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10654 raw10654Labels permutation265 hz
    mixedMoment B raw10654step0 raw10654step0Labels = mixedMoment B raw10654step1 raw10654step1Labels := by
      have ha : raw10654step1 = (fun i j => raw10654step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10654step1 raw10654step0; decide +kernel
      have hl : raw10654step1Labels = raw10654step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10654step0 raw10654step0Labels permutation139 permutation7
    mixedMoment B raw10654step1 raw10654step1Labels = mixedMoment B raw10654step2 raw10654step2Labels := by
      have ha : raw10654step2 = raw10654step1 := by apply Matrix.ext; unfold raw10654step2 raw10654step1; decide +kernel
      have hl : raw10654step1Labels = labelEmbedding1 ∘ raw10654step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10654step1 raw10654step1Labels raw10654step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

theorem canonical10655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10655 raw10655Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw10655 raw10655Labels = mixedMoment B raw10655step0 raw10655step0Labels := by
      have hz : ∀ j, raw10655 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10655step0 = (fun i j => raw10655 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10655step0 raw10655; decide +kernel
      have hl : raw10655step0Labels = raw10655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10655 raw10655Labels permutation520 hz
    mixedMoment B raw10655step0 raw10655step0Labels = mixedMoment B raw10655step1 raw10655step1Labels := by
      have hz : ∀ j, raw10655step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10655step1 = (fun i j => raw10655step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10655step1 raw10655step0; decide +kernel
      have hl : raw10655step1Labels = raw10655step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10655step0 raw10655step0Labels permutation56 hz
    mixedMoment B raw10655step1 raw10655step1Labels = mixedMoment B raw10655step2 raw10655step2Labels := by
      have ha : raw10655step2 = (fun i j => raw10655step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10655step2 raw10655step1; decide +kernel
      have hl : raw10655step2Labels = raw10655step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10655step1 raw10655step1Labels permutation29 permutation7
    mixedMoment B raw10655step2 raw10655step2Labels = mixedMoment B raw10655step3 raw10655step3Labels := by
      have ha : raw10655step3 = raw10655step2 := by apply Matrix.ext; unfold raw10655step3 raw10655step2; decide +kernel
      have hl : raw10655step2Labels = labelEmbedding1 ∘ raw10655step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10655step2 raw10655step2Labels raw10655step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical10656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10656 raw10656Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw10656 raw10656Labels = mixedMoment B raw10656step0 raw10656step0Labels := by
      have hz : ∀ j, raw10656 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10656step0 = (fun i j => raw10656 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10656step0 raw10656; decide +kernel
      have hl : raw10656step0Labels = raw10656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10656 raw10656Labels permutation265 hz
    mixedMoment B raw10656step0 raw10656step0Labels = mixedMoment B raw10656step1 raw10656step1Labels := by
      have ha : raw10656step1 = (fun i j => raw10656step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10656step1 raw10656step0; decide +kernel
      have hl : raw10656step1Labels = raw10656step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10656step0 raw10656step0Labels permutation139 permutation7
    mixedMoment B raw10656step1 raw10656step1Labels = mixedMoment B raw10656step2 raw10656step2Labels := by
      have ha : raw10656step2 = raw10656step1 := by apply Matrix.ext; unfold raw10656step2 raw10656step1; decide +kernel
      have hl : raw10656step1Labels = labelEmbedding1 ∘ raw10656step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10656step1 raw10656step1Labels raw10656step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

theorem canonical10657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10657 raw10657Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw10657 raw10657Labels = mixedMoment B raw10657step0 raw10657step0Labels := by
      have hz : ∀ j, raw10657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10657step0 = (fun i j => raw10657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10657step0 raw10657; decide +kernel
      have hl : raw10657step0Labels = raw10657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10657 raw10657Labels permutation346 hz
    mixedMoment B raw10657step0 raw10657step0Labels = mixedMoment B raw10657step1 raw10657step1Labels := by
      have hz : ∀ j, raw10657step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10657step1 = (fun i j => raw10657step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10657step1 raw10657step0; decide +kernel
      have hl : raw10657step1Labels = raw10657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10657step0 raw10657step0Labels permutation56 hz
    mixedMoment B raw10657step1 raw10657step1Labels = mixedMoment B raw10657step2 raw10657step2Labels := by
      have ha : raw10657step2 = (fun i j => raw10657step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10657step2 raw10657step1; decide +kernel
      have hl : raw10657step2Labels = raw10657step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10657step1 raw10657step1Labels permutation31 permutation7
    mixedMoment B raw10657step2 raw10657step2Labels = mixedMoment B raw10657step3 raw10657step3Labels := by
      have ha : raw10657step3 = raw10657step2 := by apply Matrix.ext; unfold raw10657step3 raw10657step2; decide +kernel
      have hl : raw10657step2Labels = labelEmbedding1 ∘ raw10657step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10657step2 raw10657step2Labels raw10657step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

theorem canonical10658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10658 raw10658Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10658 raw10658Labels = mixedMoment B raw10658step0 raw10658step0Labels := by
      have hz : ∀ j, raw10658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10658step0 = (fun i j => raw10658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10658step0 raw10658; decide +kernel
      have hl : raw10658step0Labels = raw10658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10658 raw10658Labels permutation346 hz
    mixedMoment B raw10658step0 raw10658step0Labels = mixedMoment B raw10658step1 raw10658step1Labels := by
      have ha : raw10658step1 = (fun i j => raw10658step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10658step1 raw10658step0; decide +kernel
      have hl : raw10658step1Labels = raw10658step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10658step0 raw10658step0Labels permutation149 permutation7
    mixedMoment B raw10658step1 raw10658step1Labels = mixedMoment B raw10658step2 raw10658step2Labels := by
      have ha : raw10658step2 = raw10658step1 := by apply Matrix.ext; unfold raw10658step2 raw10658step1; decide +kernel
      have hl : raw10658step1Labels = labelEmbedding1 ∘ raw10658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10658step1 raw10658step1Labels raw10658step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

theorem canonical10659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10659 raw10659Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10659 raw10659Labels = mixedMoment B raw10659step0 raw10659step0Labels := by
      have hz : ∀ j, raw10659 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10659step0 = (fun i j => raw10659 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10659step0 raw10659; decide +kernel
      have hl : raw10659step0Labels = raw10659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10659 raw10659Labels permutation265 hz
    mixedMoment B raw10659step0 raw10659step0Labels = mixedMoment B raw10659step1 raw10659step1Labels := by
      have ha : raw10659step1 = (fun i j => raw10659step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10659step1 raw10659step0; decide +kernel
      have hl : raw10659step1Labels = raw10659step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10659step0 raw10659step0Labels permutation149 permutation7
    mixedMoment B raw10659step1 raw10659step1Labels = mixedMoment B raw10659step2 raw10659step2Labels := by
      have ha : raw10659step2 = raw10659step1 := by apply Matrix.ext; unfold raw10659step2 raw10659step1; decide +kernel
      have hl : raw10659step1Labels = labelEmbedding1 ∘ raw10659step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10659step1 raw10659step1Labels raw10659step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

theorem canonical10660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10660 raw10660Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw10660 raw10660Labels = mixedMoment B raw10660step0 raw10660step0Labels := by
      have hz : ∀ j, raw10660 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10660step0 = (fun i j => raw10660 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10660step0 raw10660; decide +kernel
      have hl : raw10660step0Labels = raw10660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10660 raw10660Labels permutation520 hz
    mixedMoment B raw10660step0 raw10660step0Labels = mixedMoment B raw10660step1 raw10660step1Labels := by
      have hz : ∀ j, raw10660step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10660step1 = (fun i j => raw10660step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10660step1 raw10660step0; decide +kernel
      have hl : raw10660step1Labels = raw10660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10660step0 raw10660step0Labels permutation80 hz
    mixedMoment B raw10660step1 raw10660step1Labels = mixedMoment B raw10660step2 raw10660step2Labels := by
      have hz : ∀ j, raw10660step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10660step2 = (fun i j => raw10660step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10660step2 raw10660step1; decide +kernel
      have hl : raw10660step2Labels = raw10660step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10660step1 raw10660step1Labels permutation14 hz
    mixedMoment B raw10660step2 raw10660step2Labels = mixedMoment B raw10660step3 raw10660step3Labels := by
      have ha : raw10660step3 = (fun i j => raw10660step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10660step3 raw10660step2; decide +kernel
      have hl : raw10660step3Labels = raw10660step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10660step2 raw10660step2Labels permutation7 permutation7
    mixedMoment B raw10660step3 raw10660step3Labels = mixedMoment B raw10660step4 raw10660step4Labels := by
      have ha : raw10660step4 = raw10660step3 := by apply Matrix.ext; unfold raw10660step4 raw10660step3; decide +kernel
      have hl : raw10660step3Labels = labelEmbedding1 ∘ raw10660step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10660step3 raw10660step3Labels raw10660step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2783 node2783Labels := by rfl

theorem canonical10661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10661 raw10661Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw10661 raw10661Labels = mixedMoment B raw10661step0 raw10661step0Labels := by
      have hz : ∀ j, raw10661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10661step0 = (fun i j => raw10661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10661step0 raw10661; decide +kernel
      have hl : raw10661step0Labels = raw10661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10661 raw10661Labels permutation346 hz
    mixedMoment B raw10661step0 raw10661step0Labels = mixedMoment B raw10661step1 raw10661step1Labels := by
      have hz : ∀ j, raw10661step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10661step1 = (fun i j => raw10661step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10661step1 raw10661step0; decide +kernel
      have hl : raw10661step1Labels = raw10661step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10661step0 raw10661step0Labels permutation56 hz
    mixedMoment B raw10661step1 raw10661step1Labels = mixedMoment B raw10661step2 raw10661step2Labels := by
      have ha : raw10661step2 = (fun i j => raw10661step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10661step2 raw10661step1; decide +kernel
      have hl : raw10661step2Labels = raw10661step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10661step1 raw10661step1Labels permutation31 permutation7
    mixedMoment B raw10661step2 raw10661step2Labels = mixedMoment B raw10661step3 raw10661step3Labels := by
      have ha : raw10661step3 = raw10661step2 := by apply Matrix.ext; unfold raw10661step3 raw10661step2; decide +kernel
      have hl : raw10661step2Labels = labelEmbedding1 ∘ raw10661step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10661step2 raw10661step2Labels raw10661step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

theorem canonical10662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10662 raw10662Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw10662 raw10662Labels = mixedMoment B raw10662step0 raw10662step0Labels := by
      have hz : ∀ j, raw10662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10662step0 = (fun i j => raw10662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10662step0 raw10662; decide +kernel
      have hl : raw10662step0Labels = raw10662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10662 raw10662Labels permutation346 hz
    mixedMoment B raw10662step0 raw10662step0Labels = mixedMoment B raw10662step1 raw10662step1Labels := by
      have hz : ∀ j, raw10662step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10662step1 = (fun i j => raw10662step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10662step1 raw10662step0; decide +kernel
      have hl : raw10662step1Labels = raw10662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10662step0 raw10662step0Labels permutation56 hz
    mixedMoment B raw10662step1 raw10662step1Labels = mixedMoment B raw10662step2 raw10662step2Labels := by
      have ha : raw10662step2 = (fun i j => raw10662step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10662step2 raw10662step1; decide +kernel
      have hl : raw10662step2Labels = raw10662step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10662step1 raw10662step1Labels permutation31 permutation7
    mixedMoment B raw10662step2 raw10662step2Labels = mixedMoment B raw10662step3 raw10662step3Labels := by
      have ha : raw10662step3 = raw10662step2 := by apply Matrix.ext; unfold raw10662step3 raw10662step2; decide +kernel
      have hl : raw10662step2Labels = labelEmbedding1 ∘ raw10662step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10662step2 raw10662step2Labels raw10662step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2683 node2683Labels := by rfl

theorem canonical10663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10663 raw10663Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw10663 raw10663Labels = mixedMoment B raw10663step0 raw10663step0Labels := by
      have hz : ∀ j, raw10663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10663step0 = (fun i j => raw10663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10663step0 raw10663; decide +kernel
      have hl : raw10663step0Labels = raw10663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10663 raw10663Labels permutation346 hz
    mixedMoment B raw10663step0 raw10663step0Labels = mixedMoment B raw10663step1 raw10663step1Labels := by
      have ha : raw10663step1 = (fun i j => raw10663step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10663step1 raw10663step0; decide +kernel
      have hl : raw10663step1Labels = raw10663step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10663step0 raw10663step0Labels permutation149 permutation7
    mixedMoment B raw10663step1 raw10663step1Labels = mixedMoment B raw10663step2 raw10663step2Labels := by
      have ha : raw10663step2 = raw10663step1 := by apply Matrix.ext; unfold raw10663step2 raw10663step1; decide +kernel
      have hl : raw10663step1Labels = labelEmbedding1 ∘ raw10663step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10663step1 raw10663step1Labels raw10663step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

theorem canonical10664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10664 raw10664Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw10664 raw10664Labels = mixedMoment B raw10664step0 raw10664step0Labels := by
      have hz : ∀ j, raw10664 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10664step0 = (fun i j => raw10664 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10664step0 raw10664; decide +kernel
      have hl : raw10664step0Labels = raw10664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10664 raw10664Labels permutation265 hz
    mixedMoment B raw10664step0 raw10664step0Labels = mixedMoment B raw10664step1 raw10664step1Labels := by
      have ha : raw10664step1 = (fun i j => raw10664step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10664step1 raw10664step0; decide +kernel
      have hl : raw10664step1Labels = raw10664step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10664step0 raw10664step0Labels permutation149 permutation7
    mixedMoment B raw10664step1 raw10664step1Labels = mixedMoment B raw10664step2 raw10664step2Labels := by
      have ha : raw10664step2 = raw10664step1 := by apply Matrix.ext; unfold raw10664step2 raw10664step1; decide +kernel
      have hl : raw10664step1Labels = labelEmbedding1 ∘ raw10664step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10664step1 raw10664step1Labels raw10664step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

theorem canonical10665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10665 raw10665Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw10665 raw10665Labels = mixedMoment B raw10665step0 raw10665step0Labels := by
      have hz : ∀ j, raw10665 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10665step0 = (fun i j => raw10665 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10665step0 raw10665; decide +kernel
      have hl : raw10665step0Labels = raw10665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10665 raw10665Labels permutation346 hz
    mixedMoment B raw10665step0 raw10665step0Labels = mixedMoment B raw10665step1 raw10665step1Labels := by
      have hz : ∀ j, raw10665step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10665step1 = (fun i j => raw10665step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10665step1 raw10665step0; decide +kernel
      have hl : raw10665step1Labels = raw10665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10665step0 raw10665step0Labels permutation56 hz
    mixedMoment B raw10665step1 raw10665step1Labels = mixedMoment B raw10665step2 raw10665step2Labels := by
      have ha : raw10665step2 = (fun i j => raw10665step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10665step2 raw10665step1; decide +kernel
      have hl : raw10665step2Labels = raw10665step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10665step1 raw10665step1Labels permutation31 permutation7
    mixedMoment B raw10665step2 raw10665step2Labels = mixedMoment B raw10665step3 raw10665step3Labels := by
      have ha : raw10665step3 = raw10665step2 := by apply Matrix.ext; unfold raw10665step3 raw10665step2; decide +kernel
      have hl : raw10665step2Labels = labelEmbedding1 ∘ raw10665step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10665step2 raw10665step2Labels raw10665step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2685 node2685Labels := by rfl

theorem canonical10666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10666 raw10666Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw10666 raw10666Labels = mixedMoment B raw10666step0 raw10666step0Labels := by
      have hz : ∀ j, raw10666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10666step0 = (fun i j => raw10666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10666step0 raw10666; decide +kernel
      have hl : raw10666step0Labels = raw10666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10666 raw10666Labels permutation346 hz
    mixedMoment B raw10666step0 raw10666step0Labels = mixedMoment B raw10666step1 raw10666step1Labels := by
      have hz : ∀ j, raw10666step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10666step1 = (fun i j => raw10666step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10666step1 raw10666step0; decide +kernel
      have hl : raw10666step1Labels = raw10666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10666step0 raw10666step0Labels permutation56 hz
    mixedMoment B raw10666step1 raw10666step1Labels = mixedMoment B raw10666step2 raw10666step2Labels := by
      have ha : raw10666step2 = (fun i j => raw10666step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10666step2 raw10666step1; decide +kernel
      have hl : raw10666step2Labels = raw10666step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10666step1 raw10666step1Labels permutation31 permutation7
    mixedMoment B raw10666step2 raw10666step2Labels = mixedMoment B raw10666step3 raw10666step3Labels := by
      have ha : raw10666step3 = raw10666step2 := by apply Matrix.ext; unfold raw10666step3 raw10666step2; decide +kernel
      have hl : raw10666step2Labels = labelEmbedding1 ∘ raw10666step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10666step2 raw10666step2Labels raw10666step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3052 node3052Labels := by rfl

theorem canonical10667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10667 raw10667Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw10667 raw10667Labels = mixedMoment B raw10667step0 raw10667step0Labels := by
      have hz : ∀ j, raw10667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10667step0 = (fun i j => raw10667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10667step0 raw10667; decide +kernel
      have hl : raw10667step0Labels = raw10667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10667 raw10667Labels permutation346 hz
    mixedMoment B raw10667step0 raw10667step0Labels = mixedMoment B raw10667step1 raw10667step1Labels := by
      have hz : ∀ j, raw10667step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10667step1 = (fun i j => raw10667step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10667step1 raw10667step0; decide +kernel
      have hl : raw10667step1Labels = raw10667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10667step0 raw10667step0Labels permutation56 hz
    mixedMoment B raw10667step1 raw10667step1Labels = mixedMoment B raw10667step2 raw10667step2Labels := by
      have ha : raw10667step2 = (fun i j => raw10667step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10667step2 raw10667step1; decide +kernel
      have hl : raw10667step2Labels = raw10667step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10667step1 raw10667step1Labels permutation31 permutation7
    mixedMoment B raw10667step2 raw10667step2Labels = mixedMoment B raw10667step3 raw10667step3Labels := by
      have ha : raw10667step3 = raw10667step2 := by apply Matrix.ext; unfold raw10667step3 raw10667step2; decide +kernel
      have hl : raw10667step2Labels = labelEmbedding1 ∘ raw10667step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10667step2 raw10667step2Labels raw10667step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical10668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10668 raw10668Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw10668 raw10668Labels = mixedMoment B raw10668step0 raw10668step0Labels := by
      have hz : ∀ j, raw10668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10668step0 = (fun i j => raw10668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10668step0 raw10668; decide +kernel
      have hl : raw10668step0Labels = raw10668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10668 raw10668Labels permutation346 hz
    mixedMoment B raw10668step0 raw10668step0Labels = mixedMoment B raw10668step1 raw10668step1Labels := by
      have ha : raw10668step1 = (fun i j => raw10668step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10668step1 raw10668step0; decide +kernel
      have hl : raw10668step1Labels = raw10668step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10668step0 raw10668step0Labels permutation149 permutation7
    mixedMoment B raw10668step1 raw10668step1Labels = mixedMoment B raw10668step2 raw10668step2Labels := by
      have ha : raw10668step2 = raw10668step1 := by apply Matrix.ext; unfold raw10668step2 raw10668step1; decide +kernel
      have hl : raw10668step1Labels = labelEmbedding1 ∘ raw10668step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10668step1 raw10668step1Labels raw10668step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical10669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10669 raw10669Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw10669 raw10669Labels = mixedMoment B raw10669step0 raw10669step0Labels := by
      have hz : ∀ j, raw10669 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10669step0 = (fun i j => raw10669 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10669step0 raw10669; decide +kernel
      have hl : raw10669step0Labels = raw10669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10669 raw10669Labels permutation265 hz
    mixedMoment B raw10669step0 raw10669step0Labels = mixedMoment B raw10669step1 raw10669step1Labels := by
      have ha : raw10669step1 = (fun i j => raw10669step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10669step1 raw10669step0; decide +kernel
      have hl : raw10669step1Labels = raw10669step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10669step0 raw10669step0Labels permutation149 permutation7
    mixedMoment B raw10669step1 raw10669step1Labels = mixedMoment B raw10669step2 raw10669step2Labels := by
      have ha : raw10669step2 = raw10669step1 := by apply Matrix.ext; unfold raw10669step2 raw10669step1; decide +kernel
      have hl : raw10669step1Labels = labelEmbedding1 ∘ raw10669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10669step1 raw10669step1Labels raw10669step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical10670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10670 raw10670Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw10670 raw10670Labels = mixedMoment B raw10670step0 raw10670step0Labels := by
      have hz : ∀ j, raw10670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10670step0 = (fun i j => raw10670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10670step0 raw10670; decide +kernel
      have hl : raw10670step0Labels = raw10670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10670 raw10670Labels permutation346 hz
    mixedMoment B raw10670step0 raw10670step0Labels = mixedMoment B raw10670step1 raw10670step1Labels := by
      have hz : ∀ j, raw10670step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10670step1 = (fun i j => raw10670step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10670step1 raw10670step0; decide +kernel
      have hl : raw10670step1Labels = raw10670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10670step0 raw10670step0Labels permutation56 hz
    mixedMoment B raw10670step1 raw10670step1Labels = mixedMoment B raw10670step2 raw10670step2Labels := by
      have ha : raw10670step2 = (fun i j => raw10670step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10670step2 raw10670step1; decide +kernel
      have hl : raw10670step2Labels = raw10670step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10670step1 raw10670step1Labels permutation31 permutation7
    mixedMoment B raw10670step2 raw10670step2Labels = mixedMoment B raw10670step3 raw10670step3Labels := by
      have ha : raw10670step3 = raw10670step2 := by apply Matrix.ext; unfold raw10670step3 raw10670step2; decide +kernel
      have hl : raw10670step2Labels = labelEmbedding1 ∘ raw10670step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10670step2 raw10670step2Labels raw10670step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

theorem canonical10671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10671 raw10671Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw10671 raw10671Labels = mixedMoment B raw10671step0 raw10671step0Labels := by
      have hz : ∀ j, raw10671 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10671step0 = (fun i j => raw10671 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10671step0 raw10671; decide +kernel
      have hl : raw10671step0Labels = raw10671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10671 raw10671Labels permutation520 hz
    mixedMoment B raw10671step0 raw10671step0Labels = mixedMoment B raw10671step1 raw10671step1Labels := by
      have hz : ∀ j, raw10671step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10671step1 = (fun i j => raw10671step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10671step1 raw10671step0; decide +kernel
      have hl : raw10671step1Labels = raw10671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10671step0 raw10671step0Labels permutation80 hz
    mixedMoment B raw10671step1 raw10671step1Labels = mixedMoment B raw10671step2 raw10671step2Labels := by
      have hz : ∀ j, raw10671step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10671step2 = (fun i j => raw10671step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10671step2 raw10671step1; decide +kernel
      have hl : raw10671step2Labels = raw10671step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10671step1 raw10671step1Labels permutation14 hz
    mixedMoment B raw10671step2 raw10671step2Labels = mixedMoment B raw10671step3 raw10671step3Labels := by
      have ha : raw10671step3 = (fun i j => raw10671step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10671step3 raw10671step2; decide +kernel
      have hl : raw10671step3Labels = raw10671step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10671step2 raw10671step2Labels permutation7 permutation7
    mixedMoment B raw10671step3 raw10671step3Labels = mixedMoment B raw10671step4 raw10671step4Labels := by
      have ha : raw10671step4 = raw10671step3 := by apply Matrix.ext; unfold raw10671step4 raw10671step3; decide +kernel
      have hl : raw10671step3Labels = labelEmbedding1 ∘ raw10671step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10671step3 raw10671step3Labels raw10671step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2292 node2292Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7671 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7671 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7671 = injectiveMoment H raw7671step0 := by
      have hz : ∀ j, raw7671 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7671step0 = (fun i j => raw7671 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7671 permutation21 hz
    injectiveMoment H raw7671step0 = injectiveMoment H raw7671step1 := by
      have heq : raw7671step1 = (fun i j => raw7671step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7671step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

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

theorem canonical782 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw782 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw782 = injectiveMoment H raw782step0 := by
      have heq : raw782step0 = -raw782 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw782).symm
    injectiveMoment H raw782step0 = injectiveMoment H raw782step1 := by
      have heq : raw782step1 = (fun i j => raw782step0 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw782step0 permutation13 permutation8
    _ = injectiveMoment H node185 := by rfl

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

theorem canonical2863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2863 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2863 = injectiveMoment H raw2863step0 := by
      have heq : raw2863step0 = (fun i j => raw2863 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2863 permutation4 permutation5
    _ = injectiveMoment H node56 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5979 = injectiveMoment H node57 := by
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

theorem sound185 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node185 = Sparse.eval value185 (momentVector H) := by
  have heq : pivotMatrix185 = (fun u v => node185 (pivotPermutation185 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node185 = injectiveMoment H pivotMatrix185 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix185 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix185 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (0 : Fin 3) = raw5979 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (1 : Fin 3) = raw2863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2863 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node185 + (injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value185, value36, value56, value57, Sparse.eval] at hc ⊢
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

theorem singlePair405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node405 node405Labels = Sparse.eval singlePairValue405 (familyPairVector B) := by
  have hp := single_label_three B hB node405
  have hl : node405Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node405 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 1) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node405 PairSemantics.raw5204; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 2) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node405 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node405 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value185 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 4) = PairSemantics.raw782 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node405 PairSemantics.raw782; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical782 hH).trans (PairSemantics.sound185 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue405, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value185, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3101 node3101Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node405 node405Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw380 singletonSmall3101
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3101) = raw380Labels := by decide +kernel
  rw [hl, canonical380 B hB] at h
  have hc0 : mixedMoment B raw380 (Fin.cases (0 : Fin 1) singletonSmall3101) =
      mixedMoment B node405 node405Labels := by
    have ha : raw380 = raw381 := by apply Matrix.ext; unfold raw380 raw381; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3101 = raw381Labels := by decide +kernel
    rw [ha, hj, canonical381 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem zero2292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = 0 := by
  exact mixedMoment_order_one B hB node2292 node2292Labels 1
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

theorem sound2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = Sparse.eval nodeValue2292 (mixedVector B) := by
  simpa only [nodeValue2292, Sparse.eval_nil] using zero2292 B _hB _hF

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

theorem sound2670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2670 node2670Labels = Sparse.eval nodeValue2670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2670) = mixedMoment B node2670 node2670Labels := rfl
  simpa [nodeValue2670, Sparse.eval] using hc.symm

theorem sound2683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2683 node2683Labels = Sparse.eval nodeValue2683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2683) = mixedMoment B node2683 node2683Labels := rfl
  simpa [nodeValue2683, Sparse.eval] using hc.symm

theorem sound2685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2685 node2685Labels = Sparse.eval nodeValue2685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2685) = mixedMoment B node2685 node2685Labels := rfl
  simpa [nodeValue2685, Sparse.eval] using hc.symm

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

theorem zero2693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2693 node2693Labels = 0 := by
  exact mixedMoment_alpha B hF node2693 node2693Labels 1 permutation213
    (by decide +kernel)

theorem zero2742 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = 0 := by
  exact mixedMoment_order_one B hB node2742 node2742Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2693 node2693Labels = Sparse.eval nodeValue2693 (mixedVector B) := by
  simpa only [nodeValue2693, Sparse.eval_nil] using zero2693 B _hB _hF

theorem sound2702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2702 node2702Labels = Sparse.eval nodeValue2702 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2702) = mixedMoment B node2702 node2702Labels := rfl
  simpa [nodeValue2702, Sparse.eval] using hc.symm

theorem sound2704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2704 node2704Labels = Sparse.eval nodeValue2704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2704) = mixedMoment B node2704 node2704Labels := rfl
  simpa [nodeValue2704, Sparse.eval] using hc.symm

theorem sound2719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2719 node2719Labels = Sparse.eval nodeValue2719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2719) = mixedMoment B node2719 node2719Labels := rfl
  simpa [nodeValue2719, Sparse.eval] using hc.symm

theorem sound2722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2722 node2722Labels = Sparse.eval nodeValue2722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2722) = mixedMoment B node2722 node2722Labels := rfl
  simpa [nodeValue2722, Sparse.eval] using hc.symm

theorem sound2737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2737 node2737Labels = Sparse.eval nodeValue2737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2737) = mixedMoment B node2737 node2737Labels := rfl
  simpa [nodeValue2737, Sparse.eval] using hc.symm

theorem sound2740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2740 node2740Labels = Sparse.eval nodeValue2740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2740) = mixedMoment B node2740 node2740Labels := rfl
  simpa [nodeValue2740, Sparse.eval] using hc.symm

theorem sound2742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = Sparse.eval nodeValue2742 (mixedVector B) := by
  simpa only [nodeValue2742, Sparse.eval_nil] using zero2742 B _hB _hF

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

theorem sound405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node405 node405Labels = Sparse.eval nodeValue405 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue405 (familyPairVector B) := singlePair405 B _hB
    _ = _ := by
      norm_num [singlePairValue405, nodeValue405, Sparse.eval, mixedVector]
      ring

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3052 node3052Labels = Sparse.eval nodeValue3052 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3052) = mixedMoment B node3052 node3052Labels := rfl
  simpa [nodeValue3052, Sparse.eval] using hc.symm

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

theorem sound3075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3075 node3075Labels = Sparse.eval nodeValue3075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3075) = mixedMoment B node3075 node3075Labels := rfl
  simpa [nodeValue3075, Sparse.eval] using hc.symm

theorem sound3098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3098 node3098Labels = Sparse.eval nodeValue3098 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3098) = mixedMoment B node3098 node3098Labels := rfl
  simpa [nodeValue3098, Sparse.eval] using hc.symm

theorem sound3101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3101 node3101Labels = Sparse.eval nodeValue3101 (mixedVector B) := by
  have h := singleton3101 B _hB
  rw [sound405 B _hB _hF] at h
  norm_num [nodeValue3101, nodeValue405, Sparse.eval] at h ⊢
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

theorem sourceEq631 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm631 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA631 + difference 0 1) (sourceB631 + difference 1 0) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA631 + difference 0 1) (sourceB631 + difference 1 0) sourceC631) = raw10642 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10642; decide +kernel
    rw [ha]
    exact (canonical10642 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA631 + difference 0 2) (sourceB631 + difference 2 0) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA631 + difference 0 2) (sourceB631 + difference 2 0) sourceC631) = raw10643 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10643; decide +kernel
    rw [ha]
    exact (canonical10643 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA631 + difference 0 3) (sourceB631 + difference 3 0) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA631 + difference 0 3) (sourceB631 + difference 3 0) sourceC631) = raw10644 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10644; decide +kernel
    rw [ha]
    exact (canonical10644 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA631 + difference 0 4) (sourceB631 + difference 4 0) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2786) := by
    have ha : (tripleCharges (sourceA631 + difference 0 4) (sourceB631 + difference 4 0) sourceC631) = raw10645 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10645; decide +kernel
    rw [ha]
    exact (canonical10645 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA631 + difference 0 5) (sourceB631 + difference 5 0) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA631 + difference 0 5) (sourceB631 + difference 5 0) sourceC631) = raw10646 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10646; decide +kernel
    rw [ha]
    exact (canonical10646 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA631 + difference 1 0) (sourceB631 + difference 0 1) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA631 + difference 1 0) (sourceB631 + difference 0 1) sourceC631) = raw10647 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10647; decide +kernel
    rw [ha]
    exact (canonical10647 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA631 + difference 1 2) (sourceB631 + difference 2 1) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2693) := by
    have ha : (tripleCharges (sourceA631 + difference 1 2) (sourceB631 + difference 2 1) sourceC631) = raw10648 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10648; decide +kernel
    rw [ha]
    exact (canonical10648 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA631 + difference 1 3) (sourceB631 + difference 3 1) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA631 + difference 1 3) (sourceB631 + difference 3 1) sourceC631) = raw10649 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10649; decide +kernel
    rw [ha]
    exact (canonical10649 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA631 + difference 1 4) (sourceB631 + difference 4 1) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA631 + difference 1 4) (sourceB631 + difference 4 1) sourceC631) = raw10650 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10650; decide +kernel
    rw [ha]
    exact (canonical10650 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA631 + difference 1 5) (sourceB631 + difference 5 1) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA631 + difference 1 5) (sourceB631 + difference 5 1) sourceC631) = raw10651 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10651; decide +kernel
    rw [ha]
    exact (canonical10651 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA631 + difference 2 0) (sourceB631 + difference 0 2) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA631 + difference 2 0) (sourceB631 + difference 0 2) sourceC631) = raw10652 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10652; decide +kernel
    rw [ha]
    exact (canonical10652 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA631 + difference 2 1) (sourceB631 + difference 1 2) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2693) := by
    have ha : (tripleCharges (sourceA631 + difference 2 1) (sourceB631 + difference 1 2) sourceC631) = raw10653 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10653; decide +kernel
    rw [ha]
    exact (canonical10653 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA631 + difference 2 3) (sourceB631 + difference 3 2) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA631 + difference 2 3) (sourceB631 + difference 3 2) sourceC631) = raw10654 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10654; decide +kernel
    rw [ha]
    exact (canonical10654 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA631 + difference 2 4) (sourceB631 + difference 4 2) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA631 + difference 2 4) (sourceB631 + difference 4 2) sourceC631) = raw10655 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10655; decide +kernel
    rw [ha]
    exact (canonical10655 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA631 + difference 2 5) (sourceB631 + difference 5 2) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA631 + difference 2 5) (sourceB631 + difference 5 2) sourceC631) = raw10656 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10656; decide +kernel
    rw [ha]
    exact (canonical10656 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA631 + difference 3 0) (sourceB631 + difference 0 3) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA631 + difference 3 0) (sourceB631 + difference 0 3) sourceC631) = raw10657 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10657; decide +kernel
    rw [ha]
    exact (canonical10657 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA631 + difference 3 1) (sourceB631 + difference 1 3) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA631 + difference 3 1) (sourceB631 + difference 1 3) sourceC631) = raw10658 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10658; decide +kernel
    rw [ha]
    exact (canonical10658 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA631 + difference 3 2) (sourceB631 + difference 2 3) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA631 + difference 3 2) (sourceB631 + difference 2 3) sourceC631) = raw10659 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10659; decide +kernel
    rw [ha]
    exact (canonical10659 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA631 + difference 3 4) (sourceB631 + difference 4 3) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA631 + difference 3 4) (sourceB631 + difference 4 3) sourceC631) = raw10660 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10660; decide +kernel
    rw [ha]
    exact (canonical10660 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA631 + difference 3 5) (sourceB631 + difference 5 3) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA631 + difference 3 5) (sourceB631 + difference 5 3) sourceC631) = raw10661 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10661; decide +kernel
    rw [ha]
    exact (canonical10661 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA631 + difference 4 0) (sourceB631 + difference 0 4) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA631 + difference 4 0) (sourceB631 + difference 0 4) sourceC631) = raw10662 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10662; decide +kernel
    rw [ha]
    exact (canonical10662 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA631 + difference 4 1) (sourceB631 + difference 1 4) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA631 + difference 4 1) (sourceB631 + difference 1 4) sourceC631) = raw10663 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10663; decide +kernel
    rw [ha]
    exact (canonical10663 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA631 + difference 4 2) (sourceB631 + difference 2 4) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA631 + difference 4 2) (sourceB631 + difference 2 4) sourceC631) = raw10664 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10664; decide +kernel
    rw [ha]
    exact (canonical10664 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA631 + difference 4 3) (sourceB631 + difference 3 4) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA631 + difference 4 3) (sourceB631 + difference 3 4) sourceC631) = raw10665 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10665; decide +kernel
    rw [ha]
    exact (canonical10665 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA631 + difference 4 5) (sourceB631 + difference 5 4) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA631 + difference 4 5) (sourceB631 + difference 5 4) sourceC631) = raw10666 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10666; decide +kernel
    rw [ha]
    exact (canonical10666 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA631 + difference 5 0) (sourceB631 + difference 0 5) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA631 + difference 5 0) (sourceB631 + difference 0 5) sourceC631) = raw10667 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10667; decide +kernel
    rw [ha]
    exact (canonical10667 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA631 + difference 5 1) (sourceB631 + difference 1 5) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA631 + difference 5 1) (sourceB631 + difference 1 5) sourceC631) = raw10668 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10668; decide +kernel
    rw [ha]
    exact (canonical10668 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA631 + difference 5 2) (sourceB631 + difference 2 5) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA631 + difference 5 2) (sourceB631 + difference 2 5) sourceC631) = raw10669 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10669; decide +kernel
    rw [ha]
    exact (canonical10669 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA631 + difference 5 3) (sourceB631 + difference 3 5) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA631 + difference 5 3) (sourceB631 + difference 3 5) sourceC631) = raw10670 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10670; decide +kernel
    rw [ha]
    exact (canonical10670 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA631 + difference 5 4) (sourceB631 + difference 4 5) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA631 + difference 5 4) (sourceB631 + difference 4 5) sourceC631) = raw10671 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10671; decide +kernel
    rw [ha]
    exact (canonical10671 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA631 sourceB631 sourceC631
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm631, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck540 : Integer.Sparse.reindex keyMap MixedData.row540 = numericRow540 := by decide +kernel

theorem numericCheck540 (x : Master → ℝ) : Integer.Sparse.eval numericRow540 x =
    (2160 : ℝ) * reducedSource540 x := by
  norm_num [numericRow540, reducedSource540, Integer.Sparse.eval, Sparse.eval, nodeValue2203, nodeValue2226, nodeValue2228, nodeValue2292, nodeValue2670, nodeValue2683, nodeValue2685, nodeValue2693, nodeValue2702, nodeValue2704, nodeValue2719, nodeValue2722, nodeValue2737, nodeValue2740, nodeValue2742, nodeValue2783, nodeValue2786, nodeValue3052, nodeValue3075, nodeValue3098, nodeValue3101]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero540 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource540 (mixedVector B) = 0 := by
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h2693 : mixedVector B (Sum.inr 2693) = Sparse.eval nodeValue2693 (mixedVector B) := by
    change mixedMoment B node2693 node2693Labels = _
    exact sound2693 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h2719 : mixedVector B (Sum.inr 2719) = Sparse.eval nodeValue2719 (mixedVector B) := by
    change mixedMoment B node2719 node2719Labels = _
    exact sound2719 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  have h2786 : mixedVector B (Sum.inr 2786) = Sparse.eval nodeValue2786 (mixedVector B) := by
    change mixedMoment B node2786 node2786Labels = _
    exact sound2786 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  simpa only [sourceForm631, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2203, h2226, h2228, h2292, h2670, h2683, h2685, h2693, h2702, h2704, h2719, h2722, h2737, h2740, h2742, h2783, h2786, h3052, h3075, h3098, h3101, reducedSource540] using sourceEq631 B hB

theorem rowSound540_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row540 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck540, numericCheck540, reducedZero540 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e_oai
