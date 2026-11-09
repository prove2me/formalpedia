-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T01:08:20.58689+00:00
-- url     : https://prove2.me/submissions/049ee0e8-f476-4d86-bcd6-2062716f915b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3995_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw254 raw254Labels = mixedMoment B node2637 node2637Labels := by
  calc
    mixedMoment B raw254 raw254Labels = mixedMoment B raw254step0 raw254step0Labels := by
      have ha : raw254step0 = (fun i j => raw254 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw254step0 raw254; decide +kernel
      have hl : raw254step0Labels = raw254Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw254 raw254Labels permutation32 permutation5
    mixedMoment B raw254step0 raw254step0Labels = mixedMoment B raw254step1 raw254step1Labels := by
      have ha : raw254step1 = raw254step0 := by apply Matrix.ext; unfold raw254step1 raw254step0; decide +kernel
      have hl : raw254step0Labels = labelEmbedding1 ∘ raw254step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw254step0 raw254step0Labels raw254step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2637 node2637Labels := by rfl

theorem canonical255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw255 raw255Labels = mixedMoment B node352 node352Labels := by
  calc
    mixedMoment B raw255 raw255Labels = mixedMoment B raw255step0 raw255step0Labels := by
      have ha : raw255step0 = (fun i j => raw255 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw255step0 raw255; decide +kernel
      have hl : raw255step0Labels = raw255Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw255 raw255Labels permutation32 permutation5
    _ = mixedMoment B node352 node352Labels := by rfl

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

theorem canonical276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw276 raw276Labels = mixedMoment B node2775 node2775Labels := by
  calc
    mixedMoment B raw276 raw276Labels = mixedMoment B raw276step0 raw276step0Labels := by
      have ha : raw276step0 = (fun i j => raw276 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw276step0 raw276; decide +kernel
      have hl : raw276step0Labels = raw276Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw276 raw276Labels permutation32 permutation5
    mixedMoment B raw276step0 raw276step0Labels = mixedMoment B raw276step1 raw276step1Labels := by
      have ha : raw276step1 = raw276step0 := by apply Matrix.ext; unfold raw276step1 raw276step0; decide +kernel
      have hl : raw276step0Labels = labelEmbedding1 ∘ raw276step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw276step0 raw276step0Labels raw276step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2775 node2775Labels := by rfl

theorem canonical277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw277 raw277Labels = mixedMoment B node411 node411Labels := by
  calc
    mixedMoment B raw277 raw277Labels = mixedMoment B raw277step0 raw277step0Labels := by
      have ha : raw277step0 = (fun i j => raw277 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw277step0 raw277; decide +kernel
      have hl : raw277step0Labels = raw277Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw277 raw277Labels permutation32 permutation5
    _ = mixedMoment B node411 node411Labels := by rfl

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

theorem canonical542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw542 raw542Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw542 raw542Labels = mixedMoment B raw542step0 raw542step0Labels := by
      have ha : raw542step0 = (fun i j => raw542 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw542step0 raw542; decide +kernel
      have hl : raw542step0Labels = raw542Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw542 raw542Labels permutation32 permutation5
    mixedMoment B raw542step0 raw542step0Labels = mixedMoment B raw542step1 raw542step1Labels := by
      have ha : raw542step1 = raw542step0 := by apply Matrix.ext; unfold raw542step1 raw542step0; decide +kernel
      have hl : raw542step0Labels = labelEmbedding1 ∘ raw542step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw542step0 raw542step0Labels raw542step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3887 node3887Labels := by rfl

theorem canonical543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw543 raw543Labels = mixedMoment B node502 node502Labels := by
  calc
    mixedMoment B raw543 raw543Labels = mixedMoment B raw543step0 raw543step0Labels := by
      have ha : raw543step0 = (fun i j => raw543 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw543step0 raw543; decide +kernel
      have hl : raw543step0Labels = raw543Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw543 raw543Labels permutation32 permutation5
    _ = mixedMoment B node502 node502Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6608 raw6608Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw6608 raw6608Labels = mixedMoment B raw6608step0 raw6608step0Labels := by
      have hz : ∀ j, raw6608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6608step0 = (fun i j => raw6608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6608step0 raw6608; decide +kernel
      have hl : raw6608step0Labels = raw6608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6608 raw6608Labels permutation346 hz
    mixedMoment B raw6608step0 raw6608step0Labels = mixedMoment B raw6608step1 raw6608step1Labels := by
      have ha : raw6608step1 = (fun i j => raw6608step0 (permutation85 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6608step1 raw6608step0; decide +kernel
      have hl : raw6608step1Labels = raw6608step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6608step0 raw6608step0Labels permutation85 permutation6
    mixedMoment B raw6608step1 raw6608step1Labels = mixedMoment B raw6608step2 raw6608step2Labels := by
      have ha : raw6608step2 = -raw6608step1 := by apply Matrix.ext; change ∀ i j, raw6608step2 i j = -(raw6608step1 i j); unfold raw6608step2 raw6608step1; decide +kernel
      have hl : raw6608step2Labels = raw6608step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3884 node3884Labels := by rfl

theorem canonical6609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6609 raw6609Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw6609 raw6609Labels = mixedMoment B raw6609step0 raw6609step0Labels := by
      have ha : raw6609step0 = (fun i j => raw6609 (permutation442 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6609step0 raw6609; decide +kernel
      have hl : raw6609step0Labels = raw6609Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6609 raw6609Labels permutation442 permutation6
    mixedMoment B raw6609step0 raw6609step0Labels = mixedMoment B raw6609step1 raw6609step1Labels := by
      have ha : raw6609step1 = -raw6609step0 := by apply Matrix.ext; change ∀ i j, raw6609step1 i j = -(raw6609step0 i j); unfold raw6609step1 raw6609step0; decide +kernel
      have hl : raw6609step1Labels = raw6609step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3880 node3880Labels := by rfl

theorem canonical6610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6610 raw6610Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw6610 raw6610Labels = mixedMoment B raw6610step0 raw6610step0Labels := by
      have hz : ∀ j, raw6610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6610step0 = (fun i j => raw6610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6610step0 raw6610; decide +kernel
      have hl : raw6610step0Labels = raw6610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6610 raw6610Labels permutation346 hz
    mixedMoment B raw6610step0 raw6610step0Labels = mixedMoment B raw6610step1 raw6610step1Labels := by
      have ha : raw6610step1 = (fun i j => raw6610step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6610step1 raw6610step0; decide +kernel
      have hl : raw6610step1Labels = raw6610step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6610step0 raw6610step0Labels permutation149 permutation3
    mixedMoment B raw6610step1 raw6610step1Labels = mixedMoment B raw6610step2 raw6610step2Labels := by
      have ha : raw6610step2 = -raw6610step1 := by apply Matrix.ext; change ∀ i j, raw6610step2 i j = -(raw6610step1 i j); unfold raw6610step2 raw6610step1; decide +kernel
      have hl : raw6610step2Labels = raw6610step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3995 node3995Labels := by rfl

theorem canonical6611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6611 raw6611Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw6611 raw6611Labels = mixedMoment B raw6611step0 raw6611step0Labels := by
      have hz : ∀ j, raw6611 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6611step0 = (fun i j => raw6611 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6611step0 raw6611; decide +kernel
      have hl : raw6611step0Labels = raw6611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6611 raw6611Labels permutation346 hz
    mixedMoment B raw6611step0 raw6611step0Labels = mixedMoment B raw6611step1 raw6611step1Labels := by
      have ha : raw6611step1 = (fun i j => raw6611step0 (permutation84 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6611step1 raw6611step0; decide +kernel
      have hl : raw6611step1Labels = raw6611step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6611step0 raw6611step0Labels permutation84 permutation6
    mixedMoment B raw6611step1 raw6611step1Labels = mixedMoment B raw6611step2 raw6611step2Labels := by
      have ha : raw6611step2 = -raw6611step1 := by apply Matrix.ext; change ∀ i j, raw6611step2 i j = -(raw6611step1 i j); unfold raw6611step2 raw6611step1; decide +kernel
      have hl : raw6611step2Labels = raw6611step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3885 node3885Labels := by rfl

theorem canonical6612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6612 raw6612Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw6612 raw6612Labels = mixedMoment B raw6612step0 raw6612step0Labels := by
      have hz : ∀ j, raw6612 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6612step0 = (fun i j => raw6612 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6612step0 raw6612; decide +kernel
      have hl : raw6612step0Labels = raw6612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6612 raw6612Labels permutation346 hz
    mixedMoment B raw6612step0 raw6612step0Labels = mixedMoment B raw6612step1 raw6612step1Labels := by
      have ha : raw6612step1 = (fun i j => raw6612step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6612step1 raw6612step0; decide +kernel
      have hl : raw6612step1Labels = raw6612step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6612step0 raw6612step0Labels permutation83 permutation6
    mixedMoment B raw6612step1 raw6612step1Labels = mixedMoment B raw6612step2 raw6612step2Labels := by
      have ha : raw6612step2 = -raw6612step1 := by apply Matrix.ext; change ∀ i j, raw6612step2 i j = -(raw6612step1 i j); unfold raw6612step2 raw6612step1; decide +kernel
      have hl : raw6612step2Labels = raw6612step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3887 node3887Labels := by rfl

theorem canonical6613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6613 raw6613Labels = mixedMoment B node1057 node1057Labels := by
  calc
    mixedMoment B raw6613 raw6613Labels = mixedMoment B raw6613step0 raw6613step0Labels := by
      have hz : ∀ j, raw6613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6613step0 = (fun i j => raw6613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6613step0 raw6613; decide +kernel
      have hl : raw6613step0Labels = raw6613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6613 raw6613Labels permutation346 hz
    mixedMoment B raw6613step0 raw6613step0Labels = mixedMoment B raw6613step1 raw6613step1Labels := by
      have ha : raw6613step1 = (fun i j => raw6613step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6613step1 raw6613step0; decide +kernel
      have hl : raw6613step1Labels = raw6613step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6613step0 raw6613step0Labels permutation38 permutation3
    _ = mixedMoment B node1057 node1057Labels := by rfl

theorem canonical6614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6614 raw6614Labels = mixedMoment B node2493 node2493Labels := by
  calc
    mixedMoment B raw6614 raw6614Labels = mixedMoment B raw6614step0 raw6614step0Labels := by
      have ha : raw6614step0 = (fun i j => raw6614 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6614step0 raw6614; decide +kernel
      have hl : raw6614step0Labels = raw6614Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6614 raw6614Labels permutation182 permutation3
    _ = mixedMoment B node2493 node2493Labels := by rfl

theorem canonical6615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6615 raw6615Labels = mixedMoment B node2637 node2637Labels := by
  calc
    mixedMoment B raw6615 raw6615Labels = mixedMoment B raw6615step0 raw6615step0Labels := by
      have hz : ∀ j, raw6615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6615step0 = (fun i j => raw6615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6615step0 raw6615; decide +kernel
      have hl : raw6615step0Labels = raw6615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6615 raw6615Labels permutation346 hz
    mixedMoment B raw6615step0 raw6615step0Labels = mixedMoment B raw6615step1 raw6615step1Labels := by
      have ha : raw6615step1 = (fun i j => raw6615step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6615step1 raw6615step0; decide +kernel
      have hl : raw6615step1Labels = raw6615step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6615step0 raw6615step0Labels permutation38 permutation3
    _ = mixedMoment B node2637 node2637Labels := by rfl

theorem canonical6616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6616 raw6616Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw6616 raw6616Labels = mixedMoment B raw6616step0 raw6616step0Labels := by
      have hz : ∀ j, raw6616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6616step0 = (fun i j => raw6616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6616step0 raw6616; decide +kernel
      have hl : raw6616step0Labels = raw6616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6616 raw6616Labels permutation346 hz
    mixedMoment B raw6616step0 raw6616step0Labels = mixedMoment B raw6616step1 raw6616step1Labels := by
      have ha : raw6616step1 = (fun i j => raw6616step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6616step1 raw6616step0; decide +kernel
      have hl : raw6616step1Labels = raw6616step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6616step0 raw6616step0Labels permutation46 permutation3
    _ = mixedMoment B node2731 node2731Labels := by rfl

theorem canonical6617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6617 raw6617Labels = mixedMoment B node2775 node2775Labels := by
  calc
    mixedMoment B raw6617 raw6617Labels = mixedMoment B raw6617step0 raw6617step0Labels := by
      have hz : ∀ j, raw6617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6617step0 = (fun i j => raw6617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6617step0 raw6617; decide +kernel
      have hl : raw6617step0Labels = raw6617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6617 raw6617Labels permutation346 hz
    mixedMoment B raw6617step0 raw6617step0Labels = mixedMoment B raw6617step1 raw6617step1Labels := by
      have ha : raw6617step1 = (fun i j => raw6617step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6617step1 raw6617step0; decide +kernel
      have hl : raw6617step1Labels = raw6617step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6617step0 raw6617step0Labels permutation38 permutation3
    _ = mixedMoment B node2775 node2775Labels := by rfl

theorem canonical6618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6618 raw6618Labels = mixedMoment B node988 node988Labels := by
  calc
    mixedMoment B raw6618 raw6618Labels = mixedMoment B raw6618step0 raw6618step0Labels := by
      have ha : raw6618step0 = (fun i j => raw6618 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6618step0 raw6618; decide +kernel
      have hl : raw6618step0Labels = raw6618Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6618 raw6618Labels permutation160 permutation3
    _ = mixedMoment B node988 node988Labels := by rfl

theorem canonical6619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6619 raw6619Labels = mixedMoment B node2390 node2390Labels := by
  calc
    mixedMoment B raw6619 raw6619Labels = mixedMoment B raw6619step0 raw6619step0Labels := by
      have ha : raw6619step0 = (fun i j => raw6619 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6619step0 raw6619; decide +kernel
      have hl : raw6619step0Labels = raw6619Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6619 raw6619Labels permutation160 permutation3
    _ = mixedMoment B node2390 node2390Labels := by rfl

theorem canonical6620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6620 raw6620Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw6620 raw6620Labels = mixedMoment B raw6620step0 raw6620step0Labels := by
      have ha : raw6620step0 = (fun i j => raw6620 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6620step0 raw6620; decide +kernel
      have hl : raw6620step0Labels = raw6620Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6620 raw6620Labels permutation202 permutation3
    _ = mixedMoment B node2615 node2615Labels := by rfl

theorem canonical6621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6621 raw6621Labels = mixedMoment B node2698 node2698Labels := by
  calc
    mixedMoment B raw6621 raw6621Labels = mixedMoment B raw6621step0 raw6621step0Labels := by
      have ha : raw6621step0 = (fun i j => raw6621 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6621step0 raw6621; decide +kernel
      have hl : raw6621step0Labels = raw6621Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6621 raw6621Labels permutation166 permutation3
    _ = mixedMoment B node2698 node2698Labels := by rfl

theorem canonical6622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6622 raw6622Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw6622 raw6622Labels = mixedMoment B raw6622step0 raw6622step0Labels := by
      have ha : raw6622step0 = (fun i j => raw6622 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6622step0 raw6622; decide +kernel
      have hl : raw6622step0Labels = raw6622Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6622 raw6622Labels permutation161 permutation3
    _ = mixedMoment B node2730 node2730Labels := by rfl

theorem canonical6623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6623 raw6623Labels = mixedMoment B node1001 node1001Labels := by
  calc
    mixedMoment B raw6623 raw6623Labels = mixedMoment B raw6623step0 raw6623step0Labels := by
      have hz : ∀ j, raw6623 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6623step0 = (fun i j => raw6623 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6623step0 raw6623; decide +kernel
      have hl : raw6623step0Labels = raw6623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6623 raw6623Labels permutation346 hz
    mixedMoment B raw6623step0 raw6623step0Labels = mixedMoment B raw6623step1 raw6623step1Labels := by
      have ha : raw6623step1 = (fun i j => raw6623step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6623step1 raw6623step0; decide +kernel
      have hl : raw6623step1Labels = raw6623step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6623step0 raw6623step0Labels permutation34 permutation3
    _ = mixedMoment B node1001 node1001Labels := by rfl

theorem canonical6624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6624 raw6624Labels = mixedMoment B node2401 node2401Labels := by
  calc
    mixedMoment B raw6624 raw6624Labels = mixedMoment B raw6624step0 raw6624step0Labels := by
      have hz : ∀ j, raw6624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6624step0 = (fun i j => raw6624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6624step0 raw6624; decide +kernel
      have hl : raw6624step0Labels = raw6624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6624 raw6624Labels permutation346 hz
    mixedMoment B raw6624step0 raw6624step0Labels = mixedMoment B raw6624step1 raw6624step1Labels := by
      have ha : raw6624step1 = (fun i j => raw6624step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6624step1 raw6624step0; decide +kernel
      have hl : raw6624step1Labels = raw6624step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6624step0 raw6624step0Labels permutation34 permutation3
    _ = mixedMoment B node2401 node2401Labels := by rfl

theorem canonical6625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6625 raw6625Labels = mixedMoment B node2460 node2460Labels := by
  calc
    mixedMoment B raw6625 raw6625Labels = mixedMoment B raw6625step0 raw6625step0Labels := by
      have ha : raw6625step0 = (fun i j => raw6625 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6625step0 raw6625; decide +kernel
      have hl : raw6625step0Labels = raw6625Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6625 raw6625Labels permutation178 permutation3
    _ = mixedMoment B node2460 node2460Labels := by rfl

theorem canonical6626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6626 raw6626Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw6626 raw6626Labels = mixedMoment B raw6626step0 raw6626step0Labels := by
      have hz : ∀ j, raw6626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6626step0 = (fun i j => raw6626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6626step0 raw6626; decide +kernel
      have hl : raw6626step0Labels = raw6626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6626 raw6626Labels permutation346 hz
    mixedMoment B raw6626step0 raw6626step0Labels = mixedMoment B raw6626step1 raw6626step1Labels := by
      have ha : raw6626step1 = (fun i j => raw6626step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6626step1 raw6626step0; decide +kernel
      have hl : raw6626step1Labels = raw6626step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6626step0 raw6626step0Labels permutation34 permutation3
    _ = mixedMoment B node2706 node2706Labels := by rfl

theorem canonical6627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6627 raw6627Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw6627 raw6627Labels = mixedMoment B raw6627step0 raw6627step0Labels := by
      have hz : ∀ j, raw6627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6627step0 = (fun i j => raw6627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6627step0 raw6627; decide +kernel
      have hl : raw6627step0Labels = raw6627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6627 raw6627Labels permutation346 hz
    mixedMoment B raw6627step0 raw6627step0Labels = mixedMoment B raw6627step1 raw6627step1Labels := by
      have ha : raw6627step1 = (fun i j => raw6627step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6627step1 raw6627step0; decide +kernel
      have hl : raw6627step1Labels = raw6627step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6627step0 raw6627step0Labels permutation35 permutation3
    _ = mixedMoment B node2738 node2738Labels := by rfl

theorem canonical6628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6628 raw6628Labels = mixedMoment B node993 node993Labels := by
  calc
    mixedMoment B raw6628 raw6628Labels = mixedMoment B raw6628step0 raw6628step0Labels := by
      have hz : ∀ j, raw6628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6628step0 = (fun i j => raw6628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6628step0 raw6628; decide +kernel
      have hl : raw6628step0Labels = raw6628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6628 raw6628Labels permutation346 hz
    mixedMoment B raw6628step0 raw6628step0Labels = mixedMoment B raw6628step1 raw6628step1Labels := by
      have ha : raw6628step1 = (fun i j => raw6628step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6628step1 raw6628step0; decide +kernel
      have hl : raw6628step1Labels = raw6628step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6628step0 raw6628step0Labels permutation32 permutation3
    _ = mixedMoment B node993 node993Labels := by rfl

theorem canonical6629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6629 raw6629Labels = mixedMoment B node2395 node2395Labels := by
  calc
    mixedMoment B raw6629 raw6629Labels = mixedMoment B raw6629step0 raw6629step0Labels := by
      have hz : ∀ j, raw6629 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6629step0 = (fun i j => raw6629 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6629step0 raw6629; decide +kernel
      have hl : raw6629step0Labels = raw6629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6629 raw6629Labels permutation346 hz
    mixedMoment B raw6629step0 raw6629step0Labels = mixedMoment B raw6629step1 raw6629step1Labels := by
      have ha : raw6629step1 = (fun i j => raw6629step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6629step1 raw6629step0; decide +kernel
      have hl : raw6629step1Labels = raw6629step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6629step0 raw6629step0Labels permutation32 permutation3
    _ = mixedMoment B node2395 node2395Labels := by rfl

theorem canonical6630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6630 raw6630Labels = mixedMoment B node2456 node2456Labels := by
  calc
    mixedMoment B raw6630 raw6630Labels = mixedMoment B raw6630step0 raw6630step0Labels := by
      have ha : raw6630step0 = (fun i j => raw6630 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6630step0 raw6630; decide +kernel
      have hl : raw6630step0Labels = raw6630Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6630 raw6630Labels permutation176 permutation3
    _ = mixedMoment B node2456 node2456Labels := by rfl

theorem canonical6631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6631 raw6631Labels = mixedMoment B node2621 node2621Labels := by
  calc
    mixedMoment B raw6631 raw6631Labels = mixedMoment B raw6631step0 raw6631step0Labels := by
      have hz : ∀ j, raw6631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6631step0 = (fun i j => raw6631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6631step0 raw6631; decide +kernel
      have hl : raw6631step0Labels = raw6631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6631 raw6631Labels permutation346 hz
    mixedMoment B raw6631step0 raw6631step0Labels = mixedMoment B raw6631step1 raw6631step1Labels := by
      have ha : raw6631step1 = (fun i j => raw6631step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6631step1 raw6631step0; decide +kernel
      have hl : raw6631step1Labels = raw6631step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6631step0 raw6631step0Labels permutation38 permutation3
    _ = mixedMoment B node2621 node2621Labels := by rfl

theorem canonical6632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6632 raw6632Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw6632 raw6632Labels = mixedMoment B raw6632step0 raw6632step0Labels := by
      have hz : ∀ j, raw6632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6632step0 = (fun i j => raw6632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6632step0 raw6632; decide +kernel
      have hl : raw6632step0Labels = raw6632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6632 raw6632Labels permutation346 hz
    mixedMoment B raw6632step0 raw6632step0Labels = mixedMoment B raw6632step1 raw6632step1Labels := by
      have ha : raw6632step1 = (fun i j => raw6632step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6632step1 raw6632step0; decide +kernel
      have hl : raw6632step1Labels = raw6632step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6632step0 raw6632step0Labels permutation33 permutation3
    _ = mixedMoment B node2731 node2731Labels := by rfl

theorem canonical6633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6633 raw6633Labels = mixedMoment B node989 node989Labels := by
  calc
    mixedMoment B raw6633 raw6633Labels = mixedMoment B raw6633step0 raw6633step0Labels := by
      have hz : ∀ j, raw6633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6633step0 = (fun i j => raw6633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6633step0 raw6633; decide +kernel
      have hl : raw6633step0Labels = raw6633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6633 raw6633Labels permutation346 hz
    mixedMoment B raw6633step0 raw6633step0Labels = mixedMoment B raw6633step1 raw6633step1Labels := by
      have ha : raw6633step1 = (fun i j => raw6633step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6633step1 raw6633step0; decide +kernel
      have hl : raw6633step1Labels = raw6633step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6633step0 raw6633step0Labels permutation32 permutation3
    _ = mixedMoment B node989 node989Labels := by rfl

theorem canonical6634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6634 raw6634Labels = mixedMoment B node2391 node2391Labels := by
  calc
    mixedMoment B raw6634 raw6634Labels = mixedMoment B raw6634step0 raw6634step0Labels := by
      have hz : ∀ j, raw6634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6634step0 = (fun i j => raw6634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6634step0 raw6634; decide +kernel
      have hl : raw6634step0Labels = raw6634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6634 raw6634Labels permutation346 hz
    mixedMoment B raw6634step0 raw6634step0Labels = mixedMoment B raw6634step1 raw6634step1Labels := by
      have ha : raw6634step1 = (fun i j => raw6634step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6634step1 raw6634step0; decide +kernel
      have hl : raw6634step1Labels = raw6634step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6634step0 raw6634step0Labels permutation32 permutation3
    _ = mixedMoment B node2391 node2391Labels := by rfl

theorem canonical6635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6635 raw6635Labels = mixedMoment B node2453 node2453Labels := by
  calc
    mixedMoment B raw6635 raw6635Labels = mixedMoment B raw6635step0 raw6635step0Labels := by
      have ha : raw6635step0 = (fun i j => raw6635 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6635step0 raw6635; decide +kernel
      have hl : raw6635step0Labels = raw6635Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6635 raw6635Labels permutation176 permutation3
    _ = mixedMoment B node2453 node2453Labels := by rfl

theorem canonical6636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6636 raw6636Labels = mixedMoment B node2569 node2569Labels := by
  calc
    mixedMoment B raw6636 raw6636Labels = mixedMoment B raw6636step0 raw6636step0Labels := by
      have hz : ∀ j, raw6636 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6636step0 = (fun i j => raw6636 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6636step0 raw6636; decide +kernel
      have hl : raw6636step0Labels = raw6636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6636 raw6636Labels permutation346 hz
    mixedMoment B raw6636step0 raw6636step0Labels = mixedMoment B raw6636step1 raw6636step1Labels := by
      have ha : raw6636step1 = (fun i j => raw6636step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6636step1 raw6636step0; decide +kernel
      have hl : raw6636step1Labels = raw6636step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6636step0 raw6636step0Labels permutation149 permutation3
    mixedMoment B raw6636step1 raw6636step1Labels = mixedMoment B raw6636step2 raw6636step2Labels := by
      have ha : raw6636step2 = -raw6636step1 := by apply Matrix.ext; change ∀ i j, raw6636step2 i j = -(raw6636step1 i j); unfold raw6636step2 raw6636step1; decide +kernel
      have hl : raw6636step2Labels = raw6636step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2569 node2569Labels := by rfl

theorem canonical6637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6637 raw6637Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw6637 raw6637Labels = mixedMoment B raw6637step0 raw6637step0Labels := by
      have hz : ∀ j, raw6637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6637step0 = (fun i j => raw6637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6637step0 raw6637; decide +kernel
      have hl : raw6637step0Labels = raw6637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6637 raw6637Labels permutation346 hz
    mixedMoment B raw6637step0 raw6637step0Labels = mixedMoment B raw6637step1 raw6637step1Labels := by
      have ha : raw6637step1 = (fun i j => raw6637step0 (permutation143 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6637step1 raw6637step0; decide +kernel
      have hl : raw6637step1Labels = raw6637step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6637step0 raw6637step0Labels permutation143 permutation3
    mixedMoment B raw6637step1 raw6637step1Labels = mixedMoment B raw6637step2 raw6637step2Labels := by
      have ha : raw6637step2 = -raw6637step1 := by apply Matrix.ext; change ∀ i j, raw6637step2 i j = -(raw6637step1 i j); unfold raw6637step2 raw6637step1; decide +kernel
      have hl : raw6637step2Labels = raw6637step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2664 node2664Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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

theorem canonical5196 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5196 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5196 = injectiveMoment H raw5196step0 := by
      have hz : ∀ j, raw5196 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5196step0 = (fun i j => raw5196 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5196 permutation104 hz
    injectiveMoment H raw5196step0 = injectiveMoment H raw5196step1 := by
      have hz : ∀ j, raw5196step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5196step1 = (fun i j => raw5196step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5196step0 permutation21 hz
    _ = injectiveMoment H node11 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical680 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw680 = injectiveMoment H node569 := by
  calc
    injectiveMoment H raw680 = injectiveMoment H raw680step0 := by
      have heq : raw680step0 = -raw680 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw680).symm
    injectiveMoment H raw680step0 = injectiveMoment H raw680step1 := by
      have heq : raw680step1 = (fun i j => raw680step0 (permutation41 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw680step0 permutation41 permutation8
    _ = injectiveMoment H node569 := by rfl

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

theorem canonical7634 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7634 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7634 = injectiveMoment H raw7634step0 := by
      have heq : raw7634step0 = (fun i j => raw7634 (permutation57 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7634 permutation57 permutation1
    _ = injectiveMoment H node232 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical867 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw867 = injectiveMoment H node118 := by
  rfl

theorem canonical893 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw893 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw893 = injectiveMoment H raw893step0 := by
      have hz : ∀ j, raw893 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw893step0 = (fun i j => raw893 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw893 permutation57 hz
    _ = injectiveMoment H node26 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical233
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7462 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7462 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7462 = injectiveMoment H raw7462step0 := by
      have hz : ∀ i, raw7462 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw7462step0 = (fun i j => raw7462 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7462 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical909 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw909 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw909 = injectiveMoment H raw909step0 := by
      have hz : ∀ j, raw909 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw909step0 = (fun i j => raw909 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw909 permutation21 hz
    _ = injectiveMoment H node10 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw208 = injectiveMoment H node16 := by
  rfl

theorem canonical211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw211 = injectiveMoment H node8 := by
  rfl

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
  rfl

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
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

theorem sound2 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node2 = Sparse.eval value2 (momentVector H) := by
  have hc : momentVector H 6 = injectiveMoment H node2 := rfl
  simp [value2, Sparse.eval, hc]

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

theorem sound8 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node8 = Sparse.eval value8 (momentVector H) := by
  have heq : pivotMatrix8 = (fun u v => node8 (pivotPermutation8 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node8 = injectiveMoment H pivotMatrix8 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix8 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix8 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (0 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (1 : Fin 2) = raw215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical215 hH).trans (sound2 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node8 + (injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value8, value2, value3, Sparse.eval] at hc ⊢
  linarith

theorem sound9 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node9 = Sparse.eval value9 (momentVector H) := by
  have hc : momentVector H 5 = injectiveMoment H node9 := rfl
  simp [value9, Sparse.eval, hc]

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

theorem sound16 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node16 = Sparse.eval value16 (momentVector H) := by
  have heq : pivotMatrix16 = (fun u v => node16 (pivotPermutation16 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node16 = injectiveMoment H pivotMatrix16 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix16 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix16 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (1 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (2 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node16 + (injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value16, value10, value8, value9, Sparse.eval] at hc ⊢
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

theorem sound37 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node37 = Sparse.eval value37 (momentVector H) := by
  have hc : momentVector H 13 = injectiveMoment H node37 := rfl
  simp [value37, Sparse.eval, hc]

theorem sound40 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node40 = Sparse.eval value40 (momentVector H) := by
  have hc : momentVector H 52 = injectiveMoment H node40 := rfl
  simp [value40, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

theorem sound44 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node44 = Sparse.eval value44 (momentVector H) := by
  have hc : momentVector H 4 = injectiveMoment H node44 := rfl
  simp [value44, Sparse.eval, hc]

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

theorem sound61 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node61 = Sparse.eval value61 (momentVector H) := by
  have heq : pivotMatrix61 = (fun u v => node61 (pivotPermutation61 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node61 = injectiveMoment H pivotMatrix61 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix61 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix61 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix61 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix61 (0 : Fin 2) = raw7462 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7462 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix61 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix61 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node61 + (injectiveMoment H (mergeFirst pivotMatrix61 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix61 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value61, value11, value5, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4130 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4130 = injectiveMoment H node210 := by
  rfl

theorem canonical4131 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4131 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw4131 = injectiveMoment H raw4131step0 := by
      have heq : raw4131step0 = (fun i j => raw4131 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4131 permutation25 permutation6
    _ = injectiveMoment H node294 := by rfl

theorem canonical4134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4134 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4134 = injectiveMoment H raw4134step0 := by
      have heq : raw4134step0 = (fun i j => raw4134 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4134 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

theorem canonical4139 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4139 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw4139 = injectiveMoment H raw4139step0 := by
      have heq : raw4139step0 = -raw4139 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4139).symm
    injectiveMoment H raw4139step0 = injectiveMoment H raw4139step1 := by
      have heq : raw4139step1 = (fun i j => raw4139step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4139step0 permutation19 permutation5
    _ = injectiveMoment H node203 := by rfl

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

theorem canonical4159 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4159 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4159 = injectiveMoment H raw4159step0 := by
      have heq : raw4159step0 = -raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4159).symm
    injectiveMoment H raw4159step0 = injectiveMoment H raw4159step1 := by
      have heq : raw4159step1 = (fun i j => raw4159step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4159step0 permutation7 permutation5
    _ = injectiveMoment H node36 := by rfl

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

theorem canonical791 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw791 = injectiveMoment H node566 := by
  calc
    injectiveMoment H raw791 = injectiveMoment H raw791step0 := by
      have heq : raw791step0 = -raw791 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw791).symm
    injectiveMoment H raw791step0 = injectiveMoment H raw791step1 := by
      have heq : raw791step1 = (fun i j => raw791step0 (permutation42 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw791step0 permutation42 permutation8
    _ = injectiveMoment H node566 := by rfl

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

theorem canonical2860 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2860 = injectiveMoment H node40 := by
  rfl

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

theorem sound118 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node118 = Sparse.eval value118 (momentVector H) := by
  have heq : pivotMatrix118 = (fun u v => node118 (pivotPermutation118 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node118 = injectiveMoment H pivotMatrix118 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix118 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix118 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix118 (0 : Fin 4)) =
      Sparse.eval value16 (momentVector H) := by
    have heq : mergeFirst pivotMatrix118 (0 : Fin 4) = raw208 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical208 hH).trans (sound16 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix118 (1 : Fin 4)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix118 (1 : Fin 4) = raw895 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical895 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix118 (2 : Fin 4)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix118 (2 : Fin 4) = raw909 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical909 hH).trans (sound10 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix118 (3 : Fin 4)) =
      Sparse.eval value26 (momentVector H) := by
    have heq : mergeFirst pivotMatrix118 (3 : Fin 4) = raw914 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical914 hH).trans (sound26 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node118 + (injectiveMoment H (mergeFirst pivotMatrix118 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix118 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix118 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix118 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value118, value10, value16, value26, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4954 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4954 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw4954 = injectiveMoment H raw4954step0 := by
      have heq : raw4954step0 = (fun i j => raw4954 (permutation10 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4954 permutation10 permutation4
    _ = injectiveMoment H node230 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4966 = injectiveMoment H node44 := by
  rfl

theorem canonical4967 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4967 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw4967 = injectiveMoment H raw4967step0 := by
      have heq : raw4967step0 = -raw4967 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4967).symm
    injectiveMoment H raw4967step0 = injectiveMoment H raw4967step1 := by
      have heq : raw4967step1 = (fun i j => raw4967step0 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4967step0 permutation4 permutation6
    _ = injectiveMoment H node61 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical214
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6865 = injectiveMoment H node62 := by
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

theorem canonical2817 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2817 = injectiveMoment H node180 := by
  rfl

theorem canonical2820 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2820 = injectiveMoment H node181 := by
  rfl

theorem canonical2823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2823 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw2823 = injectiveMoment H raw2823step0 := by
      have heq : raw2823step0 = (fun i j => raw2823 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2823 permutation4 permutation5
    _ = injectiveMoment H node57 := by rfl

theorem canonical2833 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2833 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw2833 = injectiveMoment H raw2833step0 := by
      have heq : raw2833step0 = (fun i j => raw2833 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2833 permutation11 permutation3
    _ = injectiveMoment H node177 := by rfl

theorem canonical2839 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2839 = injectiveMoment H node184 := by
  rfl

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

theorem sound180 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node180 = Sparse.eval value180 (momentVector H) := by
  have heq : pivotMatrix180 = (fun u v => node180 (pivotPermutation180 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node180 = injectiveMoment H pivotMatrix180 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix180 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix180 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix180 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix180 (0 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix180 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix180 (1 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix180 (2 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix180 (2 : Fin 3) = raw2860 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2860 hH).trans (sound40 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node180 + (injectiveMoment H (mergeFirst pivotMatrix180 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix180 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix180 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value180, value36, value40, value63, Sparse.eval] at hc ⊢
  linarith

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

theorem sound184 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node184 = Sparse.eval value184 (momentVector H) := by
  have hc : momentVector H 51 = injectiveMoment H node184 := rfl
  simp [value184, Sparse.eval, hc]

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

theorem sound210 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node210 = Sparse.eval value210 (momentVector H) := by
  have heq : pivotMatrix210 = (fun u v => node210 (pivotPermutation210 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node210 = injectiveMoment H pivotMatrix210 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix210 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix210 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix210 (0 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (0 : Fin 3) = raw4966 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4966 hH).trans (sound44 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix210 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (1 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix210 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (2 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node210 + (injectiveMoment H (mergeFirst pivotMatrix210 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix210 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix210 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value210, value36, value44, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound230 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node230 = Sparse.eval value230 (momentVector H) := by
  have heq : pivotMatrix230 = (fun u v => node230 (pivotPermutation230 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node230 = injectiveMoment H pivotMatrix230 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix230 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix230 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix230 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix230 (0 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix230 (1 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix230 (1 : Fin 3) = raw4966 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4966 hH).trans (sound44 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix230 (2 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix230 (2 : Fin 3) = raw4967 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4967 hH).trans (sound61 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node230 + (injectiveMoment H (mergeFirst pivotMatrix230 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix230 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix230 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value230, value44, value61, value62, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical267
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8545 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8545 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw8545 = injectiveMoment H raw8545step0 := by
      have heq : raw8545step0 = (fun i j => raw8545 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8545 permutation5 permutation4
    _ = injectiveMoment H node61 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical274
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8778 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8778 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw8778 = injectiveMoment H raw8778step0 := by
      have hz : ∀ i, raw8778 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8778step0 = (fun i j => raw8778 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8778 permutation3 hz
    injectiveMoment H raw8778step0 = injectiveMoment H raw8778step1 := by
      have heq : raw8778step1 = (fun i j => raw8778step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8778step0 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound4
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound294 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node294 = Sparse.eval value294 (momentVector H) := by
  have heq : pivotMatrix294 = (fun u v => node294 (pivotPermutation294 u) v) := by apply Matrix.ext; unfold pivotMatrix294 node294 pivotPermutation294; decide +kernel
  have hmoment : injectiveMoment H node294 = injectiveMoment H pivotMatrix294 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix294 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix294 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix294 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix294 (0 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix294 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix294 (1 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix294 (1 : Fin 3) = raw8545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix294 raw8545; decide +kernel
    rw [heq]
    exact (canonical8545 hH).trans (sound61 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix294 (2 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix294 (2 : Fin 3) = raw8778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix294 raw8778; decide +kernel
    rw [heq]
    exact (canonical8778 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node294 + (injectiveMoment H (mergeFirst pivotMatrix294 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix294 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix294 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value294, value11, value61, value62, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical4117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4117 = injectiveMoment H node207 := by
  rfl

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

theorem canonical2811 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2811 = injectiveMoment H node177 := by
  rfl

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

theorem sound667 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node667 = Sparse.eval value667 (momentVector H) := by
  have heq : pivotMatrix667 = (fun u v => node667 (pivotPermutation667 u) v) := by apply Matrix.ext; unfold pivotMatrix667 node667 pivotPermutation667; decide +kernel
  have hmoment : injectiveMoment H node667 = injectiveMoment H pivotMatrix667 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix667 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix667 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix667 (0 : Fin 4)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix667 (0 : Fin 4) = raw4954 := by apply Matrix.ext; unfold mergeFirst pivotMatrix667 raw4954; decide +kernel
    rw [heq]
    exact (canonical4954 hH).trans (sound230 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix667 (1 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix667 (1 : Fin 4) = raw4139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix667 raw4139; decide +kernel
    rw [heq]
    exact (canonical4139 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix667 (2 : Fin 4)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix667 (2 : Fin 4) = raw4131 := by apply Matrix.ext; unfold mergeFirst pivotMatrix667 raw4131; decide +kernel
    rw [heq]
    exact (canonical4131 hH).trans (sound294 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix667 (3 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix667 (3 : Fin 4) = raw4130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix667 raw4130; decide +kernel
    rw [heq]
    exact (canonical4130 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node667 + (injectiveMoment H (mergeFirst pivotMatrix667 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix667 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix667 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix667 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value667, value203, value210, value230, value294, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3977 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3977 = injectiveMoment H node667 := by
  calc
    injectiveMoment H raw3977 = injectiveMoment H raw3977step0 := by
      have heq : raw3977step0 = -raw3977 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3977).symm
    injectiveMoment H raw3977step0 = injectiveMoment H raw3977step1 := by
      have heq : raw3977step1 = (fun i j => raw3977step0 (permutation41 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3977step0 permutation41 permutation8
    _ = injectiveMoment H node667 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound8
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound566 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node566 = Sparse.eval value566 (momentVector H) := by
  have heq : pivotMatrix566 = (fun u v => node566 (pivotPermutation566 u) v) := by apply Matrix.ext; unfold pivotMatrix566 node566 pivotPermutation566; decide +kernel
  have hmoment : injectiveMoment H node566 = injectiveMoment H pivotMatrix566 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix566 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix566 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix566 (0 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix566 (0 : Fin 4) = raw4117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix566 raw4117; decide +kernel
    rw [heq]
    exact (canonical4117 hH).trans (sound207 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix566 (1 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix566 (1 : Fin 4) = raw2833 := by apply Matrix.ext; unfold mergeFirst pivotMatrix566 raw2833; decide +kernel
    rw [heq]
    exact (canonical2833 hH).trans (sound177 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix566 (2 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix566 (2 : Fin 4) = raw2811 := by apply Matrix.ext; unfold mergeFirst pivotMatrix566 raw2811; decide +kernel
    rw [heq]
    exact (canonical2811 hH).trans (sound177 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix566 (3 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix566 (3 : Fin 4) = raw2803 := by apply Matrix.ext; unfold mergeFirst pivotMatrix566 raw2803; decide +kernel
    rw [heq]
    exact (canonical2803 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node566 + (injectiveMoment H (mergeFirst pivotMatrix566 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix566 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix566 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix566 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value566, value176, value177, value207, Sparse.eval] at hc ⊢
  linarith

theorem sound569 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node569 = Sparse.eval value569 (momentVector H) := by
  have heq : pivotMatrix569 = (fun u v => node569 (pivotPermutation569 u) v) := by apply Matrix.ext; unfold pivotMatrix569 node569 pivotPermutation569; decide +kernel
  have hmoment : injectiveMoment H node569 = injectiveMoment H pivotMatrix569 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix569 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix569 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix569 (0 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix569 (0 : Fin 4) = raw4130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix569 raw4130; decide +kernel
    rw [heq]
    exact (canonical4130 hH).trans (sound210 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix569 (1 : Fin 4)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix569 (1 : Fin 4) = raw2839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix569 raw2839; decide +kernel
    rw [heq]
    exact (canonical2839 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix569 (2 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix569 (2 : Fin 4) = raw2820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix569 raw2820; decide +kernel
    rw [heq]
    exact (canonical2820 hH).trans (sound181 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix569 (3 : Fin 4)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix569 (3 : Fin 4) = raw2817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix569 raw2817; decide +kernel
    rw [heq]
    exact (canonical2817 hH).trans (sound180 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node569 + (injectiveMoment H (mergeFirst pivotMatrix569 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix569 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix569 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix569 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value569, value180, value181, value184, value210, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node352 node352Labels = Sparse.eval singlePairValue352 (familyPairVector B) := by
  have hp := single_label_three B hB node352
  have hl : node352Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node352 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node352 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node352 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node352 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node352 (EqualityPatterns.family3.label 1) = PairSemantics.raw5196 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node352 PairSemantics.raw5196; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5196 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node352 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node352 (EqualityPatterns.family3.label 2) = PairSemantics.raw7634 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node352 PairSemantics.raw7634; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7634 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node352 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node352 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node352 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node352 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value569 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node352 (EqualityPatterns.family3.label 4) = PairSemantics.raw680 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node352 PairSemantics.raw680; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical680 hH).trans (PairSemantics.sound569 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue352, PairSemantics.value0, PairSemantics.value11, PairSemantics.value118, PairSemantics.value232, PairSemantics.value569, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5216 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5216 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5216 = injectiveMoment H raw5216step0 := by
      have hz : ∀ j, raw5216 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5216step0 = (fun i j => raw5216 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5216 permutation128 hz
    injectiveMoment H raw5216step0 = injectiveMoment H raw5216step1 := by
      have hz : ∀ j, raw5216step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5216step1 = (fun i j => raw5216step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5216step0 permutation27 hz
    injectiveMoment H raw5216step1 = injectiveMoment H raw5216step2 := by
      have hz : ∀ j, raw5216step1 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw5216step2 = (fun i j => raw5216step1 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5216step1 permutation7 hz
    _ = injectiveMoment H node4 := by rfl

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

theorem singlePair411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node411 node411Labels = Sparse.eval singlePairValue411 (familyPairVector B) := by
  have hp := single_label_three B hB node411
  have hl : node411Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node411 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node411 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node411 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node411 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node411 (EqualityPatterns.family3.label 1) = PairSemantics.raw5216 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node411 PairSemantics.raw5216; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5216 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node411 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node411 (EqualityPatterns.family3.label 2) = PairSemantics.raw7634 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node411 PairSemantics.raw7634; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7634 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node411 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node411 (EqualityPatterns.family3.label 3) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node411 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node411 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value566 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node411 (EqualityPatterns.family3.label 4) = PairSemantics.raw791 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node411 PairSemantics.raw791; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical791 hH).trans (PairSemantics.sound566 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue411, PairSemantics.value0, PairSemantics.value4, PairSemantics.value26, PairSemantics.value232, PairSemantics.value566, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

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

theorem canonical8981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8981 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw8981 = injectiveMoment H raw8981step0 := by
      have hz : ∀ j, raw8981 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8981step0 = (fun i j => raw8981 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8981 permutation128 hz
    injectiveMoment H raw8981step0 = injectiveMoment H raw8981step1 := by
      have hz : ∀ j, raw8981step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8981step1 = (fun i j => raw8981step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8981step0 permutation9 hz
    _ = injectiveMoment H node11 := by rfl

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

theorem singlePair502 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node502 node502Labels = Sparse.eval singlePairValue502 (familyPairVector B) := by
  have hp := single_label_three B hB node502
  have hl : node502Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node502 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node502 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node502 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node502 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node502 (EqualityPatterns.family3.label 1) = PairSemantics.raw5196 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node502 PairSemantics.raw5196; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5196 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node502 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node502 (EqualityPatterns.family3.label 2) = PairSemantics.raw8981 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node502 PairSemantics.raw8981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8981 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node502 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node502 (EqualityPatterns.family3.label 3) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node502 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node502 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value667 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node502 (EqualityPatterns.family3.label 4) = PairSemantics.raw3977 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node502 PairSemantics.raw3977; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3977 hH).trans (PairSemantics.sound667 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue502, PairSemantics.value0, PairSemantics.value11, PairSemantics.value232, PairSemantics.value667, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton2637 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2637 node2637Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node352 node352Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw254 singletonSmall2637
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2637) = raw254Labels := by decide +kernel
  rw [hl, canonical254 B hB] at h
  have hc0 : mixedMoment B raw254 (Fin.cases (0 : Fin 1) singletonSmall2637) =
      mixedMoment B node352 node352Labels := by
    have ha : raw254 = raw255 := by apply Matrix.ext; unfold raw254 raw255; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2637 = raw255Labels := by decide +kernel
    rw [ha, hj, canonical255 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem singleton2775 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2775 node2775Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node411 node411Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw276 singletonSmall2775
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2775) = raw276Labels := by decide +kernel
  rw [hl, canonical276 B hB] at h
  have hc0 : mixedMoment B raw276 (Fin.cases (0 : Fin 1) singletonSmall2775) =
      mixedMoment B node411 node411Labels := by
    have ha : raw276 = raw277 := by apply Matrix.ext; unfold raw276 raw277; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2775 = raw277Labels := by decide +kernel
    rw [ha, hj, canonical277 B hB]
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

theorem singleton3887 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3887 node3887Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node502 node502Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw542 singletonSmall3887
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3887) = raw542Labels := by decide +kernel
  rw [hl, canonical542 B hB] at h
  have hc0 : mixedMoment B raw542 (Fin.cases (0 : Fin 1) singletonSmall3887) =
      mixedMoment B node502 node502Labels := by
    have ha : raw542 = raw543 := by apply Matrix.ext; unfold raw542 raw543; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3887 = raw543Labels := by decide +kernel
    rw [ha, hj, canonical543 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem sound988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node988 node988Labels = Sparse.eval nodeValue988 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 988) = mixedMoment B node988 node988Labels := rfl
  simpa [nodeValue988, Sparse.eval] using hc.symm

theorem sound989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node989 node989Labels = Sparse.eval nodeValue989 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 989) = mixedMoment B node989 node989Labels := rfl
  simpa [nodeValue989, Sparse.eval] using hc.symm

theorem sound993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node993 node993Labels = Sparse.eval nodeValue993 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 993) = mixedMoment B node993 node993Labels := rfl
  simpa [nodeValue993, Sparse.eval] using hc.symm

theorem sound1001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1001 node1001Labels = Sparse.eval nodeValue1001 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1001) = mixedMoment B node1001 node1001Labels := rfl
  simpa [nodeValue1001, Sparse.eval] using hc.symm

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

theorem sound1057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1057 node1057Labels = Sparse.eval nodeValue1057 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1057) = mixedMoment B node1057 node1057Labels := rfl
  simpa [nodeValue1057, Sparse.eval] using hc.symm

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

theorem sound2390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2390 node2390Labels = Sparse.eval nodeValue2390 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2390) = mixedMoment B node2390 node2390Labels := rfl
  simpa [nodeValue2390, Sparse.eval] using hc.symm

theorem sound2391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2391 node2391Labels = Sparse.eval nodeValue2391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2391) = mixedMoment B node2391 node2391Labels := rfl
  simpa [nodeValue2391, Sparse.eval] using hc.symm

theorem sound2395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2395 node2395Labels = Sparse.eval nodeValue2395 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2395) = mixedMoment B node2395 node2395Labels := rfl
  simpa [nodeValue2395, Sparse.eval] using hc.symm

theorem sound2401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2401 node2401Labels = Sparse.eval nodeValue2401 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2401) = mixedMoment B node2401 node2401Labels := rfl
  simpa [nodeValue2401, Sparse.eval] using hc.symm

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

theorem sound2453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2453 node2453Labels = Sparse.eval nodeValue2453 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2453) = mixedMoment B node2453 node2453Labels := rfl
  simpa [nodeValue2453, Sparse.eval] using hc.symm

theorem sound2456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2456 node2456Labels = Sparse.eval nodeValue2456 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2456) = mixedMoment B node2456 node2456Labels := rfl
  simpa [nodeValue2456, Sparse.eval] using hc.symm

theorem sound2460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2460 node2460Labels = Sparse.eval nodeValue2460 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2460) = mixedMoment B node2460 node2460Labels := rfl
  simpa [nodeValue2460, Sparse.eval] using hc.symm

theorem sound2493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2493 node2493Labels = Sparse.eval nodeValue2493 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2493) = mixedMoment B node2493 node2493Labels := rfl
  simpa [nodeValue2493, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node352 node352Labels = Sparse.eval nodeValue352 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue352 (familyPairVector B) := singlePair352 B _hB
    _ = _ := by norm_num [singlePairValue352, nodeValue352, Sparse.eval, mixedVector] <;> ring

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

theorem sound2569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2569 node2569Labels = Sparse.eval nodeValue2569 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2569) = mixedMoment B node2569 node2569Labels := rfl
  simpa [nodeValue2569, Sparse.eval] using hc.symm

theorem sound2615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2615 node2615Labels = Sparse.eval nodeValue2615 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2615) = mixedMoment B node2615 node2615Labels := rfl
  simpa [nodeValue2615, Sparse.eval] using hc.symm

theorem sound2621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2621 node2621Labels = Sparse.eval nodeValue2621 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2621) = mixedMoment B node2621 node2621Labels := rfl
  simpa [nodeValue2621, Sparse.eval] using hc.symm

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

theorem sound2637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2637 node2637Labels = Sparse.eval nodeValue2637 (mixedVector B) := by
  have h := singleton2637 B _hB
  rw [sound352 B _hB _hF] at h
  norm_num [nodeValue2637, nodeValue352, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2664 node2664Labels = Sparse.eval nodeValue2664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2664) = mixedMoment B node2664 node2664Labels := rfl
  simpa [nodeValue2664, Sparse.eval] using hc.symm

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

theorem sound2698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2698 node2698Labels = Sparse.eval nodeValue2698 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2698) = mixedMoment B node2698 node2698Labels := rfl
  simpa [nodeValue2698, Sparse.eval] using hc.symm

theorem sound2706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2706 node2706Labels = Sparse.eval nodeValue2706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2706) = mixedMoment B node2706 node2706Labels := rfl
  simpa [nodeValue2706, Sparse.eval] using hc.symm

theorem sound2730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2730 node2730Labels = Sparse.eval nodeValue2730 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2730) = mixedMoment B node2730 node2730Labels := rfl
  simpa [nodeValue2730, Sparse.eval] using hc.symm

theorem sound2731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2731 node2731Labels = Sparse.eval nodeValue2731 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2731) = mixedMoment B node2731 node2731Labels := rfl
  simpa [nodeValue2731, Sparse.eval] using hc.symm

theorem sound2738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2738 node2738Labels = Sparse.eval nodeValue2738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2738) = mixedMoment B node2738 node2738Labels := rfl
  simpa [nodeValue2738, Sparse.eval] using hc.symm

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

theorem sound411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node411 node411Labels = Sparse.eval nodeValue411 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue411 (familyPairVector B) := singlePair411 B _hB
    _ = _ := by
      norm_num [singlePairValue411, nodeValue411, Sparse.eval, mixedVector]
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

theorem sound2775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2775 node2775Labels = Sparse.eval nodeValue2775 (mixedVector B) := by
  have h := singleton2775 B _hB
  rw [sound411 B _hB _hF] at h
  norm_num [nodeValue2775, nodeValue411, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node502 node502Labels = Sparse.eval nodeValue502 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue502 (familyPairVector B) := singlePair502 B _hB
    _ = _ := by norm_num [singlePairValue502, nodeValue502, Sparse.eval, mixedVector] <;> ring

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

theorem sound3880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3880 node3880Labels = Sparse.eval nodeValue3880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3880) = mixedMoment B node3880 node3880Labels := rfl
  simpa [nodeValue3880, Sparse.eval] using hc.symm

theorem sound3884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3884 node3884Labels = Sparse.eval nodeValue3884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3884) = mixedMoment B node3884 node3884Labels := rfl
  simpa [nodeValue3884, Sparse.eval] using hc.symm

theorem sound3885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3885 node3885Labels = Sparse.eval nodeValue3885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3885) = mixedMoment B node3885 node3885Labels := rfl
  simpa [nodeValue3885, Sparse.eval] using hc.symm

theorem sound3887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3887 node3887Labels = Sparse.eval nodeValue3887 (mixedVector B) := by
  have h := singleton3887 B _hB
  rw [sound502 B _hB _hF] at h
  norm_num [nodeValue3887, nodeValue502, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources9
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq303 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm303 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA303 + difference 0 1) (sourceB303 + difference 1 0) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA303 + difference 0 1) (sourceB303 + difference 1 0) sourceC303) = raw6608 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6608; decide +kernel
    rw [ha]
    exact (canonical6608 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA303 + difference 0 2) (sourceB303 + difference 2 0) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA303 + difference 0 2) (sourceB303 + difference 2 0) sourceC303) = raw6609 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6609; decide +kernel
    rw [ha]
    exact (canonical6609 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA303 + difference 0 3) (sourceB303 + difference 3 0) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA303 + difference 0 3) (sourceB303 + difference 3 0) sourceC303) = raw6610 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6610; decide +kernel
    rw [ha]
    exact (canonical6610 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA303 + difference 0 4) (sourceB303 + difference 4 0) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA303 + difference 0 4) (sourceB303 + difference 4 0) sourceC303) = raw6611 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6611; decide +kernel
    rw [ha]
    exact (canonical6611 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA303 + difference 0 5) (sourceB303 + difference 5 0) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA303 + difference 0 5) (sourceB303 + difference 5 0) sourceC303) = raw6612 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6612; decide +kernel
    rw [ha]
    exact (canonical6612 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA303 + difference 1 0) (sourceB303 + difference 0 1) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1057) := by
    have ha : (tripleCharges (sourceA303 + difference 1 0) (sourceB303 + difference 0 1) sourceC303) = raw6613 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6613; decide +kernel
    rw [ha]
    exact (canonical6613 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA303 + difference 1 2) (sourceB303 + difference 2 1) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2493) := by
    have ha : (tripleCharges (sourceA303 + difference 1 2) (sourceB303 + difference 2 1) sourceC303) = raw6614 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6614; decide +kernel
    rw [ha]
    exact (canonical6614 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA303 + difference 1 3) (sourceB303 + difference 3 1) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2637) := by
    have ha : (tripleCharges (sourceA303 + difference 1 3) (sourceB303 + difference 3 1) sourceC303) = raw6615 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6615; decide +kernel
    rw [ha]
    exact (canonical6615 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA303 + difference 1 4) (sourceB303 + difference 4 1) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA303 + difference 1 4) (sourceB303 + difference 4 1) sourceC303) = raw6616 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6616; decide +kernel
    rw [ha]
    exact (canonical6616 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA303 + difference 1 5) (sourceB303 + difference 5 1) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2775) := by
    have ha : (tripleCharges (sourceA303 + difference 1 5) (sourceB303 + difference 5 1) sourceC303) = raw6617 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6617; decide +kernel
    rw [ha]
    exact (canonical6617 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA303 + difference 2 0) (sourceB303 + difference 0 2) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 988) := by
    have ha : (tripleCharges (sourceA303 + difference 2 0) (sourceB303 + difference 0 2) sourceC303) = raw6618 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6618; decide +kernel
    rw [ha]
    exact (canonical6618 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA303 + difference 2 1) (sourceB303 + difference 1 2) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2390) := by
    have ha : (tripleCharges (sourceA303 + difference 2 1) (sourceB303 + difference 1 2) sourceC303) = raw6619 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6619; decide +kernel
    rw [ha]
    exact (canonical6619 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA303 + difference 2 3) (sourceB303 + difference 3 2) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA303 + difference 2 3) (sourceB303 + difference 3 2) sourceC303) = raw6620 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6620; decide +kernel
    rw [ha]
    exact (canonical6620 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA303 + difference 2 4) (sourceB303 + difference 4 2) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2698) := by
    have ha : (tripleCharges (sourceA303 + difference 2 4) (sourceB303 + difference 4 2) sourceC303) = raw6621 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6621; decide +kernel
    rw [ha]
    exact (canonical6621 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA303 + difference 2 5) (sourceB303 + difference 5 2) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA303 + difference 2 5) (sourceB303 + difference 5 2) sourceC303) = raw6622 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6622; decide +kernel
    rw [ha]
    exact (canonical6622 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA303 + difference 3 0) (sourceB303 + difference 0 3) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1001) := by
    have ha : (tripleCharges (sourceA303 + difference 3 0) (sourceB303 + difference 0 3) sourceC303) = raw6623 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6623; decide +kernel
    rw [ha]
    exact (canonical6623 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA303 + difference 3 1) (sourceB303 + difference 1 3) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2401) := by
    have ha : (tripleCharges (sourceA303 + difference 3 1) (sourceB303 + difference 1 3) sourceC303) = raw6624 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6624; decide +kernel
    rw [ha]
    exact (canonical6624 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA303 + difference 3 2) (sourceB303 + difference 2 3) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2460) := by
    have ha : (tripleCharges (sourceA303 + difference 3 2) (sourceB303 + difference 2 3) sourceC303) = raw6625 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6625; decide +kernel
    rw [ha]
    exact (canonical6625 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA303 + difference 3 4) (sourceB303 + difference 4 3) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA303 + difference 3 4) (sourceB303 + difference 4 3) sourceC303) = raw6626 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6626; decide +kernel
    rw [ha]
    exact (canonical6626 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA303 + difference 3 5) (sourceB303 + difference 5 3) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA303 + difference 3 5) (sourceB303 + difference 5 3) sourceC303) = raw6627 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6627; decide +kernel
    rw [ha]
    exact (canonical6627 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA303 + difference 4 0) (sourceB303 + difference 0 4) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 993) := by
    have ha : (tripleCharges (sourceA303 + difference 4 0) (sourceB303 + difference 0 4) sourceC303) = raw6628 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6628; decide +kernel
    rw [ha]
    exact (canonical6628 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA303 + difference 4 1) (sourceB303 + difference 1 4) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2395) := by
    have ha : (tripleCharges (sourceA303 + difference 4 1) (sourceB303 + difference 1 4) sourceC303) = raw6629 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6629; decide +kernel
    rw [ha]
    exact (canonical6629 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA303 + difference 4 2) (sourceB303 + difference 2 4) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2456) := by
    have ha : (tripleCharges (sourceA303 + difference 4 2) (sourceB303 + difference 2 4) sourceC303) = raw6630 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6630; decide +kernel
    rw [ha]
    exact (canonical6630 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA303 + difference 4 3) (sourceB303 + difference 3 4) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2621) := by
    have ha : (tripleCharges (sourceA303 + difference 4 3) (sourceB303 + difference 3 4) sourceC303) = raw6631 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6631; decide +kernel
    rw [ha]
    exact (canonical6631 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA303 + difference 4 5) (sourceB303 + difference 5 4) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA303 + difference 4 5) (sourceB303 + difference 5 4) sourceC303) = raw6632 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6632; decide +kernel
    rw [ha]
    exact (canonical6632 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA303 + difference 5 0) (sourceB303 + difference 0 5) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 989) := by
    have ha : (tripleCharges (sourceA303 + difference 5 0) (sourceB303 + difference 0 5) sourceC303) = raw6633 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6633; decide +kernel
    rw [ha]
    exact (canonical6633 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA303 + difference 5 1) (sourceB303 + difference 1 5) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2391) := by
    have ha : (tripleCharges (sourceA303 + difference 5 1) (sourceB303 + difference 1 5) sourceC303) = raw6634 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6634; decide +kernel
    rw [ha]
    exact (canonical6634 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA303 + difference 5 2) (sourceB303 + difference 2 5) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2453) := by
    have ha : (tripleCharges (sourceA303 + difference 5 2) (sourceB303 + difference 2 5) sourceC303) = raw6635 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6635; decide +kernel
    rw [ha]
    exact (canonical6635 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA303 + difference 5 3) (sourceB303 + difference 3 5) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2569) := by
    have ha : (tripleCharges (sourceA303 + difference 5 3) (sourceB303 + difference 3 5) sourceC303) = raw6636 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6636; decide +kernel
    rw [ha]
    exact (canonical6636 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA303 + difference 5 4) (sourceB303 + difference 4 5) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA303 + difference 5 4) (sourceB303 + difference 4 5) sourceC303) = raw6637 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6637; decide +kernel
    rw [ha]
    exact (canonical6637 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA303 sourceB303 sourceC303
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm303, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck255 : Integer.Sparse.reindex keyMap MixedData.row255 = numericRow255 := by decide +kernel

theorem numericCheck255 (x : Master → ℝ) : Integer.Sparse.eval numericRow255 x =
    (8640 : ℝ) * reducedSource255 x := by
  norm_num [numericRow255, reducedSource255, Integer.Sparse.eval, Sparse.eval, nodeValue988, nodeValue989, nodeValue993, nodeValue1001, nodeValue1057, nodeValue2390, nodeValue2391, nodeValue2395, nodeValue2401, nodeValue2453, nodeValue2456, nodeValue2460, nodeValue2493, nodeValue2569, nodeValue2615, nodeValue2621, nodeValue2637, nodeValue2664, nodeValue2698, nodeValue2706, nodeValue2730, nodeValue2731, nodeValue2738, nodeValue2775, nodeValue3880, nodeValue3884, nodeValue3885, nodeValue3887, nodeValue3995] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero255 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource255 (mixedVector B) = 0 := by
  have h988 : mixedVector B (Sum.inr 988) = Sparse.eval nodeValue988 (mixedVector B) := by
    change mixedMoment B node988 node988Labels = _
    exact sound988 B hB hF
  have h989 : mixedVector B (Sum.inr 989) = Sparse.eval nodeValue989 (mixedVector B) := by
    change mixedMoment B node989 node989Labels = _
    exact sound989 B hB hF
  have h993 : mixedVector B (Sum.inr 993) = Sparse.eval nodeValue993 (mixedVector B) := by
    change mixedMoment B node993 node993Labels = _
    exact sound993 B hB hF
  have h1001 : mixedVector B (Sum.inr 1001) = Sparse.eval nodeValue1001 (mixedVector B) := by
    change mixedMoment B node1001 node1001Labels = _
    exact sound1001 B hB hF
  have h1057 : mixedVector B (Sum.inr 1057) = Sparse.eval nodeValue1057 (mixedVector B) := by
    change mixedMoment B node1057 node1057Labels = _
    exact sound1057 B hB hF
  have h2390 : mixedVector B (Sum.inr 2390) = Sparse.eval nodeValue2390 (mixedVector B) := by
    change mixedMoment B node2390 node2390Labels = _
    exact sound2390 B hB hF
  have h2391 : mixedVector B (Sum.inr 2391) = Sparse.eval nodeValue2391 (mixedVector B) := by
    change mixedMoment B node2391 node2391Labels = _
    exact sound2391 B hB hF
  have h2395 : mixedVector B (Sum.inr 2395) = Sparse.eval nodeValue2395 (mixedVector B) := by
    change mixedMoment B node2395 node2395Labels = _
    exact sound2395 B hB hF
  have h2401 : mixedVector B (Sum.inr 2401) = Sparse.eval nodeValue2401 (mixedVector B) := by
    change mixedMoment B node2401 node2401Labels = _
    exact sound2401 B hB hF
  have h2453 : mixedVector B (Sum.inr 2453) = Sparse.eval nodeValue2453 (mixedVector B) := by
    change mixedMoment B node2453 node2453Labels = _
    exact sound2453 B hB hF
  have h2456 : mixedVector B (Sum.inr 2456) = Sparse.eval nodeValue2456 (mixedVector B) := by
    change mixedMoment B node2456 node2456Labels = _
    exact sound2456 B hB hF
  have h2460 : mixedVector B (Sum.inr 2460) = Sparse.eval nodeValue2460 (mixedVector B) := by
    change mixedMoment B node2460 node2460Labels = _
    exact sound2460 B hB hF
  have h2493 : mixedVector B (Sum.inr 2493) = Sparse.eval nodeValue2493 (mixedVector B) := by
    change mixedMoment B node2493 node2493Labels = _
    exact sound2493 B hB hF
  have h2569 : mixedVector B (Sum.inr 2569) = Sparse.eval nodeValue2569 (mixedVector B) := by
    change mixedMoment B node2569 node2569Labels = _
    exact sound2569 B hB hF
  have h2615 : mixedVector B (Sum.inr 2615) = Sparse.eval nodeValue2615 (mixedVector B) := by
    change mixedMoment B node2615 node2615Labels = _
    exact sound2615 B hB hF
  have h2621 : mixedVector B (Sum.inr 2621) = Sparse.eval nodeValue2621 (mixedVector B) := by
    change mixedMoment B node2621 node2621Labels = _
    exact sound2621 B hB hF
  have h2637 : mixedVector B (Sum.inr 2637) = Sparse.eval nodeValue2637 (mixedVector B) := by
    change mixedMoment B node2637 node2637Labels = _
    exact sound2637 B hB hF
  have h2664 : mixedVector B (Sum.inr 2664) = Sparse.eval nodeValue2664 (mixedVector B) := by
    change mixedMoment B node2664 node2664Labels = _
    exact sound2664 B hB hF
  have h2698 : mixedVector B (Sum.inr 2698) = Sparse.eval nodeValue2698 (mixedVector B) := by
    change mixedMoment B node2698 node2698Labels = _
    exact sound2698 B hB hF
  have h2706 : mixedVector B (Sum.inr 2706) = Sparse.eval nodeValue2706 (mixedVector B) := by
    change mixedMoment B node2706 node2706Labels = _
    exact sound2706 B hB hF
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h2775 : mixedVector B (Sum.inr 2775) = Sparse.eval nodeValue2775 (mixedVector B) := by
    change mixedMoment B node2775 node2775Labels = _
    exact sound2775 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h3885 : mixedVector B (Sum.inr 3885) = Sparse.eval nodeValue3885 (mixedVector B) := by
    change mixedMoment B node3885 node3885Labels = _
    exact sound3885 B hB hF
  have h3887 : mixedVector B (Sum.inr 3887) = Sparse.eval nodeValue3887 (mixedVector B) := by
    change mixedMoment B node3887 node3887Labels = _
    exact sound3887 B hB hF
  have h3995 : mixedVector B (Sum.inr 3995) = Sparse.eval nodeValue3995 (mixedVector B) := by
    change mixedMoment B node3995 node3995Labels = _
    exact sound3995_e B hB hF
  simpa only [sourceForm303, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h988, h989, h993, h1001, h1057, h2390, h2391, h2395, h2401, h2453, h2456, h2460, h2493, h2569, h2615, h2621, h2637, h2664, h2698, h2706, h2730, h2731, h2738, h2775, h3880, h3884, h3885, h3887, h3995, reducedSource255] using sourceEq303 B hB

theorem rowSound255_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row255 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck255, numericCheck255, reducedZero255 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e_oai
