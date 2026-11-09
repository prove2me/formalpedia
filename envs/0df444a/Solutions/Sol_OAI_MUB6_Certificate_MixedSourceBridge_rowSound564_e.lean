-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T02:14:50.5122+00:00
-- url     : https://prove2.me/submissions/a8bbceca-1974-4a2d-b88a-af7de1e0bbb6

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
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5435_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5450_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1644 raw1644Labels = mixedMoment B node4729 node4729Labels := by
  calc
    mixedMoment B raw1644 raw1644Labels = mixedMoment B raw1644step0 raw1644step0Labels := by
      have ha : raw1644step0 = (fun i j => raw1644 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1644step0 raw1644; decide +kernel
      have hl : raw1644step0Labels = raw1644Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1644 raw1644Labels permutation152 permutation4
    mixedMoment B raw1644step0 raw1644step0Labels = mixedMoment B raw1644step1 raw1644step1Labels := by
      have ha : raw1644step1 = raw1644step0 := by apply Matrix.ext; unfold raw1644step1 raw1644step0; decide +kernel
      have hl : raw1644step0Labels = labelEmbedding7 ∘ raw1644step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1644step0 raw1644step0Labels raw1644step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4729 node4729Labels := by rfl

theorem canonical1645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1645 raw1645Labels = mixedMoment B node1898 node1898Labels := by
  calc
    mixedMoment B raw1645 raw1645Labels = mixedMoment B raw1645step0 raw1645step0Labels := by
      have ha : raw1645step0 = (fun i j => raw1645 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1645step0 raw1645; decide +kernel
      have hl : raw1645step0Labels = raw1645Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1645 raw1645Labels permutation152 permutation4
    _ = mixedMoment B node1898 node1898Labels := by rfl

theorem canonical1646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1646 raw1646Labels = mixedMoment B node1940 node1940Labels := by
  calc
    mixedMoment B raw1646 raw1646Labels = mixedMoment B raw1646step0 raw1646step0Labels := by
      have ha : raw1646step0 = (fun i j => raw1646 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1646step0 raw1646; decide +kernel
      have hl : raw1646step0Labels = raw1646Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1646 raw1646Labels permutation152 permutation6
    mixedMoment B raw1646step0 raw1646step0Labels = mixedMoment B raw1646step1 raw1646step1Labels := by
      have ha : raw1646step1 = -raw1646step0 := by apply Matrix.ext; change ∀ i j, raw1646step1 i j = -(raw1646step0 i j); unfold raw1646step1 raw1646step0; decide +kernel
      have hl : raw1646step1Labels = raw1646step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1646step1 raw1646step1Labels = mixedMoment B raw1646step2 raw1646step2Labels := by
      have ha : raw1646step2 = raw1646step1 := by apply Matrix.ext; unfold raw1646step2 raw1646step1; decide +kernel
      have hl : raw1646step1Labels = labelEmbedding1 ∘ raw1646step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1646step1 raw1646step1Labels raw1646step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1940 node1940Labels := by rfl

theorem canonical1647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1647 raw1647Labels = mixedMoment B node4731 node4731Labels := by
  calc
    mixedMoment B raw1647 raw1647Labels = mixedMoment B raw1647step0 raw1647step0Labels := by
      have ha : raw1647step0 = (fun i j => raw1647 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1647step0 raw1647; decide +kernel
      have hl : raw1647step0Labels = raw1647Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1647 raw1647Labels permutation152 permutation4
    mixedMoment B raw1647step0 raw1647step0Labels = mixedMoment B raw1647step1 raw1647step1Labels := by
      have ha : raw1647step1 = raw1647step0 := by apply Matrix.ext; unfold raw1647step1 raw1647step0; decide +kernel
      have hl : raw1647step0Labels = labelEmbedding7 ∘ raw1647step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1647step0 raw1647step0Labels raw1647step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4731 node4731Labels := by rfl

theorem canonical1648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1648 raw1648Labels = mixedMoment B node1900 node1900Labels := by
  calc
    mixedMoment B raw1648 raw1648Labels = mixedMoment B raw1648step0 raw1648step0Labels := by
      have ha : raw1648step0 = (fun i j => raw1648 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1648step0 raw1648; decide +kernel
      have hl : raw1648step0Labels = raw1648Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1648 raw1648Labels permutation152 permutation4
    _ = mixedMoment B node1900 node1900Labels := by rfl

theorem canonical1649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1649 raw1649Labels = mixedMoment B node1921 node1921Labels := by
  calc
    mixedMoment B raw1649 raw1649Labels = mixedMoment B raw1649step0 raw1649step0Labels := by
      have ha : raw1649step0 = (fun i j => raw1649 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1649step0 raw1649; decide +kernel
      have hl : raw1649step0Labels = raw1649Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1649 raw1649Labels permutation164 permutation6
    mixedMoment B raw1649step0 raw1649step0Labels = mixedMoment B raw1649step1 raw1649step1Labels := by
      have ha : raw1649step1 = -raw1649step0 := by apply Matrix.ext; change ∀ i j, raw1649step1 i j = -(raw1649step0 i j); unfold raw1649step1 raw1649step0; decide +kernel
      have hl : raw1649step1Labels = raw1649step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1649step1 raw1649step1Labels = mixedMoment B raw1649step2 raw1649step2Labels := by
      have ha : raw1649step2 = raw1649step1 := by apply Matrix.ext; unfold raw1649step2 raw1649step1; decide +kernel
      have hl : raw1649step1Labels = labelEmbedding1 ∘ raw1649step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1649step1 raw1649step1Labels raw1649step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1921 node1921Labels := by rfl

theorem canonical1656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1656 raw1656Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw1656 raw1656Labels = mixedMoment B raw1656step0 raw1656step0Labels := by
      have ha : raw1656step0 = (fun i j => raw1656 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1656step0 raw1656; decide +kernel
      have hl : raw1656step0Labels = raw1656Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1656 raw1656Labels permutation152 permutation4
    mixedMoment B raw1656step0 raw1656step0Labels = mixedMoment B raw1656step1 raw1656step1Labels := by
      have ha : raw1656step1 = raw1656step0 := by apply Matrix.ext; unfold raw1656step1 raw1656step0; decide +kernel
      have hl : raw1656step0Labels = labelEmbedding7 ∘ raw1656step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1656step0 raw1656step0Labels raw1656step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

theorem canonical1657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1657 raw1657Labels = mixedMoment B node1913 node1913Labels := by
  calc
    mixedMoment B raw1657 raw1657Labels = mixedMoment B raw1657step0 raw1657step0Labels := by
      have ha : raw1657step0 = (fun i j => raw1657 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1657step0 raw1657; decide +kernel
      have hl : raw1657step0Labels = raw1657Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1657 raw1657Labels permutation152 permutation4
    _ = mixedMoment B node1913 node1913Labels := by rfl

theorem canonical1658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1658 raw1658Labels = mixedMoment B node1922 node1922Labels := by
  calc
    mixedMoment B raw1658 raw1658Labels = mixedMoment B raw1658step0 raw1658step0Labels := by
      have ha : raw1658step0 = (fun i j => raw1658 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1658step0 raw1658; decide +kernel
      have hl : raw1658step0Labels = raw1658Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1658 raw1658Labels permutation170 permutation6
    mixedMoment B raw1658step0 raw1658step0Labels = mixedMoment B raw1658step1 raw1658step1Labels := by
      have ha : raw1658step1 = -raw1658step0 := by apply Matrix.ext; change ∀ i j, raw1658step1 i j = -(raw1658step0 i j); unfold raw1658step1 raw1658step0; decide +kernel
      have hl : raw1658step1Labels = raw1658step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1658step1 raw1658step1Labels = mixedMoment B raw1658step2 raw1658step2Labels := by
      have ha : raw1658step2 = raw1658step1 := by apply Matrix.ext; unfold raw1658step2 raw1658step1; decide +kernel
      have hl : raw1658step1Labels = labelEmbedding1 ∘ raw1658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1658step1 raw1658step1Labels raw1658step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1922 node1922Labels := by rfl

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

theorem canonical1740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1740 raw1740Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw1740 raw1740Labels = mixedMoment B raw1740step0 raw1740step0Labels := by
      have ha : raw1740step0 = (fun i j => raw1740 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1740step0 raw1740; decide +kernel
      have hl : raw1740step0Labels = raw1740Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1740 raw1740Labels permutation152 permutation4
    mixedMoment B raw1740step0 raw1740step0Labels = mixedMoment B raw1740step1 raw1740step1Labels := by
      have ha : raw1740step1 = raw1740step0 := by apply Matrix.ext; unfold raw1740step1 raw1740step0; decide +kernel
      have hl : raw1740step0Labels = labelEmbedding7 ∘ raw1740step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1740step0 raw1740step0Labels raw1740step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical1741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1741 raw1741Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw1741 raw1741Labels = mixedMoment B raw1741step0 raw1741step0Labels := by
      have ha : raw1741step0 = (fun i j => raw1741 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1741step0 raw1741; decide +kernel
      have hl : raw1741step0Labels = raw1741Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1741 raw1741Labels permutation152 permutation4
    _ = mixedMoment B node2023 node2023Labels := by rfl

theorem canonical1742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1742 raw1742Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw1742 raw1742Labels = mixedMoment B raw1742step0 raw1742step0Labels := by
      have ha : raw1742step0 = (fun i j => raw1742 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1742step0 raw1742; decide +kernel
      have hl : raw1742step0Labels = raw1742Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1742 raw1742Labels permutation170 permutation6
    mixedMoment B raw1742step0 raw1742step0Labels = mixedMoment B raw1742step1 raw1742step1Labels := by
      have ha : raw1742step1 = -raw1742step0 := by apply Matrix.ext; change ∀ i j, raw1742step1 i j = -(raw1742step0 i j); unfold raw1742step1 raw1742step0; decide +kernel
      have hl : raw1742step1Labels = raw1742step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1742step1 raw1742step1Labels = mixedMoment B raw1742step2 raw1742step2Labels := by
      have ha : raw1742step2 = raw1742step1 := by apply Matrix.ext; unfold raw1742step2 raw1742step1; decide +kernel
      have hl : raw1742step1Labels = labelEmbedding1 ∘ raw1742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1742step1 raw1742step1Labels raw1742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

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

theorem canonical1746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1746 raw1746Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw1746 raw1746Labels = mixedMoment B raw1746step0 raw1746step0Labels := by
      have ha : raw1746step0 = (fun i j => raw1746 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1746step0 raw1746; decide +kernel
      have hl : raw1746step0Labels = raw1746Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1746 raw1746Labels permutation32 permutation4
    mixedMoment B raw1746step0 raw1746step0Labels = mixedMoment B raw1746step1 raw1746step1Labels := by
      have ha : raw1746step1 = raw1746step0 := by apply Matrix.ext; unfold raw1746step1 raw1746step0; decide +kernel
      have hl : raw1746step0Labels = labelEmbedding7 ∘ raw1746step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1746step0 raw1746step0Labels raw1746step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical1747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1747 raw1747Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw1747 raw1747Labels = mixedMoment B raw1747step0 raw1747step0Labels := by
      have ha : raw1747step0 = (fun i j => raw1747 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1747step0 raw1747; decide +kernel
      have hl : raw1747step0Labels = raw1747Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1747 raw1747Labels permutation32 permutation4
    _ = mixedMoment B node2028 node2028Labels := by rfl

theorem canonical1748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1748 raw1748Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw1748 raw1748Labels = mixedMoment B raw1748step0 raw1748step0Labels := by
      have ha : raw1748step0 = (fun i j => raw1748 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1748step0 raw1748; decide +kernel
      have hl : raw1748step0Labels = raw1748Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1748 raw1748Labels permutation34 permutation6
    mixedMoment B raw1748step0 raw1748step0Labels = mixedMoment B raw1748step1 raw1748step1Labels := by
      have ha : raw1748step1 = -raw1748step0 := by apply Matrix.ext; change ∀ i j, raw1748step1 i j = -(raw1748step0 i j); unfold raw1748step1 raw1748step0; decide +kernel
      have hl : raw1748step1Labels = raw1748step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1748step1 raw1748step1Labels = mixedMoment B raw1748step2 raw1748step2Labels := by
      have ha : raw1748step2 = raw1748step1 := by apply Matrix.ext; unfold raw1748step2 raw1748step1; decide +kernel
      have hl : raw1748step1Labels = labelEmbedding1 ∘ raw1748step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1748step1 raw1748step1Labels raw1748step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical1770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1770 raw1770Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw1770 raw1770Labels = mixedMoment B raw1770step0 raw1770step0Labels := by
      have ha : raw1770step0 = (fun i j => raw1770 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1770step0 raw1770; decide +kernel
      have hl : raw1770step0Labels = raw1770Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1770 raw1770Labels permutation32 permutation4
    mixedMoment B raw1770step0 raw1770step0Labels = mixedMoment B raw1770step1 raw1770step1Labels := by
      have ha : raw1770step1 = raw1770step0 := by apply Matrix.ext; unfold raw1770step1 raw1770step0; decide +kernel
      have hl : raw1770step0Labels = labelEmbedding7 ∘ raw1770step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1770step0 raw1770step0Labels raw1770step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical1771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1771 raw1771Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw1771 raw1771Labels = mixedMoment B raw1771step0 raw1771step0Labels := by
      have ha : raw1771step0 = (fun i j => raw1771 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1771step0 raw1771; decide +kernel
      have hl : raw1771step0Labels = raw1771Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1771 raw1771Labels permutation32 permutation4
    _ = mixedMoment B node2058 node2058Labels := by rfl

theorem canonical1772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1772 raw1772Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw1772 raw1772Labels = mixedMoment B raw1772step0 raw1772step0Labels := by
      have ha : raw1772step0 = (fun i j => raw1772 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1772step0 raw1772; decide +kernel
      have hl : raw1772step0Labels = raw1772Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1772 raw1772Labels permutation36 permutation6
    mixedMoment B raw1772step0 raw1772step0Labels = mixedMoment B raw1772step1 raw1772step1Labels := by
      have ha : raw1772step1 = -raw1772step0 := by apply Matrix.ext; change ∀ i j, raw1772step1 i j = -(raw1772step0 i j); unfold raw1772step1 raw1772step0; decide +kernel
      have hl : raw1772step1Labels = raw1772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1772step1 raw1772step1Labels = mixedMoment B raw1772step2 raw1772step2Labels := by
      have ha : raw1772step2 = raw1772step1 := by apply Matrix.ext; unfold raw1772step2 raw1772step1; decide +kernel
      have hl : raw1772step1Labels = labelEmbedding1 ∘ raw1772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1772step1 raw1772step1Labels raw1772step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

theorem canonical1788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1788 raw1788Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw1788 raw1788Labels = mixedMoment B raw1788step0 raw1788step0Labels := by
      have ha : raw1788step0 = (fun i j => raw1788 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1788step0 raw1788; decide +kernel
      have hl : raw1788step0Labels = raw1788Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1788 raw1788Labels permutation152 permutation4
    mixedMoment B raw1788step0 raw1788step0Labels = mixedMoment B raw1788step1 raw1788step1Labels := by
      have ha : raw1788step1 = raw1788step0 := by apply Matrix.ext; unfold raw1788step1 raw1788step0; decide +kernel
      have hl : raw1788step0Labels = labelEmbedding7 ∘ raw1788step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1788step0 raw1788step0Labels raw1788step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

theorem canonical1789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1789 raw1789Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw1789 raw1789Labels = mixedMoment B raw1789step0 raw1789step0Labels := by
      have ha : raw1789step0 = (fun i j => raw1789 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1789step0 raw1789; decide +kernel
      have hl : raw1789step0Labels = raw1789Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1789 raw1789Labels permutation152 permutation4
    _ = mixedMoment B node2105 node2105Labels := by rfl

theorem canonical1790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1790 raw1790Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw1790 raw1790Labels = mixedMoment B raw1790step0 raw1790step0Labels := by
      have ha : raw1790step0 = (fun i j => raw1790 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1790step0 raw1790; decide +kernel
      have hl : raw1790step0Labels = raw1790Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1790 raw1790Labels permutation182 permutation6
    mixedMoment B raw1790step0 raw1790step0Labels = mixedMoment B raw1790step1 raw1790step1Labels := by
      have ha : raw1790step1 = -raw1790step0 := by apply Matrix.ext; change ∀ i j, raw1790step1 i j = -(raw1790step0 i j); unfold raw1790step1 raw1790step0; decide +kernel
      have hl : raw1790step1Labels = raw1790step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1790step1 raw1790step1Labels = mixedMoment B raw1790step2 raw1790step2Labels := by
      have ha : raw1790step2 = raw1790step1 := by apply Matrix.ext; unfold raw1790step2 raw1790step1; decide +kernel
      have hl : raw1790step1Labels = labelEmbedding1 ∘ raw1790step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1790step1 raw1790step1Labels raw1790step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2241 node2241Labels := by rfl

theorem canonical1791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1791 raw1791Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw1791 raw1791Labels = mixedMoment B raw1791step0 raw1791step0Labels := by
      have ha : raw1791step0 = (fun i j => raw1791 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1791step0 raw1791; decide +kernel
      have hl : raw1791step0Labels = raw1791Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1791 raw1791Labels permutation32 permutation4
    mixedMoment B raw1791step0 raw1791step0Labels = mixedMoment B raw1791step1 raw1791step1Labels := by
      have ha : raw1791step1 = raw1791step0 := by apply Matrix.ext; unfold raw1791step1 raw1791step0; decide +kernel
      have hl : raw1791step0Labels = labelEmbedding7 ∘ raw1791step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1791step0 raw1791step0Labels raw1791step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

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

theorem canonical1792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1792 raw1792Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw1792 raw1792Labels = mixedMoment B raw1792step0 raw1792step0Labels := by
      have ha : raw1792step0 = (fun i j => raw1792 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1792step0 raw1792; decide +kernel
      have hl : raw1792step0Labels = raw1792Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1792 raw1792Labels permutation32 permutation4
    _ = mixedMoment B node2106 node2106Labels := by rfl

theorem canonical1793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1793 raw1793Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw1793 raw1793Labels = mixedMoment B raw1793step0 raw1793step0Labels := by
      have ha : raw1793step0 = (fun i j => raw1793 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1793step0 raw1793; decide +kernel
      have hl : raw1793step0Labels = raw1793Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1793 raw1793Labels permutation40 permutation6
    mixedMoment B raw1793step0 raw1793step0Labels = mixedMoment B raw1793step1 raw1793step1Labels := by
      have ha : raw1793step1 = -raw1793step0 := by apply Matrix.ext; change ∀ i j, raw1793step1 i j = -(raw1793step0 i j); unfold raw1793step1 raw1793step0; decide +kernel
      have hl : raw1793step1Labels = raw1793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1793step1 raw1793step1Labels = mixedMoment B raw1793step2 raw1793step2Labels := by
      have ha : raw1793step2 = raw1793step1 := by apply Matrix.ext; unfold raw1793step2 raw1793step1; decide +kernel
      have hl : raw1793step1Labels = labelEmbedding1 ∘ raw1793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1793step1 raw1793step1Labels raw1793step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical1794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1794 raw1794Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw1794 raw1794Labels = mixedMoment B raw1794step0 raw1794step0Labels := by
      have ha : raw1794step0 = (fun i j => raw1794 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1794step0 raw1794; decide +kernel
      have hl : raw1794step0Labels = raw1794Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1794 raw1794Labels permutation32 permutation4
    mixedMoment B raw1794step0 raw1794step0Labels = mixedMoment B raw1794step1 raw1794step1Labels := by
      have ha : raw1794step1 = raw1794step0 := by apply Matrix.ext; unfold raw1794step1 raw1794step0; decide +kernel
      have hl : raw1794step0Labels = labelEmbedding7 ∘ raw1794step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1794step0 raw1794step0Labels raw1794step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical1795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1795 raw1795Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw1795 raw1795Labels = mixedMoment B raw1795step0 raw1795step0Labels := by
      have ha : raw1795step0 = (fun i j => raw1795 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1795step0 raw1795; decide +kernel
      have hl : raw1795step0Labels = raw1795Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1795 raw1795Labels permutation32 permutation4
    _ = mixedMoment B node2107 node2107Labels := by rfl

theorem canonical1796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1796 raw1796Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw1796 raw1796Labels = mixedMoment B raw1796step0 raw1796step0Labels := by
      have ha : raw1796step0 = (fun i j => raw1796 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1796step0 raw1796; decide +kernel
      have hl : raw1796step0Labels = raw1796Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1796 raw1796Labels permutation38 permutation6
    mixedMoment B raw1796step0 raw1796step0Labels = mixedMoment B raw1796step1 raw1796step1Labels := by
      have ha : raw1796step1 = -raw1796step0 := by apply Matrix.ext; change ∀ i j, raw1796step1 i j = -(raw1796step0 i j); unfold raw1796step1 raw1796step0; decide +kernel
      have hl : raw1796step1Labels = raw1796step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1796step1 raw1796step1Labels = mixedMoment B raw1796step2 raw1796step2Labels := by
      have ha : raw1796step2 = raw1796step1 := by apply Matrix.ext; unfold raw1796step2 raw1796step1; decide +kernel
      have hl : raw1796step1Labels = labelEmbedding1 ∘ raw1796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1796step1 raw1796step1Labels raw1796step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical1818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1818 raw1818Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw1818 raw1818Labels = mixedMoment B raw1818step0 raw1818step0Labels := by
      have ha : raw1818step0 = (fun i j => raw1818 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1818step0 raw1818; decide +kernel
      have hl : raw1818step0Labels = raw1818Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1818 raw1818Labels permutation32 permutation4
    mixedMoment B raw1818step0 raw1818step0Labels = mixedMoment B raw1818step1 raw1818step1Labels := by
      have ha : raw1818step1 = raw1818step0 := by apply Matrix.ext; unfold raw1818step1 raw1818step0; decide +kernel
      have hl : raw1818step0Labels = labelEmbedding7 ∘ raw1818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1818step0 raw1818step0Labels raw1818step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical1819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1819 raw1819Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw1819 raw1819Labels = mixedMoment B raw1819step0 raw1819step0Labels := by
      have ha : raw1819step0 = (fun i j => raw1819 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1819step0 raw1819; decide +kernel
      have hl : raw1819step0Labels = raw1819Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1819 raw1819Labels permutation32 permutation4
    _ = mixedMoment B node2245 node2245Labels := by rfl

theorem canonical1820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1820 raw1820Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw1820 raw1820Labels = mixedMoment B raw1820step0 raw1820step0Labels := by
      have ha : raw1820step0 = (fun i j => raw1820 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1820step0 raw1820; decide +kernel
      have hl : raw1820step0Labels = raw1820Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1820 raw1820Labels permutation50 permutation6
    mixedMoment B raw1820step0 raw1820step0Labels = mixedMoment B raw1820step1 raw1820step1Labels := by
      have ha : raw1820step1 = -raw1820step0 := by apply Matrix.ext; change ∀ i j, raw1820step1 i j = -(raw1820step0 i j); unfold raw1820step1 raw1820step0; decide +kernel
      have hl : raw1820step1Labels = raw1820step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1820step1 raw1820step1Labels = mixedMoment B raw1820step2 raw1820step2Labels := by
      have ha : raw1820step2 = raw1820step1 := by apply Matrix.ext; unfold raw1820step2 raw1820step1; decide +kernel
      have hl : raw1820step1Labels = labelEmbedding1 ∘ raw1820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1820step1 raw1820step1Labels raw1820step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

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

theorem canonical1824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1824 raw1824Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw1824 raw1824Labels = mixedMoment B raw1824step0 raw1824step0Labels := by
      have ha : raw1824step0 = (fun i j => raw1824 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1824step0 raw1824; decide +kernel
      have hl : raw1824step0Labels = raw1824Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1824 raw1824Labels permutation8 permutation4
    mixedMoment B raw1824step0 raw1824step0Labels = mixedMoment B raw1824step1 raw1824step1Labels := by
      have ha : raw1824step1 = raw1824step0 := by apply Matrix.ext; unfold raw1824step1 raw1824step0; decide +kernel
      have hl : raw1824step0Labels = labelEmbedding7 ∘ raw1824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1824step0 raw1824step0Labels raw1824step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical1825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1825 raw1825Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw1825 raw1825Labels = mixedMoment B raw1825step0 raw1825step0Labels := by
      have ha : raw1825step0 = (fun i j => raw1825 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1825step0 raw1825; decide +kernel
      have hl : raw1825step0Labels = raw1825Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1825 raw1825Labels permutation8 permutation4
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical1826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1826 raw1826Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw1826 raw1826Labels = mixedMoment B raw1826step0 raw1826step0Labels := by
      have ha : raw1826step0 = (fun i j => raw1826 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1826step0 raw1826; decide +kernel
      have hl : raw1826step0Labels = raw1826Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1826 raw1826Labels permutation12 permutation6
    mixedMoment B raw1826step0 raw1826step0Labels = mixedMoment B raw1826step1 raw1826step1Labels := by
      have ha : raw1826step1 = -raw1826step0 := by apply Matrix.ext; change ∀ i j, raw1826step1 i j = -(raw1826step0 i j); unfold raw1826step1 raw1826step0; decide +kernel
      have hl : raw1826step1Labels = raw1826step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1826step1 raw1826step1Labels = mixedMoment B raw1826step2 raw1826step2Labels := by
      have ha : raw1826step2 = raw1826step1 := by apply Matrix.ext; unfold raw1826step2 raw1826step1; decide +kernel
      have hl : raw1826step1Labels = labelEmbedding1 ∘ raw1826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1826step1 raw1826step1Labels raw1826step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

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

theorem canonical2487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2487 raw2487Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw2487 raw2487Labels = mixedMoment B raw2487step0 raw2487step0Labels := by
      have ha : raw2487step0 = (fun i j => raw2487 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2487step0 raw2487; decide +kernel
      have hl : raw2487step0Labels = raw2487Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2487 raw2487Labels permutation152 permutation4
    mixedMoment B raw2487step0 raw2487step0Labels = mixedMoment B raw2487step1 raw2487step1Labels := by
      have ha : raw2487step1 = raw2487step0 := by apply Matrix.ext; unfold raw2487step1 raw2487step0; decide +kernel
      have hl : raw2487step0Labels = labelEmbedding7 ∘ raw2487step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2487step0 raw2487step0Labels raw2487step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2488 raw2488Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw2488 raw2488Labels = mixedMoment B raw2488step0 raw2488step0Labels := by
      have ha : raw2488step0 = (fun i j => raw2488 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2488step0 raw2488; decide +kernel
      have hl : raw2488step0Labels = raw2488Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2488 raw2488Labels permutation152 permutation4
    _ = mixedMoment B node3801 node3801Labels := by rfl

theorem canonical2489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2489 raw2489Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw2489 raw2489Labels = mixedMoment B raw2489step0 raw2489step0Labels := by
      have ha : raw2489step0 = (fun i j => raw2489 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2489step0 raw2489; decide +kernel
      have hl : raw2489step0Labels = raw2489Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2489 raw2489Labels permutation170 permutation6
    mixedMoment B raw2489step0 raw2489step0Labels = mixedMoment B raw2489step1 raw2489step1Labels := by
      have ha : raw2489step1 = -raw2489step0 := by apply Matrix.ext; change ∀ i j, raw2489step1 i j = -(raw2489step0 i j); unfold raw2489step1 raw2489step0; decide +kernel
      have hl : raw2489step1Labels = raw2489step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2489step1 raw2489step1Labels = mixedMoment B raw2489step2 raw2489step2Labels := by
      have ha : raw2489step2 = raw2489step1 := by apply Matrix.ext; unfold raw2489step2 raw2489step1; decide +kernel
      have hl : raw2489step1Labels = labelEmbedding1 ∘ raw2489step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2489step1 raw2489step1Labels raw2489step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

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

theorem canonical2565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2565 raw2565Labels = mixedMoment B node5453 node5453Labels := by
  calc
    _ = mixedMoment B node5453 node5453Labels := by rfl

theorem canonical2566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2566 raw2566Labels = mixedMoment B node3912 node3912Labels := by
  calc
    _ = mixedMoment B node3912 node3912Labels := by rfl

theorem canonical2567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2567 raw2567Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw2567 raw2567Labels = mixedMoment B raw2567step0 raw2567step0Labels := by
      have ha : raw2567step0 = (fun i j => raw2567 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2567step0 raw2567; decide +kernel
      have hl : raw2567step0Labels = raw2567Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2567 raw2567Labels permutation29 permutation3
    mixedMoment B raw2567step0 raw2567step0Labels = mixedMoment B raw2567step1 raw2567step1Labels := by
      have ha : raw2567step1 = -raw2567step0 := by apply Matrix.ext; change ∀ i j, raw2567step1 i j = -(raw2567step0 i j); unfold raw2567step1 raw2567step0; decide +kernel
      have hl : raw2567step1Labels = raw2567step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2567step1 raw2567step1Labels = mixedMoment B raw2567step2 raw2567step2Labels := by
      have ha : raw2567step2 = raw2567step1 := by apply Matrix.ext; unfold raw2567step2 raw2567step1; decide +kernel
      have hl : raw2567step1Labels = labelEmbedding1 ∘ raw2567step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2567step1 raw2567step1Labels raw2567step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3912 node3912Labels := by rfl

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

theorem canonical550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw550 raw550Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw550 raw550Labels = mixedMoment B raw550step0 raw550step0Labels := by
      have ha : raw550step0 = (fun i j => raw550 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw550step0 raw550; decide +kernel
      have hl : raw550step0Labels = raw550Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw550 raw550Labels permutation8 permutation5
    mixedMoment B raw550step0 raw550step0Labels = mixedMoment B raw550step1 raw550step1Labels := by
      have ha : raw550step1 = raw550step0 := by apply Matrix.ext; unfold raw550step1 raw550step0; decide +kernel
      have hl : raw550step0Labels = labelEmbedding1 ∘ raw550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw550step0 raw550step0Labels raw550step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3912 node3912Labels := by rfl

theorem canonical551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw551 raw551Labels = mixedMoment B node505 node505Labels := by
  calc
    mixedMoment B raw551 raw551Labels = mixedMoment B raw551step0 raw551step0Labels := by
      have ha : raw551step0 = (fun i j => raw551 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw551step0 raw551; decide +kernel
      have hl : raw551step0Labels = raw551Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw551 raw551Labels permutation29 permutation4
    mixedMoment B raw551step0 raw551step0Labels = mixedMoment B raw551step1 raw551step1Labels := by
      have ha : raw551step1 = -raw551step0 := by apply Matrix.ext; change ∀ i j, raw551step1 i j = -(raw551step0 i j); unfold raw551step1 raw551step0; decide +kernel
      have hl : raw551step1Labels = raw551step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node505 node505Labels := by rfl

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

theorem canonical975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw975 raw975Labels = mixedMoment B node4252 node4252Labels := by
  calc
    mixedMoment B raw975 raw975Labels = mixedMoment B raw975step0 raw975step0Labels := by
      have ha : raw975step0 = (fun i j => raw975 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw975step0 raw975; decide +kernel
      have hl : raw975step0Labels = raw975Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw975 raw975Labels permutation152 permutation4
    mixedMoment B raw975step0 raw975step0Labels = mixedMoment B raw975step1 raw975step1Labels := by
      have ha : raw975step1 = raw975step0 := by apply Matrix.ext; unfold raw975step1 raw975step0; decide +kernel
      have hl : raw975step0Labels = labelEmbedding7 ∘ raw975step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw975step0 raw975step0Labels raw975step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4252 node4252Labels := by rfl

theorem canonical976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw976 raw976Labels = mixedMoment B node786 node786Labels := by
  calc
    mixedMoment B raw976 raw976Labels = mixedMoment B raw976step0 raw976step0Labels := by
      have ha : raw976step0 = (fun i j => raw976 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw976step0 raw976; decide +kernel
      have hl : raw976step0Labels = raw976Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw976 raw976Labels permutation152 permutation4
    _ = mixedMoment B node786 node786Labels := by rfl

theorem canonical977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw977 raw977Labels = mixedMoment B node822 node822Labels := by
  calc
    mixedMoment B raw977 raw977Labels = mixedMoment B raw977step0 raw977step0Labels := by
      have ha : raw977step0 = (fun i j => raw977 (permutation246 i) (permutation6 j)) := by apply Matrix.ext; unfold raw977step0 raw977; decide +kernel
      have hl : raw977step0Labels = raw977Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw977 raw977Labels permutation246 permutation6
    mixedMoment B raw977step0 raw977step0Labels = mixedMoment B raw977step1 raw977step1Labels := by
      have ha : raw977step1 = -raw977step0 := by apply Matrix.ext; change ∀ i j, raw977step1 i j = -(raw977step0 i j); unfold raw977step1 raw977step0; decide +kernel
      have hl : raw977step1Labels = raw977step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw977step1 raw977step1Labels = mixedMoment B raw977step2 raw977step2Labels := by
      have ha : raw977step2 = raw977step1 := by apply Matrix.ext; unfold raw977step2 raw977step1; decide +kernel
      have hl : raw977step1Labels = labelEmbedding1 ∘ raw977step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw977step1 raw977step1Labels raw977step2Labels labelEmbedding1 hl
    _ = mixedMoment B node822 node822Labels := by rfl

theorem canonical978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw978 raw978Labels = mixedMoment B node4253 node4253Labels := by
  calc
    mixedMoment B raw978 raw978Labels = mixedMoment B raw978step0 raw978step0Labels := by
      have ha : raw978step0 = (fun i j => raw978 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw978step0 raw978; decide +kernel
      have hl : raw978step0Labels = raw978Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw978 raw978Labels permutation32 permutation4
    mixedMoment B raw978step0 raw978step0Labels = mixedMoment B raw978step1 raw978step1Labels := by
      have ha : raw978step1 = raw978step0 := by apply Matrix.ext; unfold raw978step1 raw978step0; decide +kernel
      have hl : raw978step0Labels = labelEmbedding7 ∘ raw978step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw978step0 raw978step0Labels raw978step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4253 node4253Labels := by rfl

theorem canonical979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw979 raw979Labels = mixedMoment B node787 node787Labels := by
  calc
    mixedMoment B raw979 raw979Labels = mixedMoment B raw979step0 raw979step0Labels := by
      have ha : raw979step0 = (fun i j => raw979 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw979step0 raw979; decide +kernel
      have hl : raw979step0Labels = raw979Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw979 raw979Labels permutation32 permutation4
    _ = mixedMoment B node787 node787Labels := by rfl

theorem canonical980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw980 raw980Labels = mixedMoment B node847 node847Labels := by
  calc
    mixedMoment B raw980 raw980Labels = mixedMoment B raw980step0 raw980step0Labels := by
      have ha : raw980step0 = (fun i j => raw980 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw980step0 raw980; decide +kernel
      have hl : raw980step0Labels = raw980Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw980 raw980Labels permutation32 permutation6
    mixedMoment B raw980step0 raw980step0Labels = mixedMoment B raw980step1 raw980step1Labels := by
      have ha : raw980step1 = -raw980step0 := by apply Matrix.ext; change ∀ i j, raw980step1 i j = -(raw980step0 i j); unfold raw980step1 raw980step0; decide +kernel
      have hl : raw980step1Labels = raw980step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw980step1 raw980step1Labels = mixedMoment B raw980step2 raw980step2Labels := by
      have ha : raw980step2 = raw980step1 := by apply Matrix.ext; unfold raw980step2 raw980step1; decide +kernel
      have hl : raw980step1Labels = labelEmbedding1 ∘ raw980step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw980step1 raw980step1Labels raw980step2Labels labelEmbedding1 hl
    _ = mixedMoment B node847 node847Labels := by rfl

theorem canonical981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw981 raw981Labels = mixedMoment B node4255 node4255Labels := by
  calc
    mixedMoment B raw981 raw981Labels = mixedMoment B raw981step0 raw981step0Labels := by
      have ha : raw981step0 = (fun i j => raw981 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw981step0 raw981; decide +kernel
      have hl : raw981step0Labels = raw981Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw981 raw981Labels permutation32 permutation4
    mixedMoment B raw981step0 raw981step0Labels = mixedMoment B raw981step1 raw981step1Labels := by
      have ha : raw981step1 = raw981step0 := by apply Matrix.ext; unfold raw981step1 raw981step0; decide +kernel
      have hl : raw981step0Labels = labelEmbedding7 ∘ raw981step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw981step0 raw981step0Labels raw981step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4255 node4255Labels := by rfl

theorem canonical982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw982 raw982Labels = mixedMoment B node789 node789Labels := by
  calc
    mixedMoment B raw982 raw982Labels = mixedMoment B raw982step0 raw982step0Labels := by
      have ha : raw982step0 = (fun i j => raw982 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw982step0 raw982; decide +kernel
      have hl : raw982step0Labels = raw982Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw982 raw982Labels permutation32 permutation4
    _ = mixedMoment B node789 node789Labels := by rfl

theorem canonical983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw983 raw983Labels = mixedMoment B node823 node823Labels := by
  calc
    mixedMoment B raw983 raw983Labels = mixedMoment B raw983step0 raw983step0Labels := by
      have ha : raw983step0 = (fun i j => raw983 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw983step0 raw983; decide +kernel
      have hl : raw983step0Labels = raw983Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw983 raw983Labels permutation44 permutation6
    mixedMoment B raw983step0 raw983step0Labels = mixedMoment B raw983step1 raw983step1Labels := by
      have ha : raw983step1 = -raw983step0 := by apply Matrix.ext; change ∀ i j, raw983step1 i j = -(raw983step0 i j); unfold raw983step1 raw983step0; decide +kernel
      have hl : raw983step1Labels = raw983step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw983step1 raw983step1Labels = mixedMoment B raw983step2 raw983step2Labels := by
      have ha : raw983step2 = raw983step1 := by apply Matrix.ext; unfold raw983step2 raw983step1; decide +kernel
      have hl : raw983step1Labels = labelEmbedding1 ∘ raw983step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw983step1 raw983step1Labels raw983step2Labels labelEmbedding1 hl
    _ = mixedMoment B node823 node823Labels := by rfl

theorem canonical993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw993 raw993Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw993 raw993Labels = mixedMoment B raw993step0 raw993step0Labels := by
      have ha : raw993step0 = (fun i j => raw993 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw993step0 raw993; decide +kernel
      have hl : raw993step0Labels = raw993Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw993 raw993Labels permutation32 permutation4
    mixedMoment B raw993step0 raw993step0Labels = mixedMoment B raw993step1 raw993step1Labels := by
      have ha : raw993step1 = raw993step0 := by apply Matrix.ext; unfold raw993step1 raw993step0; decide +kernel
      have hl : raw993step0Labels = labelEmbedding7 ∘ raw993step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw993step0 raw993step0Labels raw993step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

theorem canonical994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw994 raw994Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw994 raw994Labels = mixedMoment B raw994step0 raw994step0Labels := by
      have ha : raw994step0 = (fun i j => raw994 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw994step0 raw994; decide +kernel
      have hl : raw994step0Labels = raw994Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw994 raw994Labels permutation32 permutation4
    _ = mixedMoment B node811 node811Labels := by rfl

theorem canonical995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw995 raw995Labels = mixedMoment B node824 node824Labels := by
  calc
    mixedMoment B raw995 raw995Labels = mixedMoment B raw995step0 raw995step0Labels := by
      have ha : raw995step0 = (fun i j => raw995 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw995step0 raw995; decide +kernel
      have hl : raw995step0Labels = raw995Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw995 raw995Labels permutation50 permutation6
    mixedMoment B raw995step0 raw995step0Labels = mixedMoment B raw995step1 raw995step1Labels := by
      have ha : raw995step1 = -raw995step0 := by apply Matrix.ext; change ∀ i j, raw995step1 i j = -(raw995step0 i j); unfold raw995step1 raw995step0; decide +kernel
      have hl : raw995step1Labels = raw995step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw995step1 raw995step1Labels = mixedMoment B raw995step2 raw995step2Labels := by
      have ha : raw995step2 = raw995step1 := by apply Matrix.ext; unfold raw995step2 raw995step1; decide +kernel
      have hl : raw995step1Labels = labelEmbedding1 ∘ raw995step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw995step1 raw995step1Labels raw995step2Labels labelEmbedding1 hl
    _ = mixedMoment B node824 node824Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11102 raw11102Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw11102 raw11102Labels = mixedMoment B raw11102step0 raw11102step0Labels := by
      have hz : ∀ j, raw11102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11102step0 = (fun i j => raw11102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11102step0 raw11102; decide +kernel
      have hl : raw11102step0Labels = raw11102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11102 raw11102Labels permutation434 hz
    mixedMoment B raw11102step0 raw11102step0Labels = mixedMoment B raw11102step1 raw11102step1Labels := by
      have ha : raw11102step1 = (fun i j => raw11102step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11102step1 raw11102step0; decide +kernel
      have hl : raw11102step1Labels = raw11102step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11102step0 raw11102step0Labels permutation151 permutation2
    mixedMoment B raw11102step1 raw11102step1Labels = mixedMoment B raw11102step2 raw11102step2Labels := by
      have ha : raw11102step2 = -raw11102step1 := by apply Matrix.ext; change ∀ i j, raw11102step2 i j = -(raw11102step1 i j); unfold raw11102step2 raw11102step1; decide +kernel
      have hl : raw11102step2Labels = raw11102step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical11103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11103 raw11103Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw11103 raw11103Labels = mixedMoment B raw11103step0 raw11103step0Labels := by
      have hz : ∀ j, raw11103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11103step0 = (fun i j => raw11103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11103step0 raw11103; decide +kernel
      have hl : raw11103step0Labels = raw11103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11103 raw11103Labels permutation434 hz
    mixedMoment B raw11103step0 raw11103step0Labels = mixedMoment B raw11103step1 raw11103step1Labels := by
      have ha : raw11103step1 = (fun i j => raw11103step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11103step1 raw11103step0; decide +kernel
      have hl : raw11103step1Labels = raw11103step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11103step0 raw11103step0Labels permutation149 permutation2
    mixedMoment B raw11103step1 raw11103step1Labels = mixedMoment B raw11103step2 raw11103step2Labels := by
      have ha : raw11103step2 = -raw11103step1 := by apply Matrix.ext; change ∀ i j, raw11103step2 i j = -(raw11103step1 i j); unfold raw11103step2 raw11103step1; decide +kernel
      have hl : raw11103step2Labels = raw11103step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical11104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11104 raw11104Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw11104 raw11104Labels = mixedMoment B raw11104step0 raw11104step0Labels := by
      have ha : raw11104step0 = (fun i j => raw11104 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11104step0 raw11104; decide +kernel
      have hl : raw11104step0Labels = raw11104Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11104 raw11104Labels permutation200 permutation3
    mixedMoment B raw11104step0 raw11104step0Labels = mixedMoment B raw11104step1 raw11104step1Labels := by
      have ha : raw11104step1 = raw11104step0 := by apply Matrix.ext; unfold raw11104step1 raw11104step0; decide +kernel
      have hl : raw11104step0Labels = labelEmbedding6 ∘ raw11104step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11104step0 raw11104step0Labels raw11104step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical11105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11105 raw11105Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw11105 raw11105Labels = mixedMoment B raw11105step0 raw11105step0Labels := by
      have hz : ∀ j, raw11105 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11105step0 = (fun i j => raw11105 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11105step0 raw11105; decide +kernel
      have hl : raw11105step0Labels = raw11105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11105 raw11105Labels permutation520 hz
    mixedMoment B raw11105step0 raw11105step0Labels = mixedMoment B raw11105step1 raw11105step1Labels := by
      have hz : ∀ j, raw11105step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11105step1 = (fun i j => raw11105step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11105step1 raw11105step0; decide +kernel
      have hl : raw11105step1Labels = raw11105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11105step0 raw11105step0Labels permutation104 hz
    mixedMoment B raw11105step1 raw11105step1Labels = mixedMoment B raw11105step2 raw11105step2Labels := by
      have ha : raw11105step2 = (fun i j => raw11105step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11105step2 raw11105step1; decide +kernel
      have hl : raw11105step2Labels = raw11105step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11105step1 raw11105step1Labels permutation29 permutation2
    mixedMoment B raw11105step2 raw11105step2Labels = mixedMoment B raw11105step3 raw11105step3Labels := by
      have ha : raw11105step3 = -raw11105step2 := by apply Matrix.ext; change ∀ i j, raw11105step3 i j = -(raw11105step2 i j); unfold raw11105step3 raw11105step2; decide +kernel
      have hl : raw11105step3Labels = raw11105step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5453 node5453Labels := by rfl

theorem canonical11106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11106 raw11106Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw11106 raw11106Labels = mixedMoment B raw11106step0 raw11106step0Labels := by
      have hz : ∀ j, raw11106 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11106step0 = (fun i j => raw11106 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11106step0 raw11106; decide +kernel
      have hl : raw11106step0Labels = raw11106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11106 raw11106Labels permutation434 hz
    mixedMoment B raw11106step0 raw11106step0Labels = mixedMoment B raw11106step1 raw11106step1Labels := by
      have ha : raw11106step1 = (fun i j => raw11106step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11106step1 raw11106step0; decide +kernel
      have hl : raw11106step1Labels = raw11106step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11106step0 raw11106step0Labels permutation50 permutation5
    mixedMoment B raw11106step1 raw11106step1Labels = mixedMoment B raw11106step2 raw11106step2Labels := by
      have ha : raw11106step2 = -raw11106step1 := by apply Matrix.ext; change ∀ i j, raw11106step2 i j = -(raw11106step1 i j); unfold raw11106step2 raw11106step1; decide +kernel
      have hl : raw11106step2Labels = raw11106step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11106step2 raw11106step2Labels = mixedMoment B raw11106step3 raw11106step3Labels := by
      have ha : raw11106step3 = raw11106step2 := by apply Matrix.ext; unfold raw11106step3 raw11106step2; decide +kernel
      have hl : raw11106step2Labels = labelEmbedding8 ∘ raw11106step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11106step2 raw11106step2Labels raw11106step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical11107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11107 raw11107Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw11107 raw11107Labels = mixedMoment B raw11107step0 raw11107step0Labels := by
      have hz : ∀ j, raw11107 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11107step0 = (fun i j => raw11107 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11107step0 raw11107; decide +kernel
      have hl : raw11107step0Labels = raw11107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11107 raw11107Labels permutation434 hz
    mixedMoment B raw11107step0 raw11107step0Labels = mixedMoment B raw11107step1 raw11107step1Labels := by
      have ha : raw11107step1 = (fun i j => raw11107step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11107step1 raw11107step0; decide +kernel
      have hl : raw11107step1Labels = raw11107step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11107step0 raw11107step0Labels permutation40 permutation3
    mixedMoment B raw11107step1 raw11107step1Labels = mixedMoment B raw11107step2 raw11107step2Labels := by
      have ha : raw11107step2 = raw11107step1 := by apply Matrix.ext; unfold raw11107step2 raw11107step1; decide +kernel
      have hl : raw11107step1Labels = labelEmbedding6 ∘ raw11107step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11107step1 raw11107step1Labels raw11107step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

theorem canonical11108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11108 raw11108Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw11108 raw11108Labels = mixedMoment B raw11108step0 raw11108step0Labels := by
      have hz : ∀ j, raw11108 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11108step0 = (fun i j => raw11108 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11108step0 raw11108; decide +kernel
      have hl : raw11108step0Labels = raw11108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11108 raw11108Labels permutation434 hz
    mixedMoment B raw11108step0 raw11108step0Labels = mixedMoment B raw11108step1 raw11108step1Labels := by
      have ha : raw11108step1 = (fun i j => raw11108step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11108step1 raw11108step0; decide +kernel
      have hl : raw11108step1Labels = raw11108step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11108step0 raw11108step0Labels permutation40 permutation3
    mixedMoment B raw11108step1 raw11108step1Labels = mixedMoment B raw11108step2 raw11108step2Labels := by
      have ha : raw11108step2 = raw11108step1 := by apply Matrix.ext; unfold raw11108step2 raw11108step1; decide +kernel
      have hl : raw11108step1Labels = labelEmbedding6 ∘ raw11108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11108step1 raw11108step1Labels raw11108step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical11109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11109 raw11109Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw11109 raw11109Labels = mixedMoment B raw11109step0 raw11109step0Labels := by
      have ha : raw11109step0 = (fun i j => raw11109 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11109step0 raw11109; decide +kernel
      have hl : raw11109step0Labels = raw11109Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11109 raw11109Labels permutation208 permutation3
    mixedMoment B raw11109step0 raw11109step0Labels = mixedMoment B raw11109step1 raw11109step1Labels := by
      have ha : raw11109step1 = raw11109step0 := by apply Matrix.ext; unfold raw11109step1 raw11109step0; decide +kernel
      have hl : raw11109step0Labels = labelEmbedding6 ∘ raw11109step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11109step0 raw11109step0Labels raw11109step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

theorem canonical11110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11110 raw11110Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw11110 raw11110Labels = mixedMoment B raw11110step0 raw11110step0Labels := by
      have hz : ∀ j, raw11110 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11110step0 = (fun i j => raw11110 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11110step0 raw11110; decide +kernel
      have hl : raw11110step0Labels = raw11110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11110 raw11110Labels permutation520 hz
    mixedMoment B raw11110step0 raw11110step0Labels = mixedMoment B raw11110step1 raw11110step1Labels := by
      have hz : ∀ j, raw11110step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11110step1 = (fun i j => raw11110step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11110step1 raw11110step0; decide +kernel
      have hl : raw11110step1Labels = raw11110step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11110step0 raw11110step0Labels permutation104 hz
    mixedMoment B raw11110step1 raw11110step1Labels = mixedMoment B raw11110step2 raw11110step2Labels := by
      have ha : raw11110step2 = (fun i j => raw11110step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11110step2 raw11110step1; decide +kernel
      have hl : raw11110step2Labels = raw11110step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11110step1 raw11110step1Labels permutation10 permutation3
    mixedMoment B raw11110step2 raw11110step2Labels = mixedMoment B raw11110step3 raw11110step3Labels := by
      have ha : raw11110step3 = raw11110step2 := by apply Matrix.ext; unfold raw11110step3 raw11110step2; decide +kernel
      have hl : raw11110step2Labels = labelEmbedding6 ∘ raw11110step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11110step2 raw11110step2Labels raw11110step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical11111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11111 raw11111Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw11111 raw11111Labels = mixedMoment B raw11111step0 raw11111step0Labels := by
      have hz : ∀ j, raw11111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11111step0 = (fun i j => raw11111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11111step0 raw11111; decide +kernel
      have hl : raw11111step0Labels = raw11111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11111 raw11111Labels permutation434 hz
    mixedMoment B raw11111step0 raw11111step0Labels = mixedMoment B raw11111step1 raw11111step1Labels := by
      have ha : raw11111step1 = (fun i j => raw11111step0 (permutation53 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11111step1 raw11111step0; decide +kernel
      have hl : raw11111step1Labels = raw11111step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11111step0 raw11111step0Labels permutation53 permutation5
    mixedMoment B raw11111step1 raw11111step1Labels = mixedMoment B raw11111step2 raw11111step2Labels := by
      have ha : raw11111step2 = -raw11111step1 := by apply Matrix.ext; change ∀ i j, raw11111step2 i j = -(raw11111step1 i j); unfold raw11111step2 raw11111step1; decide +kernel
      have hl : raw11111step2Labels = raw11111step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11111step2 raw11111step2Labels = mixedMoment B raw11111step3 raw11111step3Labels := by
      have ha : raw11111step3 = raw11111step2 := by apply Matrix.ext; unfold raw11111step3 raw11111step2; decide +kernel
      have hl : raw11111step2Labels = labelEmbedding8 ∘ raw11111step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11111step2 raw11111step2Labels raw11111step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical11112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11112 raw11112Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw11112 raw11112Labels = mixedMoment B raw11112step0 raw11112step0Labels := by
      have hz : ∀ j, raw11112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11112step0 = (fun i j => raw11112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11112step0 raw11112; decide +kernel
      have hl : raw11112step0Labels = raw11112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11112 raw11112Labels permutation434 hz
    mixedMoment B raw11112step0 raw11112step0Labels = mixedMoment B raw11112step1 raw11112step1Labels := by
      have ha : raw11112step1 = (fun i j => raw11112step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11112step1 raw11112step0; decide +kernel
      have hl : raw11112step1Labels = raw11112step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11112step0 raw11112step0Labels permutation34 permutation3
    mixedMoment B raw11112step1 raw11112step1Labels = mixedMoment B raw11112step2 raw11112step2Labels := by
      have ha : raw11112step2 = raw11112step1 := by apply Matrix.ext; unfold raw11112step2 raw11112step1; decide +kernel
      have hl : raw11112step1Labels = labelEmbedding6 ∘ raw11112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11112step1 raw11112step1Labels raw11112step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

theorem canonical11113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11113 raw11113Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw11113 raw11113Labels = mixedMoment B raw11113step0 raw11113step0Labels := by
      have hz : ∀ j, raw11113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11113step0 = (fun i j => raw11113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11113step0 raw11113; decide +kernel
      have hl : raw11113step0Labels = raw11113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11113 raw11113Labels permutation434 hz
    mixedMoment B raw11113step0 raw11113step0Labels = mixedMoment B raw11113step1 raw11113step1Labels := by
      have ha : raw11113step1 = (fun i j => raw11113step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11113step1 raw11113step0; decide +kernel
      have hl : raw11113step1Labels = raw11113step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11113step0 raw11113step0Labels permutation34 permutation3
    mixedMoment B raw11113step1 raw11113step1Labels = mixedMoment B raw11113step2 raw11113step2Labels := by
      have ha : raw11113step2 = raw11113step1 := by apply Matrix.ext; unfold raw11113step2 raw11113step1; decide +kernel
      have hl : raw11113step1Labels = labelEmbedding6 ∘ raw11113step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11113step1 raw11113step1Labels raw11113step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical11114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11114 raw11114Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw11114 raw11114Labels = mixedMoment B raw11114step0 raw11114step0Labels := by
      have ha : raw11114step0 = (fun i j => raw11114 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11114step0 raw11114; decide +kernel
      have hl : raw11114step0Labels = raw11114Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11114 raw11114Labels permutation202 permutation3
    mixedMoment B raw11114step0 raw11114step0Labels = mixedMoment B raw11114step1 raw11114step1Labels := by
      have ha : raw11114step1 = raw11114step0 := by apply Matrix.ext; unfold raw11114step1 raw11114step0; decide +kernel
      have hl : raw11114step0Labels = labelEmbedding6 ∘ raw11114step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11114step0 raw11114step0Labels raw11114step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

theorem canonical11115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11115 raw11115Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw11115 raw11115Labels = mixedMoment B raw11115step0 raw11115step0Labels := by
      have hz : ∀ j, raw11115 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11115step0 = (fun i j => raw11115 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11115step0 raw11115; decide +kernel
      have hl : raw11115step0Labels = raw11115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11115 raw11115Labels permutation520 hz
    mixedMoment B raw11115step0 raw11115step0Labels = mixedMoment B raw11115step1 raw11115step1Labels := by
      have hz : ∀ j, raw11115step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11115step1 = (fun i j => raw11115step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11115step1 raw11115step0; decide +kernel
      have hl : raw11115step1Labels = raw11115step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11115step0 raw11115step0Labels permutation104 hz
    mixedMoment B raw11115step1 raw11115step1Labels = mixedMoment B raw11115step2 raw11115step2Labels := by
      have ha : raw11115step2 = (fun i j => raw11115step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11115step2 raw11115step1; decide +kernel
      have hl : raw11115step2Labels = raw11115step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11115step1 raw11115step1Labels permutation8 permutation3
    mixedMoment B raw11115step2 raw11115step2Labels = mixedMoment B raw11115step3 raw11115step3Labels := by
      have ha : raw11115step3 = raw11115step2 := by apply Matrix.ext; unfold raw11115step3 raw11115step2; decide +kernel
      have hl : raw11115step2Labels = labelEmbedding6 ∘ raw11115step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11115step2 raw11115step2Labels raw11115step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical11116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11116 raw11116Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw11116 raw11116Labels = mixedMoment B raw11116step0 raw11116step0Labels := by
      have hz : ∀ j, raw11116 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11116step0 = (fun i j => raw11116 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11116step0 raw11116; decide +kernel
      have hl : raw11116step0Labels = raw11116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11116 raw11116Labels permutation434 hz
    mixedMoment B raw11116step0 raw11116step0Labels = mixedMoment B raw11116step1 raw11116step1Labels := by
      have ha : raw11116step1 = (fun i j => raw11116step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11116step1 raw11116step0; decide +kernel
      have hl : raw11116step1Labels = raw11116step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11116step0 raw11116step0Labels permutation51 permutation5
    mixedMoment B raw11116step1 raw11116step1Labels = mixedMoment B raw11116step2 raw11116step2Labels := by
      have ha : raw11116step2 = -raw11116step1 := by apply Matrix.ext; change ∀ i j, raw11116step2 i j = -(raw11116step1 i j); unfold raw11116step2 raw11116step1; decide +kernel
      have hl : raw11116step2Labels = raw11116step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11116step2 raw11116step2Labels = mixedMoment B raw11116step3 raw11116step3Labels := by
      have ha : raw11116step3 = raw11116step2 := by apply Matrix.ext; unfold raw11116step3 raw11116step2; decide +kernel
      have hl : raw11116step2Labels = labelEmbedding8 ∘ raw11116step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11116step2 raw11116step2Labels raw11116step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical11117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11117 raw11117Labels = mixedMoment B node4252 node4252Labels := by
  calc
    mixedMoment B raw11117 raw11117Labels = mixedMoment B raw11117step0 raw11117step0Labels := by
      have ha : raw11117step0 = (fun i j => raw11117 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11117step0 raw11117; decide +kernel
      have hl : raw11117step0Labels = raw11117Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11117 raw11117Labels permutation152 permutation3
    mixedMoment B raw11117step0 raw11117step0Labels = mixedMoment B raw11117step1 raw11117step1Labels := by
      have ha : raw11117step1 = raw11117step0 := by apply Matrix.ext; unfold raw11117step1 raw11117step0; decide +kernel
      have hl : raw11117step0Labels = labelEmbedding6 ∘ raw11117step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11117step0 raw11117step0Labels raw11117step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4252 node4252Labels := by rfl

theorem canonical11118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11118 raw11118Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw11118 raw11118Labels = mixedMoment B raw11118step0 raw11118step0Labels := by
      have ha : raw11118step0 = (fun i j => raw11118 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11118step0 raw11118; decide +kernel
      have hl : raw11118step0Labels = raw11118Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11118 raw11118Labels permutation152 permutation3
    mixedMoment B raw11118step0 raw11118step0Labels = mixedMoment B raw11118step1 raw11118step1Labels := by
      have ha : raw11118step1 = raw11118step0 := by apply Matrix.ext; unfold raw11118step1 raw11118step0; decide +kernel
      have hl : raw11118step0Labels = labelEmbedding6 ∘ raw11118step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11118step0 raw11118step0Labels raw11118step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical11119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11119 raw11119Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw11119 raw11119Labels = mixedMoment B raw11119step0 raw11119step0Labels := by
      have ha : raw11119step0 = (fun i j => raw11119 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11119step0 raw11119; decide +kernel
      have hl : raw11119step0Labels = raw11119Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11119 raw11119Labels permutation176 permutation3
    mixedMoment B raw11119step0 raw11119step0Labels = mixedMoment B raw11119step1 raw11119step1Labels := by
      have ha : raw11119step1 = raw11119step0 := by apply Matrix.ext; unfold raw11119step1 raw11119step0; decide +kernel
      have hl : raw11119step0Labels = labelEmbedding6 ∘ raw11119step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11119step0 raw11119step0Labels raw11119step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical11120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11120 raw11120Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw11120 raw11120Labels = mixedMoment B raw11120step0 raw11120step0Labels := by
      have hz : ∀ j, raw11120 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11120step0 = (fun i j => raw11120 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11120step0 raw11120; decide +kernel
      have hl : raw11120step0Labels = raw11120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11120 raw11120Labels permutation520 hz
    mixedMoment B raw11120step0 raw11120step0Labels = mixedMoment B raw11120step1 raw11120step1Labels := by
      have ha : raw11120step1 = (fun i j => raw11120step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11120step1 raw11120step0; decide +kernel
      have hl : raw11120step1Labels = raw11120step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11120step0 raw11120step0Labels permutation32 permutation3
    mixedMoment B raw11120step1 raw11120step1Labels = mixedMoment B raw11120step2 raw11120step2Labels := by
      have ha : raw11120step2 = raw11120step1 := by apply Matrix.ext; unfold raw11120step2 raw11120step1; decide +kernel
      have hl : raw11120step1Labels = labelEmbedding6 ∘ raw11120step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11120step1 raw11120step1Labels raw11120step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical11121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11121 raw11121Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw11121 raw11121Labels = mixedMoment B raw11121step0 raw11121step0Labels := by
      have ha : raw11121step0 = (fun i j => raw11121 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11121step0 raw11121; decide +kernel
      have hl : raw11121step0Labels = raw11121Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11121 raw11121Labels permutation246 permutation5
    mixedMoment B raw11121step0 raw11121step0Labels = mixedMoment B raw11121step1 raw11121step1Labels := by
      have ha : raw11121step1 = -raw11121step0 := by apply Matrix.ext; change ∀ i j, raw11121step1 i j = -(raw11121step0 i j); unfold raw11121step1 raw11121step0; decide +kernel
      have hl : raw11121step1Labels = raw11121step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11121step1 raw11121step1Labels = mixedMoment B raw11121step2 raw11121step2Labels := by
      have ha : raw11121step2 = raw11121step1 := by apply Matrix.ext; unfold raw11121step2 raw11121step1; decide +kernel
      have hl : raw11121step1Labels = labelEmbedding8 ∘ raw11121step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11121step1 raw11121step1Labels raw11121step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

theorem canonical11122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11122 raw11122Labels = mixedMoment B node4255 node4255Labels := by
  calc
    mixedMoment B raw11122 raw11122Labels = mixedMoment B raw11122step0 raw11122step0Labels := by
      have hz : ∀ j, raw11122 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11122step0 = (fun i j => raw11122 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11122step0 raw11122; decide +kernel
      have hl : raw11122step0Labels = raw11122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11122 raw11122Labels permutation434 hz
    mixedMoment B raw11122step0 raw11122step0Labels = mixedMoment B raw11122step1 raw11122step1Labels := by
      have ha : raw11122step1 = (fun i j => raw11122step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11122step1 raw11122step0; decide +kernel
      have hl : raw11122step1Labels = raw11122step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11122step0 raw11122step0Labels permutation33 permutation3
    mixedMoment B raw11122step1 raw11122step1Labels = mixedMoment B raw11122step2 raw11122step2Labels := by
      have ha : raw11122step2 = raw11122step1 := by apply Matrix.ext; unfold raw11122step2 raw11122step1; decide +kernel
      have hl : raw11122step1Labels = labelEmbedding6 ∘ raw11122step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11122step1 raw11122step1Labels raw11122step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4255 node4255Labels := by rfl

theorem canonical11123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11123 raw11123Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw11123 raw11123Labels = mixedMoment B raw11123step0 raw11123step0Labels := by
      have hz : ∀ j, raw11123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11123step0 = (fun i j => raw11123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11123step0 raw11123; decide +kernel
      have hl : raw11123step0Labels = raw11123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11123 raw11123Labels permutation434 hz
    mixedMoment B raw11123step0 raw11123step0Labels = mixedMoment B raw11123step1 raw11123step1Labels := by
      have ha : raw11123step1 = (fun i j => raw11123step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11123step1 raw11123step0; decide +kernel
      have hl : raw11123step1Labels = raw11123step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11123step0 raw11123step0Labels permutation33 permutation3
    mixedMoment B raw11123step1 raw11123step1Labels = mixedMoment B raw11123step2 raw11123step2Labels := by
      have ha : raw11123step2 = raw11123step1 := by apply Matrix.ext; unfold raw11123step2 raw11123step1; decide +kernel
      have hl : raw11123step1Labels = labelEmbedding6 ∘ raw11123step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11123step1 raw11123step1Labels raw11123step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical11124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11124 raw11124Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw11124 raw11124Labels = mixedMoment B raw11124step0 raw11124step0Labels := by
      have hz : ∀ j, raw11124 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11124step0 = (fun i j => raw11124 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11124step0 raw11124; decide +kernel
      have hl : raw11124step0Labels = raw11124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11124 raw11124Labels permutation434 hz
    mixedMoment B raw11124step0 raw11124step0Labels = mixedMoment B raw11124step1 raw11124step1Labels := by
      have ha : raw11124step1 = (fun i j => raw11124step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11124step1 raw11124step0; decide +kernel
      have hl : raw11124step1Labels = raw11124step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11124step0 raw11124step0Labels permutation39 permutation3
    mixedMoment B raw11124step1 raw11124step1Labels = mixedMoment B raw11124step2 raw11124step2Labels := by
      have ha : raw11124step2 = raw11124step1 := by apply Matrix.ext; unfold raw11124step2 raw11124step1; decide +kernel
      have hl : raw11124step1Labels = labelEmbedding6 ∘ raw11124step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11124step1 raw11124step1Labels raw11124step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical11125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11125 raw11125Labels = mixedMoment B node4731 node4731Labels := by
  calc
    mixedMoment B raw11125 raw11125Labels = mixedMoment B raw11125step0 raw11125step0Labels := by
      have ha : raw11125step0 = (fun i j => raw11125 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11125step0 raw11125; decide +kernel
      have hl : raw11125step0Labels = raw11125Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11125 raw11125Labels permutation201 permutation3
    mixedMoment B raw11125step0 raw11125step0Labels = mixedMoment B raw11125step1 raw11125step1Labels := by
      have ha : raw11125step1 = raw11125step0 := by apply Matrix.ext; unfold raw11125step1 raw11125step0; decide +kernel
      have hl : raw11125step0Labels = labelEmbedding6 ∘ raw11125step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11125step0 raw11125step0Labels raw11125step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4731 node4731Labels := by rfl

theorem canonical11126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11126 raw11126Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw11126 raw11126Labels = mixedMoment B raw11126step0 raw11126step0Labels := by
      have hz : ∀ j, raw11126 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11126step0 = (fun i j => raw11126 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11126step0 raw11126; decide +kernel
      have hl : raw11126step0Labels = raw11126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11126 raw11126Labels permutation434 hz
    mixedMoment B raw11126step0 raw11126step0Labels = mixedMoment B raw11126step1 raw11126step1Labels := by
      have ha : raw11126step1 = (fun i j => raw11126step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11126step1 raw11126step0; decide +kernel
      have hl : raw11126step1Labels = raw11126step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11126step0 raw11126step0Labels permutation50 permutation5
    mixedMoment B raw11126step1 raw11126step1Labels = mixedMoment B raw11126step2 raw11126step2Labels := by
      have ha : raw11126step2 = -raw11126step1 := by apply Matrix.ext; change ∀ i j, raw11126step2 i j = -(raw11126step1 i j); unfold raw11126step2 raw11126step1; decide +kernel
      have hl : raw11126step2Labels = raw11126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11126step2 raw11126step2Labels = mixedMoment B raw11126step3 raw11126step3Labels := by
      have ha : raw11126step3 = raw11126step2 := by apply Matrix.ext; unfold raw11126step3 raw11126step2; decide +kernel
      have hl : raw11126step2Labels = labelEmbedding8 ∘ raw11126step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11126step2 raw11126step2Labels raw11126step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

theorem canonical11127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11127 raw11127Labels = mixedMoment B node4253 node4253Labels := by
  calc
    mixedMoment B raw11127 raw11127Labels = mixedMoment B raw11127step0 raw11127step0Labels := by
      have hz : ∀ j, raw11127 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11127step0 = (fun i j => raw11127 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11127step0 raw11127; decide +kernel
      have hl : raw11127step0Labels = raw11127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11127 raw11127Labels permutation434 hz
    mixedMoment B raw11127step0 raw11127step0Labels = mixedMoment B raw11127step1 raw11127step1Labels := by
      have ha : raw11127step1 = (fun i j => raw11127step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11127step1 raw11127step0; decide +kernel
      have hl : raw11127step1Labels = raw11127step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11127step0 raw11127step0Labels permutation32 permutation3
    mixedMoment B raw11127step1 raw11127step1Labels = mixedMoment B raw11127step2 raw11127step2Labels := by
      have ha : raw11127step2 = raw11127step1 := by apply Matrix.ext; unfold raw11127step2 raw11127step1; decide +kernel
      have hl : raw11127step1Labels = labelEmbedding6 ∘ raw11127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11127step1 raw11127step1Labels raw11127step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4253 node4253Labels := by rfl

theorem canonical11128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11128 raw11128Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw11128 raw11128Labels = mixedMoment B raw11128step0 raw11128step0Labels := by
      have hz : ∀ j, raw11128 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11128step0 = (fun i j => raw11128 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11128step0 raw11128; decide +kernel
      have hl : raw11128step0Labels = raw11128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11128 raw11128Labels permutation434 hz
    mixedMoment B raw11128step0 raw11128step0Labels = mixedMoment B raw11128step1 raw11128step1Labels := by
      have ha : raw11128step1 = (fun i j => raw11128step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11128step1 raw11128step0; decide +kernel
      have hl : raw11128step1Labels = raw11128step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11128step0 raw11128step0Labels permutation32 permutation3
    mixedMoment B raw11128step1 raw11128step1Labels = mixedMoment B raw11128step2 raw11128step2Labels := by
      have ha : raw11128step2 = raw11128step1 := by apply Matrix.ext; unfold raw11128step2 raw11128step1; decide +kernel
      have hl : raw11128step1Labels = labelEmbedding6 ∘ raw11128step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11128step1 raw11128step1Labels raw11128step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical11129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11129 raw11129Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw11129 raw11129Labels = mixedMoment B raw11129step0 raw11129step0Labels := by
      have hz : ∀ j, raw11129 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11129step0 = (fun i j => raw11129 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11129step0 raw11129; decide +kernel
      have hl : raw11129step0Labels = raw11129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11129 raw11129Labels permutation434 hz
    mixedMoment B raw11129step0 raw11129step0Labels = mixedMoment B raw11129step1 raw11129step1Labels := by
      have ha : raw11129step1 = (fun i j => raw11129step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11129step1 raw11129step0; decide +kernel
      have hl : raw11129step1Labels = raw11129step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11129step0 raw11129step0Labels permutation38 permutation3
    mixedMoment B raw11129step1 raw11129step1Labels = mixedMoment B raw11129step2 raw11129step2Labels := by
      have ha : raw11129step2 = raw11129step1 := by apply Matrix.ext; unfold raw11129step2 raw11129step1; decide +kernel
      have hl : raw11129step1Labels = labelEmbedding6 ∘ raw11129step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11129step1 raw11129step1Labels raw11129step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical11130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11130 raw11130Labels = mixedMoment B node4729 node4729Labels := by
  calc
    mixedMoment B raw11130 raw11130Labels = mixedMoment B raw11130step0 raw11130step0Labels := by
      have ha : raw11130step0 = (fun i j => raw11130 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11130step0 raw11130; decide +kernel
      have hl : raw11130step0Labels = raw11130Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11130 raw11130Labels permutation200 permutation3
    mixedMoment B raw11130step0 raw11130step0Labels = mixedMoment B raw11130step1 raw11130step1Labels := by
      have ha : raw11130step1 = raw11130step0 := by apply Matrix.ext; unfold raw11130step1 raw11130step0; decide +kernel
      have hl : raw11130step0Labels = labelEmbedding6 ∘ raw11130step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11130step0 raw11130step0Labels raw11130step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4729 node4729Labels := by rfl

theorem canonical11131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11131 raw11131Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw11131 raw11131Labels = mixedMoment B raw11131step0 raw11131step0Labels := by
      have hz : ∀ j, raw11131 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11131step0 = (fun i j => raw11131 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11131step0 raw11131; decide +kernel
      have hl : raw11131step0Labels = raw11131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11131 raw11131Labels permutation520 hz
    mixedMoment B raw11131step0 raw11131step0Labels = mixedMoment B raw11131step1 raw11131step1Labels := by
      have hz : ∀ j, raw11131step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11131step1 = (fun i j => raw11131step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11131step1 raw11131step0; decide +kernel
      have hl : raw11131step1Labels = raw11131step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11131step0 raw11131step0Labels permutation104 hz
    mixedMoment B raw11131step1 raw11131step1Labels = mixedMoment B raw11131step2 raw11131step2Labels := by
      have ha : raw11131step2 = (fun i j => raw11131step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11131step2 raw11131step1; decide +kernel
      have hl : raw11131step2Labels = raw11131step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11131step1 raw11131step1Labels permutation8 permutation3
    mixedMoment B raw11131step2 raw11131step2Labels = mixedMoment B raw11131step3 raw11131step3Labels := by
      have ha : raw11131step3 = raw11131step2 := by apply Matrix.ext; unfold raw11131step3 raw11131step2; decide +kernel
      have hl : raw11131step2Labels = labelEmbedding6 ∘ raw11131step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11131step2 raw11131step2Labels raw11131step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5169 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5169 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5169 = injectiveMoment H raw5169step0 := by
      have hz : ∀ j, raw5169 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5169step0 = (fun i j => raw5169 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169 permutation21 hz
    injectiveMoment H raw5169step0 = injectiveMoment H raw5169step1 := by
      have hz : ∀ j, raw5169step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5169step1 = (fun i j => raw5169step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169step0 permutation5 hz
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

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

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

theorem singlePair505 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node505 node505Labels = Sparse.eval singlePairValue505 (familyPairVector B) := by
  have hp := single_label_three B hB node505
  have hl : node505Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node505 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node505 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node505 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node505 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node505 (EqualityPatterns.family3.label 1) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node505 PairSemantics.raw5204; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node505 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node505 (EqualityPatterns.family3.label 2) = PairSemantics.raw9013 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node505 PairSemantics.raw9013; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9013 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node505 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node505 (EqualityPatterns.family3.label 3) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node505 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm4 : familyPairMoment B (groupedColumns node505 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value207 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node505 (EqualityPatterns.family3.label 4) = PairSemantics.raw4117 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node505 PairSemantics.raw4117; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4117 hH).trans (PairSemantics.sound207 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue505, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value207, Sparse.eval] at hp ⊢
  linarith only [hp]

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

theorem singleton3912 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3912 node3912Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node505 node505Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw550 singletonSmall3912
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3912) = raw550Labels := by decide +kernel
  rw [hl, canonical550 B hB] at h
  have hc0 : mixedMoment B raw550 (Fin.cases (0 : Fin 1) singletonSmall3912) =
      mixedMoment B node505 node505Labels := by
    have ha : raw550 = raw551 := by apply Matrix.ext; unfold raw550 raw551; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3912 = raw551Labels := by decide +kernel
    rw [ha, hj, canonical551 B hB]
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

theorem singleton4252 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4252 node4252Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node786 node786Labels + mixedMoment B node822 node822Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw975 singletonSmall4252
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4252) = raw975Labels := by decide +kernel
  rw [hl, canonical975 B hB] at h
  have hc0 : mixedMoment B raw975 (Fin.cases (0 : Fin 2) singletonSmall4252) =
      mixedMoment B node786 node786Labels := by
    have ha : raw975 = raw976 := by apply Matrix.ext; unfold raw975 raw976; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4252 = raw976Labels := by decide +kernel
    rw [ha, hj, canonical976 B hB]
  have hc1 : mixedMoment B raw975 (Fin.cases (1 : Fin 2) singletonSmall4252) =
      mixedMoment B node822 node822Labels := by
    have ha : raw975 = raw977 := by apply Matrix.ext; unfold raw975 raw977; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4252 = raw977Labels := by decide +kernel
    rw [ha, hj, canonical977 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4253 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4253 node4253Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node787 node787Labels + mixedMoment B node847 node847Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw978 singletonSmall4253
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4253) = raw978Labels := by decide +kernel
  rw [hl, canonical978 B hB] at h
  have hc0 : mixedMoment B raw978 (Fin.cases (0 : Fin 2) singletonSmall4253) =
      mixedMoment B node787 node787Labels := by
    have ha : raw978 = raw979 := by apply Matrix.ext; unfold raw978 raw979; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4253 = raw979Labels := by decide +kernel
    rw [ha, hj, canonical979 B hB]
  have hc1 : mixedMoment B raw978 (Fin.cases (1 : Fin 2) singletonSmall4253) =
      mixedMoment B node847 node847Labels := by
    have ha : raw978 = raw980 := by apply Matrix.ext; unfold raw978 raw980; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4253 = raw980Labels := by decide +kernel
    rw [ha, hj, canonical980 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4255 node4255Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node789 node789Labels + mixedMoment B node823 node823Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw981 singletonSmall4255
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4255) = raw981Labels := by decide +kernel
  rw [hl, canonical981 B hB] at h
  have hc0 : mixedMoment B raw981 (Fin.cases (0 : Fin 2) singletonSmall4255) =
      mixedMoment B node789 node789Labels := by
    have ha : raw981 = raw982 := by apply Matrix.ext; unfold raw981 raw982; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4255 = raw982Labels := by decide +kernel
    rw [ha, hj, canonical982 B hB]
  have hc1 : mixedMoment B raw981 (Fin.cases (1 : Fin 2) singletonSmall4255) =
      mixedMoment B node823 node823Labels := by
    have ha : raw981 = raw983 := by apply Matrix.ext; unfold raw981 raw983; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4255 = raw983Labels := by decide +kernel
    rw [ha, hj, canonical983 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4268 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4268 node4268Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node811 node811Labels + mixedMoment B node824 node824Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw993 singletonSmall4268
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4268) = raw993Labels := by decide +kernel
  rw [hl, canonical993 B hB] at h
  have hc0 : mixedMoment B raw993 (Fin.cases (0 : Fin 2) singletonSmall4268) =
      mixedMoment B node811 node811Labels := by
    have ha : raw993 = raw994 := by apply Matrix.ext; unfold raw993 raw994; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4268 = raw994Labels := by decide +kernel
    rw [ha, hj, canonical994 B hB]
  have hc1 : mixedMoment B raw993 (Fin.cases (1 : Fin 2) singletonSmall4268) =
      mixedMoment B node824 node824Labels := by
    have ha : raw993 = raw995 := by apply Matrix.ext; unfold raw993 raw995; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4268 = raw995Labels := by decide +kernel
    rw [ha, hj, canonical995 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4729 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4729 node4729Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1898 node1898Labels + mixedMoment B node1940 node1940Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1644 singletonSmall4729
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4729) = raw1644Labels := by decide +kernel
  rw [hl, canonical1644 B hB] at h
  have hc0 : mixedMoment B raw1644 (Fin.cases (0 : Fin 2) singletonSmall4729) =
      mixedMoment B node1898 node1898Labels := by
    have ha : raw1644 = raw1645 := by apply Matrix.ext; unfold raw1644 raw1645; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4729 = raw1645Labels := by decide +kernel
    rw [ha, hj, canonical1645 B hB]
  have hc1 : mixedMoment B raw1644 (Fin.cases (1 : Fin 2) singletonSmall4729) =
      mixedMoment B node1940 node1940Labels := by
    have ha : raw1644 = raw1646 := by apply Matrix.ext; unfold raw1644 raw1646; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4729 = raw1646Labels := by decide +kernel
    rw [ha, hj, canonical1646 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4731 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4731 node4731Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1900 node1900Labels + mixedMoment B node1921 node1921Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1647 singletonSmall4731
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4731) = raw1647Labels := by decide +kernel
  rw [hl, canonical1647 B hB] at h
  have hc0 : mixedMoment B raw1647 (Fin.cases (0 : Fin 2) singletonSmall4731) =
      mixedMoment B node1900 node1900Labels := by
    have ha : raw1647 = raw1648 := by apply Matrix.ext; unfold raw1647 raw1648; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4731 = raw1648Labels := by decide +kernel
    rw [ha, hj, canonical1648 B hB]
  have hc1 : mixedMoment B raw1647 (Fin.cases (1 : Fin 2) singletonSmall4731) =
      mixedMoment B node1921 node1921Labels := by
    have ha : raw1647 = raw1649 := by apply Matrix.ext; unfold raw1647 raw1649; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4731 = raw1649Labels := by decide +kernel
    rw [ha, hj, canonical1649 B hB]
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

theorem singleton4740 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4740 node4740Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1913 node1913Labels + mixedMoment B node1922 node1922Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1656 singletonSmall4740
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4740) = raw1656Labels := by decide +kernel
  rw [hl, canonical1656 B hB] at h
  have hc0 : mixedMoment B raw1656 (Fin.cases (0 : Fin 2) singletonSmall4740) =
      mixedMoment B node1913 node1913Labels := by
    have ha : raw1656 = raw1657 := by apply Matrix.ext; unfold raw1656 raw1657; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4740 = raw1657Labels := by decide +kernel
    rw [ha, hj, canonical1657 B hB]
  have hc1 : mixedMoment B raw1656 (Fin.cases (1 : Fin 2) singletonSmall4740) =
      mixedMoment B node1922 node1922Labels := by
    have ha : raw1656 = raw1658 := by apply Matrix.ext; unfold raw1656 raw1658; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4740 = raw1658Labels := by decide +kernel
    rw [ha, hj, canonical1658 B hB]
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

theorem singleton4805 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4805 node4805Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2023 node2023Labels + mixedMoment B node2214 node2214Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1740 singletonSmall4805
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4805) = raw1740Labels := by decide +kernel
  rw [hl, canonical1740 B hB] at h
  have hc0 : mixedMoment B raw1740 (Fin.cases (0 : Fin 2) singletonSmall4805) =
      mixedMoment B node2023 node2023Labels := by
    have ha : raw1740 = raw1741 := by apply Matrix.ext; unfold raw1740 raw1741; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4805 = raw1741Labels := by decide +kernel
    rw [ha, hj, canonical1741 B hB]
  have hc1 : mixedMoment B raw1740 (Fin.cases (1 : Fin 2) singletonSmall4805) =
      mixedMoment B node2214 node2214Labels := by
    have ha : raw1740 = raw1742 := by apply Matrix.ext; unfold raw1740 raw1742; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4805 = raw1742Labels := by decide +kernel
    rw [ha, hj, canonical1742 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4810 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4810 node4810Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2028 node2028Labels + mixedMoment B node2215 node2215Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1746 singletonSmall4810
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4810) = raw1746Labels := by decide +kernel
  rw [hl, canonical1746 B hB] at h
  have hc0 : mixedMoment B raw1746 (Fin.cases (0 : Fin 2) singletonSmall4810) =
      mixedMoment B node2028 node2028Labels := by
    have ha : raw1746 = raw1747 := by apply Matrix.ext; unfold raw1746 raw1747; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4810 = raw1747Labels := by decide +kernel
    rw [ha, hj, canonical1747 B hB]
  have hc1 : mixedMoment B raw1746 (Fin.cases (1 : Fin 2) singletonSmall4810) =
      mixedMoment B node2215 node2215Labels := by
    have ha : raw1746 = raw1748 := by apply Matrix.ext; unfold raw1746 raw1748; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4810 = raw1748Labels := by decide +kernel
    rw [ha, hj, canonical1748 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4839 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4839 node4839Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2058 node2058Labels + mixedMoment B node2216 node2216Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1770 singletonSmall4839
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4839) = raw1770Labels := by decide +kernel
  rw [hl, canonical1770 B hB] at h
  have hc0 : mixedMoment B raw1770 (Fin.cases (0 : Fin 2) singletonSmall4839) =
      mixedMoment B node2058 node2058Labels := by
    have ha : raw1770 = raw1771 := by apply Matrix.ext; unfold raw1770 raw1771; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4839 = raw1771Labels := by decide +kernel
    rw [ha, hj, canonical1771 B hB]
  have hc1 : mixedMoment B raw1770 (Fin.cases (1 : Fin 2) singletonSmall4839) =
      mixedMoment B node2216 node2216Labels := by
    have ha : raw1770 = raw1772 := by apply Matrix.ext; unfold raw1770 raw1772; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4839 = raw1772Labels := by decide +kernel
    rw [ha, hj, canonical1772 B hB]
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

theorem singleton4864 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4864 node4864Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2105 node2105Labels + mixedMoment B node2241 node2241Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1788 singletonSmall4864
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4864) = raw1788Labels := by decide +kernel
  rw [hl, canonical1788 B hB] at h
  have hc0 : mixedMoment B raw1788 (Fin.cases (0 : Fin 2) singletonSmall4864) =
      mixedMoment B node2105 node2105Labels := by
    have ha : raw1788 = raw1789 := by apply Matrix.ext; unfold raw1788 raw1789; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4864 = raw1789Labels := by decide +kernel
    rw [ha, hj, canonical1789 B hB]
  have hc1 : mixedMoment B raw1788 (Fin.cases (1 : Fin 2) singletonSmall4864) =
      mixedMoment B node2241 node2241Labels := by
    have ha : raw1788 = raw1790 := by apply Matrix.ext; unfold raw1788 raw1790; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4864 = raw1790Labels := by decide +kernel
    rw [ha, hj, canonical1790 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4865 node4865Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2106 node2106Labels + mixedMoment B node2242 node2242Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1791 singletonSmall4865
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4865) = raw1791Labels := by decide +kernel
  rw [hl, canonical1791 B hB] at h
  have hc0 : mixedMoment B raw1791 (Fin.cases (0 : Fin 2) singletonSmall4865) =
      mixedMoment B node2106 node2106Labels := by
    have ha : raw1791 = raw1792 := by apply Matrix.ext; unfold raw1791 raw1792; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4865 = raw1792Labels := by decide +kernel
    rw [ha, hj, canonical1792 B hB]
  have hc1 : mixedMoment B raw1791 (Fin.cases (1 : Fin 2) singletonSmall4865) =
      mixedMoment B node2242 node2242Labels := by
    have ha : raw1791 = raw1793 := by apply Matrix.ext; unfold raw1791 raw1793; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4865 = raw1793Labels := by decide +kernel
    rw [ha, hj, canonical1793 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4866 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4866 node4866Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2107 node2107Labels + mixedMoment B node2260 node2260Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1794 singletonSmall4866
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4866) = raw1794Labels := by decide +kernel
  rw [hl, canonical1794 B hB] at h
  have hc0 : mixedMoment B raw1794 (Fin.cases (0 : Fin 2) singletonSmall4866) =
      mixedMoment B node2107 node2107Labels := by
    have ha : raw1794 = raw1795 := by apply Matrix.ext; unfold raw1794 raw1795; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4866 = raw1795Labels := by decide +kernel
    rw [ha, hj, canonical1795 B hB]
  have hc1 : mixedMoment B raw1794 (Fin.cases (1 : Fin 2) singletonSmall4866) =
      mixedMoment B node2260 node2260Labels := by
    have ha : raw1794 = raw1796 := by apply Matrix.ext; unfold raw1794 raw1796; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4866 = raw1796Labels := by decide +kernel
    rw [ha, hj, canonical1796 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4889 node4889Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2245 node2245Labels + mixedMoment B node2277 node2277Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1818 singletonSmall4889
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4889) = raw1818Labels := by decide +kernel
  rw [hl, canonical1818 B hB] at h
  have hc0 : mixedMoment B raw1818 (Fin.cases (0 : Fin 2) singletonSmall4889) =
      mixedMoment B node2245 node2245Labels := by
    have ha : raw1818 = raw1819 := by apply Matrix.ext; unfold raw1818 raw1819; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4889 = raw1819Labels := by decide +kernel
    rw [ha, hj, canonical1819 B hB]
  have hc1 : mixedMoment B raw1818 (Fin.cases (1 : Fin 2) singletonSmall4889) =
      mixedMoment B node2277 node2277Labels := by
    have ha : raw1818 = raw1820 := by apply Matrix.ext; unfold raw1818 raw1820; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4889 = raw1820Labels := by decide +kernel
    rw [ha, hj, canonical1820 B hB]
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

theorem singleton4896 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4896 node4896Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2266 node2266Labels + mixedMoment B node2278 node2278Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1824 singletonSmall4896
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4896) = raw1824Labels := by decide +kernel
  rw [hl, canonical1824 B hB] at h
  have hc0 : mixedMoment B raw1824 (Fin.cases (0 : Fin 2) singletonSmall4896) =
      mixedMoment B node2266 node2266Labels := by
    have ha : raw1824 = raw1825 := by apply Matrix.ext; unfold raw1824 raw1825; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4896 = raw1825Labels := by decide +kernel
    rw [ha, hj, canonical1825 B hB]
  have hc1 : mixedMoment B raw1824 (Fin.cases (1 : Fin 2) singletonSmall4896) =
      mixedMoment B node2278 node2278Labels := by
    have ha : raw1824 = raw1826 := by apply Matrix.ext; unfold raw1824 raw1826; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4896 = raw1826Labels := by decide +kernel
    rw [ha, hj, canonical1826 B hB]
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

theorem singleton5406 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5406 node5406Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3801 node3801Labels + mixedMoment B node3812 node3812Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2487 singletonSmall5406
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5406) = raw2487Labels := by decide +kernel
  rw [hl, canonical2487 B hB] at h
  have hc0 : mixedMoment B raw2487 (Fin.cases (0 : Fin 2) singletonSmall5406) =
      mixedMoment B node3801 node3801Labels := by
    have ha : raw2487 = raw2488 := by apply Matrix.ext; unfold raw2487 raw2488; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5406 = raw2488Labels := by decide +kernel
    rw [ha, hj, canonical2488 B hB]
  have hc1 : mixedMoment B raw2487 (Fin.cases (1 : Fin 2) singletonSmall5406) =
      mixedMoment B node3812 node3812Labels := by
    have ha : raw2487 = raw2489 := by apply Matrix.ext; unfold raw2487 raw2489; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5406 = raw2489Labels := by decide +kernel
    rw [ha, hj, canonical2489 B hB]
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

theorem singleton5453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5453 node5453Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3912 node3912Labels + mixedMoment B node3912 node3912Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2565 singletonSmall5453
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5453) = raw2565Labels := by decide +kernel
  rw [hl, canonical2565 B hB] at h
  have hc0 : mixedMoment B raw2565 (Fin.cases (0 : Fin 2) singletonSmall5453) =
      mixedMoment B node3912 node3912Labels := by
    have ha : raw2565 = raw2566 := by apply Matrix.ext; unfold raw2565 raw2566; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5453 = raw2566Labels := by decide +kernel
    rw [ha, hj, canonical2566 B hB]
  have hc1 : mixedMoment B raw2565 (Fin.cases (1 : Fin 2) singletonSmall5453) =
      mixedMoment B node3912 node3912Labels := by
    have ha : raw2565 = raw2567 := by apply Matrix.ext; unfold raw2565 raw2567; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5453 = raw2567Labels := by decide +kernel
    rw [ha, hj, canonical2567 B hB]
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

theorem sound505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node505 node505Labels = Sparse.eval nodeValue505 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue505 (familyPairVector B) := singlePair505 B _hB
    _ = _ := by norm_num [singlePairValue505, nodeValue505, Sparse.eval, mixedVector] <;> ring

theorem sound3912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3912 node3912Labels = Sparse.eval nodeValue3912 (mixedVector B) := by
  have h := singleton3912 B _hB
  rw [sound505 B _hB _hF] at h
  norm_num [nodeValue3912, nodeValue505, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5453 node5453Labels = Sparse.eval nodeValue5453 (mixedVector B) := by
  have h := singleton5453 B _hB
  rw [sound3912 B _hB _hF] at h
  norm_num [nodeValue5453, nodeValue3912, Sparse.eval] at h ⊢
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

theorem sound786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node786 node786Labels = Sparse.eval nodeValue786 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 786) = mixedMoment B node786 node786Labels := rfl
  simpa [nodeValue786, Sparse.eval] using hc.symm

theorem sound787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node787 node787Labels = Sparse.eval nodeValue787 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 787) = mixedMoment B node787 node787Labels := rfl
  simpa [nodeValue787, Sparse.eval] using hc.symm

theorem sound789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node789 node789Labels = Sparse.eval nodeValue789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 789) = mixedMoment B node789 node789Labels := rfl
  simpa [nodeValue789, Sparse.eval] using hc.symm

theorem sound811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node811 node811Labels = Sparse.eval nodeValue811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 811) = mixedMoment B node811 node811Labels := rfl
  simpa [nodeValue811, Sparse.eval] using hc.symm

theorem sound822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node822 node822Labels = Sparse.eval nodeValue822 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 822) = mixedMoment B node822 node822Labels := rfl
  simpa [nodeValue822, Sparse.eval] using hc.symm

theorem sound823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node823 node823Labels = Sparse.eval nodeValue823 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 823) = mixedMoment B node823 node823Labels := rfl
  simpa [nodeValue823, Sparse.eval] using hc.symm

theorem sound824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node824 node824Labels = Sparse.eval nodeValue824 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 824) = mixedMoment B node824 node824Labels := rfl
  simpa [nodeValue824, Sparse.eval] using hc.symm

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

theorem sound847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node847 node847Labels = Sparse.eval nodeValue847 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 847) = mixedMoment B node847 node847Labels := rfl
  simpa [nodeValue847, Sparse.eval] using hc.symm

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

theorem sound1898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1898 node1898Labels = Sparse.eval nodeValue1898 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1898) = mixedMoment B node1898 node1898Labels := rfl
  simpa [nodeValue1898, Sparse.eval] using hc.symm

theorem sound1900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1900 node1900Labels = Sparse.eval nodeValue1900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1900) = mixedMoment B node1900 node1900Labels := rfl
  simpa [nodeValue1900, Sparse.eval] using hc.symm

theorem sound1913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1913 node1913Labels = Sparse.eval nodeValue1913 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1913) = mixedMoment B node1913 node1913Labels := rfl
  simpa [nodeValue1913, Sparse.eval] using hc.symm

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

theorem sound1921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1921 node1921Labels = Sparse.eval nodeValue1921 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1921) = mixedMoment B node1921 node1921Labels := rfl
  simpa [nodeValue1921, Sparse.eval] using hc.symm

theorem sound1922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1922 node1922Labels = Sparse.eval nodeValue1922 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1922) = mixedMoment B node1922 node1922Labels := rfl
  simpa [nodeValue1922, Sparse.eval] using hc.symm

theorem sound1940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1940 node1940Labels = Sparse.eval nodeValue1940 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1940) = mixedMoment B node1940 node1940Labels := rfl
  simpa [nodeValue1940, Sparse.eval] using hc.symm

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

theorem sound2023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2023 node2023Labels = Sparse.eval nodeValue2023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2023) = mixedMoment B node2023 node2023Labels := rfl
  simpa [nodeValue2023, Sparse.eval] using hc.symm

theorem sound2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2025 node2025Labels = Sparse.eval nodeValue2025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2025) = mixedMoment B node2025 node2025Labels := rfl
  simpa [nodeValue2025, Sparse.eval] using hc.symm

theorem sound2028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2028 node2028Labels = Sparse.eval nodeValue2028 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2028) = mixedMoment B node2028 node2028Labels := rfl
  simpa [nodeValue2028, Sparse.eval] using hc.symm

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

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

theorem sound2105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2105 node2105Labels = Sparse.eval nodeValue2105 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2105) = mixedMoment B node2105 node2105Labels := rfl
  simpa [nodeValue2105, Sparse.eval] using hc.symm

theorem sound2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2106 node2106Labels = Sparse.eval nodeValue2106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2106) = mixedMoment B node2106 node2106Labels := rfl
  simpa [nodeValue2106, Sparse.eval] using hc.symm

theorem sound2107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2107 node2107Labels = Sparse.eval nodeValue2107 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2107) = mixedMoment B node2107 node2107Labels := rfl
  simpa [nodeValue2107, Sparse.eval] using hc.symm

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

theorem sound2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2214 node2214Labels = Sparse.eval nodeValue2214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2214) = mixedMoment B node2214 node2214Labels := rfl
  simpa [nodeValue2214, Sparse.eval] using hc.symm

theorem sound2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2215 node2215Labels = Sparse.eval nodeValue2215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2215) = mixedMoment B node2215 node2215Labels := rfl
  simpa [nodeValue2215, Sparse.eval] using hc.symm

theorem sound2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2216 node2216Labels = Sparse.eval nodeValue2216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2216) = mixedMoment B node2216 node2216Labels := rfl
  simpa [nodeValue2216, Sparse.eval] using hc.symm

theorem sound2224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2224 node2224Labels = Sparse.eval nodeValue2224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2224) = mixedMoment B node2224 node2224Labels := rfl
  simpa [nodeValue2224, Sparse.eval] using hc.symm

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

theorem sound2241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2241 node2241Labels = Sparse.eval nodeValue2241 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2241) = mixedMoment B node2241 node2241Labels := rfl
  simpa [nodeValue2241, Sparse.eval] using hc.symm

theorem sound2242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2242 node2242Labels = Sparse.eval nodeValue2242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2242) = mixedMoment B node2242 node2242Labels := rfl
  simpa [nodeValue2242, Sparse.eval] using hc.symm

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2247 node2247Labels = Sparse.eval nodeValue2247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2247) = mixedMoment B node2247 node2247Labels := rfl
  simpa [nodeValue2247, Sparse.eval] using hc.symm

theorem sound2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2260 node2260Labels = Sparse.eval nodeValue2260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2260) = mixedMoment B node2260 node2260Labels := rfl
  simpa [nodeValue2260, Sparse.eval] using hc.symm

theorem sound2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2266 node2266Labels = Sparse.eval nodeValue2266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2266) = mixedMoment B node2266 node2266Labels := rfl
  simpa [nodeValue2266, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

theorem sound2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2278 node2278Labels = Sparse.eval nodeValue2278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2278) = mixedMoment B node2278 node2278Labels := rfl
  simpa [nodeValue2278, Sparse.eval] using hc.symm

theorem sound2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2290 node2290Labels = Sparse.eval nodeValue2290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2290) = mixedMoment B node2290 node2290Labels := rfl
  simpa [nodeValue2290, Sparse.eval] using hc.symm

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

theorem sound3812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3812 node3812Labels = Sparse.eval nodeValue3812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3812) = mixedMoment B node3812 node3812Labels := rfl
  simpa [nodeValue3812, Sparse.eval] using hc.symm

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

theorem sound4252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4252 node4252Labels = Sparse.eval nodeValue4252 (mixedVector B) := by
  have h := singleton4252 B _hB
  rw [sound786 B _hB _hF, sound822 B _hB _hF] at h
  norm_num [nodeValue4252, nodeValue786, nodeValue822, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4253 node4253Labels = Sparse.eval nodeValue4253 (mixedVector B) := by
  have h := singleton4253 B _hB
  rw [sound787 B _hB _hF, sound847 B _hB _hF] at h
  norm_num [nodeValue4253, nodeValue787, nodeValue847, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4255 node4255Labels = Sparse.eval nodeValue4255 (mixedVector B) := by
  have h := singleton4255 B _hB
  rw [sound789 B _hB _hF, sound823 B _hB _hF] at h
  norm_num [nodeValue4255, nodeValue789, nodeValue823, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4268 node4268Labels = Sparse.eval nodeValue4268 (mixedVector B) := by
  have h := singleton4268 B _hB
  rw [sound811 B _hB _hF, sound824 B _hB _hF] at h
  norm_num [nodeValue4268, nodeValue811, nodeValue824, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4729 node4729Labels = Sparse.eval nodeValue4729 (mixedVector B) := by
  have h := singleton4729 B _hB
  rw [sound1898 B _hB _hF, sound1940 B _hB _hF] at h
  norm_num [nodeValue4729, nodeValue1898, nodeValue1940, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4731 node4731Labels = Sparse.eval nodeValue4731 (mixedVector B) := by
  have h := singleton4731 B _hB
  rw [sound1900 B _hB _hF, sound1921 B _hB _hF] at h
  norm_num [nodeValue4731, nodeValue1900, nodeValue1921, Sparse.eval] at h ⊢
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

theorem sound4740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4740 node4740Labels = Sparse.eval nodeValue4740 (mixedVector B) := by
  have h := singleton4740 B _hB
  rw [sound1913 B _hB _hF, sound1922 B _hB _hF] at h
  norm_num [nodeValue4740, nodeValue1913, nodeValue1922, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4805 node4805Labels = Sparse.eval nodeValue4805 (mixedVector B) := by
  have h := singleton4805 B _hB
  rw [sound2023 B _hB _hF, sound2214 B _hB _hF] at h
  norm_num [nodeValue4805, nodeValue2023, nodeValue2214, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4807 node4807Labels = Sparse.eval nodeValue4807 (mixedVector B) := by
  have h := singleton4807 B _hB
  rw [sound2025 B _hB _hF, sound2224 B _hB _hF] at h
  norm_num [nodeValue4807, nodeValue2025, nodeValue2224, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4810 node4810Labels = Sparse.eval nodeValue4810 (mixedVector B) := by
  have h := singleton4810 B _hB
  rw [sound2028 B _hB _hF, sound2215 B _hB _hF] at h
  norm_num [nodeValue4810, nodeValue2028, nodeValue2215, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4839 node4839Labels = Sparse.eval nodeValue4839 (mixedVector B) := by
  have h := singleton4839 B _hB
  rw [sound2058 B _hB _hF, sound2216 B _hB _hF] at h
  norm_num [nodeValue4839, nodeValue2058, nodeValue2216, Sparse.eval] at h ⊢
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

theorem sound4864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4864 node4864Labels = Sparse.eval nodeValue4864 (mixedVector B) := by
  have h := singleton4864 B _hB
  rw [sound2105 B _hB _hF, sound2241 B _hB _hF] at h
  norm_num [nodeValue4864, nodeValue2105, nodeValue2241, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4865 node4865Labels = Sparse.eval nodeValue4865 (mixedVector B) := by
  have h := singleton4865 B _hB
  rw [sound2106 B _hB _hF, sound2242 B _hB _hF] at h
  norm_num [nodeValue4865, nodeValue2106, nodeValue2242, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4866 node4866Labels = Sparse.eval nodeValue4866 (mixedVector B) := by
  have h := singleton4866 B _hB
  rw [sound2107 B _hB _hF, sound2260 B _hB _hF] at h
  norm_num [nodeValue4866, nodeValue2107, nodeValue2260, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4889 node4889Labels = Sparse.eval nodeValue4889 (mixedVector B) := by
  have h := singleton4889 B _hB
  rw [sound2245 B _hB _hF, sound2277 B _hB _hF] at h
  norm_num [nodeValue4889, nodeValue2245, nodeValue2277, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4890 node4890Labels = Sparse.eval nodeValue4890 (mixedVector B) := by
  have h := singleton4890 B _hB
  rw [sound2247 B _hB _hF, sound2290 B _hB _hF] at h
  norm_num [nodeValue4890, nodeValue2247, nodeValue2290, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4896 node4896Labels = Sparse.eval nodeValue4896 (mixedVector B) := by
  have h := singleton4896 B _hB
  rw [sound2266 B _hB _hF, sound2278 B _hB _hF] at h
  norm_num [nodeValue4896, nodeValue2266, nodeValue2278, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5406 node5406Labels = Sparse.eval nodeValue5406 (mixedVector B) := by
  have h := singleton5406 B _hB
  rw [sound3801 B _hB _hF, sound3812 B _hB _hF] at h
  norm_num [nodeValue5406, nodeValue3801, nodeValue3812, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources20
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq655 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm655 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA655 + difference 0 1) (sourceB655 + difference 1 0) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA655 + difference 0 1) (sourceB655 + difference 1 0) sourceC655) = raw11102 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11102; decide +kernel
    rw [ha]
    exact (canonical11102 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA655 + difference 0 2) (sourceB655 + difference 2 0) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA655 + difference 0 2) (sourceB655 + difference 2 0) sourceC655) = raw11103 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11103; decide +kernel
    rw [ha]
    exact (canonical11103 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA655 + difference 0 3) (sourceB655 + difference 3 0) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA655 + difference 0 3) (sourceB655 + difference 3 0) sourceC655) = raw11104 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11104; decide +kernel
    rw [ha]
    exact (canonical11104 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA655 + difference 0 4) (sourceB655 + difference 4 0) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA655 + difference 0 4) (sourceB655 + difference 4 0) sourceC655) = raw11105 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11105; decide +kernel
    rw [ha]
    exact (canonical11105 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA655 + difference 0 5) (sourceB655 + difference 5 0) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA655 + difference 0 5) (sourceB655 + difference 5 0) sourceC655) = raw11106 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11106; decide +kernel
    rw [ha]
    exact (canonical11106 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA655 + difference 1 0) (sourceB655 + difference 0 1) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA655 + difference 1 0) (sourceB655 + difference 0 1) sourceC655) = raw11107 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11107; decide +kernel
    rw [ha]
    exact (canonical11107 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA655 + difference 1 2) (sourceB655 + difference 2 1) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA655 + difference 1 2) (sourceB655 + difference 2 1) sourceC655) = raw11108 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11108; decide +kernel
    rw [ha]
    exact (canonical11108 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA655 + difference 1 3) (sourceB655 + difference 3 1) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA655 + difference 1 3) (sourceB655 + difference 3 1) sourceC655) = raw11109 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11109; decide +kernel
    rw [ha]
    exact (canonical11109 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA655 + difference 1 4) (sourceB655 + difference 4 1) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA655 + difference 1 4) (sourceB655 + difference 4 1) sourceC655) = raw11110 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11110; decide +kernel
    rw [ha]
    exact (canonical11110 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA655 + difference 1 5) (sourceB655 + difference 5 1) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA655 + difference 1 5) (sourceB655 + difference 5 1) sourceC655) = raw11111 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11111; decide +kernel
    rw [ha]
    exact (canonical11111 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA655 + difference 2 0) (sourceB655 + difference 0 2) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA655 + difference 2 0) (sourceB655 + difference 0 2) sourceC655) = raw11112 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11112; decide +kernel
    rw [ha]
    exact (canonical11112 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA655 + difference 2 1) (sourceB655 + difference 1 2) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA655 + difference 2 1) (sourceB655 + difference 1 2) sourceC655) = raw11113 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11113; decide +kernel
    rw [ha]
    exact (canonical11113 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA655 + difference 2 3) (sourceB655 + difference 3 2) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA655 + difference 2 3) (sourceB655 + difference 3 2) sourceC655) = raw11114 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11114; decide +kernel
    rw [ha]
    exact (canonical11114 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA655 + difference 2 4) (sourceB655 + difference 4 2) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA655 + difference 2 4) (sourceB655 + difference 4 2) sourceC655) = raw11115 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11115; decide +kernel
    rw [ha]
    exact (canonical11115 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA655 + difference 2 5) (sourceB655 + difference 5 2) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA655 + difference 2 5) (sourceB655 + difference 5 2) sourceC655) = raw11116 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11116; decide +kernel
    rw [ha]
    exact (canonical11116 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA655 + difference 3 0) (sourceB655 + difference 0 3) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4252) := by
    have ha : (tripleCharges (sourceA655 + difference 3 0) (sourceB655 + difference 0 3) sourceC655) = raw11117 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11117; decide +kernel
    rw [ha]
    exact (canonical11117 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA655 + difference 3 1) (sourceB655 + difference 1 3) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA655 + difference 3 1) (sourceB655 + difference 1 3) sourceC655) = raw11118 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11118; decide +kernel
    rw [ha]
    exact (canonical11118 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA655 + difference 3 2) (sourceB655 + difference 2 3) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA655 + difference 3 2) (sourceB655 + difference 2 3) sourceC655) = raw11119 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11119; decide +kernel
    rw [ha]
    exact (canonical11119 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA655 + difference 3 4) (sourceB655 + difference 4 3) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA655 + difference 3 4) (sourceB655 + difference 4 3) sourceC655) = raw11120 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11120; decide +kernel
    rw [ha]
    exact (canonical11120 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA655 + difference 3 5) (sourceB655 + difference 5 3) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA655 + difference 3 5) (sourceB655 + difference 5 3) sourceC655) = raw11121 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11121; decide +kernel
    rw [ha]
    exact (canonical11121 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA655 + difference 4 0) (sourceB655 + difference 0 4) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4255) := by
    have ha : (tripleCharges (sourceA655 + difference 4 0) (sourceB655 + difference 0 4) sourceC655) = raw11122 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11122; decide +kernel
    rw [ha]
    exact (canonical11122 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA655 + difference 4 1) (sourceB655 + difference 1 4) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA655 + difference 4 1) (sourceB655 + difference 1 4) sourceC655) = raw11123 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11123; decide +kernel
    rw [ha]
    exact (canonical11123 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA655 + difference 4 2) (sourceB655 + difference 2 4) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA655 + difference 4 2) (sourceB655 + difference 2 4) sourceC655) = raw11124 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11124; decide +kernel
    rw [ha]
    exact (canonical11124 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA655 + difference 4 3) (sourceB655 + difference 3 4) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4731) := by
    have ha : (tripleCharges (sourceA655 + difference 4 3) (sourceB655 + difference 3 4) sourceC655) = raw11125 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11125; decide +kernel
    rw [ha]
    exact (canonical11125 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA655 + difference 4 5) (sourceB655 + difference 5 4) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA655 + difference 4 5) (sourceB655 + difference 5 4) sourceC655) = raw11126 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11126; decide +kernel
    rw [ha]
    exact (canonical11126 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA655 + difference 5 0) (sourceB655 + difference 0 5) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4253) := by
    have ha : (tripleCharges (sourceA655 + difference 5 0) (sourceB655 + difference 0 5) sourceC655) = raw11127 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11127; decide +kernel
    rw [ha]
    exact (canonical11127 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA655 + difference 5 1) (sourceB655 + difference 1 5) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA655 + difference 5 1) (sourceB655 + difference 1 5) sourceC655) = raw11128 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11128; decide +kernel
    rw [ha]
    exact (canonical11128 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA655 + difference 5 2) (sourceB655 + difference 2 5) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA655 + difference 5 2) (sourceB655 + difference 2 5) sourceC655) = raw11129 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11129; decide +kernel
    rw [ha]
    exact (canonical11129 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA655 + difference 5 3) (sourceB655 + difference 3 5) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4729) := by
    have ha : (tripleCharges (sourceA655 + difference 5 3) (sourceB655 + difference 3 5) sourceC655) = raw11130 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11130; decide +kernel
    rw [ha]
    exact (canonical11130 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA655 + difference 5 4) (sourceB655 + difference 4 5) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA655 + difference 5 4) (sourceB655 + difference 4 5) sourceC655) = raw11131 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11131; decide +kernel
    rw [ha]
    exact (canonical11131 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA655 sourceB655 sourceC655
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm655, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck564 : Integer.Sparse.reindex keyMap MixedData.row564 = numericRow564 := by decide +kernel

theorem numericCheck564 (x : Master → ℝ) : Integer.Sparse.eval numericRow564 x =
    (8640 : ℝ) * reducedSource564 x := by
  norm_num [numericRow564, reducedSource564, Integer.Sparse.eval, Sparse.eval, nodeValue4252, nodeValue4253, nodeValue4255, nodeValue4268, nodeValue4729, nodeValue4731, nodeValue4740, nodeValue4805, nodeValue4807, nodeValue4810, nodeValue4839, nodeValue4864, nodeValue4865, nodeValue4866, nodeValue4889, nodeValue4890, nodeValue4896, nodeValue5406, nodeValue5435, nodeValue5450, nodeValue5453]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero564 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource564 (mixedVector B) = 0 := by
  have h4252 : mixedVector B (Sum.inr 4252) = Sparse.eval nodeValue4252 (mixedVector B) := by
    change mixedMoment B node4252 node4252Labels = _
    exact sound4252 B hB hF
  have h4253 : mixedVector B (Sum.inr 4253) = Sparse.eval nodeValue4253 (mixedVector B) := by
    change mixedMoment B node4253 node4253Labels = _
    exact sound4253 B hB hF
  have h4255 : mixedVector B (Sum.inr 4255) = Sparse.eval nodeValue4255 (mixedVector B) := by
    change mixedMoment B node4255 node4255Labels = _
    exact sound4255 B hB hF
  have h4268 : mixedVector B (Sum.inr 4268) = Sparse.eval nodeValue4268 (mixedVector B) := by
    change mixedMoment B node4268 node4268Labels = _
    exact sound4268 B hB hF
  have h4729 : mixedVector B (Sum.inr 4729) = Sparse.eval nodeValue4729 (mixedVector B) := by
    change mixedMoment B node4729 node4729Labels = _
    exact sound4729 B hB hF
  have h4731 : mixedVector B (Sum.inr 4731) = Sparse.eval nodeValue4731 (mixedVector B) := by
    change mixedMoment B node4731 node4731Labels = _
    exact sound4731 B hB hF
  have h4740 : mixedVector B (Sum.inr 4740) = Sparse.eval nodeValue4740 (mixedVector B) := by
    change mixedMoment B node4740 node4740Labels = _
    exact sound4740 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4864 : mixedVector B (Sum.inr 4864) = Sparse.eval nodeValue4864 (mixedVector B) := by
    change mixedMoment B node4864 node4864Labels = _
    exact sound4864 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435_e B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450_e B hB hF
  have h5453 : mixedVector B (Sum.inr 5453) = Sparse.eval nodeValue5453 (mixedVector B) := by
    change mixedMoment B node5453 node5453Labels = _
    exact sound5453 B hB hF
  simpa only [sourceForm655, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4252, h4253, h4255, h4268, h4729, h4731, h4740, h4805, h4807, h4810, h4839, h4864, h4865, h4866, h4889, h4890, h4896, h5406, h5435, h5450, h5453, reducedSource564] using sourceEq655 B hB

theorem rowSound564_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row564 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck564, numericCheck564, reducedZero564 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e_oai
