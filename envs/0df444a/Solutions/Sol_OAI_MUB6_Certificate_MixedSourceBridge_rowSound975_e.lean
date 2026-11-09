-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound975_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:10:46.948524+00:00
-- url     : https://prove2.me/submissions/75e4d74f-c653-41a7-b6d7-e8e7dc2a5b6d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E129
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3984_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3998_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical148
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18953 raw18953Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw18953 raw18953Labels = mixedMoment B raw18953step0 raw18953step0Labels := by
      have hz : ∀ j, raw18953 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18953step0 = (fun i j => raw18953 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18953step0 raw18953; decide +kernel
      have hl : raw18953step0Labels = raw18953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18953 raw18953Labels permutation346 hz
    mixedMoment B raw18953step0 raw18953step0Labels = mixedMoment B raw18953step1 raw18953step1Labels := by
      have ha : raw18953step1 = (fun i j => raw18953step0 (permutation96 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18953step1 raw18953step0; decide +kernel
      have hl : raw18953step1Labels = raw18953step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18953step0 raw18953step0Labels permutation96 permutation7
    mixedMoment B raw18953step1 raw18953step1Labels = mixedMoment B raw18953step2 raw18953step2Labels := by
      have ha : raw18953step2 = raw18953step1 := by apply Matrix.ext; unfold raw18953step2 raw18953step1; decide +kernel
      have hl : raw18953step1Labels = labelEmbedding1 ∘ raw18953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18953step1 raw18953step1Labels raw18953step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

theorem canonical18954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18954 raw18954Labels = mixedMoment B node3979 node3979Labels := by
  calc
    mixedMoment B raw18954 raw18954Labels = mixedMoment B raw18954step0 raw18954step0Labels := by
      have ha : raw18954step0 = (fun i j => raw18954 (permutation497 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18954step0 raw18954; decide +kernel
      have hl : raw18954step0Labels = raw18954Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18954 raw18954Labels permutation497 permutation7
    mixedMoment B raw18954step0 raw18954step0Labels = mixedMoment B raw18954step1 raw18954step1Labels := by
      have ha : raw18954step1 = raw18954step0 := by apply Matrix.ext; unfold raw18954step1 raw18954step0; decide +kernel
      have hl : raw18954step0Labels = labelEmbedding1 ∘ raw18954step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18954step0 raw18954step0Labels raw18954step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3979 node3979Labels := by rfl

theorem canonical18955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18955 raw18955Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw18955 raw18955Labels = mixedMoment B raw18955step0 raw18955step0Labels := by
      have hz : ∀ j, raw18955 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18955step0 = (fun i j => raw18955 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18955step0 raw18955; decide +kernel
      have hl : raw18955step0Labels = raw18955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18955 raw18955Labels permutation346 hz
    mixedMoment B raw18955step0 raw18955step0Labels = mixedMoment B raw18955step1 raw18955step1Labels := by
      have ha : raw18955step1 = (fun i j => raw18955step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18955step1 raw18955step0; decide +kernel
      have hl : raw18955step1Labels = raw18955step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18955step0 raw18955step0Labels permutation146 permutation5
    mixedMoment B raw18955step1 raw18955step1Labels = mixedMoment B raw18955step2 raw18955step2Labels := by
      have ha : raw18955step2 = raw18955step1 := by apply Matrix.ext; unfold raw18955step2 raw18955step1; decide +kernel
      have hl : raw18955step1Labels = labelEmbedding1 ∘ raw18955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18955step1 raw18955step1Labels raw18955step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4012 node4012Labels := by rfl

theorem canonical18956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18956 raw18956Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw18956 raw18956Labels = mixedMoment B raw18956step0 raw18956step0Labels := by
      have hz : ∀ j, raw18956 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18956step0 = (fun i j => raw18956 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18956step0 raw18956; decide +kernel
      have hl : raw18956step0Labels = raw18956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18956 raw18956Labels permutation346 hz
    mixedMoment B raw18956step0 raw18956step0Labels = mixedMoment B raw18956step1 raw18956step1Labels := by
      have ha : raw18956step1 = (fun i j => raw18956step0 (permutation96 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18956step1 raw18956step0; decide +kernel
      have hl : raw18956step1Labels = raw18956step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18956step0 raw18956step0Labels permutation96 permutation7
    mixedMoment B raw18956step1 raw18956step1Labels = mixedMoment B raw18956step2 raw18956step2Labels := by
      have ha : raw18956step2 = raw18956step1 := by apply Matrix.ext; unfold raw18956step2 raw18956step1; decide +kernel
      have hl : raw18956step1Labels = labelEmbedding1 ∘ raw18956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18956step1 raw18956step1Labels raw18956step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3998 node3998Labels := by rfl

theorem canonical18957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18957 raw18957Labels = mixedMoment B node3985 node3985Labels := by
  calc
    mixedMoment B raw18957 raw18957Labels = mixedMoment B raw18957step0 raw18957step0Labels := by
      have hz : ∀ j, raw18957 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18957step0 = (fun i j => raw18957 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18957step0 raw18957; decide +kernel
      have hl : raw18957step0Labels = raw18957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18957 raw18957Labels permutation346 hz
    mixedMoment B raw18957step0 raw18957step0Labels = mixedMoment B raw18957step1 raw18957step1Labels := by
      have ha : raw18957step1 = (fun i j => raw18957step0 (permutation96 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18957step1 raw18957step0; decide +kernel
      have hl : raw18957step1Labels = raw18957step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18957step0 raw18957step0Labels permutation96 permutation7
    mixedMoment B raw18957step1 raw18957step1Labels = mixedMoment B raw18957step2 raw18957step2Labels := by
      have ha : raw18957step2 = raw18957step1 := by apply Matrix.ext; unfold raw18957step2 raw18957step1; decide +kernel
      have hl : raw18957step1Labels = labelEmbedding1 ∘ raw18957step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18957step1 raw18957step1Labels raw18957step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3985 node3985Labels := by rfl

theorem canonical18958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18958 raw18958Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw18958 raw18958Labels = mixedMoment B raw18958step0 raw18958step0Labels := by
      have hz : ∀ j, raw18958 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18958step0 = (fun i j => raw18958 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18958step0 raw18958; decide +kernel
      have hl : raw18958step0Labels = raw18958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18958 raw18958Labels permutation346 hz
    mixedMoment B raw18958step0 raw18958step0Labels = mixedMoment B raw18958step1 raw18958step1Labels := by
      have ha : raw18958step1 = (fun i j => raw18958step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18958step1 raw18958step0; decide +kernel
      have hl : raw18958step1Labels = raw18958step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18958step0 raw18958step0Labels permutation40 permutation5
    mixedMoment B raw18958step1 raw18958step1Labels = mixedMoment B raw18958step2 raw18958step2Labels := by
      have ha : raw18958step2 = -raw18958step1 := by apply Matrix.ext; change ∀ i j, raw18958step2 i j = -(raw18958step1 i j); unfold raw18958step2 raw18958step1; decide +kernel
      have hl : raw18958step2Labels = raw18958step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18958step2 raw18958step2Labels = mixedMoment B raw18958step3 raw18958step3Labels := by
      have ha : raw18958step3 = raw18958step2 := by apply Matrix.ext; unfold raw18958step3 raw18958step2; decide +kernel
      have hl : raw18958step2Labels = labelEmbedding1 ∘ raw18958step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18958step2 raw18958step2Labels raw18958step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical18959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18959 raw18959Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw18959 raw18959Labels = mixedMoment B raw18959step0 raw18959step0Labels := by
      have ha : raw18959step0 = (fun i j => raw18959 (permutation498 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18959step0 raw18959; decide +kernel
      have hl : raw18959step0Labels = raw18959Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18959 raw18959Labels permutation498 permutation7
    mixedMoment B raw18959step0 raw18959step0Labels = mixedMoment B raw18959step1 raw18959step1Labels := by
      have ha : raw18959step1 = raw18959step0 := by apply Matrix.ext; unfold raw18959step1 raw18959step0; decide +kernel
      have hl : raw18959step0Labels = labelEmbedding1 ∘ raw18959step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18959step0 raw18959step0Labels raw18959step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

theorem canonical18960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18960 raw18960Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw18960 raw18960Labels = mixedMoment B raw18960step0 raw18960step0Labels := by
      have hz : ∀ j, raw18960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18960step0 = (fun i j => raw18960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18960step0 raw18960; decide +kernel
      have hl : raw18960step0Labels = raw18960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18960 raw18960Labels permutation346 hz
    mixedMoment B raw18960step0 raw18960step0Labels = mixedMoment B raw18960step1 raw18960step1Labels := by
      have ha : raw18960step1 = (fun i j => raw18960step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18960step1 raw18960step0; decide +kernel
      have hl : raw18960step1Labels = raw18960step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18960step0 raw18960step0Labels permutation138 permutation5
    mixedMoment B raw18960step1 raw18960step1Labels = mixedMoment B raw18960step2 raw18960step2Labels := by
      have ha : raw18960step2 = raw18960step1 := by apply Matrix.ext; unfold raw18960step2 raw18960step1; decide +kernel
      have hl : raw18960step1Labels = labelEmbedding1 ∘ raw18960step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18960step1 raw18960step1Labels raw18960step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

theorem canonical18961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18961 raw18961Labels = mixedMoment B node3997 node3997Labels := by
  calc
    mixedMoment B raw18961 raw18961Labels = mixedMoment B raw18961step0 raw18961step0Labels := by
      have hz : ∀ j, raw18961 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18961step0 = (fun i j => raw18961 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18961step0 raw18961; decide +kernel
      have hl : raw18961step0Labels = raw18961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18961 raw18961Labels permutation346 hz
    mixedMoment B raw18961step0 raw18961step0Labels = mixedMoment B raw18961step1 raw18961step1Labels := by
      have ha : raw18961step1 = (fun i j => raw18961step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18961step1 raw18961step0; decide +kernel
      have hl : raw18961step1Labels = raw18961step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18961step0 raw18961step0Labels permutation137 permutation5
    mixedMoment B raw18961step1 raw18961step1Labels = mixedMoment B raw18961step2 raw18961step2Labels := by
      have ha : raw18961step2 = raw18961step1 := by apply Matrix.ext; unfold raw18961step2 raw18961step1; decide +kernel
      have hl : raw18961step1Labels = labelEmbedding1 ∘ raw18961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18961step1 raw18961step1Labels raw18961step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3997 node3997Labels := by rfl

theorem canonical18962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18962 raw18962Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw18962 raw18962Labels = mixedMoment B raw18962step0 raw18962step0Labels := by
      have hz : ∀ j, raw18962 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18962step0 = (fun i j => raw18962 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18962step0 raw18962; decide +kernel
      have hl : raw18962step0Labels = raw18962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18962 raw18962Labels permutation346 hz
    mixedMoment B raw18962step0 raw18962step0Labels = mixedMoment B raw18962step1 raw18962step1Labels := by
      have ha : raw18962step1 = (fun i j => raw18962step0 (permutation95 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18962step1 raw18962step0; decide +kernel
      have hl : raw18962step1Labels = raw18962step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18962step0 raw18962step0Labels permutation95 permutation7
    mixedMoment B raw18962step1 raw18962step1Labels = mixedMoment B raw18962step2 raw18962step2Labels := by
      have ha : raw18962step2 = raw18962step1 := by apply Matrix.ext; unfold raw18962step2 raw18962step1; decide +kernel
      have hl : raw18962step1Labels = labelEmbedding1 ∘ raw18962step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18962step1 raw18962step1Labels raw18962step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3984 node3984Labels := by rfl

theorem canonical18963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18963 raw18963Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw18963 raw18963Labels = mixedMoment B raw18963step0 raw18963step0Labels := by
      have ha : raw18963step0 = (fun i j => raw18963 (permutation202 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18963step0 raw18963; decide +kernel
      have hl : raw18963step0Labels = raw18963Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18963 raw18963Labels permutation202 permutation5
    mixedMoment B raw18963step0 raw18963step0Labels = mixedMoment B raw18963step1 raw18963step1Labels := by
      have ha : raw18963step1 = -raw18963step0 := by apply Matrix.ext; change ∀ i j, raw18963step1 i j = -(raw18963step0 i j); unfold raw18963step1 raw18963step0; decide +kernel
      have hl : raw18963step1Labels = raw18963step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18963step1 raw18963step1Labels = mixedMoment B raw18963step2 raw18963step2Labels := by
      have ha : raw18963step2 = raw18963step1 := by apply Matrix.ext; unfold raw18963step2 raw18963step1; decide +kernel
      have hl : raw18963step1Labels = labelEmbedding1 ∘ raw18963step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18963step1 raw18963step1Labels raw18963step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

theorem canonical18964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18964 raw18964Labels = mixedMoment B node3973 node3973Labels := by
  calc
    mixedMoment B raw18964 raw18964Labels = mixedMoment B raw18964step0 raw18964step0Labels := by
      have ha : raw18964step0 = (fun i j => raw18964 (permutation645 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18964step0 raw18964; decide +kernel
      have hl : raw18964step0Labels = raw18964Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18964 raw18964Labels permutation645 permutation5
    mixedMoment B raw18964step0 raw18964step0Labels = mixedMoment B raw18964step1 raw18964step1Labels := by
      have ha : raw18964step1 = raw18964step0 := by apply Matrix.ext; unfold raw18964step1 raw18964step0; decide +kernel
      have hl : raw18964step0Labels = labelEmbedding1 ∘ raw18964step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18964step0 raw18964step0Labels raw18964step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3973 node3973Labels := by rfl

theorem canonical18965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18965 raw18965Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw18965 raw18965Labels = mixedMoment B raw18965step0 raw18965step0Labels := by
      have ha : raw18965step0 = (fun i j => raw18965 (permutation643 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18965step0 raw18965; decide +kernel
      have hl : raw18965step0Labels = raw18965Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18965 raw18965Labels permutation643 permutation5
    mixedMoment B raw18965step0 raw18965step0Labels = mixedMoment B raw18965step1 raw18965step1Labels := by
      have ha : raw18965step1 = raw18965step0 := by apply Matrix.ext; unfold raw18965step1 raw18965step0; decide +kernel
      have hl : raw18965step0Labels = labelEmbedding1 ∘ raw18965step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18965step0 raw18965step0Labels raw18965step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3972 node3972Labels := by rfl

theorem canonical18966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18966 raw18966Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw18966 raw18966Labels = mixedMoment B raw18966step0 raw18966step0Labels := by
      have ha : raw18966step0 = (fun i j => raw18966 (permutation632 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18966step0 raw18966; decide +kernel
      have hl : raw18966step0Labels = raw18966Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18966 raw18966Labels permutation632 permutation5
    mixedMoment B raw18966step0 raw18966step0Labels = mixedMoment B raw18966step1 raw18966step1Labels := by
      have ha : raw18966step1 = raw18966step0 := by apply Matrix.ext; unfold raw18966step1 raw18966step0; decide +kernel
      have hl : raw18966step0Labels = labelEmbedding1 ∘ raw18966step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18966step0 raw18966step0Labels raw18966step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

theorem canonical18967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18967 raw18967Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw18967 raw18967Labels = mixedMoment B raw18967step0 raw18967step0Labels := by
      have ha : raw18967step0 = (fun i j => raw18967 (permutation498 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18967step0 raw18967; decide +kernel
      have hl : raw18967step0Labels = raw18967Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18967 raw18967Labels permutation498 permutation7
    mixedMoment B raw18967step0 raw18967step0Labels = mixedMoment B raw18967step1 raw18967step1Labels := by
      have ha : raw18967step1 = raw18967step0 := by apply Matrix.ext; unfold raw18967step1 raw18967step0; decide +kernel
      have hl : raw18967step0Labels = labelEmbedding1 ∘ raw18967step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18967step0 raw18967step0Labels raw18967step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical18968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18968 raw18968Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw18968 raw18968Labels = mixedMoment B raw18968step0 raw18968step0Labels := by
      have hz : ∀ j, raw18968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18968step0 = (fun i j => raw18968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18968step0 raw18968; decide +kernel
      have hl : raw18968step0Labels = raw18968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18968 raw18968Labels permutation346 hz
    mixedMoment B raw18968step0 raw18968step0Labels = mixedMoment B raw18968step1 raw18968step1Labels := by
      have ha : raw18968step1 = (fun i j => raw18968step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18968step1 raw18968step0; decide +kernel
      have hl : raw18968step1Labels = raw18968step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18968step0 raw18968step0Labels permutation34 permutation5
    mixedMoment B raw18968step1 raw18968step1Labels = mixedMoment B raw18968step2 raw18968step2Labels := by
      have ha : raw18968step2 = -raw18968step1 := by apply Matrix.ext; change ∀ i j, raw18968step2 i j = -(raw18968step1 i j); unfold raw18968step2 raw18968step1; decide +kernel
      have hl : raw18968step2Labels = raw18968step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18968step2 raw18968step2Labels = mixedMoment B raw18968step3 raw18968step3Labels := by
      have ha : raw18968step3 = raw18968step2 := by apply Matrix.ext; unfold raw18968step3 raw18968step2; decide +kernel
      have hl : raw18968step2Labels = labelEmbedding1 ∘ raw18968step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18968step2 raw18968step2Labels raw18968step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

theorem canonical18969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18969 raw18969Labels = mixedMoment B node3815 node3815Labels := by
  calc
    mixedMoment B raw18969 raw18969Labels = mixedMoment B raw18969step0 raw18969step0Labels := by
      have hz : ∀ j, raw18969 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18969step0 = (fun i j => raw18969 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18969step0 raw18969; decide +kernel
      have hl : raw18969step0Labels = raw18969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18969 raw18969Labels permutation346 hz
    mixedMoment B raw18969step0 raw18969step0Labels = mixedMoment B raw18969step1 raw18969step1Labels := by
      have ha : raw18969step1 = (fun i j => raw18969step0 (permutation96 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18969step1 raw18969step0; decide +kernel
      have hl : raw18969step1Labels = raw18969step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18969step0 raw18969step0Labels permutation96 permutation7
    mixedMoment B raw18969step1 raw18969step1Labels = mixedMoment B raw18969step2 raw18969step2Labels := by
      have ha : raw18969step2 = raw18969step1 := by apply Matrix.ext; unfold raw18969step2 raw18969step1; decide +kernel
      have hl : raw18969step1Labels = labelEmbedding1 ∘ raw18969step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18969step1 raw18969step1Labels raw18969step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3815 node3815Labels := by rfl

theorem canonical18970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18970 raw18970Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw18970 raw18970Labels = mixedMoment B raw18970step0 raw18970step0Labels := by
      have ha : raw18970step0 = (fun i j => raw18970 (permutation498 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18970step0 raw18970; decide +kernel
      have hl : raw18970step0Labels = raw18970Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18970 raw18970Labels permutation498 permutation7
    mixedMoment B raw18970step0 raw18970step0Labels = mixedMoment B raw18970step1 raw18970step1Labels := by
      have ha : raw18970step1 = raw18970step0 := by apply Matrix.ext; unfold raw18970step1 raw18970step0; decide +kernel
      have hl : raw18970step0Labels = labelEmbedding1 ∘ raw18970step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18970step0 raw18970step0Labels raw18970step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

theorem canonical18971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18971 raw18971Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw18971 raw18971Labels = mixedMoment B raw18971step0 raw18971step0Labels := by
      have hz : ∀ j, raw18971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18971step0 = (fun i j => raw18971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18971step0 raw18971; decide +kernel
      have hl : raw18971step0Labels = raw18971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18971 raw18971Labels permutation346 hz
    mixedMoment B raw18971step0 raw18971step0Labels = mixedMoment B raw18971step1 raw18971step1Labels := by
      have ha : raw18971step1 = (fun i j => raw18971step0 (permutation97 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18971step1 raw18971step0; decide +kernel
      have hl : raw18971step1Labels = raw18971step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18971step0 raw18971step0Labels permutation97 permutation7
    mixedMoment B raw18971step1 raw18971step1Labels = mixedMoment B raw18971step2 raw18971step2Labels := by
      have ha : raw18971step2 = raw18971step1 := by apply Matrix.ext; unfold raw18971step2 raw18971step1; decide +kernel
      have hl : raw18971step1Labels = labelEmbedding1 ∘ raw18971step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18971step1 raw18971step1Labels raw18971step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical18972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18972 raw18972Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw18972 raw18972Labels = mixedMoment B raw18972step0 raw18972step0Labels := by
      have hz : ∀ j, raw18972 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18972step0 = (fun i j => raw18972 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18972step0 raw18972; decide +kernel
      have hl : raw18972step0Labels = raw18972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18972 raw18972Labels permutation346 hz
    mixedMoment B raw18972step0 raw18972step0Labels = mixedMoment B raw18972step1 raw18972step1Labels := by
      have ha : raw18972step1 = (fun i j => raw18972step0 (permutation97 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18972step1 raw18972step0; decide +kernel
      have hl : raw18972step1Labels = raw18972step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18972step0 raw18972step0Labels permutation97 permutation7
    mixedMoment B raw18972step1 raw18972step1Labels = mixedMoment B raw18972step2 raw18972step2Labels := by
      have ha : raw18972step2 = raw18972step1 := by apply Matrix.ext; unfold raw18972step2 raw18972step1; decide +kernel
      have hl : raw18972step1Labels = labelEmbedding1 ∘ raw18972step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18972step1 raw18972step1Labels raw18972step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical18973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18973 raw18973Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw18973 raw18973Labels = mixedMoment B raw18973step0 raw18973step0Labels := by
      have hz : ∀ j, raw18973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18973step0 = (fun i j => raw18973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18973step0 raw18973; decide +kernel
      have hl : raw18973step0Labels = raw18973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18973 raw18973Labels permutation346 hz
    mixedMoment B raw18973step0 raw18973step0Labels = mixedMoment B raw18973step1 raw18973step1Labels := by
      have ha : raw18973step1 = (fun i j => raw18973step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18973step1 raw18973step0; decide +kernel
      have hl : raw18973step1Labels = raw18973step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18973step0 raw18973step0Labels permutation38 permutation5
    mixedMoment B raw18973step1 raw18973step1Labels = mixedMoment B raw18973step2 raw18973step2Labels := by
      have ha : raw18973step2 = -raw18973step1 := by apply Matrix.ext; change ∀ i j, raw18973step2 i j = -(raw18973step1 i j); unfold raw18973step2 raw18973step1; decide +kernel
      have hl : raw18973step2Labels = raw18973step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18973step2 raw18973step2Labels = mixedMoment B raw18973step3 raw18973step3Labels := by
      have ha : raw18973step3 = raw18973step2 := by apply Matrix.ext; unfold raw18973step3 raw18973step2; decide +kernel
      have hl : raw18973step2Labels = labelEmbedding1 ∘ raw18973step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18973step2 raw18973step2Labels raw18973step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

theorem canonical18974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18974 raw18974Labels = mixedMoment B node3960 node3960Labels := by
  calc
    mixedMoment B raw18974 raw18974Labels = mixedMoment B raw18974step0 raw18974step0Labels := by
      have hz : ∀ j, raw18974 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18974step0 = (fun i j => raw18974 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18974step0 raw18974; decide +kernel
      have hl : raw18974step0Labels = raw18974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18974 raw18974Labels permutation346 hz
    mixedMoment B raw18974step0 raw18974step0Labels = mixedMoment B raw18974step1 raw18974step1Labels := by
      have ha : raw18974step1 = (fun i j => raw18974step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18974step1 raw18974step0; decide +kernel
      have hl : raw18974step1Labels = raw18974step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18974step0 raw18974step0Labels permutation150 permutation5
    mixedMoment B raw18974step1 raw18974step1Labels = mixedMoment B raw18974step2 raw18974step2Labels := by
      have ha : raw18974step2 = raw18974step1 := by apply Matrix.ext; unfold raw18974step2 raw18974step1; decide +kernel
      have hl : raw18974step1Labels = labelEmbedding1 ∘ raw18974step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18974step1 raw18974step1Labels raw18974step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3960 node3960Labels := by rfl

theorem canonical18975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18975 raw18975Labels = mixedMoment B node3955 node3955Labels := by
  calc
    mixedMoment B raw18975 raw18975Labels = mixedMoment B raw18975step0 raw18975step0Labels := by
      have ha : raw18975step0 = (fun i j => raw18975 (permutation676 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18975step0 raw18975; decide +kernel
      have hl : raw18975step0Labels = raw18975Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18975 raw18975Labels permutation676 permutation5
    mixedMoment B raw18975step0 raw18975step0Labels = mixedMoment B raw18975step1 raw18975step1Labels := by
      have ha : raw18975step1 = raw18975step0 := by apply Matrix.ext; unfold raw18975step1 raw18975step0; decide +kernel
      have hl : raw18975step0Labels = labelEmbedding1 ∘ raw18975step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18975step0 raw18975step0Labels raw18975step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3955 node3955Labels := by rfl

theorem canonical18976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18976 raw18976Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw18976 raw18976Labels = mixedMoment B raw18976step0 raw18976step0Labels := by
      have hz : ∀ j, raw18976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18976step0 = (fun i j => raw18976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18976step0 raw18976; decide +kernel
      have hl : raw18976step0Labels = raw18976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18976 raw18976Labels permutation346 hz
    mixedMoment B raw18976step0 raw18976step0Labels = mixedMoment B raw18976step1 raw18976step1Labels := by
      have ha : raw18976step1 = (fun i j => raw18976step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18976step1 raw18976step0; decide +kernel
      have hl : raw18976step1Labels = raw18976step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18976step0 raw18976step0Labels permutation148 permutation5
    mixedMoment B raw18976step1 raw18976step1Labels = mixedMoment B raw18976step2 raw18976step2Labels := by
      have ha : raw18976step2 = raw18976step1 := by apply Matrix.ext; unfold raw18976step2 raw18976step1; decide +kernel
      have hl : raw18976step1Labels = labelEmbedding1 ∘ raw18976step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18976step1 raw18976step1Labels raw18976step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

theorem canonical18977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18977 raw18977Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw18977 raw18977Labels = mixedMoment B raw18977step0 raw18977step0Labels := by
      have hz : ∀ j, raw18977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18977step0 = (fun i j => raw18977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18977step0 raw18977; decide +kernel
      have hl : raw18977step0Labels = raw18977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18977 raw18977Labels permutation346 hz
    mixedMoment B raw18977step0 raw18977step0Labels = mixedMoment B raw18977step1 raw18977step1Labels := by
      have ha : raw18977step1 = (fun i j => raw18977step0 (permutation97 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18977step1 raw18977step0; decide +kernel
      have hl : raw18977step1Labels = raw18977step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18977step0 raw18977step0Labels permutation97 permutation7
    mixedMoment B raw18977step1 raw18977step1Labels = mixedMoment B raw18977step2 raw18977step2Labels := by
      have ha : raw18977step2 = raw18977step1 := by apply Matrix.ext; unfold raw18977step2 raw18977step1; decide +kernel
      have hl : raw18977step1Labels = labelEmbedding1 ∘ raw18977step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18977step1 raw18977step1Labels raw18977step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

theorem canonical18978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18978 raw18978Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw18978 raw18978Labels = mixedMoment B raw18978step0 raw18978step0Labels := by
      have hz : ∀ j, raw18978 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18978step0 = (fun i j => raw18978 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18978step0 raw18978; decide +kernel
      have hl : raw18978step0Labels = raw18978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18978 raw18978Labels permutation346 hz
    mixedMoment B raw18978step0 raw18978step0Labels = mixedMoment B raw18978step1 raw18978step1Labels := by
      have ha : raw18978step1 = (fun i j => raw18978step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18978step1 raw18978step0; decide +kernel
      have hl : raw18978step1Labels = raw18978step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18978step0 raw18978step0Labels permutation149 permutation5
    mixedMoment B raw18978step1 raw18978step1Labels = mixedMoment B raw18978step2 raw18978step2Labels := by
      have ha : raw18978step2 = raw18978step1 := by apply Matrix.ext; unfold raw18978step2 raw18978step1; decide +kernel
      have hl : raw18978step1Labels = labelEmbedding1 ∘ raw18978step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18978step1 raw18978step1Labels raw18978step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

theorem canonical18979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18979 raw18979Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw18979 raw18979Labels = mixedMoment B raw18979step0 raw18979step0Labels := by
      have hz : ∀ j, raw18979 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18979step0 = (fun i j => raw18979 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18979step0 raw18979; decide +kernel
      have hl : raw18979step0Labels = raw18979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18979 raw18979Labels permutation346 hz
    mixedMoment B raw18979step0 raw18979step0Labels = mixedMoment B raw18979step1 raw18979step1Labels := by
      have ha : raw18979step1 = (fun i j => raw18979step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18979step1 raw18979step0; decide +kernel
      have hl : raw18979step1Labels = raw18979step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18979step0 raw18979step0Labels permutation150 permutation5
    mixedMoment B raw18979step1 raw18979step1Labels = mixedMoment B raw18979step2 raw18979step2Labels := by
      have ha : raw18979step2 = raw18979step1 := by apply Matrix.ext; unfold raw18979step2 raw18979step1; decide +kernel
      have hl : raw18979step1Labels = labelEmbedding1 ∘ raw18979step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18979step1 raw18979step1Labels raw18979step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2736 node2736Labels := by rfl

theorem canonical18980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18980 raw18980Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw18980 raw18980Labels = mixedMoment B raw18980step0 raw18980step0Labels := by
      have ha : raw18980step0 = (fun i j => raw18980 (permutation676 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18980step0 raw18980; decide +kernel
      have hl : raw18980step0Labels = raw18980Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18980 raw18980Labels permutation676 permutation5
    mixedMoment B raw18980step0 raw18980step0Labels = mixedMoment B raw18980step1 raw18980step1Labels := by
      have ha : raw18980step1 = raw18980step0 := by apply Matrix.ext; unfold raw18980step1 raw18980step0; decide +kernel
      have hl : raw18980step0Labels = labelEmbedding1 ∘ raw18980step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18980step0 raw18980step0Labels raw18980step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2718 node2718Labels := by rfl

theorem canonical18981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18981 raw18981Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw18981 raw18981Labels = mixedMoment B raw18981step0 raw18981step0Labels := by
      have hz : ∀ j, raw18981 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18981step0 = (fun i j => raw18981 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18981step0 raw18981; decide +kernel
      have hl : raw18981step0Labels = raw18981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18981 raw18981Labels permutation346 hz
    mixedMoment B raw18981step0 raw18981step0Labels = mixedMoment B raw18981step1 raw18981step1Labels := by
      have ha : raw18981step1 = (fun i j => raw18981step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18981step1 raw18981step0; decide +kernel
      have hl : raw18981step1Labels = raw18981step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18981step0 raw18981step0Labels permutation148 permutation5
    mixedMoment B raw18981step1 raw18981step1Labels = mixedMoment B raw18981step2 raw18981step2Labels := by
      have ha : raw18981step2 = raw18981step1 := by apply Matrix.ext; unfold raw18981step2 raw18981step1; decide +kernel
      have hl : raw18981step1Labels = labelEmbedding1 ∘ raw18981step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18981step1 raw18981step1Labels raw18981step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2724 node2724Labels := by rfl

theorem canonical18982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18982 raw18982Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw18982 raw18982Labels = mixedMoment B raw18982step0 raw18982step0Labels := by
      have hz : ∀ j, raw18982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18982step0 = (fun i j => raw18982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18982step0 raw18982; decide +kernel
      have hl : raw18982step0Labels = raw18982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18982 raw18982Labels permutation346 hz
    mixedMoment B raw18982step0 raw18982step0Labels = mixedMoment B raw18982step1 raw18982step1Labels := by
      have ha : raw18982step1 = (fun i j => raw18982step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18982step1 raw18982step0; decide +kernel
      have hl : raw18982step1Labels = raw18982step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18982step0 raw18982step0Labels permutation137 permutation5
    mixedMoment B raw18982step1 raw18982step1Labels = mixedMoment B raw18982step2 raw18982step2Labels := by
      have ha : raw18982step2 = raw18982step1 := by apply Matrix.ext; unfold raw18982step2 raw18982step1; decide +kernel
      have hl : raw18982step1Labels = labelEmbedding1 ∘ raw18982step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18982step1 raw18982step1Labels raw18982step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

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

theorem canonical606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw606 raw606Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw606 raw606Labels = mixedMoment B raw606step0 raw606step0Labels := by
      have ha : raw606step0 = (fun i j => raw606 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw606step0 raw606; decide +kernel
      have hl : raw606step0Labels = raw606Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw606 raw606Labels permutation32 permutation5
    mixedMoment B raw606step0 raw606step0Labels = mixedMoment B raw606step1 raw606step1Labels := by
      have ha : raw606step1 = raw606step0 := by apply Matrix.ext; unfold raw606step1 raw606step0; decide +kernel
      have hl : raw606step0Labels = labelEmbedding1 ∘ raw606step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw606step0 raw606step0Labels raw606step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

theorem canonical607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw607 raw607Labels = mixedMoment B node493 node493Labels := by
  calc
    mixedMoment B raw607 raw607Labels = mixedMoment B raw607step0 raw607step0Labels := by
      have ha : raw607step0 = (fun i j => raw607 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw607step0 raw607; decide +kernel
      have hl : raw607step0Labels = raw607Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw607 raw607Labels permutation145 permutation6
    _ = mixedMoment B node493 node493Labels := by rfl

theorem canonical612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw612 raw612Labels = mixedMoment B node3997 node3997Labels := by
  calc
    mixedMoment B raw612 raw612Labels = mixedMoment B raw612step0 raw612step0Labels := by
      have ha : raw612step0 = (fun i j => raw612 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw612step0 raw612; decide +kernel
      have hl : raw612step0Labels = raw612Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw612 raw612Labels permutation32 permutation5
    mixedMoment B raw612step0 raw612step0Labels = mixedMoment B raw612step1 raw612step1Labels := by
      have ha : raw612step1 = raw612step0 := by apply Matrix.ext; unfold raw612step1 raw612step0; decide +kernel
      have hl : raw612step0Labels = labelEmbedding1 ∘ raw612step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw612step0 raw612step0Labels raw612step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3997 node3997Labels := by rfl

theorem canonical613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw613 raw613Labels = mixedMoment B node522 node522Labels := by
  calc
    mixedMoment B raw613 raw613Labels = mixedMoment B raw613step0 raw613step0Labels := by
      have ha : raw613step0 = (fun i j => raw613 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw613step0 raw613; decide +kernel
      have hl : raw613step0Labels = raw613Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw613 raw613Labels permutation37 permutation4
    _ = mixedMoment B node522 node522Labels := by rfl

theorem canonical622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw622 raw622Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw622 raw622Labels = mixedMoment B raw622step0 raw622step0Labels := by
      have ha : raw622step0 = (fun i j => raw622 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw622step0 raw622; decide +kernel
      have hl : raw622step0Labels = raw622Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw622 raw622Labels permutation32 permutation5
    mixedMoment B raw622step0 raw622step0Labels = mixedMoment B raw622step1 raw622step1Labels := by
      have ha : raw622step1 = raw622step0 := by apply Matrix.ext; unfold raw622step1 raw622step0; decide +kernel
      have hl : raw622step0Labels = labelEmbedding1 ∘ raw622step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw622step0 raw622step0Labels raw622step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4012 node4012Labels := by rfl

theorem canonical623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw623 raw623Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw623 raw623Labels = mixedMoment B raw623step0 raw623step0Labels := by
      have ha : raw623step0 = (fun i j => raw623 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw623step0 raw623; decide +kernel
      have hl : raw623step0Labels = raw623Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw623 raw623Labels permutation137 permutation6
    _ = mixedMoment B node494 node494Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3959 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3959 = injectiveMoment H node705 := by
  calc
    injectiveMoment H raw3959 = injectiveMoment H raw3959step0 := by
      have heq : raw3959step0 = (fun i j => raw3959 (permutation82 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3959 permutation82 permutation5
    _ = injectiveMoment H node705 := by rfl

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

theorem canonical4130 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4130 = injectiveMoment H node210 := by
  rfl

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

theorem canonical5157 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5157 = injectiveMoment H node46 := by
  clear _hH
  calc
    injectiveMoment H raw5157 = injectiveMoment H raw5157step0 := by
      have hz : ∀ j, raw5157 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw5157step0 = (fun i j => raw5157 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5157 permutation57 hz
    _ = injectiveMoment H node46 := by rfl

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

theorem canonical9034 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9034 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9034 = injectiveMoment H raw9034step0 := by
      have hz : ∀ j, raw9034 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw9034step0 = (fun i j => raw9034 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9034 permutation104 hz
    injectiveMoment H raw9034step0 = injectiveMoment H raw9034step1 := by
      have hz : ∀ j, raw9034step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9034step1 = (fun i j => raw9034step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9034step0 permutation9 hz
    injectiveMoment H raw9034step1 = injectiveMoment H raw9034step2 := by
      have heq : raw9034step2 = (fun i j => raw9034step1 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9034step1 permutation5 permutation2
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

theorem canonical7717 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7717 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7717 = injectiveMoment H raw7717step0 := by
      have hz : ∀ j, raw7717 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7717step0 = (fun i j => raw7717 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7717 permutation104 hz
    injectiveMoment H raw7717step0 = injectiveMoment H raw7717step1 := by
      have hz : ∀ j, raw7717step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw7717step1 = (fun i j => raw7717step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7717step0 permutation15 hz
    injectiveMoment H raw7717step1 = injectiveMoment H raw7717step2 := by
      have heq : raw7717step2 = (fun i j => raw7717step1 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7717step1 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

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

theorem sound43 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node43 = Sparse.eval value43 (momentVector H) := by
  have hc : momentVector H 26 = injectiveMoment H node43 := rfl
  simp [value43, Sparse.eval, hc]

theorem sound44 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node44 = Sparse.eval value44 (momentVector H) := by
  have hc : momentVector H 4 = injectiveMoment H node44 := rfl
  simp [value44, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical152
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4887 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4887 = injectiveMoment H node710 := by
  calc
    injectiveMoment H raw4887 = injectiveMoment H raw4887step0 := by
      have heq : raw4887step0 = (fun i j => raw4887 (permutation88 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4887 permutation88 permutation5
    _ = injectiveMoment H node710 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4922 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4922 = injectiveMoment H node226 := by
  rfl

theorem canonical4923 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4923 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw4923 = injectiveMoment H raw4923step0 := by
      have heq : raw4923step0 = (fun i j => raw4923 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4923 permutation17 permutation5
    _ = injectiveMoment H node210 := by rfl

theorem canonical4925 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4925 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4925 = injectiveMoment H raw4925step0 := by
      have heq : raw4925step0 = -raw4925 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4925).symm
    injectiveMoment H raw4925step0 = injectiveMoment H raw4925step1 := by
      have heq : raw4925step1 = (fun i j => raw4925step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4925step0 permutation8 permutation3
    _ = injectiveMoment H node36 := by rfl

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

theorem canonical4946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4946 = injectiveMoment H node230 := by
  rfl

theorem canonical4948 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4948 = injectiveMoment H node44 := by
  calc
    injectiveMoment H raw4948 = injectiveMoment H raw4948step0 := by
      have hz : ∀ j, raw4948 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw4948step0 = (fun i j => raw4948 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4948 permutation15 hz
    _ = injectiveMoment H node44 := by rfl

theorem canonical4953 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4953 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw4953 = injectiveMoment H raw4953step0 := by
      have heq : raw4953step0 = (fun i j => raw4953 (permutation10 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4953 permutation10 permutation4
    _ = injectiveMoment H node229 := by rfl

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

theorem canonical4965 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4965 = injectiveMoment H node43 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5385 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5385 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw5385 = injectiveMoment H raw5385step0 := by
      have heq : raw5385step0 = -raw5385 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5385).symm
    injectiveMoment H raw5385step0 = injectiveMoment H raw5385step1 := by
      have heq : raw5385step1 = (fun i j => raw5385step0 (permutation17 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5385step0 permutation17 permutation7
    _ = injectiveMoment H node203 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical231
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7419 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7419 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw7419 = injectiveMoment H raw7419step0 := by
      have heq : raw7419step0 = -raw7419 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7419).symm
    injectiveMoment H raw7419step0 = injectiveMoment H raw7419step1 := by
      have heq : raw7419step1 = (fun i j => raw7419step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7419step0 permutation8 permutation3
    _ = injectiveMoment H node57 := by rfl

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

theorem sound226 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node226 = Sparse.eval value226 (momentVector H) := by
  have heq : pivotMatrix226 = (fun u v => node226 (pivotPermutation226 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node226 = injectiveMoment H pivotMatrix226 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix226 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix226 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix226 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix226 (0 : Fin 3) = raw7419 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7419 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix226 (1 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix226 (1 : Fin 3) = raw4965 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4965 hH).trans (sound43 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix226 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix226 (2 : Fin 3) = raw4925 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4925 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node226 + (injectiveMoment H (mergeFirst pivotMatrix226 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix226 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix226 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value226, value36, value43, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound229 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node229 = Sparse.eval value229 (momentVector H) := by
  have heq : pivotMatrix229 = (fun u v => node229 (pivotPermutation229 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node229 = injectiveMoment H pivotMatrix229 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix229 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix229 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix229 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix229 (0 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix229 (1 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix229 (1 : Fin 3) = raw4965 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4965 hH).trans (sound43 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix229 (2 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix229 (2 : Fin 3) = raw4966 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4966 hH).trans (sound44 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node229 + (injectiveMoment H (mergeFirst pivotMatrix229 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix229 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix229 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value229, value36, value43, value44, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound11
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound705 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node705 = Sparse.eval value705 (momentVector H) := by
  have heq : pivotMatrix705 = (fun u v => node705 (pivotPermutation705 u) v) := by apply Matrix.ext; unfold pivotMatrix705 node705 pivotPermutation705; decide +kernel
  have hmoment : injectiveMoment H node705 = injectiveMoment H pivotMatrix705 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix705 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix705 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix705 (0 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix705 (0 : Fin 4) = raw5385 := by apply Matrix.ext; unfold mergeFirst pivotMatrix705 raw5385; decide +kernel
    rw [heq]
    exact (canonical5385 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix705 (1 : Fin 4)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix705 (1 : Fin 4) = raw4946 := by apply Matrix.ext; unfold mergeFirst pivotMatrix705 raw4946; decide +kernel
    rw [heq]
    exact (canonical4946 hH).trans (sound230 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix705 (2 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix705 (2 : Fin 4) = raw4923 := by apply Matrix.ext; unfold mergeFirst pivotMatrix705 raw4923; decide +kernel
    rw [heq]
    exact (canonical4923 hH).trans (sound210 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix705 (3 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix705 (3 : Fin 4) = raw4922 := by apply Matrix.ext; unfold mergeFirst pivotMatrix705 raw4922; decide +kernel
    rw [heq]
    exact (canonical4922 hH).trans (sound226 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node705 + (injectiveMoment H (mergeFirst pivotMatrix705 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix705 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix705 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix705 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value705, value203, value210, value226, value230, Sparse.eval] at hc ⊢
  linarith

theorem sound710 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node710 = Sparse.eval value710 (momentVector H) := by
  have heq : pivotMatrix710 = (fun u v => node710 (pivotPermutation710 u) v) := by apply Matrix.ext; unfold pivotMatrix710 node710 pivotPermutation710; decide +kernel
  have hmoment : injectiveMoment H node710 = injectiveMoment H pivotMatrix710 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix710 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix710 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix710 (0 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix710 (0 : Fin 4) = raw4130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix710 raw4130; decide +kernel
    rw [heq]
    exact (canonical4130 hH).trans (sound210 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix710 (1 : Fin 4)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix710 (1 : Fin 4) = raw4948 := by apply Matrix.ext; unfold mergeFirst pivotMatrix710 raw4948; decide +kernel
    rw [heq]
    exact (canonical4948 hH).trans (sound44 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix710 (2 : Fin 4)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix710 (2 : Fin 4) = raw4953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix710 raw4953; decide +kernel
    rw [heq]
    exact (canonical4953 hH).trans (sound229 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix710 (3 : Fin 4)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix710 (3 : Fin 4) = raw4954 := by apply Matrix.ext; unfold mergeFirst pivotMatrix710 raw4954; decide +kernel
    rw [heq]
    exact (canonical4954 hH).trans (sound230 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node710 + (injectiveMoment H (mergeFirst pivotMatrix710 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix710 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix710 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix710 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value710, value210, value229, value230, value44, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical7659 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7659 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7659 = injectiveMoment H raw7659step0 := by
      have heq : raw7659step0 = (fun i j => raw7659 (permutation145 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7659 permutation145 permutation2
    _ = injectiveMoment H node232 := by rfl

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

theorem singlePair493 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node493 node493Labels = Sparse.eval singlePairValue493 (familyPairVector B) := by
  have hp := single_label_three B hB node493
  have hl : node493Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node493 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node493 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node493 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node493 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node493 (EqualityPatterns.family3.label 1) = PairSemantics.raw5157 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node493 PairSemantics.raw5157; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5157 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node493 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node493 (EqualityPatterns.family3.label 2) = PairSemantics.raw9034 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node493 PairSemantics.raw9034; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9034 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node493 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node493 (EqualityPatterns.family3.label 3) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node493 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node493 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value705 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node493 (EqualityPatterns.family3.label 4) = PairSemantics.raw3959 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node493 PairSemantics.raw3959; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3959 hH).trans (PairSemantics.sound705 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue493, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value232, PairSemantics.value705, Sparse.eval] at hp ⊢
  linarith only [hp]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair522 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node522 node522Labels = Sparse.eval singlePairValue522 (familyPairVector B) := by
  have hp := single_label_three B hB node522
  have hl : node522Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node522 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node522 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node522 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node522 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node522 (EqualityPatterns.family3.label 1) = PairSemantics.raw7659 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node522 PairSemantics.raw7659; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7659 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node522 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node522 (EqualityPatterns.family3.label 2) = PairSemantics.raw7717 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node522 PairSemantics.raw7717; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7717 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node522 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node522 (EqualityPatterns.family3.label 3) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node522 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node522 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value710 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node522 (EqualityPatterns.family3.label 4) = PairSemantics.raw4887 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node522 PairSemantics.raw4887; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4887 hH).trans (PairSemantics.sound710 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue522, PairSemantics.value0, PairSemantics.value11, PairSemantics.value232, PairSemantics.value710, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3993 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3993 node3993Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node493 node493Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw606 singletonSmall3993
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3993) = raw606Labels := by decide +kernel
  rw [hl, canonical606 B hB] at h
  have hc0 : mixedMoment B raw606 (Fin.cases (0 : Fin 1) singletonSmall3993) =
      mixedMoment B node493 node493Labels := by
    have ha : raw606 = raw607 := by apply Matrix.ext; unfold raw606 raw607; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3993 = raw607Labels := by decide +kernel
    rw [ha, hj, canonical607 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton3997 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3997 node3997Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node522 node522Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw612 singletonSmall3997
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3997) = raw612Labels := by decide +kernel
  rw [hl, canonical612 B hB] at h
  have hc0 : mixedMoment B raw612 (Fin.cases (0 : Fin 1) singletonSmall3997) =
      mixedMoment B node522 node522Labels := by
    have ha : raw612 = raw613 := by apply Matrix.ext; unfold raw612 raw613; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3997 = raw613Labels := by decide +kernel
    rw [ha, hj, canonical613 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton4012 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4012 node4012Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node494 node494Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw622 singletonSmall4012
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4012) = raw622Labels := by decide +kernel
  rw [hl, canonical622 B hB] at h
  have hc0 : mixedMoment B raw622 (Fin.cases (0 : Fin 1) singletonSmall4012) =
      mixedMoment B node494 node494Labels := by
    have ha : raw622 = raw623 := by apply Matrix.ext; unfold raw622 raw623; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4012 = raw623Labels := by decide +kernel
    rw [ha, hj, canonical623 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem sound2718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2718 node2718Labels = Sparse.eval nodeValue2718 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2718) = mixedMoment B node2718 node2718Labels := rfl
  simpa [nodeValue2718, Sparse.eval] using hc.symm

theorem sound2719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2719 node2719Labels = Sparse.eval nodeValue2719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2719) = mixedMoment B node2719 node2719Labels := rfl
  simpa [nodeValue2719, Sparse.eval] using hc.symm

theorem sound2724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2724 node2724Labels = Sparse.eval nodeValue2724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2724) = mixedMoment B node2724 node2724Labels := rfl
  simpa [nodeValue2724, Sparse.eval] using hc.symm

theorem sound2736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2736 node2736Labels = Sparse.eval nodeValue2736 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2736) = mixedMoment B node2736 node2736Labels := rfl
  simpa [nodeValue2736, Sparse.eval] using hc.symm

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

theorem sound2763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2763 node2763Labels = Sparse.eval nodeValue2763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2763) = mixedMoment B node2763 node2763Labels := rfl
  simpa [nodeValue2763, Sparse.eval] using hc.symm

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

theorem sound3558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3558 node3558Labels = Sparse.eval nodeValue3558 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3558) = mixedMoment B node3558 node3558Labels := rfl
  simpa [nodeValue3558, Sparse.eval] using hc.symm

theorem sound3565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3565 node3565Labels = Sparse.eval nodeValue3565 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3565) = mixedMoment B node3565 node3565Labels := rfl
  simpa [nodeValue3565, Sparse.eval] using hc.symm

theorem sound3572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3572 node3572Labels = Sparse.eval nodeValue3572 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3572) = mixedMoment B node3572 node3572Labels := rfl
  simpa [nodeValue3572, Sparse.eval] using hc.symm

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

theorem sound3606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3606 node3606Labels = Sparse.eval nodeValue3606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3606) = mixedMoment B node3606 node3606Labels := rfl
  simpa [nodeValue3606, Sparse.eval] using hc.symm

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

theorem sound493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node493 node493Labels = Sparse.eval nodeValue493 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue493 (familyPairVector B) := singlePair493 B _hB
    _ = _ := by norm_num [singlePairValue493, nodeValue493, Sparse.eval, mixedVector] <;> ring

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = 0 := by
  exact mixedMoment_order_one B hB node3816 node3816Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3804 node3804Labels = Sparse.eval nodeValue3804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3804) = mixedMoment B node3804 node3804Labels := rfl
  simpa [nodeValue3804, Sparse.eval] using hc.symm

theorem sound3815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3815 node3815Labels = Sparse.eval nodeValue3815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3815) = mixedMoment B node3815 node3815Labels := rfl
  simpa [nodeValue3815, Sparse.eval] using hc.symm

theorem sound3816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = Sparse.eval nodeValue3816 (mixedVector B) := by
  simpa only [nodeValue3816, Sparse.eval_nil] using zero3816 B _hB _hF

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

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node522 node522Labels = Sparse.eval nodeValue522 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue522 (familyPairVector B) := singlePair522 B _hB
    _ = _ := by norm_num [singlePairValue522, nodeValue522, Sparse.eval, mixedVector] <;> ring

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

theorem sound3955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3955 node3955Labels = Sparse.eval nodeValue3955 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3955) = mixedMoment B node3955 node3955Labels := rfl
  simpa [nodeValue3955, Sparse.eval] using hc.symm

theorem sound3959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3959 node3959Labels = Sparse.eval nodeValue3959 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3959) = mixedMoment B node3959 node3959Labels := rfl
  simpa [nodeValue3959, Sparse.eval] using hc.symm

theorem sound3960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3960 node3960Labels = Sparse.eval nodeValue3960 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3960) = mixedMoment B node3960 node3960Labels := rfl
  simpa [nodeValue3960, Sparse.eval] using hc.symm

theorem sound3961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3961 node3961Labels = Sparse.eval nodeValue3961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3961) = mixedMoment B node3961 node3961Labels := rfl
  simpa [nodeValue3961, Sparse.eval] using hc.symm

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

theorem zero3979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3979 node3979Labels = 0 := by
  exact mixedMoment_alpha B hF node3979 node3979Labels 2 permutation158
    (by decide +kernel)

theorem zero3985 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3985 node3985Labels = 0 := by
  exact mixedMoment_order_one B hB node3985 node3985Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3972 node3972Labels = Sparse.eval nodeValue3972 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3972) = mixedMoment B node3972 node3972Labels := rfl
  simpa [nodeValue3972, Sparse.eval] using hc.symm

theorem sound3973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3973 node3973Labels = Sparse.eval nodeValue3973 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3973) = mixedMoment B node3973 node3973Labels := rfl
  simpa [nodeValue3973, Sparse.eval] using hc.symm

theorem sound3974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3974 node3974Labels = Sparse.eval nodeValue3974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3974) = mixedMoment B node3974 node3974Labels := rfl
  simpa [nodeValue3974, Sparse.eval] using hc.symm

theorem sound3978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3978 node3978Labels = Sparse.eval nodeValue3978 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3978) = mixedMoment B node3978 node3978Labels := rfl
  simpa [nodeValue3978, Sparse.eval] using hc.symm

theorem sound3979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3979 node3979Labels = Sparse.eval nodeValue3979 (mixedVector B) := by
  simpa only [nodeValue3979, Sparse.eval_nil] using zero3979 B _hB _hF

theorem sound3983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3983 node3983Labels = Sparse.eval nodeValue3983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3983) = mixedMoment B node3983 node3983Labels := rfl
  simpa [nodeValue3983, Sparse.eval] using hc.symm

theorem sound3985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3985 node3985Labels = Sparse.eval nodeValue3985 (mixedVector B) := by
  simpa only [nodeValue3985, Sparse.eval_nil] using zero3985 B _hB _hF

theorem sound3993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3993 node3993Labels = Sparse.eval nodeValue3993 (mixedVector B) := by
  have h := singleton3993 B _hB
  rw [sound493 B _hB _hF] at h
  norm_num [nodeValue3993, nodeValue493, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3997 node3997Labels = Sparse.eval nodeValue3997 (mixedVector B) := by
  have h := singleton3997 B _hB
  rw [sound522 B _hB _hF] at h
  norm_num [nodeValue3997, nodeValue522, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4012 node4012Labels = Sparse.eval nodeValue4012 (mixedVector B) := by
  have h := singleton4012 B _hB
  rw [sound494 B _hB _hF] at h
  norm_num [nodeValue4012, nodeValue494, Sparse.eval] at h ⊢
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

theorem sourceEq1123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1123 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1123 + difference 0 1) (sourceB1123 + difference 1 0) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA1123 + difference 0 1) (sourceB1123 + difference 1 0) sourceC1123) = raw18953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18953; decide +kernel
    rw [ha]
    exact (canonical18953 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1123 + difference 0 2) (sourceB1123 + difference 2 0) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA1123 + difference 0 2) (sourceB1123 + difference 2 0) sourceC1123) = raw18954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18954; decide +kernel
    rw [ha]
    exact (canonical18954 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1123 + difference 0 3) (sourceB1123 + difference 3 0) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA1123 + difference 0 3) (sourceB1123 + difference 3 0) sourceC1123) = raw18955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18955; decide +kernel
    rw [ha]
    exact (canonical18955 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1123 + difference 0 4) (sourceB1123 + difference 4 0) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA1123 + difference 0 4) (sourceB1123 + difference 4 0) sourceC1123) = raw18956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18956; decide +kernel
    rw [ha]
    exact (canonical18956 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1123 + difference 0 5) (sourceB1123 + difference 5 0) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3985) := by
    have ha : (tripleCharges (sourceA1123 + difference 0 5) (sourceB1123 + difference 5 0) sourceC1123) = raw18957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18957; decide +kernel
    rw [ha]
    exact (canonical18957 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1123 + difference 1 0) (sourceB1123 + difference 0 1) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA1123 + difference 1 0) (sourceB1123 + difference 0 1) sourceC1123) = raw18958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18958; decide +kernel
    rw [ha]
    exact (canonical18958 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1123 + difference 1 2) (sourceB1123 + difference 2 1) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA1123 + difference 1 2) (sourceB1123 + difference 2 1) sourceC1123) = raw18959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18959; decide +kernel
    rw [ha]
    exact (canonical18959 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1123 + difference 1 3) (sourceB1123 + difference 3 1) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA1123 + difference 1 3) (sourceB1123 + difference 3 1) sourceC1123) = raw18960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18960; decide +kernel
    rw [ha]
    exact (canonical18960 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1123 + difference 1 4) (sourceB1123 + difference 4 1) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3997) := by
    have ha : (tripleCharges (sourceA1123 + difference 1 4) (sourceB1123 + difference 4 1) sourceC1123) = raw18961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18961; decide +kernel
    rw [ha]
    exact (canonical18961 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1123 + difference 1 5) (sourceB1123 + difference 5 1) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3984) := by
    have ha : (tripleCharges (sourceA1123 + difference 1 5) (sourceB1123 + difference 5 1) sourceC1123) = raw18962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18962; decide +kernel
    rw [ha]
    exact (canonical18962 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1123 + difference 2 0) (sourceB1123 + difference 0 2) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA1123 + difference 2 0) (sourceB1123 + difference 0 2) sourceC1123) = raw18963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18963; decide +kernel
    rw [ha]
    exact (canonical18963 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1123 + difference 2 1) (sourceB1123 + difference 1 2) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3973) := by
    have ha : (tripleCharges (sourceA1123 + difference 2 1) (sourceB1123 + difference 1 2) sourceC1123) = raw18964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18964; decide +kernel
    rw [ha]
    exact (canonical18964 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1123 + difference 2 3) (sourceB1123 + difference 3 2) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA1123 + difference 2 3) (sourceB1123 + difference 3 2) sourceC1123) = raw18965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18965; decide +kernel
    rw [ha]
    exact (canonical18965 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1123 + difference 2 4) (sourceB1123 + difference 4 2) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA1123 + difference 2 4) (sourceB1123 + difference 4 2) sourceC1123) = raw18966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18966; decide +kernel
    rw [ha]
    exact (canonical18966 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1123 + difference 2 5) (sourceB1123 + difference 5 2) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA1123 + difference 2 5) (sourceB1123 + difference 5 2) sourceC1123) = raw18967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18967; decide +kernel
    rw [ha]
    exact (canonical18967 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1123 + difference 3 0) (sourceB1123 + difference 0 3) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA1123 + difference 3 0) (sourceB1123 + difference 0 3) sourceC1123) = raw18968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18968; decide +kernel
    rw [ha]
    exact (canonical18968 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1123 + difference 3 1) (sourceB1123 + difference 1 3) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3815) := by
    have ha : (tripleCharges (sourceA1123 + difference 3 1) (sourceB1123 + difference 1 3) sourceC1123) = raw18969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18969; decide +kernel
    rw [ha]
    exact (canonical18969 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1123 + difference 3 2) (sourceB1123 + difference 2 3) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA1123 + difference 3 2) (sourceB1123 + difference 2 3) sourceC1123) = raw18970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18970; decide +kernel
    rw [ha]
    exact (canonical18970 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1123 + difference 3 4) (sourceB1123 + difference 4 3) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA1123 + difference 3 4) (sourceB1123 + difference 4 3) sourceC1123) = raw18971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18971; decide +kernel
    rw [ha]
    exact (canonical18971 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1123 + difference 3 5) (sourceB1123 + difference 5 3) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA1123 + difference 3 5) (sourceB1123 + difference 5 3) sourceC1123) = raw18972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18972; decide +kernel
    rw [ha]
    exact (canonical18972 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1123 + difference 4 0) (sourceB1123 + difference 0 4) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA1123 + difference 4 0) (sourceB1123 + difference 0 4) sourceC1123) = raw18973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18973; decide +kernel
    rw [ha]
    exact (canonical18973 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1123 + difference 4 1) (sourceB1123 + difference 1 4) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3960) := by
    have ha : (tripleCharges (sourceA1123 + difference 4 1) (sourceB1123 + difference 1 4) sourceC1123) = raw18974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18974; decide +kernel
    rw [ha]
    exact (canonical18974 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1123 + difference 4 2) (sourceB1123 + difference 2 4) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3955) := by
    have ha : (tripleCharges (sourceA1123 + difference 4 2) (sourceB1123 + difference 2 4) sourceC1123) = raw18975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18975; decide +kernel
    rw [ha]
    exact (canonical18975 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1123 + difference 4 3) (sourceB1123 + difference 3 4) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1123 + difference 4 3) (sourceB1123 + difference 3 4) sourceC1123) = raw18976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18976; decide +kernel
    rw [ha]
    exact (canonical18976 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1123 + difference 4 5) (sourceB1123 + difference 5 4) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA1123 + difference 4 5) (sourceB1123 + difference 5 4) sourceC1123) = raw18977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18977; decide +kernel
    rw [ha]
    exact (canonical18977 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1123 + difference 5 0) (sourceB1123 + difference 0 5) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA1123 + difference 5 0) (sourceB1123 + difference 0 5) sourceC1123) = raw18978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18978; decide +kernel
    rw [ha]
    exact (canonical18978 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1123 + difference 5 1) (sourceB1123 + difference 1 5) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA1123 + difference 5 1) (sourceB1123 + difference 1 5) sourceC1123) = raw18979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18979; decide +kernel
    rw [ha]
    exact (canonical18979 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1123 + difference 5 2) (sourceB1123 + difference 2 5) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA1123 + difference 5 2) (sourceB1123 + difference 2 5) sourceC1123) = raw18980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18980; decide +kernel
    rw [ha]
    exact (canonical18980 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1123 + difference 5 3) (sourceB1123 + difference 3 5) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA1123 + difference 5 3) (sourceB1123 + difference 3 5) sourceC1123) = raw18981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18981; decide +kernel
    rw [ha]
    exact (canonical18981 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1123 + difference 5 4) (sourceB1123 + difference 4 5) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA1123 + difference 5 4) (sourceB1123 + difference 4 5) sourceC1123) = raw18982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18982; decide +kernel
    rw [ha]
    exact (canonical18982 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1123 sourceB1123 sourceC1123
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1123, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck975 : Integer.Sparse.reindex keyMap MixedData.row975 = numericRow975 := by decide +kernel

theorem numericCheck975 (x : Master → ℝ) : Integer.Sparse.eval numericRow975 x =
    (4320 : ℝ) * reducedSource975 x := by
  norm_num [numericRow975, reducedSource975, Integer.Sparse.eval, Sparse.eval, nodeValue2718, nodeValue2719, nodeValue2724, nodeValue2736, nodeValue2763, nodeValue3558, nodeValue3565, nodeValue3572, nodeValue3606, nodeValue3804, nodeValue3815, nodeValue3816, nodeValue3857, nodeValue3955, nodeValue3959, nodeValue3960, nodeValue3961, nodeValue3972, nodeValue3973, nodeValue3974, nodeValue3978, nodeValue3979, nodeValue3983, nodeValue3984, nodeValue3985, nodeValue3993, nodeValue3997, nodeValue3998, nodeValue4012]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero975 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource975 (mixedVector B) = 0 := by
  have h2718 : mixedVector B (Sum.inr 2718) = Sparse.eval nodeValue2718 (mixedVector B) := by
    change mixedMoment B node2718 node2718Labels = _
    exact sound2718 B hB hF
  have h2719 : mixedVector B (Sum.inr 2719) = Sparse.eval nodeValue2719 (mixedVector B) := by
    change mixedMoment B node2719 node2719Labels = _
    exact sound2719 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h2736 : mixedVector B (Sum.inr 2736) = Sparse.eval nodeValue2736 (mixedVector B) := by
    change mixedMoment B node2736 node2736Labels = _
    exact sound2736 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h3558 : mixedVector B (Sum.inr 3558) = Sparse.eval nodeValue3558 (mixedVector B) := by
    change mixedMoment B node3558 node3558Labels = _
    exact sound3558 B hB hF
  have h3565 : mixedVector B (Sum.inr 3565) = Sparse.eval nodeValue3565 (mixedVector B) := by
    change mixedMoment B node3565 node3565Labels = _
    exact sound3565 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3606 : mixedVector B (Sum.inr 3606) = Sparse.eval nodeValue3606 (mixedVector B) := by
    change mixedMoment B node3606 node3606Labels = _
    exact sound3606 B hB hF
  have h3804 : mixedVector B (Sum.inr 3804) = Sparse.eval nodeValue3804 (mixedVector B) := by
    change mixedMoment B node3804 node3804Labels = _
    exact sound3804 B hB hF
  have h3815 : mixedVector B (Sum.inr 3815) = Sparse.eval nodeValue3815 (mixedVector B) := by
    change mixedMoment B node3815 node3815Labels = _
    exact sound3815 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h3955 : mixedVector B (Sum.inr 3955) = Sparse.eval nodeValue3955 (mixedVector B) := by
    change mixedMoment B node3955 node3955Labels = _
    exact sound3955 B hB hF
  have h3959 : mixedVector B (Sum.inr 3959) = Sparse.eval nodeValue3959 (mixedVector B) := by
    change mixedMoment B node3959 node3959Labels = _
    exact sound3959 B hB hF
  have h3960 : mixedVector B (Sum.inr 3960) = Sparse.eval nodeValue3960 (mixedVector B) := by
    change mixedMoment B node3960 node3960Labels = _
    exact sound3960 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  have h3972 : mixedVector B (Sum.inr 3972) = Sparse.eval nodeValue3972 (mixedVector B) := by
    change mixedMoment B node3972 node3972Labels = _
    exact sound3972 B hB hF
  have h3973 : mixedVector B (Sum.inr 3973) = Sparse.eval nodeValue3973 (mixedVector B) := by
    change mixedMoment B node3973 node3973Labels = _
    exact sound3973 B hB hF
  have h3974 : mixedVector B (Sum.inr 3974) = Sparse.eval nodeValue3974 (mixedVector B) := by
    change mixedMoment B node3974 node3974Labels = _
    exact sound3974 B hB hF
  have h3978 : mixedVector B (Sum.inr 3978) = Sparse.eval nodeValue3978 (mixedVector B) := by
    change mixedMoment B node3978 node3978Labels = _
    exact sound3978 B hB hF
  have h3979 : mixedVector B (Sum.inr 3979) = Sparse.eval nodeValue3979 (mixedVector B) := by
    change mixedMoment B node3979 node3979Labels = _
    exact sound3979 B hB hF
  have h3983 : mixedVector B (Sum.inr 3983) = Sparse.eval nodeValue3983 (mixedVector B) := by
    change mixedMoment B node3983 node3983Labels = _
    exact sound3983 B hB hF
  have h3984 : mixedVector B (Sum.inr 3984) = Sparse.eval nodeValue3984 (mixedVector B) := by
    change mixedMoment B node3984 node3984Labels = _
    exact sound3984_e B hB hF
  have h3985 : mixedVector B (Sum.inr 3985) = Sparse.eval nodeValue3985 (mixedVector B) := by
    change mixedMoment B node3985 node3985Labels = _
    exact sound3985 B hB hF
  have h3993 : mixedVector B (Sum.inr 3993) = Sparse.eval nodeValue3993 (mixedVector B) := by
    change mixedMoment B node3993 node3993Labels = _
    exact sound3993 B hB hF
  have h3997 : mixedVector B (Sum.inr 3997) = Sparse.eval nodeValue3997 (mixedVector B) := by
    change mixedMoment B node3997 node3997Labels = _
    exact sound3997 B hB hF
  have h3998 : mixedVector B (Sum.inr 3998) = Sparse.eval nodeValue3998 (mixedVector B) := by
    change mixedMoment B node3998 node3998Labels = _
    exact sound3998_e B hB hF
  have h4012 : mixedVector B (Sum.inr 4012) = Sparse.eval nodeValue4012 (mixedVector B) := by
    change mixedMoment B node4012 node4012Labels = _
    exact sound4012 B hB hF
  simpa only [sourceForm1123, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2718, h2719, h2724, h2736, h2763, h3558, h3565, h3572, h3606, h3804, h3815, h3816, h3857, h3955, h3959, h3960, h3961, h3972, h3973, h3974, h3978, h3979, h3983, h3984, h3985, h3993, h3997, h3998, h4012, reducedSource975] using sourceEq1123 B hB

theorem rowSound975_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row975 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck975, numericCheck975, reducedZero975 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound975_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound975_e_oai
