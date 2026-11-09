-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1978_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:32:09.930508+00:00
-- url     : https://prove2.me/submissions/79e389a5-a39c-4c49-b988-ca794f456f69

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5168_e

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

theorem canonical1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1725 raw1725Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw1725 raw1725Labels = mixedMoment B raw1725step0 raw1725step0Labels := by
      have ha : raw1725step0 = (fun i j => raw1725 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1725step0 raw1725; decide +kernel
      have hl : raw1725step0Labels = raw1725Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1725 raw1725Labels permutation152 permutation4
    mixedMoment B raw1725step0 raw1725step0Labels = mixedMoment B raw1725step1 raw1725step1Labels := by
      have ha : raw1725step1 = raw1725step0 := by apply Matrix.ext; unfold raw1725step1 raw1725step0; decide +kernel
      have hl : raw1725step0Labels = labelEmbedding7 ∘ raw1725step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1725step0 raw1725step0Labels raw1725step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical1726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1726 raw1726Labels = mixedMoment B node2016 node2016Labels := by
  calc
    mixedMoment B raw1726 raw1726Labels = mixedMoment B raw1726step0 raw1726step0Labels := by
      have ha : raw1726step0 = (fun i j => raw1726 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1726step0 raw1726; decide +kernel
      have hl : raw1726step0Labels = raw1726Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1726 raw1726Labels permutation152 permutation4
    _ = mixedMoment B node2016 node2016Labels := by rfl

theorem canonical1727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1727 raw1727Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw1727 raw1727Labels = mixedMoment B raw1727step0 raw1727step0Labels := by
      have ha : raw1727step0 = (fun i j => raw1727 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1727step0 raw1727; decide +kernel
      have hl : raw1727step0Labels = raw1727Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1727 raw1727Labels permutation200 permutation6
    mixedMoment B raw1727step0 raw1727step0Labels = mixedMoment B raw1727step1 raw1727step1Labels := by
      have ha : raw1727step1 = -raw1727step0 := by apply Matrix.ext; change ∀ i j, raw1727step1 i j = -(raw1727step0 i j); unfold raw1727step1 raw1727step0; decide +kernel
      have hl : raw1727step1Labels = raw1727step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1727step1 raw1727step1Labels = mixedMoment B raw1727step2 raw1727step2Labels := by
      have ha : raw1727step2 = raw1727step1 := by apply Matrix.ext; unfold raw1727step2 raw1727step1; decide +kernel
      have hl : raw1727step1Labels = labelEmbedding1 ∘ raw1727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1727step1 raw1727step1Labels raw1727step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2075 node2075Labels := by rfl

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

theorem canonical1764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1764 raw1764Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw1764 raw1764Labels = mixedMoment B raw1764step0 raw1764step0Labels := by
      have ha : raw1764step0 = (fun i j => raw1764 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1764step0 raw1764; decide +kernel
      have hl : raw1764step0Labels = raw1764Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1764 raw1764Labels permutation32 permutation4
    mixedMoment B raw1764step0 raw1764step0Labels = mixedMoment B raw1764step1 raw1764step1Labels := by
      have ha : raw1764step1 = raw1764step0 := by apply Matrix.ext; unfold raw1764step1 raw1764step0; decide +kernel
      have hl : raw1764step0Labels = labelEmbedding7 ∘ raw1764step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1764step0 raw1764step0Labels raw1764step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

theorem canonical1765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1765 raw1765Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw1765 raw1765Labels = mixedMoment B raw1765step0 raw1765step0Labels := by
      have ha : raw1765step0 = (fun i j => raw1765 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1765step0 raw1765; decide +kernel
      have hl : raw1765step0Labels = raw1765Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1765 raw1765Labels permutation32 permutation4
    _ = mixedMoment B node2052 node2052Labels := by rfl

theorem canonical1766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1766 raw1766Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw1766 raw1766Labels = mixedMoment B raw1766step0 raw1766step0Labels := by
      have ha : raw1766step0 = (fun i j => raw1766 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1766step0 raw1766; decide +kernel
      have hl : raw1766step0Labels = raw1766Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1766 raw1766Labels permutation32 permutation6
    mixedMoment B raw1766step0 raw1766step0Labels = mixedMoment B raw1766step1 raw1766step1Labels := by
      have ha : raw1766step1 = -raw1766step0 := by apply Matrix.ext; change ∀ i j, raw1766step1 i j = -(raw1766step0 i j); unfold raw1766step1 raw1766step0; decide +kernel
      have hl : raw1766step1Labels = raw1766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1766step1 raw1766step1Labels = mixedMoment B raw1766step2 raw1766step2Labels := by
      have ha : raw1766step2 = raw1766step1 := by apply Matrix.ext; unfold raw1766step2 raw1766step1; decide +kernel
      have hl : raw1766step1Labels = labelEmbedding1 ∘ raw1766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1766step1 raw1766step1Labels raw1766step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

theorem canonical1782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1782 raw1782Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw1782 raw1782Labels = mixedMoment B raw1782step0 raw1782step0Labels := by
      have ha : raw1782step0 = (fun i j => raw1782 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1782step0 raw1782; decide +kernel
      have hl : raw1782step0Labels = raw1782Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1782 raw1782Labels permutation32 permutation4
    mixedMoment B raw1782step0 raw1782step0Labels = mixedMoment B raw1782step1 raw1782step1Labels := by
      have ha : raw1782step1 = raw1782step0 := by apply Matrix.ext; unfold raw1782step1 raw1782step0; decide +kernel
      have hl : raw1782step0Labels = labelEmbedding7 ∘ raw1782step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1782step0 raw1782step0Labels raw1782step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

theorem canonical1783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1783 raw1783Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw1783 raw1783Labels = mixedMoment B raw1783step0 raw1783step0Labels := by
      have ha : raw1783step0 = (fun i j => raw1783 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1783step0 raw1783; decide +kernel
      have hl : raw1783step0Labels = raw1783Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1783 raw1783Labels permutation32 permutation4
    _ = mixedMoment B node2101 node2101Labels := by rfl

theorem canonical1784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1784 raw1784Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw1784 raw1784Labels = mixedMoment B raw1784step0 raw1784step0Labels := by
      have ha : raw1784step0 = (fun i j => raw1784 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1784step0 raw1784; decide +kernel
      have hl : raw1784step0Labels = raw1784Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1784 raw1784Labels permutation38 permutation6
    mixedMoment B raw1784step0 raw1784step0Labels = mixedMoment B raw1784step1 raw1784step1Labels := by
      have ha : raw1784step1 = -raw1784step0 := by apply Matrix.ext; change ∀ i j, raw1784step1 i j = -(raw1784step0 i j); unfold raw1784step1 raw1784step0; decide +kernel
      have hl : raw1784step1Labels = raw1784step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1784step1 raw1784step1Labels = mixedMoment B raw1784step2 raw1784step2Labels := by
      have ha : raw1784step2 = raw1784step1 := by apply Matrix.ext; unfold raw1784step2 raw1784step1; decide +kernel
      have hl : raw1784step1Labels = labelEmbedding1 ∘ raw1784step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1784step1 raw1784step1Labels raw1784step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2101 node2101Labels := by rfl

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

theorem canonical2229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2229 raw2229Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw2229 raw2229Labels = mixedMoment B raw2229step0 raw2229step0Labels := by
      have ha : raw2229step0 = (fun i j => raw2229 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2229step0 raw2229; decide +kernel
      have hl : raw2229step0Labels = raw2229Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2229 raw2229Labels permutation32 permutation5
    mixedMoment B raw2229step0 raw2229step0Labels = mixedMoment B raw2229step1 raw2229step1Labels := by
      have ha : raw2229step1 = raw2229step0 := by apply Matrix.ext; unfold raw2229step1 raw2229step0; decide +kernel
      have hl : raw2229step0Labels = labelEmbedding8 ∘ raw2229step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2229step0 raw2229step0Labels raw2229step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

theorem canonical2230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2230 raw2230Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw2230 raw2230Labels = mixedMoment B raw2230step0 raw2230step0Labels := by
      have ha : raw2230step0 = (fun i j => raw2230 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2230step0 raw2230; decide +kernel
      have hl : raw2230step0Labels = raw2230Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2230 raw2230Labels permutation32 permutation4
    _ = mixedMoment B node2884 node2884Labels := by rfl

theorem canonical2231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2231 raw2231Labels = mixedMoment B node3621 node3621Labels := by
  calc
    mixedMoment B raw2231 raw2231Labels = mixedMoment B raw2231step0 raw2231step0Labels := by
      have ha : raw2231step0 = (fun i j => raw2231 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2231step0 raw2231; decide +kernel
      have hl : raw2231step0Labels = raw2231Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2231 raw2231Labels permutation40 permutation3
    mixedMoment B raw2231step0 raw2231step0Labels = mixedMoment B raw2231step1 raw2231step1Labels := by
      have ha : raw2231step1 = -raw2231step0 := by apply Matrix.ext; change ∀ i j, raw2231step1 i j = -(raw2231step0 i j); unfold raw2231step1 raw2231step0; decide +kernel
      have hl : raw2231step1Labels = raw2231step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2231step1 raw2231step1Labels = mixedMoment B raw2231step2 raw2231step2Labels := by
      have ha : raw2231step2 = raw2231step1 := by apply Matrix.ext; unfold raw2231step2 raw2231step1; decide +kernel
      have hl : raw2231step1Labels = labelEmbedding1 ∘ raw2231step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2231step1 raw2231step1Labels raw2231step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3621 node3621Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical252
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32317 raw32317Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw32317 raw32317Labels = mixedMoment B raw32317step0 raw32317step0Labels := by
      have ha : raw32317step0 = (fun i j => raw32317 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32317step0 raw32317; decide +kernel
      have hl : raw32317step0Labels = raw32317Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32317 raw32317Labels permutation152 permutation6
    mixedMoment B raw32317step0 raw32317step0Labels = mixedMoment B raw32317step1 raw32317step1Labels := by
      have ha : raw32317step1 = raw32317step0 := by apply Matrix.ext; unfold raw32317step1 raw32317step0; decide +kernel
      have hl : raw32317step0Labels = labelEmbedding9 ∘ raw32317step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32317step0 raw32317step0Labels raw32317step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

theorem canonical32318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32318 raw32318Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw32318 raw32318Labels = mixedMoment B raw32318step0 raw32318step0Labels := by
      have hz : ∀ j, raw32318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32318step0 = (fun i j => raw32318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32318step0 raw32318; decide +kernel
      have hl : raw32318step0Labels = raw32318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32318 raw32318Labels permutation346 hz
    mixedMoment B raw32318step0 raw32318step0Labels = mixedMoment B raw32318step1 raw32318step1Labels := by
      have ha : raw32318step1 = (fun i j => raw32318step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32318step1 raw32318step0; decide +kernel
      have hl : raw32318step1Labels = raw32318step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32318step0 raw32318step0Labels permutation32 permutation6
    mixedMoment B raw32318step1 raw32318step1Labels = mixedMoment B raw32318step2 raw32318step2Labels := by
      have ha : raw32318step2 = raw32318step1 := by apply Matrix.ext; unfold raw32318step2 raw32318step1; decide +kernel
      have hl : raw32318step1Labels = labelEmbedding9 ∘ raw32318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32318step1 raw32318step1Labels raw32318step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

theorem canonical32333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32333 raw32333Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw32333 raw32333Labels = mixedMoment B raw32333step0 raw32333step0Labels := by
      have ha : raw32333step0 = (fun i j => raw32333 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32333step0 raw32333; decide +kernel
      have hl : raw32333step0Labels = raw32333Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32333 raw32333Labels permutation152 permutation6
    mixedMoment B raw32333step0 raw32333step0Labels = mixedMoment B raw32333step1 raw32333step1Labels := by
      have ha : raw32333step1 = raw32333step0 := by apply Matrix.ext; unfold raw32333step1 raw32333step0; decide +kernel
      have hl : raw32333step0Labels = labelEmbedding9 ∘ raw32333step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32333step0 raw32333step0Labels raw32333step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

theorem canonical32335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32335 raw32335Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw32335 raw32335Labels = mixedMoment B raw32335step0 raw32335step0Labels := by
      have hz : ∀ j, raw32335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32335step0 = (fun i j => raw32335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32335step0 raw32335; decide +kernel
      have hl : raw32335step0Labels = raw32335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32335 raw32335Labels permutation346 hz
    mixedMoment B raw32335step0 raw32335step0Labels = mixedMoment B raw32335step1 raw32335step1Labels := by
      have ha : raw32335step1 = (fun i j => raw32335step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32335step1 raw32335step0; decide +kernel
      have hl : raw32335step1Labels = raw32335step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32335step0 raw32335step0Labels permutation32 permutation6
    mixedMoment B raw32335step1 raw32335step1Labels = mixedMoment B raw32335step2 raw32335step2Labels := by
      have ha : raw32335step2 = raw32335step1 := by apply Matrix.ext; unfold raw32335step2 raw32335step1; decide +kernel
      have hl : raw32335step1Labels = labelEmbedding9 ∘ raw32335step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32335step1 raw32335step1Labels raw32335step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32822 raw32822Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw32822 raw32822Labels = mixedMoment B raw32822step0 raw32822step0Labels := by
      have hz : ∀ j, raw32822 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32822step0 = (fun i j => raw32822 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32822step0 raw32822; decide +kernel
      have hl : raw32822step0Labels = raw32822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32822 raw32822Labels permutation346 hz
    mixedMoment B raw32822step0 raw32822step0Labels = mixedMoment B raw32822step1 raw32822step1Labels := by
      have ha : raw32822step1 = (fun i j => raw32822step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32822step1 raw32822step0; decide +kernel
      have hl : raw32822step1Labels = raw32822step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32822step0 raw32822step0Labels permutation44 permutation4
    mixedMoment B raw32822step1 raw32822step1Labels = mixedMoment B raw32822step2 raw32822step2Labels := by
      have ha : raw32822step2 = -raw32822step1 := by apply Matrix.ext; change ∀ i j, raw32822step2 i j = -(raw32822step1 i j); unfold raw32822step2 raw32822step1; decide +kernel
      have hl : raw32822step2Labels = raw32822step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32822step2 raw32822step2Labels = mixedMoment B raw32822step3 raw32822step3Labels := by
      have ha : raw32822step3 = raw32822step2 := by apply Matrix.ext; unfold raw32822step3 raw32822step2; decide +kernel
      have hl : raw32822step2Labels = labelEmbedding7 ∘ raw32822step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32822step2 raw32822step2Labels raw32822step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

theorem canonical32824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32824 raw32824Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw32824 raw32824Labels = mixedMoment B raw32824step0 raw32824step0Labels := by
      have hz : ∀ j, raw32824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32824step0 = (fun i j => raw32824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32824step0 raw32824; decide +kernel
      have hl : raw32824step0Labels = raw32824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32824 raw32824Labels permutation346 hz
    mixedMoment B raw32824step0 raw32824step0Labels = mixedMoment B raw32824step1 raw32824step1Labels := by
      have ha : raw32824step1 = (fun i j => raw32824step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32824step1 raw32824step0; decide +kernel
      have hl : raw32824step1Labels = raw32824step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32824step0 raw32824step0Labels permutation34 permutation6
    mixedMoment B raw32824step1 raw32824step1Labels = mixedMoment B raw32824step2 raw32824step2Labels := by
      have ha : raw32824step2 = raw32824step1 := by apply Matrix.ext; unfold raw32824step2 raw32824step1; decide +kernel
      have hl : raw32824step1Labels = labelEmbedding9 ∘ raw32824step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32824step1 raw32824step1Labels raw32824step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

theorem canonical32835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32835 raw32835Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw32835 raw32835Labels = mixedMoment B raw32835step0 raw32835step0Labels := by
      have hz : ∀ j, raw32835 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32835step0 = (fun i j => raw32835 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32835step0 raw32835; decide +kernel
      have hl : raw32835step0Labels = raw32835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32835 raw32835Labels permutation346 hz
    mixedMoment B raw32835step0 raw32835step0Labels = mixedMoment B raw32835step1 raw32835step1Labels := by
      have ha : raw32835step1 = (fun i j => raw32835step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32835step1 raw32835step0; decide +kernel
      have hl : raw32835step1Labels = raw32835step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32835step0 raw32835step0Labels permutation34 permutation6
    mixedMoment B raw32835step1 raw32835step1Labels = mixedMoment B raw32835step2 raw32835step2Labels := by
      have ha : raw32835step2 = raw32835step1 := by apply Matrix.ext; unfold raw32835step2 raw32835step1; decide +kernel
      have hl : raw32835step1Labels = labelEmbedding9 ∘ raw32835step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32835step1 raw32835step1Labels raw32835step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4834 node4834Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical257
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32999 raw32999Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw32999 raw32999Labels = mixedMoment B raw32999step0 raw32999step0Labels := by
      have ha : raw32999step0 = (fun i j => raw32999 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32999step0 raw32999; decide +kernel
      have hl : raw32999step0Labels = raw32999Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32999 raw32999Labels permutation188 permutation4
    mixedMoment B raw32999step0 raw32999step0Labels = mixedMoment B raw32999step1 raw32999step1Labels := by
      have ha : raw32999step1 = -raw32999step0 := by apply Matrix.ext; change ∀ i j, raw32999step1 i j = -(raw32999step0 i j); unfold raw32999step1 raw32999step0; decide +kernel
      have hl : raw32999step1Labels = raw32999step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32999step1 raw32999step1Labels = mixedMoment B raw32999step2 raw32999step2Labels := by
      have ha : raw32999step2 = raw32999step1 := by apply Matrix.ext; unfold raw32999step2 raw32999step1; decide +kernel
      have hl : raw32999step1Labels = labelEmbedding7 ∘ raw32999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32999step1 raw32999step1Labels raw32999step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical33001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33001 raw33001Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw33001 raw33001Labels = mixedMoment B raw33001step0 raw33001step0Labels := by
      have ha : raw33001step0 = (fun i j => raw33001 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33001step0 raw33001; decide +kernel
      have hl : raw33001step0Labels = raw33001Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33001 raw33001Labels permutation152 permutation6
    mixedMoment B raw33001step0 raw33001step0Labels = mixedMoment B raw33001step1 raw33001step1Labels := by
      have ha : raw33001step1 = raw33001step0 := by apply Matrix.ext; unfold raw33001step1 raw33001step0; decide +kernel
      have hl : raw33001step0Labels = labelEmbedding9 ∘ raw33001step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33001step0 raw33001step0Labels raw33001step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5184 node5184Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical262
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33567 raw33567Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw33567 raw33567Labels = mixedMoment B raw33567step0 raw33567step0Labels := by
      have hz : ∀ j, raw33567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33567step0 = (fun i j => raw33567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33567step0 raw33567; decide +kernel
      have hl : raw33567step0Labels = raw33567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33567 raw33567Labels permutation346 hz
    mixedMoment B raw33567step0 raw33567step0Labels = mixedMoment B raw33567step1 raw33567step1Labels := by
      have ha : raw33567step1 = (fun i j => raw33567step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33567step1 raw33567step0; decide +kernel
      have hl : raw33567step1Labels = raw33567step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33567step0 raw33567step0Labels permutation32 permutation6
    mixedMoment B raw33567step1 raw33567step1Labels = mixedMoment B raw33567step2 raw33567step2Labels := by
      have ha : raw33567step2 = raw33567step1 := by apply Matrix.ext; unfold raw33567step2 raw33567step1; decide +kernel
      have hl : raw33567step1Labels = labelEmbedding9 ∘ raw33567step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33567step1 raw33567step1Labels raw33567step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical33568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33568 raw33568Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw33568 raw33568Labels = mixedMoment B raw33568step0 raw33568step0Labels := by
      have hz : ∀ j, raw33568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33568step0 = (fun i j => raw33568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33568step0 raw33568; decide +kernel
      have hl : raw33568step0Labels = raw33568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33568 raw33568Labels permutation346 hz
    mixedMoment B raw33568step0 raw33568step0Labels = mixedMoment B raw33568step1 raw33568step1Labels := by
      have ha : raw33568step1 = (fun i j => raw33568step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33568step1 raw33568step0; decide +kernel
      have hl : raw33568step1Labels = raw33568step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33568step0 raw33568step0Labels permutation34 permutation6
    mixedMoment B raw33568step1 raw33568step1Labels = mixedMoment B raw33568step2 raw33568step2Labels := by
      have ha : raw33568step2 = raw33568step1 := by apply Matrix.ext; unfold raw33568step2 raw33568step1; decide +kernel
      have hl : raw33568step1Labels = labelEmbedding9 ∘ raw33568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33568step1 raw33568step1Labels raw33568step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical33644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33644 raw33644Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw33644 raw33644Labels = mixedMoment B raw33644step0 raw33644step0Labels := by
      have hz : ∀ j, raw33644 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33644step0 = (fun i j => raw33644 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33644step0 raw33644; decide +kernel
      have hl : raw33644step0Labels = raw33644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33644 raw33644Labels permutation346 hz
    mixedMoment B raw33644step0 raw33644step0Labels = mixedMoment B raw33644step1 raw33644step1Labels := by
      have ha : raw33644step1 = (fun i j => raw33644step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33644step1 raw33644step0; decide +kernel
      have hl : raw33644step1Labels = raw33644step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33644step0 raw33644step0Labels permutation32 permutation6
    mixedMoment B raw33644step1 raw33644step1Labels = mixedMoment B raw33644step2 raw33644step2Labels := by
      have ha : raw33644step2 = raw33644step1 := by apply Matrix.ext; unfold raw33644step2 raw33644step1; decide +kernel
      have hl : raw33644step1Labels = labelEmbedding9 ∘ raw33644step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33644step1 raw33644step1Labels raw33644step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

theorem canonical33652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33652 raw33652Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw33652 raw33652Labels = mixedMoment B raw33652step0 raw33652step0Labels := by
      have hz : ∀ j, raw33652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33652step0 = (fun i j => raw33652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33652step0 raw33652; decide +kernel
      have hl : raw33652step0Labels = raw33652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33652 raw33652Labels permutation346 hz
    mixedMoment B raw33652step0 raw33652step0Labels = mixedMoment B raw33652step1 raw33652step1Labels := by
      have ha : raw33652step1 = (fun i j => raw33652step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33652step1 raw33652step0; decide +kernel
      have hl : raw33652step1Labels = raw33652step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33652step0 raw33652step0Labels permutation44 permutation4
    mixedMoment B raw33652step1 raw33652step1Labels = mixedMoment B raw33652step2 raw33652step2Labels := by
      have ha : raw33652step2 = -raw33652step1 := by apply Matrix.ext; change ∀ i j, raw33652step2 i j = -(raw33652step1 i j); unfold raw33652step2 raw33652step1; decide +kernel
      have hl : raw33652step2Labels = raw33652step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33652step2 raw33652step2Labels = mixedMoment B raw33652step3 raw33652step3Labels := by
      have ha : raw33652step3 = raw33652step2 := by apply Matrix.ext; unfold raw33652step3 raw33652step2; decide +kernel
      have hl : raw33652step2Labels = labelEmbedding7 ∘ raw33652step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33652step2 raw33652step2Labels raw33652step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical263
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33766 raw33766Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw33766 raw33766Labels = mixedMoment B raw33766step0 raw33766step0Labels := by
      have hz : ∀ j, raw33766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33766step0 = (fun i j => raw33766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33766step0 raw33766; decide +kernel
      have hl : raw33766step0Labels = raw33766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33766 raw33766Labels permutation346 hz
    mixedMoment B raw33766step0 raw33766step0Labels = mixedMoment B raw33766step1 raw33766step1Labels := by
      have ha : raw33766step1 = (fun i j => raw33766step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33766step1 raw33766step0; decide +kernel
      have hl : raw33766step1Labels = raw33766step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33766step0 raw33766step0Labels permutation32 permutation6
    mixedMoment B raw33766step1 raw33766step1Labels = mixedMoment B raw33766step2 raw33766step2Labels := by
      have ha : raw33766step2 = raw33766step1 := by apply Matrix.ext; unfold raw33766step2 raw33766step1; decide +kernel
      have hl : raw33766step1Labels = labelEmbedding9 ∘ raw33766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33766step1 raw33766step1Labels raw33766step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

theorem canonical33767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33767 raw33767Labels = mixedMoment B node4443 node4443Labels := by
  calc
    mixedMoment B raw33767 raw33767Labels = mixedMoment B raw33767step0 raw33767step0Labels := by
      have hz : ∀ j, raw33767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33767step0 = (fun i j => raw33767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33767step0 raw33767; decide +kernel
      have hl : raw33767step0Labels = raw33767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33767 raw33767Labels permutation346 hz
    mixedMoment B raw33767step0 raw33767step0Labels = mixedMoment B raw33767step1 raw33767step1Labels := by
      have ha : raw33767step1 = (fun i j => raw33767step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33767step1 raw33767step0; decide +kernel
      have hl : raw33767step1Labels = raw33767step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33767step0 raw33767step0Labels permutation40 permutation4
    mixedMoment B raw33767step1 raw33767step1Labels = mixedMoment B raw33767step2 raw33767step2Labels := by
      have ha : raw33767step2 = -raw33767step1 := by apply Matrix.ext; change ∀ i j, raw33767step2 i j = -(raw33767step1 i j); unfold raw33767step2 raw33767step1; decide +kernel
      have hl : raw33767step2Labels = raw33767step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33767step2 raw33767step2Labels = mixedMoment B raw33767step3 raw33767step3Labels := by
      have ha : raw33767step3 = raw33767step2 := by apply Matrix.ext; unfold raw33767step3 raw33767step2; decide +kernel
      have hl : raw33767step2Labels = labelEmbedding7 ∘ raw33767step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33767step2 raw33767step2Labels raw33767step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4443 node4443Labels := by rfl

theorem canonical33768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33768 raw33768Labels = mixedMoment B node4794 node4794Labels := by
  calc
    mixedMoment B raw33768 raw33768Labels = mixedMoment B raw33768step0 raw33768step0Labels := by
      have ha : raw33768step0 = (fun i j => raw33768 (permutation184 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33768step0 raw33768; decide +kernel
      have hl : raw33768step0Labels = raw33768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33768 raw33768Labels permutation184 permutation4
    mixedMoment B raw33768step0 raw33768step0Labels = mixedMoment B raw33768step1 raw33768step1Labels := by
      have ha : raw33768step1 = -raw33768step0 := by apply Matrix.ext; change ∀ i j, raw33768step1 i j = -(raw33768step0 i j); unfold raw33768step1 raw33768step0; decide +kernel
      have hl : raw33768step1Labels = raw33768step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33768step1 raw33768step1Labels = mixedMoment B raw33768step2 raw33768step2Labels := by
      have ha : raw33768step2 = raw33768step1 := by apply Matrix.ext; unfold raw33768step2 raw33768step1; decide +kernel
      have hl : raw33768step1Labels = labelEmbedding7 ∘ raw33768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33768step1 raw33768step1Labels raw33768step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4794 node4794Labels := by rfl

theorem canonical33769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33769 raw33769Labels = mixedMoment B node4855 node4855Labels := by
  calc
    mixedMoment B raw33769 raw33769Labels = mixedMoment B raw33769step0 raw33769step0Labels := by
      have hz : ∀ j, raw33769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33769step0 = (fun i j => raw33769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33769step0 raw33769; decide +kernel
      have hl : raw33769step0Labels = raw33769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33769 raw33769Labels permutation346 hz
    mixedMoment B raw33769step0 raw33769step0Labels = mixedMoment B raw33769step1 raw33769step1Labels := by
      have ha : raw33769step1 = (fun i j => raw33769step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33769step1 raw33769step0; decide +kernel
      have hl : raw33769step1Labels = raw33769step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33769step0 raw33769step0Labels permutation40 permutation4
    mixedMoment B raw33769step1 raw33769step1Labels = mixedMoment B raw33769step2 raw33769step2Labels := by
      have ha : raw33769step2 = -raw33769step1 := by apply Matrix.ext; change ∀ i j, raw33769step2 i j = -(raw33769step1 i j); unfold raw33769step2 raw33769step1; decide +kernel
      have hl : raw33769step2Labels = raw33769step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33769step2 raw33769step2Labels = mixedMoment B raw33769step3 raw33769step3Labels := by
      have ha : raw33769step3 = raw33769step2 := by apply Matrix.ext; unfold raw33769step3 raw33769step2; decide +kernel
      have hl : raw33769step2Labels = labelEmbedding7 ∘ raw33769step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33769step2 raw33769step2Labels raw33769step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4855 node4855Labels := by rfl

theorem canonical33770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33770 raw33770Labels = mixedMoment B node4855 node4855Labels := by
  calc
    mixedMoment B raw33770 raw33770Labels = mixedMoment B raw33770step0 raw33770step0Labels := by
      have hz : ∀ j, raw33770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33770step0 = (fun i j => raw33770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33770step0 raw33770; decide +kernel
      have hl : raw33770step0Labels = raw33770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33770 raw33770Labels permutation346 hz
    mixedMoment B raw33770step0 raw33770step0Labels = mixedMoment B raw33770step1 raw33770step1Labels := by
      have ha : raw33770step1 = (fun i j => raw33770step0 (permutation46 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33770step1 raw33770step0; decide +kernel
      have hl : raw33770step1Labels = raw33770step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33770step0 raw33770step0Labels permutation46 permutation4
    mixedMoment B raw33770step1 raw33770step1Labels = mixedMoment B raw33770step2 raw33770step2Labels := by
      have ha : raw33770step2 = -raw33770step1 := by apply Matrix.ext; change ∀ i j, raw33770step2 i j = -(raw33770step1 i j); unfold raw33770step2 raw33770step1; decide +kernel
      have hl : raw33770step2Labels = raw33770step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33770step2 raw33770step2Labels = mixedMoment B raw33770step3 raw33770step3Labels := by
      have ha : raw33770step3 = raw33770step2 := by apply Matrix.ext; unfold raw33770step3 raw33770step2; decide +kernel
      have hl : raw33770step2Labels = labelEmbedding7 ∘ raw33770step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33770step2 raw33770step2Labels raw33770step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4855 node4855Labels := by rfl

theorem canonical33771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33771 raw33771Labels = mixedMoment B node4435 node4435Labels := by
  calc
    mixedMoment B raw33771 raw33771Labels = mixedMoment B raw33771step0 raw33771step0Labels := by
      have ha : raw33771step0 = (fun i j => raw33771 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33771step0 raw33771; decide +kernel
      have hl : raw33771step0Labels = raw33771Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33771 raw33771Labels permutation212 permutation4
    mixedMoment B raw33771step0 raw33771step0Labels = mixedMoment B raw33771step1 raw33771step1Labels := by
      have ha : raw33771step1 = -raw33771step0 := by apply Matrix.ext; change ∀ i j, raw33771step1 i j = -(raw33771step0 i j); unfold raw33771step1 raw33771step0; decide +kernel
      have hl : raw33771step1Labels = raw33771step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33771step1 raw33771step1Labels = mixedMoment B raw33771step2 raw33771step2Labels := by
      have ha : raw33771step2 = raw33771step1 := by apply Matrix.ext; unfold raw33771step2 raw33771step1; decide +kernel
      have hl : raw33771step1Labels = labelEmbedding7 ∘ raw33771step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33771step1 raw33771step1Labels raw33771step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4435 node4435Labels := by rfl

theorem canonical33772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33772 raw33772Labels = mixedMoment B node4848 node4848Labels := by
  calc
    mixedMoment B raw33772 raw33772Labels = mixedMoment B raw33772step0 raw33772step0Labels := by
      have ha : raw33772step0 = (fun i j => raw33772 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33772step0 raw33772; decide +kernel
      have hl : raw33772step0Labels = raw33772Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33772 raw33772Labels permutation212 permutation4
    mixedMoment B raw33772step0 raw33772step0Labels = mixedMoment B raw33772step1 raw33772step1Labels := by
      have ha : raw33772step1 = -raw33772step0 := by apply Matrix.ext; change ∀ i j, raw33772step1 i j = -(raw33772step0 i j); unfold raw33772step1 raw33772step0; decide +kernel
      have hl : raw33772step1Labels = raw33772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33772step1 raw33772step1Labels = mixedMoment B raw33772step2 raw33772step2Labels := by
      have ha : raw33772step2 = raw33772step1 := by apply Matrix.ext; unfold raw33772step2 raw33772step1; decide +kernel
      have hl : raw33772step1Labels = labelEmbedding7 ∘ raw33772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33772step1 raw33772step1Labels raw33772step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4848 node4848Labels := by rfl

theorem canonical33773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33773 raw33773Labels = mixedMoment B node4848 node4848Labels := by
  calc
    mixedMoment B raw33773 raw33773Labels = mixedMoment B raw33773step0 raw33773step0Labels := by
      have ha : raw33773step0 = (fun i j => raw33773 (permutation234 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33773step0 raw33773; decide +kernel
      have hl : raw33773step0Labels = raw33773Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33773 raw33773Labels permutation234 permutation4
    mixedMoment B raw33773step0 raw33773step0Labels = mixedMoment B raw33773step1 raw33773step1Labels := by
      have ha : raw33773step1 = -raw33773step0 := by apply Matrix.ext; change ∀ i j, raw33773step1 i j = -(raw33773step0 i j); unfold raw33773step1 raw33773step0; decide +kernel
      have hl : raw33773step1Labels = raw33773step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33773step1 raw33773step1Labels = mixedMoment B raw33773step2 raw33773step2Labels := by
      have ha : raw33773step2 = raw33773step1 := by apply Matrix.ext; unfold raw33773step2 raw33773step1; decide +kernel
      have hl : raw33773step1Labels = labelEmbedding7 ∘ raw33773step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33773step1 raw33773step1Labels raw33773step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4848 node4848Labels := by rfl

theorem canonical33774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33774 raw33774Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw33774 raw33774Labels = mixedMoment B raw33774step0 raw33774step0Labels := by
      have hz : ∀ j, raw33774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33774step0 = (fun i j => raw33774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33774step0 raw33774; decide +kernel
      have hl : raw33774step0Labels = raw33774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33774 raw33774Labels permutation346 hz
    mixedMoment B raw33774step0 raw33774step0Labels = mixedMoment B raw33774step1 raw33774step1Labels := by
      have ha : raw33774step1 = (fun i j => raw33774step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33774step1 raw33774step0; decide +kernel
      have hl : raw33774step1Labels = raw33774step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33774step0 raw33774step0Labels permutation38 permutation4
    mixedMoment B raw33774step1 raw33774step1Labels = mixedMoment B raw33774step2 raw33774step2Labels := by
      have ha : raw33774step2 = -raw33774step1 := by apply Matrix.ext; change ∀ i j, raw33774step2 i j = -(raw33774step1 i j); unfold raw33774step2 raw33774step1; decide +kernel
      have hl : raw33774step2Labels = raw33774step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33774step2 raw33774step2Labels = mixedMoment B raw33774step3 raw33774step3Labels := by
      have ha : raw33774step3 = raw33774step2 := by apply Matrix.ext; unfold raw33774step3 raw33774step2; decide +kernel
      have hl : raw33774step2Labels = labelEmbedding7 ∘ raw33774step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33774step2 raw33774step2Labels raw33774step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

theorem canonical33775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33775 raw33775Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw33775 raw33775Labels = mixedMoment B raw33775step0 raw33775step0Labels := by
      have hz : ∀ j, raw33775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33775step0 = (fun i j => raw33775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33775step0 raw33775; decide +kernel
      have hl : raw33775step0Labels = raw33775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33775 raw33775Labels permutation346 hz
    mixedMoment B raw33775step0 raw33775step0Labels = mixedMoment B raw33775step1 raw33775step1Labels := by
      have ha : raw33775step1 = (fun i j => raw33775step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33775step1 raw33775step0; decide +kernel
      have hl : raw33775step1Labels = raw33775step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33775step0 raw33775step0Labels permutation32 permutation6
    mixedMoment B raw33775step1 raw33775step1Labels = mixedMoment B raw33775step2 raw33775step2Labels := by
      have ha : raw33775step2 = raw33775step1 := by apply Matrix.ext; unfold raw33775step2 raw33775step1; decide +kernel
      have hl : raw33775step1Labels = labelEmbedding9 ∘ raw33775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33775step1 raw33775step1Labels raw33775step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4834 node4834Labels := by rfl

theorem canonical33776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33776 raw33776Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw33776 raw33776Labels = mixedMoment B raw33776step0 raw33776step0Labels := by
      have ha : raw33776step0 = (fun i j => raw33776 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33776step0 raw33776; decide +kernel
      have hl : raw33776step0Labels = raw33776Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33776 raw33776Labels permutation182 permutation4
    mixedMoment B raw33776step0 raw33776step0Labels = mixedMoment B raw33776step1 raw33776step1Labels := by
      have ha : raw33776step1 = -raw33776step0 := by apply Matrix.ext; change ∀ i j, raw33776step1 i j = -(raw33776step0 i j); unfold raw33776step1 raw33776step0; decide +kernel
      have hl : raw33776step1Labels = raw33776step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33776step1 raw33776step1Labels = mixedMoment B raw33776step2 raw33776step2Labels := by
      have ha : raw33776step2 = raw33776step1 := by apply Matrix.ext; unfold raw33776step2 raw33776step1; decide +kernel
      have hl : raw33776step1Labels = labelEmbedding7 ∘ raw33776step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33776step1 raw33776step1Labels raw33776step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical33777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33777 raw33777Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw33777 raw33777Labels = mixedMoment B raw33777step0 raw33777step0Labels := by
      have hz : ∀ j, raw33777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33777step0 = (fun i j => raw33777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33777step0 raw33777; decide +kernel
      have hl : raw33777step0Labels = raw33777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33777 raw33777Labels permutation346 hz
    mixedMoment B raw33777step0 raw33777step0Labels = mixedMoment B raw33777step1 raw33777step1Labels := by
      have ha : raw33777step1 = (fun i j => raw33777step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33777step1 raw33777step0; decide +kernel
      have hl : raw33777step1Labels = raw33777step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33777step0 raw33777step0Labels permutation38 permutation4
    mixedMoment B raw33777step1 raw33777step1Labels = mixedMoment B raw33777step2 raw33777step2Labels := by
      have ha : raw33777step2 = -raw33777step1 := by apply Matrix.ext; change ∀ i j, raw33777step2 i j = -(raw33777step1 i j); unfold raw33777step2 raw33777step1; decide +kernel
      have hl : raw33777step2Labels = raw33777step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33777step2 raw33777step2Labels = mixedMoment B raw33777step3 raw33777step3Labels := by
      have ha : raw33777step3 = raw33777step2 := by apply Matrix.ext; unfold raw33777step3 raw33777step2; decide +kernel
      have hl : raw33777step2Labels = labelEmbedding7 ∘ raw33777step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33777step2 raw33777step2Labels raw33777step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

theorem canonical33778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33778 raw33778Labels = mixedMoment B node4437 node4437Labels := by
  calc
    mixedMoment B raw33778 raw33778Labels = mixedMoment B raw33778step0 raw33778step0Labels := by
      have hz : ∀ j, raw33778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33778step0 = (fun i j => raw33778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33778step0 raw33778; decide +kernel
      have hl : raw33778step0Labels = raw33778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33778 raw33778Labels permutation346 hz
    mixedMoment B raw33778step0 raw33778step0Labels = mixedMoment B raw33778step1 raw33778step1Labels := by
      have ha : raw33778step1 = (fun i j => raw33778step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33778step1 raw33778step0; decide +kernel
      have hl : raw33778step1Labels = raw33778step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33778step0 raw33778step0Labels permutation40 permutation4
    mixedMoment B raw33778step1 raw33778step1Labels = mixedMoment B raw33778step2 raw33778step2Labels := by
      have ha : raw33778step2 = -raw33778step1 := by apply Matrix.ext; change ∀ i j, raw33778step2 i j = -(raw33778step1 i j); unfold raw33778step2 raw33778step1; decide +kernel
      have hl : raw33778step2Labels = raw33778step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33778step2 raw33778step2Labels = mixedMoment B raw33778step3 raw33778step3Labels := by
      have ha : raw33778step3 = raw33778step2 := by apply Matrix.ext; unfold raw33778step3 raw33778step2; decide +kernel
      have hl : raw33778step2Labels = labelEmbedding7 ∘ raw33778step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33778step2 raw33778step2Labels raw33778step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4437 node4437Labels := by rfl

theorem canonical33779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33779 raw33779Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw33779 raw33779Labels = mixedMoment B raw33779step0 raw33779step0Labels := by
      have hz : ∀ j, raw33779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33779step0 = (fun i j => raw33779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33779step0 raw33779; decide +kernel
      have hl : raw33779step0Labels = raw33779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33779 raw33779Labels permutation346 hz
    mixedMoment B raw33779step0 raw33779step0Labels = mixedMoment B raw33779step1 raw33779step1Labels := by
      have ha : raw33779step1 = (fun i j => raw33779step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33779step1 raw33779step0; decide +kernel
      have hl : raw33779step1Labels = raw33779step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33779step0 raw33779step0Labels permutation32 permutation6
    mixedMoment B raw33779step1 raw33779step1Labels = mixedMoment B raw33779step2 raw33779step2Labels := by
      have ha : raw33779step2 = raw33779step1 := by apply Matrix.ext; unfold raw33779step2 raw33779step1; decide +kernel
      have hl : raw33779step1Labels = labelEmbedding9 ∘ raw33779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33779step1 raw33779step1Labels raw33779step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

theorem canonical33780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33780 raw33780Labels = mixedMoment B node4791 node4791Labels := by
  calc
    mixedMoment B raw33780 raw33780Labels = mixedMoment B raw33780step0 raw33780step0Labels := by
      have ha : raw33780step0 = (fun i j => raw33780 (permutation184 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33780step0 raw33780; decide +kernel
      have hl : raw33780step0Labels = raw33780Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33780 raw33780Labels permutation184 permutation4
    mixedMoment B raw33780step0 raw33780step0Labels = mixedMoment B raw33780step1 raw33780step1Labels := by
      have ha : raw33780step1 = -raw33780step0 := by apply Matrix.ext; change ∀ i j, raw33780step1 i j = -(raw33780step0 i j); unfold raw33780step1 raw33780step0; decide +kernel
      have hl : raw33780step1Labels = raw33780step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33780step1 raw33780step1Labels = mixedMoment B raw33780step2 raw33780step2Labels := by
      have ha : raw33780step2 = raw33780step1 := by apply Matrix.ext; unfold raw33780step2 raw33780step1; decide +kernel
      have hl : raw33780step1Labels = labelEmbedding7 ∘ raw33780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33780step1 raw33780step1Labels raw33780step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4791 node4791Labels := by rfl

theorem canonical33781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33781 raw33781Labels = mixedMoment B node4850 node4850Labels := by
  calc
    mixedMoment B raw33781 raw33781Labels = mixedMoment B raw33781step0 raw33781step0Labels := by
      have hz : ∀ j, raw33781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33781step0 = (fun i j => raw33781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33781step0 raw33781; decide +kernel
      have hl : raw33781step0Labels = raw33781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33781 raw33781Labels permutation346 hz
    mixedMoment B raw33781step0 raw33781step0Labels = mixedMoment B raw33781step1 raw33781step1Labels := by
      have ha : raw33781step1 = (fun i j => raw33781step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33781step1 raw33781step0; decide +kernel
      have hl : raw33781step1Labels = raw33781step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33781step0 raw33781step0Labels permutation40 permutation4
    mixedMoment B raw33781step1 raw33781step1Labels = mixedMoment B raw33781step2 raw33781step2Labels := by
      have ha : raw33781step2 = -raw33781step1 := by apply Matrix.ext; change ∀ i j, raw33781step2 i j = -(raw33781step1 i j); unfold raw33781step2 raw33781step1; decide +kernel
      have hl : raw33781step2Labels = raw33781step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33781step2 raw33781step2Labels = mixedMoment B raw33781step3 raw33781step3Labels := by
      have ha : raw33781step3 = raw33781step2 := by apply Matrix.ext; unfold raw33781step3 raw33781step2; decide +kernel
      have hl : raw33781step2Labels = labelEmbedding7 ∘ raw33781step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33781step2 raw33781step2Labels raw33781step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4850 node4850Labels := by rfl

theorem canonical33782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33782 raw33782Labels = mixedMoment B node4850 node4850Labels := by
  calc
    mixedMoment B raw33782 raw33782Labels = mixedMoment B raw33782step0 raw33782step0Labels := by
      have hz : ∀ j, raw33782 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33782step0 = (fun i j => raw33782 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33782step0 raw33782; decide +kernel
      have hl : raw33782step0Labels = raw33782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33782 raw33782Labels permutation346 hz
    mixedMoment B raw33782step0 raw33782step0Labels = mixedMoment B raw33782step1 raw33782step1Labels := by
      have ha : raw33782step1 = (fun i j => raw33782step0 (permutation46 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33782step1 raw33782step0; decide +kernel
      have hl : raw33782step1Labels = raw33782step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33782step0 raw33782step0Labels permutation46 permutation4
    mixedMoment B raw33782step1 raw33782step1Labels = mixedMoment B raw33782step2 raw33782step2Labels := by
      have ha : raw33782step2 = -raw33782step1 := by apply Matrix.ext; change ∀ i j, raw33782step2 i j = -(raw33782step1 i j); unfold raw33782step2 raw33782step1; decide +kernel
      have hl : raw33782step2Labels = raw33782step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33782step2 raw33782step2Labels = mixedMoment B raw33782step3 raw33782step3Labels := by
      have ha : raw33782step3 = raw33782step2 := by apply Matrix.ext; unfold raw33782step3 raw33782step2; decide +kernel
      have hl : raw33782step2Labels = labelEmbedding7 ∘ raw33782step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33782step2 raw33782step2Labels raw33782step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4850 node4850Labels := by rfl

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

theorem canonical1248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1248 raw1248Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw1248 raw1248Labels = mixedMoment B raw1248step0 raw1248step0Labels := by
      have ha : raw1248step0 = (fun i j => raw1248 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1248step0 raw1248; decide +kernel
      have hl : raw1248step0Labels = raw1248Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1248 raw1248Labels permutation32 permutation4
    mixedMoment B raw1248step0 raw1248step0Labels = mixedMoment B raw1248step1 raw1248step1Labels := by
      have ha : raw1248step1 = raw1248step0 := by apply Matrix.ext; unfold raw1248step1 raw1248step0; decide +kernel
      have hl : raw1248step0Labels = labelEmbedding7 ∘ raw1248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1248step0 raw1248step0Labels raw1248step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

theorem canonical1249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1249 raw1249Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw1249 raw1249Labels = mixedMoment B raw1249step0 raw1249step0Labels := by
      have ha : raw1249step0 = (fun i j => raw1249 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1249step0 raw1249; decide +kernel
      have hl : raw1249step0Labels = raw1249Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1249 raw1249Labels permutation32 permutation4
    _ = mixedMoment B node1035 node1035Labels := by rfl

theorem canonical1250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1250 raw1250Labels = mixedMoment B node1645 node1645Labels := by
  calc
    mixedMoment B raw1250 raw1250Labels = mixedMoment B raw1250step0 raw1250step0Labels := by
      have ha : raw1250step0 = (fun i j => raw1250 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1250step0 raw1250; decide +kernel
      have hl : raw1250step0Labels = raw1250Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1250 raw1250Labels permutation38 permutation6
    mixedMoment B raw1250step0 raw1250step0Labels = mixedMoment B raw1250step1 raw1250step1Labels := by
      have ha : raw1250step1 = -raw1250step0 := by apply Matrix.ext; change ∀ i j, raw1250step1 i j = -(raw1250step0 i j); unfold raw1250step1 raw1250step0; decide +kernel
      have hl : raw1250step1Labels = raw1250step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1250step1 raw1250step1Labels = mixedMoment B raw1250step2 raw1250step2Labels := by
      have ha : raw1250step2 = raw1250step1 := by apply Matrix.ext; unfold raw1250step2 raw1250step1; decide +kernel
      have hl : raw1250step1Labels = labelEmbedding1 ∘ raw1250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1250step1 raw1250step1Labels raw1250step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1645 node1645Labels := by rfl

end MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4452 node4452Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1035 node1035Labels + mixedMoment B node1645 node1645Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1248 singletonSmall4452
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4452) = raw1248Labels := by decide +kernel
  rw [hl, canonical1248 B hB] at h
  have hc0 : mixedMoment B raw1248 (Fin.cases (0 : Fin 2) singletonSmall4452) =
      mixedMoment B node1035 node1035Labels := by
    have ha : raw1248 = raw1249 := by apply Matrix.ext; unfold raw1248 raw1249; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4452 = raw1249Labels := by decide +kernel
    rw [ha, hj, canonical1249 B hB]
  have hc1 : mixedMoment B raw1248 (Fin.cases (1 : Fin 2) singletonSmall4452) =
      mixedMoment B node1645 node1645Labels := by
    have ha : raw1248 = raw1250 := by apply Matrix.ext; unfold raw1248 raw1250; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4452 = raw1250Labels := by decide +kernel
    rw [ha, hj, canonical1250 B hB]
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

theorem singleton4798 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4798 node4798Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2016 node2016Labels + mixedMoment B node2075 node2075Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1725 singletonSmall4798
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4798) = raw1725Labels := by decide +kernel
  rw [hl, canonical1725 B hB] at h
  have hc0 : mixedMoment B raw1725 (Fin.cases (0 : Fin 2) singletonSmall4798) =
      mixedMoment B node2016 node2016Labels := by
    have ha : raw1725 = raw1726 := by apply Matrix.ext; unfold raw1725 raw1726; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4798 = raw1726Labels := by decide +kernel
    rw [ha, hj, canonical1726 B hB]
  have hc1 : mixedMoment B raw1725 (Fin.cases (1 : Fin 2) singletonSmall4798) =
      mixedMoment B node2075 node2075Labels := by
    have ha : raw1725 = raw1727 := by apply Matrix.ext; unfold raw1725 raw1727; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4798 = raw1727Labels := by decide +kernel
    rw [ha, hj, canonical1727 B hB]
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

theorem singleton4832 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4832 node4832Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2052 node2052Labels + mixedMoment B node2193 node2193Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1764 singletonSmall4832
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4832) = raw1764Labels := by decide +kernel
  rw [hl, canonical1764 B hB] at h
  have hc0 : mixedMoment B raw1764 (Fin.cases (0 : Fin 2) singletonSmall4832) =
      mixedMoment B node2052 node2052Labels := by
    have ha : raw1764 = raw1765 := by apply Matrix.ext; unfold raw1764 raw1765; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4832 = raw1765Labels := by decide +kernel
    rw [ha, hj, canonical1765 B hB]
  have hc1 : mixedMoment B raw1764 (Fin.cases (1 : Fin 2) singletonSmall4832) =
      mixedMoment B node2193 node2193Labels := by
    have ha : raw1764 = raw1766 := by apply Matrix.ext; unfold raw1764 raw1766; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4832 = raw1766Labels := by decide +kernel
    rw [ha, hj, canonical1766 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4860 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4860 node4860Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2101 node2101Labels + mixedMoment B node2101 node2101Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1782 singletonSmall4860
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4860) = raw1782Labels := by decide +kernel
  rw [hl, canonical1782 B hB] at h
  have hc0 : mixedMoment B raw1782 (Fin.cases (0 : Fin 2) singletonSmall4860) =
      mixedMoment B node2101 node2101Labels := by
    have ha : raw1782 = raw1783 := by apply Matrix.ext; unfold raw1782 raw1783; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4860 = raw1783Labels := by decide +kernel
    rw [ha, hj, canonical1783 B hB]
  have hc1 : mixedMoment B raw1782 (Fin.cases (1 : Fin 2) singletonSmall4860) =
      mixedMoment B node2101 node2101Labels := by
    have ha : raw1782 = raw1784 := by apply Matrix.ext; unfold raw1782 raw1784; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4860 = raw1784Labels := by decide +kernel
    rw [ha, hj, canonical1784 B hB]
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

theorem singleton5203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5203 node5203Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2884 node2884Labels + mixedMoment B node3621 node3621Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2229 singletonSmall5203
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5203) = raw2229Labels := by decide +kernel
  rw [hl, canonical2229 B hB] at h
  have hc0 : mixedMoment B raw2229 (Fin.cases (0 : Fin 2) singletonSmall5203) =
      mixedMoment B node2884 node2884Labels := by
    have ha : raw2229 = raw2230 := by apply Matrix.ext; unfold raw2229 raw2230; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5203 = raw2230Labels := by decide +kernel
    rw [ha, hj, canonical2230 B hB]
  have hc1 : mixedMoment B raw2229 (Fin.cases (1 : Fin 2) singletonSmall5203) =
      mixedMoment B node3621 node3621Labels := by
    have ha : raw2229 = raw2231 := by apply Matrix.ext; unfold raw2229 raw2231; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5203 = raw2231Labels := by decide +kernel
    rw [ha, hj, canonical2231 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound1035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1035 node1035Labels = Sparse.eval nodeValue1035 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1035) = mixedMoment B node1035 node1035Labels := rfl
  simpa [nodeValue1035, Sparse.eval] using hc.symm

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

theorem sound1645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1645 node1645Labels = Sparse.eval nodeValue1645 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1645) = mixedMoment B node1645 node1645Labels := rfl
  simpa [nodeValue1645, Sparse.eval] using hc.symm

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

theorem sound2016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2016 node2016Labels = Sparse.eval nodeValue2016 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2016) = mixedMoment B node2016 node2016Labels := rfl
  simpa [nodeValue2016, Sparse.eval] using hc.symm

theorem sound2019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2019 node2019Labels = Sparse.eval nodeValue2019 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2019) = mixedMoment B node2019 node2019Labels := rfl
  simpa [nodeValue2019, Sparse.eval] using hc.symm

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

theorem sound2052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2052 node2052Labels = Sparse.eval nodeValue2052 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2052) = mixedMoment B node2052 node2052Labels := rfl
  simpa [nodeValue2052, Sparse.eval] using hc.symm

theorem sound2075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2075 node2075Labels = Sparse.eval nodeValue2075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2075) = mixedMoment B node2075 node2075Labels := rfl
  simpa [nodeValue2075, Sparse.eval] using hc.symm

theorem sound2101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2101 node2101Labels = Sparse.eval nodeValue2101 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2101) = mixedMoment B node2101 node2101Labels := rfl
  simpa [nodeValue2101, Sparse.eval] using hc.symm

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

theorem sound2190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2190 node2190Labels = Sparse.eval nodeValue2190 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2190) = mixedMoment B node2190 node2190Labels := rfl
  simpa [nodeValue2190, Sparse.eval] using hc.symm

theorem sound2193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2193 node2193Labels = Sparse.eval nodeValue2193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2193) = mixedMoment B node2193 node2193Labels := rfl
  simpa [nodeValue2193, Sparse.eval] using hc.symm

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

theorem sound2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2260 node2260Labels = Sparse.eval nodeValue2260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2260) = mixedMoment B node2260 node2260Labels := rfl
  simpa [nodeValue2260, Sparse.eval] using hc.symm

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

theorem sound2884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2884 node2884Labels = Sparse.eval nodeValue2884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2884) = mixedMoment B node2884 node2884Labels := rfl
  simpa [nodeValue2884, Sparse.eval] using hc.symm

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

theorem sound3621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3621 node3621Labels = Sparse.eval nodeValue3621 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3621) = mixedMoment B node3621 node3621Labels := rfl
  simpa [nodeValue3621, Sparse.eval] using hc.symm

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

theorem sound4435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4435 node4435Labels = Sparse.eval nodeValue4435 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4435) = mixedMoment B node4435 node4435Labels := rfl
  simpa [nodeValue4435, Sparse.eval] using hc.symm

theorem sound4437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4437 node4437Labels = Sparse.eval nodeValue4437 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4437) = mixedMoment B node4437 node4437Labels := rfl
  simpa [nodeValue4437, Sparse.eval] using hc.symm

theorem sound4443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4443 node4443Labels = Sparse.eval nodeValue4443 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4443) = mixedMoment B node4443 node4443Labels := rfl
  simpa [nodeValue4443, Sparse.eval] using hc.symm

theorem sound4452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4452 node4452Labels = Sparse.eval nodeValue4452 (mixedVector B) := by
  have h := singleton4452 B _hB
  rw [sound1035 B _hB _hF, sound1645 B _hB _hF] at h
  norm_num [nodeValue4452, nodeValue1035, nodeValue1645, Sparse.eval] at h ⊢
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

theorem sound4791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4791 node4791Labels = Sparse.eval nodeValue4791 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4791) = mixedMoment B node4791 node4791Labels := rfl
  simpa [nodeValue4791, Sparse.eval] using hc.symm

theorem sound4794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4794 node4794Labels = Sparse.eval nodeValue4794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4794) = mixedMoment B node4794 node4794Labels := rfl
  simpa [nodeValue4794, Sparse.eval] using hc.symm

theorem sound4798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4798 node4798Labels = Sparse.eval nodeValue4798 (mixedVector B) := by
  have h := singleton4798 B _hB
  rw [sound2016 B _hB _hF, sound2075 B _hB _hF] at h
  norm_num [nodeValue4798, nodeValue2016, nodeValue2075, Sparse.eval] at h ⊢
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

theorem zero4834 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4834 node4834Labels = 0 := by
  exact mixedMoment_order_one B hB node4834 node4834Labels 1
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

theorem sound4801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4801 node4801Labels = Sparse.eval nodeValue4801 (mixedVector B) := by
  have h := singleton4801 B _hB
  rw [sound2019 B _hB _hF, sound2190 B _hB _hF] at h
  norm_num [nodeValue4801, nodeValue2019, nodeValue2190, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4832 node4832Labels = Sparse.eval nodeValue4832 (mixedVector B) := by
  have h := singleton4832 B _hB
  rw [sound2052 B _hB _hF, sound2193 B _hB _hF] at h
  norm_num [nodeValue4832, nodeValue2052, nodeValue2193, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4834 node4834Labels = Sparse.eval nodeValue4834 (mixedVector B) := by
  simpa only [nodeValue4834, Sparse.eval_nil] using zero4834 B _hB _hF

theorem sound4848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4848 node4848Labels = Sparse.eval nodeValue4848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4848) = mixedMoment B node4848 node4848Labels := rfl
  simpa [nodeValue4848, Sparse.eval] using hc.symm

theorem sound4850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4850 node4850Labels = Sparse.eval nodeValue4850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4850) = mixedMoment B node4850 node4850Labels := rfl
  simpa [nodeValue4850, Sparse.eval] using hc.symm

theorem sound4851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4851 node4851Labels = Sparse.eval nodeValue4851 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4851) = mixedMoment B node4851 node4851Labels := rfl
  simpa [nodeValue4851, Sparse.eval] using hc.symm

theorem sound4855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4855 node4855Labels = Sparse.eval nodeValue4855 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4855) = mixedMoment B node4855 node4855Labels := rfl
  simpa [nodeValue4855, Sparse.eval] using hc.symm

theorem sound4860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4860 node4860Labels = Sparse.eval nodeValue4860 (mixedVector B) := by
  have h := singleton4860 B _hB
  rw [sound2101 B _hB _hF] at h
  norm_num [nodeValue4860, nodeValue2101, Sparse.eval] at h ⊢
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

theorem sound4866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4866 node4866Labels = Sparse.eval nodeValue4866 (mixedVector B) := by
  have h := singleton4866 B _hB
  rw [sound2107 B _hB _hF, sound2260 B _hB _hF] at h
  norm_num [nodeValue4866, nodeValue2107, nodeValue2260, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4879 node4879Labels = Sparse.eval nodeValue4879 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4879) = mixedMoment B node4879 node4879Labels := rfl
  simpa [nodeValue4879, Sparse.eval] using hc.symm

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

theorem sound5184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5184 node5184Labels = Sparse.eval nodeValue5184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5184) = mixedMoment B node5184 node5184Labels := rfl
  simpa [nodeValue5184, Sparse.eval] using hc.symm

theorem sound5198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5198 node5198Labels = Sparse.eval nodeValue5198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5198) = mixedMoment B node5198 node5198Labels := rfl
  simpa [nodeValue5198, Sparse.eval] using hc.symm

theorem sound5203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5203 node5203Labels = Sparse.eval nodeValue5203 (mixedVector B) := by
  have h := singleton5203 B _hB
  rw [sound2884 B _hB _hF, sound3621 B _hB _hF] at h
  norm_num [nodeValue5203, nodeValue2884, nodeValue3621, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources76
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2458 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2458 + difference 0 1) (sourceB2458 + difference 1 0) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2458 + difference 0 1) (sourceB2458 + difference 1 0) sourceC2458) = raw32335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw32335; decide +kernel
    rw [ha]
    exact (canonical32335 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2458 + difference 0 2) (sourceB2458 + difference 2 0) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5184) := by
    have ha : (tripleCharges (sourceA2458 + difference 0 2) (sourceB2458 + difference 2 0) sourceC2458) = raw33001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33001; decide +kernel
    rw [ha]
    exact (canonical33001 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2458 + difference 0 3) (sourceB2458 + difference 3 0) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA2458 + difference 0 3) (sourceB2458 + difference 3 0) sourceC2458) = raw33766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33766; decide +kernel
    rw [ha]
    exact (canonical33766 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2458 + difference 0 4) (sourceB2458 + difference 4 0) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA2458 + difference 0 4) (sourceB2458 + difference 4 0) sourceC2458) = raw32824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw32824; decide +kernel
    rw [ha]
    exact (canonical32824 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2458 + difference 0 5) (sourceB2458 + difference 5 0) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2458 + difference 0 5) (sourceB2458 + difference 5 0) sourceC2458) = raw32318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw32318; decide +kernel
    rw [ha]
    exact (canonical32318 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2458 + difference 1 0) (sourceB2458 + difference 0 1) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4443) := by
    have ha : (tripleCharges (sourceA2458 + difference 1 0) (sourceB2458 + difference 0 1) sourceC2458) = raw33767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33767; decide +kernel
    rw [ha]
    exact (canonical33767 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2458 + difference 1 2) (sourceB2458 + difference 2 1) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4794) := by
    have ha : (tripleCharges (sourceA2458 + difference 1 2) (sourceB2458 + difference 2 1) sourceC2458) = raw33768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33768; decide +kernel
    rw [ha]
    exact (canonical33768 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2458 + difference 1 3) (sourceB2458 + difference 3 1) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4855) := by
    have ha : (tripleCharges (sourceA2458 + difference 1 3) (sourceB2458 + difference 3 1) sourceC2458) = raw33769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33769; decide +kernel
    rw [ha]
    exact (canonical33769 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2458 + difference 1 4) (sourceB2458 + difference 4 1) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4855) := by
    have ha : (tripleCharges (sourceA2458 + difference 1 4) (sourceB2458 + difference 4 1) sourceC2458) = raw33770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33770; decide +kernel
    rw [ha]
    exact (canonical33770 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2458 + difference 1 5) (sourceB2458 + difference 5 1) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA2458 + difference 1 5) (sourceB2458 + difference 5 1) sourceC2458) = raw33644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33644; decide +kernel
    rw [ha]
    exact (canonical33644 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2458 + difference 2 0) (sourceB2458 + difference 0 2) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4435) := by
    have ha : (tripleCharges (sourceA2458 + difference 2 0) (sourceB2458 + difference 0 2) sourceC2458) = raw33771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33771; decide +kernel
    rw [ha]
    exact (canonical33771 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2458 + difference 2 1) (sourceB2458 + difference 1 2) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2458 + difference 2 1) (sourceB2458 + difference 1 2) sourceC2458) = raw32333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw32333; decide +kernel
    rw [ha]
    exact (canonical32333 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2458 + difference 2 3) (sourceB2458 + difference 3 2) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4848) := by
    have ha : (tripleCharges (sourceA2458 + difference 2 3) (sourceB2458 + difference 3 2) sourceC2458) = raw33772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33772; decide +kernel
    rw [ha]
    exact (canonical33772 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2458 + difference 2 4) (sourceB2458 + difference 4 2) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4848) := by
    have ha : (tripleCharges (sourceA2458 + difference 2 4) (sourceB2458 + difference 4 2) sourceC2458) = raw33773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33773; decide +kernel
    rw [ha]
    exact (canonical33773 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2458 + difference 2 5) (sourceB2458 + difference 5 2) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA2458 + difference 2 5) (sourceB2458 + difference 5 2) sourceC2458) = raw32317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw32317; decide +kernel
    rw [ha]
    exact (canonical32317 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2458 + difference 3 0) (sourceB2458 + difference 0 3) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA2458 + difference 3 0) (sourceB2458 + difference 0 3) sourceC2458) = raw33652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33652; decide +kernel
    rw [ha]
    exact (canonical33652 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2458 + difference 3 1) (sourceB2458 + difference 1 3) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2458 + difference 3 1) (sourceB2458 + difference 1 3) sourceC2458) = raw32835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw32835; decide +kernel
    rw [ha]
    exact (canonical32835 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2458 + difference 3 2) (sourceB2458 + difference 2 3) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2458 + difference 3 2) (sourceB2458 + difference 2 3) sourceC2458) = raw32999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw32999; decide +kernel
    rw [ha]
    exact (canonical32999 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2458 + difference 3 4) (sourceB2458 + difference 4 3) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA2458 + difference 3 4) (sourceB2458 + difference 4 3) sourceC2458) = raw32822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw32822; decide +kernel
    rw [ha]
    exact (canonical32822 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2458 + difference 3 5) (sourceB2458 + difference 5 3) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2458 + difference 3 5) (sourceB2458 + difference 5 3) sourceC2458) = raw33568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33568; decide +kernel
    rw [ha]
    exact (canonical33568 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2458 + difference 4 0) (sourceB2458 + difference 0 4) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA2458 + difference 4 0) (sourceB2458 + difference 0 4) sourceC2458) = raw33774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33774; decide +kernel
    rw [ha]
    exact (canonical33774 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2458 + difference 4 1) (sourceB2458 + difference 1 4) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2458 + difference 4 1) (sourceB2458 + difference 1 4) sourceC2458) = raw33775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33775; decide +kernel
    rw [ha]
    exact (canonical33775 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2458 + difference 4 2) (sourceB2458 + difference 2 4) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2458 + difference 4 2) (sourceB2458 + difference 2 4) sourceC2458) = raw33776 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33776; decide +kernel
    rw [ha]
    exact (canonical33776 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2458 + difference 4 3) (sourceB2458 + difference 3 4) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA2458 + difference 4 3) (sourceB2458 + difference 3 4) sourceC2458) = raw33777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33777; decide +kernel
    rw [ha]
    exact (canonical33777 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2458 + difference 4 5) (sourceB2458 + difference 5 4) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2458 + difference 4 5) (sourceB2458 + difference 5 4) sourceC2458) = raw33567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33567; decide +kernel
    rw [ha]
    exact (canonical33567 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2458 + difference 5 0) (sourceB2458 + difference 0 5) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4437) := by
    have ha : (tripleCharges (sourceA2458 + difference 5 0) (sourceB2458 + difference 0 5) sourceC2458) = raw33778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33778; decide +kernel
    rw [ha]
    exact (canonical33778 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2458 + difference 5 1) (sourceB2458 + difference 1 5) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2458 + difference 5 1) (sourceB2458 + difference 1 5) sourceC2458) = raw33779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33779; decide +kernel
    rw [ha]
    exact (canonical33779 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2458 + difference 5 2) (sourceB2458 + difference 2 5) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4791) := by
    have ha : (tripleCharges (sourceA2458 + difference 5 2) (sourceB2458 + difference 2 5) sourceC2458) = raw33780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33780; decide +kernel
    rw [ha]
    exact (canonical33780 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2458 + difference 5 3) (sourceB2458 + difference 3 5) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4850) := by
    have ha : (tripleCharges (sourceA2458 + difference 5 3) (sourceB2458 + difference 3 5) sourceC2458) = raw33781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33781; decide +kernel
    rw [ha]
    exact (canonical33781 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2458 + difference 5 4) (sourceB2458 + difference 4 5) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4850) := by
    have ha : (tripleCharges (sourceA2458 + difference 5 4) (sourceB2458 + difference 4 5) sourceC2458) = raw33782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33782; decide +kernel
    rw [ha]
    exact (canonical33782 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2458 sourceB2458 sourceC2458
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2458, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1978 : Integer.Sparse.reindex keyMap MixedData.row1978 = numericRow1978 := by decide +kernel

theorem numericCheck1978 (x : Master → ℝ) : Integer.Sparse.eval numericRow1978 x =
    (17280 : ℝ) * reducedSource1978 x := by
  norm_num [numericRow1978, reducedSource1978, Integer.Sparse.eval, Sparse.eval, nodeValue4435, nodeValue4437, nodeValue4443, nodeValue4452, nodeValue4791, nodeValue4794, nodeValue4798, nodeValue4801, nodeValue4832, nodeValue4834, nodeValue4848, nodeValue4850, nodeValue4851, nodeValue4855, nodeValue4860, nodeValue4866, nodeValue4879, nodeValue5168, nodeValue5184, nodeValue5198, nodeValue5203]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1978 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1978 (mixedVector B) = 0 := by
  have h4435 : mixedVector B (Sum.inr 4435) = Sparse.eval nodeValue4435 (mixedVector B) := by
    change mixedMoment B node4435 node4435Labels = _
    exact sound4435 B hB hF
  have h4437 : mixedVector B (Sum.inr 4437) = Sparse.eval nodeValue4437 (mixedVector B) := by
    change mixedMoment B node4437 node4437Labels = _
    exact sound4437 B hB hF
  have h4443 : mixedVector B (Sum.inr 4443) = Sparse.eval nodeValue4443 (mixedVector B) := by
    change mixedMoment B node4443 node4443Labels = _
    exact sound4443 B hB hF
  have h4452 : mixedVector B (Sum.inr 4452) = Sparse.eval nodeValue4452 (mixedVector B) := by
    change mixedMoment B node4452 node4452Labels = _
    exact sound4452 B hB hF
  have h4791 : mixedVector B (Sum.inr 4791) = Sparse.eval nodeValue4791 (mixedVector B) := by
    change mixedMoment B node4791 node4791Labels = _
    exact sound4791 B hB hF
  have h4794 : mixedVector B (Sum.inr 4794) = Sparse.eval nodeValue4794 (mixedVector B) := by
    change mixedMoment B node4794 node4794Labels = _
    exact sound4794 B hB hF
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4848 : mixedVector B (Sum.inr 4848) = Sparse.eval nodeValue4848 (mixedVector B) := by
    change mixedMoment B node4848 node4848Labels = _
    exact sound4848 B hB hF
  have h4850 : mixedVector B (Sum.inr 4850) = Sparse.eval nodeValue4850 (mixedVector B) := by
    change mixedMoment B node4850 node4850Labels = _
    exact sound4850 B hB hF
  have h4851 : mixedVector B (Sum.inr 4851) = Sparse.eval nodeValue4851 (mixedVector B) := by
    change mixedMoment B node4851 node4851Labels = _
    exact sound4851 B hB hF
  have h4855 : mixedVector B (Sum.inr 4855) = Sparse.eval nodeValue4855 (mixedVector B) := by
    change mixedMoment B node4855 node4855Labels = _
    exact sound4855 B hB hF
  have h4860 : mixedVector B (Sum.inr 4860) = Sparse.eval nodeValue4860 (mixedVector B) := by
    change mixedMoment B node4860 node4860Labels = _
    exact sound4860 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4879 : mixedVector B (Sum.inr 4879) = Sparse.eval nodeValue4879 (mixedVector B) := by
    change mixedMoment B node4879 node4879Labels = _
    exact sound4879 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168_e B hB hF
  have h5184 : mixedVector B (Sum.inr 5184) = Sparse.eval nodeValue5184 (mixedVector B) := by
    change mixedMoment B node5184 node5184Labels = _
    exact sound5184 B hB hF
  have h5198 : mixedVector B (Sum.inr 5198) = Sparse.eval nodeValue5198 (mixedVector B) := by
    change mixedMoment B node5198 node5198Labels = _
    exact sound5198 B hB hF
  have h5203 : mixedVector B (Sum.inr 5203) = Sparse.eval nodeValue5203 (mixedVector B) := by
    change mixedMoment B node5203 node5203Labels = _
    exact sound5203 B hB hF
  simpa only [sourceForm2458, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4435, h4437, h4443, h4452, h4791, h4794, h4798, h4801, h4832, h4834, h4848, h4850, h4851, h4855, h4860, h4866, h4879, h5168, h5184, h5198, h5203, reducedSource1978] using sourceEq2458 B hB

theorem rowSound1978_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1978 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1978, numericCheck1978, reducedZero1978 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1978_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1978_e_oai
