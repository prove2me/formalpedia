-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:48:56.606203+00:00
-- url     : https://prove2.me/submissions/0c6ef018-a224-4b01-b724-d16dca9af87c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5167_e

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

theorem canonical1779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1779 raw1779Labels = mixedMoment B node4859 node4859Labels := by
  calc
    mixedMoment B raw1779 raw1779Labels = mixedMoment B raw1779step0 raw1779step0Labels := by
      have ha : raw1779step0 = (fun i j => raw1779 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1779step0 raw1779; decide +kernel
      have hl : raw1779step0Labels = raw1779Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1779 raw1779Labels permutation152 permutation4
    mixedMoment B raw1779step0 raw1779step0Labels = mixedMoment B raw1779step1 raw1779step1Labels := by
      have ha : raw1779step1 = raw1779step0 := by apply Matrix.ext; unfold raw1779step1 raw1779step0; decide +kernel
      have hl : raw1779step0Labels = labelEmbedding7 ∘ raw1779step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1779step0 raw1779step0Labels raw1779step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4859 node4859Labels := by rfl

theorem canonical1780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1780 raw1780Labels = mixedMoment B node2100 node2100Labels := by
  calc
    mixedMoment B raw1780 raw1780Labels = mixedMoment B raw1780step0 raw1780step0Labels := by
      have ha : raw1780step0 = (fun i j => raw1780 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1780step0 raw1780; decide +kernel
      have hl : raw1780step0Labels = raw1780Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1780 raw1780Labels permutation152 permutation4
    _ = mixedMoment B node2100 node2100Labels := by rfl

theorem canonical1781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1781 raw1781Labels = mixedMoment B node2100 node2100Labels := by
  calc
    mixedMoment B raw1781 raw1781Labels = mixedMoment B raw1781step0 raw1781step0Labels := by
      have ha : raw1781step0 = (fun i j => raw1781 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1781step0 raw1781; decide +kernel
      have hl : raw1781step0Labels = raw1781Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1781 raw1781Labels permutation176 permutation6
    mixedMoment B raw1781step0 raw1781step0Labels = mixedMoment B raw1781step1 raw1781step1Labels := by
      have ha : raw1781step1 = -raw1781step0 := by apply Matrix.ext; change ∀ i j, raw1781step1 i j = -(raw1781step0 i j); unfold raw1781step1 raw1781step0; decide +kernel
      have hl : raw1781step1Labels = raw1781step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1781step1 raw1781step1Labels = mixedMoment B raw1781step2 raw1781step2Labels := by
      have ha : raw1781step2 = raw1781step1 := by apply Matrix.ext; unfold raw1781step2 raw1781step1; decide +kernel
      have hl : raw1781step1Labels = labelEmbedding1 ∘ raw1781step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1781step1 raw1781step1Labels raw1781step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2100 node2100Labels := by rfl

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

theorem canonical2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2226 raw2226Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw2226 raw2226Labels = mixedMoment B raw2226step0 raw2226step0Labels := by
      have ha : raw2226step0 = (fun i j => raw2226 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2226step0 raw2226; decide +kernel
      have hl : raw2226step0Labels = raw2226Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2226 raw2226Labels permutation152 permutation5
    mixedMoment B raw2226step0 raw2226step0Labels = mixedMoment B raw2226step1 raw2226step1Labels := by
      have ha : raw2226step1 = raw2226step0 := by apply Matrix.ext; unfold raw2226step1 raw2226step0; decide +kernel
      have hl : raw2226step0Labels = labelEmbedding8 ∘ raw2226step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2226step0 raw2226step0Labels raw2226step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

theorem canonical2227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2227 raw2227Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw2227 raw2227Labels = mixedMoment B raw2227step0 raw2227step0Labels := by
      have ha : raw2227step0 = (fun i j => raw2227 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2227step0 raw2227; decide +kernel
      have hl : raw2227step0Labels = raw2227Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2227 raw2227Labels permutation170 permutation4
    _ = mixedMoment B node2880 node2880Labels := by rfl

theorem canonical2228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2228 raw2228Labels = mixedMoment B node3617 node3617Labels := by
  calc
    mixedMoment B raw2228 raw2228Labels = mixedMoment B raw2228step0 raw2228step0Labels := by
      have ha : raw2228step0 = (fun i j => raw2228 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2228step0 raw2228; decide +kernel
      have hl : raw2228step0Labels = raw2228Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2228 raw2228Labels permutation184 permutation3
    mixedMoment B raw2228step0 raw2228step0Labels = mixedMoment B raw2228step1 raw2228step1Labels := by
      have ha : raw2228step1 = -raw2228step0 := by apply Matrix.ext; change ∀ i j, raw2228step1 i j = -(raw2228step0 i j); unfold raw2228step1 raw2228step0; decide +kernel
      have hl : raw2228step1Labels = raw2228step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2228step1 raw2228step1Labels = mixedMoment B raw2228step2 raw2228step2Labels := by
      have ha : raw2228step2 = raw2228step1 := by apply Matrix.ext; unfold raw2228step2 raw2228step1; decide +kernel
      have hl : raw2228step1Labels = labelEmbedding1 ∘ raw2228step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2228step1 raw2228step1Labels raw2228step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3617 node3617Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical269
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34536 raw34536Labels = mixedMoment B node4859 node4859Labels := by
  calc
    mixedMoment B raw34536 raw34536Labels = mixedMoment B raw34536step0 raw34536step0Labels := by
      have ha : raw34536step0 = (fun i j => raw34536 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34536step0 raw34536; decide +kernel
      have hl : raw34536step0Labels = raw34536Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34536 raw34536Labels permutation246 permutation4
    mixedMoment B raw34536step0 raw34536step0Labels = mixedMoment B raw34536step1 raw34536step1Labels := by
      have ha : raw34536step1 = -raw34536step0 := by apply Matrix.ext; change ∀ i j, raw34536step1 i j = -(raw34536step0 i j); unfold raw34536step1 raw34536step0; decide +kernel
      have hl : raw34536step1Labels = raw34536step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34536step1 raw34536step1Labels = mixedMoment B raw34536step2 raw34536step2Labels := by
      have ha : raw34536step2 = raw34536step1 := by apply Matrix.ext; unfold raw34536step2 raw34536step1; decide +kernel
      have hl : raw34536step1Labels = labelEmbedding7 ∘ raw34536step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34536step1 raw34536step1Labels raw34536step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4859 node4859Labels := by rfl

theorem canonical34539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34539 raw34539Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw34539 raw34539Labels = mixedMoment B raw34539step0 raw34539step0Labels := by
      have ha : raw34539step0 = (fun i j => raw34539 (permutation174 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34539step0 raw34539; decide +kernel
      have hl : raw34539step0Labels = raw34539Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34539 raw34539Labels permutation174 permutation6
    mixedMoment B raw34539step0 raw34539step0Labels = mixedMoment B raw34539step1 raw34539step1Labels := by
      have ha : raw34539step1 = raw34539step0 := by apply Matrix.ext; unfold raw34539step1 raw34539step0; decide +kernel
      have hl : raw34539step0Labels = labelEmbedding9 ∘ raw34539step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34539step0 raw34539step0Labels raw34539step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5197 node5197Labels := by rfl

theorem canonical34556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34556 raw34556Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw34556 raw34556Labels = mixedMoment B raw34556step0 raw34556step0Labels := by
      have ha : raw34556step0 = (fun i j => raw34556 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34556step0 raw34556; decide +kernel
      have hl : raw34556step0Labels = raw34556Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34556 raw34556Labels permutation170 permutation6
    mixedMoment B raw34556step0 raw34556step0Labels = mixedMoment B raw34556step1 raw34556step1Labels := by
      have ha : raw34556step1 = raw34556step0 := by apply Matrix.ext; unfold raw34556step1 raw34556step0; decide +kernel
      have hl : raw34556step0Labels = labelEmbedding9 ∘ raw34556step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34556step0 raw34556step0Labels raw34556step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4833 node4833Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical270
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34560 raw34560Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw34560 raw34560Labels = mixedMoment B raw34560step0 raw34560step0Labels := by
      have ha : raw34560step0 = (fun i j => raw34560 (permutation168 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34560step0 raw34560; decide +kernel
      have hl : raw34560step0Labels = raw34560Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34560 raw34560Labels permutation168 permutation6
    mixedMoment B raw34560step0 raw34560step0Labels = mixedMoment B raw34560step1 raw34560step1Labels := by
      have ha : raw34560step1 = raw34560step0 := by apply Matrix.ext; unfold raw34560step1 raw34560step0; decide +kernel
      have hl : raw34560step0Labels = labelEmbedding9 ∘ raw34560step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34560step0 raw34560step0Labels raw34560step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5167 node5167Labels := by rfl

theorem canonical34654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34654 raw34654Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw34654 raw34654Labels = mixedMoment B raw34654step0 raw34654step0Labels := by
      have ha : raw34654step0 = (fun i j => raw34654 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34654step0 raw34654; decide +kernel
      have hl : raw34654step0Labels = raw34654Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34654 raw34654Labels permutation155 permutation6
    mixedMoment B raw34654step0 raw34654step0Labels = mixedMoment B raw34654step1 raw34654step1Labels := by
      have ha : raw34654step1 = raw34654step0 := by apply Matrix.ext; unfold raw34654step1 raw34654step0; decide +kernel
      have hl : raw34654step0Labels = labelEmbedding9 ∘ raw34654step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34654step0 raw34654step0Labels raw34654step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

theorem canonical34655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34655 raw34655Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw34655 raw34655Labels = mixedMoment B raw34655step0 raw34655step0Labels := by
      have ha : raw34655step0 = (fun i j => raw34655 (permutation161 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34655step0 raw34655; decide +kernel
      have hl : raw34655step0Labels = raw34655Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34655 raw34655Labels permutation161 permutation6
    mixedMoment B raw34655step0 raw34655step0Labels = mixedMoment B raw34655step1 raw34655step1Labels := by
      have ha : raw34655step1 = raw34655step0 := by apply Matrix.ext; unfold raw34655step1 raw34655step0; decide +kernel
      have hl : raw34655step0Labels = labelEmbedding9 ∘ raw34655step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34655step0 raw34655step0Labels raw34655step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

theorem canonical34656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34656 raw34656Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw34656 raw34656Labels = mixedMoment B raw34656step0 raw34656step0Labels := by
      have ha : raw34656step0 = (fun i j => raw34656 (permutation168 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34656step0 raw34656; decide +kernel
      have hl : raw34656step0Labels = raw34656Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34656 raw34656Labels permutation168 permutation6
    mixedMoment B raw34656step0 raw34656step0Labels = mixedMoment B raw34656step1 raw34656step1Labels := by
      have ha : raw34656step1 = raw34656step0 := by apply Matrix.ext; unfold raw34656step1 raw34656step0; decide +kernel
      have hl : raw34656step0Labels = labelEmbedding9 ∘ raw34656step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34656step0 raw34656step0Labels raw34656step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5197 node5197Labels := by rfl

theorem canonical34657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34657 raw34657Labels = mixedMoment B node4441 node4441Labels := by
  calc
    mixedMoment B raw34657 raw34657Labels = mixedMoment B raw34657step0 raw34657step0Labels := by
      have ha : raw34657step0 = (fun i j => raw34657 (permutation243 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34657step0 raw34657; decide +kernel
      have hl : raw34657step0Labels = raw34657Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34657 raw34657Labels permutation243 permutation4
    mixedMoment B raw34657step0 raw34657step0Labels = mixedMoment B raw34657step1 raw34657step1Labels := by
      have ha : raw34657step1 = -raw34657step0 := by apply Matrix.ext; change ∀ i j, raw34657step1 i j = -(raw34657step0 i j); unfold raw34657step1 raw34657step0; decide +kernel
      have hl : raw34657step1Labels = raw34657step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34657step1 raw34657step1Labels = mixedMoment B raw34657step2 raw34657step2Labels := by
      have ha : raw34657step2 = raw34657step1 := by apply Matrix.ext; unfold raw34657step2 raw34657step1; decide +kernel
      have hl : raw34657step1Labels = labelEmbedding7 ∘ raw34657step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34657step1 raw34657step1Labels raw34657step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4441 node4441Labels := by rfl

theorem canonical34658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34658 raw34658Labels = mixedMoment B node4878 node4878Labels := by
  calc
    mixedMoment B raw34658 raw34658Labels = mixedMoment B raw34658step0 raw34658step0Labels := by
      have ha : raw34658step0 = (fun i j => raw34658 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34658step0 raw34658; decide +kernel
      have hl : raw34658step0Labels = raw34658Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34658 raw34658Labels permutation155 permutation6
    mixedMoment B raw34658step0 raw34658step0Labels = mixedMoment B raw34658step1 raw34658step1Labels := by
      have ha : raw34658step1 = raw34658step0 := by apply Matrix.ext; unfold raw34658step1 raw34658step0; decide +kernel
      have hl : raw34658step0Labels = labelEmbedding9 ∘ raw34658step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34658step0 raw34658step0Labels raw34658step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4878 node4878Labels := by rfl

theorem canonical34659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34659 raw34659Labels = mixedMoment B node4878 node4878Labels := by
  calc
    mixedMoment B raw34659 raw34659Labels = mixedMoment B raw34659step0 raw34659step0Labels := by
      have ha : raw34659step0 = (fun i j => raw34659 (permutation161 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34659step0 raw34659; decide +kernel
      have hl : raw34659step0Labels = raw34659Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34659 raw34659Labels permutation161 permutation6
    mixedMoment B raw34659step0 raw34659step0Labels = mixedMoment B raw34659step1 raw34659step1Labels := by
      have ha : raw34659step1 = raw34659step0 := by apply Matrix.ext; unfold raw34659step1 raw34659step0; decide +kernel
      have hl : raw34659step0Labels = labelEmbedding9 ∘ raw34659step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34659step0 raw34659step0Labels raw34659step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4878 node4878Labels := by rfl

theorem canonical34660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34660 raw34660Labels = mixedMoment B node4854 node4854Labels := by
  calc
    mixedMoment B raw34660 raw34660Labels = mixedMoment B raw34660step0 raw34660step0Labels := by
      have ha : raw34660step0 = (fun i j => raw34660 (permutation243 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34660step0 raw34660; decide +kernel
      have hl : raw34660step0Labels = raw34660Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34660 raw34660Labels permutation243 permutation4
    mixedMoment B raw34660step0 raw34660step0Labels = mixedMoment B raw34660step1 raw34660step1Labels := by
      have ha : raw34660step1 = -raw34660step0 := by apply Matrix.ext; change ∀ i j, raw34660step1 i j = -(raw34660step0 i j); unfold raw34660step1 raw34660step0; decide +kernel
      have hl : raw34660step1Labels = raw34660step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34660step1 raw34660step1Labels = mixedMoment B raw34660step2 raw34660step2Labels := by
      have ha : raw34660step2 = raw34660step1 := by apply Matrix.ext; unfold raw34660step2 raw34660step1; decide +kernel
      have hl : raw34660step1Labels = labelEmbedding7 ∘ raw34660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34660step1 raw34660step1Labels raw34660step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4854 node4854Labels := by rfl

theorem canonical34661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34661 raw34661Labels = mixedMoment B node4854 node4854Labels := by
  calc
    mixedMoment B raw34661 raw34661Labels = mixedMoment B raw34661step0 raw34661step0Labels := by
      have ha : raw34661step0 = (fun i j => raw34661 (permutation263 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34661step0 raw34661; decide +kernel
      have hl : raw34661step0Labels = raw34661Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34661 raw34661Labels permutation263 permutation4
    mixedMoment B raw34661step0 raw34661step0Labels = mixedMoment B raw34661step1 raw34661step1Labels := by
      have ha : raw34661step1 = -raw34661step0 := by apply Matrix.ext; change ∀ i j, raw34661step1 i j = -(raw34661step0 i j); unfold raw34661step1 raw34661step0; decide +kernel
      have hl : raw34661step1Labels = raw34661step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34661step1 raw34661step1Labels = mixedMoment B raw34661step2 raw34661step2Labels := by
      have ha : raw34661step2 = raw34661step1 := by apply Matrix.ext; unfold raw34661step2 raw34661step1; decide +kernel
      have hl : raw34661step1Labels = labelEmbedding7 ∘ raw34661step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34661step1 raw34661step1Labels raw34661step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4854 node4854Labels := by rfl

theorem canonical34662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34662 raw34662Labels = mixedMoment B node4436 node4436Labels := by
  calc
    mixedMoment B raw34662 raw34662Labels = mixedMoment B raw34662step0 raw34662step0Labels := by
      have ha : raw34662step0 = (fun i j => raw34662 (permutation241 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34662step0 raw34662; decide +kernel
      have hl : raw34662step0Labels = raw34662Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34662 raw34662Labels permutation241 permutation4
    mixedMoment B raw34662step0 raw34662step0Labels = mixedMoment B raw34662step1 raw34662step1Labels := by
      have ha : raw34662step1 = -raw34662step0 := by apply Matrix.ext; change ∀ i j, raw34662step1 i j = -(raw34662step0 i j); unfold raw34662step1 raw34662step0; decide +kernel
      have hl : raw34662step1Labels = raw34662step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34662step1 raw34662step1Labels = mixedMoment B raw34662step2 raw34662step2Labels := by
      have ha : raw34662step2 = raw34662step1 := by apply Matrix.ext; unfold raw34662step2 raw34662step1; decide +kernel
      have hl : raw34662step1Labels = labelEmbedding7 ∘ raw34662step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34662step1 raw34662step1Labels raw34662step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4436 node4436Labels := by rfl

theorem canonical34663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34663 raw34663Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw34663 raw34663Labels = mixedMoment B raw34663step0 raw34663step0Labels := by
      have ha : raw34663step0 = (fun i j => raw34663 (permutation169 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34663step0 raw34663; decide +kernel
      have hl : raw34663step0Labels = raw34663Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34663 raw34663Labels permutation169 permutation6
    mixedMoment B raw34663step0 raw34663step0Labels = mixedMoment B raw34663step1 raw34663step1Labels := by
      have ha : raw34663step1 = raw34663step0 := by apply Matrix.ext; unfold raw34663step1 raw34663step0; decide +kernel
      have hl : raw34663step0Labels = labelEmbedding9 ∘ raw34663step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34663step0 raw34663step0Labels raw34663step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

theorem canonical34664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34664 raw34664Labels = mixedMoment B node4863 node4863Labels := by
  calc
    mixedMoment B raw34664 raw34664Labels = mixedMoment B raw34664step0 raw34664step0Labels := by
      have ha : raw34664step0 = (fun i j => raw34664 (permutation161 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34664step0 raw34664; decide +kernel
      have hl : raw34664step0Labels = raw34664Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34664 raw34664Labels permutation161 permutation6
    mixedMoment B raw34664step0 raw34664step0Labels = mixedMoment B raw34664step1 raw34664step1Labels := by
      have ha : raw34664step1 = raw34664step0 := by apply Matrix.ext; unfold raw34664step1 raw34664step0; decide +kernel
      have hl : raw34664step0Labels = labelEmbedding9 ∘ raw34664step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34664step0 raw34664step0Labels raw34664step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4863 node4863Labels := by rfl

theorem canonical34665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34665 raw34665Labels = mixedMoment B node4849 node4849Labels := by
  calc
    mixedMoment B raw34665 raw34665Labels = mixedMoment B raw34665step0 raw34665step0Labels := by
      have ha : raw34665step0 = (fun i j => raw34665 (permutation241 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34665step0 raw34665; decide +kernel
      have hl : raw34665step0Labels = raw34665Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34665 raw34665Labels permutation241 permutation4
    mixedMoment B raw34665step0 raw34665step0Labels = mixedMoment B raw34665step1 raw34665step1Labels := by
      have ha : raw34665step1 = -raw34665step0 := by apply Matrix.ext; change ∀ i j, raw34665step1 i j = -(raw34665step0 i j); unfold raw34665step1 raw34665step0; decide +kernel
      have hl : raw34665step1Labels = raw34665step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34665step1 raw34665step1Labels = mixedMoment B raw34665step2 raw34665step2Labels := by
      have ha : raw34665step2 = raw34665step1 := by apply Matrix.ext; unfold raw34665step2 raw34665step1; decide +kernel
      have hl : raw34665step1Labels = labelEmbedding7 ∘ raw34665step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34665step1 raw34665step1Labels raw34665step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4849 node4849Labels := by rfl

theorem canonical34666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34666 raw34666Labels = mixedMoment B node4849 node4849Labels := by
  calc
    mixedMoment B raw34666 raw34666Labels = mixedMoment B raw34666step0 raw34666step0Labels := by
      have ha : raw34666step0 = (fun i j => raw34666 (permutation261 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34666step0 raw34666; decide +kernel
      have hl : raw34666step0Labels = raw34666Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34666 raw34666Labels permutation261 permutation4
    mixedMoment B raw34666step0 raw34666step0Labels = mixedMoment B raw34666step1 raw34666step1Labels := by
      have ha : raw34666step1 = -raw34666step0 := by apply Matrix.ext; change ∀ i j, raw34666step1 i j = -(raw34666step0 i j); unfold raw34666step1 raw34666step0; decide +kernel
      have hl : raw34666step1Labels = raw34666step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34666step1 raw34666step1Labels = mixedMoment B raw34666step2 raw34666step2Labels := by
      have ha : raw34666step2 = raw34666step1 := by apply Matrix.ext; unfold raw34666step2 raw34666step1; decide +kernel
      have hl : raw34666step1Labels = labelEmbedding7 ∘ raw34666step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34666step1 raw34666step1Labels raw34666step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4849 node4849Labels := by rfl

theorem canonical34667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34667 raw34667Labels = mixedMoment B node4436 node4436Labels := by
  calc
    mixedMoment B raw34667 raw34667Labels = mixedMoment B raw34667step0 raw34667step0Labels := by
      have ha : raw34667step0 = (fun i j => raw34667 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34667step0 raw34667; decide +kernel
      have hl : raw34667step0Labels = raw34667Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34667 raw34667Labels permutation240 permutation4
    mixedMoment B raw34667step0 raw34667step0Labels = mixedMoment B raw34667step1 raw34667step1Labels := by
      have ha : raw34667step1 = -raw34667step0 := by apply Matrix.ext; change ∀ i j, raw34667step1 i j = -(raw34667step0 i j); unfold raw34667step1 raw34667step0; decide +kernel
      have hl : raw34667step1Labels = raw34667step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34667step1 raw34667step1Labels = mixedMoment B raw34667step2 raw34667step2Labels := by
      have ha : raw34667step2 = raw34667step1 := by apply Matrix.ext; unfold raw34667step2 raw34667step1; decide +kernel
      have hl : raw34667step1Labels = labelEmbedding7 ∘ raw34667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34667step1 raw34667step1Labels raw34667step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4436 node4436Labels := by rfl

theorem canonical34668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34668 raw34668Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw34668 raw34668Labels = mixedMoment B raw34668step0 raw34668step0Labels := by
      have ha : raw34668step0 = (fun i j => raw34668 (permutation168 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34668step0 raw34668; decide +kernel
      have hl : raw34668step0Labels = raw34668Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34668 raw34668Labels permutation168 permutation6
    mixedMoment B raw34668step0 raw34668step0Labels = mixedMoment B raw34668step1 raw34668step1Labels := by
      have ha : raw34668step1 = raw34668step0 := by apply Matrix.ext; unfold raw34668step1 raw34668step0; decide +kernel
      have hl : raw34668step0Labels = labelEmbedding9 ∘ raw34668step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34668step0 raw34668step0Labels raw34668step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

theorem canonical34669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34669 raw34669Labels = mixedMoment B node4863 node4863Labels := by
  calc
    mixedMoment B raw34669 raw34669Labels = mixedMoment B raw34669step0 raw34669step0Labels := by
      have ha : raw34669step0 = (fun i j => raw34669 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34669step0 raw34669; decide +kernel
      have hl : raw34669step0Labels = raw34669Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34669 raw34669Labels permutation155 permutation6
    mixedMoment B raw34669step0 raw34669step0Labels = mixedMoment B raw34669step1 raw34669step1Labels := by
      have ha : raw34669step1 = raw34669step0 := by apply Matrix.ext; unfold raw34669step1 raw34669step0; decide +kernel
      have hl : raw34669step0Labels = labelEmbedding9 ∘ raw34669step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34669step0 raw34669step0Labels raw34669step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4863 node4863Labels := by rfl

theorem canonical34670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34670 raw34670Labels = mixedMoment B node4849 node4849Labels := by
  calc
    mixedMoment B raw34670 raw34670Labels = mixedMoment B raw34670step0 raw34670step0Labels := by
      have ha : raw34670step0 = (fun i j => raw34670 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34670step0 raw34670; decide +kernel
      have hl : raw34670step0Labels = raw34670Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34670 raw34670Labels permutation240 permutation4
    mixedMoment B raw34670step0 raw34670step0Labels = mixedMoment B raw34670step1 raw34670step1Labels := by
      have ha : raw34670step1 = -raw34670step0 := by apply Matrix.ext; change ∀ i j, raw34670step1 i j = -(raw34670step0 i j); unfold raw34670step1 raw34670step0; decide +kernel
      have hl : raw34670step1Labels = raw34670step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34670step1 raw34670step1Labels = mixedMoment B raw34670step2 raw34670step2Labels := by
      have ha : raw34670step2 = raw34670step1 := by apply Matrix.ext; unfold raw34670step2 raw34670step1; decide +kernel
      have hl : raw34670step1Labels = labelEmbedding7 ∘ raw34670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34670step1 raw34670step1Labels raw34670step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4849 node4849Labels := by rfl

theorem canonical34671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34671 raw34671Labels = mixedMoment B node4849 node4849Labels := by
  calc
    mixedMoment B raw34671 raw34671Labels = mixedMoment B raw34671step0 raw34671step0Labels := by
      have ha : raw34671step0 = (fun i j => raw34671 (permutation260 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34671step0 raw34671; decide +kernel
      have hl : raw34671step0Labels = raw34671Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34671 raw34671Labels permutation260 permutation4
    mixedMoment B raw34671step0 raw34671step0Labels = mixedMoment B raw34671step1 raw34671step1Labels := by
      have ha : raw34671step1 = -raw34671step0 := by apply Matrix.ext; change ∀ i j, raw34671step1 i j = -(raw34671step0 i j); unfold raw34671step1 raw34671step0; decide +kernel
      have hl : raw34671step1Labels = raw34671step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34671step1 raw34671step1Labels = mixedMoment B raw34671step2 raw34671step2Labels := by
      have ha : raw34671step2 = raw34671step1 := by apply Matrix.ext; unfold raw34671step2 raw34671step1; decide +kernel
      have hl : raw34671step1Labels = labelEmbedding7 ∘ raw34671step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34671step1 raw34671step1Labels raw34671step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4849 node4849Labels := by rfl

theorem canonical34672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34672 raw34672Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw34672 raw34672Labels = mixedMoment B raw34672step0 raw34672step0Labels := by
      have ha : raw34672step0 = (fun i j => raw34672 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34672step0 raw34672; decide +kernel
      have hl : raw34672step0Labels = raw34672Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34672 raw34672Labels permutation246 permutation4
    mixedMoment B raw34672step0 raw34672step0Labels = mixedMoment B raw34672step1 raw34672step1Labels := by
      have ha : raw34672step1 = -raw34672step0 := by apply Matrix.ext; change ∀ i j, raw34672step1 i j = -(raw34672step0 i j); unfold raw34672step1 raw34672step0; decide +kernel
      have hl : raw34672step1Labels = raw34672step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34672step1 raw34672step1Labels = mixedMoment B raw34672step2 raw34672step2Labels := by
      have ha : raw34672step2 = raw34672step1 := by apply Matrix.ext; unfold raw34672step2 raw34672step1; decide +kernel
      have hl : raw34672step1Labels = labelEmbedding7 ∘ raw34672step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34672step1 raw34672step1Labels raw34672step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

theorem canonical34673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34673 raw34673Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw34673 raw34673Labels = mixedMoment B raw34673step0 raw34673step0Labels := by
      have ha : raw34673step0 = (fun i j => raw34673 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34673step0 raw34673; decide +kernel
      have hl : raw34673step0Labels = raw34673Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34673 raw34673Labels permutation156 permutation6
    mixedMoment B raw34673step0 raw34673step0Labels = mixedMoment B raw34673step1 raw34673step1Labels := by
      have ha : raw34673step1 = raw34673step0 := by apply Matrix.ext; unfold raw34673step1 raw34673step0; decide +kernel
      have hl : raw34673step0Labels = labelEmbedding9 ∘ raw34673step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34673step0 raw34673step0Labels raw34673step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

theorem canonical34674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34674 raw34674Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw34674 raw34674Labels = mixedMoment B raw34674step0 raw34674step0Labels := by
      have ha : raw34674step0 = (fun i j => raw34674 (permutation162 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34674step0 raw34674; decide +kernel
      have hl : raw34674step0Labels = raw34674Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34674 raw34674Labels permutation162 permutation6
    mixedMoment B raw34674step0 raw34674step0Labels = mixedMoment B raw34674step1 raw34674step1Labels := by
      have ha : raw34674step1 = raw34674step0 := by apply Matrix.ext; unfold raw34674step1 raw34674step0; decide +kernel
      have hl : raw34674step0Labels = labelEmbedding9 ∘ raw34674step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34674step0 raw34674step0Labels raw34674step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

theorem canonical34675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34675 raw34675Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw34675 raw34675Labels = mixedMoment B raw34675step0 raw34675step0Labels := by
      have ha : raw34675step0 = (fun i j => raw34675 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34675step0 raw34675; decide +kernel
      have hl : raw34675step0Labels = raw34675Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34675 raw34675Labels permutation224 permutation4
    mixedMoment B raw34675step0 raw34675step0Labels = mixedMoment B raw34675step1 raw34675step1Labels := by
      have ha : raw34675step1 = -raw34675step0 := by apply Matrix.ext; change ∀ i j, raw34675step1 i j = -(raw34675step0 i j); unfold raw34675step1 raw34675step0; decide +kernel
      have hl : raw34675step1Labels = raw34675step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34675step1 raw34675step1Labels = mixedMoment B raw34675step2 raw34675step2Labels := by
      have ha : raw34675step2 = raw34675step1 := by apply Matrix.ext; unfold raw34675step2 raw34675step1; decide +kernel
      have hl : raw34675step1Labels = labelEmbedding7 ∘ raw34675step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34675step1 raw34675step1Labels raw34675step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

theorem canonical34676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34676 raw34676Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw34676 raw34676Labels = mixedMoment B raw34676step0 raw34676step0Labels := by
      have ha : raw34676step0 = (fun i j => raw34676 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34676step0 raw34676; decide +kernel
      have hl : raw34676step0Labels = raw34676Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34676 raw34676Labels permutation164 permutation6
    mixedMoment B raw34676step0 raw34676step0Labels = mixedMoment B raw34676step1 raw34676step1Labels := by
      have ha : raw34676step1 = raw34676step0 := by apply Matrix.ext; unfold raw34676step1 raw34676step0; decide +kernel
      have hl : raw34676step0Labels = labelEmbedding9 ∘ raw34676step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34676step0 raw34676step0Labels raw34676step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4833 node4833Labels := by rfl

theorem canonical34677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34677 raw34677Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw34677 raw34677Labels = mixedMoment B raw34677step0 raw34677step0Labels := by
      have ha : raw34677step0 = (fun i j => raw34677 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34677step0 raw34677; decide +kernel
      have hl : raw34677step0Labels = raw34677Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34677 raw34677Labels permutation154 permutation6
    mixedMoment B raw34677step0 raw34677step0Labels = mixedMoment B raw34677step1 raw34677step1Labels := by
      have ha : raw34677step1 = raw34677step0 := by apply Matrix.ext; unfold raw34677step1 raw34677step0; decide +kernel
      have hl : raw34677step0Labels = labelEmbedding9 ∘ raw34677step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34677step0 raw34677step0Labels raw34677step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

theorem canonical34678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34678 raw34678Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw34678 raw34678Labels = mixedMoment B raw34678step0 raw34678step0Labels := by
      have ha : raw34678step0 = (fun i j => raw34678 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34678step0 raw34678; decide +kernel
      have hl : raw34678step0Labels = raw34678Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34678 raw34678Labels permutation160 permutation6
    mixedMoment B raw34678step0 raw34678step0Labels = mixedMoment B raw34678step1 raw34678step1Labels := by
      have ha : raw34678step1 = raw34678step0 := by apply Matrix.ext; unfold raw34678step1 raw34678step0; decide +kernel
      have hl : raw34678step0Labels = labelEmbedding9 ∘ raw34678step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34678step0 raw34678step0Labels raw34678step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

theorem canonical34679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34679 raw34679Labels = mixedMoment B node4859 node4859Labels := by
  calc
    mixedMoment B raw34679 raw34679Labels = mixedMoment B raw34679step0 raw34679step0Labels := by
      have ha : raw34679step0 = (fun i j => raw34679 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34679step0 raw34679; decide +kernel
      have hl : raw34679step0Labels = raw34679Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34679 raw34679Labels permutation224 permutation4
    mixedMoment B raw34679step0 raw34679step0Labels = mixedMoment B raw34679step1 raw34679step1Labels := by
      have ha : raw34679step1 = -raw34679step0 := by apply Matrix.ext; change ∀ i j, raw34679step1 i j = -(raw34679step0 i j); unfold raw34679step1 raw34679step0; decide +kernel
      have hl : raw34679step1Labels = raw34679step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34679step1 raw34679step1Labels = mixedMoment B raw34679step2 raw34679step2Labels := by
      have ha : raw34679step2 = raw34679step1 := by apply Matrix.ext; unfold raw34679step2 raw34679step1; decide +kernel
      have hl : raw34679step1Labels = labelEmbedding7 ∘ raw34679step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34679step1 raw34679step1Labels raw34679step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4859 node4859Labels := by rfl

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

theorem canonical1245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1245 raw1245Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw1245 raw1245Labels = mixedMoment B raw1245step0 raw1245step0Labels := by
      have ha : raw1245step0 = (fun i j => raw1245 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1245step0 raw1245; decide +kernel
      have hl : raw1245step0Labels = raw1245Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1245 raw1245Labels permutation152 permutation4
    mixedMoment B raw1245step0 raw1245step0Labels = mixedMoment B raw1245step1 raw1245step1Labels := by
      have ha : raw1245step1 = raw1245step0 := by apply Matrix.ext; unfold raw1245step1 raw1245step0; decide +kernel
      have hl : raw1245step0Labels = labelEmbedding7 ∘ raw1245step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1245step0 raw1245step0Labels raw1245step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

theorem canonical1246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1246 raw1246Labels = mixedMoment B node1034 node1034Labels := by
  calc
    mixedMoment B raw1246 raw1246Labels = mixedMoment B raw1246step0 raw1246step0Labels := by
      have ha : raw1246step0 = (fun i j => raw1246 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1246step0 raw1246; decide +kernel
      have hl : raw1246step0Labels = raw1246Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1246 raw1246Labels permutation152 permutation4
    _ = mixedMoment B node1034 node1034Labels := by rfl

theorem canonical1247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1247 raw1247Labels = mixedMoment B node1644 node1644Labels := by
  calc
    mixedMoment B raw1247 raw1247Labels = mixedMoment B raw1247step0 raw1247step0Labels := by
      have ha : raw1247step0 = (fun i j => raw1247 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1247step0 raw1247; decide +kernel
      have hl : raw1247step0Labels = raw1247Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1247 raw1247Labels permutation176 permutation6
    mixedMoment B raw1247step0 raw1247step0Labels = mixedMoment B raw1247step1 raw1247step1Labels := by
      have ha : raw1247step1 = -raw1247step0 := by apply Matrix.ext; change ∀ i j, raw1247step1 i j = -(raw1247step0 i j); unfold raw1247step1 raw1247step0; decide +kernel
      have hl : raw1247step1Labels = raw1247step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1247step1 raw1247step1Labels = mixedMoment B raw1247step2 raw1247step2Labels := by
      have ha : raw1247step2 = raw1247step1 := by apply Matrix.ext; unfold raw1247step2 raw1247step1; decide +kernel
      have hl : raw1247step1Labels = labelEmbedding1 ∘ raw1247step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1247step1 raw1247step1Labels raw1247step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1644 node1644Labels := by rfl

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

theorem singleton4451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4451 node4451Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1034 node1034Labels + mixedMoment B node1644 node1644Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1245 singletonSmall4451
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4451) = raw1245Labels := by decide +kernel
  rw [hl, canonical1245 B hB] at h
  have hc0 : mixedMoment B raw1245 (Fin.cases (0 : Fin 2) singletonSmall4451) =
      mixedMoment B node1034 node1034Labels := by
    have ha : raw1245 = raw1246 := by apply Matrix.ext; unfold raw1245 raw1246; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4451 = raw1246Labels := by decide +kernel
    rw [ha, hj, canonical1246 B hB]
  have hc1 : mixedMoment B raw1245 (Fin.cases (1 : Fin 2) singletonSmall4451) =
      mixedMoment B node1644 node1644Labels := by
    have ha : raw1245 = raw1247 := by apply Matrix.ext; unfold raw1245 raw1247; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4451 = raw1247Labels := by decide +kernel
    rw [ha, hj, canonical1247 B hB]
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

theorem singleton4859 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4859 node4859Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2100 node2100Labels + mixedMoment B node2100 node2100Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1779 singletonSmall4859
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4859) = raw1779Labels := by decide +kernel
  rw [hl, canonical1779 B hB] at h
  have hc0 : mixedMoment B raw1779 (Fin.cases (0 : Fin 2) singletonSmall4859) =
      mixedMoment B node2100 node2100Labels := by
    have ha : raw1779 = raw1780 := by apply Matrix.ext; unfold raw1779 raw1780; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4859 = raw1780Labels := by decide +kernel
    rw [ha, hj, canonical1780 B hB]
  have hc1 : mixedMoment B raw1779 (Fin.cases (1 : Fin 2) singletonSmall4859) =
      mixedMoment B node2100 node2100Labels := by
    have ha : raw1779 = raw1781 := by apply Matrix.ext; unfold raw1779 raw1781; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4859 = raw1781Labels := by decide +kernel
    rw [ha, hj, canonical1781 B hB]
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

theorem singleton5202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5202 node5202Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2880 node2880Labels + mixedMoment B node3617 node3617Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2226 singletonSmall5202
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5202) = raw2226Labels := by decide +kernel
  rw [hl, canonical2226 B hB] at h
  have hc0 : mixedMoment B raw2226 (Fin.cases (0 : Fin 2) singletonSmall5202) =
      mixedMoment B node2880 node2880Labels := by
    have ha : raw2226 = raw2227 := by apply Matrix.ext; unfold raw2226 raw2227; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5202 = raw2227Labels := by decide +kernel
    rw [ha, hj, canonical2227 B hB]
  have hc1 : mixedMoment B raw2226 (Fin.cases (1 : Fin 2) singletonSmall5202) =
      mixedMoment B node3617 node3617Labels := by
    have ha : raw2226 = raw2228 := by apply Matrix.ext; unfold raw2226 raw2228; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5202 = raw2228Labels := by decide +kernel
    rw [ha, hj, canonical2228 B hB]
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

theorem sound1034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1034 node1034Labels = Sparse.eval nodeValue1034 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1034) = mixedMoment B node1034 node1034Labels := rfl
  simpa [nodeValue1034, Sparse.eval] using hc.symm

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

theorem sound1644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1644 node1644Labels = Sparse.eval nodeValue1644 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1644) = mixedMoment B node1644 node1644Labels := rfl
  simpa [nodeValue1644, Sparse.eval] using hc.symm

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

theorem sound2100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2100 node2100Labels = Sparse.eval nodeValue2100 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2100) = mixedMoment B node2100 node2100Labels := rfl
  simpa [nodeValue2100, Sparse.eval] using hc.symm

theorem sound2105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2105 node2105Labels = Sparse.eval nodeValue2105 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2105) = mixedMoment B node2105 node2105Labels := rfl
  simpa [nodeValue2105, Sparse.eval] using hc.symm

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

theorem sound2241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2241 node2241Labels = Sparse.eval nodeValue2241 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2241) = mixedMoment B node2241 node2241Labels := rfl
  simpa [nodeValue2241, Sparse.eval] using hc.symm

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

theorem sound2880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2880 node2880Labels = Sparse.eval nodeValue2880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2880) = mixedMoment B node2880 node2880Labels := rfl
  simpa [nodeValue2880, Sparse.eval] using hc.symm

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

theorem sound3617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3617 node3617Labels = Sparse.eval nodeValue3617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3617) = mixedMoment B node3617 node3617Labels := rfl
  simpa [nodeValue3617, Sparse.eval] using hc.symm

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

theorem sound4436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4436 node4436Labels = Sparse.eval nodeValue4436 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4436) = mixedMoment B node4436 node4436Labels := rfl
  simpa [nodeValue4436, Sparse.eval] using hc.symm

theorem sound4441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4441 node4441Labels = Sparse.eval nodeValue4441 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4441) = mixedMoment B node4441 node4441Labels := rfl
  simpa [nodeValue4441, Sparse.eval] using hc.symm

theorem sound4451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4451 node4451Labels = Sparse.eval nodeValue4451 (mixedVector B) := by
  have h := singleton4451 B _hB
  rw [sound1034 B _hB _hF, sound1644 B _hB _hF] at h
  norm_num [nodeValue4451, nodeValue1034, nodeValue1644, Sparse.eval] at h ⊢
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

theorem zero4833 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4833 node4833Labels = 0 := by
  exact mixedMoment_order_one B hB node4833 node4833Labels 1
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

theorem sound4831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4831 node4831Labels = Sparse.eval nodeValue4831 (mixedVector B) := by
  have h := singleton4831 B _hB
  rw [sound2051 B _hB _hF, sound2191 B _hB _hF] at h
  norm_num [nodeValue4831, nodeValue2051, nodeValue2191, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4833 node4833Labels = Sparse.eval nodeValue4833 (mixedVector B) := by
  simpa only [nodeValue4833, Sparse.eval_nil] using zero4833 B _hB _hF

theorem sound4849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4849 node4849Labels = Sparse.eval nodeValue4849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4849) = mixedMoment B node4849 node4849Labels := rfl
  simpa [nodeValue4849, Sparse.eval] using hc.symm

theorem sound4854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4854 node4854Labels = Sparse.eval nodeValue4854 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4854) = mixedMoment B node4854 node4854Labels := rfl
  simpa [nodeValue4854, Sparse.eval] using hc.symm

theorem sound4859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4859 node4859Labels = Sparse.eval nodeValue4859 (mixedVector B) := by
  have h := singleton4859 B _hB
  rw [sound2100 B _hB _hF] at h
  norm_num [nodeValue4859, nodeValue2100, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4863 node4863Labels = Sparse.eval nodeValue4863 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4863) = mixedMoment B node4863 node4863Labels := rfl
  simpa [nodeValue4863, Sparse.eval] using hc.symm

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

theorem sound4878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4878 node4878Labels = Sparse.eval nodeValue4878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4878) = mixedMoment B node4878 node4878Labels := rfl
  simpa [nodeValue4878, Sparse.eval] using hc.symm

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

theorem sound5197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5197 node5197Labels = Sparse.eval nodeValue5197 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5197) = mixedMoment B node5197 node5197Labels := rfl
  simpa [nodeValue5197, Sparse.eval] using hc.symm

theorem sound5202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5202 node5202Labels = Sparse.eval nodeValue5202 (mixedVector B) := by
  have h := singleton5202 B _hB
  rw [sound2880 B _hB _hF, sound3617 B _hB _hF] at h
  norm_num [nodeValue5202, nodeValue2880, nodeValue3617, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources78
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2511 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2511 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2511 + difference 0 1) (sourceB2511 + difference 1 0) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA2511 + difference 0 1) (sourceB2511 + difference 1 0) sourceC2511) = raw34560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34560; decide +kernel
    rw [ha]
    exact (canonical34560 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2511 + difference 0 2) (sourceB2511 + difference 2 0) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA2511 + difference 0 2) (sourceB2511 + difference 2 0) sourceC2511) = raw34654 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34654; decide +kernel
    rw [ha]
    exact (canonical34654 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2511 + difference 0 3) (sourceB2511 + difference 3 0) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA2511 + difference 0 3) (sourceB2511 + difference 3 0) sourceC2511) = raw34655 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34655; decide +kernel
    rw [ha]
    exact (canonical34655 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2511 + difference 0 4) (sourceB2511 + difference 4 0) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5197) := by
    have ha : (tripleCharges (sourceA2511 + difference 0 4) (sourceB2511 + difference 4 0) sourceC2511) = raw34656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34656; decide +kernel
    rw [ha]
    exact (canonical34656 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2511 + difference 0 5) (sourceB2511 + difference 5 0) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5197) := by
    have ha : (tripleCharges (sourceA2511 + difference 0 5) (sourceB2511 + difference 5 0) sourceC2511) = raw34539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34539; decide +kernel
    rw [ha]
    exact (canonical34539 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2511 + difference 1 0) (sourceB2511 + difference 0 1) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4441) := by
    have ha : (tripleCharges (sourceA2511 + difference 1 0) (sourceB2511 + difference 0 1) sourceC2511) = raw34657 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34657; decide +kernel
    rw [ha]
    exact (canonical34657 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2511 + difference 1 2) (sourceB2511 + difference 2 1) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4878) := by
    have ha : (tripleCharges (sourceA2511 + difference 1 2) (sourceB2511 + difference 2 1) sourceC2511) = raw34658 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34658; decide +kernel
    rw [ha]
    exact (canonical34658 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2511 + difference 1 3) (sourceB2511 + difference 3 1) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4878) := by
    have ha : (tripleCharges (sourceA2511 + difference 1 3) (sourceB2511 + difference 3 1) sourceC2511) = raw34659 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34659; decide +kernel
    rw [ha]
    exact (canonical34659 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2511 + difference 1 4) (sourceB2511 + difference 4 1) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4854) := by
    have ha : (tripleCharges (sourceA2511 + difference 1 4) (sourceB2511 + difference 4 1) sourceC2511) = raw34660 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34660; decide +kernel
    rw [ha]
    exact (canonical34660 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2511 + difference 1 5) (sourceB2511 + difference 5 1) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4854) := by
    have ha : (tripleCharges (sourceA2511 + difference 1 5) (sourceB2511 + difference 5 1) sourceC2511) = raw34661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34661; decide +kernel
    rw [ha]
    exact (canonical34661 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2511 + difference 2 0) (sourceB2511 + difference 0 2) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4436) := by
    have ha : (tripleCharges (sourceA2511 + difference 2 0) (sourceB2511 + difference 0 2) sourceC2511) = raw34662 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34662; decide +kernel
    rw [ha]
    exact (canonical34662 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2511 + difference 2 1) (sourceB2511 + difference 1 2) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA2511 + difference 2 1) (sourceB2511 + difference 1 2) sourceC2511) = raw34663 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34663; decide +kernel
    rw [ha]
    exact (canonical34663 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2511 + difference 2 3) (sourceB2511 + difference 3 2) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4863) := by
    have ha : (tripleCharges (sourceA2511 + difference 2 3) (sourceB2511 + difference 3 2) sourceC2511) = raw34664 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34664; decide +kernel
    rw [ha]
    exact (canonical34664 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2511 + difference 2 4) (sourceB2511 + difference 4 2) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4849) := by
    have ha : (tripleCharges (sourceA2511 + difference 2 4) (sourceB2511 + difference 4 2) sourceC2511) = raw34665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34665; decide +kernel
    rw [ha]
    exact (canonical34665 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2511 + difference 2 5) (sourceB2511 + difference 5 2) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4849) := by
    have ha : (tripleCharges (sourceA2511 + difference 2 5) (sourceB2511 + difference 5 2) sourceC2511) = raw34666 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34666; decide +kernel
    rw [ha]
    exact (canonical34666 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2511 + difference 3 0) (sourceB2511 + difference 0 3) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4436) := by
    have ha : (tripleCharges (sourceA2511 + difference 3 0) (sourceB2511 + difference 0 3) sourceC2511) = raw34667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34667; decide +kernel
    rw [ha]
    exact (canonical34667 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2511 + difference 3 1) (sourceB2511 + difference 1 3) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA2511 + difference 3 1) (sourceB2511 + difference 1 3) sourceC2511) = raw34668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34668; decide +kernel
    rw [ha]
    exact (canonical34668 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2511 + difference 3 2) (sourceB2511 + difference 2 3) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4863) := by
    have ha : (tripleCharges (sourceA2511 + difference 3 2) (sourceB2511 + difference 2 3) sourceC2511) = raw34669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34669; decide +kernel
    rw [ha]
    exact (canonical34669 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2511 + difference 3 4) (sourceB2511 + difference 4 3) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4849) := by
    have ha : (tripleCharges (sourceA2511 + difference 3 4) (sourceB2511 + difference 4 3) sourceC2511) = raw34670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34670; decide +kernel
    rw [ha]
    exact (canonical34670 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2511 + difference 3 5) (sourceB2511 + difference 5 3) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4849) := by
    have ha : (tripleCharges (sourceA2511 + difference 3 5) (sourceB2511 + difference 5 3) sourceC2511) = raw34671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34671; decide +kernel
    rw [ha]
    exact (canonical34671 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2511 + difference 4 0) (sourceB2511 + difference 0 4) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA2511 + difference 4 0) (sourceB2511 + difference 0 4) sourceC2511) = raw34672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34672; decide +kernel
    rw [ha]
    exact (canonical34672 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2511 + difference 4 1) (sourceB2511 + difference 1 4) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA2511 + difference 4 1) (sourceB2511 + difference 1 4) sourceC2511) = raw34556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34556; decide +kernel
    rw [ha]
    exact (canonical34556 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2511 + difference 4 2) (sourceB2511 + difference 2 4) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA2511 + difference 4 2) (sourceB2511 + difference 2 4) sourceC2511) = raw34673 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34673; decide +kernel
    rw [ha]
    exact (canonical34673 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2511 + difference 4 3) (sourceB2511 + difference 3 4) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA2511 + difference 4 3) (sourceB2511 + difference 3 4) sourceC2511) = raw34674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34674; decide +kernel
    rw [ha]
    exact (canonical34674 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2511 + difference 4 5) (sourceB2511 + difference 5 4) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4859) := by
    have ha : (tripleCharges (sourceA2511 + difference 4 5) (sourceB2511 + difference 5 4) sourceC2511) = raw34536 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34536; decide +kernel
    rw [ha]
    exact (canonical34536 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2511 + difference 5 0) (sourceB2511 + difference 0 5) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA2511 + difference 5 0) (sourceB2511 + difference 0 5) sourceC2511) = raw34675 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34675; decide +kernel
    rw [ha]
    exact (canonical34675 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2511 + difference 5 1) (sourceB2511 + difference 1 5) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA2511 + difference 5 1) (sourceB2511 + difference 1 5) sourceC2511) = raw34676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34676; decide +kernel
    rw [ha]
    exact (canonical34676 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2511 + difference 5 2) (sourceB2511 + difference 2 5) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA2511 + difference 5 2) (sourceB2511 + difference 2 5) sourceC2511) = raw34677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34677; decide +kernel
    rw [ha]
    exact (canonical34677 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2511 + difference 5 3) (sourceB2511 + difference 3 5) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA2511 + difference 5 3) (sourceB2511 + difference 3 5) sourceC2511) = raw34678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34678; decide +kernel
    rw [ha]
    exact (canonical34678 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2511 + difference 5 4) (sourceB2511 + difference 4 5) sourceC2511) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4859) := by
    have ha : (tripleCharges (sourceA2511 + difference 5 4) (sourceB2511 + difference 4 5) sourceC2511) = raw34679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2511 sourceB2511 sourceC2511 difference raw34679; decide +kernel
    rw [ha]
    exact (canonical34679 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2511 sourceB2511 sourceC2511
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2511, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2022 : Integer.Sparse.reindex keyMap MixedData.row2022 = numericRow2022 := by decide +kernel

theorem numericCheck2022 (x : Master → ℝ) : Integer.Sparse.eval numericRow2022 x =
    (17280 : ℝ) * reducedSource2022 x := by
  norm_num [numericRow2022, reducedSource2022, Integer.Sparse.eval, Sparse.eval, nodeValue4436, nodeValue4441, nodeValue4451, nodeValue4831, nodeValue4833, nodeValue4849, nodeValue4854, nodeValue4859, nodeValue4863, nodeValue4864, nodeValue4878, nodeValue5167, nodeValue5197, nodeValue5202]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2022 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2022 (mixedVector B) = 0 := by
  have h4436 : mixedVector B (Sum.inr 4436) = Sparse.eval nodeValue4436 (mixedVector B) := by
    change mixedMoment B node4436 node4436Labels = _
    exact sound4436 B hB hF
  have h4441 : mixedVector B (Sum.inr 4441) = Sparse.eval nodeValue4441 (mixedVector B) := by
    change mixedMoment B node4441 node4441Labels = _
    exact sound4441 B hB hF
  have h4451 : mixedVector B (Sum.inr 4451) = Sparse.eval nodeValue4451 (mixedVector B) := by
    change mixedMoment B node4451 node4451Labels = _
    exact sound4451 B hB hF
  have h4831 : mixedVector B (Sum.inr 4831) = Sparse.eval nodeValue4831 (mixedVector B) := by
    change mixedMoment B node4831 node4831Labels = _
    exact sound4831 B hB hF
  have h4833 : mixedVector B (Sum.inr 4833) = Sparse.eval nodeValue4833 (mixedVector B) := by
    change mixedMoment B node4833 node4833Labels = _
    exact sound4833 B hB hF
  have h4849 : mixedVector B (Sum.inr 4849) = Sparse.eval nodeValue4849 (mixedVector B) := by
    change mixedMoment B node4849 node4849Labels = _
    exact sound4849 B hB hF
  have h4854 : mixedVector B (Sum.inr 4854) = Sparse.eval nodeValue4854 (mixedVector B) := by
    change mixedMoment B node4854 node4854Labels = _
    exact sound4854 B hB hF
  have h4859 : mixedVector B (Sum.inr 4859) = Sparse.eval nodeValue4859 (mixedVector B) := by
    change mixedMoment B node4859 node4859Labels = _
    exact sound4859 B hB hF
  have h4863 : mixedVector B (Sum.inr 4863) = Sparse.eval nodeValue4863 (mixedVector B) := by
    change mixedMoment B node4863 node4863Labels = _
    exact sound4863 B hB hF
  have h4864 : mixedVector B (Sum.inr 4864) = Sparse.eval nodeValue4864 (mixedVector B) := by
    change mixedMoment B node4864 node4864Labels = _
    exact sound4864 B hB hF
  have h4878 : mixedVector B (Sum.inr 4878) = Sparse.eval nodeValue4878 (mixedVector B) := by
    change mixedMoment B node4878 node4878Labels = _
    exact sound4878 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167_e B hB hF
  have h5197 : mixedVector B (Sum.inr 5197) = Sparse.eval nodeValue5197 (mixedVector B) := by
    change mixedMoment B node5197 node5197Labels = _
    exact sound5197 B hB hF
  have h5202 : mixedVector B (Sum.inr 5202) = Sparse.eval nodeValue5202 (mixedVector B) := by
    change mixedMoment B node5202 node5202Labels = _
    exact sound5202 B hB hF
  simpa only [sourceForm2511, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4436, h4441, h4451, h4831, h4833, h4849, h4854, h4859, h4863, h4864, h4878, h5167, h5197, h5202, reducedSource2022] using sourceEq2511 B hB

theorem rowSound2022_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2022 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2022, numericCheck2022, reducedZero2022 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022_e_oai
