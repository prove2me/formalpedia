-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound682_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T02:13:49.115296+00:00
-- url     : https://prove2.me/submissions/c7ce87bf-f1da-4d6e-afdd-738c6296a554

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12998 raw12998Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw12998 raw12998Labels = mixedMoment B raw12998step0 raw12998step0Labels := by
      have ha : raw12998step0 = (fun i j => raw12998 (permutation346 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12998step0 raw12998; decide +kernel
      have hl : raw12998step0Labels = raw12998Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12998 raw12998Labels permutation346 permutation6
    mixedMoment B raw12998step0 raw12998step0Labels = mixedMoment B raw12998step1 raw12998step1Labels := by
      have ha : raw12998step1 = -raw12998step0 := by apply Matrix.ext; change ∀ i j, raw12998step1 i j = -(raw12998step0 i j); unfold raw12998step1 raw12998step0; decide +kernel
      have hl : raw12998step1Labels = raw12998step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12998step1 raw12998step1Labels = mixedMoment B raw12998step2 raw12998step2Labels := by
      have ha : raw12998step2 = raw12998step1 := by apply Matrix.ext; unfold raw12998step2 raw12998step1; decide +kernel
      have hl : raw12998step1Labels = labelEmbedding9 ∘ raw12998step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12998step1 raw12998step1Labels raw12998step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical12999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12999 raw12999Labels = mixedMoment B node5474 node5474Labels := by
  calc
    mixedMoment B raw12999 raw12999Labels = mixedMoment B raw12999step0 raw12999step0Labels := by
      have hz : ∀ j, raw12999 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12999step0 = (fun i j => raw12999 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12999step0 raw12999; decide +kernel
      have hl : raw12999step0Labels = raw12999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12999 raw12999Labels permutation265 hz
    _ = mixedMoment B node5474 node5474Labels := by rfl

theorem canonical13000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13000 raw13000Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw13000 raw13000Labels = mixedMoment B raw13000step0 raw13000step0Labels := by
      have hz : ∀ j, raw13000 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13000step0 = (fun i j => raw13000 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13000step0 raw13000; decide +kernel
      have hl : raw13000step0Labels = raw13000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13000 raw13000Labels permutation265 hz
    mixedMoment B raw13000step0 raw13000step0Labels = mixedMoment B raw13000step1 raw13000step1Labels := by
      have ha : raw13000step1 = (fun i j => raw13000step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13000step1 raw13000step0; decide +kernel
      have hl : raw13000step1Labels = raw13000step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13000step0 raw13000step0Labels permutation59 permutation6
    mixedMoment B raw13000step1 raw13000step1Labels = mixedMoment B raw13000step2 raw13000step2Labels := by
      have ha : raw13000step2 = -raw13000step1 := by apply Matrix.ext; change ∀ i j, raw13000step2 i j = -(raw13000step1 i j); unfold raw13000step2 raw13000step1; decide +kernel
      have hl : raw13000step2Labels = raw13000step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13000step2 raw13000step2Labels = mixedMoment B raw13000step3 raw13000step3Labels := by
      have ha : raw13000step3 = raw13000step2 := by apply Matrix.ext; unfold raw13000step3 raw13000step2; decide +kernel
      have hl : raw13000step2Labels = labelEmbedding9 ∘ raw13000step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13000step2 raw13000step2Labels raw13000step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical13001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13001 raw13001Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw13001 raw13001Labels = mixedMoment B raw13001step0 raw13001step0Labels := by
      have hz : ∀ j, raw13001 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13001step0 = (fun i j => raw13001 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13001step0 raw13001; decide +kernel
      have hl : raw13001step0Labels = raw13001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13001 raw13001Labels permutation265 hz
    mixedMoment B raw13001step0 raw13001step0Labels = mixedMoment B raw13001step1 raw13001step1Labels := by
      have ha : raw13001step1 = (fun i j => raw13001step0 (permutation57 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13001step1 raw13001step0; decide +kernel
      have hl : raw13001step1Labels = raw13001step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13001step0 raw13001step0Labels permutation57 permutation6
    mixedMoment B raw13001step1 raw13001step1Labels = mixedMoment B raw13001step2 raw13001step2Labels := by
      have ha : raw13001step2 = -raw13001step1 := by apply Matrix.ext; change ∀ i j, raw13001step2 i j = -(raw13001step1 i j); unfold raw13001step2 raw13001step1; decide +kernel
      have hl : raw13001step2Labels = raw13001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13001step2 raw13001step2Labels = mixedMoment B raw13001step3 raw13001step3Labels := by
      have ha : raw13001step3 = raw13001step2 := by apply Matrix.ext; unfold raw13001step3 raw13001step2; decide +kernel
      have hl : raw13001step2Labels = labelEmbedding9 ∘ raw13001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13001step2 raw13001step2Labels raw13001step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical13002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13002 raw13002Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw13002 raw13002Labels = mixedMoment B raw13002step0 raw13002step0Labels := by
      have hz : ∀ j, raw13002 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13002step0 = (fun i j => raw13002 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13002step0 raw13002; decide +kernel
      have hl : raw13002step0Labels = raw13002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13002 raw13002Labels permutation265 hz
    mixedMoment B raw13002step0 raw13002step0Labels = mixedMoment B raw13002step1 raw13002step1Labels := by
      have ha : raw13002step1 = (fun i j => raw13002step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13002step1 raw13002step0; decide +kernel
      have hl : raw13002step1Labels = raw13002step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13002step0 raw13002step0Labels permutation56 permutation6
    mixedMoment B raw13002step1 raw13002step1Labels = mixedMoment B raw13002step2 raw13002step2Labels := by
      have ha : raw13002step2 = -raw13002step1 := by apply Matrix.ext; change ∀ i j, raw13002step2 i j = -(raw13002step1 i j); unfold raw13002step2 raw13002step1; decide +kernel
      have hl : raw13002step2Labels = raw13002step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13002step2 raw13002step2Labels = mixedMoment B raw13002step3 raw13002step3Labels := by
      have ha : raw13002step3 = raw13002step2 := by apply Matrix.ext; unfold raw13002step3 raw13002step2; decide +kernel
      have hl : raw13002step2Labels = labelEmbedding9 ∘ raw13002step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13002step2 raw13002step2Labels raw13002step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical13003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13003 raw13003Labels = mixedMoment B node4473 node4473Labels := by
  calc
    mixedMoment B raw13003 raw13003Labels = mixedMoment B raw13003step0 raw13003step0Labels := by
      have ha : raw13003step0 = (fun i j => raw13003 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13003step0 raw13003; decide +kernel
      have hl : raw13003step0Labels = raw13003Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13003 raw13003Labels permutation185 permutation3
    mixedMoment B raw13003step0 raw13003step0Labels = mixedMoment B raw13003step1 raw13003step1Labels := by
      have ha : raw13003step1 = raw13003step0 := by apply Matrix.ext; unfold raw13003step1 raw13003step0; decide +kernel
      have hl : raw13003step0Labels = labelEmbedding6 ∘ raw13003step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13003step0 raw13003step0Labels raw13003step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4473 node4473Labels := by rfl

theorem canonical13004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13004 raw13004Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw13004 raw13004Labels = mixedMoment B raw13004step0 raw13004step0Labels := by
      have ha : raw13004step0 = (fun i j => raw13004 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13004step0 raw13004; decide +kernel
      have hl : raw13004step0Labels = raw13004Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13004 raw13004Labels permutation185 permutation3
    mixedMoment B raw13004step0 raw13004step0Labels = mixedMoment B raw13004step1 raw13004step1Labels := by
      have ha : raw13004step1 = raw13004step0 := by apply Matrix.ext; unfold raw13004step1 raw13004step0; decide +kernel
      have hl : raw13004step0Labels = labelEmbedding6 ∘ raw13004step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13004step0 raw13004step0Labels raw13004step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

theorem canonical13005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13005 raw13005Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw13005 raw13005Labels = mixedMoment B raw13005step0 raw13005step0Labels := by
      have ha : raw13005step0 = (fun i j => raw13005 (permutation209 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13005step0 raw13005; decide +kernel
      have hl : raw13005step0Labels = raw13005Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13005 raw13005Labels permutation209 permutation3
    mixedMoment B raw13005step0 raw13005step0Labels = mixedMoment B raw13005step1 raw13005step1Labels := by
      have ha : raw13005step1 = raw13005step0 := by apply Matrix.ext; unfold raw13005step1 raw13005step0; decide +kernel
      have hl : raw13005step0Labels = labelEmbedding6 ∘ raw13005step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13005step0 raw13005step0Labels raw13005step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical13006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13006 raw13006Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw13006 raw13006Labels = mixedMoment B raw13006step0 raw13006step0Labels := by
      have ha : raw13006step0 = (fun i j => raw13006 (permutation233 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13006step0 raw13006; decide +kernel
      have hl : raw13006step0Labels = raw13006Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13006 raw13006Labels permutation233 permutation3
    mixedMoment B raw13006step0 raw13006step0Labels = mixedMoment B raw13006step1 raw13006step1Labels := by
      have ha : raw13006step1 = raw13006step0 := by apply Matrix.ext; unfold raw13006step1 raw13006step0; decide +kernel
      have hl : raw13006step0Labels = labelEmbedding6 ∘ raw13006step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13006step0 raw13006step0Labels raw13006step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical13007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13007 raw13007Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw13007 raw13007Labels = mixedMoment B raw13007step0 raw13007step0Labels := by
      have ha : raw13007step0 = (fun i j => raw13007 (permutation255 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13007step0 raw13007; decide +kernel
      have hl : raw13007step0Labels = raw13007Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13007 raw13007Labels permutation255 permutation3
    mixedMoment B raw13007step0 raw13007step0Labels = mixedMoment B raw13007step1 raw13007step1Labels := by
      have ha : raw13007step1 = raw13007step0 := by apply Matrix.ext; unfold raw13007step1 raw13007step0; decide +kernel
      have hl : raw13007step0Labels = labelEmbedding6 ∘ raw13007step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13007step0 raw13007step0Labels raw13007step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical13008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13008 raw13008Labels = mixedMoment B node4494 node4494Labels := by
  calc
    mixedMoment B raw13008 raw13008Labels = mixedMoment B raw13008step0 raw13008step0Labels := by
      have hz : ∀ j, raw13008 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13008step0 = (fun i j => raw13008 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13008step0 raw13008; decide +kernel
      have hl : raw13008step0Labels = raw13008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13008 raw13008Labels permutation265 hz
    mixedMoment B raw13008step0 raw13008step0Labels = mixedMoment B raw13008step1 raw13008step1Labels := by
      have ha : raw13008step1 = (fun i j => raw13008step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13008step1 raw13008step0; decide +kernel
      have hl : raw13008step1Labels = raw13008step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13008step0 raw13008step0Labels permutation41 permutation3
    mixedMoment B raw13008step1 raw13008step1Labels = mixedMoment B raw13008step2 raw13008step2Labels := by
      have ha : raw13008step2 = raw13008step1 := by apply Matrix.ext; unfold raw13008step2 raw13008step1; decide +kernel
      have hl : raw13008step1Labels = labelEmbedding6 ∘ raw13008step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13008step1 raw13008step1Labels raw13008step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4494 node4494Labels := by rfl

theorem canonical13009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13009 raw13009Labels = mixedMoment B node5097 node5097Labels := by
  calc
    mixedMoment B raw13009 raw13009Labels = mixedMoment B raw13009step0 raw13009step0Labels := by
      have ha : raw13009step0 = (fun i j => raw13009 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13009step0 raw13009; decide +kernel
      have hl : raw13009step0Labels = raw13009Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13009 raw13009Labels permutation161 permutation3
    mixedMoment B raw13009step0 raw13009step0Labels = mixedMoment B raw13009step1 raw13009step1Labels := by
      have ha : raw13009step1 = raw13009step0 := by apply Matrix.ext; unfold raw13009step1 raw13009step0; decide +kernel
      have hl : raw13009step0Labels = labelEmbedding6 ∘ raw13009step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13009step0 raw13009step0Labels raw13009step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5097 node5097Labels := by rfl

theorem canonical13010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13010 raw13010Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw13010 raw13010Labels = mixedMoment B raw13010step0 raw13010step0Labels := by
      have hz : ∀ j, raw13010 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13010step0 = (fun i j => raw13010 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13010step0 raw13010; decide +kernel
      have hl : raw13010step0Labels = raw13010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13010 raw13010Labels permutation265 hz
    mixedMoment B raw13010step0 raw13010step0Labels = mixedMoment B raw13010step1 raw13010step1Labels := by
      have ha : raw13010step1 = (fun i j => raw13010step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13010step1 raw13010step0; decide +kernel
      have hl : raw13010step1Labels = raw13010step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13010step0 raw13010step0Labels permutation41 permutation3
    mixedMoment B raw13010step1 raw13010step1Labels = mixedMoment B raw13010step2 raw13010step2Labels := by
      have ha : raw13010step2 = raw13010step1 := by apply Matrix.ext; unfold raw13010step2 raw13010step1; decide +kernel
      have hl : raw13010step1Labels = labelEmbedding6 ∘ raw13010step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13010step1 raw13010step1Labels raw13010step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

theorem canonical13011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13011 raw13011Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw13011 raw13011Labels = mixedMoment B raw13011step0 raw13011step0Labels := by
      have hz : ∀ j, raw13011 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13011step0 = (fun i j => raw13011 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13011step0 raw13011; decide +kernel
      have hl : raw13011step0Labels = raw13011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13011 raw13011Labels permutation265 hz
    mixedMoment B raw13011step0 raw13011step0Labels = mixedMoment B raw13011step1 raw13011step1Labels := by
      have ha : raw13011step1 = (fun i j => raw13011step0 (permutation47 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13011step1 raw13011step0; decide +kernel
      have hl : raw13011step1Labels = raw13011step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13011step0 raw13011step0Labels permutation47 permutation3
    mixedMoment B raw13011step1 raw13011step1Labels = mixedMoment B raw13011step2 raw13011step2Labels := by
      have ha : raw13011step2 = raw13011step1 := by apply Matrix.ext; unfold raw13011step2 raw13011step1; decide +kernel
      have hl : raw13011step1Labels = labelEmbedding6 ∘ raw13011step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13011step1 raw13011step1Labels raw13011step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

theorem canonical13012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13012 raw13012Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw13012 raw13012Labels = mixedMoment B raw13012step0 raw13012step0Labels := by
      have hz : ∀ j, raw13012 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13012step0 = (fun i j => raw13012 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13012step0 raw13012; decide +kernel
      have hl : raw13012step0Labels = raw13012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13012 raw13012Labels permutation265 hz
    mixedMoment B raw13012step0 raw13012step0Labels = mixedMoment B raw13012step1 raw13012step1Labels := by
      have ha : raw13012step1 = (fun i j => raw13012step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13012step1 raw13012step0; decide +kernel
      have hl : raw13012step1Labels = raw13012step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13012step0 raw13012step0Labels permutation53 permutation3
    mixedMoment B raw13012step1 raw13012step1Labels = mixedMoment B raw13012step2 raw13012step2Labels := by
      have ha : raw13012step2 = raw13012step1 := by apply Matrix.ext; unfold raw13012step2 raw13012step1; decide +kernel
      have hl : raw13012step1Labels = labelEmbedding6 ∘ raw13012step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13012step1 raw13012step1Labels raw13012step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

theorem canonical13013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13013 raw13013Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw13013 raw13013Labels = mixedMoment B raw13013step0 raw13013step0Labels := by
      have hz : ∀ j, raw13013 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13013step0 = (fun i j => raw13013 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13013step0 raw13013; decide +kernel
      have hl : raw13013step0Labels = raw13013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13013 raw13013Labels permutation265 hz
    mixedMoment B raw13013step0 raw13013step0Labels = mixedMoment B raw13013step1 raw13013step1Labels := by
      have ha : raw13013step1 = (fun i j => raw13013step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13013step1 raw13013step0; decide +kernel
      have hl : raw13013step1Labels = raw13013step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13013step0 raw13013step0Labels permutation35 permutation3
    mixedMoment B raw13013step1 raw13013step1Labels = mixedMoment B raw13013step2 raw13013step2Labels := by
      have ha : raw13013step2 = raw13013step1 := by apply Matrix.ext; unfold raw13013step2 raw13013step1; decide +kernel
      have hl : raw13013step1Labels = labelEmbedding6 ∘ raw13013step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13013step1 raw13013step1Labels raw13013step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4474 node4474Labels := by rfl

theorem canonical13014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13014 raw13014Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw13014 raw13014Labels = mixedMoment B raw13014step0 raw13014step0Labels := by
      have ha : raw13014step0 = (fun i j => raw13014 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13014step0 raw13014; decide +kernel
      have hl : raw13014step0Labels = raw13014Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13014 raw13014Labels permutation155 permutation3
    mixedMoment B raw13014step0 raw13014step0Labels = mixedMoment B raw13014step1 raw13014step1Labels := by
      have ha : raw13014step1 = raw13014step0 := by apply Matrix.ext; unfold raw13014step1 raw13014step0; decide +kernel
      have hl : raw13014step0Labels = labelEmbedding6 ∘ raw13014step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13014step0 raw13014step0Labels raw13014step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

theorem canonical13015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13015 raw13015Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw13015 raw13015Labels = mixedMoment B raw13015step0 raw13015step0Labels := by
      have hz : ∀ j, raw13015 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13015step0 = (fun i j => raw13015 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13015step0 raw13015; decide +kernel
      have hl : raw13015step0Labels = raw13015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13015 raw13015Labels permutation265 hz
    mixedMoment B raw13015step0 raw13015step0Labels = mixedMoment B raw13015step1 raw13015step1Labels := by
      have ha : raw13015step1 = (fun i j => raw13015step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13015step1 raw13015step0; decide +kernel
      have hl : raw13015step1Labels = raw13015step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13015step0 raw13015step0Labels permutation35 permutation3
    mixedMoment B raw13015step1 raw13015step1Labels = mixedMoment B raw13015step2 raw13015step2Labels := by
      have ha : raw13015step2 = raw13015step1 := by apply Matrix.ext; unfold raw13015step2 raw13015step1; decide +kernel
      have hl : raw13015step1Labels = labelEmbedding6 ∘ raw13015step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13015step1 raw13015step1Labels raw13015step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

theorem canonical13016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13016 raw13016Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw13016 raw13016Labels = mixedMoment B raw13016step0 raw13016step0Labels := by
      have hz : ∀ j, raw13016 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13016step0 = (fun i j => raw13016 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13016step0 raw13016; decide +kernel
      have hl : raw13016step0Labels = raw13016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13016 raw13016Labels permutation265 hz
    mixedMoment B raw13016step0 raw13016step0Labels = mixedMoment B raw13016step1 raw13016step1Labels := by
      have ha : raw13016step1 = (fun i j => raw13016step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13016step1 raw13016step0; decide +kernel
      have hl : raw13016step1Labels = raw13016step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13016step0 raw13016step0Labels permutation45 permutation3
    mixedMoment B raw13016step1 raw13016step1Labels = mixedMoment B raw13016step2 raw13016step2Labels := by
      have ha : raw13016step2 = raw13016step1 := by apply Matrix.ext; unfold raw13016step2 raw13016step1; decide +kernel
      have hl : raw13016step1Labels = labelEmbedding6 ∘ raw13016step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13016step1 raw13016step1Labels raw13016step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical13017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13017 raw13017Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw13017 raw13017Labels = mixedMoment B raw13017step0 raw13017step0Labels := by
      have hz : ∀ j, raw13017 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13017step0 = (fun i j => raw13017 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13017step0 raw13017; decide +kernel
      have hl : raw13017step0Labels = raw13017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13017 raw13017Labels permutation265 hz
    mixedMoment B raw13017step0 raw13017step0Labels = mixedMoment B raw13017step1 raw13017step1Labels := by
      have ha : raw13017step1 = (fun i j => raw13017step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13017step1 raw13017step0; decide +kernel
      have hl : raw13017step1Labels = raw13017step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13017step0 raw13017step0Labels permutation51 permutation3
    mixedMoment B raw13017step1 raw13017step1Labels = mixedMoment B raw13017step2 raw13017step2Labels := by
      have ha : raw13017step2 = raw13017step1 := by apply Matrix.ext; unfold raw13017step2 raw13017step1; decide +kernel
      have hl : raw13017step1Labels = labelEmbedding6 ∘ raw13017step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13017step1 raw13017step1Labels raw13017step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical13018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13018 raw13018Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw13018 raw13018Labels = mixedMoment B raw13018step0 raw13018step0Labels := by
      have hz : ∀ j, raw13018 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13018step0 = (fun i j => raw13018 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13018step0 raw13018; decide +kernel
      have hl : raw13018step0Labels = raw13018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13018 raw13018Labels permutation265 hz
    mixedMoment B raw13018step0 raw13018step0Labels = mixedMoment B raw13018step1 raw13018step1Labels := by
      have ha : raw13018step1 = (fun i j => raw13018step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13018step1 raw13018step0; decide +kernel
      have hl : raw13018step1Labels = raw13018step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13018step0 raw13018step0Labels permutation33 permutation3
    mixedMoment B raw13018step1 raw13018step1Labels = mixedMoment B raw13018step2 raw13018step2Labels := by
      have ha : raw13018step2 = raw13018step1 := by apply Matrix.ext; unfold raw13018step2 raw13018step1; decide +kernel
      have hl : raw13018step1Labels = labelEmbedding6 ∘ raw13018step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13018step1 raw13018step1Labels raw13018step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4474 node4474Labels := by rfl

theorem canonical13019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13019 raw13019Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw13019 raw13019Labels = mixedMoment B raw13019step0 raw13019step0Labels := by
      have ha : raw13019step0 = (fun i j => raw13019 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13019step0 raw13019; decide +kernel
      have hl : raw13019step0Labels = raw13019Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13019 raw13019Labels permutation153 permutation3
    mixedMoment B raw13019step0 raw13019step0Labels = mixedMoment B raw13019step1 raw13019step1Labels := by
      have ha : raw13019step1 = raw13019step0 := by apply Matrix.ext; unfold raw13019step1 raw13019step0; decide +kernel
      have hl : raw13019step0Labels = labelEmbedding6 ∘ raw13019step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13019step0 raw13019step0Labels raw13019step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

theorem canonical13020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13020 raw13020Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw13020 raw13020Labels = mixedMoment B raw13020step0 raw13020step0Labels := by
      have hz : ∀ j, raw13020 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13020step0 = (fun i j => raw13020 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13020step0 raw13020; decide +kernel
      have hl : raw13020step0Labels = raw13020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13020 raw13020Labels permutation265 hz
    mixedMoment B raw13020step0 raw13020step0Labels = mixedMoment B raw13020step1 raw13020step1Labels := by
      have ha : raw13020step1 = (fun i j => raw13020step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13020step1 raw13020step0; decide +kernel
      have hl : raw13020step1Labels = raw13020step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13020step0 raw13020step0Labels permutation33 permutation3
    mixedMoment B raw13020step1 raw13020step1Labels = mixedMoment B raw13020step2 raw13020step2Labels := by
      have ha : raw13020step2 = raw13020step1 := by apply Matrix.ext; unfold raw13020step2 raw13020step1; decide +kernel
      have hl : raw13020step1Labels = labelEmbedding6 ∘ raw13020step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13020step1 raw13020step1Labels raw13020step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

theorem canonical13021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13021 raw13021Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw13021 raw13021Labels = mixedMoment B raw13021step0 raw13021step0Labels := by
      have hz : ∀ j, raw13021 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13021step0 = (fun i j => raw13021 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13021step0 raw13021; decide +kernel
      have hl : raw13021step0Labels = raw13021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13021 raw13021Labels permutation265 hz
    mixedMoment B raw13021step0 raw13021step0Labels = mixedMoment B raw13021step1 raw13021step1Labels := by
      have ha : raw13021step1 = (fun i j => raw13021step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13021step1 raw13021step0; decide +kernel
      have hl : raw13021step1Labels = raw13021step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13021step0 raw13021step0Labels permutation39 permutation3
    mixedMoment B raw13021step1 raw13021step1Labels = mixedMoment B raw13021step2 raw13021step2Labels := by
      have ha : raw13021step2 = raw13021step1 := by apply Matrix.ext; unfold raw13021step2 raw13021step1; decide +kernel
      have hl : raw13021step1Labels = labelEmbedding6 ∘ raw13021step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13021step1 raw13021step1Labels raw13021step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical13022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13022 raw13022Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw13022 raw13022Labels = mixedMoment B raw13022step0 raw13022step0Labels := by
      have hz : ∀ j, raw13022 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13022step0 = (fun i j => raw13022 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13022step0 raw13022; decide +kernel
      have hl : raw13022step0Labels = raw13022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13022 raw13022Labels permutation265 hz
    mixedMoment B raw13022step0 raw13022step0Labels = mixedMoment B raw13022step1 raw13022step1Labels := by
      have ha : raw13022step1 = (fun i j => raw13022step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13022step1 raw13022step0; decide +kernel
      have hl : raw13022step1Labels = raw13022step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13022step0 raw13022step0Labels permutation50 permutation3
    mixedMoment B raw13022step1 raw13022step1Labels = mixedMoment B raw13022step2 raw13022step2Labels := by
      have ha : raw13022step2 = raw13022step1 := by apply Matrix.ext; unfold raw13022step2 raw13022step1; decide +kernel
      have hl : raw13022step1Labels = labelEmbedding6 ∘ raw13022step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13022step1 raw13022step1Labels raw13022step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical13023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13023 raw13023Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw13023 raw13023Labels = mixedMoment B raw13023step0 raw13023step0Labels := by
      have hz : ∀ j, raw13023 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13023step0 = (fun i j => raw13023 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13023step0 raw13023; decide +kernel
      have hl : raw13023step0Labels = raw13023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13023 raw13023Labels permutation265 hz
    mixedMoment B raw13023step0 raw13023step0Labels = mixedMoment B raw13023step1 raw13023step1Labels := by
      have ha : raw13023step1 = (fun i j => raw13023step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13023step1 raw13023step0; decide +kernel
      have hl : raw13023step1Labels = raw13023step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13023step0 raw13023step0Labels permutation32 permutation3
    mixedMoment B raw13023step1 raw13023step1Labels = mixedMoment B raw13023step2 raw13023step2Labels := by
      have ha : raw13023step2 = raw13023step1 := by apply Matrix.ext; unfold raw13023step2 raw13023step1; decide +kernel
      have hl : raw13023step1Labels = labelEmbedding6 ∘ raw13023step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13023step1 raw13023step1Labels raw13023step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4474 node4474Labels := by rfl

theorem canonical13024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13024 raw13024Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw13024 raw13024Labels = mixedMoment B raw13024step0 raw13024step0Labels := by
      have ha : raw13024step0 = (fun i j => raw13024 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13024step0 raw13024; decide +kernel
      have hl : raw13024step0Labels = raw13024Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13024 raw13024Labels permutation152 permutation3
    mixedMoment B raw13024step0 raw13024step0Labels = mixedMoment B raw13024step1 raw13024step1Labels := by
      have ha : raw13024step1 = raw13024step0 := by apply Matrix.ext; unfold raw13024step1 raw13024step0; decide +kernel
      have hl : raw13024step0Labels = labelEmbedding6 ∘ raw13024step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13024step0 raw13024step0Labels raw13024step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

theorem canonical13025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13025 raw13025Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw13025 raw13025Labels = mixedMoment B raw13025step0 raw13025step0Labels := by
      have hz : ∀ j, raw13025 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13025step0 = (fun i j => raw13025 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13025step0 raw13025; decide +kernel
      have hl : raw13025step0Labels = raw13025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13025 raw13025Labels permutation265 hz
    mixedMoment B raw13025step0 raw13025step0Labels = mixedMoment B raw13025step1 raw13025step1Labels := by
      have ha : raw13025step1 = (fun i j => raw13025step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13025step1 raw13025step0; decide +kernel
      have hl : raw13025step1Labels = raw13025step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13025step0 raw13025step0Labels permutation32 permutation3
    mixedMoment B raw13025step1 raw13025step1Labels = mixedMoment B raw13025step2 raw13025step2Labels := by
      have ha : raw13025step2 = raw13025step1 := by apply Matrix.ext; unfold raw13025step2 raw13025step1; decide +kernel
      have hl : raw13025step1Labels = labelEmbedding6 ∘ raw13025step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13025step1 raw13025step1Labels raw13025step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

theorem canonical13026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13026 raw13026Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw13026 raw13026Labels = mixedMoment B raw13026step0 raw13026step0Labels := by
      have hz : ∀ j, raw13026 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13026step0 = (fun i j => raw13026 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13026step0 raw13026; decide +kernel
      have hl : raw13026step0Labels = raw13026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13026 raw13026Labels permutation265 hz
    mixedMoment B raw13026step0 raw13026step0Labels = mixedMoment B raw13026step1 raw13026step1Labels := by
      have ha : raw13026step1 = (fun i j => raw13026step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13026step1 raw13026step0; decide +kernel
      have hl : raw13026step1Labels = raw13026step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13026step0 raw13026step0Labels permutation38 permutation3
    mixedMoment B raw13026step1 raw13026step1Labels = mixedMoment B raw13026step2 raw13026step2Labels := by
      have ha : raw13026step2 = raw13026step1 := by apply Matrix.ext; unfold raw13026step2 raw13026step1; decide +kernel
      have hl : raw13026step1Labels = labelEmbedding6 ∘ raw13026step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13026step1 raw13026step1Labels raw13026step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical13027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13027 raw13027Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw13027 raw13027Labels = mixedMoment B raw13027step0 raw13027step0Labels := by
      have hz : ∀ j, raw13027 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13027step0 = (fun i j => raw13027 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13027step0 raw13027; decide +kernel
      have hl : raw13027step0Labels = raw13027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13027 raw13027Labels permutation265 hz
    mixedMoment B raw13027step0 raw13027step0Labels = mixedMoment B raw13027step1 raw13027step1Labels := by
      have ha : raw13027step1 = (fun i j => raw13027step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13027step1 raw13027step0; decide +kernel
      have hl : raw13027step1Labels = raw13027step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13027step0 raw13027step0Labels permutation44 permutation3
    mixedMoment B raw13027step1 raw13027step1Labels = mixedMoment B raw13027step2 raw13027step2Labels := by
      have ha : raw13027step2 = raw13027step1 := by apply Matrix.ext; unfold raw13027step2 raw13027step1; decide +kernel
      have hl : raw13027step1Labels = labelEmbedding6 ∘ raw13027step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13027step1 raw13027step1Labels raw13027step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2547 raw2547Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw2547 raw2547Labels = mixedMoment B raw2547step0 raw2547step0Labels := by
      have ha : raw2547step0 = (fun i j => raw2547 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2547step0 raw2547; decide +kernel
      have hl : raw2547step0Labels = raw2547Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2547 raw2547Labels permutation152 permutation5
    mixedMoment B raw2547step0 raw2547step0Labels = mixedMoment B raw2547step1 raw2547step1Labels := by
      have ha : raw2547step1 = raw2547step0 := by apply Matrix.ext; unfold raw2547step1 raw2547step0; decide +kernel
      have hl : raw2547step0Labels = labelEmbedding8 ∘ raw2547step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2547step0 raw2547step0Labels raw2547step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical2548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2548 raw2548Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw2548 raw2548Labels = mixedMoment B raw2548step0 raw2548step0Labels := by
      have ha : raw2548step0 = (fun i j => raw2548 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2548step0 raw2548; decide +kernel
      have hl : raw2548step0Labels = raw2548Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2548 raw2548Labels permutation152 permutation4
    _ = mixedMoment B node4025 node4025Labels := by rfl

theorem canonical2549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2549 raw2549Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw2549 raw2549Labels = mixedMoment B raw2549step0 raw2549step0Labels := by
      have ha : raw2549step0 = (fun i j => raw2549 (permutation216 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2549step0 raw2549; decide +kernel
      have hl : raw2549step0Labels = raw2549Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2549 raw2549Labels permutation216 permutation3
    mixedMoment B raw2549step0 raw2549step0Labels = mixedMoment B raw2549step1 raw2549step1Labels := by
      have ha : raw2549step1 = -raw2549step0 := by apply Matrix.ext; change ∀ i j, raw2549step1 i j = -(raw2549step0 i j); unfold raw2549step1 raw2549step0; decide +kernel
      have hl : raw2549step1Labels = raw2549step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2549step1 raw2549step1Labels = mixedMoment B raw2549step2 raw2549step2Labels := by
      have ha : raw2549step2 = raw2549step1 := by apply Matrix.ext; unfold raw2549step2 raw2549step1; decide +kernel
      have hl : raw2549step1Labels = labelEmbedding1 ∘ raw2549step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2549step1 raw2549step1Labels raw2549step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3909 node3909Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5447 node5447Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node4025 node4025Labels + mixedMoment B node3909 node3909Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2547 singletonSmall5447
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5447) = raw2547Labels := by decide +kernel
  rw [hl, canonical2547 B hB] at h
  have hc0 : mixedMoment B raw2547 (Fin.cases (0 : Fin 2) singletonSmall5447) =
      mixedMoment B node4025 node4025Labels := by
    have ha : raw2547 = raw2548 := by apply Matrix.ext; unfold raw2547 raw2548; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5447 = raw2548Labels := by decide +kernel
    rw [ha, hj, canonical2548 B hB]
  have hc1 : mixedMoment B raw2547 (Fin.cases (1 : Fin 2) singletonSmall5447) =
      mixedMoment B node3909 node3909Labels := by
    have ha : raw2547 = raw2549 := by apply Matrix.ext; unfold raw2547 raw2549; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5447 = raw2549Labels := by decide +kernel
    rw [ha, hj, canonical2549 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5474 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5474 node5474Labels = 0 := by
  exact mixedMoment_order_one B hB node5474 node5474Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3617 node3617Labels = Sparse.eval nodeValue3617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3617) = mixedMoment B node3617 node3617Labels := rfl
  simpa [nodeValue3617, Sparse.eval] using hc.symm

theorem sound3621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3621 node3621Labels = Sparse.eval nodeValue3621 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3621) = mixedMoment B node3621 node3621Labels := rfl
  simpa [nodeValue3621, Sparse.eval] using hc.symm

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

theorem sound3909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3909 node3909Labels = Sparse.eval nodeValue3909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3909) = mixedMoment B node3909 node3909Labels := rfl
  simpa [nodeValue3909, Sparse.eval] using hc.symm

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

theorem sound4025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4025 node4025Labels = Sparse.eval nodeValue4025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4025) = mixedMoment B node4025 node4025Labels := rfl
  simpa [nodeValue4025, Sparse.eval] using hc.symm

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

theorem sound4473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4473 node4473Labels = Sparse.eval nodeValue4473 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4473) = mixedMoment B node4473 node4473Labels := rfl
  simpa [nodeValue4473, Sparse.eval] using hc.symm

theorem sound4474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4474 node4474Labels = Sparse.eval nodeValue4474 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4474) = mixedMoment B node4474 node4474Labels := rfl
  simpa [nodeValue4474, Sparse.eval] using hc.symm

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

theorem sound4494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4494 node4494Labels = Sparse.eval nodeValue4494 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4494) = mixedMoment B node4494 node4494Labels := rfl
  simpa [nodeValue4494, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5085 node5085Labels = Sparse.eval nodeValue5085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5085) = mixedMoment B node5085 node5085Labels := rfl
  simpa [nodeValue5085, Sparse.eval] using hc.symm

theorem sound5097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5097 node5097Labels = Sparse.eval nodeValue5097 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5097) = mixedMoment B node5097 node5097Labels := rfl
  simpa [nodeValue5097, Sparse.eval] using hc.symm

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

theorem sound5202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5202 node5202Labels = Sparse.eval nodeValue5202 (mixedVector B) := by
  have h := singleton5202 B _hB
  rw [sound2880 B _hB _hF, sound3617 B _hB _hF] at h
  norm_num [nodeValue5202, nodeValue2880, nodeValue3617, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5265 node5265Labels = Sparse.eval nodeValue5265 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5265) = mixedMoment B node5265 node5265Labels := rfl
  simpa [nodeValue5265, Sparse.eval] using hc.symm

theorem sound5266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5266 node5266Labels = Sparse.eval nodeValue5266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5266) = mixedMoment B node5266 node5266Labels := rfl
  simpa [nodeValue5266, Sparse.eval] using hc.symm

theorem sound5270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5270 node5270Labels = Sparse.eval nodeValue5270 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5270) = mixedMoment B node5270 node5270Labels := rfl
  simpa [nodeValue5270, Sparse.eval] using hc.symm

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

theorem sound5447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5447 node5447Labels = Sparse.eval nodeValue5447 (mixedVector B) := by
  have h := singleton5447 B _hB
  rw [sound3909 B _hB _hF, sound4025 B _hB _hF] at h
  norm_num [nodeValue5447, nodeValue3909, nodeValue4025, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5474 node5474Labels = Sparse.eval nodeValue5474 (mixedVector B) := by
  simpa only [nodeValue5474, Sparse.eval_nil] using zero5474 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources24
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm788 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA788 + difference 0 1) (sourceB788 + difference 1 0) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA788 + difference 0 1) (sourceB788 + difference 1 0) sourceC788) = raw12998 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw12998; decide +kernel
    rw [ha]
    exact (canonical12998 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA788 + difference 0 2) (sourceB788 + difference 2 0) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5474) := by
    have ha : (tripleCharges (sourceA788 + difference 0 2) (sourceB788 + difference 2 0) sourceC788) = raw12999 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw12999; decide +kernel
    rw [ha]
    exact (canonical12999 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA788 + difference 0 3) (sourceB788 + difference 3 0) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA788 + difference 0 3) (sourceB788 + difference 3 0) sourceC788) = raw13000 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13000; decide +kernel
    rw [ha]
    exact (canonical13000 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA788 + difference 0 4) (sourceB788 + difference 4 0) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA788 + difference 0 4) (sourceB788 + difference 4 0) sourceC788) = raw13001 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13001; decide +kernel
    rw [ha]
    exact (canonical13001 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA788 + difference 0 5) (sourceB788 + difference 5 0) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA788 + difference 0 5) (sourceB788 + difference 5 0) sourceC788) = raw13002 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13002; decide +kernel
    rw [ha]
    exact (canonical13002 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA788 + difference 1 0) (sourceB788 + difference 0 1) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4473) := by
    have ha : (tripleCharges (sourceA788 + difference 1 0) (sourceB788 + difference 0 1) sourceC788) = raw13003 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13003; decide +kernel
    rw [ha]
    exact (canonical13003 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA788 + difference 1 2) (sourceB788 + difference 2 1) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA788 + difference 1 2) (sourceB788 + difference 2 1) sourceC788) = raw13004 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13004; decide +kernel
    rw [ha]
    exact (canonical13004 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA788 + difference 1 3) (sourceB788 + difference 3 1) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA788 + difference 1 3) (sourceB788 + difference 3 1) sourceC788) = raw13005 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13005; decide +kernel
    rw [ha]
    exact (canonical13005 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA788 + difference 1 4) (sourceB788 + difference 4 1) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA788 + difference 1 4) (sourceB788 + difference 4 1) sourceC788) = raw13006 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13006; decide +kernel
    rw [ha]
    exact (canonical13006 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA788 + difference 1 5) (sourceB788 + difference 5 1) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA788 + difference 1 5) (sourceB788 + difference 5 1) sourceC788) = raw13007 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13007; decide +kernel
    rw [ha]
    exact (canonical13007 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA788 + difference 2 0) (sourceB788 + difference 0 2) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4494) := by
    have ha : (tripleCharges (sourceA788 + difference 2 0) (sourceB788 + difference 0 2) sourceC788) = raw13008 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13008; decide +kernel
    rw [ha]
    exact (canonical13008 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA788 + difference 2 1) (sourceB788 + difference 1 2) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5097) := by
    have ha : (tripleCharges (sourceA788 + difference 2 1) (sourceB788 + difference 1 2) sourceC788) = raw13009 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13009; decide +kernel
    rw [ha]
    exact (canonical13009 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA788 + difference 2 3) (sourceB788 + difference 3 2) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA788 + difference 2 3) (sourceB788 + difference 3 2) sourceC788) = raw13010 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13010; decide +kernel
    rw [ha]
    exact (canonical13010 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA788 + difference 2 4) (sourceB788 + difference 4 2) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA788 + difference 2 4) (sourceB788 + difference 4 2) sourceC788) = raw13011 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13011; decide +kernel
    rw [ha]
    exact (canonical13011 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA788 + difference 2 5) (sourceB788 + difference 5 2) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA788 + difference 2 5) (sourceB788 + difference 5 2) sourceC788) = raw13012 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13012; decide +kernel
    rw [ha]
    exact (canonical13012 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA788 + difference 3 0) (sourceB788 + difference 0 3) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA788 + difference 3 0) (sourceB788 + difference 0 3) sourceC788) = raw13013 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13013; decide +kernel
    rw [ha]
    exact (canonical13013 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA788 + difference 3 1) (sourceB788 + difference 1 3) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA788 + difference 3 1) (sourceB788 + difference 1 3) sourceC788) = raw13014 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13014; decide +kernel
    rw [ha]
    exact (canonical13014 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA788 + difference 3 2) (sourceB788 + difference 2 3) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA788 + difference 3 2) (sourceB788 + difference 2 3) sourceC788) = raw13015 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13015; decide +kernel
    rw [ha]
    exact (canonical13015 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA788 + difference 3 4) (sourceB788 + difference 4 3) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA788 + difference 3 4) (sourceB788 + difference 4 3) sourceC788) = raw13016 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13016; decide +kernel
    rw [ha]
    exact (canonical13016 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA788 + difference 3 5) (sourceB788 + difference 5 3) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA788 + difference 3 5) (sourceB788 + difference 5 3) sourceC788) = raw13017 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13017; decide +kernel
    rw [ha]
    exact (canonical13017 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA788 + difference 4 0) (sourceB788 + difference 0 4) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA788 + difference 4 0) (sourceB788 + difference 0 4) sourceC788) = raw13018 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13018; decide +kernel
    rw [ha]
    exact (canonical13018 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA788 + difference 4 1) (sourceB788 + difference 1 4) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA788 + difference 4 1) (sourceB788 + difference 1 4) sourceC788) = raw13019 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13019; decide +kernel
    rw [ha]
    exact (canonical13019 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA788 + difference 4 2) (sourceB788 + difference 2 4) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA788 + difference 4 2) (sourceB788 + difference 2 4) sourceC788) = raw13020 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13020; decide +kernel
    rw [ha]
    exact (canonical13020 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA788 + difference 4 3) (sourceB788 + difference 3 4) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA788 + difference 4 3) (sourceB788 + difference 3 4) sourceC788) = raw13021 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13021; decide +kernel
    rw [ha]
    exact (canonical13021 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA788 + difference 4 5) (sourceB788 + difference 5 4) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA788 + difference 4 5) (sourceB788 + difference 5 4) sourceC788) = raw13022 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13022; decide +kernel
    rw [ha]
    exact (canonical13022 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA788 + difference 5 0) (sourceB788 + difference 0 5) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA788 + difference 5 0) (sourceB788 + difference 0 5) sourceC788) = raw13023 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13023; decide +kernel
    rw [ha]
    exact (canonical13023 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA788 + difference 5 1) (sourceB788 + difference 1 5) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA788 + difference 5 1) (sourceB788 + difference 1 5) sourceC788) = raw13024 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13024; decide +kernel
    rw [ha]
    exact (canonical13024 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA788 + difference 5 2) (sourceB788 + difference 2 5) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA788 + difference 5 2) (sourceB788 + difference 2 5) sourceC788) = raw13025 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13025; decide +kernel
    rw [ha]
    exact (canonical13025 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA788 + difference 5 3) (sourceB788 + difference 3 5) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA788 + difference 5 3) (sourceB788 + difference 3 5) sourceC788) = raw13026 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13026; decide +kernel
    rw [ha]
    exact (canonical13026 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA788 + difference 5 4) (sourceB788 + difference 4 5) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA788 + difference 5 4) (sourceB788 + difference 4 5) sourceC788) = raw13027 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13027; decide +kernel
    rw [ha]
    exact (canonical13027 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA788 sourceB788 sourceC788
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm788, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck682 : Integer.Sparse.reindex keyMap MixedData.row682 = numericRow682 := by decide +kernel

theorem numericCheck682 (x : Master → ℝ) : Integer.Sparse.eval numericRow682 x =
    (2880 : ℝ) * reducedSource682 x := by
  norm_num [numericRow682, reducedSource682, Integer.Sparse.eval, Sparse.eval, nodeValue4473, nodeValue4474, nodeValue4494, nodeValue5085, nodeValue5097, nodeValue5202, nodeValue5203, nodeValue5265, nodeValue5266, nodeValue5270, nodeValue5447, nodeValue5450, nodeValue5474]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero682 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource682 (mixedVector B) = 0 := by
  have h4473 : mixedVector B (Sum.inr 4473) = Sparse.eval nodeValue4473 (mixedVector B) := by
    change mixedMoment B node4473 node4473Labels = _
    exact sound4473 B hB hF
  have h4474 : mixedVector B (Sum.inr 4474) = Sparse.eval nodeValue4474 (mixedVector B) := by
    change mixedMoment B node4474 node4474Labels = _
    exact sound4474 B hB hF
  have h4494 : mixedVector B (Sum.inr 4494) = Sparse.eval nodeValue4494 (mixedVector B) := by
    change mixedMoment B node4494 node4494Labels = _
    exact sound4494 B hB hF
  have h5085 : mixedVector B (Sum.inr 5085) = Sparse.eval nodeValue5085 (mixedVector B) := by
    change mixedMoment B node5085 node5085Labels = _
    exact sound5085 B hB hF
  have h5097 : mixedVector B (Sum.inr 5097) = Sparse.eval nodeValue5097 (mixedVector B) := by
    change mixedMoment B node5097 node5097Labels = _
    exact sound5097 B hB hF
  have h5202 : mixedVector B (Sum.inr 5202) = Sparse.eval nodeValue5202 (mixedVector B) := by
    change mixedMoment B node5202 node5202Labels = _
    exact sound5202 B hB hF
  have h5203 : mixedVector B (Sum.inr 5203) = Sparse.eval nodeValue5203 (mixedVector B) := by
    change mixedMoment B node5203 node5203Labels = _
    exact sound5203 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5266 : mixedVector B (Sum.inr 5266) = Sparse.eval nodeValue5266 (mixedVector B) := by
    change mixedMoment B node5266 node5266Labels = _
    exact sound5266 B hB hF
  have h5270 : mixedVector B (Sum.inr 5270) = Sparse.eval nodeValue5270 (mixedVector B) := by
    change mixedMoment B node5270 node5270Labels = _
    exact sound5270 B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450_e B hB hF
  have h5474 : mixedVector B (Sum.inr 5474) = Sparse.eval nodeValue5474 (mixedVector B) := by
    change mixedMoment B node5474 node5474Labels = _
    exact sound5474 B hB hF
  simpa only [sourceForm788, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4473, h4474, h4494, h5085, h5097, h5202, h5203, h5265, h5266, h5270, h5447, h5450, h5474, reducedSource682] using sourceEq788 B hB

theorem rowSound682_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row682 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck682, numericCheck682, reducedZero682 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound682_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound682_e_oai
