-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:06:18.524844+00:00
-- url     : https://prove2.me/submissions/258be7e9-a8c6-490c-8ce5-21df1b11a61c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170

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

theorem canonical1692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1692 raw1692Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw1692 raw1692Labels = mixedMoment B raw1692step0 raw1692step0Labels := by
      have ha : raw1692step0 = (fun i j => raw1692 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1692step0 raw1692; decide +kernel
      have hl : raw1692step0Labels = raw1692Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1692 raw1692Labels permutation152 permutation4
    mixedMoment B raw1692step0 raw1692step0Labels = mixedMoment B raw1692step1 raw1692step1Labels := by
      have ha : raw1692step1 = raw1692step0 := by apply Matrix.ext; unfold raw1692step1 raw1692step0; decide +kernel
      have hl : raw1692step0Labels = labelEmbedding7 ∘ raw1692step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1692step0 raw1692step0Labels raw1692step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4763 node4763Labels := by rfl

theorem canonical1693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1693 raw1693Labels = mixedMoment B node1963 node1963Labels := by
  calc
    mixedMoment B raw1693 raw1693Labels = mixedMoment B raw1693step0 raw1693step0Labels := by
      have ha : raw1693step0 = (fun i j => raw1693 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1693step0 raw1693; decide +kernel
      have hl : raw1693step0Labels = raw1693Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1693 raw1693Labels permutation152 permutation4
    _ = mixedMoment B node1963 node1963Labels := by rfl

theorem canonical1694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1694 raw1694Labels = mixedMoment B node2174 node2174Labels := by
  calc
    mixedMoment B raw1694 raw1694Labels = mixedMoment B raw1694step0 raw1694step0Labels := by
      have ha : raw1694step0 = (fun i j => raw1694 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1694step0 raw1694; decide +kernel
      have hl : raw1694step0Labels = raw1694Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1694 raw1694Labels permutation152 permutation6
    mixedMoment B raw1694step0 raw1694step0Labels = mixedMoment B raw1694step1 raw1694step1Labels := by
      have ha : raw1694step1 = -raw1694step0 := by apply Matrix.ext; change ∀ i j, raw1694step1 i j = -(raw1694step0 i j); unfold raw1694step1 raw1694step0; decide +kernel
      have hl : raw1694step1Labels = raw1694step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1694step1 raw1694step1Labels = mixedMoment B raw1694step2 raw1694step2Labels := by
      have ha : raw1694step2 = raw1694step1 := by apply Matrix.ext; unfold raw1694step2 raw1694step1; decide +kernel
      have hl : raw1694step1Labels = labelEmbedding1 ∘ raw1694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1694step1 raw1694step1Labels raw1694step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2174 node2174Labels := by rfl

theorem canonical1704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1704 raw1704Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw1704 raw1704Labels = mixedMoment B raw1704step0 raw1704step0Labels := by
      have ha : raw1704step0 = (fun i j => raw1704 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1704step0 raw1704; decide +kernel
      have hl : raw1704step0Labels = raw1704Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1704 raw1704Labels permutation32 permutation4
    mixedMoment B raw1704step0 raw1704step0Labels = mixedMoment B raw1704step1 raw1704step1Labels := by
      have ha : raw1704step1 = raw1704step0 := by apply Matrix.ext; unfold raw1704step1 raw1704step0; decide +kernel
      have hl : raw1704step0Labels = labelEmbedding7 ∘ raw1704step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1704step0 raw1704step0Labels raw1704step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4769 node4769Labels := by rfl

theorem canonical1705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1705 raw1705Labels = mixedMoment B node1969 node1969Labels := by
  calc
    mixedMoment B raw1705 raw1705Labels = mixedMoment B raw1705step0 raw1705step0Labels := by
      have ha : raw1705step0 = (fun i j => raw1705 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1705step0 raw1705; decide +kernel
      have hl : raw1705step0Labels = raw1705Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1705 raw1705Labels permutation32 permutation4
    _ = mixedMoment B node1969 node1969Labels := by rfl

theorem canonical1706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1706 raw1706Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw1706 raw1706Labels = mixedMoment B raw1706step0 raw1706step0Labels := by
      have ha : raw1706step0 = (fun i j => raw1706 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1706step0 raw1706; decide +kernel
      have hl : raw1706step0Labels = raw1706Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1706 raw1706Labels permutation32 permutation6
    mixedMoment B raw1706step0 raw1706step0Labels = mixedMoment B raw1706step1 raw1706step1Labels := by
      have ha : raw1706step1 = -raw1706step0 := by apply Matrix.ext; change ∀ i j, raw1706step1 i j = -(raw1706step0 i j); unfold raw1706step1 raw1706step0; decide +kernel
      have hl : raw1706step1Labels = raw1706step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1706step1 raw1706step1Labels = mixedMoment B raw1706step2 raw1706step2Labels := by
      have ha : raw1706step2 = raw1706step1 := by apply Matrix.ext; unfold raw1706step2 raw1706step1; decide +kernel
      have hl : raw1706step1Labels = labelEmbedding1 ∘ raw1706step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1706step1 raw1706step1Labels raw1706step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

theorem canonical1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1707 raw1707Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw1707 raw1707Labels = mixedMoment B raw1707step0 raw1707step0Labels := by
      have ha : raw1707step0 = (fun i j => raw1707 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1707step0 raw1707; decide +kernel
      have hl : raw1707step0Labels = raw1707Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1707 raw1707Labels permutation32 permutation4
    mixedMoment B raw1707step0 raw1707step0Labels = mixedMoment B raw1707step1 raw1707step1Labels := by
      have ha : raw1707step1 = raw1707step0 := by apply Matrix.ext; unfold raw1707step1 raw1707step0; decide +kernel
      have hl : raw1707step0Labels = labelEmbedding7 ∘ raw1707step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1707step0 raw1707step0Labels raw1707step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4770 node4770Labels := by rfl

theorem canonical1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1708 raw1708Labels = mixedMoment B node1970 node1970Labels := by
  calc
    mixedMoment B raw1708 raw1708Labels = mixedMoment B raw1708step0 raw1708step0Labels := by
      have ha : raw1708step0 = (fun i j => raw1708 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1708step0 raw1708; decide +kernel
      have hl : raw1708step0Labels = raw1708Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1708 raw1708Labels permutation32 permutation4
    _ = mixedMoment B node1970 node1970Labels := by rfl

theorem canonical1709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1709 raw1709Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw1709 raw1709Labels = mixedMoment B raw1709step0 raw1709step0Labels := by
      have ha : raw1709step0 = (fun i j => raw1709 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1709step0 raw1709; decide +kernel
      have hl : raw1709step0Labels = raw1709Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1709 raw1709Labels permutation33 permutation6
    mixedMoment B raw1709step0 raw1709step0Labels = mixedMoment B raw1709step1 raw1709step1Labels := by
      have ha : raw1709step1 = -raw1709step0 := by apply Matrix.ext; change ∀ i j, raw1709step1 i j = -(raw1709step0 i j); unfold raw1709step1 raw1709step0; decide +kernel
      have hl : raw1709step1Labels = raw1709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1709step1 raw1709step1Labels = mixedMoment B raw1709step2 raw1709step2Labels := by
      have ha : raw1709step2 = raw1709step1 := by apply Matrix.ext; unfold raw1709step2 raw1709step1; decide +kernel
      have hl : raw1709step1Labels = labelEmbedding1 ∘ raw1709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1709step1 raw1709step1Labels raw1709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2186 node2186Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2124 raw2124Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw2124 raw2124Labels = mixedMoment B raw2124step0 raw2124step0Labels := by
      have ha : raw2124step0 = (fun i j => raw2124 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2124step0 raw2124; decide +kernel
      have hl : raw2124step0Labels = raw2124Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2124 raw2124Labels permutation32 permutation4
    mixedMoment B raw2124step0 raw2124step0Labels = mixedMoment B raw2124step1 raw2124step1Labels := by
      have ha : raw2124step1 = raw2124step0 := by apply Matrix.ext; unfold raw2124step1 raw2124step0; decide +kernel
      have hl : raw2124step0Labels = labelEmbedding7 ∘ raw2124step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2124step0 raw2124step0Labels raw2124step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

theorem canonical2125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2125 raw2125Labels = mixedMoment B node2509 node2509Labels := by
  calc
    mixedMoment B raw2125 raw2125Labels = mixedMoment B raw2125step0 raw2125step0Labels := by
      have ha : raw2125step0 = (fun i j => raw2125 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2125step0 raw2125; decide +kernel
      have hl : raw2125step0Labels = raw2125Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2125 raw2125Labels permutation32 permutation4
    _ = mixedMoment B node2509 node2509Labels := by rfl

theorem canonical2126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2126 raw2126Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw2126 raw2126Labels = mixedMoment B raw2126step0 raw2126step0Labels := by
      have ha : raw2126step0 = (fun i j => raw2126 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2126step0 raw2126; decide +kernel
      have hl : raw2126step0Labels = raw2126Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2126 raw2126Labels permutation145 permutation6
    mixedMoment B raw2126step0 raw2126step0Labels = mixedMoment B raw2126step1 raw2126step1Labels := by
      have ha : raw2126step1 = raw2126step0 := by apply Matrix.ext; unfold raw2126step1 raw2126step0; decide +kernel
      have hl : raw2126step0Labels = labelEmbedding1 ∘ raw2126step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2126step0 raw2126step0Labels raw2126step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

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

theorem canonical2256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2256 raw2256Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw2256 raw2256Labels = mixedMoment B raw2256step0 raw2256step0Labels := by
      have ha : raw2256step0 = (fun i j => raw2256 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2256step0 raw2256; decide +kernel
      have hl : raw2256step0Labels = raw2256Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2256 raw2256Labels permutation8 permutation4
    mixedMoment B raw2256step0 raw2256step0Labels = mixedMoment B raw2256step1 raw2256step1Labels := by
      have ha : raw2256step1 = raw2256step0 := by apply Matrix.ext; unfold raw2256step1 raw2256step0; decide +kernel
      have hl : raw2256step0Labels = labelEmbedding7 ∘ raw2256step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2256step0 raw2256step0Labels raw2256step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

theorem canonical2257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2257 raw2257Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw2257 raw2257Labels = mixedMoment B raw2257step0 raw2257step0Labels := by
      have ha : raw2257step0 = (fun i j => raw2257 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2257step0 raw2257; decide +kernel
      have hl : raw2257step0Labels = raw2257Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2257 raw2257Labels permutation8 permutation4
    _ = mixedMoment B node2686 node2686Labels := by rfl

theorem canonical2258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2258 raw2258Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw2258 raw2258Labels = mixedMoment B raw2258step0 raw2258step0Labels := by
      have ha : raw2258step0 = (fun i j => raw2258 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2258step0 raw2258; decide +kernel
      have hl : raw2258step0Labels = raw2258Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2258 raw2258Labels permutation8 permutation6
    mixedMoment B raw2258step0 raw2258step0Labels = mixedMoment B raw2258step1 raw2258step1Labels := by
      have ha : raw2258step1 = -raw2258step0 := by apply Matrix.ext; change ∀ i j, raw2258step1 i j = -(raw2258step0 i j); unfold raw2258step1 raw2258step0; decide +kernel
      have hl : raw2258step1Labels = raw2258step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2258step1 raw2258step1Labels = mixedMoment B raw2258step2 raw2258step2Labels := by
      have ha : raw2258step2 = raw2258step1 := by apply Matrix.ext; unfold raw2258step2 raw2258step1; decide +kernel
      have hl : raw2258step1Labels = labelEmbedding1 ∘ raw2258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2258step1 raw2258step1Labels raw2258step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3397 node3397Labels := by rfl

theorem canonical2259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2259 raw2259Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw2259 raw2259Labels = mixedMoment B raw2259step0 raw2259step0Labels := by
      have ha : raw2259step0 = (fun i j => raw2259 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2259step0 raw2259; decide +kernel
      have hl : raw2259step0Labels = raw2259Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2259 raw2259Labels permutation152 permutation4
    mixedMoment B raw2259step0 raw2259step0Labels = mixedMoment B raw2259step1 raw2259step1Labels := by
      have ha : raw2259step1 = raw2259step0 := by apply Matrix.ext; unfold raw2259step1 raw2259step0; decide +kernel
      have hl : raw2259step0Labels = labelEmbedding7 ∘ raw2259step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2259step0 raw2259step0Labels raw2259step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

theorem canonical2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2260 raw2260Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw2260 raw2260Labels = mixedMoment B raw2260step0 raw2260step0Labels := by
      have ha : raw2260step0 = (fun i j => raw2260 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2260step0 raw2260; decide +kernel
      have hl : raw2260step0Labels = raw2260Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2260 raw2260Labels permutation152 permutation4
    _ = mixedMoment B node2694 node2694Labels := by rfl

theorem canonical2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2261 raw2261Labels = mixedMoment B node3493 node3493Labels := by
  calc
    mixedMoment B raw2261 raw2261Labels = mixedMoment B raw2261step0 raw2261step0Labels := by
      have ha : raw2261step0 = (fun i j => raw2261 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2261step0 raw2261; decide +kernel
      have hl : raw2261step0Labels = raw2261Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2261 raw2261Labels permutation152 permutation6
    mixedMoment B raw2261step0 raw2261step0Labels = mixedMoment B raw2261step1 raw2261step1Labels := by
      have ha : raw2261step1 = -raw2261step0 := by apply Matrix.ext; change ∀ i j, raw2261step1 i j = -(raw2261step0 i j); unfold raw2261step1 raw2261step0; decide +kernel
      have hl : raw2261step1Labels = raw2261step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2261step1 raw2261step1Labels = mixedMoment B raw2261step2 raw2261step2Labels := by
      have ha : raw2261step2 = raw2261step1 := by apply Matrix.ext; unfold raw2261step2 raw2261step1; decide +kernel
      have hl : raw2261step1Labels = labelEmbedding1 ∘ raw2261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2261step1 raw2261step1Labels raw2261step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3493 node3493Labels := by rfl

theorem canonical2265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2265 raw2265Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw2265 raw2265Labels = mixedMoment B raw2265step0 raw2265step0Labels := by
      have ha : raw2265step0 = (fun i j => raw2265 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2265step0 raw2265; decide +kernel
      have hl : raw2265step0Labels = raw2265Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2265 raw2265Labels permutation32 permutation4
    mixedMoment B raw2265step0 raw2265step0Labels = mixedMoment B raw2265step1 raw2265step1Labels := by
      have ha : raw2265step1 = raw2265step0 := by apply Matrix.ext; unfold raw2265step1 raw2265step0; decide +kernel
      have hl : raw2265step0Labels = labelEmbedding7 ∘ raw2265step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2265step0 raw2265step0Labels raw2265step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

theorem canonical2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2266 raw2266Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw2266 raw2266Labels = mixedMoment B raw2266step0 raw2266step0Labels := by
      have ha : raw2266step0 = (fun i j => raw2266 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2266step0 raw2266; decide +kernel
      have hl : raw2266step0Labels = raw2266Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2266 raw2266Labels permutation32 permutation4
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical2267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2267 raw2267Labels = mixedMoment B node3498 node3498Labels := by
  calc
    mixedMoment B raw2267 raw2267Labels = mixedMoment B raw2267step0 raw2267step0Labels := by
      have ha : raw2267step0 = (fun i j => raw2267 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2267step0 raw2267; decide +kernel
      have hl : raw2267step0Labels = raw2267Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2267 raw2267Labels permutation32 permutation6
    mixedMoment B raw2267step0 raw2267step0Labels = mixedMoment B raw2267step1 raw2267step1Labels := by
      have ha : raw2267step1 = -raw2267step0 := by apply Matrix.ext; change ∀ i j, raw2267step1 i j = -(raw2267step0 i j); unfold raw2267step1 raw2267step0; decide +kernel
      have hl : raw2267step1Labels = raw2267step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2267step1 raw2267step1Labels = mixedMoment B raw2267step2 raw2267step2Labels := by
      have ha : raw2267step2 = raw2267step1 := by apply Matrix.ext; unfold raw2267step2 raw2267step1; decide +kernel
      have hl : raw2267step1Labels = labelEmbedding1 ∘ raw2267step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2267step1 raw2267step1Labels raw2267step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3498 node3498Labels := by rfl

theorem canonical2286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2286 raw2286Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw2286 raw2286Labels = mixedMoment B raw2286step0 raw2286step0Labels := by
      have ha : raw2286step0 = (fun i j => raw2286 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2286step0 raw2286; decide +kernel
      have hl : raw2286step0Labels = raw2286Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2286 raw2286Labels permutation8 permutation4
    mixedMoment B raw2286step0 raw2286step0Labels = mixedMoment B raw2286step1 raw2286step1Labels := by
      have ha : raw2286step1 = raw2286step0 := by apply Matrix.ext; unfold raw2286step1 raw2286step0; decide +kernel
      have hl : raw2286step0Labels = labelEmbedding7 ∘ raw2286step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2286step0 raw2286step0Labels raw2286step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2287 raw2287Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw2287 raw2287Labels = mixedMoment B raw2287step0 raw2287step0Labels := by
      have ha : raw2287step0 = (fun i j => raw2287 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2287step0 raw2287; decide +kernel
      have hl : raw2287step0Labels = raw2287Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2287 raw2287Labels permutation8 permutation4
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical2288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2288 raw2288Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw2288 raw2288Labels = mixedMoment B raw2288step0 raw2288step0Labels := by
      have ha : raw2288step0 = (fun i j => raw2288 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2288step0 raw2288; decide +kernel
      have hl : raw2288step0Labels = raw2288Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2288 raw2288Labels permutation9 permutation6
    mixedMoment B raw2288step0 raw2288step0Labels = mixedMoment B raw2288step1 raw2288step1Labels := by
      have ha : raw2288step1 = -raw2288step0 := by apply Matrix.ext; change ∀ i j, raw2288step1 i j = -(raw2288step0 i j); unfold raw2288step1 raw2288step0; decide +kernel
      have hl : raw2288step1Labels = raw2288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2288step1 raw2288step1Labels = mixedMoment B raw2288step2 raw2288step2Labels := by
      have ha : raw2288step2 = raw2288step1 := by apply Matrix.ext; unfold raw2288step2 raw2288step1; decide +kernel
      have hl : raw2288step1Labels = labelEmbedding1 ∘ raw2288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2288step1 raw2288step1Labels raw2288step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

theorem canonical2289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2289 raw2289Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw2289 raw2289Labels = mixedMoment B raw2289step0 raw2289step0Labels := by
      have ha : raw2289step0 = (fun i j => raw2289 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2289step0 raw2289; decide +kernel
      have hl : raw2289step0Labels = raw2289Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2289 raw2289Labels permutation32 permutation5
    mixedMoment B raw2289step0 raw2289step0Labels = mixedMoment B raw2289step1 raw2289step1Labels := by
      have ha : raw2289step1 = raw2289step0 := by apply Matrix.ext; unfold raw2289step1 raw2289step0; decide +kernel
      have hl : raw2289step0Labels = labelEmbedding8 ∘ raw2289step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2289step0 raw2289step0Labels raw2289step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2290 raw2290Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw2290 raw2290Labels = mixedMoment B raw2290step0 raw2290step0Labels := by
      have ha : raw2290step0 = (fun i j => raw2290 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2290step0 raw2290; decide +kernel
      have hl : raw2290step0Labels = raw2290Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2290 raw2290Labels permutation32 permutation4
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2291 raw2291Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw2291 raw2291Labels = mixedMoment B raw2291step0 raw2291step0Labels := by
      have ha : raw2291step0 = (fun i j => raw2291 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2291step0 raw2291; decide +kernel
      have hl : raw2291step0Labels = raw2291Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2291 raw2291Labels permutation48 permutation3
    mixedMoment B raw2291step0 raw2291step0Labels = mixedMoment B raw2291step1 raw2291step1Labels := by
      have ha : raw2291step1 = -raw2291step0 := by apply Matrix.ext; change ∀ i j, raw2291step1 i j = -(raw2291step0 i j); unfold raw2291step1 raw2291step0; decide +kernel
      have hl : raw2291step1Labels = raw2291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2291step1 raw2291step1Labels = mixedMoment B raw2291step2 raw2291step2Labels := by
      have ha : raw2291step2 = raw2291step1 := by apply Matrix.ext; unfold raw2291step2 raw2291step1; decide +kernel
      have hl : raw2291step1Labels = labelEmbedding1 ∘ raw2291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2291step1 raw2291step1Labels raw2291step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical221
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28395 raw28395Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw28395 raw28395Labels = mixedMoment B raw28395step0 raw28395step0Labels := by
      have hz : ∀ j, raw28395 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28395step0 = (fun i j => raw28395 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28395step0 raw28395; decide +kernel
      have hl : raw28395step0Labels = raw28395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28395 raw28395Labels permutation434 hz
    mixedMoment B raw28395step0 raw28395step0Labels = mixedMoment B raw28395step1 raw28395step1Labels := by
      have hz : ∀ j, raw28395step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28395step1 = (fun i j => raw28395step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28395step1 raw28395step0; decide +kernel
      have hl : raw28395step1Labels = raw28395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28395step0 raw28395step0Labels permutation80 hz
    mixedMoment B raw28395step1 raw28395step1Labels = mixedMoment B raw28395step2 raw28395step2Labels := by
      have ha : raw28395step2 = (fun i j => raw28395step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28395step2 raw28395step1; decide +kernel
      have hl : raw28395step2Labels = raw28395step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28395step1 raw28395step1Labels permutation30 permutation2
    mixedMoment B raw28395step2 raw28395step2Labels = mixedMoment B raw28395step3 raw28395step3Labels := by
      have ha : raw28395step3 = -raw28395step2 := by apply Matrix.ext; change ∀ i j, raw28395step3 i j = -(raw28395step2 i j); unfold raw28395step3 raw28395step2; decide +kernel
      have hl : raw28395step3Labels = raw28395step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4846 node4846Labels := by rfl

theorem canonical28399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28399 raw28399Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw28399 raw28399Labels = mixedMoment B raw28399step0 raw28399step0Labels := by
      have hz : ∀ j, raw28399 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28399step0 = (fun i j => raw28399 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28399step0 raw28399; decide +kernel
      have hl : raw28399step0Labels = raw28399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28399 raw28399Labels permutation434 hz
    mixedMoment B raw28399step0 raw28399step0Labels = mixedMoment B raw28399step1 raw28399step1Labels := by
      have hz : ∀ j, raw28399step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28399step1 = (fun i j => raw28399step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28399step1 raw28399step0; decide +kernel
      have hl : raw28399step1Labels = raw28399step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28399step0 raw28399step0Labels permutation80 hz
    mixedMoment B raw28399step1 raw28399step1Labels = mixedMoment B raw28399step2 raw28399step2Labels := by
      have ha : raw28399step2 = (fun i j => raw28399step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28399step2 raw28399step1; decide +kernel
      have hl : raw28399step2Labels = raw28399step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28399step1 raw28399step1Labels permutation30 permutation7
    mixedMoment B raw28399step2 raw28399step2Labels = mixedMoment B raw28399step3 raw28399step3Labels := by
      have ha : raw28399step3 = raw28399step2 := by apply Matrix.ext; unfold raw28399step3 raw28399step2; decide +kernel
      have hl : raw28399step2Labels = labelEmbedding10 ∘ raw28399step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28399step2 raw28399step2Labels raw28399step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical28411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28411 raw28411Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw28411 raw28411Labels = mixedMoment B raw28411step0 raw28411step0Labels := by
      have hz : ∀ j, raw28411 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28411step0 = (fun i j => raw28411 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28411step0 raw28411; decide +kernel
      have hl : raw28411step0Labels = raw28411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28411 raw28411Labels permutation346 hz
    mixedMoment B raw28411step0 raw28411step0Labels = mixedMoment B raw28411step1 raw28411step1Labels := by
      have ha : raw28411step1 = (fun i j => raw28411step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28411step1 raw28411step0; decide +kernel
      have hl : raw28411step1Labels = raw28411step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28411step0 raw28411step0Labels permutation145 permutation2
    mixedMoment B raw28411step1 raw28411step1Labels = mixedMoment B raw28411step2 raw28411step2Labels := by
      have ha : raw28411step2 = -raw28411step1 := by apply Matrix.ext; change ∀ i j, raw28411step2 i j = -(raw28411step1 i j); unfold raw28411step2 raw28411step1; decide +kernel
      have hl : raw28411step2Labels = raw28411step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4770 node4770Labels := by rfl

theorem canonical28414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28414 raw28414Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw28414 raw28414Labels = mixedMoment B raw28414step0 raw28414step0Labels := by
      have hz : ∀ j, raw28414 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28414step0 = (fun i j => raw28414 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28414step0 raw28414; decide +kernel
      have hl : raw28414step0Labels = raw28414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28414 raw28414Labels permutation346 hz
    mixedMoment B raw28414step0 raw28414step0Labels = mixedMoment B raw28414step1 raw28414step1Labels := by
      have ha : raw28414step1 = (fun i j => raw28414step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28414step1 raw28414step0; decide +kernel
      have hl : raw28414step1Labels = raw28414step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28414step0 raw28414step0Labels permutation32 permutation3
    mixedMoment B raw28414step1 raw28414step1Labels = mixedMoment B raw28414step2 raw28414step2Labels := by
      have ha : raw28414step2 = raw28414step1 := by apply Matrix.ext; unfold raw28414step2 raw28414step1; decide +kernel
      have hl : raw28414step1Labels = labelEmbedding6 ∘ raw28414step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28414step1 raw28414step1Labels raw28414step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5205 node5205Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical287
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36789 raw36789Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw36789 raw36789Labels = mixedMoment B raw36789step0 raw36789step0Labels := by
      have hz : ∀ j, raw36789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36789step0 = (fun i j => raw36789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36789step0 raw36789; decide +kernel
      have hl : raw36789step0Labels = raw36789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36789 raw36789Labels permutation346 hz
    mixedMoment B raw36789step0 raw36789step0Labels = mixedMoment B raw36789step1 raw36789step1Labels := by
      have ha : raw36789step1 = (fun i j => raw36789step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36789step1 raw36789step0; decide +kernel
      have hl : raw36789step1Labels = raw36789step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36789step0 raw36789step0Labels permutation56 permutation2
    _ = mixedMoment B node5099 node5099Labels := by rfl

theorem canonical36790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36790 raw36790Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw36790 raw36790Labels = mixedMoment B raw36790step0 raw36790step0Labels := by
      have ha : raw36790step0 = (fun i j => raw36790 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36790step0 raw36790; decide +kernel
      have hl : raw36790step0Labels = raw36790Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36790 raw36790Labels permutation663 permutation7
    mixedMoment B raw36790step0 raw36790step0Labels = mixedMoment B raw36790step1 raw36790step1Labels := by
      have ha : raw36790step1 = raw36790step0 := by apply Matrix.ext; unfold raw36790step1 raw36790step0; decide +kernel
      have hl : raw36790step0Labels = labelEmbedding10 ∘ raw36790step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36790step0 raw36790step0Labels raw36790step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

theorem canonical36791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36791 raw36791Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw36791 raw36791Labels = mixedMoment B raw36791step0 raw36791step0Labels := by
      have hz : ∀ j, raw36791 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36791step0 = (fun i j => raw36791 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36791step0 raw36791; decide +kernel
      have hl : raw36791step0Labels = raw36791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36791 raw36791Labels permutation434 hz
    mixedMoment B raw36791step0 raw36791step0Labels = mixedMoment B raw36791step1 raw36791step1Labels := by
      have hz : ∀ j, raw36791step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36791step1 = (fun i j => raw36791step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36791step1 raw36791step0; decide +kernel
      have hl : raw36791step1Labels = raw36791step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36791step0 raw36791step0Labels permutation80 hz
    mixedMoment B raw36791step1 raw36791step1Labels = mixedMoment B raw36791step2 raw36791step2Labels := by
      have ha : raw36791step2 = (fun i j => raw36791step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36791step2 raw36791step1; decide +kernel
      have hl : raw36791step2Labels = raw36791step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36791step1 raw36791step1Labels permutation30 permutation7
    mixedMoment B raw36791step2 raw36791step2Labels = mixedMoment B raw36791step3 raw36791step3Labels := by
      have ha : raw36791step3 = raw36791step2 := by apply Matrix.ext; unfold raw36791step3 raw36791step2; decide +kernel
      have hl : raw36791step2Labels = labelEmbedding10 ∘ raw36791step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36791step2 raw36791step2Labels raw36791step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

theorem canonical36792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36792 raw36792Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw36792 raw36792Labels = mixedMoment B raw36792step0 raw36792step0Labels := by
      have hz : ∀ j, raw36792 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36792step0 = (fun i j => raw36792 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36792step0 raw36792; decide +kernel
      have hl : raw36792step0Labels = raw36792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36792 raw36792Labels permutation520 hz
    mixedMoment B raw36792step0 raw36792step0Labels = mixedMoment B raw36792step1 raw36792step1Labels := by
      have hz : ∀ j, raw36792step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36792step1 = (fun i j => raw36792step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36792step1 raw36792step0; decide +kernel
      have hl : raw36792step1Labels = raw36792step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36792step0 raw36792step0Labels permutation80 hz
    mixedMoment B raw36792step1 raw36792step1Labels = mixedMoment B raw36792step2 raw36792step2Labels := by
      have ha : raw36792step2 = (fun i j => raw36792step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36792step2 raw36792step1; decide +kernel
      have hl : raw36792step2Labels = raw36792step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36792step1 raw36792step1Labels permutation30 permutation7
    mixedMoment B raw36792step2 raw36792step2Labels = mixedMoment B raw36792step3 raw36792step3Labels := by
      have ha : raw36792step3 = raw36792step2 := by apply Matrix.ext; unfold raw36792step3 raw36792step2; decide +kernel
      have hl : raw36792step2Labels = labelEmbedding10 ∘ raw36792step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36792step2 raw36792step2Labels raw36792step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

theorem canonical36793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36793 raw36793Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw36793 raw36793Labels = mixedMoment B raw36793step0 raw36793step0Labels := by
      have hz : ∀ j, raw36793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36793step0 = (fun i j => raw36793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36793step0 raw36793; decide +kernel
      have hl : raw36793step0Labels = raw36793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36793 raw36793Labels permutation346 hz
    mixedMoment B raw36793step0 raw36793step0Labels = mixedMoment B raw36793step1 raw36793step1Labels := by
      have ha : raw36793step1 = (fun i j => raw36793step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36793step1 raw36793step0; decide +kernel
      have hl : raw36793step1Labels = raw36793step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36793step0 raw36793step0Labels permutation144 permutation6
    mixedMoment B raw36793step1 raw36793step1Labels = mixedMoment B raw36793step2 raw36793step2Labels := by
      have ha : raw36793step2 = raw36793step1 := by apply Matrix.ext; unfold raw36793step2 raw36793step1; decide +kernel
      have hl : raw36793step1Labels = labelEmbedding9 ∘ raw36793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36793step1 raw36793step1Labels raw36793step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical36794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36794 raw36794Labels = mixedMoment B node5242 node5242Labels := by
  calc
    mixedMoment B raw36794 raw36794Labels = mixedMoment B raw36794step0 raw36794step0Labels := by
      have ha : raw36794step0 = (fun i j => raw36794 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36794step0 raw36794; decide +kernel
      have hl : raw36794step0Labels = raw36794Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36794 raw36794Labels permutation663 permutation7
    mixedMoment B raw36794step0 raw36794step0Labels = mixedMoment B raw36794step1 raw36794step1Labels := by
      have ha : raw36794step1 = raw36794step0 := by apply Matrix.ext; unfold raw36794step1 raw36794step0; decide +kernel
      have hl : raw36794step0Labels = labelEmbedding10 ∘ raw36794step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36794step0 raw36794step0Labels raw36794step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5242 node5242Labels := by rfl

theorem canonical36795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36795 raw36795Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw36795 raw36795Labels = mixedMoment B raw36795step0 raw36795step0Labels := by
      have hz : ∀ j, raw36795 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36795step0 = (fun i j => raw36795 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36795step0 raw36795; decide +kernel
      have hl : raw36795step0Labels = raw36795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36795 raw36795Labels permutation520 hz
    mixedMoment B raw36795step0 raw36795step0Labels = mixedMoment B raw36795step1 raw36795step1Labels := by
      have hz : ∀ j, raw36795step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36795step1 = (fun i j => raw36795step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36795step1 raw36795step0; decide +kernel
      have hl : raw36795step1Labels = raw36795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36795step0 raw36795step0Labels permutation80 hz
    mixedMoment B raw36795step1 raw36795step1Labels = mixedMoment B raw36795step2 raw36795step2Labels := by
      have ha : raw36795step2 = (fun i j => raw36795step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36795step2 raw36795step1; decide +kernel
      have hl : raw36795step2Labels = raw36795step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36795step1 raw36795step1Labels permutation30 permutation7
    mixedMoment B raw36795step2 raw36795step2Labels = mixedMoment B raw36795step3 raw36795step3Labels := by
      have ha : raw36795step3 = raw36795step2 := by apply Matrix.ext; unfold raw36795step3 raw36795step2; decide +kernel
      have hl : raw36795step2Labels = labelEmbedding10 ∘ raw36795step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36795step2 raw36795step2Labels raw36795step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical36796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36796 raw36796Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw36796 raw36796Labels = mixedMoment B raw36796step0 raw36796step0Labels := by
      have hz : ∀ j, raw36796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36796step0 = (fun i j => raw36796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36796step0 raw36796; decide +kernel
      have hl : raw36796step0Labels = raw36796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36796 raw36796Labels permutation346 hz
    mixedMoment B raw36796step0 raw36796step0Labels = mixedMoment B raw36796step1 raw36796step1Labels := by
      have ha : raw36796step1 = (fun i j => raw36796step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36796step1 raw36796step0; decide +kernel
      have hl : raw36796step1Labels = raw36796step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36796step0 raw36796step0Labels permutation144 permutation6
    mixedMoment B raw36796step1 raw36796step1Labels = mixedMoment B raw36796step2 raw36796step2Labels := by
      have ha : raw36796step2 = raw36796step1 := by apply Matrix.ext; unfold raw36796step2 raw36796step1; decide +kernel
      have hl : raw36796step1Labels = labelEmbedding9 ∘ raw36796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36796step1 raw36796step1Labels raw36796step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

theorem canonical36797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36797 raw36797Labels = mixedMoment B node4975 node4975Labels := by
  calc
    mixedMoment B raw36797 raw36797Labels = mixedMoment B raw36797step0 raw36797step0Labels := by
      have ha : raw36797step0 = (fun i j => raw36797 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36797step0 raw36797; decide +kernel
      have hl : raw36797step0Labels = raw36797Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36797 raw36797Labels permutation152 permutation3
    mixedMoment B raw36797step0 raw36797step0Labels = mixedMoment B raw36797step1 raw36797step1Labels := by
      have ha : raw36797step1 = raw36797step0 := by apply Matrix.ext; unfold raw36797step1 raw36797step0; decide +kernel
      have hl : raw36797step0Labels = labelEmbedding6 ∘ raw36797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36797step0 raw36797step0Labels raw36797step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4975 node4975Labels := by rfl

theorem canonical36798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36798 raw36798Labels = mixedMoment B node4938 node4938Labels := by
  calc
    mixedMoment B raw36798 raw36798Labels = mixedMoment B raw36798step0 raw36798step0Labels := by
      have ha : raw36798step0 = (fun i j => raw36798 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36798step0 raw36798; decide +kernel
      have hl : raw36798step0Labels = raw36798Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36798 raw36798Labels permutation265 permutation2
    _ = mixedMoment B node4938 node4938Labels := by rfl

theorem canonical36799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36799 raw36799Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw36799 raw36799Labels = mixedMoment B raw36799step0 raw36799step0Labels := by
      have hz : ∀ j, raw36799 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36799step0 = (fun i j => raw36799 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36799step0 raw36799; decide +kernel
      have hl : raw36799step0Labels = raw36799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36799 raw36799Labels permutation434 hz
    mixedMoment B raw36799step0 raw36799step0Labels = mixedMoment B raw36799step1 raw36799step1Labels := by
      have ha : raw36799step1 = (fun i j => raw36799step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36799step1 raw36799step0; decide +kernel
      have hl : raw36799step1Labels = raw36799step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36799step0 raw36799step0Labels permutation144 permutation7
    mixedMoment B raw36799step1 raw36799step1Labels = mixedMoment B raw36799step2 raw36799step2Labels := by
      have ha : raw36799step2 = raw36799step1 := by apply Matrix.ext; unfold raw36799step2 raw36799step1; decide +kernel
      have hl : raw36799step1Labels = labelEmbedding10 ∘ raw36799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36799step1 raw36799step1Labels raw36799step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

theorem canonical36800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36800 raw36800Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw36800 raw36800Labels = mixedMoment B raw36800step0 raw36800step0Labels := by
      have hz : ∀ j, raw36800 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36800step0 = (fun i j => raw36800 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36800step0 raw36800; decide +kernel
      have hl : raw36800step0Labels = raw36800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36800 raw36800Labels permutation520 hz
    mixedMoment B raw36800step0 raw36800step0Labels = mixedMoment B raw36800step1 raw36800step1Labels := by
      have ha : raw36800step1 = (fun i j => raw36800step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36800step1 raw36800step0; decide +kernel
      have hl : raw36800step1Labels = raw36800step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36800step0 raw36800step0Labels permutation144 permutation7
    mixedMoment B raw36800step1 raw36800step1Labels = mixedMoment B raw36800step2 raw36800step2Labels := by
      have ha : raw36800step2 = raw36800step1 := by apply Matrix.ext; unfold raw36800step2 raw36800step1; decide +kernel
      have hl : raw36800step1Labels = labelEmbedding10 ∘ raw36800step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36800step1 raw36800step1Labels raw36800step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

theorem canonical36801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36801 raw36801Labels = mixedMoment B node5277 node5277Labels := by
  calc
    mixedMoment B raw36801 raw36801Labels = mixedMoment B raw36801step0 raw36801step0Labels := by
      have ha : raw36801step0 = (fun i j => raw36801 (permutation639 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36801step0 raw36801; decide +kernel
      have hl : raw36801step0Labels = raw36801Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36801 raw36801Labels permutation639 permutation6
    mixedMoment B raw36801step0 raw36801step0Labels = mixedMoment B raw36801step1 raw36801step1Labels := by
      have ha : raw36801step1 = raw36801step0 := by apply Matrix.ext; unfold raw36801step1 raw36801step0; decide +kernel
      have hl : raw36801step0Labels = labelEmbedding9 ∘ raw36801step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36801step0 raw36801step0Labels raw36801step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5277 node5277Labels := by rfl

theorem canonical36802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36802 raw36802Labels = mixedMoment B node4976 node4976Labels := by
  calc
    mixedMoment B raw36802 raw36802Labels = mixedMoment B raw36802step0 raw36802step0Labels := by
      have hz : ∀ j, raw36802 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36802step0 = (fun i j => raw36802 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36802step0 raw36802; decide +kernel
      have hl : raw36802step0Labels = raw36802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36802 raw36802Labels permutation346 hz
    mixedMoment B raw36802step0 raw36802step0Labels = mixedMoment B raw36802step1 raw36802step1Labels := by
      have ha : raw36802step1 = (fun i j => raw36802step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36802step1 raw36802step0; decide +kernel
      have hl : raw36802step1Labels = raw36802step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36802step0 raw36802step0Labels permutation35 permutation3
    mixedMoment B raw36802step1 raw36802step1Labels = mixedMoment B raw36802step2 raw36802step2Labels := by
      have ha : raw36802step2 = raw36802step1 := by apply Matrix.ext; unfold raw36802step2 raw36802step1; decide +kernel
      have hl : raw36802step1Labels = labelEmbedding6 ∘ raw36802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36802step1 raw36802step1Labels raw36802step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4976 node4976Labels := by rfl

theorem canonical36803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36803 raw36803Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw36803 raw36803Labels = mixedMoment B raw36803step0 raw36803step0Labels := by
      have hz : ∀ j, raw36803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36803step0 = (fun i j => raw36803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36803step0 raw36803; decide +kernel
      have hl : raw36803step0Labels = raw36803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36803 raw36803Labels permutation346 hz
    mixedMoment B raw36803step0 raw36803step0Labels = mixedMoment B raw36803step1 raw36803step1Labels := by
      have ha : raw36803step1 = (fun i j => raw36803step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36803step1 raw36803step0; decide +kernel
      have hl : raw36803step1Labels = raw36803step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36803step0 raw36803step0Labels permutation58 permutation2
    _ = mixedMoment B node4945 node4945Labels := by rfl

theorem canonical36804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36804 raw36804Labels = mixedMoment B node5215 node5215Labels := by
  calc
    mixedMoment B raw36804 raw36804Labels = mixedMoment B raw36804step0 raw36804step0Labels := by
      have ha : raw36804step0 = (fun i j => raw36804 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36804step0 raw36804; decide +kernel
      have hl : raw36804step0Labels = raw36804Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36804 raw36804Labels permutation663 permutation7
    mixedMoment B raw36804step0 raw36804step0Labels = mixedMoment B raw36804step1 raw36804step1Labels := by
      have ha : raw36804step1 = raw36804step0 := by apply Matrix.ext; unfold raw36804step1 raw36804step0; decide +kernel
      have hl : raw36804step0Labels = labelEmbedding10 ∘ raw36804step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36804step0 raw36804step0Labels raw36804step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5215 node5215Labels := by rfl

theorem canonical36805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36805 raw36805Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw36805 raw36805Labels = mixedMoment B raw36805step0 raw36805step0Labels := by
      have hz : ∀ j, raw36805 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36805step0 = (fun i j => raw36805 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36805step0 raw36805; decide +kernel
      have hl : raw36805step0Labels = raw36805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36805 raw36805Labels permutation520 hz
    mixedMoment B raw36805step0 raw36805step0Labels = mixedMoment B raw36805step1 raw36805step1Labels := by
      have hz : ∀ j, raw36805step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36805step1 = (fun i j => raw36805step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36805step1 raw36805step0; decide +kernel
      have hl : raw36805step1Labels = raw36805step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36805step0 raw36805step0Labels permutation80 hz
    mixedMoment B raw36805step1 raw36805step1Labels = mixedMoment B raw36805step2 raw36805step2Labels := by
      have ha : raw36805step2 = (fun i j => raw36805step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36805step2 raw36805step1; decide +kernel
      have hl : raw36805step2Labels = raw36805step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36805step1 raw36805step1Labels permutation30 permutation7
    mixedMoment B raw36805step2 raw36805step2Labels = mixedMoment B raw36805step3 raw36805step3Labels := by
      have ha : raw36805step3 = raw36805step2 := by apply Matrix.ext; unfold raw36805step3 raw36805step2; decide +kernel
      have hl : raw36805step2Labels = labelEmbedding10 ∘ raw36805step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36805step2 raw36805step2Labels raw36805step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

theorem canonical36806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36806 raw36806Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw36806 raw36806Labels = mixedMoment B raw36806step0 raw36806step0Labels := by
      have hz : ∀ j, raw36806 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36806step0 = (fun i j => raw36806 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36806step0 raw36806; decide +kernel
      have hl : raw36806step0Labels = raw36806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36806 raw36806Labels permutation346 hz
    mixedMoment B raw36806step0 raw36806step0Labels = mixedMoment B raw36806step1 raw36806step1Labels := by
      have ha : raw36806step1 = (fun i j => raw36806step0 (permutation150 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36806step1 raw36806step0; decide +kernel
      have hl : raw36806step1Labels = raw36806step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36806step0 raw36806step0Labels permutation150 permutation6
    mixedMoment B raw36806step1 raw36806step1Labels = mixedMoment B raw36806step2 raw36806step2Labels := by
      have ha : raw36806step2 = raw36806step1 := by apply Matrix.ext; unfold raw36806step2 raw36806step1; decide +kernel
      have hl : raw36806step1Labels = labelEmbedding9 ∘ raw36806step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36806step1 raw36806step1Labels raw36806step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

theorem canonical36807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36807 raw36807Labels = mixedMoment B node4976 node4976Labels := by
  calc
    mixedMoment B raw36807 raw36807Labels = mixedMoment B raw36807step0 raw36807step0Labels := by
      have hz : ∀ j, raw36807 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36807step0 = (fun i j => raw36807 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36807step0 raw36807; decide +kernel
      have hl : raw36807step0Labels = raw36807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36807 raw36807Labels permutation346 hz
    mixedMoment B raw36807step0 raw36807step0Labels = mixedMoment B raw36807step1 raw36807step1Labels := by
      have ha : raw36807step1 = (fun i j => raw36807step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36807step1 raw36807step0; decide +kernel
      have hl : raw36807step1Labels = raw36807step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36807step0 raw36807step0Labels permutation33 permutation3
    mixedMoment B raw36807step1 raw36807step1Labels = mixedMoment B raw36807step2 raw36807step2Labels := by
      have ha : raw36807step2 = raw36807step1 := by apply Matrix.ext; unfold raw36807step2 raw36807step1; decide +kernel
      have hl : raw36807step1Labels = labelEmbedding6 ∘ raw36807step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36807step1 raw36807step1Labels raw36807step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4976 node4976Labels := by rfl

theorem canonical36808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36808 raw36808Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw36808 raw36808Labels = mixedMoment B raw36808step0 raw36808step0Labels := by
      have hz : ∀ j, raw36808 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36808step0 = (fun i j => raw36808 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36808step0 raw36808; decide +kernel
      have hl : raw36808step0Labels = raw36808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36808 raw36808Labels permutation346 hz
    mixedMoment B raw36808step0 raw36808step0Labels = mixedMoment B raw36808step1 raw36808step1Labels := by
      have ha : raw36808step1 = (fun i j => raw36808step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36808step1 raw36808step0; decide +kernel
      have hl : raw36808step1Labels = raw36808step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36808step0 raw36808step0Labels permutation56 permutation2
    _ = mixedMoment B node4945 node4945Labels := by rfl

theorem canonical36809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36809 raw36809Labels = mixedMoment B node5215 node5215Labels := by
  calc
    mixedMoment B raw36809 raw36809Labels = mixedMoment B raw36809step0 raw36809step0Labels := by
      have ha : raw36809step0 = (fun i j => raw36809 (permutation687 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36809step0 raw36809; decide +kernel
      have hl : raw36809step0Labels = raw36809Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36809 raw36809Labels permutation687 permutation7
    mixedMoment B raw36809step0 raw36809step0Labels = mixedMoment B raw36809step1 raw36809step1Labels := by
      have ha : raw36809step1 = raw36809step0 := by apply Matrix.ext; unfold raw36809step1 raw36809step0; decide +kernel
      have hl : raw36809step0Labels = labelEmbedding10 ∘ raw36809step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36809step0 raw36809step0Labels raw36809step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5215 node5215Labels := by rfl

theorem canonical36810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36810 raw36810Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw36810 raw36810Labels = mixedMoment B raw36810step0 raw36810step0Labels := by
      have hz : ∀ j, raw36810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36810step0 = (fun i j => raw36810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36810step0 raw36810; decide +kernel
      have hl : raw36810step0Labels = raw36810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36810 raw36810Labels permutation434 hz
    mixedMoment B raw36810step0 raw36810step0Labels = mixedMoment B raw36810step1 raw36810step1Labels := by
      have hz : ∀ j, raw36810step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36810step1 = (fun i j => raw36810step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36810step1 raw36810step0; decide +kernel
      have hl : raw36810step1Labels = raw36810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36810step0 raw36810step0Labels permutation80 hz
    mixedMoment B raw36810step1 raw36810step1Labels = mixedMoment B raw36810step2 raw36810step2Labels := by
      have ha : raw36810step2 = (fun i j => raw36810step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36810step2 raw36810step1; decide +kernel
      have hl : raw36810step2Labels = raw36810step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36810step1 raw36810step1Labels permutation30 permutation7
    mixedMoment B raw36810step2 raw36810step2Labels = mixedMoment B raw36810step3 raw36810step3Labels := by
      have ha : raw36810step3 = raw36810step2 := by apply Matrix.ext; unfold raw36810step3 raw36810step2; decide +kernel
      have hl : raw36810step2Labels = labelEmbedding10 ∘ raw36810step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36810step2 raw36810step2Labels raw36810step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

theorem canonical36811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36811 raw36811Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw36811 raw36811Labels = mixedMoment B raw36811step0 raw36811step0Labels := by
      have hz : ∀ j, raw36811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36811step0 = (fun i j => raw36811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36811step0 raw36811; decide +kernel
      have hl : raw36811step0Labels = raw36811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36811 raw36811Labels permutation346 hz
    mixedMoment B raw36811step0 raw36811step0Labels = mixedMoment B raw36811step1 raw36811step1Labels := by
      have ha : raw36811step1 = (fun i j => raw36811step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36811step1 raw36811step0; decide +kernel
      have hl : raw36811step1Labels = raw36811step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36811step0 raw36811step0Labels permutation144 permutation6
    mixedMoment B raw36811step1 raw36811step1Labels = mixedMoment B raw36811step2 raw36811step2Labels := by
      have ha : raw36811step2 = raw36811step1 := by apply Matrix.ext; unfold raw36811step2 raw36811step1; decide +kernel
      have hl : raw36811step1Labels = labelEmbedding9 ∘ raw36811step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36811step1 raw36811step1Labels raw36811step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

theorem canonical36812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36812 raw36812Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw36812 raw36812Labels = mixedMoment B raw36812step0 raw36812step0Labels := by
      have hz : ∀ j, raw36812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36812step0 = (fun i j => raw36812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36812step0 raw36812; decide +kernel
      have hl : raw36812step0Labels = raw36812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36812 raw36812Labels permutation346 hz
    mixedMoment B raw36812step0 raw36812step0Labels = mixedMoment B raw36812step1 raw36812step1Labels := by
      have ha : raw36812step1 = (fun i j => raw36812step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36812step1 raw36812step0; decide +kernel
      have hl : raw36812step1Labels = raw36812step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36812step0 raw36812step0Labels permutation144 permutation2
    mixedMoment B raw36812step1 raw36812step1Labels = mixedMoment B raw36812step2 raw36812step2Labels := by
      have ha : raw36812step2 = -raw36812step1 := by apply Matrix.ext; change ∀ i j, raw36812step2 i j = -(raw36812step1 i j); unfold raw36812step2 raw36812step1; decide +kernel
      have hl : raw36812step2Labels = raw36812step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4769 node4769Labels := by rfl

theorem canonical36813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36813 raw36813Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw36813 raw36813Labels = mixedMoment B raw36813step0 raw36813step0Labels := by
      have ha : raw36813step0 = (fun i j => raw36813 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36813step0 raw36813; decide +kernel
      have hl : raw36813step0Labels = raw36813Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36813 raw36813Labels permutation663 permutation2
    mixedMoment B raw36813step0 raw36813step0Labels = mixedMoment B raw36813step1 raw36813step1Labels := by
      have ha : raw36813step1 = -raw36813step0 := by apply Matrix.ext; change ∀ i j, raw36813step1 i j = -(raw36813step0 i j); unfold raw36813step1 raw36813step0; decide +kernel
      have hl : raw36813step1Labels = raw36813step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4763 node4763Labels := by rfl

theorem canonical36814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36814 raw36814Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw36814 raw36814Labels = mixedMoment B raw36814step0 raw36814step0Labels := by
      have hz : ∀ j, raw36814 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36814step0 = (fun i j => raw36814 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36814step0 raw36814; decide +kernel
      have hl : raw36814step0Labels = raw36814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36814 raw36814Labels permutation520 hz
    mixedMoment B raw36814step0 raw36814step0Labels = mixedMoment B raw36814step1 raw36814step1Labels := by
      have hz : ∀ j, raw36814step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36814step1 = (fun i j => raw36814step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36814step1 raw36814step0; decide +kernel
      have hl : raw36814step1Labels = raw36814step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36814step0 raw36814step0Labels permutation80 hz
    mixedMoment B raw36814step1 raw36814step1Labels = mixedMoment B raw36814step2 raw36814step2Labels := by
      have ha : raw36814step2 = (fun i j => raw36814step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36814step2 raw36814step1; decide +kernel
      have hl : raw36814step2Labels = raw36814step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36814step1 raw36814step1Labels permutation30 permutation2
    mixedMoment B raw36814step2 raw36814step2Labels = mixedMoment B raw36814step3 raw36814step3Labels := by
      have ha : raw36814step3 = -raw36814step2 := by apply Matrix.ext; change ∀ i j, raw36814step3 i j = -(raw36814step2 i j); unfold raw36814step3 raw36814step2; decide +kernel
      have hl : raw36814step3Labels = raw36814step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4846 node4846Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4763 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4763 node4763Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1963 node1963Labels + mixedMoment B node2174 node2174Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1692 singletonSmall4763
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4763) = raw1692Labels := by decide +kernel
  rw [hl, canonical1692 B hB] at h
  have hc0 : mixedMoment B raw1692 (Fin.cases (0 : Fin 2) singletonSmall4763) =
      mixedMoment B node1963 node1963Labels := by
    have ha : raw1692 = raw1693 := by apply Matrix.ext; unfold raw1692 raw1693; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4763 = raw1693Labels := by decide +kernel
    rw [ha, hj, canonical1693 B hB]
  have hc1 : mixedMoment B raw1692 (Fin.cases (1 : Fin 2) singletonSmall4763) =
      mixedMoment B node2174 node2174Labels := by
    have ha : raw1692 = raw1694 := by apply Matrix.ext; unfold raw1692 raw1694; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4763 = raw1694Labels := by decide +kernel
    rw [ha, hj, canonical1694 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4769 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4769 node4769Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1969 node1969Labels + mixedMoment B node2185 node2185Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1704 singletonSmall4769
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4769) = raw1704Labels := by decide +kernel
  rw [hl, canonical1704 B hB] at h
  have hc0 : mixedMoment B raw1704 (Fin.cases (0 : Fin 2) singletonSmall4769) =
      mixedMoment B node1969 node1969Labels := by
    have ha : raw1704 = raw1705 := by apply Matrix.ext; unfold raw1704 raw1705; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4769 = raw1705Labels := by decide +kernel
    rw [ha, hj, canonical1705 B hB]
  have hc1 : mixedMoment B raw1704 (Fin.cases (1 : Fin 2) singletonSmall4769) =
      mixedMoment B node2185 node2185Labels := by
    have ha : raw1704 = raw1706 := by apply Matrix.ext; unfold raw1704 raw1706; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4769 = raw1706Labels := by decide +kernel
    rw [ha, hj, canonical1706 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4770 node4770Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1970 node1970Labels + mixedMoment B node2186 node2186Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1707 singletonSmall4770
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4770) = raw1707Labels := by decide +kernel
  rw [hl, canonical1707 B hB] at h
  have hc0 : mixedMoment B raw1707 (Fin.cases (0 : Fin 2) singletonSmall4770) =
      mixedMoment B node1970 node1970Labels := by
    have ha : raw1707 = raw1708 := by apply Matrix.ext; unfold raw1707 raw1708; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4770 = raw1708Labels := by decide +kernel
    rw [ha, hj, canonical1708 B hB]
  have hc1 : mixedMoment B raw1707 (Fin.cases (1 : Fin 2) singletonSmall4770) =
      mixedMoment B node2186 node2186Labels := by
    have ha : raw1707 = raw1709 := by apply Matrix.ext; unfold raw1707 raw1709; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4770 = raw1709Labels := by decide +kernel
    rw [ha, hj, canonical1709 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5099 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5099 node5099Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2509 node2509Labels + mixedMoment B node2704 node2704Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2124 singletonSmall5099
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5099) = raw2124Labels := by decide +kernel
  rw [hl, canonical2124 B hB] at h
  have hc0 : mixedMoment B raw2124 (Fin.cases (0 : Fin 2) singletonSmall5099) =
      mixedMoment B node2509 node2509Labels := by
    have ha : raw2124 = raw2125 := by apply Matrix.ext; unfold raw2124 raw2125; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5099 = raw2125Labels := by decide +kernel
    rw [ha, hj, canonical2125 B hB]
  have hc1 : mixedMoment B raw2124 (Fin.cases (1 : Fin 2) singletonSmall5099) =
      mixedMoment B node2704 node2704Labels := by
    have ha : raw2124 = raw2126 := by apply Matrix.ext; unfold raw2124 raw2126; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5099 = raw2126Labels := by decide +kernel
    rw [ha, hj, canonical2126 B hB]
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

theorem singleton5238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5238 node5238Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2686 node2686Labels + mixedMoment B node3397 node3397Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2256 singletonSmall5238
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5238) = raw2256Labels := by decide +kernel
  rw [hl, canonical2256 B hB] at h
  have hc0 : mixedMoment B raw2256 (Fin.cases (0 : Fin 2) singletonSmall5238) =
      mixedMoment B node2686 node2686Labels := by
    have ha : raw2256 = raw2257 := by apply Matrix.ext; unfold raw2256 raw2257; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5238 = raw2257Labels := by decide +kernel
    rw [ha, hj, canonical2257 B hB]
  have hc1 : mixedMoment B raw2256 (Fin.cases (1 : Fin 2) singletonSmall5238) =
      mixedMoment B node3397 node3397Labels := by
    have ha : raw2256 = raw2258 := by apply Matrix.ext; unfold raw2256 raw2258; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5238 = raw2258Labels := by decide +kernel
    rw [ha, hj, canonical2258 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5241 node5241Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2694 node2694Labels + mixedMoment B node3493 node3493Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2259 singletonSmall5241
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5241) = raw2259Labels := by decide +kernel
  rw [hl, canonical2259 B hB] at h
  have hc0 : mixedMoment B raw2259 (Fin.cases (0 : Fin 2) singletonSmall5241) =
      mixedMoment B node2694 node2694Labels := by
    have ha : raw2259 = raw2260 := by apply Matrix.ext; unfold raw2259 raw2260; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5241 = raw2260Labels := by decide +kernel
    rw [ha, hj, canonical2260 B hB]
  have hc1 : mixedMoment B raw2259 (Fin.cases (1 : Fin 2) singletonSmall5241) =
      mixedMoment B node3493 node3493Labels := by
    have ha : raw2259 = raw2261 := by apply Matrix.ext; unfold raw2259 raw2261; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5241 = raw2261Labels := by decide +kernel
    rw [ha, hj, canonical2261 B hB]
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

theorem singleton5248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5248 node5248Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2705 node2705Labels + mixedMoment B node3498 node3498Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2265 singletonSmall5248
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5248) = raw2265Labels := by decide +kernel
  rw [hl, canonical2265 B hB] at h
  have hc0 : mixedMoment B raw2265 (Fin.cases (0 : Fin 2) singletonSmall5248) =
      mixedMoment B node2705 node2705Labels := by
    have ha : raw2265 = raw2266 := by apply Matrix.ext; unfold raw2265 raw2266; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5248 = raw2266Labels := by decide +kernel
    rw [ha, hj, canonical2266 B hB]
  have hc1 : mixedMoment B raw2265 (Fin.cases (1 : Fin 2) singletonSmall5248) =
      mixedMoment B node3498 node3498Labels := by
    have ha : raw2265 = raw2267 := by apply Matrix.ext; unfold raw2265 raw2267; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5248 = raw2267Labels := by decide +kernel
    rw [ha, hj, canonical2267 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5275 node5275Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2743 node2743Labels + mixedMoment B node3548 node3548Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2286 singletonSmall5275
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5275) = raw2286Labels := by decide +kernel
  rw [hl, canonical2286 B hB] at h
  have hc0 : mixedMoment B raw2286 (Fin.cases (0 : Fin 2) singletonSmall5275) =
      mixedMoment B node2743 node2743Labels := by
    have ha : raw2286 = raw2287 := by apply Matrix.ext; unfold raw2286 raw2287; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5275 = raw2287Labels := by decide +kernel
    rw [ha, hj, canonical2287 B hB]
  have hc1 : mixedMoment B raw2286 (Fin.cases (1 : Fin 2) singletonSmall5275) =
      mixedMoment B node3548 node3548Labels := by
    have ha : raw2286 = raw2288 := by apply Matrix.ext; unfold raw2286 raw2288; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5275 = raw2288Labels := by decide +kernel
    rw [ha, hj, canonical2288 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5284 node5284Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3077 node3077Labels + mixedMoment B node3625 node3625Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2289 singletonSmall5284
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5284) = raw2289Labels := by decide +kernel
  rw [hl, canonical2289 B hB] at h
  have hc0 : mixedMoment B raw2289 (Fin.cases (0 : Fin 2) singletonSmall5284) =
      mixedMoment B node3077 node3077Labels := by
    have ha : raw2289 = raw2290 := by apply Matrix.ext; unfold raw2289 raw2290; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5284 = raw2290Labels := by decide +kernel
    rw [ha, hj, canonical2290 B hB]
  have hc1 : mixedMoment B raw2289 (Fin.cases (1 : Fin 2) singletonSmall5284) =
      mixedMoment B node3625 node3625Labels := by
    have ha : raw2289 = raw2291 := by apply Matrix.ext; unfold raw2289 raw2291; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5284 = raw2291Labels := by decide +kernel
    rw [ha, hj, canonical2291 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound1963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1963 node1963Labels = Sparse.eval nodeValue1963 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1963) = mixedMoment B node1963 node1963Labels := rfl
  simpa [nodeValue1963, Sparse.eval] using hc.symm

theorem sound1969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1969 node1969Labels = Sparse.eval nodeValue1969 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1969) = mixedMoment B node1969 node1969Labels := rfl
  simpa [nodeValue1969, Sparse.eval] using hc.symm

theorem sound1970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1970 node1970Labels = Sparse.eval nodeValue1970 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1970) = mixedMoment B node1970 node1970Labels := rfl
  simpa [nodeValue1970, Sparse.eval] using hc.symm

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

theorem sound2174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2174 node2174Labels = Sparse.eval nodeValue2174 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2174) = mixedMoment B node2174 node2174Labels := rfl
  simpa [nodeValue2174, Sparse.eval] using hc.symm

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

theorem sound2185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2185 node2185Labels = Sparse.eval nodeValue2185 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2185) = mixedMoment B node2185 node2185Labels := rfl
  simpa [nodeValue2185, Sparse.eval] using hc.symm

theorem sound2186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2186 node2186Labels = Sparse.eval nodeValue2186 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2186) = mixedMoment B node2186 node2186Labels := rfl
  simpa [nodeValue2186, Sparse.eval] using hc.symm

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

theorem sound2509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2509 node2509Labels = Sparse.eval nodeValue2509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2509) = mixedMoment B node2509 node2509Labels := rfl
  simpa [nodeValue2509, Sparse.eval] using hc.symm

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

theorem sound2686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2686 node2686Labels = Sparse.eval nodeValue2686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2686) = mixedMoment B node2686 node2686Labels := rfl
  simpa [nodeValue2686, Sparse.eval] using hc.symm

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

theorem sound2694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2694 node2694Labels = Sparse.eval nodeValue2694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2694) = mixedMoment B node2694 node2694Labels := rfl
  simpa [nodeValue2694, Sparse.eval] using hc.symm

theorem sound2704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2704 node2704Labels = Sparse.eval nodeValue2704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2704) = mixedMoment B node2704 node2704Labels := rfl
  simpa [nodeValue2704, Sparse.eval] using hc.symm

theorem sound2705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2705 node2705Labels = Sparse.eval nodeValue2705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2705) = mixedMoment B node2705 node2705Labels := rfl
  simpa [nodeValue2705, Sparse.eval] using hc.symm

theorem sound2743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2743 node2743Labels = Sparse.eval nodeValue2743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2743) = mixedMoment B node2743 node2743Labels := rfl
  simpa [nodeValue2743, Sparse.eval] using hc.symm

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

theorem sound3077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3077 node3077Labels = Sparse.eval nodeValue3077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3077) = mixedMoment B node3077 node3077Labels := rfl
  simpa [nodeValue3077, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3397 node3397Labels = Sparse.eval nodeValue3397 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3397) = mixedMoment B node3397 node3397Labels := rfl
  simpa [nodeValue3397, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3493 node3493Labels = Sparse.eval nodeValue3493 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3493) = mixedMoment B node3493 node3493Labels := rfl
  simpa [nodeValue3493, Sparse.eval] using hc.symm

theorem sound3498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3498 node3498Labels = Sparse.eval nodeValue3498 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3498) = mixedMoment B node3498 node3498Labels := rfl
  simpa [nodeValue3498, Sparse.eval] using hc.symm

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

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4763 node4763Labels = Sparse.eval nodeValue4763 (mixedVector B) := by
  have h := singleton4763 B _hB
  rw [sound1963 B _hB _hF, sound2174 B _hB _hF] at h
  norm_num [nodeValue4763, nodeValue1963, nodeValue2174, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4769 node4769Labels = Sparse.eval nodeValue4769 (mixedVector B) := by
  have h := singleton4769 B _hB
  rw [sound1969 B _hB _hF, sound2185 B _hB _hF] at h
  norm_num [nodeValue4769, nodeValue1969, nodeValue2185, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4770 node4770Labels = Sparse.eval nodeValue4770 (mixedVector B) := by
  have h := singleton4770 B _hB
  rw [sound1970 B _hB _hF, sound2186 B _hB _hF] at h
  norm_num [nodeValue4770, nodeValue1970, nodeValue2186, Sparse.eval] at h ⊢
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

theorem zero4846 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4846 node4846Labels = 0 := by
  exact mixedMoment_order_one B hB node4846 node4846Labels 1
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

theorem sound4846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4846 node4846Labels = Sparse.eval nodeValue4846 (mixedVector B) := by
  simpa only [nodeValue4846, Sparse.eval_nil] using zero4846 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4938 node4938Labels = 0 := by
  exact mixedMoment_alpha B hF node4938 node4938Labels 1 permutation161
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4938 node4938Labels = Sparse.eval nodeValue4938 (mixedVector B) := by
  simpa only [nodeValue4938, Sparse.eval_nil] using zero4938 B _hB _hF

theorem sound4945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4945 node4945Labels = Sparse.eval nodeValue4945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4945) = mixedMoment B node4945 node4945Labels := rfl
  simpa [nodeValue4945, Sparse.eval] using hc.symm

theorem sound4975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4975 node4975Labels = Sparse.eval nodeValue4975 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4975) = mixedMoment B node4975 node4975Labels := rfl
  simpa [nodeValue4975, Sparse.eval] using hc.symm

theorem sound4976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4976 node4976Labels = Sparse.eval nodeValue4976 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4976) = mixedMoment B node4976 node4976Labels := rfl
  simpa [nodeValue4976, Sparse.eval] using hc.symm

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

theorem sound5099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5099 node5099Labels = Sparse.eval nodeValue5099 (mixedVector B) := by
  have h := singleton5099 B _hB
  rw [sound2509 B _hB _hF, sound2704 B _hB _hF] at h
  norm_num [nodeValue5099, nodeValue2509, nodeValue2704, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5242 node5242Labels = 0 := by
  exact mixedMoment_alpha B hF node5242 node5242Labels 1 permutation212
    (by decide +kernel)

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

theorem sound5205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5205 node5205Labels = Sparse.eval nodeValue5205 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5205) = mixedMoment B node5205 node5205Labels := rfl
  simpa [nodeValue5205, Sparse.eval] using hc.symm

theorem sound5215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5215 node5215Labels = Sparse.eval nodeValue5215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5215) = mixedMoment B node5215 node5215Labels := rfl
  simpa [nodeValue5215, Sparse.eval] using hc.symm

theorem sound5238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5238 node5238Labels = Sparse.eval nodeValue5238 (mixedVector B) := by
  have h := singleton5238 B _hB
  rw [sound2686 B _hB _hF, sound3397 B _hB _hF] at h
  norm_num [nodeValue5238, nodeValue2686, nodeValue3397, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5241 node5241Labels = Sparse.eval nodeValue5241 (mixedVector B) := by
  have h := singleton5241 B _hB
  rw [sound2694 B _hB _hF, sound3493 B _hB _hF] at h
  norm_num [nodeValue5241, nodeValue2694, nodeValue3493, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5242 node5242Labels = Sparse.eval nodeValue5242 (mixedVector B) := by
  simpa only [nodeValue5242, Sparse.eval_nil] using zero5242 B _hB _hF

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

theorem zero5274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5274 node5274Labels = 0 := by
  exact mixedMoment_order_one B hB node5274 node5274Labels 1
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

theorem sound5248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5248 node5248Labels = Sparse.eval nodeValue5248 (mixedVector B) := by
  have h := singleton5248 B _hB
  rw [sound2705 B _hB _hF, sound3498 B _hB _hF] at h
  norm_num [nodeValue5248, nodeValue2705, nodeValue3498, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5274 node5274Labels = Sparse.eval nodeValue5274 (mixedVector B) := by
  simpa only [nodeValue5274, Sparse.eval_nil] using zero5274 B _hB _hF

theorem sound5275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5275 node5275Labels = Sparse.eval nodeValue5275 (mixedVector B) := by
  have h := singleton5275 B _hB
  rw [sound2743 B _hB _hF, sound3548 B _hB _hF] at h
  norm_num [nodeValue5275, nodeValue2743, nodeValue3548, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5277 node5277Labels = Sparse.eval nodeValue5277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5277) = mixedMoment B node5277 node5277Labels := rfl
  simpa [nodeValue5277, Sparse.eval] using hc.symm

theorem sound5282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5282 node5282Labels = Sparse.eval nodeValue5282 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5282) = mixedMoment B node5282 node5282Labels := rfl
  simpa [nodeValue5282, Sparse.eval] using hc.symm

theorem sound5284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5284 node5284Labels = Sparse.eval nodeValue5284 (mixedVector B) := by
  have h := singleton5284 B _hB
  rw [sound3077 B _hB _hF, sound3625 B _hB _hF] at h
  norm_num [nodeValue5284, nodeValue3077, nodeValue3625, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5287 node5287Labels = Sparse.eval nodeValue5287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5287) = mixedMoment B node5287 node5287Labels := rfl
  simpa [nodeValue5287, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources82
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2629 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2629 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2629 + difference 0 1) (sourceB2629 + difference 1 0) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2629 + difference 0 1) (sourceB2629 + difference 1 0) sourceC2629) = raw36789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36789; decide +kernel
    rw [ha]
    exact (canonical36789 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2629 + difference 0 2) (sourceB2629 + difference 2 0) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA2629 + difference 0 2) (sourceB2629 + difference 2 0) sourceC2629) = raw36790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36790; decide +kernel
    rw [ha]
    exact (canonical36790 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2629 + difference 0 3) (sourceB2629 + difference 3 0) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2629 + difference 0 3) (sourceB2629 + difference 3 0) sourceC2629) = raw36791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36791; decide +kernel
    rw [ha]
    exact (canonical36791 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2629 + difference 0 4) (sourceB2629 + difference 4 0) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2629 + difference 0 4) (sourceB2629 + difference 4 0) sourceC2629) = raw36792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36792; decide +kernel
    rw [ha]
    exact (canonical36792 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2629 + difference 0 5) (sourceB2629 + difference 5 0) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA2629 + difference 0 5) (sourceB2629 + difference 5 0) sourceC2629) = raw36793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36793; decide +kernel
    rw [ha]
    exact (canonical36793 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2629 + difference 1 0) (sourceB2629 + difference 0 1) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA2629 + difference 1 0) (sourceB2629 + difference 0 1) sourceC2629) = raw28414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw28414; decide +kernel
    rw [ha]
    exact (canonical28414 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2629 + difference 1 2) (sourceB2629 + difference 2 1) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5242) := by
    have ha : (tripleCharges (sourceA2629 + difference 1 2) (sourceB2629 + difference 2 1) sourceC2629) = raw36794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36794; decide +kernel
    rw [ha]
    exact (canonical36794 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2629 + difference 1 3) (sourceB2629 + difference 3 1) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA2629 + difference 1 3) (sourceB2629 + difference 3 1) sourceC2629) = raw28399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw28399; decide +kernel
    rw [ha]
    exact (canonical28399 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2629 + difference 1 4) (sourceB2629 + difference 4 1) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA2629 + difference 1 4) (sourceB2629 + difference 4 1) sourceC2629) = raw36795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36795; decide +kernel
    rw [ha]
    exact (canonical36795 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2629 + difference 1 5) (sourceB2629 + difference 5 1) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA2629 + difference 1 5) (sourceB2629 + difference 5 1) sourceC2629) = raw36796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36796; decide +kernel
    rw [ha]
    exact (canonical36796 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2629 + difference 2 0) (sourceB2629 + difference 0 2) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4975) := by
    have ha : (tripleCharges (sourceA2629 + difference 2 0) (sourceB2629 + difference 0 2) sourceC2629) = raw36797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36797; decide +kernel
    rw [ha]
    exact (canonical36797 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2629 + difference 2 1) (sourceB2629 + difference 1 2) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4938) := by
    have ha : (tripleCharges (sourceA2629 + difference 2 1) (sourceB2629 + difference 1 2) sourceC2629) = raw36798 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36798; decide +kernel
    rw [ha]
    exact (canonical36798 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2629 + difference 2 3) (sourceB2629 + difference 3 2) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2629 + difference 2 3) (sourceB2629 + difference 3 2) sourceC2629) = raw36799 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36799; decide +kernel
    rw [ha]
    exact (canonical36799 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2629 + difference 2 4) (sourceB2629 + difference 4 2) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2629 + difference 2 4) (sourceB2629 + difference 4 2) sourceC2629) = raw36800 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36800; decide +kernel
    rw [ha]
    exact (canonical36800 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2629 + difference 2 5) (sourceB2629 + difference 5 2) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5277) := by
    have ha : (tripleCharges (sourceA2629 + difference 2 5) (sourceB2629 + difference 5 2) sourceC2629) = raw36801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36801; decide +kernel
    rw [ha]
    exact (canonical36801 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2629 + difference 3 0) (sourceB2629 + difference 0 3) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4976) := by
    have ha : (tripleCharges (sourceA2629 + difference 3 0) (sourceB2629 + difference 0 3) sourceC2629) = raw36802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36802; decide +kernel
    rw [ha]
    exact (canonical36802 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2629 + difference 3 1) (sourceB2629 + difference 1 3) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2629 + difference 3 1) (sourceB2629 + difference 1 3) sourceC2629) = raw36803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36803; decide +kernel
    rw [ha]
    exact (canonical36803 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2629 + difference 3 2) (sourceB2629 + difference 2 3) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5215) := by
    have ha : (tripleCharges (sourceA2629 + difference 3 2) (sourceB2629 + difference 2 3) sourceC2629) = raw36804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36804; decide +kernel
    rw [ha]
    exact (canonical36804 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2629 + difference 3 4) (sourceB2629 + difference 4 3) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2629 + difference 3 4) (sourceB2629 + difference 4 3) sourceC2629) = raw36805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36805; decide +kernel
    rw [ha]
    exact (canonical36805 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2629 + difference 3 5) (sourceB2629 + difference 5 3) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA2629 + difference 3 5) (sourceB2629 + difference 5 3) sourceC2629) = raw36806 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36806; decide +kernel
    rw [ha]
    exact (canonical36806 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2629 + difference 4 0) (sourceB2629 + difference 0 4) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4976) := by
    have ha : (tripleCharges (sourceA2629 + difference 4 0) (sourceB2629 + difference 0 4) sourceC2629) = raw36807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36807; decide +kernel
    rw [ha]
    exact (canonical36807 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2629 + difference 4 1) (sourceB2629 + difference 1 4) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2629 + difference 4 1) (sourceB2629 + difference 1 4) sourceC2629) = raw36808 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36808; decide +kernel
    rw [ha]
    exact (canonical36808 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2629 + difference 4 2) (sourceB2629 + difference 2 4) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5215) := by
    have ha : (tripleCharges (sourceA2629 + difference 4 2) (sourceB2629 + difference 2 4) sourceC2629) = raw36809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36809; decide +kernel
    rw [ha]
    exact (canonical36809 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2629 + difference 4 3) (sourceB2629 + difference 3 4) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2629 + difference 4 3) (sourceB2629 + difference 3 4) sourceC2629) = raw36810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36810; decide +kernel
    rw [ha]
    exact (canonical36810 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2629 + difference 4 5) (sourceB2629 + difference 5 4) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA2629 + difference 4 5) (sourceB2629 + difference 5 4) sourceC2629) = raw36811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36811; decide +kernel
    rw [ha]
    exact (canonical36811 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2629 + difference 5 0) (sourceB2629 + difference 0 5) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4770) := by
    have ha : (tripleCharges (sourceA2629 + difference 5 0) (sourceB2629 + difference 0 5) sourceC2629) = raw28411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw28411; decide +kernel
    rw [ha]
    exact (canonical28411 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2629 + difference 5 1) (sourceB2629 + difference 1 5) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2629 + difference 5 1) (sourceB2629 + difference 1 5) sourceC2629) = raw36812 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36812; decide +kernel
    rw [ha]
    exact (canonical36812 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2629 + difference 5 2) (sourceB2629 + difference 2 5) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2629 + difference 5 2) (sourceB2629 + difference 2 5) sourceC2629) = raw36813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36813; decide +kernel
    rw [ha]
    exact (canonical36813 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2629 + difference 5 3) (sourceB2629 + difference 3 5) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2629 + difference 5 3) (sourceB2629 + difference 3 5) sourceC2629) = raw28395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw28395; decide +kernel
    rw [ha]
    exact (canonical28395 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2629 + difference 5 4) (sourceB2629 + difference 4 5) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2629 + difference 5 4) (sourceB2629 + difference 4 5) sourceC2629) = raw36814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36814; decide +kernel
    rw [ha]
    exact (canonical36814 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2629 sourceB2629 sourceC2629
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2629, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2094 : Integer.Sparse.reindex keyMap MixedData.row2094 = numericRow2094 := by decide +kernel

theorem numericCheck2094 (x : Master → ℝ) : Integer.Sparse.eval numericRow2094 x =
    (4 : ℝ) * reducedSource2094 x := by
  norm_num [numericRow2094, reducedSource2094, Integer.Sparse.eval, Sparse.eval, nodeValue4763, nodeValue4769, nodeValue4770, nodeValue4846, nodeValue4938, nodeValue4945, nodeValue4975, nodeValue4976, nodeValue5099, nodeValue5205, nodeValue5215, nodeValue5238, nodeValue5241, nodeValue5242, nodeValue5248, nodeValue5274, nodeValue5275, nodeValue5277, nodeValue5282, nodeValue5284, nodeValue5287]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2094 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2094 (mixedVector B) = 0 := by
  have h4763 : mixedVector B (Sum.inr 4763) = Sparse.eval nodeValue4763 (mixedVector B) := by
    change mixedMoment B node4763 node4763Labels = _
    exact sound4763 B hB hF
  have h4769 : mixedVector B (Sum.inr 4769) = Sparse.eval nodeValue4769 (mixedVector B) := by
    change mixedMoment B node4769 node4769Labels = _
    exact sound4769 B hB hF
  have h4770 : mixedVector B (Sum.inr 4770) = Sparse.eval nodeValue4770 (mixedVector B) := by
    change mixedMoment B node4770 node4770Labels = _
    exact sound4770 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4938 : mixedVector B (Sum.inr 4938) = Sparse.eval nodeValue4938 (mixedVector B) := by
    change mixedMoment B node4938 node4938Labels = _
    exact sound4938 B hB hF
  have h4945 : mixedVector B (Sum.inr 4945) = Sparse.eval nodeValue4945 (mixedVector B) := by
    change mixedMoment B node4945 node4945Labels = _
    exact sound4945 B hB hF
  have h4975 : mixedVector B (Sum.inr 4975) = Sparse.eval nodeValue4975 (mixedVector B) := by
    change mixedMoment B node4975 node4975Labels = _
    exact sound4975 B hB hF
  have h4976 : mixedVector B (Sum.inr 4976) = Sparse.eval nodeValue4976 (mixedVector B) := by
    change mixedMoment B node4976 node4976Labels = _
    exact sound4976 B hB hF
  have h5099 : mixedVector B (Sum.inr 5099) = Sparse.eval nodeValue5099 (mixedVector B) := by
    change mixedMoment B node5099 node5099Labels = _
    exact sound5099 B hB hF
  have h5205 : mixedVector B (Sum.inr 5205) = Sparse.eval nodeValue5205 (mixedVector B) := by
    change mixedMoment B node5205 node5205Labels = _
    exact sound5205 B hB hF
  have h5215 : mixedVector B (Sum.inr 5215) = Sparse.eval nodeValue5215 (mixedVector B) := by
    change mixedMoment B node5215 node5215Labels = _
    exact sound5215 B hB hF
  have h5238 : mixedVector B (Sum.inr 5238) = Sparse.eval nodeValue5238 (mixedVector B) := by
    change mixedMoment B node5238 node5238Labels = _
    exact sound5238 B hB hF
  have h5241 : mixedVector B (Sum.inr 5241) = Sparse.eval nodeValue5241 (mixedVector B) := by
    change mixedMoment B node5241 node5241Labels = _
    exact sound5241 B hB hF
  have h5242 : mixedVector B (Sum.inr 5242) = Sparse.eval nodeValue5242 (mixedVector B) := by
    change mixedMoment B node5242 node5242Labels = _
    exact sound5242 B hB hF
  have h5248 : mixedVector B (Sum.inr 5248) = Sparse.eval nodeValue5248 (mixedVector B) := by
    change mixedMoment B node5248 node5248Labels = _
    exact sound5248 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5277 : mixedVector B (Sum.inr 5277) = Sparse.eval nodeValue5277 (mixedVector B) := by
    change mixedMoment B node5277 node5277Labels = _
    exact sound5277 B hB hF
  have h5282 : mixedVector B (Sum.inr 5282) = Sparse.eval nodeValue5282 (mixedVector B) := by
    change mixedMoment B node5282 node5282Labels = _
    exact sound5282 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5287 : mixedVector B (Sum.inr 5287) = Sparse.eval nodeValue5287 (mixedVector B) := by
    change mixedMoment B node5287 node5287Labels = _
    exact sound5287 B hB hF
  simpa only [sourceForm2629, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4763, h4769, h4770, h4846, h4938, h4945, h4975, h4976, h5099, h5205, h5215, h5238, h5241, h5242, h5248, h5274, h5275, h5277, h5282, h5284, h5287, reducedSource2094] using sourceEq2629 B hB

theorem rowSound2094_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2094 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2094, numericCheck2094, reducedZero2094 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094_e_oai
