-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:06:20.04743+00:00
-- url     : https://prove2.me/submissions/5f27b88a-1771-4a41-a916-08576b3cea0d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E101
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

theorem delete_zero_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (σ : Equiv.Perm (Fin (n + 1))) (hz : ∀ i, A i (σ 0) = 0) :
    mixedMoment B A label =
      mixedMoment B (fun i j => A i (σ j.succ)) (fun j => label (σ j.succ)) := by
  rw [← mixedMoment_factor_permutation B A label σ]
  exact mixedMoment_zero_first_factor B _ _ hz

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1890 raw1890Labels = mixedMoment B node4927 node4927Labels := by
  calc
    mixedMoment B raw1890 raw1890Labels = mixedMoment B raw1890step0 raw1890step0Labels := by
      have ha : raw1890step0 = (fun i j => raw1890 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1890step0 raw1890; decide +kernel
      have hl : raw1890step0Labels = raw1890Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1890 raw1890Labels permutation152 permutation4
    mixedMoment B raw1890step0 raw1890step0Labels = mixedMoment B raw1890step1 raw1890step1Labels := by
      have ha : raw1890step1 = raw1890step0 := by apply Matrix.ext; unfold raw1890step1 raw1890step0; decide +kernel
      have hl : raw1890step0Labels = labelEmbedding7 ∘ raw1890step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1890step0 raw1890step0Labels raw1890step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4927 node4927Labels := by rfl

theorem canonical1891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1891 raw1891Labels = mixedMoment B node2317 node2317Labels := by
  calc
    mixedMoment B raw1891 raw1891Labels = mixedMoment B raw1891step0 raw1891step0Labels := by
      have ha : raw1891step0 = (fun i j => raw1891 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1891step0 raw1891; decide +kernel
      have hl : raw1891step0Labels = raw1891Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1891 raw1891Labels permutation152 permutation4
    _ = mixedMoment B node2317 node2317Labels := by rfl

theorem canonical1892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1892 raw1892Labels = mixedMoment B node3399 node3399Labels := by
  calc
    mixedMoment B raw1892 raw1892Labels = mixedMoment B raw1892step0 raw1892step0Labels := by
      have ha : raw1892step0 = (fun i j => raw1892 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1892step0 raw1892; decide +kernel
      have hl : raw1892step0Labels = raw1892Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1892 raw1892Labels permutation152 permutation6
    mixedMoment B raw1892step0 raw1892step0Labels = mixedMoment B raw1892step1 raw1892step1Labels := by
      have ha : raw1892step1 = -raw1892step0 := by apply Matrix.ext; change ∀ i j, raw1892step1 i j = -(raw1892step0 i j); unfold raw1892step1 raw1892step0; decide +kernel
      have hl : raw1892step1Labels = raw1892step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1892step1 raw1892step1Labels = mixedMoment B raw1892step2 raw1892step2Labels := by
      have ha : raw1892step2 = raw1892step1 := by apply Matrix.ext; unfold raw1892step2 raw1892step1; decide +kernel
      have hl : raw1892step1Labels = labelEmbedding1 ∘ raw1892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1892step1 raw1892step1Labels raw1892step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3399 node3399Labels := by rfl

theorem canonical1893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1893 raw1893Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw1893 raw1893Labels = mixedMoment B raw1893step0 raw1893step0Labels := by
      have ha : raw1893step0 = (fun i j => raw1893 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1893step0 raw1893; decide +kernel
      have hl : raw1893step0Labels = raw1893Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1893 raw1893Labels permutation152 permutation4
    mixedMoment B raw1893step0 raw1893step0Labels = mixedMoment B raw1893step1 raw1893step1Labels := by
      have ha : raw1893step1 = raw1893step0 := by apply Matrix.ext; unfold raw1893step1 raw1893step0; decide +kernel
      have hl : raw1893step0Labels = labelEmbedding7 ∘ raw1893step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1893step0 raw1893step0Labels raw1893step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4928 node4928Labels := by rfl

theorem canonical1894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1894 raw1894Labels = mixedMoment B node2318 node2318Labels := by
  calc
    mixedMoment B raw1894 raw1894Labels = mixedMoment B raw1894step0 raw1894step0Labels := by
      have ha : raw1894step0 = (fun i j => raw1894 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1894step0 raw1894; decide +kernel
      have hl : raw1894step0Labels = raw1894Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1894 raw1894Labels permutation152 permutation4
    _ = mixedMoment B node2318 node2318Labels := by rfl

theorem canonical1895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1895 raw1895Labels = mixedMoment B node3400 node3400Labels := by
  calc
    mixedMoment B raw1895 raw1895Labels = mixedMoment B raw1895step0 raw1895step0Labels := by
      have ha : raw1895step0 = (fun i j => raw1895 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1895step0 raw1895; decide +kernel
      have hl : raw1895step0Labels = raw1895Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1895 raw1895Labels permutation152 permutation6
    mixedMoment B raw1895step0 raw1895step0Labels = mixedMoment B raw1895step1 raw1895step1Labels := by
      have ha : raw1895step1 = -raw1895step0 := by apply Matrix.ext; change ∀ i j, raw1895step1 i j = -(raw1895step0 i j); unfold raw1895step1 raw1895step0; decide +kernel
      have hl : raw1895step1Labels = raw1895step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1895step1 raw1895step1Labels = mixedMoment B raw1895step2 raw1895step2Labels := by
      have ha : raw1895step2 = raw1895step1 := by apply Matrix.ext; unfold raw1895step2 raw1895step1; decide +kernel
      have hl : raw1895step1Labels = labelEmbedding1 ∘ raw1895step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1895step1 raw1895step1Labels raw1895step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3400 node3400Labels := by rfl

theorem canonical1896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1896 raw1896Labels = mixedMoment B node4936 node4936Labels := by
  calc
    mixedMoment B raw1896 raw1896Labels = mixedMoment B raw1896step0 raw1896step0Labels := by
      have ha : raw1896step0 = (fun i j => raw1896 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1896step0 raw1896; decide +kernel
      have hl : raw1896step0Labels = raw1896Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1896 raw1896Labels permutation152 permutation4
    mixedMoment B raw1896step0 raw1896step0Labels = mixedMoment B raw1896step1 raw1896step1Labels := by
      have ha : raw1896step1 = raw1896step0 := by apply Matrix.ext; unfold raw1896step1 raw1896step0; decide +kernel
      have hl : raw1896step0Labels = labelEmbedding7 ∘ raw1896step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1896step0 raw1896step0Labels raw1896step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4936 node4936Labels := by rfl

theorem canonical1897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1897 raw1897Labels = mixedMoment B node2328 node2328Labels := by
  calc
    mixedMoment B raw1897 raw1897Labels = mixedMoment B raw1897step0 raw1897step0Labels := by
      have ha : raw1897step0 = (fun i j => raw1897 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1897step0 raw1897; decide +kernel
      have hl : raw1897step0Labels = raw1897Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1897 raw1897Labels permutation152 permutation4
    _ = mixedMoment B node2328 node2328Labels := by rfl

theorem canonical1898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1898 raw1898Labels = mixedMoment B node3401 node3401Labels := by
  calc
    mixedMoment B raw1898 raw1898Labels = mixedMoment B raw1898step0 raw1898step0Labels := by
      have ha : raw1898step0 = (fun i j => raw1898 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1898step0 raw1898; decide +kernel
      have hl : raw1898step0Labels = raw1898Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1898 raw1898Labels permutation152 permutation6
    mixedMoment B raw1898step0 raw1898step0Labels = mixedMoment B raw1898step1 raw1898step1Labels := by
      have ha : raw1898step1 = -raw1898step0 := by apply Matrix.ext; change ∀ i j, raw1898step1 i j = -(raw1898step0 i j); unfold raw1898step1 raw1898step0; decide +kernel
      have hl : raw1898step1Labels = raw1898step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1898step1 raw1898step1Labels = mixedMoment B raw1898step2 raw1898step2Labels := by
      have ha : raw1898step2 = raw1898step1 := by apply Matrix.ext; unfold raw1898step2 raw1898step1; decide +kernel
      have hl : raw1898step1Labels = labelEmbedding1 ∘ raw1898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1898step1 raw1898step1Labels raw1898step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3401 node3401Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1932 raw1932Labels = mixedMoment B node4960 node4960Labels := by
  calc
    mixedMoment B raw1932 raw1932Labels = mixedMoment B raw1932step0 raw1932step0Labels := by
      have ha : raw1932step0 = (fun i j => raw1932 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1932step0 raw1932; decide +kernel
      have hl : raw1932step0Labels = raw1932Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1932 raw1932Labels permutation152 permutation5
    mixedMoment B raw1932step0 raw1932step0Labels = mixedMoment B raw1932step1 raw1932step1Labels := by
      have ha : raw1932step1 = raw1932step0 := by apply Matrix.ext; unfold raw1932step1 raw1932step0; decide +kernel
      have hl : raw1932step0Labels = labelEmbedding8 ∘ raw1932step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1932step0 raw1932step0Labels raw1932step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4960 node4960Labels := by rfl

theorem canonical1933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1933 raw1933Labels = mixedMoment B node2412 node2412Labels := by
  calc
    mixedMoment B raw1933 raw1933Labels = mixedMoment B raw1933step0 raw1933step0Labels := by
      have ha : raw1933step0 = (fun i j => raw1933 (permutation664 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1933step0 raw1933; decide +kernel
      have hl : raw1933step0Labels = raw1933Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1933 raw1933Labels permutation664 permutation4
    mixedMoment B raw1933step0 raw1933step0Labels = mixedMoment B raw1933step1 raw1933step1Labels := by
      have ha : raw1933step1 = -raw1933step0 := by apply Matrix.ext; change ∀ i j, raw1933step1 i j = -(raw1933step0 i j); unfold raw1933step1 raw1933step0; decide +kernel
      have hl : raw1933step1Labels = raw1933step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2412 node2412Labels := by rfl

theorem canonical1934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1934 raw1934Labels = mixedMoment B node3426 node3426Labels := by
  calc
    mixedMoment B raw1934 raw1934Labels = mixedMoment B raw1934step0 raw1934step0Labels := by
      have ha : raw1934step0 = (fun i j => raw1934 (permutation663 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1934step0 raw1934; decide +kernel
      have hl : raw1934step0Labels = raw1934Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1934 raw1934Labels permutation663 permutation6
    mixedMoment B raw1934step0 raw1934step0Labels = mixedMoment B raw1934step1 raw1934step1Labels := by
      have ha : raw1934step1 = raw1934step0 := by apply Matrix.ext; unfold raw1934step1 raw1934step0; decide +kernel
      have hl : raw1934step0Labels = labelEmbedding1 ∘ raw1934step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1934step0 raw1934step0Labels raw1934step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3426 node3426Labels := by rfl

theorem canonical1935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1935 raw1935Labels = mixedMoment B node4961 node4961Labels := by
  calc
    mixedMoment B raw1935 raw1935Labels = mixedMoment B raw1935step0 raw1935step0Labels := by
      have ha : raw1935step0 = (fun i j => raw1935 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1935step0 raw1935; decide +kernel
      have hl : raw1935step0Labels = raw1935Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1935 raw1935Labels permutation152 permutation5
    mixedMoment B raw1935step0 raw1935step0Labels = mixedMoment B raw1935step1 raw1935step1Labels := by
      have ha : raw1935step1 = raw1935step0 := by apply Matrix.ext; unfold raw1935step1 raw1935step0; decide +kernel
      have hl : raw1935step0Labels = labelEmbedding8 ∘ raw1935step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1935step0 raw1935step0Labels raw1935step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4961 node4961Labels := by rfl

theorem canonical1936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1936 raw1936Labels = mixedMoment B node2796 node2796Labels := by
  calc
    mixedMoment B raw1936 raw1936Labels = mixedMoment B raw1936step0 raw1936step0Labels := by
      have ha : raw1936step0 = (fun i j => raw1936 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1936step0 raw1936; decide +kernel
      have hl : raw1936step0Labels = raw1936Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1936 raw1936Labels permutation153 permutation4
    _ = mixedMoment B node2796 node2796Labels := by rfl

theorem canonical1937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1937 raw1937Labels = mixedMoment B node3589 node3589Labels := by
  calc
    mixedMoment B raw1937 raw1937Labels = mixedMoment B raw1937step0 raw1937step0Labels := by
      have ha : raw1937step0 = (fun i j => raw1937 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1937step0 raw1937; decide +kernel
      have hl : raw1937step0Labels = raw1937Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1937 raw1937Labels permutation160 permutation3
    mixedMoment B raw1937step0 raw1937step0Labels = mixedMoment B raw1937step1 raw1937step1Labels := by
      have ha : raw1937step1 = -raw1937step0 := by apply Matrix.ext; change ∀ i j, raw1937step1 i j = -(raw1937step0 i j); unfold raw1937step1 raw1937step0; decide +kernel
      have hl : raw1937step1Labels = raw1937step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1937step1 raw1937step1Labels = mixedMoment B raw1937step2 raw1937step2Labels := by
      have ha : raw1937step2 = raw1937step1 := by apply Matrix.ext; unfold raw1937step2 raw1937step1; decide +kernel
      have hl : raw1937step1Labels = labelEmbedding1 ∘ raw1937step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1937step1 raw1937step1Labels raw1937step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3589 node3589Labels := by rfl

theorem canonical1947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1947 raw1947Labels = mixedMoment B node4969 node4969Labels := by
  calc
    mixedMoment B raw1947 raw1947Labels = mixedMoment B raw1947step0 raw1947step0Labels := by
      have ha : raw1947step0 = (fun i j => raw1947 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1947step0 raw1947; decide +kernel
      have hl : raw1947step0Labels = raw1947Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1947 raw1947Labels permutation152 permutation5
    mixedMoment B raw1947step0 raw1947step0Labels = mixedMoment B raw1947step1 raw1947step1Labels := by
      have ha : raw1947step1 = raw1947step0 := by apply Matrix.ext; unfold raw1947step1 raw1947step0; decide +kernel
      have hl : raw1947step0Labels = labelEmbedding8 ∘ raw1947step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1947step0 raw1947step0Labels raw1947step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4969 node4969Labels := by rfl

theorem canonical1948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1948 raw1948Labels = mixedMoment B node2804 node2804Labels := by
  calc
    mixedMoment B raw1948 raw1948Labels = mixedMoment B raw1948step0 raw1948step0Labels := by
      have ha : raw1948step0 = (fun i j => raw1948 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1948step0 raw1948; decide +kernel
      have hl : raw1948step0Labels = raw1948Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1948 raw1948Labels permutation164 permutation4
    _ = mixedMoment B node2804 node2804Labels := by rfl

theorem canonical1949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1949 raw1949Labels = mixedMoment B node3586 node3586Labels := by
  calc
    mixedMoment B raw1949 raw1949Labels = mixedMoment B raw1949step0 raw1949step0Labels := by
      have ha : raw1949step0 = (fun i j => raw1949 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1949step0 raw1949; decide +kernel
      have hl : raw1949step0Labels = raw1949Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1949 raw1949Labels permutation153 permutation3
    mixedMoment B raw1949step0 raw1949step0Labels = mixedMoment B raw1949step1 raw1949step1Labels := by
      have ha : raw1949step1 = -raw1949step0 := by apply Matrix.ext; change ∀ i j, raw1949step1 i j = -(raw1949step0 i j); unfold raw1949step1 raw1949step0; decide +kernel
      have hl : raw1949step1Labels = raw1949step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1949step1 raw1949step1Labels = mixedMoment B raw1949step2 raw1949step2Labels := by
      have ha : raw1949step2 = raw1949step1 := by apply Matrix.ext; unfold raw1949step2 raw1949step1; decide +kernel
      have hl : raw1949step1Labels = labelEmbedding1 ∘ raw1949step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1949step1 raw1949step1Labels raw1949step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3586 node3586Labels := by rfl

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

theorem canonical2076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2076 raw2076Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw2076 raw2076Labels = mixedMoment B raw2076step0 raw2076step0Labels := by
      have ha : raw2076step0 = (fun i j => raw2076 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2076step0 raw2076; decide +kernel
      have hl : raw2076step0Labels = raw2076Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2076 raw2076Labels permutation152 permutation4
    mixedMoment B raw2076step0 raw2076step0Labels = mixedMoment B raw2076step1 raw2076step1Labels := by
      have ha : raw2076step1 = raw2076step0 := by apply Matrix.ext; unfold raw2076step1 raw2076step0; decide +kernel
      have hl : raw2076step0Labels = labelEmbedding7 ∘ raw2076step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2076step0 raw2076step0Labels raw2076step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

theorem canonical2077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2077 raw2077Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw2077 raw2077Labels = mixedMoment B raw2077step0 raw2077step0Labels := by
      have ha : raw2077step0 = (fun i j => raw2077 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2077step0 raw2077; decide +kernel
      have hl : raw2077step0Labels = raw2077Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2077 raw2077Labels permutation152 permutation4
    _ = mixedMoment B node2452 node2452Labels := by rfl

theorem canonical2078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2078 raw2078Labels = mixedMoment B node3433 node3433Labels := by
  calc
    mixedMoment B raw2078 raw2078Labels = mixedMoment B raw2078step0 raw2078step0Labels := by
      have ha : raw2078step0 = (fun i j => raw2078 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2078step0 raw2078; decide +kernel
      have hl : raw2078step0Labels = raw2078Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2078 raw2078Labels permutation152 permutation6
    mixedMoment B raw2078step0 raw2078step0Labels = mixedMoment B raw2078step1 raw2078step1Labels := by
      have ha : raw2078step1 = -raw2078step0 := by apply Matrix.ext; change ∀ i j, raw2078step1 i j = -(raw2078step0 i j); unfold raw2078step1 raw2078step0; decide +kernel
      have hl : raw2078step1Labels = raw2078step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2078step1 raw2078step1Labels = mixedMoment B raw2078step2 raw2078step2Labels := by
      have ha : raw2078step2 = raw2078step1 := by apply Matrix.ext; unfold raw2078step2 raw2078step1; decide +kernel
      have hl : raw2078step1Labels = labelEmbedding1 ∘ raw2078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2078step1 raw2078step1Labels raw2078step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3433 node3433Labels := by rfl

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

theorem canonical2220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2220 raw2220Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw2220 raw2220Labels = mixedMoment B raw2220step0 raw2220step0Labels := by
      have ha : raw2220step0 = (fun i j => raw2220 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2220step0 raw2220; decide +kernel
      have hl : raw2220step0Labels = raw2220Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2220 raw2220Labels permutation152 permutation5
    mixedMoment B raw2220step0 raw2220step0Labels = mixedMoment B raw2220step1 raw2220step1Labels := by
      have ha : raw2220step1 = raw2220step0 := by apply Matrix.ext; unfold raw2220step1 raw2220step0; decide +kernel
      have hl : raw2220step0Labels = labelEmbedding8 ∘ raw2220step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2220step0 raw2220step0Labels raw2220step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5192 node5192Labels := by rfl

theorem canonical2221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2221 raw2221Labels = mixedMoment B node2853 node2853Labels := by
  calc
    mixedMoment B raw2221 raw2221Labels = mixedMoment B raw2221step0 raw2221step0Labels := by
      have ha : raw2221step0 = (fun i j => raw2221 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2221step0 raw2221; decide +kernel
      have hl : raw2221step0Labels = raw2221Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2221 raw2221Labels permutation152 permutation4
    _ = mixedMoment B node2853 node2853Labels := by rfl

theorem canonical2222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2222 raw2222Labels = mixedMoment B node3620 node3620Labels := by
  calc
    mixedMoment B raw2222 raw2222Labels = mixedMoment B raw2222step0 raw2222step0Labels := by
      have ha : raw2222step0 = (fun i j => raw2222 (permutation216 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2222step0 raw2222; decide +kernel
      have hl : raw2222step0Labels = raw2222Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2222 raw2222Labels permutation216 permutation3
    mixedMoment B raw2222step0 raw2222step0Labels = mixedMoment B raw2222step1 raw2222step1Labels := by
      have ha : raw2222step1 = -raw2222step0 := by apply Matrix.ext; change ∀ i j, raw2222step1 i j = -(raw2222step0 i j); unfold raw2222step1 raw2222step0; decide +kernel
      have hl : raw2222step1Labels = raw2222step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2222step1 raw2222step1Labels = mixedMoment B raw2222step2 raw2222step2Labels := by
      have ha : raw2222step2 = raw2222step1 := by apply Matrix.ext; unfold raw2222step2 raw2222step1; decide +kernel
      have hl : raw2222step1Labels = labelEmbedding1 ∘ raw2222step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2222step1 raw2222step1Labels raw2222step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3620 node3620Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2379 raw2379Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw2379 raw2379Labels = mixedMoment B raw2379step0 raw2379step0Labels := by
      have ha : raw2379step0 = (fun i j => raw2379 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2379step0 raw2379; decide +kernel
      have hl : raw2379step0Labels = raw2379Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2379 raw2379Labels permutation152 permutation4
    mixedMoment B raw2379step0 raw2379step0Labels = mixedMoment B raw2379step1 raw2379step1Labels := by
      have ha : raw2379step1 = raw2379step0 := by apply Matrix.ext; unfold raw2379step1 raw2379step0; decide +kernel
      have hl : raw2379step0Labels = labelEmbedding7 ∘ raw2379step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2379step0 raw2379step0Labels raw2379step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5341 node5341Labels := by rfl

theorem canonical2380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2380 raw2380Labels = mixedMoment B node3678 node3678Labels := by
  calc
    mixedMoment B raw2380 raw2380Labels = mixedMoment B raw2380step0 raw2380step0Labels := by
      have ha : raw2380step0 = (fun i j => raw2380 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2380step0 raw2380; decide +kernel
      have hl : raw2380step0Labels = raw2380Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2380 raw2380Labels permutation152 permutation4
    _ = mixedMoment B node3678 node3678Labels := by rfl

theorem canonical2381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2381 raw2381Labels = mixedMoment B node3744 node3744Labels := by
  calc
    mixedMoment B raw2381 raw2381Labels = mixedMoment B raw2381step0 raw2381step0Labels := by
      have ha : raw2381step0 = (fun i j => raw2381 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2381step0 raw2381; decide +kernel
      have hl : raw2381step0Labels = raw2381Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2381 raw2381Labels permutation688 permutation6
    mixedMoment B raw2381step0 raw2381step0Labels = mixedMoment B raw2381step1 raw2381step1Labels := by
      have ha : raw2381step1 = raw2381step0 := by apply Matrix.ext; unfold raw2381step1 raw2381step0; decide +kernel
      have hl : raw2381step0Labels = labelEmbedding1 ∘ raw2381step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2381step0 raw2381step0Labels raw2381step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3744 node3744Labels := by rfl

theorem canonical2385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2385 raw2385Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw2385 raw2385Labels = mixedMoment B raw2385step0 raw2385step0Labels := by
      have ha : raw2385step0 = (fun i j => raw2385 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2385step0 raw2385; decide +kernel
      have hl : raw2385step0Labels = raw2385Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2385 raw2385Labels permutation152 permutation4
    mixedMoment B raw2385step0 raw2385step0Labels = mixedMoment B raw2385step1 raw2385step1Labels := by
      have ha : raw2385step1 = raw2385step0 := by apply Matrix.ext; unfold raw2385step1 raw2385step0; decide +kernel
      have hl : raw2385step0Labels = labelEmbedding7 ∘ raw2385step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2385step0 raw2385step0Labels raw2385step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

theorem canonical2386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2386 raw2386Labels = mixedMoment B node3683 node3683Labels := by
  calc
    mixedMoment B raw2386 raw2386Labels = mixedMoment B raw2386step0 raw2386step0Labels := by
      have ha : raw2386step0 = (fun i j => raw2386 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2386step0 raw2386; decide +kernel
      have hl : raw2386step0Labels = raw2386Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2386 raw2386Labels permutation152 permutation4
    _ = mixedMoment B node3683 node3683Labels := by rfl

theorem canonical2387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2387 raw2387Labels = mixedMoment B node3746 node3746Labels := by
  calc
    mixedMoment B raw2387 raw2387Labels = mixedMoment B raw2387step0 raw2387step0Labels := by
      have ha : raw2387step0 = (fun i j => raw2387 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2387step0 raw2387; decide +kernel
      have hl : raw2387step0Labels = raw2387Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2387 raw2387Labels permutation153 permutation6
    mixedMoment B raw2387step0 raw2387step0Labels = mixedMoment B raw2387step1 raw2387step1Labels := by
      have ha : raw2387step1 = -raw2387step0 := by apply Matrix.ext; change ∀ i j, raw2387step1 i j = -(raw2387step0 i j); unfold raw2387step1 raw2387step0; decide +kernel
      have hl : raw2387step1Labels = raw2387step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2387step1 raw2387step1Labels = mixedMoment B raw2387step2 raw2387step2Labels := by
      have ha : raw2387step2 = raw2387step1 := by apply Matrix.ext; unfold raw2387step2 raw2387step1; decide +kernel
      have hl : raw2387step1Labels = labelEmbedding1 ∘ raw2387step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2387step1 raw2387step1Labels raw2387step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3746 node3746Labels := by rfl

theorem canonical2388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2388 raw2388Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw2388 raw2388Labels = mixedMoment B raw2388step0 raw2388step0Labels := by
      have ha : raw2388step0 = (fun i j => raw2388 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2388step0 raw2388; decide +kernel
      have hl : raw2388step0Labels = raw2388Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2388 raw2388Labels permutation152 permutation4
    mixedMoment B raw2388step0 raw2388step0Labels = mixedMoment B raw2388step1 raw2388step1Labels := by
      have ha : raw2388step1 = raw2388step0 := by apply Matrix.ext; unfold raw2388step1 raw2388step0; decide +kernel
      have hl : raw2388step0Labels = labelEmbedding7 ∘ raw2388step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2388step0 raw2388step0Labels raw2388step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

theorem canonical2389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2389 raw2389Labels = mixedMoment B node3687 node3687Labels := by
  calc
    mixedMoment B raw2389 raw2389Labels = mixedMoment B raw2389step0 raw2389step0Labels := by
      have ha : raw2389step0 = (fun i j => raw2389 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2389step0 raw2389; decide +kernel
      have hl : raw2389step0Labels = raw2389Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2389 raw2389Labels permutation152 permutation4
    _ = mixedMoment B node3687 node3687Labels := by rfl

theorem canonical2390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2390 raw2390Labels = mixedMoment B node3749 node3749Labels := by
  calc
    mixedMoment B raw2390 raw2390Labels = mixedMoment B raw2390step0 raw2390step0Labels := by
      have ha : raw2390step0 = (fun i j => raw2390 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2390step0 raw2390; decide +kernel
      have hl : raw2390step0Labels = raw2390Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2390 raw2390Labels permutation158 permutation6
    mixedMoment B raw2390step0 raw2390step0Labels = mixedMoment B raw2390step1 raw2390step1Labels := by
      have ha : raw2390step1 = -raw2390step0 := by apply Matrix.ext; change ∀ i j, raw2390step1 i j = -(raw2390step0 i j); unfold raw2390step1 raw2390step0; decide +kernel
      have hl : raw2390step1Labels = raw2390step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2390step1 raw2390step1Labels = mixedMoment B raw2390step2 raw2390step2Labels := by
      have ha : raw2390step2 = raw2390step1 := by apply Matrix.ext; unfold raw2390step2 raw2390step1; decide +kernel
      have hl : raw2390step1Labels = labelEmbedding1 ∘ raw2390step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2390step1 raw2390step1Labels raw2390step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3749 node3749Labels := by rfl

theorem canonical2406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2406 raw2406Labels = mixedMoment B node5363 node5363Labels := by
  calc
    mixedMoment B raw2406 raw2406Labels = mixedMoment B raw2406step0 raw2406step0Labels := by
      have ha : raw2406step0 = (fun i j => raw2406 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2406step0 raw2406; decide +kernel
      have hl : raw2406step0Labels = raw2406Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2406 raw2406Labels permutation152 permutation4
    mixedMoment B raw2406step0 raw2406step0Labels = mixedMoment B raw2406step1 raw2406step1Labels := by
      have ha : raw2406step1 = raw2406step0 := by apply Matrix.ext; unfold raw2406step1 raw2406step0; decide +kernel
      have hl : raw2406step0Labels = labelEmbedding7 ∘ raw2406step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2406step0 raw2406step0Labels raw2406step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5363 node5363Labels := by rfl

theorem canonical2407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2407 raw2407Labels = mixedMoment B node3701 node3701Labels := by
  calc
    mixedMoment B raw2407 raw2407Labels = mixedMoment B raw2407step0 raw2407step0Labels := by
      have ha : raw2407step0 = (fun i j => raw2407 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2407step0 raw2407; decide +kernel
      have hl : raw2407step0Labels = raw2407Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2407 raw2407Labels permutation152 permutation4
    _ = mixedMoment B node3701 node3701Labels := by rfl

theorem canonical2408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2408 raw2408Labels = mixedMoment B node3751 node3751Labels := by
  calc
    mixedMoment B raw2408 raw2408Labels = mixedMoment B raw2408step0 raw2408step0Labels := by
      have ha : raw2408step0 = (fun i j => raw2408 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2408step0 raw2408; decide +kernel
      have hl : raw2408step0Labels = raw2408Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2408 raw2408Labels permutation152 permutation6
    mixedMoment B raw2408step0 raw2408step0Labels = mixedMoment B raw2408step1 raw2408step1Labels := by
      have ha : raw2408step1 = -raw2408step0 := by apply Matrix.ext; change ∀ i j, raw2408step1 i j = -(raw2408step0 i j); unfold raw2408step1 raw2408step0; decide +kernel
      have hl : raw2408step1Labels = raw2408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2408step1 raw2408step1Labels = mixedMoment B raw2408step2 raw2408step2Labels := by
      have ha : raw2408step2 = raw2408step1 := by apply Matrix.ext; unfold raw2408step2 raw2408step1; decide +kernel
      have hl : raw2408step1Labels = labelEmbedding1 ∘ raw2408step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2408step1 raw2408step1Labels raw2408step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3751 node3751Labels := by rfl

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

theorem canonical2463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2463 raw2463Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw2463 raw2463Labels = mixedMoment B raw2463step0 raw2463step0Labels := by
      have ha : raw2463step0 = (fun i j => raw2463 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2463step0 raw2463; decide +kernel
      have hl : raw2463step0Labels = raw2463Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2463 raw2463Labels permutation152 permutation4
    mixedMoment B raw2463step0 raw2463step0Labels = mixedMoment B raw2463step1 raw2463step1Labels := by
      have ha : raw2463step1 = raw2463step0 := by apply Matrix.ext; unfold raw2463step1 raw2463step0; decide +kernel
      have hl : raw2463step0Labels = labelEmbedding7 ∘ raw2463step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2463step0 raw2463step0Labels raw2463step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical2464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2464 raw2464Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw2464 raw2464Labels = mixedMoment B raw2464step0 raw2464step0Labels := by
      have ha : raw2464step0 = (fun i j => raw2464 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2464step0 raw2464; decide +kernel
      have hl : raw2464step0Labels = raw2464Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2464 raw2464Labels permutation152 permutation4
    _ = mixedMoment B node3781 node3781Labels := by rfl

theorem canonical2465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2465 raw2465Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw2465 raw2465Labels = mixedMoment B raw2465step0 raw2465step0Labels := by
      have ha : raw2465step0 = (fun i j => raw2465 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2465step0 raw2465; decide +kernel
      have hl : raw2465step0Labels = raw2465Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2465 raw2465Labels permutation153 permutation6
    mixedMoment B raw2465step0 raw2465step0Labels = mixedMoment B raw2465step1 raw2465step1Labels := by
      have ha : raw2465step1 = -raw2465step0 := by apply Matrix.ext; change ∀ i j, raw2465step1 i j = -(raw2465step0 i j); unfold raw2465step1 raw2465step0; decide +kernel
      have hl : raw2465step1Labels = raw2465step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2465step1 raw2465step1Labels = mixedMoment B raw2465step2 raw2465step2Labels := by
      have ha : raw2465step2 = raw2465step1 := by apply Matrix.ext; unfold raw2465step2 raw2465step1; decide +kernel
      have hl : raw2465step1Labels = labelEmbedding1 ∘ raw2465step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2465step1 raw2465step1Labels raw2465step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3794 node3794Labels := by rfl

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

theorem canonical2583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2583 raw2583Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw2583 raw2583Labels = mixedMoment B raw2583step0 raw2583step0Labels := by
      have ha : raw2583step0 = (fun i j => raw2583 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2583step0 raw2583; decide +kernel
      have hl : raw2583step0Labels = raw2583Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2583 raw2583Labels permutation152 permutation4
    mixedMoment B raw2583step0 raw2583step0Labels = mixedMoment B raw2583step1 raw2583step1Labels := by
      have ha : raw2583step1 = raw2583step0 := by apply Matrix.ext; unfold raw2583step1 raw2583step0; decide +kernel
      have hl : raw2583step0Labels = labelEmbedding7 ∘ raw2583step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2583step0 raw2583step0Labels raw2583step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

theorem canonical2584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2584 raw2584Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw2584 raw2584Labels = mixedMoment B raw2584step0 raw2584step0Labels := by
      have ha : raw2584step0 = (fun i j => raw2584 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2584step0 raw2584; decide +kernel
      have hl : raw2584step0Labels = raw2584Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2584 raw2584Labels permutation152 permutation4
    _ = mixedMoment B node3945 node3945Labels := by rfl

theorem canonical2585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2585 raw2585Labels = mixedMoment B node3952 node3952Labels := by
  calc
    mixedMoment B raw2585 raw2585Labels = mixedMoment B raw2585step0 raw2585step0Labels := by
      have ha : raw2585step0 = (fun i j => raw2585 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2585step0 raw2585; decide +kernel
      have hl : raw2585step0Labels = raw2585Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2585 raw2585Labels permutation265 permutation6
    mixedMoment B raw2585step0 raw2585step0Labels = mixedMoment B raw2585step1 raw2585step1Labels := by
      have ha : raw2585step1 = -raw2585step0 := by apply Matrix.ext; change ∀ i j, raw2585step1 i j = -(raw2585step0 i j); unfold raw2585step1 raw2585step0; decide +kernel
      have hl : raw2585step1Labels = raw2585step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2585step1 raw2585step1Labels = mixedMoment B raw2585step2 raw2585step2Labels := by
      have ha : raw2585step2 = raw2585step1 := by apply Matrix.ext; unfold raw2585step2 raw2585step1; decide +kernel
      have hl : raw2585step1Labels = labelEmbedding1 ∘ raw2585step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2585step1 raw2585step1Labels raw2585step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3952 node3952Labels := by rfl

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

theorem canonical36858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36858 raw36858Labels = mixedMoment B node5058 node5058Labels := by
  calc
    mixedMoment B raw36858 raw36858Labels = mixedMoment B raw36858step0 raw36858step0Labels := by
      have ha : raw36858step0 = (fun i j => raw36858 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36858step0 raw36858; decide +kernel
      have hl : raw36858step0Labels = raw36858Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36858 raw36858Labels permutation265 permutation2
    _ = mixedMoment B node5058 node5058Labels := by rfl

theorem canonical36859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36859 raw36859Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw36859 raw36859Labels = mixedMoment B raw36859step0 raw36859step0Labels := by
      have hz : ∀ i, raw36859 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw36859step0 = (fun i j => raw36859 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw36859step0 raw36859; decide +kernel
      have hl : raw36859step0Labels = (fun j => raw36859Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw36859 raw36859Labels permutation4 hz
    mixedMoment B raw36859step0 raw36859step0Labels = mixedMoment B raw36859step1 raw36859step1Labels := by
      have ha : raw36859step1 = (fun i j => raw36859step0 (permutation265 i) (permutation0 j)) := by apply Matrix.ext; unfold raw36859step1 raw36859step0; decide +kernel
      have hl : raw36859step1Labels = raw36859step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36859step0 raw36859step0Labels permutation265 permutation0
    mixedMoment B raw36859step1 raw36859step1Labels = mixedMoment B raw36859step2 raw36859step2Labels := by
      have ha : raw36859step2 = raw36859step1 := by apply Matrix.ext; unfold raw36859step2 raw36859step1; decide +kernel
      have hl : raw36859step1Labels = labelEmbedding2 ∘ raw36859step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36859step1 raw36859step1Labels raw36859step2Labels labelEmbedding2 hl
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical36860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36860 raw36860Labels = mixedMoment B node5394 node5394Labels := by
  calc
    mixedMoment B raw36860 raw36860Labels = mixedMoment B raw36860step0 raw36860step0Labels := by
      have ha : raw36860step0 = (fun i j => raw36860 (permutation687 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36860step0 raw36860; decide +kernel
      have hl : raw36860step0Labels = raw36860Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36860 raw36860Labels permutation687 permutation7
    mixedMoment B raw36860step0 raw36860step0Labels = mixedMoment B raw36860step1 raw36860step1Labels := by
      have ha : raw36860step1 = raw36860step0 := by apply Matrix.ext; unfold raw36860step1 raw36860step0; decide +kernel
      have hl : raw36860step0Labels = labelEmbedding10 ∘ raw36860step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36860step0 raw36860step0Labels raw36860step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5394 node5394Labels := by rfl

theorem canonical36861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36861 raw36861Labels = mixedMoment B node5394 node5394Labels := by
  calc
    mixedMoment B raw36861 raw36861Labels = mixedMoment B raw36861step0 raw36861step0Labels := by
      have ha : raw36861step0 = (fun i j => raw36861 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36861step0 raw36861; decide +kernel
      have hl : raw36861step0Labels = raw36861Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36861 raw36861Labels permutation663 permutation7
    mixedMoment B raw36861step0 raw36861step0Labels = mixedMoment B raw36861step1 raw36861step1Labels := by
      have ha : raw36861step1 = raw36861step0 := by apply Matrix.ext; unfold raw36861step1 raw36861step0; decide +kernel
      have hl : raw36861step0Labels = labelEmbedding10 ∘ raw36861step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36861step0 raw36861step0Labels raw36861step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5394 node5394Labels := by rfl

theorem canonical36862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36862 raw36862Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw36862 raw36862Labels = mixedMoment B raw36862step0 raw36862step0Labels := by
      have ha : raw36862step0 = (fun i j => raw36862 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36862step0 raw36862; decide +kernel
      have hl : raw36862step0Labels = raw36862Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36862 raw36862Labels permutation265 permutation7
    mixedMoment B raw36862step0 raw36862step0Labels = mixedMoment B raw36862step1 raw36862step1Labels := by
      have ha : raw36862step1 = -raw36862step0 := by apply Matrix.ext; change ∀ i j, raw36862step1 i j = -(raw36862step0 i j); unfold raw36862step1 raw36862step0; decide +kernel
      have hl : raw36862step1Labels = raw36862step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36862step1 raw36862step1Labels = mixedMoment B raw36862step2 raw36862step2Labels := by
      have ha : raw36862step2 = raw36862step1 := by apply Matrix.ext; unfold raw36862step2 raw36862step1; decide +kernel
      have hl : raw36862step1Labels = labelEmbedding10 ∘ raw36862step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36862step1 raw36862step1Labels raw36862step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5396 node5396Labels := by rfl

theorem canonical36863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36863 raw36863Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw36863 raw36863Labels = mixedMoment B raw36863step0 raw36863step0Labels := by
      have ha : raw36863step0 = (fun i j => raw36863 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36863step0 raw36863; decide +kernel
      have hl : raw36863step0Labels = raw36863Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36863 raw36863Labels permutation152 permutation3
    mixedMoment B raw36863step0 raw36863step0Labels = mixedMoment B raw36863step1 raw36863step1Labels := by
      have ha : raw36863step1 = raw36863step0 := by apply Matrix.ext; unfold raw36863step1 raw36863step0; decide +kernel
      have hl : raw36863step0Labels = labelEmbedding6 ∘ raw36863step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36863step0 raw36863step0Labels raw36863step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5192 node5192Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical288
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36864 raw36864Labels = mixedMoment B node5392 node5392Labels := by
  calc
    mixedMoment B raw36864 raw36864Labels = mixedMoment B raw36864step0 raw36864step0Labels := by
      have ha : raw36864step0 = (fun i j => raw36864 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36864step0 raw36864; decide +kernel
      have hl : raw36864step0Labels = raw36864Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36864 raw36864Labels permutation664 permutation2
    mixedMoment B raw36864step0 raw36864step0Labels = mixedMoment B raw36864step1 raw36864step1Labels := by
      have ha : raw36864step1 = -raw36864step0 := by apply Matrix.ext; change ∀ i j, raw36864step1 i j = -(raw36864step0 i j); unfold raw36864step1 raw36864step0; decide +kernel
      have hl : raw36864step1Labels = raw36864step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5392 node5392Labels := by rfl

theorem canonical36865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36865 raw36865Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw36865 raw36865Labels = mixedMoment B raw36865step0 raw36865step0Labels := by
      have ha : raw36865step0 = (fun i j => raw36865 (permutation687 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36865step0 raw36865; decide +kernel
      have hl : raw36865step0Labels = raw36865Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36865 raw36865Labels permutation687 permutation7
    mixedMoment B raw36865step0 raw36865step0Labels = mixedMoment B raw36865step1 raw36865step1Labels := by
      have ha : raw36865step1 = raw36865step0 := by apply Matrix.ext; unfold raw36865step1 raw36865step0; decide +kernel
      have hl : raw36865step0Labels = labelEmbedding10 ∘ raw36865step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36865step0 raw36865step0Labels raw36865step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical36866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36866 raw36866Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw36866 raw36866Labels = mixedMoment B raw36866step0 raw36866step0Labels := by
      have ha : raw36866step0 = (fun i j => raw36866 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36866step0 raw36866; decide +kernel
      have hl : raw36866step0Labels = raw36866Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36866 raw36866Labels permutation663 permutation7
    mixedMoment B raw36866step0 raw36866step0Labels = mixedMoment B raw36866step1 raw36866step1Labels := by
      have ha : raw36866step1 = raw36866step0 := by apply Matrix.ext; unfold raw36866step1 raw36866step0; decide +kernel
      have hl : raw36866step0Labels = labelEmbedding10 ∘ raw36866step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36866step0 raw36866step0Labels raw36866step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical36867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36867 raw36867Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw36867 raw36867Labels = mixedMoment B raw36867step0 raw36867step0Labels := by
      have ha : raw36867step0 = (fun i j => raw36867 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36867step0 raw36867; decide +kernel
      have hl : raw36867step0Labels = raw36867Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36867 raw36867Labels permutation265 permutation7
    mixedMoment B raw36867step0 raw36867step0Labels = mixedMoment B raw36867step1 raw36867step1Labels := by
      have ha : raw36867step1 = -raw36867step0 := by apply Matrix.ext; change ∀ i j, raw36867step1 i j = -(raw36867step0 i j); unfold raw36867step1 raw36867step0; decide +kernel
      have hl : raw36867step1Labels = raw36867step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36867step1 raw36867step1Labels = mixedMoment B raw36867step2 raw36867step2Labels := by
      have ha : raw36867step2 = raw36867step1 := by apply Matrix.ext; unfold raw36867step2 raw36867step1; decide +kernel
      have hl : raw36867step1Labels = labelEmbedding10 ∘ raw36867step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36867step1 raw36867step1Labels raw36867step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

theorem canonical36868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36868 raw36868Labels = mixedMoment B node4969 node4969Labels := by
  calc
    mixedMoment B raw36868 raw36868Labels = mixedMoment B raw36868step0 raw36868step0Labels := by
      have ha : raw36868step0 = (fun i j => raw36868 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36868step0 raw36868; decide +kernel
      have hl : raw36868step0Labels = raw36868Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36868 raw36868Labels permutation160 permutation3
    mixedMoment B raw36868step0 raw36868step0Labels = mixedMoment B raw36868step1 raw36868step1Labels := by
      have ha : raw36868step1 = raw36868step0 := by apply Matrix.ext; unfold raw36868step1 raw36868step0; decide +kernel
      have hl : raw36868step0Labels = labelEmbedding6 ∘ raw36868step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36868step0 raw36868step0Labels raw36868step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4969 node4969Labels := by rfl

theorem canonical36869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36869 raw36869Labels = mixedMoment B node4936 node4936Labels := by
  calc
    mixedMoment B raw36869 raw36869Labels = mixedMoment B raw36869step0 raw36869step0Labels := by
      have ha : raw36869step0 = (fun i j => raw36869 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36869step0 raw36869; decide +kernel
      have hl : raw36869step0Labels = raw36869Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36869 raw36869Labels permutation265 permutation2
    _ = mixedMoment B node4936 node4936Labels := by rfl

theorem canonical36870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36870 raw36870Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw36870 raw36870Labels = mixedMoment B raw36870step0 raw36870step0Labels := by
      have ha : raw36870step0 = (fun i j => raw36870 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36870step0 raw36870; decide +kernel
      have hl : raw36870step0Labels = raw36870Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36870 raw36870Labels permutation271 permutation2
    _ = mixedMoment B node5349 node5349Labels := by rfl

theorem canonical36871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36871 raw36871Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw36871 raw36871Labels = mixedMoment B raw36871step0 raw36871step0Labels := by
      have ha : raw36871step0 = (fun i j => raw36871 (permutation277 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36871step0 raw36871; decide +kernel
      have hl : raw36871step0Labels = raw36871Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36871 raw36871Labels permutation277 permutation2
    _ = mixedMoment B node5349 node5349Labels := by rfl

theorem canonical36872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36872 raw36872Labels = mixedMoment B node5363 node5363Labels := by
  calc
    mixedMoment B raw36872 raw36872Labels = mixedMoment B raw36872step0 raw36872step0Labels := by
      have ha : raw36872step0 = (fun i j => raw36872 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36872step0 raw36872; decide +kernel
      have hl : raw36872step0Labels = raw36872Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36872 raw36872Labels permutation265 permutation2
    _ = mixedMoment B node5363 node5363Labels := by rfl

theorem canonical36873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36873 raw36873Labels = mixedMoment B node4961 node4961Labels := by
  calc
    mixedMoment B raw36873 raw36873Labels = mixedMoment B raw36873step0 raw36873step0Labels := by
      have ha : raw36873step0 = (fun i j => raw36873 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36873step0 raw36873; decide +kernel
      have hl : raw36873step0Labels = raw36873Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36873 raw36873Labels permutation155 permutation3
    mixedMoment B raw36873step0 raw36873step0Labels = mixedMoment B raw36873step1 raw36873step1Labels := by
      have ha : raw36873step1 = raw36873step0 := by apply Matrix.ext; unfold raw36873step1 raw36873step0; decide +kernel
      have hl : raw36873step0Labels = labelEmbedding6 ∘ raw36873step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36873step0 raw36873step0Labels raw36873step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4961 node4961Labels := by rfl

theorem canonical36874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36874 raw36874Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw36874 raw36874Labels = mixedMoment B raw36874step0 raw36874step0Labels := by
      have ha : raw36874step0 = (fun i j => raw36874 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36874step0 raw36874; decide +kernel
      have hl : raw36874step0Labels = raw36874Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36874 raw36874Labels permutation267 permutation2
    _ = mixedMoment B node4928 node4928Labels := by rfl

theorem canonical36875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36875 raw36875Labels = mixedMoment B node5332 node5332Labels := by
  calc
    mixedMoment B raw36875 raw36875Labels = mixedMoment B raw36875step0 raw36875step0Labels := by
      have ha : raw36875step0 = (fun i j => raw36875 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36875step0 raw36875; decide +kernel
      have hl : raw36875step0Labels = raw36875Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36875 raw36875Labels permutation267 permutation2
    _ = mixedMoment B node5332 node5332Labels := by rfl

theorem canonical36876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36876 raw36876Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw36876 raw36876Labels = mixedMoment B raw36876step0 raw36876step0Labels := by
      have ha : raw36876step0 = (fun i j => raw36876 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36876step0 raw36876; decide +kernel
      have hl : raw36876step0Labels = raw36876Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36876 raw36876Labels permutation267 permutation2
    _ = mixedMoment B node5341 node5341Labels := by rfl

theorem canonical36877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36877 raw36877Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw36877 raw36877Labels = mixedMoment B raw36877step0 raw36877step0Labels := by
      have ha : raw36877step0 = (fun i j => raw36877 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36877step0 raw36877; decide +kernel
      have hl : raw36877step0Labels = raw36877Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36877 raw36877Labels permutation268 permutation2
    _ = mixedMoment B node5346 node5346Labels := by rfl

theorem canonical36878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36878 raw36878Labels = mixedMoment B node4961 node4961Labels := by
  calc
    mixedMoment B raw36878 raw36878Labels = mixedMoment B raw36878step0 raw36878step0Labels := by
      have ha : raw36878step0 = (fun i j => raw36878 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36878step0 raw36878; decide +kernel
      have hl : raw36878step0Labels = raw36878Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36878 raw36878Labels permutation153 permutation3
    mixedMoment B raw36878step0 raw36878step0Labels = mixedMoment B raw36878step1 raw36878step1Labels := by
      have ha : raw36878step1 = raw36878step0 := by apply Matrix.ext; unfold raw36878step1 raw36878step0; decide +kernel
      have hl : raw36878step0Labels = labelEmbedding6 ∘ raw36878step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36878step0 raw36878step0Labels raw36878step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4961 node4961Labels := by rfl

theorem canonical36879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36879 raw36879Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw36879 raw36879Labels = mixedMoment B raw36879step0 raw36879step0Labels := by
      have ha : raw36879step0 = (fun i j => raw36879 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36879step0 raw36879; decide +kernel
      have hl : raw36879step0Labels = raw36879Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36879 raw36879Labels permutation265 permutation2
    _ = mixedMoment B node4928 node4928Labels := by rfl

theorem canonical36880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36880 raw36880Labels = mixedMoment B node5332 node5332Labels := by
  calc
    mixedMoment B raw36880 raw36880Labels = mixedMoment B raw36880step0 raw36880step0Labels := by
      have ha : raw36880step0 = (fun i j => raw36880 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36880step0 raw36880; decide +kernel
      have hl : raw36880step0Labels = raw36880Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36880 raw36880Labels permutation265 permutation2
    _ = mixedMoment B node5332 node5332Labels := by rfl

theorem canonical36881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36881 raw36881Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw36881 raw36881Labels = mixedMoment B raw36881step0 raw36881step0Labels := by
      have ha : raw36881step0 = (fun i j => raw36881 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36881step0 raw36881; decide +kernel
      have hl : raw36881step0Labels = raw36881Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36881 raw36881Labels permutation265 permutation2
    _ = mixedMoment B node5341 node5341Labels := by rfl

theorem canonical36882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36882 raw36882Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw36882 raw36882Labels = mixedMoment B raw36882step0 raw36882step0Labels := by
      have ha : raw36882step0 = (fun i j => raw36882 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36882step0 raw36882; decide +kernel
      have hl : raw36882step0Labels = raw36882Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36882 raw36882Labels permutation266 permutation2
    _ = mixedMoment B node5346 node5346Labels := by rfl

theorem canonical36883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36883 raw36883Labels = mixedMoment B node4960 node4960Labels := by
  calc
    mixedMoment B raw36883 raw36883Labels = mixedMoment B raw36883step0 raw36883step0Labels := by
      have ha : raw36883step0 = (fun i j => raw36883 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36883step0 raw36883; decide +kernel
      have hl : raw36883step0Labels = raw36883Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36883 raw36883Labels permutation152 permutation3
    mixedMoment B raw36883step0 raw36883step0Labels = mixedMoment B raw36883step1 raw36883step1Labels := by
      have ha : raw36883step1 = raw36883step0 := by apply Matrix.ext; unfold raw36883step1 raw36883step0; decide +kernel
      have hl : raw36883step0Labels = labelEmbedding6 ∘ raw36883step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36883step0 raw36883step0Labels raw36883step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4960 node4960Labels := by rfl

theorem canonical36884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36884 raw36884Labels = mixedMoment B node4927 node4927Labels := by
  calc
    mixedMoment B raw36884 raw36884Labels = mixedMoment B raw36884step0 raw36884step0Labels := by
      have ha : raw36884step0 = (fun i j => raw36884 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36884step0 raw36884; decide +kernel
      have hl : raw36884step0Labels = raw36884Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36884 raw36884Labels permutation265 permutation2
    _ = mixedMoment B node4927 node4927Labels := by rfl

theorem canonical36885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36885 raw36885Labels = mixedMoment B node5029 node5029Labels := by
  calc
    mixedMoment B raw36885 raw36885Labels = mixedMoment B raw36885step0 raw36885step0Labels := by
      have ha : raw36885step0 = (fun i j => raw36885 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36885step0 raw36885; decide +kernel
      have hl : raw36885step0Labels = raw36885Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36885 raw36885Labels permutation663 permutation2
    mixedMoment B raw36885step0 raw36885step0Labels = mixedMoment B raw36885step1 raw36885step1Labels := by
      have ha : raw36885step1 = -raw36885step0 := by apply Matrix.ext; change ∀ i j, raw36885step1 i j = -(raw36885step0 i j); unfold raw36885step1 raw36885step0; decide +kernel
      have hl : raw36885step1Labels = raw36885step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5029 node5029Labels := by rfl

theorem canonical36886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36886 raw36886Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw36886 raw36886Labels = mixedMoment B raw36886step0 raw36886step0Labels := by
      have ha : raw36886step0 = (fun i j => raw36886 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36886step0 raw36886; decide +kernel
      have hl : raw36886step0Labels = raw36886Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36886 raw36886Labels permutation687 permutation2
    mixedMoment B raw36886step0 raw36886step0Labels = mixedMoment B raw36886step1 raw36886step1Labels := by
      have ha : raw36886step1 = -raw36886step0 := by apply Matrix.ext; change ∀ i j, raw36886step1 i j = -(raw36886step0 i j); unfold raw36886step1 raw36886step0; decide +kernel
      have hl : raw36886step1Labels = raw36886step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5050 node5050Labels := by rfl

theorem canonical36887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36887 raw36887Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw36887 raw36887Labels = mixedMoment B raw36887step0 raw36887step0Labels := by
      have ha : raw36887step0 = (fun i j => raw36887 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36887step0 raw36887; decide +kernel
      have hl : raw36887step0Labels = raw36887Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36887 raw36887Labels permutation663 permutation2
    mixedMoment B raw36887step0 raw36887step0Labels = mixedMoment B raw36887step1 raw36887step1Labels := by
      have ha : raw36887step1 = -raw36887step0 := by apply Matrix.ext; change ∀ i j, raw36887step1 i j = -(raw36887step0 i j); unfold raw36887step1 raw36887step0; decide +kernel
      have hl : raw36887step1Labels = raw36887step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5050 node5050Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4927 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4927 node4927Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2317 node2317Labels + mixedMoment B node3399 node3399Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1890 singletonSmall4927
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4927) = raw1890Labels := by decide +kernel
  rw [hl, canonical1890 B hB] at h
  have hc0 : mixedMoment B raw1890 (Fin.cases (0 : Fin 2) singletonSmall4927) =
      mixedMoment B node2317 node2317Labels := by
    have ha : raw1890 = raw1891 := by apply Matrix.ext; unfold raw1890 raw1891; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4927 = raw1891Labels := by decide +kernel
    rw [ha, hj, canonical1891 B hB]
  have hc1 : mixedMoment B raw1890 (Fin.cases (1 : Fin 2) singletonSmall4927) =
      mixedMoment B node3399 node3399Labels := by
    have ha : raw1890 = raw1892 := by apply Matrix.ext; unfold raw1890 raw1892; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4927 = raw1892Labels := by decide +kernel
    rw [ha, hj, canonical1892 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4928 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4928 node4928Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2318 node2318Labels + mixedMoment B node3400 node3400Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1893 singletonSmall4928
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4928) = raw1893Labels := by decide +kernel
  rw [hl, canonical1893 B hB] at h
  have hc0 : mixedMoment B raw1893 (Fin.cases (0 : Fin 2) singletonSmall4928) =
      mixedMoment B node2318 node2318Labels := by
    have ha : raw1893 = raw1894 := by apply Matrix.ext; unfold raw1893 raw1894; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4928 = raw1894Labels := by decide +kernel
    rw [ha, hj, canonical1894 B hB]
  have hc1 : mixedMoment B raw1893 (Fin.cases (1 : Fin 2) singletonSmall4928) =
      mixedMoment B node3400 node3400Labels := by
    have ha : raw1893 = raw1895 := by apply Matrix.ext; unfold raw1893 raw1895; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4928 = raw1895Labels := by decide +kernel
    rw [ha, hj, canonical1895 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4936 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4936 node4936Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2328 node2328Labels + mixedMoment B node3401 node3401Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1896 singletonSmall4936
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4936) = raw1896Labels := by decide +kernel
  rw [hl, canonical1896 B hB] at h
  have hc0 : mixedMoment B raw1896 (Fin.cases (0 : Fin 2) singletonSmall4936) =
      mixedMoment B node2328 node2328Labels := by
    have ha : raw1896 = raw1897 := by apply Matrix.ext; unfold raw1896 raw1897; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4936 = raw1897Labels := by decide +kernel
    rw [ha, hj, canonical1897 B hB]
  have hc1 : mixedMoment B raw1896 (Fin.cases (1 : Fin 2) singletonSmall4936) =
      mixedMoment B node3401 node3401Labels := by
    have ha : raw1896 = raw1898 := by apply Matrix.ext; unfold raw1896 raw1898; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4936 = raw1898Labels := by decide +kernel
    rw [ha, hj, canonical1898 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4960 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4960 node4960Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2412 node2412Labels + mixedMoment B node3426 node3426Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1932 singletonSmall4960
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4960) = raw1932Labels := by decide +kernel
  rw [hl, canonical1932 B hB] at h
  have hc0 : mixedMoment B raw1932 (Fin.cases (0 : Fin 2) singletonSmall4960) =
      mixedMoment B node2412 node2412Labels := by
    have ha : raw1932 = raw1933 := by apply Matrix.ext; unfold raw1932 raw1933; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4960 = raw1933Labels := by decide +kernel
    rw [ha, hj, canonical1933 B hB]
  have hc1 : mixedMoment B raw1932 (Fin.cases (1 : Fin 2) singletonSmall4960) =
      mixedMoment B node3426 node3426Labels := by
    have ha : raw1932 = raw1934 := by apply Matrix.ext; unfold raw1932 raw1934; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4960 = raw1934Labels := by decide +kernel
    rw [ha, hj, canonical1934 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4961 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4961 node4961Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2796 node2796Labels + mixedMoment B node3589 node3589Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1935 singletonSmall4961
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4961) = raw1935Labels := by decide +kernel
  rw [hl, canonical1935 B hB] at h
  have hc0 : mixedMoment B raw1935 (Fin.cases (0 : Fin 2) singletonSmall4961) =
      mixedMoment B node2796 node2796Labels := by
    have ha : raw1935 = raw1936 := by apply Matrix.ext; unfold raw1935 raw1936; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4961 = raw1936Labels := by decide +kernel
    rw [ha, hj, canonical1936 B hB]
  have hc1 : mixedMoment B raw1935 (Fin.cases (1 : Fin 2) singletonSmall4961) =
      mixedMoment B node3589 node3589Labels := by
    have ha : raw1935 = raw1937 := by apply Matrix.ext; unfold raw1935 raw1937; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4961 = raw1937Labels := by decide +kernel
    rw [ha, hj, canonical1937 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4969 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4969 node4969Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2804 node2804Labels + mixedMoment B node3586 node3586Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1947 singletonSmall4969
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4969) = raw1947Labels := by decide +kernel
  rw [hl, canonical1947 B hB] at h
  have hc0 : mixedMoment B raw1947 (Fin.cases (0 : Fin 2) singletonSmall4969) =
      mixedMoment B node2804 node2804Labels := by
    have ha : raw1947 = raw1948 := by apply Matrix.ext; unfold raw1947 raw1948; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4969 = raw1948Labels := by decide +kernel
    rw [ha, hj, canonical1948 B hB]
  have hc1 : mixedMoment B raw1947 (Fin.cases (1 : Fin 2) singletonSmall4969) =
      mixedMoment B node3586 node3586Labels := by
    have ha : raw1947 = raw1949 := by apply Matrix.ext; unfold raw1947 raw1949; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4969 = raw1949Labels := by decide +kernel
    rw [ha, hj, canonical1949 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5050 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5050 node5050Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2452 node2452Labels + mixedMoment B node3433 node3433Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2076 singletonSmall5050
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5050) = raw2076Labels := by decide +kernel
  rw [hl, canonical2076 B hB] at h
  have hc0 : mixedMoment B raw2076 (Fin.cases (0 : Fin 2) singletonSmall5050) =
      mixedMoment B node2452 node2452Labels := by
    have ha : raw2076 = raw2077 := by apply Matrix.ext; unfold raw2076 raw2077; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5050 = raw2077Labels := by decide +kernel
    rw [ha, hj, canonical2077 B hB]
  have hc1 : mixedMoment B raw2076 (Fin.cases (1 : Fin 2) singletonSmall5050) =
      mixedMoment B node3433 node3433Labels := by
    have ha : raw2076 = raw2078 := by apply Matrix.ext; unfold raw2076 raw2078; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5050 = raw2078Labels := by decide +kernel
    rw [ha, hj, canonical2078 B hB]
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

theorem singleton5192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5192 node5192Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2853 node2853Labels + mixedMoment B node3620 node3620Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2220 singletonSmall5192
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5192) = raw2220Labels := by decide +kernel
  rw [hl, canonical2220 B hB] at h
  have hc0 : mixedMoment B raw2220 (Fin.cases (0 : Fin 2) singletonSmall5192) =
      mixedMoment B node2853 node2853Labels := by
    have ha : raw2220 = raw2221 := by apply Matrix.ext; unfold raw2220 raw2221; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5192 = raw2221Labels := by decide +kernel
    rw [ha, hj, canonical2221 B hB]
  have hc1 : mixedMoment B raw2220 (Fin.cases (1 : Fin 2) singletonSmall5192) =
      mixedMoment B node3620 node3620Labels := by
    have ha : raw2220 = raw2222 := by apply Matrix.ext; unfold raw2220 raw2222; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5192 = raw2222Labels := by decide +kernel
    rw [ha, hj, canonical2222 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5341 node5341Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3678 node3678Labels + mixedMoment B node3744 node3744Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2379 singletonSmall5341
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5341) = raw2379Labels := by decide +kernel
  rw [hl, canonical2379 B hB] at h
  have hc0 : mixedMoment B raw2379 (Fin.cases (0 : Fin 2) singletonSmall5341) =
      mixedMoment B node3678 node3678Labels := by
    have ha : raw2379 = raw2380 := by apply Matrix.ext; unfold raw2379 raw2380; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5341 = raw2380Labels := by decide +kernel
    rw [ha, hj, canonical2380 B hB]
  have hc1 : mixedMoment B raw2379 (Fin.cases (1 : Fin 2) singletonSmall5341) =
      mixedMoment B node3744 node3744Labels := by
    have ha : raw2379 = raw2381 := by apply Matrix.ext; unfold raw2379 raw2381; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5341 = raw2381Labels := by decide +kernel
    rw [ha, hj, canonical2381 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5346 node5346Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3683 node3683Labels + mixedMoment B node3746 node3746Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2385 singletonSmall5346
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5346) = raw2385Labels := by decide +kernel
  rw [hl, canonical2385 B hB] at h
  have hc0 : mixedMoment B raw2385 (Fin.cases (0 : Fin 2) singletonSmall5346) =
      mixedMoment B node3683 node3683Labels := by
    have ha : raw2385 = raw2386 := by apply Matrix.ext; unfold raw2385 raw2386; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5346 = raw2386Labels := by decide +kernel
    rw [ha, hj, canonical2386 B hB]
  have hc1 : mixedMoment B raw2385 (Fin.cases (1 : Fin 2) singletonSmall5346) =
      mixedMoment B node3746 node3746Labels := by
    have ha : raw2385 = raw2387 := by apply Matrix.ext; unfold raw2385 raw2387; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5346 = raw2387Labels := by decide +kernel
    rw [ha, hj, canonical2387 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5349 node5349Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3687 node3687Labels + mixedMoment B node3749 node3749Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2388 singletonSmall5349
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5349) = raw2388Labels := by decide +kernel
  rw [hl, canonical2388 B hB] at h
  have hc0 : mixedMoment B raw2388 (Fin.cases (0 : Fin 2) singletonSmall5349) =
      mixedMoment B node3687 node3687Labels := by
    have ha : raw2388 = raw2389 := by apply Matrix.ext; unfold raw2388 raw2389; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5349 = raw2389Labels := by decide +kernel
    rw [ha, hj, canonical2389 B hB]
  have hc1 : mixedMoment B raw2388 (Fin.cases (1 : Fin 2) singletonSmall5349) =
      mixedMoment B node3749 node3749Labels := by
    have ha : raw2388 = raw2390 := by apply Matrix.ext; unfold raw2388 raw2390; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5349 = raw2390Labels := by decide +kernel
    rw [ha, hj, canonical2390 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5363 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5363 node5363Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3701 node3701Labels + mixedMoment B node3751 node3751Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2406 singletonSmall5363
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5363) = raw2406Labels := by decide +kernel
  rw [hl, canonical2406 B hB] at h
  have hc0 : mixedMoment B raw2406 (Fin.cases (0 : Fin 2) singletonSmall5363) =
      mixedMoment B node3701 node3701Labels := by
    have ha : raw2406 = raw2407 := by apply Matrix.ext; unfold raw2406 raw2407; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5363 = raw2407Labels := by decide +kernel
    rw [ha, hj, canonical2407 B hB]
  have hc1 : mixedMoment B raw2406 (Fin.cases (1 : Fin 2) singletonSmall5363) =
      mixedMoment B node3751 node3751Labels := by
    have ha : raw2406 = raw2408 := by apply Matrix.ext; unfold raw2406 raw2408; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5363 = raw2408Labels := by decide +kernel
    rw [ha, hj, canonical2408 B hB]
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

theorem singleton5395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5395 node5395Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3781 node3781Labels + mixedMoment B node3794 node3794Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2463 singletonSmall5395
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5395) = raw2463Labels := by decide +kernel
  rw [hl, canonical2463 B hB] at h
  have hc0 : mixedMoment B raw2463 (Fin.cases (0 : Fin 2) singletonSmall5395) =
      mixedMoment B node3781 node3781Labels := by
    have ha : raw2463 = raw2464 := by apply Matrix.ext; unfold raw2463 raw2464; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5395 = raw2464Labels := by decide +kernel
    rw [ha, hj, canonical2464 B hB]
  have hc1 : mixedMoment B raw2463 (Fin.cases (1 : Fin 2) singletonSmall5395) =
      mixedMoment B node3794 node3794Labels := by
    have ha : raw2463 = raw2465 := by apply Matrix.ext; unfold raw2463 raw2465; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5395 = raw2465Labels := by decide +kernel
    rw [ha, hj, canonical2465 B hB]
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

theorem singleton5469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5469 node5469Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3945 node3945Labels + mixedMoment B node3952 node3952Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2583 singletonSmall5469
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5469) = raw2583Labels := by decide +kernel
  rw [hl, canonical2583 B hB] at h
  have hc0 : mixedMoment B raw2583 (Fin.cases (0 : Fin 2) singletonSmall5469) =
      mixedMoment B node3945 node3945Labels := by
    have ha : raw2583 = raw2584 := by apply Matrix.ext; unfold raw2583 raw2584; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5469 = raw2584Labels := by decide +kernel
    rw [ha, hj, canonical2584 B hB]
  have hc1 : mixedMoment B raw2583 (Fin.cases (1 : Fin 2) singletonSmall5469) =
      mixedMoment B node3952 node3952Labels := by
    have ha : raw2583 = raw2585 := by apply Matrix.ext; unfold raw2583 raw2585; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5469 = raw2585Labels := by decide +kernel
    rw [ha, hj, canonical2585 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2317 node2317Labels = Sparse.eval nodeValue2317 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2317) = mixedMoment B node2317 node2317Labels := rfl
  simpa [nodeValue2317, Sparse.eval] using hc.symm

theorem sound2318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2318 node2318Labels = Sparse.eval nodeValue2318 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2318) = mixedMoment B node2318 node2318Labels := rfl
  simpa [nodeValue2318, Sparse.eval] using hc.symm

theorem sound2328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2328 node2328Labels = Sparse.eval nodeValue2328 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2328) = mixedMoment B node2328 node2328Labels := rfl
  simpa [nodeValue2328, Sparse.eval] using hc.symm

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

theorem sound2412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2412 node2412Labels = Sparse.eval nodeValue2412 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2412) = mixedMoment B node2412 node2412Labels := rfl
  simpa [nodeValue2412, Sparse.eval] using hc.symm

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

theorem sound2452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2452 node2452Labels = Sparse.eval nodeValue2452 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2452) = mixedMoment B node2452 node2452Labels := rfl
  simpa [nodeValue2452, Sparse.eval] using hc.symm

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

theorem sound2796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2796 node2796Labels = Sparse.eval nodeValue2796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2796) = mixedMoment B node2796 node2796Labels := rfl
  simpa [nodeValue2796, Sparse.eval] using hc.symm

theorem sound2804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2804 node2804Labels = Sparse.eval nodeValue2804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2804) = mixedMoment B node2804 node2804Labels := rfl
  simpa [nodeValue2804, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2853 node2853Labels = Sparse.eval nodeValue2853 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2853) = mixedMoment B node2853 node2853Labels := rfl
  simpa [nodeValue2853, Sparse.eval] using hc.symm

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

theorem sound3399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3399 node3399Labels = Sparse.eval nodeValue3399 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3399) = mixedMoment B node3399 node3399Labels := rfl
  simpa [nodeValue3399, Sparse.eval] using hc.symm

theorem sound3400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3400 node3400Labels = Sparse.eval nodeValue3400 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3400) = mixedMoment B node3400 node3400Labels := rfl
  simpa [nodeValue3400, Sparse.eval] using hc.symm

theorem sound3401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3401 node3401Labels = Sparse.eval nodeValue3401 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3401) = mixedMoment B node3401 node3401Labels := rfl
  simpa [nodeValue3401, Sparse.eval] using hc.symm

theorem sound3426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3426 node3426Labels = Sparse.eval nodeValue3426 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3426) = mixedMoment B node3426 node3426Labels := rfl
  simpa [nodeValue3426, Sparse.eval] using hc.symm

theorem sound3433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3433 node3433Labels = Sparse.eval nodeValue3433 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3433) = mixedMoment B node3433 node3433Labels := rfl
  simpa [nodeValue3433, Sparse.eval] using hc.symm

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

theorem sound3586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3586 node3586Labels = Sparse.eval nodeValue3586 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3586) = mixedMoment B node3586 node3586Labels := rfl
  simpa [nodeValue3586, Sparse.eval] using hc.symm

theorem sound3589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3589 node3589Labels = Sparse.eval nodeValue3589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3589) = mixedMoment B node3589 node3589Labels := rfl
  simpa [nodeValue3589, Sparse.eval] using hc.symm

theorem sound3620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3620 node3620Labels = Sparse.eval nodeValue3620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3620) = mixedMoment B node3620 node3620Labels := rfl
  simpa [nodeValue3620, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3678 node3678Labels = Sparse.eval nodeValue3678 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3678) = mixedMoment B node3678 node3678Labels := rfl
  simpa [nodeValue3678, Sparse.eval] using hc.symm

theorem sound3683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3683 node3683Labels = Sparse.eval nodeValue3683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3683) = mixedMoment B node3683 node3683Labels := rfl
  simpa [nodeValue3683, Sparse.eval] using hc.symm

theorem sound3687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3687 node3687Labels = Sparse.eval nodeValue3687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3687) = mixedMoment B node3687 node3687Labels := rfl
  simpa [nodeValue3687, Sparse.eval] using hc.symm

theorem sound3701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3701 node3701Labels = Sparse.eval nodeValue3701 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3701) = mixedMoment B node3701 node3701Labels := rfl
  simpa [nodeValue3701, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3744 node3744Labels = Sparse.eval nodeValue3744 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3744) = mixedMoment B node3744 node3744Labels := rfl
  simpa [nodeValue3744, Sparse.eval] using hc.symm

theorem sound3746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3746 node3746Labels = Sparse.eval nodeValue3746 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3746) = mixedMoment B node3746 node3746Labels := rfl
  simpa [nodeValue3746, Sparse.eval] using hc.symm

theorem sound3749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3749 node3749Labels = Sparse.eval nodeValue3749 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3749) = mixedMoment B node3749 node3749Labels := rfl
  simpa [nodeValue3749, Sparse.eval] using hc.symm

theorem sound3751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3751 node3751Labels = Sparse.eval nodeValue3751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3751) = mixedMoment B node3751 node3751Labels := rfl
  simpa [nodeValue3751, Sparse.eval] using hc.symm

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

theorem sound3781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3781 node3781Labels = Sparse.eval nodeValue3781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3781) = mixedMoment B node3781 node3781Labels := rfl
  simpa [nodeValue3781, Sparse.eval] using hc.symm

theorem sound3794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3794 node3794Labels = Sparse.eval nodeValue3794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3794) = mixedMoment B node3794 node3794Labels := rfl
  simpa [nodeValue3794, Sparse.eval] using hc.symm

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

theorem sound3945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3945 node3945Labels = Sparse.eval nodeValue3945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3945) = mixedMoment B node3945 node3945Labels := rfl
  simpa [nodeValue3945, Sparse.eval] using hc.symm

theorem sound3952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3952 node3952Labels = Sparse.eval nodeValue3952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3952) = mixedMoment B node3952 node3952Labels := rfl
  simpa [nodeValue3952, Sparse.eval] using hc.symm

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

theorem sound4090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4090 node4090Labels = Sparse.eval nodeValue4090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4090) = mixedMoment B node4090 node4090Labels := rfl
  simpa [nodeValue4090, Sparse.eval] using hc.symm

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

theorem sound4927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4927 node4927Labels = Sparse.eval nodeValue4927 (mixedVector B) := by
  have h := singleton4927 B _hB
  rw [sound2317 B _hB _hF, sound3399 B _hB _hF] at h
  norm_num [nodeValue4927, nodeValue2317, nodeValue3399, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4928 node4928Labels = Sparse.eval nodeValue4928 (mixedVector B) := by
  have h := singleton4928 B _hB
  rw [sound2318 B _hB _hF, sound3400 B _hB _hF] at h
  norm_num [nodeValue4928, nodeValue2318, nodeValue3400, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4936 node4936Labels = Sparse.eval nodeValue4936 (mixedVector B) := by
  have h := singleton4936 B _hB
  rw [sound2328 B _hB _hF, sound3401 B _hB _hF] at h
  norm_num [nodeValue4936, nodeValue2328, nodeValue3401, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4960 node4960Labels = Sparse.eval nodeValue4960 (mixedVector B) := by
  have h := singleton4960 B _hB
  rw [sound2412 B _hB _hF, sound3426 B _hB _hF] at h
  norm_num [nodeValue4960, nodeValue2412, nodeValue3426, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4961 node4961Labels = Sparse.eval nodeValue4961 (mixedVector B) := by
  have h := singleton4961 B _hB
  rw [sound2796 B _hB _hF, sound3589 B _hB _hF] at h
  norm_num [nodeValue4961, nodeValue2796, nodeValue3589, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4969 node4969Labels = Sparse.eval nodeValue4969 (mixedVector B) := by
  have h := singleton4969 B _hB
  rw [sound2804 B _hB _hF, sound3586 B _hB _hF] at h
  norm_num [nodeValue4969, nodeValue2804, nodeValue3586, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5029 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5029 node5029Labels = 0 := by
  exact mixedMoment_order_one B hB node5029 node5029Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5029 node5029Labels = Sparse.eval nodeValue5029 (mixedVector B) := by
  simpa only [nodeValue5029, Sparse.eval_nil] using zero5029 B _hB _hF

theorem sound5050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5050 node5050Labels = Sparse.eval nodeValue5050 (mixedVector B) := by
  have h := singleton5050 B _hB
  rw [sound2452 B _hB _hF, sound3433 B _hB _hF] at h
  norm_num [nodeValue5050, nodeValue2452, nodeValue3433, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5058 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5058 node5058Labels = 0 := by
  exact mixedMoment_order_one B hB node5058 node5058Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5058 node5058Labels = Sparse.eval nodeValue5058 (mixedVector B) := by
  simpa only [nodeValue5058, Sparse.eval_nil] using zero5058 B _hB _hF

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

theorem sound5192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5192 node5192Labels = Sparse.eval nodeValue5192 (mixedVector B) := by
  have h := singleton5192 B _hB
  rw [sound2853 B _hB _hF, sound3620 B _hB _hF] at h
  norm_num [nodeValue5192, nodeValue2853, nodeValue3620, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5332 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5332 node5332Labels = 0 := by
  exact mixedMoment_order_one B hB node5332 node5332Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5332 node5332Labels = Sparse.eval nodeValue5332 (mixedVector B) := by
  simpa only [nodeValue5332, Sparse.eval_nil] using zero5332 B _hB _hF

theorem sound5341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5341 node5341Labels = Sparse.eval nodeValue5341 (mixedVector B) := by
  have h := singleton5341 B _hB
  rw [sound3678 B _hB _hF, sound3744 B _hB _hF] at h
  norm_num [nodeValue5341, nodeValue3678, nodeValue3744, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5346 node5346Labels = Sparse.eval nodeValue5346 (mixedVector B) := by
  have h := singleton5346 B _hB
  rw [sound3683 B _hB _hF, sound3746 B _hB _hF] at h
  norm_num [nodeValue5346, nodeValue3683, nodeValue3746, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5349 node5349Labels = Sparse.eval nodeValue5349 (mixedVector B) := by
  have h := singleton5349 B _hB
  rw [sound3687 B _hB _hF, sound3749 B _hB _hF] at h
  norm_num [nodeValue5349, nodeValue3687, nodeValue3749, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5363 node5363Labels = Sparse.eval nodeValue5363 (mixedVector B) := by
  have h := singleton5363 B _hB
  rw [sound3701 B _hB _hF, sound3751 B _hB _hF] at h
  norm_num [nodeValue5363, nodeValue3701, nodeValue3751, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5392 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5392 node5392Labels = 0 := by
  exact mixedMoment_order_one B hB node5392 node5392Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5394 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5394 node5394Labels = 0 := by
  exact mixedMoment_order_one B hB node5394 node5394Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5396 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5396 node5396Labels = 0 := by
  exact mixedMoment_order_one B hB node5396 node5396Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5392 node5392Labels = Sparse.eval nodeValue5392 (mixedVector B) := by
  simpa only [nodeValue5392, Sparse.eval_nil] using zero5392 B _hB _hF

theorem sound5394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5394 node5394Labels = Sparse.eval nodeValue5394 (mixedVector B) := by
  simpa only [nodeValue5394, Sparse.eval_nil] using zero5394 B _hB _hF

theorem sound5395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5395 node5395Labels = Sparse.eval nodeValue5395 (mixedVector B) := by
  have h := singleton5395 B _hB
  rw [sound3781 B _hB _hF, sound3794 B _hB _hF] at h
  norm_num [nodeValue5395, nodeValue3781, nodeValue3794, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5396 node5396Labels = Sparse.eval nodeValue5396 (mixedVector B) := by
  simpa only [nodeValue5396, Sparse.eval_nil] using zero5396 B _hB _hF

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

theorem sound5469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5469 node5469Labels = Sparse.eval nodeValue5469 (mixedVector B) := by
  have h := singleton5469 B _hB
  rw [sound3945 B _hB _hF, sound3952 B _hB _hF] at h
  norm_num [nodeValue5469, nodeValue3945, nodeValue3952, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources82
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2632 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2632 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2632 + difference 0 1) (sourceB2632 + difference 1 0) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5058) := by
    have ha : (tripleCharges (sourceA2632 + difference 0 1) (sourceB2632 + difference 1 0) sourceC2632) = raw36858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36858; decide +kernel
    rw [ha]
    exact (canonical36858 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2632 + difference 0 2) (sourceB2632 + difference 2 0) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA2632 + difference 0 2) (sourceB2632 + difference 2 0) sourceC2632) = raw36859 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36859; decide +kernel
    rw [ha]
    exact (canonical36859 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2632 + difference 0 3) (sourceB2632 + difference 3 0) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5394) := by
    have ha : (tripleCharges (sourceA2632 + difference 0 3) (sourceB2632 + difference 3 0) sourceC2632) = raw36860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36860; decide +kernel
    rw [ha]
    exact (canonical36860 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2632 + difference 0 4) (sourceB2632 + difference 4 0) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5394) := by
    have ha : (tripleCharges (sourceA2632 + difference 0 4) (sourceB2632 + difference 4 0) sourceC2632) = raw36861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36861; decide +kernel
    rw [ha]
    exact (canonical36861 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2632 + difference 0 5) (sourceB2632 + difference 5 0) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA2632 + difference 0 5) (sourceB2632 + difference 5 0) sourceC2632) = raw36862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36862; decide +kernel
    rw [ha]
    exact (canonical36862 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2632 + difference 1 0) (sourceB2632 + difference 0 1) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA2632 + difference 1 0) (sourceB2632 + difference 0 1) sourceC2632) = raw36863 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36863; decide +kernel
    rw [ha]
    exact (canonical36863 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2632 + difference 1 2) (sourceB2632 + difference 2 1) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5392) := by
    have ha : (tripleCharges (sourceA2632 + difference 1 2) (sourceB2632 + difference 2 1) sourceC2632) = raw36864 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36864; decide +kernel
    rw [ha]
    exact (canonical36864 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2632 + difference 1 3) (sourceB2632 + difference 3 1) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA2632 + difference 1 3) (sourceB2632 + difference 3 1) sourceC2632) = raw36865 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36865; decide +kernel
    rw [ha]
    exact (canonical36865 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2632 + difference 1 4) (sourceB2632 + difference 4 1) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA2632 + difference 1 4) (sourceB2632 + difference 4 1) sourceC2632) = raw36866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36866; decide +kernel
    rw [ha]
    exact (canonical36866 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2632 + difference 1 5) (sourceB2632 + difference 5 1) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA2632 + difference 1 5) (sourceB2632 + difference 5 1) sourceC2632) = raw36867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36867; decide +kernel
    rw [ha]
    exact (canonical36867 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2632 + difference 2 0) (sourceB2632 + difference 0 2) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4969) := by
    have ha : (tripleCharges (sourceA2632 + difference 2 0) (sourceB2632 + difference 0 2) sourceC2632) = raw36868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36868; decide +kernel
    rw [ha]
    exact (canonical36868 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2632 + difference 2 1) (sourceB2632 + difference 1 2) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4936) := by
    have ha : (tripleCharges (sourceA2632 + difference 2 1) (sourceB2632 + difference 1 2) sourceC2632) = raw36869 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36869; decide +kernel
    rw [ha]
    exact (canonical36869 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2632 + difference 2 3) (sourceB2632 + difference 3 2) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA2632 + difference 2 3) (sourceB2632 + difference 3 2) sourceC2632) = raw36870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36870; decide +kernel
    rw [ha]
    exact (canonical36870 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2632 + difference 2 4) (sourceB2632 + difference 4 2) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA2632 + difference 2 4) (sourceB2632 + difference 4 2) sourceC2632) = raw36871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36871; decide +kernel
    rw [ha]
    exact (canonical36871 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2632 + difference 2 5) (sourceB2632 + difference 5 2) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5363) := by
    have ha : (tripleCharges (sourceA2632 + difference 2 5) (sourceB2632 + difference 5 2) sourceC2632) = raw36872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36872; decide +kernel
    rw [ha]
    exact (canonical36872 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2632 + difference 3 0) (sourceB2632 + difference 0 3) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4961) := by
    have ha : (tripleCharges (sourceA2632 + difference 3 0) (sourceB2632 + difference 0 3) sourceC2632) = raw36873 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36873; decide +kernel
    rw [ha]
    exact (canonical36873 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2632 + difference 3 1) (sourceB2632 + difference 1 3) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2632 + difference 3 1) (sourceB2632 + difference 1 3) sourceC2632) = raw36874 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36874; decide +kernel
    rw [ha]
    exact (canonical36874 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2632 + difference 3 2) (sourceB2632 + difference 2 3) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5332) := by
    have ha : (tripleCharges (sourceA2632 + difference 3 2) (sourceB2632 + difference 2 3) sourceC2632) = raw36875 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36875; decide +kernel
    rw [ha]
    exact (canonical36875 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2632 + difference 3 4) (sourceB2632 + difference 4 3) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA2632 + difference 3 4) (sourceB2632 + difference 4 3) sourceC2632) = raw36876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36876; decide +kernel
    rw [ha]
    exact (canonical36876 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2632 + difference 3 5) (sourceB2632 + difference 5 3) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA2632 + difference 3 5) (sourceB2632 + difference 5 3) sourceC2632) = raw36877 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36877; decide +kernel
    rw [ha]
    exact (canonical36877 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2632 + difference 4 0) (sourceB2632 + difference 0 4) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4961) := by
    have ha : (tripleCharges (sourceA2632 + difference 4 0) (sourceB2632 + difference 0 4) sourceC2632) = raw36878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36878; decide +kernel
    rw [ha]
    exact (canonical36878 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2632 + difference 4 1) (sourceB2632 + difference 1 4) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2632 + difference 4 1) (sourceB2632 + difference 1 4) sourceC2632) = raw36879 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36879; decide +kernel
    rw [ha]
    exact (canonical36879 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2632 + difference 4 2) (sourceB2632 + difference 2 4) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5332) := by
    have ha : (tripleCharges (sourceA2632 + difference 4 2) (sourceB2632 + difference 2 4) sourceC2632) = raw36880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36880; decide +kernel
    rw [ha]
    exact (canonical36880 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2632 + difference 4 3) (sourceB2632 + difference 3 4) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA2632 + difference 4 3) (sourceB2632 + difference 3 4) sourceC2632) = raw36881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36881; decide +kernel
    rw [ha]
    exact (canonical36881 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2632 + difference 4 5) (sourceB2632 + difference 5 4) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA2632 + difference 4 5) (sourceB2632 + difference 5 4) sourceC2632) = raw36882 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36882; decide +kernel
    rw [ha]
    exact (canonical36882 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2632 + difference 5 0) (sourceB2632 + difference 0 5) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4960) := by
    have ha : (tripleCharges (sourceA2632 + difference 5 0) (sourceB2632 + difference 0 5) sourceC2632) = raw36883 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36883; decide +kernel
    rw [ha]
    exact (canonical36883 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2632 + difference 5 1) (sourceB2632 + difference 1 5) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4927) := by
    have ha : (tripleCharges (sourceA2632 + difference 5 1) (sourceB2632 + difference 1 5) sourceC2632) = raw36884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36884; decide +kernel
    rw [ha]
    exact (canonical36884 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2632 + difference 5 2) (sourceB2632 + difference 2 5) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5029) := by
    have ha : (tripleCharges (sourceA2632 + difference 5 2) (sourceB2632 + difference 2 5) sourceC2632) = raw36885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36885; decide +kernel
    rw [ha]
    exact (canonical36885 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2632 + difference 5 3) (sourceB2632 + difference 3 5) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2632 + difference 5 3) (sourceB2632 + difference 3 5) sourceC2632) = raw36886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36886; decide +kernel
    rw [ha]
    exact (canonical36886 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2632 + difference 5 4) (sourceB2632 + difference 4 5) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2632 + difference 5 4) (sourceB2632 + difference 4 5) sourceC2632) = raw36887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36887; decide +kernel
    rw [ha]
    exact (canonical36887 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2632 sourceB2632 sourceC2632
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2632, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2096 : Integer.Sparse.reindex keyMap MixedData.row2096 = numericRow2096 := by decide +kernel

theorem numericCheck2096 (x : Master → ℝ) : Integer.Sparse.eval numericRow2096 x =
    (4 : ℝ) * reducedSource2096 x := by
  norm_num [numericRow2096, reducedSource2096, Integer.Sparse.eval, Sparse.eval, nodeValue4090, nodeValue4927, nodeValue4928, nodeValue4936, nodeValue4960, nodeValue4961, nodeValue4969, nodeValue5029, nodeValue5050, nodeValue5058, nodeValue5192, nodeValue5332, nodeValue5341, nodeValue5346, nodeValue5349, nodeValue5363, nodeValue5392, nodeValue5394, nodeValue5395, nodeValue5396, nodeValue5469] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2096 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2096 (mixedVector B) = 0 := by
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  have h4927 : mixedVector B (Sum.inr 4927) = Sparse.eval nodeValue4927 (mixedVector B) := by
    change mixedMoment B node4927 node4927Labels = _
    exact sound4927 B hB hF
  have h4928 : mixedVector B (Sum.inr 4928) = Sparse.eval nodeValue4928 (mixedVector B) := by
    change mixedMoment B node4928 node4928Labels = _
    exact sound4928 B hB hF
  have h4936 : mixedVector B (Sum.inr 4936) = Sparse.eval nodeValue4936 (mixedVector B) := by
    change mixedMoment B node4936 node4936Labels = _
    exact sound4936 B hB hF
  have h4960 : mixedVector B (Sum.inr 4960) = Sparse.eval nodeValue4960 (mixedVector B) := by
    change mixedMoment B node4960 node4960Labels = _
    exact sound4960 B hB hF
  have h4961 : mixedVector B (Sum.inr 4961) = Sparse.eval nodeValue4961 (mixedVector B) := by
    change mixedMoment B node4961 node4961Labels = _
    exact sound4961 B hB hF
  have h4969 : mixedVector B (Sum.inr 4969) = Sparse.eval nodeValue4969 (mixedVector B) := by
    change mixedMoment B node4969 node4969Labels = _
    exact sound4969 B hB hF
  have h5029 : mixedVector B (Sum.inr 5029) = Sparse.eval nodeValue5029 (mixedVector B) := by
    change mixedMoment B node5029 node5029Labels = _
    exact sound5029 B hB hF
  have h5050 : mixedVector B (Sum.inr 5050) = Sparse.eval nodeValue5050 (mixedVector B) := by
    change mixedMoment B node5050 node5050Labels = _
    exact sound5050 B hB hF
  have h5058 : mixedVector B (Sum.inr 5058) = Sparse.eval nodeValue5058 (mixedVector B) := by
    change mixedMoment B node5058 node5058Labels = _
    exact sound5058 B hB hF
  have h5192 : mixedVector B (Sum.inr 5192) = Sparse.eval nodeValue5192 (mixedVector B) := by
    change mixedMoment B node5192 node5192Labels = _
    exact sound5192 B hB hF
  have h5332 : mixedVector B (Sum.inr 5332) = Sparse.eval nodeValue5332 (mixedVector B) := by
    change mixedMoment B node5332 node5332Labels = _
    exact sound5332 B hB hF
  have h5341 : mixedVector B (Sum.inr 5341) = Sparse.eval nodeValue5341 (mixedVector B) := by
    change mixedMoment B node5341 node5341Labels = _
    exact sound5341 B hB hF
  have h5346 : mixedVector B (Sum.inr 5346) = Sparse.eval nodeValue5346 (mixedVector B) := by
    change mixedMoment B node5346 node5346Labels = _
    exact sound5346 B hB hF
  have h5349 : mixedVector B (Sum.inr 5349) = Sparse.eval nodeValue5349 (mixedVector B) := by
    change mixedMoment B node5349 node5349Labels = _
    exact sound5349 B hB hF
  have h5363 : mixedVector B (Sum.inr 5363) = Sparse.eval nodeValue5363 (mixedVector B) := by
    change mixedMoment B node5363 node5363Labels = _
    exact sound5363 B hB hF
  have h5392 : mixedVector B (Sum.inr 5392) = Sparse.eval nodeValue5392 (mixedVector B) := by
    change mixedMoment B node5392 node5392Labels = _
    exact sound5392 B hB hF
  have h5394 : mixedVector B (Sum.inr 5394) = Sparse.eval nodeValue5394 (mixedVector B) := by
    change mixedMoment B node5394 node5394Labels = _
    exact sound5394 B hB hF
  have h5395 : mixedVector B (Sum.inr 5395) = Sparse.eval nodeValue5395 (mixedVector B) := by
    change mixedMoment B node5395 node5395Labels = _
    exact sound5395 B hB hF
  have h5396 : mixedVector B (Sum.inr 5396) = Sparse.eval nodeValue5396 (mixedVector B) := by
    change mixedMoment B node5396 node5396Labels = _
    exact sound5396 B hB hF
  have h5469 : mixedVector B (Sum.inr 5469) = Sparse.eval nodeValue5469 (mixedVector B) := by
    change mixedMoment B node5469 node5469Labels = _
    exact sound5469 B hB hF
  simpa only [sourceForm2632, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4090, h4927, h4928, h4936, h4960, h4961, h4969, h5029, h5050, h5058, h5192, h5332, h5341, h5346, h5349, h5363, h5392, h5394, h5395, h5396, h5469, reducedSource2096] using sourceEq2632 B hB

theorem rowSound2096_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2096 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2096, numericCheck2096, reducedZero2096 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e_oai
