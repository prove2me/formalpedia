-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:32:20.170213+00:00
-- url     : https://prove2.me/submissions/f62b71d1-e6d6-4ce8-bdad-2785c1955ec7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
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

theorem canonical242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw242 raw242Labels = mixedMoment B node2601 node2601Labels := by
  calc
    mixedMoment B raw242 raw242Labels = mixedMoment B raw242step0 raw242step0Labels := by
      have ha : raw242step0 = (fun i j => raw242 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw242step0 raw242; decide +kernel
      have hl : raw242step0Labels = raw242Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw242 raw242Labels permutation8 permutation5
    mixedMoment B raw242step0 raw242step0Labels = mixedMoment B raw242step1 raw242step1Labels := by
      have ha : raw242step1 = raw242step0 := by apply Matrix.ext; unfold raw242step1 raw242step0; decide +kernel
      have hl : raw242step0Labels = labelEmbedding1 ∘ raw242step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw242step0 raw242step0Labels raw242step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2601 node2601Labels := by rfl

theorem canonical243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw243 raw243Labels = mixedMoment B node341 node341Labels := by
  calc
    mixedMoment B raw243 raw243Labels = mixedMoment B raw243step0 raw243step0Labels := by
      have ha : raw243step0 = (fun i j => raw243 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw243step0 raw243; decide +kernel
      have hl : raw243step0Labels = raw243Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw243 raw243Labels permutation31 permutation4
    mixedMoment B raw243step0 raw243step0Labels = mixedMoment B raw243step1 raw243step1Labels := by
      have ha : raw243step1 = -raw243step0 := by apply Matrix.ext; change ∀ i j, raw243step1 i j = -(raw243step0 i j); unfold raw243step1 raw243step0; decide +kernel
      have hl : raw243step1Labels = raw243step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node341 node341Labels := by rfl

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

theorem canonical258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw258 raw258Labels = mixedMoment B node2640 node2640Labels := by
  calc
    mixedMoment B raw258 raw258Labels = mixedMoment B raw258step0 raw258step0Labels := by
      have ha : raw258step0 = (fun i j => raw258 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw258step0 raw258; decide +kernel
      have hl : raw258step0Labels = raw258Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw258 raw258Labels permutation8 permutation5
    mixedMoment B raw258step0 raw258step0Labels = mixedMoment B raw258step1 raw258step1Labels := by
      have ha : raw258step1 = raw258step0 := by apply Matrix.ext; unfold raw258step1 raw258step0; decide +kernel
      have hl : raw258step0Labels = labelEmbedding1 ∘ raw258step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw258step0 raw258step0Labels raw258step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2640 node2640Labels := by rfl

theorem canonical259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw259 raw259Labels = mixedMoment B node315 node315Labels := by
  calc
    mixedMoment B raw259 raw259Labels = mixedMoment B raw259step0 raw259step0Labels := by
      have ha : raw259step0 = (fun i j => raw259 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw259step0 raw259; decide +kernel
      have hl : raw259step0Labels = raw259Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw259 raw259Labels permutation31 permutation4
    mixedMoment B raw259step0 raw259step0Labels = mixedMoment B raw259step1 raw259step1Labels := by
      have ha : raw259step1 = -raw259step0 := by apply Matrix.ext; change ∀ i j, raw259step1 i j = -(raw259step0 i j); unfold raw259step1 raw259step0; decide +kernel
      have hl : raw259step1Labels = raw259step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node315 node315Labels := by rfl

theorem canonical260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw260 raw260Labels = mixedMoment B node2642 node2642Labels := by
  calc
    mixedMoment B raw260 raw260Labels = mixedMoment B raw260step0 raw260step0Labels := by
      have ha : raw260step0 = (fun i j => raw260 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw260step0 raw260; decide +kernel
      have hl : raw260step0Labels = raw260Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw260 raw260Labels permutation8 permutation5
    mixedMoment B raw260step0 raw260step0Labels = mixedMoment B raw260step1 raw260step1Labels := by
      have ha : raw260step1 = raw260step0 := by apply Matrix.ext; unfold raw260step1 raw260step0; decide +kernel
      have hl : raw260step0Labels = labelEmbedding1 ∘ raw260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw260step0 raw260step0Labels raw260step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2642 node2642Labels := by rfl

theorem canonical261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw261 raw261Labels = mixedMoment B node236 node236Labels := by
  calc
    mixedMoment B raw261 raw261Labels = mixedMoment B raw261step0 raw261step0Labels := by
      have ha : raw261step0 = (fun i j => raw261 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw261step0 raw261; decide +kernel
      have hl : raw261step0Labels = raw261Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw261 raw261Labels permutation31 permutation4
    mixedMoment B raw261step0 raw261step0Labels = mixedMoment B raw261step1 raw261step1Labels := by
      have ha : raw261step1 = -raw261step0 := by apply Matrix.ext; change ∀ i j, raw261step1 i j = -(raw261step0 i j); unfold raw261step1 raw261step0; decide +kernel
      have hl : raw261step1Labels = raw261step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node236 node236Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical217
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27781 raw27781Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw27781 raw27781Labels = mixedMoment B raw27781step0 raw27781step0Labels := by
      have hz : ∀ j, raw27781 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27781step0 = (fun i j => raw27781 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27781step0 raw27781; decide +kernel
      have hl : raw27781step0Labels = raw27781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27781 raw27781Labels permutation434 hz
    mixedMoment B raw27781step0 raw27781step0Labels = mixedMoment B raw27781step1 raw27781step1Labels := by
      have hz : ∀ j, raw27781step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27781step1 = (fun i j => raw27781step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27781step1 raw27781step0; decide +kernel
      have hl : raw27781step1Labels = raw27781step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27781step0 raw27781step0Labels permutation80 hz
    mixedMoment B raw27781step1 raw27781step1Labels = mixedMoment B raw27781step2 raw27781step2Labels := by
      have ha : raw27781step2 = (fun i j => raw27781step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27781step2 raw27781step1; decide +kernel
      have hl : raw27781step2Labels = raw27781step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27781step1 raw27781step1Labels permutation31 permutation7
    mixedMoment B raw27781step2 raw27781step2Labels = mixedMoment B raw27781step3 raw27781step3Labels := by
      have ha : raw27781step3 = -raw27781step2 := by apply Matrix.ext; change ∀ i j, raw27781step3 i j = -(raw27781step2 i j); unfold raw27781step3 raw27781step2; decide +kernel
      have hl : raw27781step3Labels = raw27781step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27781step3 raw27781step3Labels = mixedMoment B raw27781step4 raw27781step4Labels := by
      have ha : raw27781step4 = raw27781step3 := by apply Matrix.ext; unfold raw27781step4 raw27781step3; decide +kernel
      have hl : raw27781step3Labels = labelEmbedding1 ∘ raw27781step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27781step3 raw27781step3Labels raw27781step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2109 node2109Labels := by rfl

theorem canonical27782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27782 raw27782Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw27782 raw27782Labels = mixedMoment B raw27782step0 raw27782step0Labels := by
      have hz : ∀ j, raw27782 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27782step0 = (fun i j => raw27782 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27782step0 raw27782; decide +kernel
      have hl : raw27782step0Labels = raw27782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27782 raw27782Labels permutation434 hz
    mixedMoment B raw27782step0 raw27782step0Labels = mixedMoment B raw27782step1 raw27782step1Labels := by
      have ha : raw27782step1 = (fun i j => raw27782step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27782step1 raw27782step0; decide +kernel
      have hl : raw27782step1Labels = raw27782step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27782step0 raw27782step0Labels permutation151 permutation7
    mixedMoment B raw27782step1 raw27782step1Labels = mixedMoment B raw27782step2 raw27782step2Labels := by
      have ha : raw27782step2 = -raw27782step1 := by apply Matrix.ext; change ∀ i j, raw27782step2 i j = -(raw27782step1 i j); unfold raw27782step2 raw27782step1; decide +kernel
      have hl : raw27782step2Labels = raw27782step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27782step2 raw27782step2Labels = mixedMoment B raw27782step3 raw27782step3Labels := by
      have ha : raw27782step3 = raw27782step2 := by apply Matrix.ext; unfold raw27782step3 raw27782step2; decide +kernel
      have hl : raw27782step2Labels = labelEmbedding1 ∘ raw27782step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27782step2 raw27782step2Labels raw27782step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2079 node2079Labels := by rfl

theorem canonical27783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27783 raw27783Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw27783 raw27783Labels = mixedMoment B raw27783step0 raw27783step0Labels := by
      have hz : ∀ j, raw27783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27783step0 = (fun i j => raw27783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27783step0 raw27783; decide +kernel
      have hl : raw27783step0Labels = raw27783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27783 raw27783Labels permutation346 hz
    mixedMoment B raw27783step0 raw27783step0Labels = mixedMoment B raw27783step1 raw27783step1Labels := by
      have ha : raw27783step1 = (fun i j => raw27783step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27783step1 raw27783step0; decide +kernel
      have hl : raw27783step1Labels = raw27783step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27783step0 raw27783step0Labels permutation151 permutation7
    mixedMoment B raw27783step1 raw27783step1Labels = mixedMoment B raw27783step2 raw27783step2Labels := by
      have ha : raw27783step2 = -raw27783step1 := by apply Matrix.ext; change ∀ i j, raw27783step2 i j = -(raw27783step1 i j); unfold raw27783step2 raw27783step1; decide +kernel
      have hl : raw27783step2Labels = raw27783step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27783step2 raw27783step2Labels = mixedMoment B raw27783step3 raw27783step3Labels := by
      have ha : raw27783step3 = raw27783step2 := by apply Matrix.ext; unfold raw27783step3 raw27783step2; decide +kernel
      have hl : raw27783step2Labels = labelEmbedding1 ∘ raw27783step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27783step2 raw27783step2Labels raw27783step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2079 node2079Labels := by rfl

theorem canonical27784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27784 raw27784Labels = mixedMoment B node2060 node2060Labels := by
  calc
    mixedMoment B raw27784 raw27784Labels = mixedMoment B raw27784step0 raw27784step0Labels := by
      have hz : ∀ j, raw27784 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27784step0 = (fun i j => raw27784 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27784step0 raw27784; decide +kernel
      have hl : raw27784step0Labels = raw27784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27784 raw27784Labels permutation434 hz
    mixedMoment B raw27784step0 raw27784step0Labels = mixedMoment B raw27784step1 raw27784step1Labels := by
      have hz : ∀ j, raw27784step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27784step1 = (fun i j => raw27784step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27784step1 raw27784step0; decide +kernel
      have hl : raw27784step1Labels = raw27784step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27784step0 raw27784step0Labels permutation80 hz
    mixedMoment B raw27784step1 raw27784step1Labels = mixedMoment B raw27784step2 raw27784step2Labels := by
      have ha : raw27784step2 = (fun i j => raw27784step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27784step2 raw27784step1; decide +kernel
      have hl : raw27784step2Labels = raw27784step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27784step1 raw27784step1Labels permutation31 permutation7
    mixedMoment B raw27784step2 raw27784step2Labels = mixedMoment B raw27784step3 raw27784step3Labels := by
      have ha : raw27784step3 = -raw27784step2 := by apply Matrix.ext; change ∀ i j, raw27784step3 i j = -(raw27784step2 i j); unfold raw27784step3 raw27784step2; decide +kernel
      have hl : raw27784step3Labels = raw27784step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27784step3 raw27784step3Labels = mixedMoment B raw27784step4 raw27784step4Labels := by
      have ha : raw27784step4 = raw27784step3 := by apply Matrix.ext; unfold raw27784step4 raw27784step3; decide +kernel
      have hl : raw27784step3Labels = labelEmbedding1 ∘ raw27784step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27784step3 raw27784step3Labels raw27784step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2060 node2060Labels := by rfl

theorem canonical27785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27785 raw27785Labels = mixedMoment B node1650 node1650Labels := by
  calc
    mixedMoment B raw27785 raw27785Labels = mixedMoment B raw27785step0 raw27785step0Labels := by
      have hz : ∀ j, raw27785 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27785step0 = (fun i j => raw27785 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27785step0 raw27785; decide +kernel
      have hl : raw27785step0Labels = raw27785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27785 raw27785Labels permutation434 hz
    mixedMoment B raw27785step0 raw27785step0Labels = mixedMoment B raw27785step1 raw27785step1Labels := by
      have hz : ∀ j, raw27785step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27785step1 = (fun i j => raw27785step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27785step1 raw27785step0; decide +kernel
      have hl : raw27785step1Labels = raw27785step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27785step0 raw27785step0Labels permutation80 hz
    mixedMoment B raw27785step1 raw27785step1Labels = mixedMoment B raw27785step2 raw27785step2Labels := by
      have ha : raw27785step2 = (fun i j => raw27785step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27785step2 raw27785step1; decide +kernel
      have hl : raw27785step2Labels = raw27785step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27785step1 raw27785step1Labels permutation31 permutation7
    mixedMoment B raw27785step2 raw27785step2Labels = mixedMoment B raw27785step3 raw27785step3Labels := by
      have ha : raw27785step3 = -raw27785step2 := by apply Matrix.ext; change ∀ i j, raw27785step3 i j = -(raw27785step2 i j); unfold raw27785step3 raw27785step2; decide +kernel
      have hl : raw27785step3Labels = raw27785step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27785step3 raw27785step3Labels = mixedMoment B raw27785step4 raw27785step4Labels := by
      have ha : raw27785step4 = raw27785step3 := by apply Matrix.ext; unfold raw27785step4 raw27785step3; decide +kernel
      have hl : raw27785step3Labels = labelEmbedding1 ∘ raw27785step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27785step3 raw27785step3Labels raw27785step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1650 node1650Labels := by rfl

theorem canonical27786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27786 raw27786Labels = mixedMoment B node2113 node2113Labels := by
  calc
    mixedMoment B raw27786 raw27786Labels = mixedMoment B raw27786step0 raw27786step0Labels := by
      have hz : ∀ j, raw27786 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27786step0 = (fun i j => raw27786 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27786step0 raw27786; decide +kernel
      have hl : raw27786step0Labels = raw27786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27786 raw27786Labels permutation434 hz
    mixedMoment B raw27786step0 raw27786step0Labels = mixedMoment B raw27786step1 raw27786step1Labels := by
      have hz : ∀ j, raw27786step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27786step1 = (fun i j => raw27786step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27786step1 raw27786step0; decide +kernel
      have hl : raw27786step1Labels = raw27786step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27786step0 raw27786step0Labels permutation80 hz
    mixedMoment B raw27786step1 raw27786step1Labels = mixedMoment B raw27786step2 raw27786step2Labels := by
      have ha : raw27786step2 = (fun i j => raw27786step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27786step2 raw27786step1; decide +kernel
      have hl : raw27786step2Labels = raw27786step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27786step1 raw27786step1Labels permutation31 permutation7
    mixedMoment B raw27786step2 raw27786step2Labels = mixedMoment B raw27786step3 raw27786step3Labels := by
      have ha : raw27786step3 = -raw27786step2 := by apply Matrix.ext; change ∀ i j, raw27786step3 i j = -(raw27786step2 i j); unfold raw27786step3 raw27786step2; decide +kernel
      have hl : raw27786step3Labels = raw27786step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27786step3 raw27786step3Labels = mixedMoment B raw27786step4 raw27786step4Labels := by
      have ha : raw27786step4 = raw27786step3 := by apply Matrix.ext; unfold raw27786step4 raw27786step3; decide +kernel
      have hl : raw27786step3Labels = labelEmbedding1 ∘ raw27786step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27786step3 raw27786step3Labels raw27786step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2113 node2113Labels := by rfl

theorem canonical27787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27787 raw27787Labels = mixedMoment B node2080 node2080Labels := by
  calc
    mixedMoment B raw27787 raw27787Labels = mixedMoment B raw27787step0 raw27787step0Labels := by
      have hz : ∀ j, raw27787 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27787step0 = (fun i j => raw27787 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27787step0 raw27787; decide +kernel
      have hl : raw27787step0Labels = raw27787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27787 raw27787Labels permutation434 hz
    mixedMoment B raw27787step0 raw27787step0Labels = mixedMoment B raw27787step1 raw27787step1Labels := by
      have ha : raw27787step1 = (fun i j => raw27787step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27787step1 raw27787step0; decide +kernel
      have hl : raw27787step1Labels = raw27787step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27787step0 raw27787step0Labels permutation151 permutation7
    mixedMoment B raw27787step1 raw27787step1Labels = mixedMoment B raw27787step2 raw27787step2Labels := by
      have ha : raw27787step2 = -raw27787step1 := by apply Matrix.ext; change ∀ i j, raw27787step2 i j = -(raw27787step1 i j); unfold raw27787step2 raw27787step1; decide +kernel
      have hl : raw27787step2Labels = raw27787step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27787step2 raw27787step2Labels = mixedMoment B raw27787step3 raw27787step3Labels := by
      have ha : raw27787step3 = raw27787step2 := by apply Matrix.ext; unfold raw27787step3 raw27787step2; decide +kernel
      have hl : raw27787step2Labels = labelEmbedding1 ∘ raw27787step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27787step2 raw27787step2Labels raw27787step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2080 node2080Labels := by rfl

theorem canonical27788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27788 raw27788Labels = mixedMoment B node2080 node2080Labels := by
  calc
    mixedMoment B raw27788 raw27788Labels = mixedMoment B raw27788step0 raw27788step0Labels := by
      have hz : ∀ j, raw27788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27788step0 = (fun i j => raw27788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27788step0 raw27788; decide +kernel
      have hl : raw27788step0Labels = raw27788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27788 raw27788Labels permutation346 hz
    mixedMoment B raw27788step0 raw27788step0Labels = mixedMoment B raw27788step1 raw27788step1Labels := by
      have ha : raw27788step1 = (fun i j => raw27788step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27788step1 raw27788step0; decide +kernel
      have hl : raw27788step1Labels = raw27788step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27788step0 raw27788step0Labels permutation151 permutation7
    mixedMoment B raw27788step1 raw27788step1Labels = mixedMoment B raw27788step2 raw27788step2Labels := by
      have ha : raw27788step2 = -raw27788step1 := by apply Matrix.ext; change ∀ i j, raw27788step2 i j = -(raw27788step1 i j); unfold raw27788step2 raw27788step1; decide +kernel
      have hl : raw27788step2Labels = raw27788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27788step2 raw27788step2Labels = mixedMoment B raw27788step3 raw27788step3Labels := by
      have ha : raw27788step3 = raw27788step2 := by apply Matrix.ext; unfold raw27788step3 raw27788step2; decide +kernel
      have hl : raw27788step2Labels = labelEmbedding1 ∘ raw27788step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27788step2 raw27788step2Labels raw27788step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2080 node2080Labels := by rfl

theorem canonical27789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27789 raw27789Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw27789 raw27789Labels = mixedMoment B raw27789step0 raw27789step0Labels := by
      have hz : ∀ j, raw27789 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27789step0 = (fun i j => raw27789 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27789step0 raw27789; decide +kernel
      have hl : raw27789step0Labels = raw27789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27789 raw27789Labels permutation434 hz
    mixedMoment B raw27789step0 raw27789step0Labels = mixedMoment B raw27789step1 raw27789step1Labels := by
      have hz : ∀ j, raw27789step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27789step1 = (fun i j => raw27789step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27789step1 raw27789step0; decide +kernel
      have hl : raw27789step1Labels = raw27789step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27789step0 raw27789step0Labels permutation80 hz
    mixedMoment B raw27789step1 raw27789step1Labels = mixedMoment B raw27789step2 raw27789step2Labels := by
      have ha : raw27789step2 = (fun i j => raw27789step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27789step2 raw27789step1; decide +kernel
      have hl : raw27789step2Labels = raw27789step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27789step1 raw27789step1Labels permutation31 permutation7
    mixedMoment B raw27789step2 raw27789step2Labels = mixedMoment B raw27789step3 raw27789step3Labels := by
      have ha : raw27789step3 = -raw27789step2 := by apply Matrix.ext; change ∀ i j, raw27789step3 i j = -(raw27789step2 i j); unfold raw27789step3 raw27789step2; decide +kernel
      have hl : raw27789step3Labels = raw27789step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27789step3 raw27789step3Labels = mixedMoment B raw27789step4 raw27789step4Labels := by
      have ha : raw27789step4 = raw27789step3 := by apply Matrix.ext; unfold raw27789step4 raw27789step3; decide +kernel
      have hl : raw27789step3Labels = labelEmbedding1 ∘ raw27789step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27789step3 raw27789step3Labels raw27789step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical27790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27790 raw27790Labels = mixedMoment B node1651 node1651Labels := by
  calc
    mixedMoment B raw27790 raw27790Labels = mixedMoment B raw27790step0 raw27790step0Labels := by
      have hz : ∀ j, raw27790 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27790step0 = (fun i j => raw27790 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27790step0 raw27790; decide +kernel
      have hl : raw27790step0Labels = raw27790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27790 raw27790Labels permutation434 hz
    mixedMoment B raw27790step0 raw27790step0Labels = mixedMoment B raw27790step1 raw27790step1Labels := by
      have hz : ∀ j, raw27790step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27790step1 = (fun i j => raw27790step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27790step1 raw27790step0; decide +kernel
      have hl : raw27790step1Labels = raw27790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27790step0 raw27790step0Labels permutation80 hz
    mixedMoment B raw27790step1 raw27790step1Labels = mixedMoment B raw27790step2 raw27790step2Labels := by
      have ha : raw27790step2 = (fun i j => raw27790step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27790step2 raw27790step1; decide +kernel
      have hl : raw27790step2Labels = raw27790step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27790step1 raw27790step1Labels permutation31 permutation7
    mixedMoment B raw27790step2 raw27790step2Labels = mixedMoment B raw27790step3 raw27790step3Labels := by
      have ha : raw27790step3 = -raw27790step2 := by apply Matrix.ext; change ∀ i j, raw27790step3 i j = -(raw27790step2 i j); unfold raw27790step3 raw27790step2; decide +kernel
      have hl : raw27790step3Labels = raw27790step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27790step3 raw27790step3Labels = mixedMoment B raw27790step4 raw27790step4Labels := by
      have ha : raw27790step4 = raw27790step3 := by apply Matrix.ext; unfold raw27790step4 raw27790step3; decide +kernel
      have hl : raw27790step3Labels = labelEmbedding1 ∘ raw27790step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27790step3 raw27790step3Labels raw27790step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1651 node1651Labels := by rfl

theorem canonical27791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27791 raw27791Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw27791 raw27791Labels = mixedMoment B raw27791step0 raw27791step0Labels := by
      have hz : ∀ j, raw27791 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27791step0 = (fun i j => raw27791 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27791step0 raw27791; decide +kernel
      have hl : raw27791step0Labels = raw27791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27791 raw27791Labels permutation434 hz
    mixedMoment B raw27791step0 raw27791step0Labels = mixedMoment B raw27791step1 raw27791step1Labels := by
      have ha : raw27791step1 = (fun i j => raw27791step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27791step1 raw27791step0; decide +kernel
      have hl : raw27791step1Labels = raw27791step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27791step0 raw27791step0Labels permutation151 permutation7
    mixedMoment B raw27791step1 raw27791step1Labels = mixedMoment B raw27791step2 raw27791step2Labels := by
      have ha : raw27791step2 = -raw27791step1 := by apply Matrix.ext; change ∀ i j, raw27791step2 i j = -(raw27791step1 i j); unfold raw27791step2 raw27791step1; decide +kernel
      have hl : raw27791step2Labels = raw27791step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27791step2 raw27791step2Labels = mixedMoment B raw27791step3 raw27791step3Labels := by
      have ha : raw27791step3 = raw27791step2 := by apply Matrix.ext; unfold raw27791step3 raw27791step2; decide +kernel
      have hl : raw27791step2Labels = labelEmbedding1 ∘ raw27791step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27791step2 raw27791step2Labels raw27791step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2092 node2092Labels := by rfl

theorem canonical27792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27792 raw27792Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw27792 raw27792Labels = mixedMoment B raw27792step0 raw27792step0Labels := by
      have hz : ∀ j, raw27792 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27792step0 = (fun i j => raw27792 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27792step0 raw27792; decide +kernel
      have hl : raw27792step0Labels = raw27792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27792 raw27792Labels permutation434 hz
    mixedMoment B raw27792step0 raw27792step0Labels = mixedMoment B raw27792step1 raw27792step1Labels := by
      have ha : raw27792step1 = (fun i j => raw27792step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27792step1 raw27792step0; decide +kernel
      have hl : raw27792step1Labels = raw27792step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27792step0 raw27792step0Labels permutation151 permutation7
    mixedMoment B raw27792step1 raw27792step1Labels = mixedMoment B raw27792step2 raw27792step2Labels := by
      have ha : raw27792step2 = -raw27792step1 := by apply Matrix.ext; change ∀ i j, raw27792step2 i j = -(raw27792step1 i j); unfold raw27792step2 raw27792step1; decide +kernel
      have hl : raw27792step2Labels = raw27792step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27792step2 raw27792step2Labels = mixedMoment B raw27792step3 raw27792step3Labels := by
      have ha : raw27792step3 = raw27792step2 := by apply Matrix.ext; unfold raw27792step3 raw27792step2; decide +kernel
      have hl : raw27792step2Labels = labelEmbedding1 ∘ raw27792step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27792step2 raw27792step2Labels raw27792step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2090 node2090Labels := by rfl

theorem canonical27793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27793 raw27793Labels = mixedMoment B node2071 node2071Labels := by
  calc
    mixedMoment B raw27793 raw27793Labels = mixedMoment B raw27793step0 raw27793step0Labels := by
      have ha : raw27793step0 = (fun i j => raw27793 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27793step0 raw27793; decide +kernel
      have hl : raw27793step0Labels = raw27793Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27793 raw27793Labels permutation688 permutation7
    mixedMoment B raw27793step0 raw27793step0Labels = mixedMoment B raw27793step1 raw27793step1Labels := by
      have ha : raw27793step1 = -raw27793step0 := by apply Matrix.ext; change ∀ i j, raw27793step1 i j = -(raw27793step0 i j); unfold raw27793step1 raw27793step0; decide +kernel
      have hl : raw27793step1Labels = raw27793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27793step1 raw27793step1Labels = mixedMoment B raw27793step2 raw27793step2Labels := by
      have ha : raw27793step2 = raw27793step1 := by apply Matrix.ext; unfold raw27793step2 raw27793step1; decide +kernel
      have hl : raw27793step1Labels = labelEmbedding1 ∘ raw27793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27793step1 raw27793step1Labels raw27793step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2071 node2071Labels := by rfl

theorem canonical27794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27794 raw27794Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw27794 raw27794Labels = mixedMoment B raw27794step0 raw27794step0Labels := by
      have hz : ∀ j, raw27794 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27794step0 = (fun i j => raw27794 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27794step0 raw27794; decide +kernel
      have hl : raw27794step0Labels = raw27794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27794 raw27794Labels permutation434 hz
    mixedMoment B raw27794step0 raw27794step0Labels = mixedMoment B raw27794step1 raw27794step1Labels := by
      have ha : raw27794step1 = (fun i j => raw27794step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27794step1 raw27794step0; decide +kernel
      have hl : raw27794step1Labels = raw27794step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27794step0 raw27794step0Labels permutation151 permutation7
    mixedMoment B raw27794step1 raw27794step1Labels = mixedMoment B raw27794step2 raw27794step2Labels := by
      have ha : raw27794step2 = -raw27794step1 := by apply Matrix.ext; change ∀ i j, raw27794step2 i j = -(raw27794step1 i j); unfold raw27794step2 raw27794step1; decide +kernel
      have hl : raw27794step2Labels = raw27794step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27794step2 raw27794step2Labels = mixedMoment B raw27794step3 raw27794step3Labels := by
      have ha : raw27794step3 = raw27794step2 := by apply Matrix.ext; unfold raw27794step3 raw27794step2; decide +kernel
      have hl : raw27794step2Labels = labelEmbedding1 ∘ raw27794step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27794step2 raw27794step2Labels raw27794step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical27795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27795 raw27795Labels = mixedMoment B node1639 node1639Labels := by
  calc
    mixedMoment B raw27795 raw27795Labels = mixedMoment B raw27795step0 raw27795step0Labels := by
      have hz : ∀ j, raw27795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27795step0 = (fun i j => raw27795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27795step0 raw27795; decide +kernel
      have hl : raw27795step0Labels = raw27795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27795 raw27795Labels permutation434 hz
    mixedMoment B raw27795step0 raw27795step0Labels = mixedMoment B raw27795step1 raw27795step1Labels := by
      have ha : raw27795step1 = (fun i j => raw27795step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27795step1 raw27795step0; decide +kernel
      have hl : raw27795step1Labels = raw27795step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27795step0 raw27795step0Labels permutation151 permutation7
    mixedMoment B raw27795step1 raw27795step1Labels = mixedMoment B raw27795step2 raw27795step2Labels := by
      have ha : raw27795step2 = -raw27795step1 := by apply Matrix.ext; change ∀ i j, raw27795step2 i j = -(raw27795step1 i j); unfold raw27795step2 raw27795step1; decide +kernel
      have hl : raw27795step2Labels = raw27795step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27795step2 raw27795step2Labels = mixedMoment B raw27795step3 raw27795step3Labels := by
      have ha : raw27795step3 = raw27795step2 := by apply Matrix.ext; unfold raw27795step3 raw27795step2; decide +kernel
      have hl : raw27795step2Labels = labelEmbedding1 ∘ raw27795step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27795step2 raw27795step2Labels raw27795step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1639 node1639Labels := by rfl

theorem canonical27796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27796 raw27796Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw27796 raw27796Labels = mixedMoment B raw27796step0 raw27796step0Labels := by
      have hz : ∀ j, raw27796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27796step0 = (fun i j => raw27796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27796step0 raw27796; decide +kernel
      have hl : raw27796step0Labels = raw27796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27796 raw27796Labels permutation346 hz
    mixedMoment B raw27796step0 raw27796step0Labels = mixedMoment B raw27796step1 raw27796step1Labels := by
      have ha : raw27796step1 = (fun i j => raw27796step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27796step1 raw27796step0; decide +kernel
      have hl : raw27796step1Labels = raw27796step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27796step0 raw27796step0Labels permutation151 permutation7
    mixedMoment B raw27796step1 raw27796step1Labels = mixedMoment B raw27796step2 raw27796step2Labels := by
      have ha : raw27796step2 = -raw27796step1 := by apply Matrix.ext; change ∀ i j, raw27796step2 i j = -(raw27796step1 i j); unfold raw27796step2 raw27796step1; decide +kernel
      have hl : raw27796step2Labels = raw27796step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27796step2 raw27796step2Labels = mixedMoment B raw27796step3 raw27796step3Labels := by
      have ha : raw27796step3 = raw27796step2 := by apply Matrix.ext; unfold raw27796step3 raw27796step2; decide +kernel
      have hl : raw27796step2Labels = labelEmbedding1 ∘ raw27796step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27796step2 raw27796step2Labels raw27796step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2092 node2092Labels := by rfl

theorem canonical27797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27797 raw27797Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw27797 raw27797Labels = mixedMoment B raw27797step0 raw27797step0Labels := by
      have hz : ∀ j, raw27797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27797step0 = (fun i j => raw27797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27797step0 raw27797; decide +kernel
      have hl : raw27797step0Labels = raw27797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27797 raw27797Labels permutation346 hz
    mixedMoment B raw27797step0 raw27797step0Labels = mixedMoment B raw27797step1 raw27797step1Labels := by
      have ha : raw27797step1 = (fun i j => raw27797step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27797step1 raw27797step0; decide +kernel
      have hl : raw27797step1Labels = raw27797step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27797step0 raw27797step0Labels permutation151 permutation7
    mixedMoment B raw27797step1 raw27797step1Labels = mixedMoment B raw27797step2 raw27797step2Labels := by
      have ha : raw27797step2 = -raw27797step1 := by apply Matrix.ext; change ∀ i j, raw27797step2 i j = -(raw27797step1 i j); unfold raw27797step2 raw27797step1; decide +kernel
      have hl : raw27797step2Labels = raw27797step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27797step2 raw27797step2Labels = mixedMoment B raw27797step3 raw27797step3Labels := by
      have ha : raw27797step3 = raw27797step2 := by apply Matrix.ext; unfold raw27797step3 raw27797step2; decide +kernel
      have hl : raw27797step2Labels = labelEmbedding1 ∘ raw27797step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27797step2 raw27797step2Labels raw27797step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2090 node2090Labels := by rfl

theorem canonical27798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27798 raw27798Labels = mixedMoment B node2071 node2071Labels := by
  calc
    mixedMoment B raw27798 raw27798Labels = mixedMoment B raw27798step0 raw27798step0Labels := by
      have ha : raw27798step0 = (fun i j => raw27798 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27798step0 raw27798; decide +kernel
      have hl : raw27798step0Labels = raw27798Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27798 raw27798Labels permutation682 permutation7
    mixedMoment B raw27798step0 raw27798step0Labels = mixedMoment B raw27798step1 raw27798step1Labels := by
      have ha : raw27798step1 = -raw27798step0 := by apply Matrix.ext; change ∀ i j, raw27798step1 i j = -(raw27798step0 i j); unfold raw27798step1 raw27798step0; decide +kernel
      have hl : raw27798step1Labels = raw27798step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27798step1 raw27798step1Labels = mixedMoment B raw27798step2 raw27798step2Labels := by
      have ha : raw27798step2 = raw27798step1 := by apply Matrix.ext; unfold raw27798step2 raw27798step1; decide +kernel
      have hl : raw27798step1Labels = labelEmbedding1 ∘ raw27798step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27798step1 raw27798step1Labels raw27798step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2071 node2071Labels := by rfl

theorem canonical27799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27799 raw27799Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw27799 raw27799Labels = mixedMoment B raw27799step0 raw27799step0Labels := by
      have hz : ∀ j, raw27799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27799step0 = (fun i j => raw27799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27799step0 raw27799; decide +kernel
      have hl : raw27799step0Labels = raw27799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27799 raw27799Labels permutation346 hz
    mixedMoment B raw27799step0 raw27799step0Labels = mixedMoment B raw27799step1 raw27799step1Labels := by
      have ha : raw27799step1 = (fun i j => raw27799step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27799step1 raw27799step0; decide +kernel
      have hl : raw27799step1Labels = raw27799step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27799step0 raw27799step0Labels permutation151 permutation7
    mixedMoment B raw27799step1 raw27799step1Labels = mixedMoment B raw27799step2 raw27799step2Labels := by
      have ha : raw27799step2 = -raw27799step1 := by apply Matrix.ext; change ∀ i j, raw27799step2 i j = -(raw27799step1 i j); unfold raw27799step2 raw27799step1; decide +kernel
      have hl : raw27799step2Labels = raw27799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27799step2 raw27799step2Labels = mixedMoment B raw27799step3 raw27799step3Labels := by
      have ha : raw27799step3 = raw27799step2 := by apply Matrix.ext; unfold raw27799step3 raw27799step2; decide +kernel
      have hl : raw27799step2Labels = labelEmbedding1 ∘ raw27799step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27799step2 raw27799step2Labels raw27799step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical27800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27800 raw27800Labels = mixedMoment B node1639 node1639Labels := by
  calc
    mixedMoment B raw27800 raw27800Labels = mixedMoment B raw27800step0 raw27800step0Labels := by
      have hz : ∀ j, raw27800 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27800step0 = (fun i j => raw27800 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27800step0 raw27800; decide +kernel
      have hl : raw27800step0Labels = raw27800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27800 raw27800Labels permutation346 hz
    mixedMoment B raw27800step0 raw27800step0Labels = mixedMoment B raw27800step1 raw27800step1Labels := by
      have ha : raw27800step1 = (fun i j => raw27800step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27800step1 raw27800step0; decide +kernel
      have hl : raw27800step1Labels = raw27800step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27800step0 raw27800step0Labels permutation151 permutation7
    mixedMoment B raw27800step1 raw27800step1Labels = mixedMoment B raw27800step2 raw27800step2Labels := by
      have ha : raw27800step2 = -raw27800step1 := by apply Matrix.ext; change ∀ i j, raw27800step2 i j = -(raw27800step1 i j); unfold raw27800step2 raw27800step1; decide +kernel
      have hl : raw27800step2Labels = raw27800step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27800step2 raw27800step2Labels = mixedMoment B raw27800step3 raw27800step3Labels := by
      have ha : raw27800step3 = raw27800step2 := by apply Matrix.ext; unfold raw27800step3 raw27800step2; decide +kernel
      have hl : raw27800step2Labels = labelEmbedding1 ∘ raw27800step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27800step2 raw27800step2Labels raw27800step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1639 node1639Labels := by rfl

theorem canonical27801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27801 raw27801Labels = mixedMoment B node2136 node2136Labels := by
  calc
    mixedMoment B raw27801 raw27801Labels = mixedMoment B raw27801step0 raw27801step0Labels := by
      have hz : ∀ j, raw27801 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27801step0 = (fun i j => raw27801 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27801step0 raw27801; decide +kernel
      have hl : raw27801step0Labels = raw27801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27801 raw27801Labels permutation434 hz
    mixedMoment B raw27801step0 raw27801step0Labels = mixedMoment B raw27801step1 raw27801step1Labels := by
      have hz : ∀ j, raw27801step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27801step1 = (fun i j => raw27801step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27801step1 raw27801step0; decide +kernel
      have hl : raw27801step1Labels = raw27801step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27801step0 raw27801step0Labels permutation80 hz
    mixedMoment B raw27801step1 raw27801step1Labels = mixedMoment B raw27801step2 raw27801step2Labels := by
      have ha : raw27801step2 = (fun i j => raw27801step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27801step2 raw27801step1; decide +kernel
      have hl : raw27801step2Labels = raw27801step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27801step1 raw27801step1Labels permutation31 permutation7
    mixedMoment B raw27801step2 raw27801step2Labels = mixedMoment B raw27801step3 raw27801step3Labels := by
      have ha : raw27801step3 = -raw27801step2 := by apply Matrix.ext; change ∀ i j, raw27801step3 i j = -(raw27801step2 i j); unfold raw27801step3 raw27801step2; decide +kernel
      have hl : raw27801step3Labels = raw27801step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27801step3 raw27801step3Labels = mixedMoment B raw27801step4 raw27801step4Labels := by
      have ha : raw27801step4 = raw27801step3 := by apply Matrix.ext; unfold raw27801step4 raw27801step3; decide +kernel
      have hl : raw27801step3Labels = labelEmbedding1 ∘ raw27801step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27801step3 raw27801step3Labels raw27801step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2136 node2136Labels := by rfl

theorem canonical27802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27802 raw27802Labels = mixedMoment B node2134 node2134Labels := by
  calc
    mixedMoment B raw27802 raw27802Labels = mixedMoment B raw27802step0 raw27802step0Labels := by
      have hz : ∀ j, raw27802 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27802step0 = (fun i j => raw27802 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27802step0 raw27802; decide +kernel
      have hl : raw27802step0Labels = raw27802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27802 raw27802Labels permutation434 hz
    mixedMoment B raw27802step0 raw27802step0Labels = mixedMoment B raw27802step1 raw27802step1Labels := by
      have hz : ∀ j, raw27802step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27802step1 = (fun i j => raw27802step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27802step1 raw27802step0; decide +kernel
      have hl : raw27802step1Labels = raw27802step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27802step0 raw27802step0Labels permutation80 hz
    mixedMoment B raw27802step1 raw27802step1Labels = mixedMoment B raw27802step2 raw27802step2Labels := by
      have ha : raw27802step2 = (fun i j => raw27802step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27802step2 raw27802step1; decide +kernel
      have hl : raw27802step2Labels = raw27802step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27802step1 raw27802step1Labels permutation31 permutation7
    mixedMoment B raw27802step2 raw27802step2Labels = mixedMoment B raw27802step3 raw27802step3Labels := by
      have ha : raw27802step3 = -raw27802step2 := by apply Matrix.ext; change ∀ i j, raw27802step3 i j = -(raw27802step2 i j); unfold raw27802step3 raw27802step2; decide +kernel
      have hl : raw27802step3Labels = raw27802step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27802step3 raw27802step3Labels = mixedMoment B raw27802step4 raw27802step4Labels := by
      have ha : raw27802step4 = raw27802step3 := by apply Matrix.ext; unfold raw27802step4 raw27802step3; decide +kernel
      have hl : raw27802step3Labels = labelEmbedding1 ∘ raw27802step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27802step3 raw27802step3Labels raw27802step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2134 node2134Labels := by rfl

theorem canonical27803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27803 raw27803Labels = mixedMoment B node2121 node2121Labels := by
  calc
    mixedMoment B raw27803 raw27803Labels = mixedMoment B raw27803step0 raw27803step0Labels := by
      have hz : ∀ j, raw27803 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27803step0 = (fun i j => raw27803 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27803step0 raw27803; decide +kernel
      have hl : raw27803step0Labels = raw27803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27803 raw27803Labels permutation434 hz
    mixedMoment B raw27803step0 raw27803step0Labels = mixedMoment B raw27803step1 raw27803step1Labels := by
      have ha : raw27803step1 = (fun i j => raw27803step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27803step1 raw27803step0; decide +kernel
      have hl : raw27803step1Labels = raw27803step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27803step0 raw27803step0Labels permutation151 permutation7
    mixedMoment B raw27803step1 raw27803step1Labels = mixedMoment B raw27803step2 raw27803step2Labels := by
      have ha : raw27803step2 = -raw27803step1 := by apply Matrix.ext; change ∀ i j, raw27803step2 i j = -(raw27803step1 i j); unfold raw27803step2 raw27803step1; decide +kernel
      have hl : raw27803step2Labels = raw27803step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27803step2 raw27803step2Labels = mixedMoment B raw27803step3 raw27803step3Labels := by
      have ha : raw27803step3 = raw27803step2 := by apply Matrix.ext; unfold raw27803step3 raw27803step2; decide +kernel
      have hl : raw27803step2Labels = labelEmbedding1 ∘ raw27803step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27803step2 raw27803step2Labels raw27803step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2121 node2121Labels := by rfl

theorem canonical27804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27804 raw27804Labels = mixedMoment B node2121 node2121Labels := by
  calc
    mixedMoment B raw27804 raw27804Labels = mixedMoment B raw27804step0 raw27804step0Labels := by
      have hz : ∀ j, raw27804 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27804step0 = (fun i j => raw27804 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27804step0 raw27804; decide +kernel
      have hl : raw27804step0Labels = raw27804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27804 raw27804Labels permutation346 hz
    mixedMoment B raw27804step0 raw27804step0Labels = mixedMoment B raw27804step1 raw27804step1Labels := by
      have ha : raw27804step1 = (fun i j => raw27804step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27804step1 raw27804step0; decide +kernel
      have hl : raw27804step1Labels = raw27804step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27804step0 raw27804step0Labels permutation151 permutation7
    mixedMoment B raw27804step1 raw27804step1Labels = mixedMoment B raw27804step2 raw27804step2Labels := by
      have ha : raw27804step2 = -raw27804step1 := by apply Matrix.ext; change ∀ i j, raw27804step2 i j = -(raw27804step1 i j); unfold raw27804step2 raw27804step1; decide +kernel
      have hl : raw27804step2Labels = raw27804step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27804step2 raw27804step2Labels = mixedMoment B raw27804step3 raw27804step3Labels := by
      have ha : raw27804step3 = raw27804step2 := by apply Matrix.ext; unfold raw27804step3 raw27804step2; decide +kernel
      have hl : raw27804step2Labels = labelEmbedding1 ∘ raw27804step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27804step2 raw27804step2Labels raw27804step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2121 node2121Labels := by rfl

theorem canonical27805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27805 raw27805Labels = mixedMoment B node1659 node1659Labels := by
  calc
    mixedMoment B raw27805 raw27805Labels = mixedMoment B raw27805step0 raw27805step0Labels := by
      have hz : ∀ j, raw27805 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27805step0 = (fun i j => raw27805 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27805step0 raw27805; decide +kernel
      have hl : raw27805step0Labels = raw27805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27805 raw27805Labels permutation434 hz
    mixedMoment B raw27805step0 raw27805step0Labels = mixedMoment B raw27805step1 raw27805step1Labels := by
      have hz : ∀ j, raw27805step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27805step1 = (fun i j => raw27805step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27805step1 raw27805step0; decide +kernel
      have hl : raw27805step1Labels = raw27805step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27805step0 raw27805step0Labels permutation80 hz
    mixedMoment B raw27805step1 raw27805step1Labels = mixedMoment B raw27805step2 raw27805step2Labels := by
      have ha : raw27805step2 = (fun i j => raw27805step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27805step2 raw27805step1; decide +kernel
      have hl : raw27805step2Labels = raw27805step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27805step1 raw27805step1Labels permutation31 permutation7
    mixedMoment B raw27805step2 raw27805step2Labels = mixedMoment B raw27805step3 raw27805step3Labels := by
      have ha : raw27805step3 = -raw27805step2 := by apply Matrix.ext; change ∀ i j, raw27805step3 i j = -(raw27805step2 i j); unfold raw27805step3 raw27805step2; decide +kernel
      have hl : raw27805step3Labels = raw27805step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27805step3 raw27805step3Labels = mixedMoment B raw27805step4 raw27805step4Labels := by
      have ha : raw27805step4 = raw27805step3 := by apply Matrix.ext; unfold raw27805step4 raw27805step3; decide +kernel
      have hl : raw27805step3Labels = labelEmbedding1 ∘ raw27805step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27805step3 raw27805step3Labels raw27805step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1659 node1659Labels := by rfl

theorem canonical27806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27806 raw27806Labels = mixedMoment B node2642 node2642Labels := by
  calc
    mixedMoment B raw27806 raw27806Labels = mixedMoment B raw27806step0 raw27806step0Labels := by
      have hz : ∀ j, raw27806 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27806step0 = (fun i j => raw27806 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27806step0 raw27806; decide +kernel
      have hl : raw27806step0Labels = raw27806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27806 raw27806Labels permutation434 hz
    mixedMoment B raw27806step0 raw27806step0Labels = mixedMoment B raw27806step1 raw27806step1Labels := by
      have hz : ∀ j, raw27806step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27806step1 = (fun i j => raw27806step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27806step1 raw27806step0; decide +kernel
      have hl : raw27806step1Labels = raw27806step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27806step0 raw27806step0Labels permutation80 hz
    mixedMoment B raw27806step1 raw27806step1Labels = mixedMoment B raw27806step2 raw27806step2Labels := by
      have ha : raw27806step2 = (fun i j => raw27806step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27806step2 raw27806step1; decide +kernel
      have hl : raw27806step2Labels = raw27806step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27806step1 raw27806step1Labels permutation31 permutation7
    mixedMoment B raw27806step2 raw27806step2Labels = mixedMoment B raw27806step3 raw27806step3Labels := by
      have ha : raw27806step3 = -raw27806step2 := by apply Matrix.ext; change ∀ i j, raw27806step3 i j = -(raw27806step2 i j); unfold raw27806step3 raw27806step2; decide +kernel
      have hl : raw27806step3Labels = raw27806step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27806step3 raw27806step3Labels = mixedMoment B raw27806step4 raw27806step4Labels := by
      have ha : raw27806step4 = raw27806step3 := by apply Matrix.ext; unfold raw27806step4 raw27806step3; decide +kernel
      have hl : raw27806step3Labels = labelEmbedding1 ∘ raw27806step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27806step3 raw27806step3Labels raw27806step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2642 node2642Labels := by rfl

theorem canonical27807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27807 raw27807Labels = mixedMoment B node2640 node2640Labels := by
  calc
    mixedMoment B raw27807 raw27807Labels = mixedMoment B raw27807step0 raw27807step0Labels := by
      have hz : ∀ j, raw27807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27807step0 = (fun i j => raw27807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27807step0 raw27807; decide +kernel
      have hl : raw27807step0Labels = raw27807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27807 raw27807Labels permutation434 hz
    mixedMoment B raw27807step0 raw27807step0Labels = mixedMoment B raw27807step1 raw27807step1Labels := by
      have hz : ∀ j, raw27807step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27807step1 = (fun i j => raw27807step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27807step1 raw27807step0; decide +kernel
      have hl : raw27807step1Labels = raw27807step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27807step0 raw27807step0Labels permutation80 hz
    mixedMoment B raw27807step1 raw27807step1Labels = mixedMoment B raw27807step2 raw27807step2Labels := by
      have ha : raw27807step2 = (fun i j => raw27807step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27807step2 raw27807step1; decide +kernel
      have hl : raw27807step2Labels = raw27807step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27807step1 raw27807step1Labels permutation31 permutation7
    mixedMoment B raw27807step2 raw27807step2Labels = mixedMoment B raw27807step3 raw27807step3Labels := by
      have ha : raw27807step3 = -raw27807step2 := by apply Matrix.ext; change ∀ i j, raw27807step3 i j = -(raw27807step2 i j); unfold raw27807step3 raw27807step2; decide +kernel
      have hl : raw27807step3Labels = raw27807step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27807step3 raw27807step3Labels = mixedMoment B raw27807step4 raw27807step4Labels := by
      have ha : raw27807step4 = raw27807step3 := by apply Matrix.ext; unfold raw27807step4 raw27807step3; decide +kernel
      have hl : raw27807step3Labels = labelEmbedding1 ∘ raw27807step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27807step3 raw27807step3Labels raw27807step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2640 node2640Labels := by rfl

theorem canonical27808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27808 raw27808Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw27808 raw27808Labels = mixedMoment B raw27808step0 raw27808step0Labels := by
      have hz : ∀ j, raw27808 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27808step0 = (fun i j => raw27808 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27808step0 raw27808; decide +kernel
      have hl : raw27808step0Labels = raw27808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27808 raw27808Labels permutation434 hz
    mixedMoment B raw27808step0 raw27808step0Labels = mixedMoment B raw27808step1 raw27808step1Labels := by
      have ha : raw27808step1 = (fun i j => raw27808step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27808step1 raw27808step0; decide +kernel
      have hl : raw27808step1Labels = raw27808step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27808step0 raw27808step0Labels permutation151 permutation7
    mixedMoment B raw27808step1 raw27808step1Labels = mixedMoment B raw27808step2 raw27808step2Labels := by
      have ha : raw27808step2 = -raw27808step1 := by apply Matrix.ext; change ∀ i j, raw27808step2 i j = -(raw27808step1 i j); unfold raw27808step2 raw27808step1; decide +kernel
      have hl : raw27808step2Labels = raw27808step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27808step2 raw27808step2Labels = mixedMoment B raw27808step3 raw27808step3Labels := by
      have ha : raw27808step3 = raw27808step2 := by apply Matrix.ext; unfold raw27808step3 raw27808step2; decide +kernel
      have hl : raw27808step2Labels = labelEmbedding1 ∘ raw27808step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27808step2 raw27808step2Labels raw27808step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2618 node2618Labels := by rfl

theorem canonical27809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27809 raw27809Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw27809 raw27809Labels = mixedMoment B raw27809step0 raw27809step0Labels := by
      have hz : ∀ j, raw27809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27809step0 = (fun i j => raw27809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27809step0 raw27809; decide +kernel
      have hl : raw27809step0Labels = raw27809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27809 raw27809Labels permutation346 hz
    mixedMoment B raw27809step0 raw27809step0Labels = mixedMoment B raw27809step1 raw27809step1Labels := by
      have ha : raw27809step1 = (fun i j => raw27809step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27809step1 raw27809step0; decide +kernel
      have hl : raw27809step1Labels = raw27809step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27809step0 raw27809step0Labels permutation151 permutation7
    mixedMoment B raw27809step1 raw27809step1Labels = mixedMoment B raw27809step2 raw27809step2Labels := by
      have ha : raw27809step2 = -raw27809step1 := by apply Matrix.ext; change ∀ i j, raw27809step2 i j = -(raw27809step1 i j); unfold raw27809step2 raw27809step1; decide +kernel
      have hl : raw27809step2Labels = raw27809step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27809step2 raw27809step2Labels = mixedMoment B raw27809step3 raw27809step3Labels := by
      have ha : raw27809step3 = raw27809step2 := by apply Matrix.ext; unfold raw27809step3 raw27809step2; decide +kernel
      have hl : raw27809step2Labels = labelEmbedding1 ∘ raw27809step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27809step2 raw27809step2Labels raw27809step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2618 node2618Labels := by rfl

theorem canonical27810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27810 raw27810Labels = mixedMoment B node2601 node2601Labels := by
  calc
    mixedMoment B raw27810 raw27810Labels = mixedMoment B raw27810step0 raw27810step0Labels := by
      have hz : ∀ j, raw27810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27810step0 = (fun i j => raw27810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27810step0 raw27810; decide +kernel
      have hl : raw27810step0Labels = raw27810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27810 raw27810Labels permutation434 hz
    mixedMoment B raw27810step0 raw27810step0Labels = mixedMoment B raw27810step1 raw27810step1Labels := by
      have hz : ∀ j, raw27810step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27810step1 = (fun i j => raw27810step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27810step1 raw27810step0; decide +kernel
      have hl : raw27810step1Labels = raw27810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27810step0 raw27810step0Labels permutation80 hz
    mixedMoment B raw27810step1 raw27810step1Labels = mixedMoment B raw27810step2 raw27810step2Labels := by
      have ha : raw27810step2 = (fun i j => raw27810step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27810step2 raw27810step1; decide +kernel
      have hl : raw27810step2Labels = raw27810step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27810step1 raw27810step1Labels permutation31 permutation7
    mixedMoment B raw27810step2 raw27810step2Labels = mixedMoment B raw27810step3 raw27810step3Labels := by
      have ha : raw27810step3 = -raw27810step2 := by apply Matrix.ext; change ∀ i j, raw27810step3 i j = -(raw27810step2 i j); unfold raw27810step3 raw27810step2; decide +kernel
      have hl : raw27810step3Labels = raw27810step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27810step3 raw27810step3Labels = mixedMoment B raw27810step4 raw27810step4Labels := by
      have ha : raw27810step4 = raw27810step3 := by apply Matrix.ext; unfold raw27810step4 raw27810step3; decide +kernel
      have hl : raw27810step3Labels = labelEmbedding1 ∘ raw27810step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27810step3 raw27810step3Labels raw27810step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2601 node2601Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical441 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw441 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw441 = injectiveMoment H raw441step0 := by
      have heq : raw441step0 = (fun i j => raw441 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw441 permutation28 permutation6
    _ = injectiveMoment H node187 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw841 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw841 = injectiveMoment H raw841step0 := by
      have heq : raw841step0 = raw841.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw841).symm
    injectiveMoment H raw841step0 = injectiveMoment H raw841step1 := by
      have heq : raw841step1 = (fun i j => raw841step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw841step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

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

theorem canonical869 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw869 = injectiveMoment H node24 := by
  rfl

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

theorem canonical898 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw898 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw898 = injectiveMoment H raw898step0 := by
      have hz : ∀ j, raw898 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw898step0 = (fun i j => raw898 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw898 permutation15 hz
    injectiveMoment H raw898step0 = injectiveMoment H raw898step1 := by
      have heq : raw898step1 = (fun i j => raw898step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw898step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

theorem canonical900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw900 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw900 = injectiveMoment H raw900step0 := by
      have hz : ∀ j, raw900 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw900step0 = (fun i j => raw900 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw900 permutation5 hz
    _ = injectiveMoment H node3 := by rfl

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

theorem canonical5199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5199 = injectiveMoment H node11 := by
  rfl

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

end MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw180 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw180 = injectiveMoment H raw180step0 := by
      have heq : raw180step0 = raw180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw180).symm
    _ = injectiveMoment H node9 := by rfl

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

theorem canonical211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw211 = injectiveMoment H node8 := by
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

theorem sound24 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node24 = Sparse.eval value24 (momentVector H) := by
  have heq : pivotMatrix24 = (fun u v => node24 (pivotPermutation24 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node24 = injectiveMoment H pivotMatrix24 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix24 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix24 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix24 (0 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix24 (0 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix24 (1 : Fin 3)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix24 (1 : Fin 3) = raw900 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical900 hH).trans (sound3 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix24 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix24 (2 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node24 + (injectiveMoment H (mergeFirst pivotMatrix24 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix24 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix24 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value24, value10, value3, value8, Sparse.eval] at hc ⊢
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

theorem sound52 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node52 = Sparse.eval value52 (momentVector H) := by
  have heq : pivotMatrix52 = (fun u v => node52.transpose (pivotPermutation52 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node52 = injectiveMoment H pivotMatrix52 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix52 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix52 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (0 : Fin 2) = raw180 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical180 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (1 : Fin 2) = raw841 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical841 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node52 + (injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value52, value10, value9, Sparse.eval] at hc ⊢
  linarith

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7705 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7705 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7705 = injectiveMoment H raw7705step0 := by
      have hz : ∀ j, raw7705 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw7705step0 = (fun i j => raw7705 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7705 permutation15 hz
    injectiveMoment H raw7705step0 = injectiveMoment H raw7705step1 := by
      have heq : raw7705step1 = (fun i j => raw7705step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7705step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1447 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1447 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1447 = injectiveMoment H raw1447step0 := by
      have heq : raw1447step0 = raw1447.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1447).symm
    injectiveMoment H raw1447step0 = injectiveMoment H raw1447step1 := by
      have heq : raw1447step1 = (fun i j => raw1447step0 (permutation8 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1447step0 permutation8 permutation6
    _ = injectiveMoment H node52 := by rfl

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

theorem canonical2865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2865 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw2865 = injectiveMoment H raw2865step0 := by
      have heq : raw2865step0 = (fun i j => raw2865 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2865 permutation4 permutation3
    _ = injectiveMoment H node40 := by rfl

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

theorem canonical6870 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6870 = injectiveMoment H node63 := by
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

theorem sound174 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node174 = Sparse.eval value174 (momentVector H) := by
  have heq : pivotMatrix174 = (fun u v => node174 (pivotPermutation174 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node174 = injectiveMoment H pivotMatrix174 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix174 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix174 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix174 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix174 (0 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix174 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix174 (1 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix174 (2 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix174 (2 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node174 + (injectiveMoment H (mergeFirst pivotMatrix174 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix174 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix174 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value174, value52, value56, value63, Sparse.eval] at hc ⊢
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

theorem sound187 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node187 = Sparse.eval value187 (momentVector H) := by
  have heq : pivotMatrix187 = (fun u v => node187 (pivotPermutation187 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node187 = injectiveMoment H pivotMatrix187 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix187 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix187 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix187 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix187 (0 : Fin 3) = raw6870 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6870 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix187 (1 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix187 (1 : Fin 3) = raw2865 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2865 hH).trans (sound40 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix187 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix187 (2 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node187 + (injectiveMoment H (mergeFirst pivotMatrix187 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix187 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix187 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value187, value37, value40, value63, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical5149 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5149 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5149 = injectiveMoment H raw5149step0 := by
      have heq : raw5149step0 = (fun i j => raw5149 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5149 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair236 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node236 node236Labels = Sparse.eval singlePairValue236 (familyPairVector B) := by
  have hp := single_label_three B hB node236
  have hl : node236Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node236 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node236 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node236 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node236 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node236 (EqualityPatterns.family3.label 1) = PairSemantics.raw898 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node236 PairSemantics.raw898; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical898 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node236 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node236 (EqualityPatterns.family3.label 2) = PairSemantics.raw9013 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node236 PairSemantics.raw9013; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9013 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node236 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node236 (EqualityPatterns.family3.label 3) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node236 PairSemantics.raw869; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node236 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value187 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node236 (EqualityPatterns.family3.label 4) = PairSemantics.raw441 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node236 PairSemantics.raw441; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical441 hH).trans (PairSemantics.sound187 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue236, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value24, PairSemantics.value187, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical641 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw641 = injectiveMoment H node180 := by
  calc
    injectiveMoment H raw641 = injectiveMoment H raw641step0 := by
      have heq : raw641step0 = (fun i j => raw641 (permutation30 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw641 permutation30 permutation6
    _ = injectiveMoment H node180 := by rfl

theorem canonical669 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw669 = injectiveMoment H node174 := by
  calc
    injectiveMoment H raw669 = injectiveMoment H raw669step0 := by
      have heq : raw669step0 = (fun i j => raw669 (permutation32 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw669 permutation32 permutation6
    _ = injectiveMoment H node174 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair315 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node315 node315Labels = Sparse.eval singlePairValue315 (familyPairVector B) := by
  have hp := single_label_three B hB node315
  have hl : node315Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node315 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node315 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node315 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node315 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node315 (EqualityPatterns.family3.label 1) = PairSemantics.raw5149 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node315 PairSemantics.raw5149; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5149 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node315 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node315 (EqualityPatterns.family3.label 2) = PairSemantics.raw7705 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node315 PairSemantics.raw7705; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7705 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node315 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node315 (EqualityPatterns.family3.label 3) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node315 PairSemantics.raw869; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node315 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value180 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node315 (EqualityPatterns.family3.label 4) = PairSemantics.raw641 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node315 PairSemantics.raw641; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical641 hH).trans (PairSemantics.sound180 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue315, PairSemantics.value0, PairSemantics.value11, PairSemantics.value24, PairSemantics.value46, PairSemantics.value180, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node341 node341Labels = Sparse.eval singlePairValue341 (familyPairVector B) := by
  have hp := single_label_three B hB node341
  have hl : node341Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node341 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node341 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node341 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node341 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node341 (EqualityPatterns.family3.label 1) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node341 PairSemantics.raw5177; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node341 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node341 (EqualityPatterns.family3.label 2) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node341 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node341 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node341 (EqualityPatterns.family3.label 3) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node341 PairSemantics.raw869; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node341 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value174 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node341 (EqualityPatterns.family3.label 4) = PairSemantics.raw669 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node341 PairSemantics.raw669; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical669 hH).trans (PairSemantics.sound174 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue341, PairSemantics.value0, PairSemantics.value11, PairSemantics.value24, PairSemantics.value174, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton2601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2601 node2601Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node341 node341Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw242 singletonSmall2601
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2601) = raw242Labels := by decide +kernel
  rw [hl, canonical242 B hB] at h
  have hc0 : mixedMoment B raw242 (Fin.cases (0 : Fin 1) singletonSmall2601) =
      mixedMoment B node341 node341Labels := by
    have ha : raw242 = raw243 := by apply Matrix.ext; unfold raw242 raw243; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2601 = raw243Labels := by decide +kernel
    rw [ha, hj, canonical243 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem singleton2640 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2640 node2640Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node315 node315Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw258 singletonSmall2640
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2640) = raw258Labels := by decide +kernel
  rw [hl, canonical258 B hB] at h
  have hc0 : mixedMoment B raw258 (Fin.cases (0 : Fin 1) singletonSmall2640) =
      mixedMoment B node315 node315Labels := by
    have ha : raw258 = raw259 := by apply Matrix.ext; unfold raw258 raw259; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2640 = raw259Labels := by decide +kernel
    rw [ha, hj, canonical259 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton2642 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2642 node2642Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node236 node236Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw260 singletonSmall2642
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2642) = raw260Labels := by decide +kernel
  rw [hl, canonical260 B hB] at h
  have hc0 : mixedMoment B raw260 (Fin.cases (0 : Fin 1) singletonSmall2642) =
      mixedMoment B node236 node236Labels := by
    have ha : raw260 = raw261 := by apply Matrix.ext; unfold raw260 raw261; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2642 = raw261Labels := by decide +kernel
    rw [ha, hj, canonical261 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem sound1639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1639 node1639Labels = Sparse.eval nodeValue1639 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1639) = mixedMoment B node1639 node1639Labels := rfl
  simpa [nodeValue1639, Sparse.eval] using hc.symm

theorem sound1650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1650 node1650Labels = Sparse.eval nodeValue1650 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1650) = mixedMoment B node1650 node1650Labels := rfl
  simpa [nodeValue1650, Sparse.eval] using hc.symm

theorem sound1651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1651 node1651Labels = Sparse.eval nodeValue1651 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1651) = mixedMoment B node1651 node1651Labels := rfl
  simpa [nodeValue1651, Sparse.eval] using hc.symm

theorem sound1659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1659 node1659Labels = Sparse.eval nodeValue1659 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1659) = mixedMoment B node1659 node1659Labels := rfl
  simpa [nodeValue1659, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node236 node236Labels = Sparse.eval nodeValue236 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue236 (familyPairVector B) := singlePair236 B _hB
    _ = _ := by norm_num [singlePairValue236, nodeValue236, Sparse.eval, mixedVector] <;> ring

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

theorem sound2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2025 node2025Labels = Sparse.eval nodeValue2025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2025) = mixedMoment B node2025 node2025Labels := rfl
  simpa [nodeValue2025, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2060 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2060 node2060Labels = 0 := by
  exact mixedMoment_order_one B hB node2060 node2060Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2060 node2060Labels = Sparse.eval nodeValue2060 (mixedVector B) := by
  simpa only [nodeValue2060, Sparse.eval_nil] using zero2060 B _hB _hF

theorem sound2062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2062 node2062Labels = Sparse.eval nodeValue2062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2062) = mixedMoment B node2062 node2062Labels := rfl
  simpa [nodeValue2062, Sparse.eval] using hc.symm

theorem sound2071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2071 node2071Labels = Sparse.eval nodeValue2071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2071) = mixedMoment B node2071 node2071Labels := rfl
  simpa [nodeValue2071, Sparse.eval] using hc.symm

theorem sound2079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2079 node2079Labels = Sparse.eval nodeValue2079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2079) = mixedMoment B node2079 node2079Labels := rfl
  simpa [nodeValue2079, Sparse.eval] using hc.symm

theorem sound2080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2080 node2080Labels = Sparse.eval nodeValue2080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2080) = mixedMoment B node2080 node2080Labels := rfl
  simpa [nodeValue2080, Sparse.eval] using hc.symm

theorem sound2090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2090 node2090Labels = Sparse.eval nodeValue2090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2090) = mixedMoment B node2090 node2090Labels := rfl
  simpa [nodeValue2090, Sparse.eval] using hc.symm

theorem sound2092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2092 node2092Labels = Sparse.eval nodeValue2092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2092) = mixedMoment B node2092 node2092Labels := rfl
  simpa [nodeValue2092, Sparse.eval] using hc.symm

theorem sound2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2109 node2109Labels = Sparse.eval nodeValue2109 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2109) = mixedMoment B node2109 node2109Labels := rfl
  simpa [nodeValue2109, Sparse.eval] using hc.symm

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

theorem sound2113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2113 node2113Labels = Sparse.eval nodeValue2113 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2113) = mixedMoment B node2113 node2113Labels := rfl
  simpa [nodeValue2113, Sparse.eval] using hc.symm

theorem sound2121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2121 node2121Labels = Sparse.eval nodeValue2121 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2121) = mixedMoment B node2121 node2121Labels := rfl
  simpa [nodeValue2121, Sparse.eval] using hc.symm

theorem sound2134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2134 node2134Labels = Sparse.eval nodeValue2134 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2134) = mixedMoment B node2134 node2134Labels := rfl
  simpa [nodeValue2134, Sparse.eval] using hc.symm

theorem sound2136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2136 node2136Labels = Sparse.eval nodeValue2136 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2136) = mixedMoment B node2136 node2136Labels := rfl
  simpa [nodeValue2136, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node315 node315Labels = Sparse.eval nodeValue315 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue315 (familyPairVector B) := singlePair315 B _hB
    _ = _ := by norm_num [singlePairValue315, nodeValue315, Sparse.eval, mixedVector] <;> ring

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

theorem sound341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node341 node341Labels = Sparse.eval nodeValue341 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue341 (familyPairVector B) := singlePair341 B _hB
    _ = _ := by norm_num [singlePairValue341, nodeValue341, Sparse.eval, mixedVector] <;> ring

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

theorem sound2601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2601 node2601Labels = Sparse.eval nodeValue2601 (mixedVector B) := by
  have h := singleton2601 B _hB
  rw [sound341 B _hB _hF] at h
  norm_num [nodeValue2601, nodeValue341, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2618 node2618Labels = Sparse.eval nodeValue2618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2618) = mixedMoment B node2618 node2618Labels := rfl
  simpa [nodeValue2618, Sparse.eval] using hc.symm

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

theorem sound2640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2640 node2640Labels = Sparse.eval nodeValue2640 (mixedVector B) := by
  have h := singleton2640 B _hB
  rw [sound315 B _hB _hF] at h
  norm_num [nodeValue2640, nodeValue315, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2642 node2642Labels = Sparse.eval nodeValue2642 (mixedVector B) := by
  have h := singleton2642 B _hB
  rw [sound236 B _hB _hF] at h
  norm_num [nodeValue2642, nodeValue236, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources61
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1957 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1957 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1957 + difference 0 1) (sourceB1957 + difference 1 0) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA1957 + difference 0 1) (sourceB1957 + difference 1 0) sourceC1957) = raw27781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27781; decide +kernel
    rw [ha]
    exact (canonical27781 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1957 + difference 0 2) (sourceB1957 + difference 2 0) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA1957 + difference 0 2) (sourceB1957 + difference 2 0) sourceC1957) = raw27782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27782; decide +kernel
    rw [ha]
    exact (canonical27782 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1957 + difference 0 3) (sourceB1957 + difference 3 0) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA1957 + difference 0 3) (sourceB1957 + difference 3 0) sourceC1957) = raw27783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27783; decide +kernel
    rw [ha]
    exact (canonical27783 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1957 + difference 0 4) (sourceB1957 + difference 4 0) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2060) := by
    have ha : (tripleCharges (sourceA1957 + difference 0 4) (sourceB1957 + difference 4 0) sourceC1957) = raw27784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27784; decide +kernel
    rw [ha]
    exact (canonical27784 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1957 + difference 0 5) (sourceB1957 + difference 5 0) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1650) := by
    have ha : (tripleCharges (sourceA1957 + difference 0 5) (sourceB1957 + difference 5 0) sourceC1957) = raw27785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27785; decide +kernel
    rw [ha]
    exact (canonical27785 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1957 + difference 1 0) (sourceB1957 + difference 0 1) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA1957 + difference 1 0) (sourceB1957 + difference 0 1) sourceC1957) = raw27786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27786; decide +kernel
    rw [ha]
    exact (canonical27786 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1957 + difference 1 2) (sourceB1957 + difference 2 1) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2080) := by
    have ha : (tripleCharges (sourceA1957 + difference 1 2) (sourceB1957 + difference 2 1) sourceC1957) = raw27787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27787; decide +kernel
    rw [ha]
    exact (canonical27787 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1957 + difference 1 3) (sourceB1957 + difference 3 1) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2080) := by
    have ha : (tripleCharges (sourceA1957 + difference 1 3) (sourceB1957 + difference 3 1) sourceC1957) = raw27788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27788; decide +kernel
    rw [ha]
    exact (canonical27788 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1957 + difference 1 4) (sourceB1957 + difference 4 1) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA1957 + difference 1 4) (sourceB1957 + difference 4 1) sourceC1957) = raw27789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27789; decide +kernel
    rw [ha]
    exact (canonical27789 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1957 + difference 1 5) (sourceB1957 + difference 5 1) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1651) := by
    have ha : (tripleCharges (sourceA1957 + difference 1 5) (sourceB1957 + difference 5 1) sourceC1957) = raw27790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27790; decide +kernel
    rw [ha]
    exact (canonical27790 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1957 + difference 2 0) (sourceB1957 + difference 0 2) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA1957 + difference 2 0) (sourceB1957 + difference 0 2) sourceC1957) = raw27791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27791; decide +kernel
    rw [ha]
    exact (canonical27791 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1957 + difference 2 1) (sourceB1957 + difference 1 2) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA1957 + difference 2 1) (sourceB1957 + difference 1 2) sourceC1957) = raw27792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27792; decide +kernel
    rw [ha]
    exact (canonical27792 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1957 + difference 2 3) (sourceB1957 + difference 3 2) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2071) := by
    have ha : (tripleCharges (sourceA1957 + difference 2 3) (sourceB1957 + difference 3 2) sourceC1957) = raw27793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27793; decide +kernel
    rw [ha]
    exact (canonical27793 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1957 + difference 2 4) (sourceB1957 + difference 4 2) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1957 + difference 2 4) (sourceB1957 + difference 4 2) sourceC1957) = raw27794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27794; decide +kernel
    rw [ha]
    exact (canonical27794 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1957 + difference 2 5) (sourceB1957 + difference 5 2) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1639) := by
    have ha : (tripleCharges (sourceA1957 + difference 2 5) (sourceB1957 + difference 5 2) sourceC1957) = raw27795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27795; decide +kernel
    rw [ha]
    exact (canonical27795 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1957 + difference 3 0) (sourceB1957 + difference 0 3) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA1957 + difference 3 0) (sourceB1957 + difference 0 3) sourceC1957) = raw27796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27796; decide +kernel
    rw [ha]
    exact (canonical27796 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1957 + difference 3 1) (sourceB1957 + difference 1 3) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA1957 + difference 3 1) (sourceB1957 + difference 1 3) sourceC1957) = raw27797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27797; decide +kernel
    rw [ha]
    exact (canonical27797 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1957 + difference 3 2) (sourceB1957 + difference 2 3) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2071) := by
    have ha : (tripleCharges (sourceA1957 + difference 3 2) (sourceB1957 + difference 2 3) sourceC1957) = raw27798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27798; decide +kernel
    rw [ha]
    exact (canonical27798 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1957 + difference 3 4) (sourceB1957 + difference 4 3) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1957 + difference 3 4) (sourceB1957 + difference 4 3) sourceC1957) = raw27799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27799; decide +kernel
    rw [ha]
    exact (canonical27799 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1957 + difference 3 5) (sourceB1957 + difference 5 3) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1639) := by
    have ha : (tripleCharges (sourceA1957 + difference 3 5) (sourceB1957 + difference 5 3) sourceC1957) = raw27800 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27800; decide +kernel
    rw [ha]
    exact (canonical27800 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1957 + difference 4 0) (sourceB1957 + difference 0 4) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA1957 + difference 4 0) (sourceB1957 + difference 0 4) sourceC1957) = raw27801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27801; decide +kernel
    rw [ha]
    exact (canonical27801 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1957 + difference 4 1) (sourceB1957 + difference 1 4) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2134) := by
    have ha : (tripleCharges (sourceA1957 + difference 4 1) (sourceB1957 + difference 1 4) sourceC1957) = raw27802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27802; decide +kernel
    rw [ha]
    exact (canonical27802 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1957 + difference 4 2) (sourceB1957 + difference 2 4) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2121) := by
    have ha : (tripleCharges (sourceA1957 + difference 4 2) (sourceB1957 + difference 2 4) sourceC1957) = raw27803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27803; decide +kernel
    rw [ha]
    exact (canonical27803 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1957 + difference 4 3) (sourceB1957 + difference 3 4) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2121) := by
    have ha : (tripleCharges (sourceA1957 + difference 4 3) (sourceB1957 + difference 3 4) sourceC1957) = raw27804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27804; decide +kernel
    rw [ha]
    exact (canonical27804 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1957 + difference 4 5) (sourceB1957 + difference 5 4) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1659) := by
    have ha : (tripleCharges (sourceA1957 + difference 4 5) (sourceB1957 + difference 5 4) sourceC1957) = raw27805 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27805; decide +kernel
    rw [ha]
    exact (canonical27805 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1957 + difference 5 0) (sourceB1957 + difference 0 5) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2642) := by
    have ha : (tripleCharges (sourceA1957 + difference 5 0) (sourceB1957 + difference 0 5) sourceC1957) = raw27806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27806; decide +kernel
    rw [ha]
    exact (canonical27806 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1957 + difference 5 1) (sourceB1957 + difference 1 5) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2640) := by
    have ha : (tripleCharges (sourceA1957 + difference 5 1) (sourceB1957 + difference 1 5) sourceC1957) = raw27807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27807; decide +kernel
    rw [ha]
    exact (canonical27807 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1957 + difference 5 2) (sourceB1957 + difference 2 5) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA1957 + difference 5 2) (sourceB1957 + difference 2 5) sourceC1957) = raw27808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27808; decide +kernel
    rw [ha]
    exact (canonical27808 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1957 + difference 5 3) (sourceB1957 + difference 3 5) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA1957 + difference 5 3) (sourceB1957 + difference 3 5) sourceC1957) = raw27809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27809; decide +kernel
    rw [ha]
    exact (canonical27809 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1957 + difference 5 4) (sourceB1957 + difference 4 5) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA1957 + difference 5 4) (sourceB1957 + difference 4 5) sourceC1957) = raw27810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27810; decide +kernel
    rw [ha]
    exact (canonical27810 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1957 sourceB1957 sourceC1957
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1957, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1662 : Integer.Sparse.reindex keyMap MixedData.row1662 = numericRow1662 := by decide +kernel

theorem numericCheck1662 (x : Master → ℝ) : Integer.Sparse.eval numericRow1662 x =
    (4320 : ℝ) * reducedSource1662 x := by
  norm_num [numericRow1662, reducedSource1662, Integer.Sparse.eval, Sparse.eval, nodeValue1639, nodeValue1650, nodeValue1651, nodeValue1659, nodeValue2025, nodeValue2060, nodeValue2062, nodeValue2071, nodeValue2079, nodeValue2080, nodeValue2090, nodeValue2092, nodeValue2109, nodeValue2113, nodeValue2121, nodeValue2134, nodeValue2136, nodeValue2601, nodeValue2618, nodeValue2640, nodeValue2642]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1662 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1662 (mixedVector B) = 0 := by
  have h1639 : mixedVector B (Sum.inr 1639) = Sparse.eval nodeValue1639 (mixedVector B) := by
    change mixedMoment B node1639 node1639Labels = _
    exact sound1639 B hB hF
  have h1650 : mixedVector B (Sum.inr 1650) = Sparse.eval nodeValue1650 (mixedVector B) := by
    change mixedMoment B node1650 node1650Labels = _
    exact sound1650 B hB hF
  have h1651 : mixedVector B (Sum.inr 1651) = Sparse.eval nodeValue1651 (mixedVector B) := by
    change mixedMoment B node1651 node1651Labels = _
    exact sound1651 B hB hF
  have h1659 : mixedVector B (Sum.inr 1659) = Sparse.eval nodeValue1659 (mixedVector B) := by
    change mixedMoment B node1659 node1659Labels = _
    exact sound1659 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2060 : mixedVector B (Sum.inr 2060) = Sparse.eval nodeValue2060 (mixedVector B) := by
    change mixedMoment B node2060 node2060Labels = _
    exact sound2060 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h2071 : mixedVector B (Sum.inr 2071) = Sparse.eval nodeValue2071 (mixedVector B) := by
    change mixedMoment B node2071 node2071Labels = _
    exact sound2071 B hB hF
  have h2079 : mixedVector B (Sum.inr 2079) = Sparse.eval nodeValue2079 (mixedVector B) := by
    change mixedMoment B node2079 node2079Labels = _
    exact sound2079 B hB hF
  have h2080 : mixedVector B (Sum.inr 2080) = Sparse.eval nodeValue2080 (mixedVector B) := by
    change mixedMoment B node2080 node2080Labels = _
    exact sound2080 B hB hF
  have h2090 : mixedVector B (Sum.inr 2090) = Sparse.eval nodeValue2090 (mixedVector B) := by
    change mixedMoment B node2090 node2090Labels = _
    exact sound2090 B hB hF
  have h2092 : mixedVector B (Sum.inr 2092) = Sparse.eval nodeValue2092 (mixedVector B) := by
    change mixedMoment B node2092 node2092Labels = _
    exact sound2092 B hB hF
  have h2109 : mixedVector B (Sum.inr 2109) = Sparse.eval nodeValue2109 (mixedVector B) := by
    change mixedMoment B node2109 node2109Labels = _
    exact sound2109 B hB hF
  have h2113 : mixedVector B (Sum.inr 2113) = Sparse.eval nodeValue2113 (mixedVector B) := by
    change mixedMoment B node2113 node2113Labels = _
    exact sound2113 B hB hF
  have h2121 : mixedVector B (Sum.inr 2121) = Sparse.eval nodeValue2121 (mixedVector B) := by
    change mixedMoment B node2121 node2121Labels = _
    exact sound2121 B hB hF
  have h2134 : mixedVector B (Sum.inr 2134) = Sparse.eval nodeValue2134 (mixedVector B) := by
    change mixedMoment B node2134 node2134Labels = _
    exact sound2134 B hB hF
  have h2136 : mixedVector B (Sum.inr 2136) = Sparse.eval nodeValue2136 (mixedVector B) := by
    change mixedMoment B node2136 node2136Labels = _
    exact sound2136 B hB hF
  have h2601 : mixedVector B (Sum.inr 2601) = Sparse.eval nodeValue2601 (mixedVector B) := by
    change mixedMoment B node2601 node2601Labels = _
    exact sound2601 B hB hF
  have h2618 : mixedVector B (Sum.inr 2618) = Sparse.eval nodeValue2618 (mixedVector B) := by
    change mixedMoment B node2618 node2618Labels = _
    exact sound2618 B hB hF
  have h2640 : mixedVector B (Sum.inr 2640) = Sparse.eval nodeValue2640 (mixedVector B) := by
    change mixedMoment B node2640 node2640Labels = _
    exact sound2640 B hB hF
  have h2642 : mixedVector B (Sum.inr 2642) = Sparse.eval nodeValue2642 (mixedVector B) := by
    change mixedMoment B node2642 node2642Labels = _
    exact sound2642 B hB hF
  simpa only [sourceForm1957, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1639, h1650, h1651, h1659, h2025, h2060, h2062, h2071, h2079, h2080, h2090, h2092, h2109, h2113, h2121, h2134, h2136, h2601, h2618, h2640, h2642, reducedSource1662] using sourceEq1957 B hB

theorem rowSound1662_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1662 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1662, numericCheck1662, reducedZero1662 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e_oai
