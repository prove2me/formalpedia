-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:50:02.055327+00:00
-- url     : https://prove2.me/submissions/788035f1-0ee5-4e2c-84d2-da9e7fd41d07

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
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

theorem canonical2400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2400 raw2400Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw2400 raw2400Labels = mixedMoment B raw2400step0 raw2400step0Labels := by
      have ha : raw2400step0 = (fun i j => raw2400 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2400step0 raw2400; decide +kernel
      have hl : raw2400step0Labels = raw2400Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2400 raw2400Labels permutation32 permutation4
    mixedMoment B raw2400step0 raw2400step0Labels = mixedMoment B raw2400step1 raw2400step1Labels := by
      have ha : raw2400step1 = raw2400step0 := by apply Matrix.ext; unfold raw2400step1 raw2400step0; decide +kernel
      have hl : raw2400step0Labels = labelEmbedding7 ∘ raw2400step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2400step0 raw2400step0Labels raw2400step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical2401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2401 raw2401Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw2401 raw2401Labels = mixedMoment B raw2401step0 raw2401step0Labels := by
      have ha : raw2401step0 = (fun i j => raw2401 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2401step0 raw2401; decide +kernel
      have hl : raw2401step0Labels = raw2401Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2401 raw2401Labels permutation32 permutation4
    _ = mixedMoment B node3693 node3693Labels := by rfl

theorem canonical2402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2402 raw2402Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw2402 raw2402Labels = mixedMoment B raw2402step0 raw2402step0Labels := by
      have ha : raw2402step0 = (fun i j => raw2402 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2402step0 raw2402; decide +kernel
      have hl : raw2402step0Labels = raw2402Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2402 raw2402Labels permutation34 permutation6
    mixedMoment B raw2402step0 raw2402step0Labels = mixedMoment B raw2402step1 raw2402step1Labels := by
      have ha : raw2402step1 = -raw2402step0 := by apply Matrix.ext; change ∀ i j, raw2402step1 i j = -(raw2402step0 i j); unfold raw2402step1 raw2402step0; decide +kernel
      have hl : raw2402step1Labels = raw2402step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2402step1 raw2402step1Labels = mixedMoment B raw2402step2 raw2402step2Labels := by
      have ha : raw2402step2 = raw2402step1 := by apply Matrix.ext; unfold raw2402step2 raw2402step1; decide +kernel
      have hl : raw2402step1Labels = labelEmbedding1 ∘ raw2402step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2402step1 raw2402step1Labels raw2402step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

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

theorem canonical2454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2454 raw2454Labels = mixedMoment B node5390 node5390Labels := by
  calc
    mixedMoment B raw2454 raw2454Labels = mixedMoment B raw2454step0 raw2454step0Labels := by
      have ha : raw2454step0 = (fun i j => raw2454 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2454step0 raw2454; decide +kernel
      have hl : raw2454step0Labels = raw2454Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2454 raw2454Labels permutation8 permutation4
    mixedMoment B raw2454step0 raw2454step0Labels = mixedMoment B raw2454step1 raw2454step1Labels := by
      have ha : raw2454step1 = raw2454step0 := by apply Matrix.ext; unfold raw2454step1 raw2454step0; decide +kernel
      have hl : raw2454step0Labels = labelEmbedding7 ∘ raw2454step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2454step0 raw2454step0Labels raw2454step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5390 node5390Labels := by rfl

theorem canonical2455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2455 raw2455Labels = mixedMoment B node3741 node3741Labels := by
  calc
    mixedMoment B raw2455 raw2455Labels = mixedMoment B raw2455step0 raw2455step0Labels := by
      have ha : raw2455step0 = (fun i j => raw2455 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2455step0 raw2455; decide +kernel
      have hl : raw2455step0Labels = raw2455Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2455 raw2455Labels permutation8 permutation4
    _ = mixedMoment B node3741 node3741Labels := by rfl

theorem canonical2456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2456 raw2456Labels = mixedMoment B node3894 node3894Labels := by
  calc
    mixedMoment B raw2456 raw2456Labels = mixedMoment B raw2456step0 raw2456step0Labels := by
      have ha : raw2456step0 = (fun i j => raw2456 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2456step0 raw2456; decide +kernel
      have hl : raw2456step0Labels = raw2456Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2456 raw2456Labels permutation14 permutation3
    mixedMoment B raw2456step0 raw2456step0Labels = mixedMoment B raw2456step1 raw2456step1Labels := by
      have ha : raw2456step1 = -raw2456step0 := by apply Matrix.ext; change ∀ i j, raw2456step1 i j = -(raw2456step0 i j); unfold raw2456step1 raw2456step0; decide +kernel
      have hl : raw2456step1Labels = raw2456step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2456step1 raw2456step1Labels = mixedMoment B raw2456step2 raw2456step2Labels := by
      have ha : raw2456step2 = raw2456step1 := by apply Matrix.ext; unfold raw2456step2 raw2456step1; decide +kernel
      have hl : raw2456step1Labels = labelEmbedding1 ∘ raw2456step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2456step1 raw2456step1Labels raw2456step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3894 node3894Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical272
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34817 raw34817Labels = mixedMoment B node5390 node5390Labels := by
  calc
    mixedMoment B raw34817 raw34817Labels = mixedMoment B raw34817step0 raw34817step0Labels := by
      have hz : ∀ j, raw34817 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34817step0 = (fun i j => raw34817 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34817step0 raw34817; decide +kernel
      have hl : raw34817step0Labels = raw34817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34817 raw34817Labels permutation434 hz
    mixedMoment B raw34817step0 raw34817step0Labels = mixedMoment B raw34817step1 raw34817step1Labels := by
      have hz : ∀ j, raw34817step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34817step1 = (fun i j => raw34817step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34817step1 raw34817step0; decide +kernel
      have hl : raw34817step1Labels = raw34817step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34817step0 raw34817step0Labels permutation80 hz
    mixedMoment B raw34817step1 raw34817step1Labels = mixedMoment B raw34817step2 raw34817step2Labels := by
      have ha : raw34817step2 = (fun i j => raw34817step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34817step2 raw34817step1; decide +kernel
      have hl : raw34817step2Labels = raw34817step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34817step1 raw34817step1Labels permutation30 permutation6
    mixedMoment B raw34817step2 raw34817step2Labels = mixedMoment B raw34817step3 raw34817step3Labels := by
      have ha : raw34817step3 = -raw34817step2 := by apply Matrix.ext; change ∀ i j, raw34817step3 i j = -(raw34817step2 i j); unfold raw34817step3 raw34817step2; decide +kernel
      have hl : raw34817step3Labels = raw34817step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34817step3 raw34817step3Labels = mixedMoment B raw34817step4 raw34817step4Labels := by
      have ha : raw34817step4 = raw34817step3 := by apply Matrix.ext; unfold raw34817step4 raw34817step3; decide +kernel
      have hl : raw34817step3Labels = labelEmbedding9 ∘ raw34817step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34817step3 raw34817step3Labels raw34817step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5390 node5390Labels := by rfl

theorem canonical34818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34818 raw34818Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34818 raw34818Labels = mixedMoment B raw34818step0 raw34818step0Labels := by
      have hz : ∀ j, raw34818 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34818step0 = (fun i j => raw34818 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34818step0 raw34818; decide +kernel
      have hl : raw34818step0Labels = raw34818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34818 raw34818Labels permutation434 hz
    mixedMoment B raw34818step0 raw34818step0Labels = mixedMoment B raw34818step1 raw34818step1Labels := by
      have ha : raw34818step1 = (fun i j => raw34818step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34818step1 raw34818step0; decide +kernel
      have hl : raw34818step1Labels = raw34818step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34818step0 raw34818step0Labels permutation57 permutation7
    mixedMoment B raw34818step1 raw34818step1Labels = mixedMoment B raw34818step2 raw34818step2Labels := by
      have ha : raw34818step2 = raw34818step1 := by apply Matrix.ext; unfold raw34818step2 raw34818step1; decide +kernel
      have hl : raw34818step1Labels = labelEmbedding10 ∘ raw34818step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34818step1 raw34818step1Labels raw34818step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical34819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34819 raw34819Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34819 raw34819Labels = mixedMoment B raw34819step0 raw34819step0Labels := by
      have hz : ∀ j, raw34819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34819step0 = (fun i j => raw34819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34819step0 raw34819; decide +kernel
      have hl : raw34819step0Labels = raw34819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34819 raw34819Labels permutation346 hz
    mixedMoment B raw34819step0 raw34819step0Labels = mixedMoment B raw34819step1 raw34819step1Labels := by
      have ha : raw34819step1 = (fun i j => raw34819step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34819step1 raw34819step0; decide +kernel
      have hl : raw34819step1Labels = raw34819step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34819step0 raw34819step0Labels permutation57 permutation7
    mixedMoment B raw34819step1 raw34819step1Labels = mixedMoment B raw34819step2 raw34819step2Labels := by
      have ha : raw34819step2 = raw34819step1 := by apply Matrix.ext; unfold raw34819step2 raw34819step1; decide +kernel
      have hl : raw34819step1Labels = labelEmbedding10 ∘ raw34819step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34819step1 raw34819step1Labels raw34819step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical34820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34820 raw34820Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw34820 raw34820Labels = mixedMoment B raw34820step0 raw34820step0Labels := by
      have hz : ∀ j, raw34820 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34820step0 = (fun i j => raw34820 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34820step0 raw34820; decide +kernel
      have hl : raw34820step0Labels = raw34820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34820 raw34820Labels permutation434 hz
    mixedMoment B raw34820step0 raw34820step0Labels = mixedMoment B raw34820step1 raw34820step1Labels := by
      have hz : ∀ j, raw34820step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34820step1 = (fun i j => raw34820step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34820step1 raw34820step0; decide +kernel
      have hl : raw34820step1Labels = raw34820step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34820step0 raw34820step0Labels permutation80 hz
    mixedMoment B raw34820step1 raw34820step1Labels = mixedMoment B raw34820step2 raw34820step2Labels := by
      have ha : raw34820step2 = (fun i j => raw34820step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34820step2 raw34820step1; decide +kernel
      have hl : raw34820step2Labels = raw34820step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34820step1 raw34820step1Labels permutation24 permutation2
    _ = mixedMoment B node5238 node5238Labels := by rfl

theorem canonical34821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34821 raw34821Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw34821 raw34821Labels = mixedMoment B raw34821step0 raw34821step0Labels := by
      have hz : ∀ j, raw34821 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34821step0 = (fun i j => raw34821 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34821step0 raw34821; decide +kernel
      have hl : raw34821step0Labels = raw34821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34821 raw34821Labels permutation434 hz
    mixedMoment B raw34821step0 raw34821step0Labels = mixedMoment B raw34821step1 raw34821step1Labels := by
      have hz : ∀ j, raw34821step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34821step1 = (fun i j => raw34821step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34821step1 raw34821step0; decide +kernel
      have hl : raw34821step1Labels = raw34821step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34821step0 raw34821step0Labels permutation80 hz
    mixedMoment B raw34821step1 raw34821step1Labels = mixedMoment B raw34821step2 raw34821step2Labels := by
      have ha : raw34821step2 = (fun i j => raw34821step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34821step2 raw34821step1; decide +kernel
      have hl : raw34821step2Labels = raw34821step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34821step1 raw34821step1Labels permutation15 permutation7
    mixedMoment B raw34821step2 raw34821step2Labels = mixedMoment B raw34821step3 raw34821step3Labels := by
      have ha : raw34821step3 = raw34821step2 := by apply Matrix.ext; unfold raw34821step3 raw34821step2; decide +kernel
      have hl : raw34821step2Labels = labelEmbedding10 ∘ raw34821step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34821step2 raw34821step2Labels raw34821step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5371 node5371Labels := by rfl

theorem canonical34822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34822 raw34822Labels = mixedMoment B node5297 node5297Labels := by
  calc
    mixedMoment B raw34822 raw34822Labels = mixedMoment B raw34822step0 raw34822step0Labels := by
      have hz : ∀ j, raw34822 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34822step0 = (fun i j => raw34822 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34822step0 raw34822; decide +kernel
      have hl : raw34822step0Labels = raw34822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34822 raw34822Labels permutation434 hz
    mixedMoment B raw34822step0 raw34822step0Labels = mixedMoment B raw34822step1 raw34822step1Labels := by
      have hz : ∀ j, raw34822step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34822step1 = (fun i j => raw34822step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34822step1 raw34822step0; decide +kernel
      have hl : raw34822step1Labels = raw34822step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34822step0 raw34822step0Labels permutation80 hz
    mixedMoment B raw34822step1 raw34822step1Labels = mixedMoment B raw34822step2 raw34822step2Labels := by
      have ha : raw34822step2 = (fun i j => raw34822step1 (permutation18 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34822step2 raw34822step1; decide +kernel
      have hl : raw34822step2Labels = raw34822step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34822step1 raw34822step1Labels permutation18 permutation2
    mixedMoment B raw34822step2 raw34822step2Labels = mixedMoment B raw34822step3 raw34822step3Labels := by
      have ha : raw34822step3 = -raw34822step2 := by apply Matrix.ext; change ∀ i j, raw34822step3 i j = -(raw34822step2 i j); unfold raw34822step3 raw34822step2; decide +kernel
      have hl : raw34822step3Labels = raw34822step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5297 node5297Labels := by rfl

theorem canonical34823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34823 raw34823Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw34823 raw34823Labels = mixedMoment B raw34823step0 raw34823step0Labels := by
      have hz : ∀ j, raw34823 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34823step0 = (fun i j => raw34823 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34823step0 raw34823; decide +kernel
      have hl : raw34823step0Labels = raw34823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34823 raw34823Labels permutation434 hz
    mixedMoment B raw34823step0 raw34823step0Labels = mixedMoment B raw34823step1 raw34823step1Labels := by
      have ha : raw34823step1 = (fun i j => raw34823step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34823step1 raw34823step0; decide +kernel
      have hl : raw34823step1Labels = raw34823step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34823step0 raw34823step0Labels permutation60 permutation2
    mixedMoment B raw34823step1 raw34823step1Labels = mixedMoment B raw34823step2 raw34823step2Labels := by
      have ha : raw34823step2 = -raw34823step1 := by apply Matrix.ext; change ∀ i j, raw34823step2 i j = -(raw34823step1 i j); unfold raw34823step2 raw34823step1; decide +kernel
      have hl : raw34823step2Labels = raw34823step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5232 node5232Labels := by rfl

theorem canonical34824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34824 raw34824Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw34824 raw34824Labels = mixedMoment B raw34824step0 raw34824step0Labels := by
      have hz : ∀ j, raw34824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34824step0 = (fun i j => raw34824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34824step0 raw34824; decide +kernel
      have hl : raw34824step0Labels = raw34824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34824 raw34824Labels permutation346 hz
    mixedMoment B raw34824step0 raw34824step0Labels = mixedMoment B raw34824step1 raw34824step1Labels := by
      have ha : raw34824step1 = (fun i j => raw34824step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34824step1 raw34824step0; decide +kernel
      have hl : raw34824step1Labels = raw34824step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34824step0 raw34824step0Labels permutation60 permutation2
    mixedMoment B raw34824step1 raw34824step1Labels = mixedMoment B raw34824step2 raw34824step2Labels := by
      have ha : raw34824step2 = -raw34824step1 := by apply Matrix.ext; change ∀ i j, raw34824step2 i j = -(raw34824step1 i j); unfold raw34824step2 raw34824step1; decide +kernel
      have hl : raw34824step2Labels = raw34824step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5232 node5232Labels := by rfl

theorem canonical34825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34825 raw34825Labels = mixedMoment B node5235 node5235Labels := by
  calc
    mixedMoment B raw34825 raw34825Labels = mixedMoment B raw34825step0 raw34825step0Labels := by
      have hz : ∀ j, raw34825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34825step0 = (fun i j => raw34825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34825step0 raw34825; decide +kernel
      have hl : raw34825step0Labels = raw34825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34825 raw34825Labels permutation434 hz
    mixedMoment B raw34825step0 raw34825step0Labels = mixedMoment B raw34825step1 raw34825step1Labels := by
      have hz : ∀ j, raw34825step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34825step1 = (fun i j => raw34825step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34825step1 raw34825step0; decide +kernel
      have hl : raw34825step1Labels = raw34825step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34825step0 raw34825step0Labels permutation80 hz
    mixedMoment B raw34825step1 raw34825step1Labels = mixedMoment B raw34825step2 raw34825step2Labels := by
      have ha : raw34825step2 = (fun i j => raw34825step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34825step2 raw34825step1; decide +kernel
      have hl : raw34825step2Labels = raw34825step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34825step1 raw34825step1Labels permutation24 permutation2
    _ = mixedMoment B node5235 node5235Labels := by rfl

theorem canonical34826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34826 raw34826Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw34826 raw34826Labels = mixedMoment B raw34826step0 raw34826step0Labels := by
      have hz : ∀ j, raw34826 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34826step0 = (fun i j => raw34826 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34826step0 raw34826; decide +kernel
      have hl : raw34826step0Labels = raw34826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34826 raw34826Labels permutation434 hz
    mixedMoment B raw34826step0 raw34826step0Labels = mixedMoment B raw34826step1 raw34826step1Labels := by
      have hz : ∀ j, raw34826step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34826step1 = (fun i j => raw34826step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34826step1 raw34826step0; decide +kernel
      have hl : raw34826step1Labels = raw34826step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34826step0 raw34826step0Labels permutation80 hz
    mixedMoment B raw34826step1 raw34826step1Labels = mixedMoment B raw34826step2 raw34826step2Labels := by
      have ha : raw34826step2 = (fun i j => raw34826step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34826step2 raw34826step1; decide +kernel
      have hl : raw34826step2Labels = raw34826step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34826step1 raw34826step1Labels permutation15 permutation2
    mixedMoment B raw34826step2 raw34826step2Labels = mixedMoment B raw34826step3 raw34826step3Labels := by
      have ha : raw34826step3 = -raw34826step2 := by apply Matrix.ext; change ∀ i j, raw34826step3 i j = -(raw34826step2 i j); unfold raw34826step3 raw34826step2; decide +kernel
      have hl : raw34826step3Labels = raw34826step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5238 node5238Labels := by rfl

theorem canonical34827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34827 raw34827Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw34827 raw34827Labels = mixedMoment B raw34827step0 raw34827step0Labels := by
      have hz : ∀ j, raw34827 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34827step0 = (fun i j => raw34827 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34827step0 raw34827; decide +kernel
      have hl : raw34827step0Labels = raw34827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34827 raw34827Labels permutation434 hz
    mixedMoment B raw34827step0 raw34827step0Labels = mixedMoment B raw34827step1 raw34827step1Labels := by
      have ha : raw34827step1 = (fun i j => raw34827step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34827step1 raw34827step0; decide +kernel
      have hl : raw34827step1Labels = raw34827step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34827step0 raw34827step0Labels permutation34 permutation4
    mixedMoment B raw34827step1 raw34827step1Labels = mixedMoment B raw34827step2 raw34827step2Labels := by
      have ha : raw34827step2 = -raw34827step1 := by apply Matrix.ext; change ∀ i j, raw34827step2 i j = -(raw34827step1 i j); unfold raw34827step2 raw34827step1; decide +kernel
      have hl : raw34827step2Labels = raw34827step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34827step2 raw34827step2Labels = mixedMoment B raw34827step3 raw34827step3Labels := by
      have ha : raw34827step3 = raw34827step2 := by apply Matrix.ext; unfold raw34827step3 raw34827step2; decide +kernel
      have hl : raw34827step2Labels = labelEmbedding7 ∘ raw34827step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34827step2 raw34827step2Labels raw34827step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

theorem canonical34828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34828 raw34828Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34828 raw34828Labels = mixedMoment B raw34828step0 raw34828step0Labels := by
      have hz : ∀ j, raw34828 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34828step0 = (fun i j => raw34828 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34828step0 raw34828; decide +kernel
      have hl : raw34828step0Labels = raw34828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34828 raw34828Labels permutation434 hz
    mixedMoment B raw34828step0 raw34828step0Labels = mixedMoment B raw34828step1 raw34828step1Labels := by
      have ha : raw34828step1 = (fun i j => raw34828step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34828step1 raw34828step0; decide +kernel
      have hl : raw34828step1Labels = raw34828step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34828step0 raw34828step0Labels permutation32 permutation6
    mixedMoment B raw34828step1 raw34828step1Labels = mixedMoment B raw34828step2 raw34828step2Labels := by
      have ha : raw34828step2 = raw34828step1 := by apply Matrix.ext; unfold raw34828step2 raw34828step1; decide +kernel
      have hl : raw34828step1Labels = labelEmbedding9 ∘ raw34828step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34828step1 raw34828step1Labels raw34828step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical34829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34829 raw34829Labels = mixedMoment B node5376 node5376Labels := by
  calc
    mixedMoment B raw34829 raw34829Labels = mixedMoment B raw34829step0 raw34829step0Labels := by
      have ha : raw34829step0 = (fun i j => raw34829 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34829step0 raw34829; decide +kernel
      have hl : raw34829step0Labels = raw34829Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34829 raw34829Labels permutation158 permutation6
    mixedMoment B raw34829step0 raw34829step0Labels = mixedMoment B raw34829step1 raw34829step1Labels := by
      have ha : raw34829step1 = raw34829step0 := by apply Matrix.ext; unfold raw34829step1 raw34829step0; decide +kernel
      have hl : raw34829step0Labels = labelEmbedding9 ∘ raw34829step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34829step0 raw34829step0Labels raw34829step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5376 node5376Labels := by rfl

theorem canonical34830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34830 raw34830Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw34830 raw34830Labels = mixedMoment B raw34830step0 raw34830step0Labels := by
      have hz : ∀ j, raw34830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34830step0 = (fun i j => raw34830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34830step0 raw34830; decide +kernel
      have hl : raw34830step0Labels = raw34830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34830 raw34830Labels permutation434 hz
    mixedMoment B raw34830step0 raw34830step0Labels = mixedMoment B raw34830step1 raw34830step1Labels := by
      have ha : raw34830step1 = (fun i j => raw34830step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34830step1 raw34830step0; decide +kernel
      have hl : raw34830step1Labels = raw34830step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34830step0 raw34830step0Labels permutation123 permutation2
    _ = mixedMoment B node5232 node5232Labels := by rfl

theorem canonical34831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34831 raw34831Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34831 raw34831Labels = mixedMoment B raw34831step0 raw34831step0Labels := by
      have hz : ∀ j, raw34831 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34831step0 = (fun i j => raw34831 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34831step0 raw34831; decide +kernel
      have hl : raw34831step0Labels = raw34831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34831 raw34831Labels permutation434 hz
    mixedMoment B raw34831step0 raw34831step0Labels = mixedMoment B raw34831step1 raw34831step1Labels := by
      have ha : raw34831step1 = (fun i j => raw34831step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34831step1 raw34831step0; decide +kernel
      have hl : raw34831step1Labels = raw34831step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34831step0 raw34831step0Labels permutation126 permutation7
    mixedMoment B raw34831step1 raw34831step1Labels = mixedMoment B raw34831step2 raw34831step2Labels := by
      have ha : raw34831step2 = -raw34831step1 := by apply Matrix.ext; change ∀ i j, raw34831step2 i j = -(raw34831step1 i j); unfold raw34831step2 raw34831step1; decide +kernel
      have hl : raw34831step2Labels = raw34831step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34831step2 raw34831step2Labels = mixedMoment B raw34831step3 raw34831step3Labels := by
      have ha : raw34831step3 = raw34831step2 := by apply Matrix.ext; unfold raw34831step3 raw34831step2; decide +kernel
      have hl : raw34831step2Labels = labelEmbedding10 ∘ raw34831step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34831step2 raw34831step2Labels raw34831step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical34832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34832 raw34832Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw34832 raw34832Labels = mixedMoment B raw34832step0 raw34832step0Labels := by
      have hz : ∀ j, raw34832 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34832step0 = (fun i j => raw34832 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34832step0 raw34832; decide +kernel
      have hl : raw34832step0Labels = raw34832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34832 raw34832Labels permutation346 hz
    mixedMoment B raw34832step0 raw34832step0Labels = mixedMoment B raw34832step1 raw34832step1Labels := by
      have ha : raw34832step1 = (fun i j => raw34832step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34832step1 raw34832step0; decide +kernel
      have hl : raw34832step1Labels = raw34832step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34832step0 raw34832step0Labels permutation34 permutation4
    mixedMoment B raw34832step1 raw34832step1Labels = mixedMoment B raw34832step2 raw34832step2Labels := by
      have ha : raw34832step2 = -raw34832step1 := by apply Matrix.ext; change ∀ i j, raw34832step2 i j = -(raw34832step1 i j); unfold raw34832step2 raw34832step1; decide +kernel
      have hl : raw34832step2Labels = raw34832step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34832step2 raw34832step2Labels = mixedMoment B raw34832step3 raw34832step3Labels := by
      have ha : raw34832step3 = raw34832step2 := by apply Matrix.ext; unfold raw34832step3 raw34832step2; decide +kernel
      have hl : raw34832step2Labels = labelEmbedding7 ∘ raw34832step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34832step2 raw34832step2Labels raw34832step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

theorem canonical34833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34833 raw34833Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34833 raw34833Labels = mixedMoment B raw34833step0 raw34833step0Labels := by
      have hz : ∀ j, raw34833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34833step0 = (fun i j => raw34833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34833step0 raw34833; decide +kernel
      have hl : raw34833step0Labels = raw34833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34833 raw34833Labels permutation346 hz
    mixedMoment B raw34833step0 raw34833step0Labels = mixedMoment B raw34833step1 raw34833step1Labels := by
      have ha : raw34833step1 = (fun i j => raw34833step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34833step1 raw34833step0; decide +kernel
      have hl : raw34833step1Labels = raw34833step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34833step0 raw34833step0Labels permutation32 permutation6
    mixedMoment B raw34833step1 raw34833step1Labels = mixedMoment B raw34833step2 raw34833step2Labels := by
      have ha : raw34833step2 = raw34833step1 := by apply Matrix.ext; unfold raw34833step2 raw34833step1; decide +kernel
      have hl : raw34833step1Labels = labelEmbedding9 ∘ raw34833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34833step1 raw34833step1Labels raw34833step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical34834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34834 raw34834Labels = mixedMoment B node5376 node5376Labels := by
  calc
    mixedMoment B raw34834 raw34834Labels = mixedMoment B raw34834step0 raw34834step0Labels := by
      have ha : raw34834step0 = (fun i j => raw34834 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34834step0 raw34834; decide +kernel
      have hl : raw34834step0Labels = raw34834Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34834 raw34834Labels permutation152 permutation6
    mixedMoment B raw34834step0 raw34834step0Labels = mixedMoment B raw34834step1 raw34834step1Labels := by
      have ha : raw34834step1 = raw34834step0 := by apply Matrix.ext; unfold raw34834step1 raw34834step0; decide +kernel
      have hl : raw34834step0Labels = labelEmbedding9 ∘ raw34834step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34834step0 raw34834step0Labels raw34834step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5376 node5376Labels := by rfl

theorem canonical34835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34835 raw34835Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw34835 raw34835Labels = mixedMoment B raw34835step0 raw34835step0Labels := by
      have hz : ∀ j, raw34835 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34835step0 = (fun i j => raw34835 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34835step0 raw34835; decide +kernel
      have hl : raw34835step0Labels = raw34835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34835 raw34835Labels permutation346 hz
    mixedMoment B raw34835step0 raw34835step0Labels = mixedMoment B raw34835step1 raw34835step1Labels := by
      have ha : raw34835step1 = (fun i j => raw34835step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34835step1 raw34835step0; decide +kernel
      have hl : raw34835step1Labels = raw34835step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34835step0 raw34835step0Labels permutation123 permutation2
    _ = mixedMoment B node5232 node5232Labels := by rfl

theorem canonical34836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34836 raw34836Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34836 raw34836Labels = mixedMoment B raw34836step0 raw34836step0Labels := by
      have hz : ∀ j, raw34836 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34836step0 = (fun i j => raw34836 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34836step0 raw34836; decide +kernel
      have hl : raw34836step0Labels = raw34836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34836 raw34836Labels permutation346 hz
    mixedMoment B raw34836step0 raw34836step0Labels = mixedMoment B raw34836step1 raw34836step1Labels := by
      have ha : raw34836step1 = (fun i j => raw34836step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34836step1 raw34836step0; decide +kernel
      have hl : raw34836step1Labels = raw34836step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34836step0 raw34836step0Labels permutation126 permutation7
    mixedMoment B raw34836step1 raw34836step1Labels = mixedMoment B raw34836step2 raw34836step2Labels := by
      have ha : raw34836step2 = -raw34836step1 := by apply Matrix.ext; change ∀ i j, raw34836step2 i j = -(raw34836step1 i j); unfold raw34836step2 raw34836step1; decide +kernel
      have hl : raw34836step2Labels = raw34836step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34836step2 raw34836step2Labels = mixedMoment B raw34836step3 raw34836step3Labels := by
      have ha : raw34836step3 = raw34836step2 := by apply Matrix.ext; unfold raw34836step3 raw34836step2; decide +kernel
      have hl : raw34836step2Labels = labelEmbedding10 ∘ raw34836step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34836step2 raw34836step2Labels raw34836step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical34837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34837 raw34837Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw34837 raw34837Labels = mixedMoment B raw34837step0 raw34837step0Labels := by
      have hz : ∀ j, raw34837 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34837step0 = (fun i j => raw34837 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34837step0 raw34837; decide +kernel
      have hl : raw34837step0Labels = raw34837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34837 raw34837Labels permutation434 hz
    mixedMoment B raw34837step0 raw34837step0Labels = mixedMoment B raw34837step1 raw34837step1Labels := by
      have hz : ∀ j, raw34837step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34837step1 = (fun i j => raw34837step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34837step1 raw34837step0; decide +kernel
      have hl : raw34837step1Labels = raw34837step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34837step0 raw34837step0Labels permutation80 hz
    mixedMoment B raw34837step1 raw34837step1Labels = mixedMoment B raw34837step2 raw34837step2Labels := by
      have ha : raw34837step2 = (fun i j => raw34837step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34837step2 raw34837step1; decide +kernel
      have hl : raw34837step2Labels = raw34837step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34837step1 raw34837step1Labels permutation8 permutation4
    mixedMoment B raw34837step2 raw34837step2Labels = mixedMoment B raw34837step3 raw34837step3Labels := by
      have ha : raw34837step3 = -raw34837step2 := by apply Matrix.ext; change ∀ i j, raw34837step3 i j = -(raw34837step2 i j); unfold raw34837step3 raw34837step2; decide +kernel
      have hl : raw34837step3Labels = raw34837step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34837step3 raw34837step3Labels = mixedMoment B raw34837step4 raw34837step4Labels := by
      have ha : raw34837step4 = raw34837step3 := by apply Matrix.ext; unfold raw34837step4 raw34837step3; decide +kernel
      have hl : raw34837step3Labels = labelEmbedding7 ∘ raw34837step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34837step3 raw34837step3Labels raw34837step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

theorem canonical34838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34838 raw34838Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw34838 raw34838Labels = mixedMoment B raw34838step0 raw34838step0Labels := by
      have hz : ∀ j, raw34838 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34838step0 = (fun i j => raw34838 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34838step0 raw34838; decide +kernel
      have hl : raw34838step0Labels = raw34838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34838 raw34838Labels permutation434 hz
    mixedMoment B raw34838step0 raw34838step0Labels = mixedMoment B raw34838step1 raw34838step1Labels := by
      have hz : ∀ j, raw34838step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34838step1 = (fun i j => raw34838step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34838step1 raw34838step0; decide +kernel
      have hl : raw34838step1Labels = raw34838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34838step0 raw34838step0Labels permutation80 hz
    mixedMoment B raw34838step1 raw34838step1Labels = mixedMoment B raw34838step2 raw34838step2Labels := by
      have ha : raw34838step2 = (fun i j => raw34838step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34838step2 raw34838step1; decide +kernel
      have hl : raw34838step2Labels = raw34838step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34838step1 raw34838step1Labels permutation8 permutation6
    mixedMoment B raw34838step2 raw34838step2Labels = mixedMoment B raw34838step3 raw34838step3Labels := by
      have ha : raw34838step3 = raw34838step2 := by apply Matrix.ext; unfold raw34838step3 raw34838step2; decide +kernel
      have hl : raw34838step2Labels = labelEmbedding9 ∘ raw34838step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34838step2 raw34838step2Labels raw34838step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5371 node5371Labels := by rfl

theorem canonical34839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34839 raw34839Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34839 raw34839Labels = mixedMoment B raw34839step0 raw34839step0Labels := by
      have hz : ∀ j, raw34839 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34839step0 = (fun i j => raw34839 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34839step0 raw34839; decide +kernel
      have hl : raw34839step0Labels = raw34839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34839 raw34839Labels permutation434 hz
    mixedMoment B raw34839step0 raw34839step0Labels = mixedMoment B raw34839step1 raw34839step1Labels := by
      have ha : raw34839step1 = (fun i j => raw34839step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34839step1 raw34839step0; decide +kernel
      have hl : raw34839step1Labels = raw34839step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34839step0 raw34839step0Labels permutation151 permutation6
    mixedMoment B raw34839step1 raw34839step1Labels = mixedMoment B raw34839step2 raw34839step2Labels := by
      have ha : raw34839step2 = -raw34839step1 := by apply Matrix.ext; change ∀ i j, raw34839step2 i j = -(raw34839step1 i j); unfold raw34839step2 raw34839step1; decide +kernel
      have hl : raw34839step2Labels = raw34839step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34839step2 raw34839step2Labels = mixedMoment B raw34839step3 raw34839step3Labels := by
      have ha : raw34839step3 = raw34839step2 := by apply Matrix.ext; unfold raw34839step3 raw34839step2; decide +kernel
      have hl : raw34839step2Labels = labelEmbedding9 ∘ raw34839step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34839step2 raw34839step2Labels raw34839step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical34840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34840 raw34840Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34840 raw34840Labels = mixedMoment B raw34840step0 raw34840step0Labels := by
      have hz : ∀ j, raw34840 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34840step0 = (fun i j => raw34840 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34840step0 raw34840; decide +kernel
      have hl : raw34840step0Labels = raw34840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34840 raw34840Labels permutation346 hz
    mixedMoment B raw34840step0 raw34840step0Labels = mixedMoment B raw34840step1 raw34840step1Labels := by
      have ha : raw34840step1 = (fun i j => raw34840step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34840step1 raw34840step0; decide +kernel
      have hl : raw34840step1Labels = raw34840step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34840step0 raw34840step0Labels permutation151 permutation6
    mixedMoment B raw34840step1 raw34840step1Labels = mixedMoment B raw34840step2 raw34840step2Labels := by
      have ha : raw34840step2 = -raw34840step1 := by apply Matrix.ext; change ∀ i j, raw34840step2 i j = -(raw34840step1 i j); unfold raw34840step2 raw34840step1; decide +kernel
      have hl : raw34840step2Labels = raw34840step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34840step2 raw34840step2Labels = mixedMoment B raw34840step3 raw34840step3Labels := by
      have ha : raw34840step3 = raw34840step2 := by apply Matrix.ext; unfold raw34840step3 raw34840step2; decide +kernel
      have hl : raw34840step2Labels = labelEmbedding9 ∘ raw34840step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34840step2 raw34840step2Labels raw34840step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical34841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34841 raw34841Labels = mixedMoment B node5390 node5390Labels := by
  calc
    mixedMoment B raw34841 raw34841Labels = mixedMoment B raw34841step0 raw34841step0Labels := by
      have hz : ∀ j, raw34841 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34841step0 = (fun i j => raw34841 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34841step0 raw34841; decide +kernel
      have hl : raw34841step0Labels = raw34841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34841 raw34841Labels permutation434 hz
    mixedMoment B raw34841step0 raw34841step0Labels = mixedMoment B raw34841step1 raw34841step1Labels := by
      have hz : ∀ j, raw34841step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34841step1 = (fun i j => raw34841step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34841step1 raw34841step0; decide +kernel
      have hl : raw34841step1Labels = raw34841step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34841step0 raw34841step0Labels permutation80 hz
    mixedMoment B raw34841step1 raw34841step1Labels = mixedMoment B raw34841step2 raw34841step2Labels := by
      have ha : raw34841step2 = (fun i j => raw34841step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34841step2 raw34841step1; decide +kernel
      have hl : raw34841step2Labels = raw34841step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34841step1 raw34841step1Labels permutation8 permutation6
    mixedMoment B raw34841step2 raw34841step2Labels = mixedMoment B raw34841step3 raw34841step3Labels := by
      have ha : raw34841step3 = raw34841step2 := by apply Matrix.ext; unfold raw34841step3 raw34841step2; decide +kernel
      have hl : raw34841step2Labels = labelEmbedding9 ∘ raw34841step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34841step2 raw34841step2Labels raw34841step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5390 node5390Labels := by rfl

theorem canonical34842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34842 raw34842Labels = mixedMoment B node5235 node5235Labels := by
  calc
    mixedMoment B raw34842 raw34842Labels = mixedMoment B raw34842step0 raw34842step0Labels := by
      have hz : ∀ j, raw34842 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34842step0 = (fun i j => raw34842 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34842step0 raw34842; decide +kernel
      have hl : raw34842step0Labels = raw34842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34842 raw34842Labels permutation434 hz
    mixedMoment B raw34842step0 raw34842step0Labels = mixedMoment B raw34842step1 raw34842step1Labels := by
      have hz : ∀ j, raw34842step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34842step1 = (fun i j => raw34842step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34842step1 raw34842step0; decide +kernel
      have hl : raw34842step1Labels = raw34842step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34842step0 raw34842step0Labels permutation80 hz
    mixedMoment B raw34842step1 raw34842step1Labels = mixedMoment B raw34842step2 raw34842step2Labels := by
      have ha : raw34842step2 = (fun i j => raw34842step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34842step2 raw34842step1; decide +kernel
      have hl : raw34842step2Labels = raw34842step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34842step1 raw34842step1Labels permutation31 permutation4
    mixedMoment B raw34842step2 raw34842step2Labels = mixedMoment B raw34842step3 raw34842step3Labels := by
      have ha : raw34842step3 = raw34842step2 := by apply Matrix.ext; unfold raw34842step3 raw34842step2; decide +kernel
      have hl : raw34842step2Labels = labelEmbedding7 ∘ raw34842step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34842step2 raw34842step2Labels raw34842step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5235 node5235Labels := by rfl

theorem canonical34843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34843 raw34843Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw34843 raw34843Labels = mixedMoment B raw34843step0 raw34843step0Labels := by
      have hz : ∀ j, raw34843 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34843step0 = (fun i j => raw34843 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34843step0 raw34843; decide +kernel
      have hl : raw34843step0Labels = raw34843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34843 raw34843Labels permutation434 hz
    mixedMoment B raw34843step0 raw34843step0Labels = mixedMoment B raw34843step1 raw34843step1Labels := by
      have hz : ∀ j, raw34843step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34843step1 = (fun i j => raw34843step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34843step1 raw34843step0; decide +kernel
      have hl : raw34843step1Labels = raw34843step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34843step0 raw34843step0Labels permutation80 hz
    mixedMoment B raw34843step1 raw34843step1Labels = mixedMoment B raw34843step2 raw34843step2Labels := by
      have ha : raw34843step2 = (fun i j => raw34843step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34843step2 raw34843step1; decide +kernel
      have hl : raw34843step2Labels = raw34843step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34843step1 raw34843step1Labels permutation31 permutation4
    mixedMoment B raw34843step2 raw34843step2Labels = mixedMoment B raw34843step3 raw34843step3Labels := by
      have ha : raw34843step3 = raw34843step2 := by apply Matrix.ext; unfold raw34843step3 raw34843step2; decide +kernel
      have hl : raw34843step2Labels = labelEmbedding7 ∘ raw34843step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34843step2 raw34843step2Labels raw34843step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

theorem canonical34844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34844 raw34844Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw34844 raw34844Labels = mixedMoment B raw34844step0 raw34844step0Labels := by
      have hz : ∀ j, raw34844 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34844step0 = (fun i j => raw34844 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34844step0 raw34844; decide +kernel
      have hl : raw34844step0Labels = raw34844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34844 raw34844Labels permutation434 hz
    mixedMoment B raw34844step0 raw34844step0Labels = mixedMoment B raw34844step1 raw34844step1Labels := by
      have ha : raw34844step1 = (fun i j => raw34844step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34844step1 raw34844step0; decide +kernel
      have hl : raw34844step1Labels = raw34844step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34844step0 raw34844step0Labels permutation149 permutation4
    mixedMoment B raw34844step1 raw34844step1Labels = mixedMoment B raw34844step2 raw34844step2Labels := by
      have ha : raw34844step2 = raw34844step1 := by apply Matrix.ext; unfold raw34844step2 raw34844step1; decide +kernel
      have hl : raw34844step1Labels = labelEmbedding7 ∘ raw34844step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34844step1 raw34844step1Labels raw34844step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

theorem canonical34845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34845 raw34845Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw34845 raw34845Labels = mixedMoment B raw34845step0 raw34845step0Labels := by
      have hz : ∀ j, raw34845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34845step0 = (fun i j => raw34845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34845step0 raw34845; decide +kernel
      have hl : raw34845step0Labels = raw34845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34845 raw34845Labels permutation346 hz
    mixedMoment B raw34845step0 raw34845step0Labels = mixedMoment B raw34845step1 raw34845step1Labels := by
      have ha : raw34845step1 = (fun i j => raw34845step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34845step1 raw34845step0; decide +kernel
      have hl : raw34845step1Labels = raw34845step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34845step0 raw34845step0Labels permutation149 permutation4
    mixedMoment B raw34845step1 raw34845step1Labels = mixedMoment B raw34845step2 raw34845step2Labels := by
      have ha : raw34845step2 = raw34845step1 := by apply Matrix.ext; unfold raw34845step2 raw34845step1; decide +kernel
      have hl : raw34845step1Labels = labelEmbedding7 ∘ raw34845step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34845step1 raw34845step1Labels raw34845step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

theorem canonical34846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34846 raw34846Labels = mixedMoment B node5297 node5297Labels := by
  calc
    mixedMoment B raw34846 raw34846Labels = mixedMoment B raw34846step0 raw34846step0Labels := by
      have hz : ∀ j, raw34846 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34846step0 = (fun i j => raw34846 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34846step0 raw34846; decide +kernel
      have hl : raw34846step0Labels = raw34846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34846 raw34846Labels permutation434 hz
    mixedMoment B raw34846step0 raw34846step0Labels = mixedMoment B raw34846step1 raw34846step1Labels := by
      have hz : ∀ j, raw34846step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34846step1 = (fun i j => raw34846step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34846step1 raw34846step0; decide +kernel
      have hl : raw34846step1Labels = raw34846step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34846step0 raw34846step0Labels permutation80 hz
    mixedMoment B raw34846step1 raw34846step1Labels = mixedMoment B raw34846step2 raw34846step2Labels := by
      have ha : raw34846step2 = (fun i j => raw34846step1 (permutation21 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34846step2 raw34846step1; decide +kernel
      have hl : raw34846step2Labels = raw34846step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34846step1 raw34846step1Labels permutation21 permutation2
    _ = mixedMoment B node5297 node5297Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw502 raw502Labels = mixedMoment B node3741 node3741Labels := by
  calc
    mixedMoment B raw502 raw502Labels = mixedMoment B raw502step0 raw502step0Labels := by
      have ha : raw502step0 = (fun i j => raw502 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw502step0 raw502; decide +kernel
      have hl : raw502step0Labels = raw502Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw502 raw502Labels permutation8 permutation5
    mixedMoment B raw502step0 raw502step0Labels = mixedMoment B raw502step1 raw502step1Labels := by
      have ha : raw502step1 = raw502step0 := by apply Matrix.ext; unfold raw502step1 raw502step0; decide +kernel
      have hl : raw502step0Labels = labelEmbedding1 ∘ raw502step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw502step0 raw502step0Labels raw502step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3741 node3741Labels := by rfl

theorem canonical503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw503 raw503Labels = mixedMoment B node452 node452Labels := by
  calc
    mixedMoment B raw503 raw503Labels = mixedMoment B raw503step0 raw503step0Labels := by
      have ha : raw503step0 = (fun i j => raw503 (permutation14 i) (permutation4 j)) := by apply Matrix.ext; unfold raw503step0 raw503; decide +kernel
      have hl : raw503step0Labels = raw503Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw503 raw503Labels permutation14 permutation4
    _ = mixedMoment B node452 node452Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3893 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3893 = injectiveMoment H node202 := by
  calc
    injectiveMoment H raw3893 = injectiveMoment H raw3893step0 := by
      have heq : raw3893step0 = -raw3893 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3893).symm
    injectiveMoment H raw3893step0 = injectiveMoment H raw3893step1 := by
      have heq : raw3893step1 = (fun i j => raw3893step0 (permutation15 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3893step0 permutation15 permutation6
    _ = injectiveMoment H node202 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5116 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5116 = injectiveMoment H node45 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical280
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8979 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw8979 = injectiveMoment H raw8979step0 := by
      have hz : ∀ j, raw8979 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8979step0 = (fun i j => raw8979 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8979 permutation9 hz
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

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

theorem sound45 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node45 = Sparse.eval value45 (momentVector H) := by
  have hc : momentVector H 27 = injectiveMoment H node45 := rfl
  simp [value45, Sparse.eval, hc]

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

theorem sound202 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node202 = Sparse.eval value202 (momentVector H) := by
  have hc : momentVector H 24 = injectiveMoment H node202 := rfl
  simp [value202, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node452 node452Labels = Sparse.eval singlePairValue452 (familyPairVector B) := by
  have hp := single_label_three B hB node452
  have hl : node452Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node452 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node452 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node452 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node452 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node452 (EqualityPatterns.family3.label 1) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node452 PairSemantics.raw5177; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node452 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node452 (EqualityPatterns.family3.label 2) = PairSemantics.raw8979 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node452 PairSemantics.raw8979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8979 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node452 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value45 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node452 (EqualityPatterns.family3.label 3) = PairSemantics.raw5116 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node452 PairSemantics.raw5116; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5116 hH).trans (PairSemantics.sound45 hH)
  have hm4 : familyPairMoment B (groupedColumns node452 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value202 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node452 (EqualityPatterns.family3.label 4) = PairSemantics.raw3893 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node452 PairSemantics.raw3893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3893 hH).trans (PairSemantics.sound202 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue452, PairSemantics.value0, PairSemantics.value11, PairSemantics.value45, PairSemantics.value202, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3741 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3741 node3741Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node452 node452Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw502 singletonSmall3741
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3741) = raw502Labels := by decide +kernel
  rw [hl, canonical502 B hB] at h
  have hc0 : mixedMoment B raw502 (Fin.cases (0 : Fin 1) singletonSmall3741) =
      mixedMoment B node452 node452Labels := by
    have ha : raw502 = raw503 := by apply Matrix.ext; unfold raw502 raw503; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3741 = raw503Labels := by decide +kernel
    rw [ha, hj, canonical503 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem singleton5355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5355 node5355Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3693 node3693Labels + mixedMoment B node3770 node3770Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2400 singletonSmall5355
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5355) = raw2400Labels := by decide +kernel
  rw [hl, canonical2400 B hB] at h
  have hc0 : mixedMoment B raw2400 (Fin.cases (0 : Fin 2) singletonSmall5355) =
      mixedMoment B node3693 node3693Labels := by
    have ha : raw2400 = raw2401 := by apply Matrix.ext; unfold raw2400 raw2401; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5355 = raw2401Labels := by decide +kernel
    rw [ha, hj, canonical2401 B hB]
  have hc1 : mixedMoment B raw2400 (Fin.cases (1 : Fin 2) singletonSmall5355) =
      mixedMoment B node3770 node3770Labels := by
    have ha : raw2400 = raw2402 := by apply Matrix.ext; unfold raw2400 raw2402; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5355 = raw2402Labels := by decide +kernel
    rw [ha, hj, canonical2402 B hB]
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

theorem singleton5390 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5390 node5390Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3741 node3741Labels + mixedMoment B node3894 node3894Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2454 singletonSmall5390
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5390) = raw2454Labels := by decide +kernel
  rw [hl, canonical2454 B hB] at h
  have hc0 : mixedMoment B raw2454 (Fin.cases (0 : Fin 2) singletonSmall5390) =
      mixedMoment B node3741 node3741Labels := by
    have ha : raw2454 = raw2455 := by apply Matrix.ext; unfold raw2454 raw2455; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5390 = raw2455Labels := by decide +kernel
    rw [ha, hj, canonical2455 B hB]
  have hc1 : mixedMoment B raw2454 (Fin.cases (1 : Fin 2) singletonSmall5390) =
      mixedMoment B node3894 node3894Labels := by
    have ha : raw2454 = raw2456 := by apply Matrix.ext; unfold raw2454 raw2456; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5390 = raw2456Labels := by decide +kernel
    rw [ha, hj, canonical2456 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3693 node3693Labels = Sparse.eval nodeValue3693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3693) = mixedMoment B node3693 node3693Labels := rfl
  simpa [nodeValue3693, Sparse.eval] using hc.symm

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

theorem sound452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node452 node452Labels = Sparse.eval nodeValue452 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue452 (familyPairVector B) := singlePair452 B _hB
    _ = _ := by norm_num [singlePairValue452, nodeValue452, Sparse.eval, mixedVector] <;> ring

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

theorem sound3741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3741 node3741Labels = Sparse.eval nodeValue3741 (mixedVector B) := by
  have h := singleton3741 B _hB
  rw [sound452 B _hB _hF] at h
  norm_num [nodeValue3741, nodeValue452, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3770 node3770Labels = Sparse.eval nodeValue3770 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3770) = mixedMoment B node3770 node3770Labels := rfl
  simpa [nodeValue3770, Sparse.eval] using hc.symm

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

theorem sound3894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3894 node3894Labels = Sparse.eval nodeValue3894 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3894) = mixedMoment B node3894 node3894Labels := rfl
  simpa [nodeValue3894, Sparse.eval] using hc.symm

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

theorem sound5232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5232 node5232Labels = Sparse.eval nodeValue5232 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5232) = mixedMoment B node5232 node5232Labels := rfl
  simpa [nodeValue5232, Sparse.eval] using hc.symm

theorem sound5235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5235 node5235Labels = Sparse.eval nodeValue5235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5235) = mixedMoment B node5235 node5235Labels := rfl
  simpa [nodeValue5235, Sparse.eval] using hc.symm

theorem sound5238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5238 node5238Labels = Sparse.eval nodeValue5238 (mixedVector B) := by
  have h := singleton5238 B _hB
  rw [sound2686 B _hB _hF, sound3397 B _hB _hF] at h
  norm_num [nodeValue5238, nodeValue2686, nodeValue3397, Sparse.eval] at h ⊢
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

theorem sound5297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5297 node5297Labels = Sparse.eval nodeValue5297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5297) = mixedMoment B node5297 node5297Labels := rfl
  simpa [nodeValue5297, Sparse.eval] using hc.symm

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

theorem zero5371 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5371 node5371Labels = 0 := by
  exact mixedMoment_order_one B hB node5371 node5371Labels 1
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

theorem sound5355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5355 node5355Labels = Sparse.eval nodeValue5355 (mixedVector B) := by
  have h := singleton5355 B _hB
  rw [sound3693 B _hB _hF, sound3770 B _hB _hF] at h
  norm_num [nodeValue5355, nodeValue3693, nodeValue3770, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5371 node5371Labels = Sparse.eval nodeValue5371 (mixedVector B) := by
  simpa only [nodeValue5371, Sparse.eval_nil] using zero5371 B _hB _hF

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

theorem sound5376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5376 node5376Labels = Sparse.eval nodeValue5376 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5376) = mixedMoment B node5376 node5376Labels := rfl
  simpa [nodeValue5376, Sparse.eval] using hc.symm

theorem sound5390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5390 node5390Labels = Sparse.eval nodeValue5390 (mixedVector B) := by
  have h := singleton5390 B _hB
  rw [sound3741 B _hB _hF, sound3894 B _hB _hF] at h
  norm_num [nodeValue5390, nodeValue3741, nodeValue3894, Sparse.eval] at h ⊢
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

theorem sourceEq2526 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2526 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2526 + difference 0 1) (sourceB2526 + difference 1 0) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA2526 + difference 0 1) (sourceB2526 + difference 1 0) sourceC2526) = raw34817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34817; decide +kernel
    rw [ha]
    exact (canonical34817 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2526 + difference 0 2) (sourceB2526 + difference 2 0) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2526 + difference 0 2) (sourceB2526 + difference 2 0) sourceC2526) = raw34818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34818; decide +kernel
    rw [ha]
    exact (canonical34818 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2526 + difference 0 3) (sourceB2526 + difference 3 0) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2526 + difference 0 3) (sourceB2526 + difference 3 0) sourceC2526) = raw34819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34819; decide +kernel
    rw [ha]
    exact (canonical34819 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2526 + difference 0 4) (sourceB2526 + difference 4 0) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2526 + difference 0 4) (sourceB2526 + difference 4 0) sourceC2526) = raw34820 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34820; decide +kernel
    rw [ha]
    exact (canonical34820 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2526 + difference 0 5) (sourceB2526 + difference 5 0) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2526 + difference 0 5) (sourceB2526 + difference 5 0) sourceC2526) = raw34821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34821; decide +kernel
    rw [ha]
    exact (canonical34821 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2526 + difference 1 0) (sourceB2526 + difference 0 1) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5297) := by
    have ha : (tripleCharges (sourceA2526 + difference 1 0) (sourceB2526 + difference 0 1) sourceC2526) = raw34822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34822; decide +kernel
    rw [ha]
    exact (canonical34822 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2526 + difference 1 2) (sourceB2526 + difference 2 1) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA2526 + difference 1 2) (sourceB2526 + difference 2 1) sourceC2526) = raw34823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34823; decide +kernel
    rw [ha]
    exact (canonical34823 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2526 + difference 1 3) (sourceB2526 + difference 3 1) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA2526 + difference 1 3) (sourceB2526 + difference 3 1) sourceC2526) = raw34824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34824; decide +kernel
    rw [ha]
    exact (canonical34824 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2526 + difference 1 4) (sourceB2526 + difference 4 1) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5235) := by
    have ha : (tripleCharges (sourceA2526 + difference 1 4) (sourceB2526 + difference 4 1) sourceC2526) = raw34825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34825; decide +kernel
    rw [ha]
    exact (canonical34825 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2526 + difference 1 5) (sourceB2526 + difference 5 1) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2526 + difference 1 5) (sourceB2526 + difference 5 1) sourceC2526) = raw34826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34826; decide +kernel
    rw [ha]
    exact (canonical34826 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2526 + difference 2 0) (sourceB2526 + difference 0 2) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA2526 + difference 2 0) (sourceB2526 + difference 0 2) sourceC2526) = raw34827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34827; decide +kernel
    rw [ha]
    exact (canonical34827 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2526 + difference 2 1) (sourceB2526 + difference 1 2) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2526 + difference 2 1) (sourceB2526 + difference 1 2) sourceC2526) = raw34828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34828; decide +kernel
    rw [ha]
    exact (canonical34828 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2526 + difference 2 3) (sourceB2526 + difference 3 2) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5376) := by
    have ha : (tripleCharges (sourceA2526 + difference 2 3) (sourceB2526 + difference 3 2) sourceC2526) = raw34829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34829; decide +kernel
    rw [ha]
    exact (canonical34829 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2526 + difference 2 4) (sourceB2526 + difference 4 2) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA2526 + difference 2 4) (sourceB2526 + difference 4 2) sourceC2526) = raw34830 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34830; decide +kernel
    rw [ha]
    exact (canonical34830 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2526 + difference 2 5) (sourceB2526 + difference 5 2) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2526 + difference 2 5) (sourceB2526 + difference 5 2) sourceC2526) = raw34831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34831; decide +kernel
    rw [ha]
    exact (canonical34831 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2526 + difference 3 0) (sourceB2526 + difference 0 3) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA2526 + difference 3 0) (sourceB2526 + difference 0 3) sourceC2526) = raw34832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34832; decide +kernel
    rw [ha]
    exact (canonical34832 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2526 + difference 3 1) (sourceB2526 + difference 1 3) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2526 + difference 3 1) (sourceB2526 + difference 1 3) sourceC2526) = raw34833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34833; decide +kernel
    rw [ha]
    exact (canonical34833 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2526 + difference 3 2) (sourceB2526 + difference 2 3) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5376) := by
    have ha : (tripleCharges (sourceA2526 + difference 3 2) (sourceB2526 + difference 2 3) sourceC2526) = raw34834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34834; decide +kernel
    rw [ha]
    exact (canonical34834 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2526 + difference 3 4) (sourceB2526 + difference 4 3) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA2526 + difference 3 4) (sourceB2526 + difference 4 3) sourceC2526) = raw34835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34835; decide +kernel
    rw [ha]
    exact (canonical34835 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2526 + difference 3 5) (sourceB2526 + difference 5 3) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2526 + difference 3 5) (sourceB2526 + difference 5 3) sourceC2526) = raw34836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34836; decide +kernel
    rw [ha]
    exact (canonical34836 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2526 + difference 4 0) (sourceB2526 + difference 0 4) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2526 + difference 4 0) (sourceB2526 + difference 0 4) sourceC2526) = raw34837 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34837; decide +kernel
    rw [ha]
    exact (canonical34837 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2526 + difference 4 1) (sourceB2526 + difference 1 4) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2526 + difference 4 1) (sourceB2526 + difference 1 4) sourceC2526) = raw34838 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34838; decide +kernel
    rw [ha]
    exact (canonical34838 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2526 + difference 4 2) (sourceB2526 + difference 2 4) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2526 + difference 4 2) (sourceB2526 + difference 2 4) sourceC2526) = raw34839 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34839; decide +kernel
    rw [ha]
    exact (canonical34839 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2526 + difference 4 3) (sourceB2526 + difference 3 4) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2526 + difference 4 3) (sourceB2526 + difference 3 4) sourceC2526) = raw34840 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34840; decide +kernel
    rw [ha]
    exact (canonical34840 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2526 + difference 4 5) (sourceB2526 + difference 5 4) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA2526 + difference 4 5) (sourceB2526 + difference 5 4) sourceC2526) = raw34841 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34841; decide +kernel
    rw [ha]
    exact (canonical34841 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2526 + difference 5 0) (sourceB2526 + difference 0 5) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5235) := by
    have ha : (tripleCharges (sourceA2526 + difference 5 0) (sourceB2526 + difference 0 5) sourceC2526) = raw34842 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34842; decide +kernel
    rw [ha]
    exact (canonical34842 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2526 + difference 5 1) (sourceB2526 + difference 1 5) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2526 + difference 5 1) (sourceB2526 + difference 1 5) sourceC2526) = raw34843 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34843; decide +kernel
    rw [ha]
    exact (canonical34843 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2526 + difference 5 2) (sourceB2526 + difference 2 5) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA2526 + difference 5 2) (sourceB2526 + difference 2 5) sourceC2526) = raw34844 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34844; decide +kernel
    rw [ha]
    exact (canonical34844 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2526 + difference 5 3) (sourceB2526 + difference 3 5) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA2526 + difference 5 3) (sourceB2526 + difference 3 5) sourceC2526) = raw34845 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34845; decide +kernel
    rw [ha]
    exact (canonical34845 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2526 + difference 5 4) (sourceB2526 + difference 4 5) sourceC2526) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5297) := by
    have ha : (tripleCharges (sourceA2526 + difference 5 4) (sourceB2526 + difference 4 5) sourceC2526) = raw34846 := by
      apply Matrix.ext; unfold tripleCharges sourceA2526 sourceB2526 sourceC2526 difference raw34846; decide +kernel
    rw [ha]
    exact (canonical34846 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2526 sourceB2526 sourceC2526
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2526, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2035 : Integer.Sparse.reindex keyMap MixedData.row2035 = numericRow2035 := by decide +kernel

theorem numericCheck2035 (x : Master → ℝ) : Integer.Sparse.eval numericRow2035 x =
    (6480 : ℝ) * reducedSource2035 x := by
  norm_num [numericRow2035, reducedSource2035, Integer.Sparse.eval, Sparse.eval, nodeValue5232, nodeValue5235, nodeValue5238, nodeValue5297, nodeValue5355, nodeValue5371, nodeValue5376, nodeValue5390] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2035 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2035 (mixedVector B) = 0 := by
  have h5232 : mixedVector B (Sum.inr 5232) = Sparse.eval nodeValue5232 (mixedVector B) := by
    change mixedMoment B node5232 node5232Labels = _
    exact sound5232 B hB hF
  have h5235 : mixedVector B (Sum.inr 5235) = Sparse.eval nodeValue5235 (mixedVector B) := by
    change mixedMoment B node5235 node5235Labels = _
    exact sound5235 B hB hF
  have h5238 : mixedVector B (Sum.inr 5238) = Sparse.eval nodeValue5238 (mixedVector B) := by
    change mixedMoment B node5238 node5238Labels = _
    exact sound5238 B hB hF
  have h5297 : mixedVector B (Sum.inr 5297) = Sparse.eval nodeValue5297 (mixedVector B) := by
    change mixedMoment B node5297 node5297Labels = _
    exact sound5297 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5371 : mixedVector B (Sum.inr 5371) = Sparse.eval nodeValue5371 (mixedVector B) := by
    change mixedMoment B node5371 node5371Labels = _
    exact sound5371 B hB hF
  have h5376 : mixedVector B (Sum.inr 5376) = Sparse.eval nodeValue5376 (mixedVector B) := by
    change mixedMoment B node5376 node5376Labels = _
    exact sound5376 B hB hF
  have h5390 : mixedVector B (Sum.inr 5390) = Sparse.eval nodeValue5390 (mixedVector B) := by
    change mixedMoment B node5390 node5390Labels = _
    exact sound5390 B hB hF
  simpa only [sourceForm2526, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5232, h5235, h5238, h5297, h5355, h5371, h5376, h5390, reducedSource2035] using sourceEq2526 B hB

theorem rowSound2035_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2035 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2035, numericCheck2035, reducedZero2035 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e_oai
