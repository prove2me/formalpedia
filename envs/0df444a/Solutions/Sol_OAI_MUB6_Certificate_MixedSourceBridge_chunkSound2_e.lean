-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:16:14.669227+00:00
-- url     : https://prove2.me/submissions/d3cb5058-1753-4682-ab04-ae85af20ae95

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E127
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Orthogonality
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- The finite orthogonality contraction underlying equation (same-matrix). -/
theorem weighted_contraction {H : CMatrix} (hH : IsHadamard H)
    (u v : Coord → ℂ) (i : Coord) :
    (∑ j, (∑ k, u k * H i k * conj (H j k)) *
      (∑ l, v l * conj (H i l) * H j l)) =
      6 * ∑ k, u k * v k := by
  have hexpand :
      (∑ j, (∑ k, u k * H i k * conj (H j k)) *
        (∑ l, v l * conj (H i l) * H j l)) =
      ∑ l, ∑ k, (u k * v l * H i k * conj (H i l)) *
        (∑ j, conj (H j k) * H j l) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  simp_rw [hH.column_orthogonal]
  have hunit (k : Coord) : H i k * conj (H i k) = 1 := by
    rw [Complex.mul_conj, hH.1]
    norm_num
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    u k * v k * H i k * conj (H i k) * 6 =
      6 * (u k * v k) * (H i k * conj (H i k)) := by ring
    _ = _ := by rw [hunit, mul_one]

theorem g_add_difference {H : CMatrix} (hH : IsHadamard H)
    (a : Charge) (i j : Coord) :
    g H (a + difference i j) = (6 : ℂ)⁻¹ *
      ∑ k, character (fun r => H r k) a * H i k * conj (H j k) := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [character_add _ (fun r => unit_ne_zero (hH.1 r k)),
    character_difference _ (fun r => hH.1 r k)]
  ring

/-- Source Lemma (basic), equation (same-matrix), for arbitrary integral charges. -/
theorem same_matrix_identity {H : CMatrix} (hH : IsHadamard H)
    (a b : Charge) (i : Coord) :
    ∑ j, g H (a + difference i j) * g H (b + difference j i) = g H (a + b) := by
  simp_rw [g_add_difference hH]
  have hexpand :
      (∑ j, ((6 : ℂ)⁻¹ * ∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
        ((6 : ℂ)⁻¹ * ∑ l, character (fun r => H r l) b * H j l * conj (H i l))) =
      (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
        (∑ j, (∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
          (∑ l, character (fun r => H r l) b * conj (H i l) * H j l)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he : (∑ l, character (fun r => H r l) b * H j l * conj (H i l)) =
        ∑ l, character (fun r => H r l) b * conj (H i l) * H j l := by
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [he]
    ring
  rw [hexpand, weighted_contraction hH]
  unfold g
  have hs : (∑ k, character (fun r => H r k) a * character (fun r => H r k) b) =
      ∑ k, character (fun r => H r k) (a + b) := by
    apply Finset.sum_congr rfl
    intro k _
    exact (character_add _ (fun r => unit_ne_zero (hH.1 r k)) a b).symm
  rw [hs]
  ring

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

theorem mixedIntegrand_two {l : ℕ} (B : Fin 7 → Basis) (a b : Charge)
    (s t : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (doubleCharges a b) ![s, t] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b := by
  simp [mixedIntegrand, doubleCharges, Fin.prod_univ_succ, rowFourier, g, character, sampledMatrix]

theorem mixedMoment_same {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference i j) (b + difference j i) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  rw [same_matrix_identity (sampledMatrix_isHadamard B hB r ρ _) a b i]

theorem mixedMoment_same_reversed {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference j i) (b + difference i j) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  have h := same_matrix_identity (sampledMatrix_isHadamard B hB r ρ (τ s)) b a i
  simpa only [mul_comm, add_comm] using congrArg
    (fun z => (z * g (sampledMatrix B r ρ (τ u)) c).re) h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3511 raw3511Labels = mixedMoment B node2285 node2285Labels := by
  calc
    mixedMoment B raw3511 raw3511Labels = mixedMoment B raw3511step0 raw3511step0Labels := by
      have hz : ∀ j, raw3511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3511step0 = (fun i j => raw3511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3511step0 raw3511; decide +kernel
      have hl : raw3511step0Labels = raw3511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3511 raw3511Labels permutation434 hz
    mixedMoment B raw3511step0 raw3511step0Labels = mixedMoment B raw3511step1 raw3511step1Labels := by
      have hz : ∀ j, raw3511step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3511step1 = (fun i j => raw3511step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3511step1 raw3511step0; decide +kernel
      have hl : raw3511step1Labels = raw3511step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3511step0 raw3511step0Labels permutation80 hz
    mixedMoment B raw3511step1 raw3511step1Labels = mixedMoment B raw3511step2 raw3511step2Labels := by
      have hz : ∀ j, raw3511step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3511step2 = (fun i j => raw3511step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3511step2 raw3511step1; decide +kernel
      have hl : raw3511step2Labels = raw3511step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3511step1 raw3511step1Labels permutation14 hz
    _ = mixedMoment B node2285 node2285Labels := by rfl

theorem canonical3512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3512 raw3512Labels = mixedMoment B node2063 node2063Labels := by
  calc
    mixedMoment B raw3512 raw3512Labels = mixedMoment B raw3512step0 raw3512step0Labels := by
      have hz : ∀ j, raw3512 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3512step0 = (fun i j => raw3512 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3512step0 raw3512; decide +kernel
      have hl : raw3512step0Labels = raw3512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3512 raw3512Labels permutation434 hz
    mixedMoment B raw3512step0 raw3512step0Labels = mixedMoment B raw3512step1 raw3512step1Labels := by
      have hz : ∀ j, raw3512step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3512step1 = (fun i j => raw3512step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3512step1 raw3512step0; decide +kernel
      have hl : raw3512step1Labels = raw3512step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3512step0 raw3512step0Labels permutation80 hz
    mixedMoment B raw3512step1 raw3512step1Labels = mixedMoment B raw3512step2 raw3512step2Labels := by
      have ha : raw3512step2 = (fun i j => raw3512step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3512step2 raw3512step1; decide +kernel
      have hl : raw3512step2Labels = raw3512step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3512step1 raw3512step1Labels permutation22 permutation4
    mixedMoment B raw3512step2 raw3512step2Labels = mixedMoment B raw3512step3 raw3512step3Labels := by
      have ha : raw3512step3 = -raw3512step2 := by apply Matrix.ext; change ∀ i j, raw3512step3 i j = -(raw3512step2 i j); unfold raw3512step3 raw3512step2; decide +kernel
      have hl : raw3512step3Labels = raw3512step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2063 node2063Labels := by rfl

theorem canonical3517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3517 raw3517Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw3517 raw3517Labels = mixedMoment B raw3517step0 raw3517step0Labels := by
      have hz : ∀ j, raw3517 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3517step0 = (fun i j => raw3517 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3517step0 raw3517; decide +kernel
      have hl : raw3517step0Labels = raw3517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517 raw3517Labels permutation590 hz
    mixedMoment B raw3517step0 raw3517step0Labels = mixedMoment B raw3517step1 raw3517step1Labels := by
      have hz : ∀ j, raw3517step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3517step1 = (fun i j => raw3517step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3517step1 raw3517step0; decide +kernel
      have hl : raw3517step1Labels = raw3517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step0 raw3517step0Labels permutation104 hz
    mixedMoment B raw3517step1 raw3517step1Labels = mixedMoment B raw3517step2 raw3517step2Labels := by
      have hz : ∀ j, raw3517step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3517step2 = (fun i j => raw3517step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3517step2 raw3517step1; decide +kernel
      have hl : raw3517step2Labels = raw3517step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step1 raw3517step1Labels permutation20 hz
    mixedMoment B raw3517step2 raw3517step2Labels = mixedMoment B raw3517step3 raw3517step3Labels := by
      have hz : ∀ j, raw3517step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3517step3 = (fun i j => raw3517step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3517step3 raw3517step2; decide +kernel
      have hl : raw3517step3Labels = raw3517step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step2 raw3517step2Labels permutation4 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

theorem canonical3518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3518 raw3518Labels = mixedMoment B node1067 node1067Labels := by
  calc
    mixedMoment B raw3518 raw3518Labels = mixedMoment B raw3518step0 raw3518step0Labels := by
      have hz : ∀ j, raw3518 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3518step0 = (fun i j => raw3518 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3518step0 raw3518; decide +kernel
      have hl : raw3518step0Labels = raw3518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3518 raw3518Labels permutation434 hz
    mixedMoment B raw3518step0 raw3518step0Labels = mixedMoment B raw3518step1 raw3518step1Labels := by
      have hz : ∀ j, raw3518step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3518step1 = (fun i j => raw3518step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3518step1 raw3518step0; decide +kernel
      have hl : raw3518step1Labels = raw3518step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3518step0 raw3518step0Labels permutation80 hz
    mixedMoment B raw3518step1 raw3518step1Labels = mixedMoment B raw3518step2 raw3518step2Labels := by
      have ha : raw3518step2 = (fun i j => raw3518step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3518step2 raw3518step1; decide +kernel
      have hl : raw3518step2Labels = raw3518step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3518step1 raw3518step1Labels permutation10 permutation2
    _ = mixedMoment B node1067 node1067Labels := by rfl

theorem canonical3522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3522 raw3522Labels = mixedMoment B node1069 node1069Labels := by
  calc
    mixedMoment B raw3522 raw3522Labels = mixedMoment B raw3522step0 raw3522step0Labels := by
      have hz : ∀ j, raw3522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3522step0 = (fun i j => raw3522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3522step0 raw3522; decide +kernel
      have hl : raw3522step0Labels = raw3522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3522 raw3522Labels permutation434 hz
    mixedMoment B raw3522step0 raw3522step0Labels = mixedMoment B raw3522step1 raw3522step1Labels := by
      have hz : ∀ j, raw3522step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3522step1 = (fun i j => raw3522step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3522step1 raw3522step0; decide +kernel
      have hl : raw3522step1Labels = raw3522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3522step0 raw3522step0Labels permutation80 hz
    mixedMoment B raw3522step1 raw3522step1Labels = mixedMoment B raw3522step2 raw3522step2Labels := by
      have hz : ∀ j, raw3522step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3522step2 = (fun i j => raw3522step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3522step2 raw3522step1; decide +kernel
      have hl : raw3522step2Labels = raw3522step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3522step1 raw3522step1Labels permutation14 hz
    _ = mixedMoment B node1069 node1069Labels := by rfl

theorem canonical3523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3523 raw3523Labels = mixedMoment B node2041 node2041Labels := by
  calc
    mixedMoment B raw3523 raw3523Labels = mixedMoment B raw3523step0 raw3523step0Labels := by
      have hz : ∀ j, raw3523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3523step0 = (fun i j => raw3523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3523step0 raw3523; decide +kernel
      have hl : raw3523step0Labels = raw3523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3523 raw3523Labels permutation434 hz
    mixedMoment B raw3523step0 raw3523step0Labels = mixedMoment B raw3523step1 raw3523step1Labels := by
      have ha : raw3523step1 = (fun i j => raw3523step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3523step1 raw3523step0; decide +kernel
      have hl : raw3523step1Labels = raw3523step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3523step0 raw3523step0Labels permutation40 permutation2
    _ = mixedMoment B node2041 node2041Labels := by rfl

theorem canonical3524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3524 raw3524Labels = mixedMoment B node2041 node2041Labels := by
  calc
    mixedMoment B raw3524 raw3524Labels = mixedMoment B raw3524step0 raw3524step0Labels := by
      have hz : ∀ j, raw3524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3524step0 = (fun i j => raw3524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3524step0 raw3524; decide +kernel
      have hl : raw3524step0Labels = raw3524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3524 raw3524Labels permutation346 hz
    mixedMoment B raw3524step0 raw3524step0Labels = mixedMoment B raw3524step1 raw3524step1Labels := by
      have ha : raw3524step1 = (fun i j => raw3524step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3524step1 raw3524step0; decide +kernel
      have hl : raw3524step1Labels = raw3524step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3524step0 raw3524step0Labels permutation40 permutation2
    _ = mixedMoment B node2041 node2041Labels := by rfl

theorem canonical3525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3525 raw3525Labels = mixedMoment B node1067 node1067Labels := by
  calc
    mixedMoment B raw3525 raw3525Labels = mixedMoment B raw3525step0 raw3525step0Labels := by
      have hz : ∀ j, raw3525 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3525step0 = (fun i j => raw3525 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3525step0 raw3525; decide +kernel
      have hl : raw3525step0Labels = raw3525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3525 raw3525Labels permutation434 hz
    mixedMoment B raw3525step0 raw3525step0Labels = mixedMoment B raw3525step1 raw3525step1Labels := by
      have hz : ∀ j, raw3525step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3525step1 = (fun i j => raw3525step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3525step1 raw3525step0; decide +kernel
      have hl : raw3525step1Labels = raw3525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3525step0 raw3525step0Labels permutation80 hz
    mixedMoment B raw3525step1 raw3525step1Labels = mixedMoment B raw3525step2 raw3525step2Labels := by
      have ha : raw3525step2 = (fun i j => raw3525step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3525step2 raw3525step1; decide +kernel
      have hl : raw3525step2Labels = raw3525step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3525step1 raw3525step1Labels permutation20 permutation4
    mixedMoment B raw3525step2 raw3525step2Labels = mixedMoment B raw3525step3 raw3525step3Labels := by
      have ha : raw3525step3 = -raw3525step2 := by apply Matrix.ext; change ∀ i j, raw3525step3 i j = -(raw3525step2 i j); unfold raw3525step3 raw3525step2; decide +kernel
      have hl : raw3525step3Labels = raw3525step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1067 node1067Labels := by rfl

theorem canonical3526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3526 raw3526Labels = mixedMoment B node2284 node2284Labels := by
  calc
    mixedMoment B raw3526 raw3526Labels = mixedMoment B raw3526step0 raw3526step0Labels := by
      have hz : ∀ j, raw3526 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3526step0 = (fun i j => raw3526 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3526step0 raw3526; decide +kernel
      have hl : raw3526step0Labels = raw3526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3526 raw3526Labels permutation434 hz
    mixedMoment B raw3526step0 raw3526step0Labels = mixedMoment B raw3526step1 raw3526step1Labels := by
      have hz : ∀ j, raw3526step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3526step1 = (fun i j => raw3526step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3526step1 raw3526step0; decide +kernel
      have hl : raw3526step1Labels = raw3526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3526step0 raw3526step0Labels permutation80 hz
    mixedMoment B raw3526step1 raw3526step1Labels = mixedMoment B raw3526step2 raw3526step2Labels := by
      have ha : raw3526step2 = (fun i j => raw3526step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3526step2 raw3526step1; decide +kernel
      have hl : raw3526step2Labels = raw3526step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3526step1 raw3526step1Labels permutation10 permutation2
    _ = mixedMoment B node2284 node2284Labels := by rfl

theorem canonical3527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3527 raw3527Labels = mixedMoment B node2041 node2041Labels := by
  calc
    mixedMoment B raw3527 raw3527Labels = mixedMoment B raw3527step0 raw3527step0Labels := by
      have hz : ∀ j, raw3527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3527step0 = (fun i j => raw3527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3527step0 raw3527; decide +kernel
      have hl : raw3527step0Labels = raw3527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3527 raw3527Labels permutation434 hz
    mixedMoment B raw3527step0 raw3527step0Labels = mixedMoment B raw3527step1 raw3527step1Labels := by
      have ha : raw3527step1 = (fun i j => raw3527step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3527step1 raw3527step0; decide +kernel
      have hl : raw3527step1Labels = raw3527step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3527step0 raw3527step0Labels permutation34 permutation2
    _ = mixedMoment B node2041 node2041Labels := by rfl

theorem canonical3528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3528 raw3528Labels = mixedMoment B node2041 node2041Labels := by
  calc
    mixedMoment B raw3528 raw3528Labels = mixedMoment B raw3528step0 raw3528step0Labels := by
      have hz : ∀ j, raw3528 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3528step0 = (fun i j => raw3528 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3528step0 raw3528; decide +kernel
      have hl : raw3528step0Labels = raw3528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3528 raw3528Labels permutation346 hz
    mixedMoment B raw3528step0 raw3528step0Labels = mixedMoment B raw3528step1 raw3528step1Labels := by
      have ha : raw3528step1 = (fun i j => raw3528step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3528step1 raw3528step0; decide +kernel
      have hl : raw3528step1Labels = raw3528step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3528step0 raw3528step0Labels permutation34 permutation2
    _ = mixedMoment B node2041 node2041Labels := by rfl

theorem canonical3529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3529 raw3529Labels = mixedMoment B node2063 node2063Labels := by
  calc
    mixedMoment B raw3529 raw3529Labels = mixedMoment B raw3529step0 raw3529step0Labels := by
      have hz : ∀ j, raw3529 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3529step0 = (fun i j => raw3529 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3529step0 raw3529; decide +kernel
      have hl : raw3529step0Labels = raw3529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3529 raw3529Labels permutation434 hz
    mixedMoment B raw3529step0 raw3529step0Labels = mixedMoment B raw3529step1 raw3529step1Labels := by
      have hz : ∀ j, raw3529step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3529step1 = (fun i j => raw3529step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3529step1 raw3529step0; decide +kernel
      have hl : raw3529step1Labels = raw3529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3529step0 raw3529step0Labels permutation80 hz
    _ = mixedMoment B node2063 node2063Labels := by rfl

theorem canonical3530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3530 raw3530Labels = mixedMoment B node1459 node1459Labels := by
  calc
    mixedMoment B raw3530 raw3530Labels = mixedMoment B raw3530step0 raw3530step0Labels := by
      have hz : ∀ j, raw3530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3530step0 = (fun i j => raw3530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3530step0 raw3530; decide +kernel
      have hl : raw3530step0Labels = raw3530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3530 raw3530Labels permutation434 hz
    mixedMoment B raw3530step0 raw3530step0Labels = mixedMoment B raw3530step1 raw3530step1Labels := by
      have hz : ∀ j, raw3530step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3530step1 = (fun i j => raw3530step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3530step1 raw3530step0; decide +kernel
      have hl : raw3530step1Labels = raw3530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3530step0 raw3530step0Labels permutation80 hz
    mixedMoment B raw3530step1 raw3530step1Labels = mixedMoment B raw3530step2 raw3530step2Labels := by
      have ha : raw3530step2 = (fun i j => raw3530step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3530step2 raw3530step1; decide +kernel
      have hl : raw3530step2Labels = raw3530step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3530step1 raw3530step1Labels permutation31 permutation2
    mixedMoment B raw3530step2 raw3530step2Labels = mixedMoment B raw3530step3 raw3530step3Labels := by
      have ha : raw3530step3 = -raw3530step2 := by apply Matrix.ext; change ∀ i j, raw3530step3 i j = -(raw3530step2 i j); unfold raw3530step3 raw3530step2; decide +kernel
      have hl : raw3530step3Labels = raw3530step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1459 node1459Labels := by rfl

theorem canonical3531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3531 raw3531Labels = mixedMoment B node1459 node1459Labels := by
  calc
    mixedMoment B raw3531 raw3531Labels = mixedMoment B raw3531step0 raw3531step0Labels := by
      have hz : ∀ j, raw3531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3531step0 = (fun i j => raw3531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3531step0 raw3531; decide +kernel
      have hl : raw3531step0Labels = raw3531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3531 raw3531Labels permutation434 hz
    mixedMoment B raw3531step0 raw3531step0Labels = mixedMoment B raw3531step1 raw3531step1Labels := by
      have hz : ∀ j, raw3531step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3531step1 = (fun i j => raw3531step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3531step1 raw3531step0; decide +kernel
      have hl : raw3531step1Labels = raw3531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3531step0 raw3531step0Labels permutation56 hz
    mixedMoment B raw3531step1 raw3531step1Labels = mixedMoment B raw3531step2 raw3531step2Labels := by
      have ha : raw3531step2 = (fun i j => raw3531step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3531step2 raw3531step1; decide +kernel
      have hl : raw3531step2Labels = raw3531step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3531step1 raw3531step1Labels permutation31 permutation2
    mixedMoment B raw3531step2 raw3531step2Labels = mixedMoment B raw3531step3 raw3531step3Labels := by
      have ha : raw3531step3 = -raw3531step2 := by apply Matrix.ext; change ∀ i j, raw3531step3 i j = -(raw3531step2 i j); unfold raw3531step3 raw3531step2; decide +kernel
      have hl : raw3531step3Labels = raw3531step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1459 node1459Labels := by rfl

theorem canonical3532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3532 raw3532Labels = mixedMoment B node1459 node1459Labels := by
  calc
    mixedMoment B raw3532 raw3532Labels = mixedMoment B raw3532step0 raw3532step0Labels := by
      have hz : ∀ j, raw3532 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3532step0 = (fun i j => raw3532 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3532step0 raw3532; decide +kernel
      have hl : raw3532step0Labels = raw3532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3532 raw3532Labels permutation346 hz
    mixedMoment B raw3532step0 raw3532step0Labels = mixedMoment B raw3532step1 raw3532step1Labels := by
      have hz : ∀ j, raw3532step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3532step1 = (fun i j => raw3532step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3532step1 raw3532step0; decide +kernel
      have hl : raw3532step1Labels = raw3532step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3532step0 raw3532step0Labels permutation56 hz
    mixedMoment B raw3532step1 raw3532step1Labels = mixedMoment B raw3532step2 raw3532step2Labels := by
      have ha : raw3532step2 = (fun i j => raw3532step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3532step2 raw3532step1; decide +kernel
      have hl : raw3532step2Labels = raw3532step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3532step1 raw3532step1Labels permutation31 permutation2
    mixedMoment B raw3532step2 raw3532step2Labels = mixedMoment B raw3532step3 raw3532step3Labels := by
      have ha : raw3532step3 = -raw3532step2 := by apply Matrix.ext; change ∀ i j, raw3532step3 i j = -(raw3532step2 i j); unfold raw3532step3 raw3532step2; decide +kernel
      have hl : raw3532step3Labels = raw3532step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1459 node1459Labels := by rfl

theorem canonical3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3533 raw3533Labels = mixedMoment B node1069 node1069Labels := by
  calc
    mixedMoment B raw3533 raw3533Labels = mixedMoment B raw3533step0 raw3533step0Labels := by
      have hz : ∀ j, raw3533 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3533step0 = (fun i j => raw3533 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3533step0 raw3533; decide +kernel
      have hl : raw3533step0Labels = raw3533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3533 raw3533Labels permutation434 hz
    mixedMoment B raw3533step0 raw3533step0Labels = mixedMoment B raw3533step1 raw3533step1Labels := by
      have hz : ∀ j, raw3533step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3533step1 = (fun i j => raw3533step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3533step1 raw3533step0; decide +kernel
      have hl : raw3533step1Labels = raw3533step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3533step0 raw3533step0Labels permutation80 hz
    mixedMoment B raw3533step1 raw3533step1Labels = mixedMoment B raw3533step2 raw3533step2Labels := by
      have hz : ∀ j, raw3533step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3533step2 = (fun i j => raw3533step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3533step2 raw3533step1; decide +kernel
      have hl : raw3533step2Labels = raw3533step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3533step1 raw3533step1Labels permutation14 hz
    mixedMoment B raw3533step2 raw3533step2Labels = mixedMoment B raw3533step3 raw3533step3Labels := by
      have ha : raw3533step3 = (fun i j => raw3533step2 (permutation4 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3533step3 raw3533step2; decide +kernel
      have hl : raw3533step3Labels = raw3533step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3533step2 raw3533step2Labels permutation4 permutation4
    mixedMoment B raw3533step3 raw3533step3Labels = mixedMoment B raw3533step4 raw3533step4Labels := by
      have ha : raw3533step4 = -raw3533step3 := by apply Matrix.ext; change ∀ i j, raw3533step4 i j = -(raw3533step3 i j); unfold raw3533step4 raw3533step3; decide +kernel
      have hl : raw3533step4Labels = raw3533step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1069 node1069Labels := by rfl

theorem canonical3564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3564 raw3564Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw3564 raw3564Labels = mixedMoment B raw3564step0 raw3564step0Labels := by
      have hz : ∀ j, raw3564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3564step0 = (fun i j => raw3564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3564step0 raw3564; decide +kernel
      have hl : raw3564step0Labels = raw3564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3564 raw3564Labels permutation346 hz
    mixedMoment B raw3564step0 raw3564step0Labels = mixedMoment B raw3564step1 raw3564step1Labels := by
      have ha : raw3564step1 = (fun i j => raw3564step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3564step1 raw3564step0; decide +kernel
      have hl : raw3564step1Labels = raw3564step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3564step0 raw3564step0Labels permutation145 permutation3
    mixedMoment B raw3564step1 raw3564step1Labels = mixedMoment B raw3564step2 raw3564step2Labels := by
      have ha : raw3564step2 = -raw3564step1 := by apply Matrix.ext; change ∀ i j, raw3564step2 i j = -(raw3564step1 i j); unfold raw3564step2 raw3564step1; decide +kernel
      have hl : raw3564step2Labels = raw3564step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2254 node2254Labels := by rfl

theorem canonical3565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3565 raw3565Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw3565 raw3565Labels = mixedMoment B raw3565step0 raw3565step0Labels := by
      have hz : ∀ j, raw3565 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3565step0 = (fun i j => raw3565 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3565step0 raw3565; decide +kernel
      have hl : raw3565step0Labels = raw3565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3565 raw3565Labels permutation265 hz
    mixedMoment B raw3565step0 raw3565step0Labels = mixedMoment B raw3565step1 raw3565step1Labels := by
      have ha : raw3565step1 = (fun i j => raw3565step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3565step1 raw3565step0; decide +kernel
      have hl : raw3565step1Labels = raw3565step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3565step0 raw3565step0Labels permutation145 permutation3
    mixedMoment B raw3565step1 raw3565step1Labels = mixedMoment B raw3565step2 raw3565step2Labels := by
      have ha : raw3565step2 = -raw3565step1 := by apply Matrix.ext; change ∀ i j, raw3565step2 i j = -(raw3565step1 i j); unfold raw3565step2 raw3565step1; decide +kernel
      have hl : raw3565step2Labels = raw3565step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2254 node2254Labels := by rfl

theorem canonical3566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3566 raw3566Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw3566 raw3566Labels = mixedMoment B raw3566step0 raw3566step0Labels := by
      have hz : ∀ j, raw3566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3566step0 = (fun i j => raw3566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3566step0 raw3566; decide +kernel
      have hl : raw3566step0Labels = raw3566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3566 raw3566Labels permutation346 hz
    mixedMoment B raw3566step0 raw3566step0Labels = mixedMoment B raw3566step1 raw3566step1Labels := by
      have hz : ∀ j, raw3566step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3566step1 = (fun i j => raw3566step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3566step1 raw3566step0; decide +kernel
      have hl : raw3566step1Labels = raw3566step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3566step0 raw3566step0Labels permutation56 hz
    mixedMoment B raw3566step1 raw3566step1Labels = mixedMoment B raw3566step2 raw3566step2Labels := by
      have ha : raw3566step2 = (fun i j => raw3566step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3566step2 raw3566step1; decide +kernel
      have hl : raw3566step2Labels = raw3566step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3566step1 raw3566step1Labels permutation31 permutation3
    mixedMoment B raw3566step2 raw3566step2Labels = mixedMoment B raw3566step3 raw3566step3Labels := by
      have ha : raw3566step3 = -raw3566step2 := by apply Matrix.ext; change ∀ i j, raw3566step3 i j = -(raw3566step2 i j); unfold raw3566step3 raw3566step2; decide +kernel
      have hl : raw3566step3Labels = raw3566step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2280 node2280Labels := by rfl

theorem canonical3567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3567 raw3567Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw3567 raw3567Labels = mixedMoment B raw3567step0 raw3567step0Labels := by
      have hz : ∀ j, raw3567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3567step0 = (fun i j => raw3567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3567step0 raw3567; decide +kernel
      have hl : raw3567step0Labels = raw3567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3567 raw3567Labels permutation346 hz
    mixedMoment B raw3567step0 raw3567step0Labels = mixedMoment B raw3567step1 raw3567step1Labels := by
      have hz : ∀ j, raw3567step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3567step1 = (fun i j => raw3567step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3567step1 raw3567step0; decide +kernel
      have hl : raw3567step1Labels = raw3567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3567step0 raw3567step0Labels permutation56 hz
    mixedMoment B raw3567step1 raw3567step1Labels = mixedMoment B raw3567step2 raw3567step2Labels := by
      have ha : raw3567step2 = (fun i j => raw3567step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3567step2 raw3567step1; decide +kernel
      have hl : raw3567step2Labels = raw3567step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3567step1 raw3567step1Labels permutation29 permutation3
    mixedMoment B raw3567step2 raw3567step2Labels = mixedMoment B raw3567step3 raw3567step3Labels := by
      have ha : raw3567step3 = -raw3567step2 := by apply Matrix.ext; change ∀ i j, raw3567step3 i j = -(raw3567step2 i j); unfold raw3567step3 raw3567step2; decide +kernel
      have hl : raw3567step3Labels = raw3567step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2267 node2267Labels := by rfl

theorem canonical3568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3568 raw3568Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw3568 raw3568Labels = mixedMoment B raw3568step0 raw3568step0Labels := by
      have hz : ∀ j, raw3568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3568step0 = (fun i j => raw3568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3568step0 raw3568; decide +kernel
      have hl : raw3568step0Labels = raw3568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3568 raw3568Labels permutation346 hz
    mixedMoment B raw3568step0 raw3568step0Labels = mixedMoment B raw3568step1 raw3568step1Labels := by
      have hz : ∀ j, raw3568step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3568step1 = (fun i j => raw3568step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3568step1 raw3568step0; decide +kernel
      have hl : raw3568step1Labels = raw3568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3568step0 raw3568step0Labels permutation56 hz
    mixedMoment B raw3568step1 raw3568step1Labels = mixedMoment B raw3568step2 raw3568step2Labels := by
      have ha : raw3568step2 = (fun i j => raw3568step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3568step2 raw3568step1; decide +kernel
      have hl : raw3568step2Labels = raw3568step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3568step1 raw3568step1Labels permutation12 permutation6
    mixedMoment B raw3568step2 raw3568step2Labels = mixedMoment B raw3568step3 raw3568step3Labels := by
      have ha : raw3568step3 = -raw3568step2 := by apply Matrix.ext; change ∀ i j, raw3568step3 i j = -(raw3568step2 i j); unfold raw3568step3 raw3568step2; decide +kernel
      have hl : raw3568step3Labels = raw3568step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical3569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3569 raw3569Labels = mixedMoment B node1355 node1355Labels := by
  calc
    mixedMoment B raw3569 raw3569Labels = mixedMoment B raw3569step0 raw3569step0Labels := by
      have hz : ∀ j, raw3569 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3569step0 = (fun i j => raw3569 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3569step0 raw3569; decide +kernel
      have hl : raw3569step0Labels = raw3569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3569 raw3569Labels permutation346 hz
    mixedMoment B raw3569step0 raw3569step0Labels = mixedMoment B raw3569step1 raw3569step1Labels := by
      have ha : raw3569step1 = (fun i j => raw3569step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3569step1 raw3569step0; decide +kernel
      have hl : raw3569step1Labels = raw3569step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3569step0 raw3569step0Labels permutation46 permutation3
    _ = mixedMoment B node1355 node1355Labels := by rfl

theorem canonical3570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3570 raw3570Labels = mixedMoment B node1903 node1903Labels := by
  calc
    mixedMoment B raw3570 raw3570Labels = mixedMoment B raw3570step0 raw3570step0Labels := by
      have ha : raw3570step0 = (fun i j => raw3570 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3570step0 raw3570; decide +kernel
      have hl : raw3570step0Labels = raw3570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3570 raw3570Labels permutation616 permutation3
    mixedMoment B raw3570step0 raw3570step0Labels = mixedMoment B raw3570step1 raw3570step1Labels := by
      have ha : raw3570step1 = -raw3570step0 := by apply Matrix.ext; change ∀ i j, raw3570step1 i j = -(raw3570step0 i j); unfold raw3570step1 raw3570step0; decide +kernel
      have hl : raw3570step1Labels = raw3570step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1903 node1903Labels := by rfl

theorem canonical3571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3571 raw3571Labels = mixedMoment B node1927 node1927Labels := by
  calc
    mixedMoment B raw3571 raw3571Labels = mixedMoment B raw3571step0 raw3571step0Labels := by
      have hz : ∀ j, raw3571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3571step0 = (fun i j => raw3571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3571step0 raw3571; decide +kernel
      have hl : raw3571step0Labels = raw3571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3571 raw3571Labels permutation346 hz
    mixedMoment B raw3571step0 raw3571step0Labels = mixedMoment B raw3571step1 raw3571step1Labels := by
      have ha : raw3571step1 = (fun i j => raw3571step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3571step1 raw3571step0; decide +kernel
      have hl : raw3571step1Labels = raw3571step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3571step0 raw3571step0Labels permutation139 permutation3
    mixedMoment B raw3571step1 raw3571step1Labels = mixedMoment B raw3571step2 raw3571step2Labels := by
      have ha : raw3571step2 = -raw3571step1 := by apply Matrix.ext; change ∀ i j, raw3571step2 i j = -(raw3571step1 i j); unfold raw3571step2 raw3571step1; decide +kernel
      have hl : raw3571step2Labels = raw3571step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1927 node1927Labels := by rfl

theorem canonical3572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3572 raw3572Labels = mixedMoment B node1916 node1916Labels := by
  calc
    mixedMoment B raw3572 raw3572Labels = mixedMoment B raw3572step0 raw3572step0Labels := by
      have hz : ∀ j, raw3572 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3572step0 = (fun i j => raw3572 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3572step0 raw3572; decide +kernel
      have hl : raw3572step0Labels = raw3572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3572 raw3572Labels permutation346 hz
    mixedMoment B raw3572step0 raw3572step0Labels = mixedMoment B raw3572step1 raw3572step1Labels := by
      have ha : raw3572step1 = (fun i j => raw3572step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3572step1 raw3572step0; decide +kernel
      have hl : raw3572step1Labels = raw3572step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3572step0 raw3572step0Labels permutation137 permutation3
    mixedMoment B raw3572step1 raw3572step1Labels = mixedMoment B raw3572step2 raw3572step2Labels := by
      have ha : raw3572step2 = -raw3572step1 := by apply Matrix.ext; change ∀ i j, raw3572step2 i j = -(raw3572step1 i j); unfold raw3572step2 raw3572step1; decide +kernel
      have hl : raw3572step2Labels = raw3572step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1916 node1916Labels := by rfl

theorem canonical3573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3573 raw3573Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw3573 raw3573Labels = mixedMoment B raw3573step0 raw3573step0Labels := by
      have hz : ∀ j, raw3573 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3573step0 = (fun i j => raw3573 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3573step0 raw3573; decide +kernel
      have hl : raw3573step0Labels = raw3573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3573 raw3573Labels permutation346 hz
    mixedMoment B raw3573step0 raw3573step0Labels = mixedMoment B raw3573step1 raw3573step1Labels := by
      have ha : raw3573step1 = (fun i j => raw3573step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3573step1 raw3573step0; decide +kernel
      have hl : raw3573step1Labels = raw3573step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3573step0 raw3573step0Labels permutation46 permutation3
    _ = mixedMoment B node3222 node3222Labels := by rfl

theorem canonical3574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3574 raw3574Labels = mixedMoment B node1355 node1355Labels := by
  calc
    mixedMoment B raw3574 raw3574Labels = mixedMoment B raw3574step0 raw3574step0Labels := by
      have hz : ∀ j, raw3574 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3574step0 = (fun i j => raw3574 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3574step0 raw3574; decide +kernel
      have hl : raw3574step0Labels = raw3574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3574 raw3574Labels permutation265 hz
    mixedMoment B raw3574step0 raw3574step0Labels = mixedMoment B raw3574step1 raw3574step1Labels := by
      have ha : raw3574step1 = (fun i j => raw3574step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3574step1 raw3574step0; decide +kernel
      have hl : raw3574step1Labels = raw3574step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3574step0 raw3574step0Labels permutation46 permutation3
    _ = mixedMoment B node1355 node1355Labels := by rfl

theorem canonical3575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3575 raw3575Labels = mixedMoment B node1903 node1903Labels := by
  calc
    mixedMoment B raw3575 raw3575Labels = mixedMoment B raw3575step0 raw3575step0Labels := by
      have ha : raw3575step0 = (fun i j => raw3575 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3575step0 raw3575; decide +kernel
      have hl : raw3575step0Labels = raw3575Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3575 raw3575Labels permutation640 permutation3
    mixedMoment B raw3575step0 raw3575step0Labels = mixedMoment B raw3575step1 raw3575step1Labels := by
      have ha : raw3575step1 = -raw3575step0 := by apply Matrix.ext; change ∀ i j, raw3575step1 i j = -(raw3575step0 i j); unfold raw3575step1 raw3575step0; decide +kernel
      have hl : raw3575step1Labels = raw3575step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1903 node1903Labels := by rfl

theorem canonical3576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3576 raw3576Labels = mixedMoment B node1927 node1927Labels := by
  calc
    mixedMoment B raw3576 raw3576Labels = mixedMoment B raw3576step0 raw3576step0Labels := by
      have hz : ∀ j, raw3576 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3576step0 = (fun i j => raw3576 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3576step0 raw3576; decide +kernel
      have hl : raw3576step0Labels = raw3576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3576 raw3576Labels permutation265 hz
    mixedMoment B raw3576step0 raw3576step0Labels = mixedMoment B raw3576step1 raw3576step1Labels := by
      have ha : raw3576step1 = (fun i j => raw3576step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3576step1 raw3576step0; decide +kernel
      have hl : raw3576step1Labels = raw3576step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3576step0 raw3576step0Labels permutation139 permutation3
    mixedMoment B raw3576step1 raw3576step1Labels = mixedMoment B raw3576step2 raw3576step2Labels := by
      have ha : raw3576step2 = -raw3576step1 := by apply Matrix.ext; change ∀ i j, raw3576step2 i j = -(raw3576step1 i j); unfold raw3576step2 raw3576step1; decide +kernel
      have hl : raw3576step2Labels = raw3576step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1927 node1927Labels := by rfl

theorem canonical3577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3577 raw3577Labels = mixedMoment B node1916 node1916Labels := by
  calc
    mixedMoment B raw3577 raw3577Labels = mixedMoment B raw3577step0 raw3577step0Labels := by
      have hz : ∀ j, raw3577 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3577step0 = (fun i j => raw3577 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3577step0 raw3577; decide +kernel
      have hl : raw3577step0Labels = raw3577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3577 raw3577Labels permutation265 hz
    mixedMoment B raw3577step0 raw3577step0Labels = mixedMoment B raw3577step1 raw3577step1Labels := by
      have ha : raw3577step1 = (fun i j => raw3577step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3577step1 raw3577step0; decide +kernel
      have hl : raw3577step1Labels = raw3577step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3577step0 raw3577step0Labels permutation137 permutation3
    mixedMoment B raw3577step1 raw3577step1Labels = mixedMoment B raw3577step2 raw3577step2Labels := by
      have ha : raw3577step2 = -raw3577step1 := by apply Matrix.ext; change ∀ i j, raw3577step2 i j = -(raw3577step1 i j); unfold raw3577step2 raw3577step1; decide +kernel
      have hl : raw3577step2Labels = raw3577step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1916 node1916Labels := by rfl

theorem canonical3578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3578 raw3578Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw3578 raw3578Labels = mixedMoment B raw3578step0 raw3578step0Labels := by
      have hz : ∀ j, raw3578 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3578step0 = (fun i j => raw3578 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3578step0 raw3578; decide +kernel
      have hl : raw3578step0Labels = raw3578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3578 raw3578Labels permutation265 hz
    mixedMoment B raw3578step0 raw3578step0Labels = mixedMoment B raw3578step1 raw3578step1Labels := by
      have ha : raw3578step1 = (fun i j => raw3578step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3578step1 raw3578step0; decide +kernel
      have hl : raw3578step1Labels = raw3578step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3578step0 raw3578step0Labels permutation46 permutation3
    _ = mixedMoment B node3222 node3222Labels := by rfl

theorem canonical3579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3579 raw3579Labels = mixedMoment B node1369 node1369Labels := by
  calc
    mixedMoment B raw3579 raw3579Labels = mixedMoment B raw3579step0 raw3579step0Labels := by
      have hz : ∀ j, raw3579 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3579step0 = (fun i j => raw3579 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3579step0 raw3579; decide +kernel
      have hl : raw3579step0Labels = raw3579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3579 raw3579Labels permutation346 hz
    mixedMoment B raw3579step0 raw3579step0Labels = mixedMoment B raw3579step1 raw3579step1Labels := by
      have hz : ∀ j, raw3579step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3579step1 = (fun i j => raw3579step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3579step1 raw3579step0; decide +kernel
      have hl : raw3579step1Labels = raw3579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3579step0 raw3579step0Labels permutation56 hz
    mixedMoment B raw3579step1 raw3579step1Labels = mixedMoment B raw3579step2 raw3579step2Labels := by
      have ha : raw3579step2 = (fun i j => raw3579step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3579step2 raw3579step1; decide +kernel
      have hl : raw3579step2Labels = raw3579step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3579step1 raw3579step1Labels permutation10 permutation3
    _ = mixedMoment B node1369 node1369Labels := by rfl

theorem canonical3580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3580 raw3580Labels = mixedMoment B node2037 node2037Labels := by
  calc
    mixedMoment B raw3580 raw3580Labels = mixedMoment B raw3580step0 raw3580step0Labels := by
      have hz : ∀ j, raw3580 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3580step0 = (fun i j => raw3580 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3580step0 raw3580; decide +kernel
      have hl : raw3580step0Labels = raw3580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3580 raw3580Labels permutation346 hz
    mixedMoment B raw3580step0 raw3580step0Labels = mixedMoment B raw3580step1 raw3580step1Labels := by
      have ha : raw3580step1 = (fun i j => raw3580step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3580step1 raw3580step0; decide +kernel
      have hl : raw3580step1Labels = raw3580step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3580step0 raw3580step0Labels permutation145 permutation3
    mixedMoment B raw3580step1 raw3580step1Labels = mixedMoment B raw3580step2 raw3580step2Labels := by
      have ha : raw3580step2 = -raw3580step1 := by apply Matrix.ext; change ∀ i j, raw3580step2 i j = -(raw3580step1 i j); unfold raw3580step2 raw3580step1; decide +kernel
      have hl : raw3580step2Labels = raw3580step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2037 node2037Labels := by rfl

theorem canonical3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3581 raw3581Labels = mixedMoment B node2037 node2037Labels := by
  calc
    mixedMoment B raw3581 raw3581Labels = mixedMoment B raw3581step0 raw3581step0Labels := by
      have hz : ∀ j, raw3581 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3581step0 = (fun i j => raw3581 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3581step0 raw3581; decide +kernel
      have hl : raw3581step0Labels = raw3581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3581 raw3581Labels permutation265 hz
    mixedMoment B raw3581step0 raw3581step0Labels = mixedMoment B raw3581step1 raw3581step1Labels := by
      have ha : raw3581step1 = (fun i j => raw3581step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3581step1 raw3581step0; decide +kernel
      have hl : raw3581step1Labels = raw3581step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3581step0 raw3581step0Labels permutation145 permutation3
    mixedMoment B raw3581step1 raw3581step1Labels = mixedMoment B raw3581step2 raw3581step2Labels := by
      have ha : raw3581step2 = -raw3581step1 := by apply Matrix.ext; change ∀ i j, raw3581step2 i j = -(raw3581step1 i j); unfold raw3581step2 raw3581step1; decide +kernel
      have hl : raw3581step2Labels = raw3581step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2037 node2037Labels := by rfl

theorem canonical3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3582 raw3582Labels = mixedMoment B node2063 node2063Labels := by
  calc
    mixedMoment B raw3582 raw3582Labels = mixedMoment B raw3582step0 raw3582step0Labels := by
      have hz : ∀ j, raw3582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3582step0 = (fun i j => raw3582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3582step0 raw3582; decide +kernel
      have hl : raw3582step0Labels = raw3582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3582 raw3582Labels permutation346 hz
    mixedMoment B raw3582step0 raw3582step0Labels = mixedMoment B raw3582step1 raw3582step1Labels := by
      have hz : ∀ j, raw3582step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3582step1 = (fun i j => raw3582step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3582step1 raw3582step0; decide +kernel
      have hl : raw3582step1Labels = raw3582step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3582step0 raw3582step0Labels permutation56 hz
    mixedMoment B raw3582step1 raw3582step1Labels = mixedMoment B raw3582step2 raw3582step2Labels := by
      have ha : raw3582step2 = (fun i j => raw3582step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3582step2 raw3582step1; decide +kernel
      have hl : raw3582step2Labels = raw3582step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3582step1 raw3582step1Labels permutation29 permutation3
    mixedMoment B raw3582step2 raw3582step2Labels = mixedMoment B raw3582step3 raw3582step3Labels := by
      have ha : raw3582step3 = -raw3582step2 := by apply Matrix.ext; change ∀ i j, raw3582step3 i j = -(raw3582step2 i j); unfold raw3582step3 raw3582step2; decide +kernel
      have hl : raw3582step3Labels = raw3582step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2063 node2063Labels := by rfl

theorem canonical3583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3583 raw3583Labels = mixedMoment B node3224 node3224Labels := by
  calc
    mixedMoment B raw3583 raw3583Labels = mixedMoment B raw3583step0 raw3583step0Labels := by
      have hz : ∀ j, raw3583 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3583step0 = (fun i j => raw3583 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3583step0 raw3583; decide +kernel
      have hl : raw3583step0Labels = raw3583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3583 raw3583Labels permutation346 hz
    mixedMoment B raw3583step0 raw3583step0Labels = mixedMoment B raw3583step1 raw3583step1Labels := by
      have hz : ∀ j, raw3583step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3583step1 = (fun i j => raw3583step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3583step1 raw3583step0; decide +kernel
      have hl : raw3583step1Labels = raw3583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3583step0 raw3583step0Labels permutation56 hz
    mixedMoment B raw3583step1 raw3583step1Labels = mixedMoment B raw3583step2 raw3583step2Labels := by
      have ha : raw3583step2 = (fun i j => raw3583step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3583step2 raw3583step1; decide +kernel
      have hl : raw3583step2Labels = raw3583step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3583step1 raw3583step1Labels permutation10 permutation3
    _ = mixedMoment B node3224 node3224Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3584 raw3584Labels = mixedMoment B node1408 node1408Labels := by
  calc
    mixedMoment B raw3584 raw3584Labels = mixedMoment B raw3584step0 raw3584step0Labels := by
      have hz : ∀ j, raw3584 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3584step0 = (fun i j => raw3584 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3584step0 raw3584; decide +kernel
      have hl : raw3584step0Labels = raw3584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3584 raw3584Labels permutation346 hz
    mixedMoment B raw3584step0 raw3584step0Labels = mixedMoment B raw3584step1 raw3584step1Labels := by
      have hz : ∀ j, raw3584step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3584step1 = (fun i j => raw3584step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3584step1 raw3584step0; decide +kernel
      have hl : raw3584step1Labels = raw3584step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3584step0 raw3584step0Labels permutation56 hz
    mixedMoment B raw3584step1 raw3584step1Labels = mixedMoment B raw3584step2 raw3584step2Labels := by
      have ha : raw3584step2 = (fun i j => raw3584step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3584step2 raw3584step1; decide +kernel
      have hl : raw3584step2Labels = raw3584step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3584step1 raw3584step1Labels permutation8 permutation3
    _ = mixedMoment B node1408 node1408Labels := by rfl

theorem canonical3585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3585 raw3585Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw3585 raw3585Labels = mixedMoment B raw3585step0 raw3585step0Labels := by
      have hz : ∀ j, raw3585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3585step0 = (fun i j => raw3585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3585step0 raw3585; decide +kernel
      have hl : raw3585step0Labels = raw3585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3585 raw3585Labels permutation346 hz
    mixedMoment B raw3585step0 raw3585step0Labels = mixedMoment B raw3585step1 raw3585step1Labels := by
      have ha : raw3585step1 = (fun i j => raw3585step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3585step1 raw3585step0; decide +kernel
      have hl : raw3585step1Labels = raw3585step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3585step0 raw3585step0Labels permutation151 permutation3
    mixedMoment B raw3585step1 raw3585step1Labels = mixedMoment B raw3585step2 raw3585step2Labels := by
      have ha : raw3585step2 = -raw3585step1 := by apply Matrix.ext; change ∀ i j, raw3585step2 i j = -(raw3585step1 i j); unfold raw3585step2 raw3585step1; decide +kernel
      have hl : raw3585step2Labels = raw3585step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2092 node2092Labels := by rfl

theorem canonical3586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3586 raw3586Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw3586 raw3586Labels = mixedMoment B raw3586step0 raw3586step0Labels := by
      have hz : ∀ j, raw3586 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3586step0 = (fun i j => raw3586 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3586step0 raw3586; decide +kernel
      have hl : raw3586step0Labels = raw3586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3586 raw3586Labels permutation265 hz
    mixedMoment B raw3586step0 raw3586step0Labels = mixedMoment B raw3586step1 raw3586step1Labels := by
      have ha : raw3586step1 = (fun i j => raw3586step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3586step1 raw3586step0; decide +kernel
      have hl : raw3586step1Labels = raw3586step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3586step0 raw3586step0Labels permutation151 permutation3
    mixedMoment B raw3586step1 raw3586step1Labels = mixedMoment B raw3586step2 raw3586step2Labels := by
      have ha : raw3586step2 = -raw3586step1 := by apply Matrix.ext; change ∀ i j, raw3586step2 i j = -(raw3586step1 i j); unfold raw3586step2 raw3586step1; decide +kernel
      have hl : raw3586step2Labels = raw3586step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2092 node2092Labels := by rfl

theorem canonical3587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3587 raw3587Labels = mixedMoment B node2113 node2113Labels := by
  calc
    mixedMoment B raw3587 raw3587Labels = mixedMoment B raw3587step0 raw3587step0Labels := by
      have hz : ∀ j, raw3587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3587step0 = (fun i j => raw3587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3587step0 raw3587; decide +kernel
      have hl : raw3587step0Labels = raw3587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3587 raw3587Labels permutation346 hz
    mixedMoment B raw3587step0 raw3587step0Labels = mixedMoment B raw3587step1 raw3587step1Labels := by
      have hz : ∀ j, raw3587step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3587step1 = (fun i j => raw3587step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3587step1 raw3587step0; decide +kernel
      have hl : raw3587step1Labels = raw3587step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3587step0 raw3587step0Labels permutation56 hz
    mixedMoment B raw3587step1 raw3587step1Labels = mixedMoment B raw3587step2 raw3587step2Labels := by
      have ha : raw3587step2 = (fun i j => raw3587step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3587step2 raw3587step1; decide +kernel
      have hl : raw3587step2Labels = raw3587step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3587step1 raw3587step1Labels permutation31 permutation3
    mixedMoment B raw3587step2 raw3587step2Labels = mixedMoment B raw3587step3 raw3587step3Labels := by
      have ha : raw3587step3 = -raw3587step2 := by apply Matrix.ext; change ∀ i j, raw3587step3 i j = -(raw3587step2 i j); unfold raw3587step3 raw3587step2; decide +kernel
      have hl : raw3587step3Labels = raw3587step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2113 node2113Labels := by rfl

theorem canonical3588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3588 raw3588Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw3588 raw3588Labels = mixedMoment B raw3588step0 raw3588step0Labels := by
      have hz : ∀ j, raw3588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3588step0 = (fun i j => raw3588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3588step0 raw3588; decide +kernel
      have hl : raw3588step0Labels = raw3588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3588 raw3588Labels permutation346 hz
    mixedMoment B raw3588step0 raw3588step0Labels = mixedMoment B raw3588step1 raw3588step1Labels := by
      have hz : ∀ j, raw3588step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3588step1 = (fun i j => raw3588step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3588step1 raw3588step0; decide +kernel
      have hl : raw3588step1Labels = raw3588step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3588step0 raw3588step0Labels permutation56 hz
    mixedMoment B raw3588step1 raw3588step1Labels = mixedMoment B raw3588step2 raw3588step2Labels := by
      have ha : raw3588step2 = (fun i j => raw3588step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3588step2 raw3588step1; decide +kernel
      have hl : raw3588step2Labels = raw3588step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3588step1 raw3588step1Labels permutation12 permutation6
    mixedMoment B raw3588step2 raw3588step2Labels = mixedMoment B raw3588step3 raw3588step3Labels := by
      have ha : raw3588step3 = -raw3588step2 := by apply Matrix.ext; change ∀ i j, raw3588step3 i j = -(raw3588step2 i j); unfold raw3588step3 raw3588step2; decide +kernel
      have hl : raw3588step3Labels = raw3588step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3225 node3225Labels := by rfl

theorem canonical3589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3589 raw3589Labels = mixedMoment B node797 node797Labels := by
  calc
    mixedMoment B raw3589 raw3589Labels = mixedMoment B raw3589step0 raw3589step0Labels := by
      have hz : ∀ j, raw3589 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3589step0 = (fun i j => raw3589 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3589step0 raw3589; decide +kernel
      have hl : raw3589step0Labels = raw3589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3589 raw3589Labels permutation346 hz
    mixedMoment B raw3589step0 raw3589step0Labels = mixedMoment B raw3589step1 raw3589step1Labels := by
      have hz : ∀ j, raw3589step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3589step1 = (fun i j => raw3589step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3589step1 raw3589step0; decide +kernel
      have hl : raw3589step1Labels = raw3589step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3589step0 raw3589step0Labels permutation56 hz
    mixedMoment B raw3589step1 raw3589step1Labels = mixedMoment B raw3589step2 raw3589step2Labels := by
      have ha : raw3589step2 = (fun i j => raw3589step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3589step2 raw3589step1; decide +kernel
      have hl : raw3589step2Labels = raw3589step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3589step1 raw3589step1Labels permutation29 permutation3
    mixedMoment B raw3589step2 raw3589step2Labels = mixedMoment B raw3589step3 raw3589step3Labels := by
      have ha : raw3589step3 = -raw3589step2 := by apply Matrix.ext; change ∀ i j, raw3589step3 i j = -(raw3589step2 i j); unfold raw3589step3 raw3589step2; decide +kernel
      have hl : raw3589step3Labels = raw3589step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node797 node797Labels := by rfl

theorem canonical3590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3590 raw3590Labels = mixedMoment B node795 node795Labels := by
  calc
    mixedMoment B raw3590 raw3590Labels = mixedMoment B raw3590step0 raw3590step0Labels := by
      have hz : ∀ j, raw3590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3590step0 = (fun i j => raw3590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3590step0 raw3590; decide +kernel
      have hl : raw3590step0Labels = raw3590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3590 raw3590Labels permutation346 hz
    mixedMoment B raw3590step0 raw3590step0Labels = mixedMoment B raw3590step1 raw3590step1Labels := by
      have ha : raw3590step1 = (fun i j => raw3590step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3590step1 raw3590step0; decide +kernel
      have hl : raw3590step1Labels = raw3590step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3590step0 raw3590step0Labels permutation145 permutation3
    mixedMoment B raw3590step1 raw3590step1Labels = mixedMoment B raw3590step2 raw3590step2Labels := by
      have ha : raw3590step2 = -raw3590step1 := by apply Matrix.ext; change ∀ i j, raw3590step2 i j = -(raw3590step1 i j); unfold raw3590step2 raw3590step1; decide +kernel
      have hl : raw3590step2Labels = raw3590step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node795 node795Labels := by rfl

theorem canonical3591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3591 raw3591Labels = mixedMoment B node795 node795Labels := by
  calc
    mixedMoment B raw3591 raw3591Labels = mixedMoment B raw3591step0 raw3591step0Labels := by
      have hz : ∀ j, raw3591 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3591step0 = (fun i j => raw3591 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3591step0 raw3591; decide +kernel
      have hl : raw3591step0Labels = raw3591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3591 raw3591Labels permutation265 hz
    mixedMoment B raw3591step0 raw3591step0Labels = mixedMoment B raw3591step1 raw3591step1Labels := by
      have ha : raw3591step1 = (fun i j => raw3591step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3591step1 raw3591step0; decide +kernel
      have hl : raw3591step1Labels = raw3591step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3591step0 raw3591step0Labels permutation145 permutation3
    mixedMoment B raw3591step1 raw3591step1Labels = mixedMoment B raw3591step2 raw3591step2Labels := by
      have ha : raw3591step2 = -raw3591step1 := by apply Matrix.ext; change ∀ i j, raw3591step2 i j = -(raw3591step1 i j); unfold raw3591step2 raw3591step1; decide +kernel
      have hl : raw3591step2Labels = raw3591step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node795 node795Labels := by rfl

theorem canonical3592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3592 raw3592Labels = mixedMoment B node829 node829Labels := by
  calc
    mixedMoment B raw3592 raw3592Labels = mixedMoment B raw3592step0 raw3592step0Labels := by
      have hz : ∀ j, raw3592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3592step0 = (fun i j => raw3592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3592step0 raw3592; decide +kernel
      have hl : raw3592step0Labels = raw3592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3592 raw3592Labels permutation346 hz
    mixedMoment B raw3592step0 raw3592step0Labels = mixedMoment B raw3592step1 raw3592step1Labels := by
      have hz : ∀ j, raw3592step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3592step1 = (fun i j => raw3592step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3592step1 raw3592step0; decide +kernel
      have hl : raw3592step1Labels = raw3592step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3592step0 raw3592step0Labels permutation56 hz
    mixedMoment B raw3592step1 raw3592step1Labels = mixedMoment B raw3592step2 raw3592step2Labels := by
      have ha : raw3592step2 = (fun i j => raw3592step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3592step2 raw3592step1; decide +kernel
      have hl : raw3592step2Labels = raw3592step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3592step1 raw3592step1Labels permutation31 permutation3
    mixedMoment B raw3592step2 raw3592step2Labels = mixedMoment B raw3592step3 raw3592step3Labels := by
      have ha : raw3592step3 = -raw3592step2 := by apply Matrix.ext; change ∀ i j, raw3592step3 i j = -(raw3592step2 i j); unfold raw3592step3 raw3592step2; decide +kernel
      have hl : raw3592step3Labels = raw3592step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node829 node829Labels := by rfl

theorem canonical3593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3593 raw3593Labels = mixedMoment B node814 node814Labels := by
  calc
    mixedMoment B raw3593 raw3593Labels = mixedMoment B raw3593step0 raw3593step0Labels := by
      have hz : ∀ j, raw3593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3593step0 = (fun i j => raw3593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3593step0 raw3593; decide +kernel
      have hl : raw3593step0Labels = raw3593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3593 raw3593Labels permutation346 hz
    mixedMoment B raw3593step0 raw3593step0Labels = mixedMoment B raw3593step1 raw3593step1Labels := by
      have hz : ∀ j, raw3593step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3593step1 = (fun i j => raw3593step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3593step1 raw3593step0; decide +kernel
      have hl : raw3593step1Labels = raw3593step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3593step0 raw3593step0Labels permutation56 hz
    mixedMoment B raw3593step1 raw3593step1Labels = mixedMoment B raw3593step2 raw3593step2Labels := by
      have ha : raw3593step2 = (fun i j => raw3593step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3593step2 raw3593step1; decide +kernel
      have hl : raw3593step2Labels = raw3593step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3593step1 raw3593step1Labels permutation29 permutation3
    mixedMoment B raw3593step2 raw3593step2Labels = mixedMoment B raw3593step3 raw3593step3Labels := by
      have ha : raw3593step3 = -raw3593step2 := by apply Matrix.ext; change ∀ i j, raw3593step3 i j = -(raw3593step2 i j); unfold raw3593step3 raw3593step2; decide +kernel
      have hl : raw3593step3Labels = raw3593step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node814 node814Labels := by rfl

theorem canonical3624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3624 raw3624Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw3624 raw3624Labels = mixedMoment B raw3624step0 raw3624step0Labels := by
      have hz : ∀ j, raw3624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3624step0 = (fun i j => raw3624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3624step0 raw3624; decide +kernel
      have hl : raw3624step0Labels = raw3624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3624 raw3624Labels permutation346 hz
    mixedMoment B raw3624step0 raw3624step0Labels = mixedMoment B raw3624step1 raw3624step1Labels := by
      have hz : ∀ j, raw3624step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3624step1 = (fun i j => raw3624step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3624step1 raw3624step0; decide +kernel
      have hl : raw3624step1Labels = raw3624step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3624step0 raw3624step0Labels permutation56 hz
    _ = mixedMoment B node2255 node2255Labels := by rfl

theorem canonical3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3625 raw3625Labels = mixedMoment B node3156 node3156Labels := by
  calc
    mixedMoment B raw3625 raw3625Labels = mixedMoment B raw3625step0 raw3625step0Labels := by
      have hz : ∀ j, raw3625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3625step0 = (fun i j => raw3625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3625step0 raw3625; decide +kernel
      have hl : raw3625step0Labels = raw3625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3625 raw3625Labels permutation346 hz
    mixedMoment B raw3625step0 raw3625step0Labels = mixedMoment B raw3625step1 raw3625step1Labels := by
      have ha : raw3625step1 = (fun i j => raw3625step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3625step1 raw3625step0; decide +kernel
      have hl : raw3625step1Labels = raw3625step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3625step0 raw3625step0Labels permutation128 permutation4
    _ = mixedMoment B node3156 node3156Labels := by rfl

theorem canonical3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3626 raw3626Labels = mixedMoment B node3156 node3156Labels := by
  calc
    mixedMoment B raw3626 raw3626Labels = mixedMoment B raw3626step0 raw3626step0Labels := by
      have hz : ∀ j, raw3626 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3626step0 = (fun i j => raw3626 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3626step0 raw3626; decide +kernel
      have hl : raw3626step0Labels = raw3626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3626 raw3626Labels permutation265 hz
    mixedMoment B raw3626step0 raw3626step0Labels = mixedMoment B raw3626step1 raw3626step1Labels := by
      have ha : raw3626step1 = (fun i j => raw3626step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3626step1 raw3626step0; decide +kernel
      have hl : raw3626step1Labels = raw3626step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3626step0 raw3626step0Labels permutation128 permutation4
    _ = mixedMoment B node3156 node3156Labels := by rfl

theorem canonical3627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3627 raw3627Labels = mixedMoment B node3161 node3161Labels := by
  calc
    mixedMoment B raw3627 raw3627Labels = mixedMoment B raw3627step0 raw3627step0Labels := by
      have hz : ∀ j, raw3627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3627step0 = (fun i j => raw3627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3627step0 raw3627; decide +kernel
      have hl : raw3627step0Labels = raw3627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3627 raw3627Labels permutation346 hz
    mixedMoment B raw3627step0 raw3627step0Labels = mixedMoment B raw3627step1 raw3627step1Labels := by
      have hz : ∀ j, raw3627step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3627step1 = (fun i j => raw3627step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3627step1 raw3627step0; decide +kernel
      have hl : raw3627step1Labels = raw3627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3627step0 raw3627step0Labels permutation56 hz
    mixedMoment B raw3627step1 raw3627step1Labels = mixedMoment B raw3627step2 raw3627step2Labels := by
      have ha : raw3627step2 = (fun i j => raw3627step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3627step2 raw3627step1; decide +kernel
      have hl : raw3627step2Labels = raw3627step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3627step1 raw3627step1Labels permutation26 permutation4
    _ = mixedMoment B node3161 node3161Labels := by rfl

theorem canonical3628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3628 raw3628Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw3628 raw3628Labels = mixedMoment B raw3628step0 raw3628step0Labels := by
      have hz : ∀ j, raw3628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3628step0 = (fun i j => raw3628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3628step0 raw3628; decide +kernel
      have hl : raw3628step0Labels = raw3628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3628 raw3628Labels permutation346 hz
    mixedMoment B raw3628step0 raw3628step0Labels = mixedMoment B raw3628step1 raw3628step1Labels := by
      have hz : ∀ j, raw3628step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3628step1 = (fun i j => raw3628step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3628step1 raw3628step0; decide +kernel
      have hl : raw3628step1Labels = raw3628step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3628step0 raw3628step0Labels permutation56 hz
    mixedMoment B raw3628step1 raw3628step1Labels = mixedMoment B raw3628step2 raw3628step2Labels := by
      have ha : raw3628step2 = (fun i j => raw3628step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3628step2 raw3628step1; decide +kernel
      have hl : raw3628step2Labels = raw3628step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3628step1 raw3628step1Labels permutation22 permutation4
    mixedMoment B raw3628step2 raw3628step2Labels = mixedMoment B raw3628step3 raw3628step3Labels := by
      have ha : raw3628step3 = -raw3628step2 := by apply Matrix.ext; change ∀ i j, raw3628step3 i j = -(raw3628step2 i j); unfold raw3628step3 raw3628step2; decide +kernel
      have hl : raw3628step3Labels = raw3628step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2520 node2520Labels := by rfl

theorem canonical3629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3629 raw3629Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw3629 raw3629Labels = mixedMoment B raw3629step0 raw3629step0Labels := by
      have hz : ∀ j, raw3629 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3629step0 = (fun i j => raw3629 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3629step0 raw3629; decide +kernel
      have hl : raw3629step0Labels = raw3629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3629 raw3629Labels permutation346 hz
    mixedMoment B raw3629step0 raw3629step0Labels = mixedMoment B raw3629step1 raw3629step1Labels := by
      have hz : ∀ j, raw3629step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3629step1 = (fun i j => raw3629step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3629step1 raw3629step0; decide +kernel
      have hl : raw3629step1Labels = raw3629step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3629step0 raw3629step0Labels permutation56 hz
    _ = mixedMoment B node3626 node3626Labels := by rfl

theorem canonical3630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3630 raw3630Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw3630 raw3630Labels = mixedMoment B raw3630step0 raw3630step0Labels := by
      have hz : ∀ j, raw3630 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3630step0 = (fun i j => raw3630 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3630step0 raw3630; decide +kernel
      have hl : raw3630step0Labels = raw3630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3630 raw3630Labels permutation590 hz
    mixedMoment B raw3630step0 raw3630step0Labels = mixedMoment B raw3630step1 raw3630step1Labels := by
      have hz : ∀ j, raw3630step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3630step1 = (fun i j => raw3630step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3630step1 raw3630step0; decide +kernel
      have hl : raw3630step1Labels = raw3630step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3630step0 raw3630step0Labels permutation80 hz
    mixedMoment B raw3630step1 raw3630step1Labels = mixedMoment B raw3630step2 raw3630step2Labels := by
      have hz : ∀ j, raw3630step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3630step2 = (fun i j => raw3630step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3630step2 raw3630step1; decide +kernel
      have hl : raw3630step2Labels = raw3630step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3630step1 raw3630step1Labels permutation14 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical3631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3631 raw3631Labels = mixedMoment B node1029 node1029Labels := by
  calc
    mixedMoment B raw3631 raw3631Labels = mixedMoment B raw3631step0 raw3631step0Labels := by
      have hz : ∀ j, raw3631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3631step0 = (fun i j => raw3631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3631step0 raw3631; decide +kernel
      have hl : raw3631step0Labels = raw3631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3631 raw3631Labels permutation346 hz
    mixedMoment B raw3631step0 raw3631step0Labels = mixedMoment B raw3631step1 raw3631step1Labels := by
      have ha : raw3631step1 = (fun i j => raw3631step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3631step1 raw3631step0; decide +kernel
      have hl : raw3631step1Labels = raw3631step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3631step0 raw3631step0Labels permutation40 permutation2
    _ = mixedMoment B node1029 node1029Labels := by rfl

theorem canonical3632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3632 raw3632Labels = mixedMoment B node1029 node1029Labels := by
  calc
    mixedMoment B raw3632 raw3632Labels = mixedMoment B raw3632step0 raw3632step0Labels := by
      have hz : ∀ j, raw3632 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3632step0 = (fun i j => raw3632 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3632step0 raw3632; decide +kernel
      have hl : raw3632step0Labels = raw3632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3632 raw3632Labels permutation265 hz
    mixedMoment B raw3632step0 raw3632step0Labels = mixedMoment B raw3632step1 raw3632step1Labels := by
      have ha : raw3632step1 = (fun i j => raw3632step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3632step1 raw3632step0; decide +kernel
      have hl : raw3632step1Labels = raw3632step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3632step0 raw3632step0Labels permutation40 permutation2
    _ = mixedMoment B node1029 node1029Labels := by rfl

theorem canonical3633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3633 raw3633Labels = mixedMoment B node1061 node1061Labels := by
  calc
    mixedMoment B raw3633 raw3633Labels = mixedMoment B raw3633step0 raw3633step0Labels := by
      have hz : ∀ j, raw3633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3633step0 = (fun i j => raw3633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3633step0 raw3633; decide +kernel
      have hl : raw3633step0Labels = raw3633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3633 raw3633Labels permutation346 hz
    mixedMoment B raw3633step0 raw3633step0Labels = mixedMoment B raw3633step1 raw3633step1Labels := by
      have hz : ∀ j, raw3633step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3633step1 = (fun i j => raw3633step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3633step1 raw3633step0; decide +kernel
      have hl : raw3633step1Labels = raw3633step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3633step0 raw3633step0Labels permutation56 hz
    mixedMoment B raw3633step1 raw3633step1Labels = mixedMoment B raw3633step2 raw3633step2Labels := by
      have ha : raw3633step2 = (fun i j => raw3633step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3633step2 raw3633step1; decide +kernel
      have hl : raw3633step2Labels = raw3633step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3633step1 raw3633step1Labels permutation10 permutation2
    _ = mixedMoment B node1061 node1061Labels := by rfl

theorem canonical3634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3634 raw3634Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw3634 raw3634Labels = mixedMoment B raw3634step0 raw3634step0Labels := by
      have hz : ∀ j, raw3634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3634step0 = (fun i j => raw3634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3634step0 raw3634; decide +kernel
      have hl : raw3634step0Labels = raw3634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3634 raw3634Labels permutation346 hz
    mixedMoment B raw3634step0 raw3634step0Labels = mixedMoment B raw3634step1 raw3634step1Labels := by
      have hz : ∀ j, raw3634step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3634step1 = (fun i j => raw3634step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3634step1 raw3634step0; decide +kernel
      have hl : raw3634step1Labels = raw3634step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3634step0 raw3634step0Labels permutation56 hz
    _ = mixedMoment B node1047 node1047Labels := by rfl

theorem canonical3635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3635 raw3635Labels = mixedMoment B node1031 node1031Labels := by
  calc
    mixedMoment B raw3635 raw3635Labels = mixedMoment B raw3635step0 raw3635step0Labels := by
      have hz : ∀ j, raw3635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3635step0 = (fun i j => raw3635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3635step0 raw3635; decide +kernel
      have hl : raw3635step0Labels = raw3635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3635 raw3635Labels permutation346 hz
    mixedMoment B raw3635step0 raw3635step0Labels = mixedMoment B raw3635step1 raw3635step1Labels := by
      have hz : ∀ j, raw3635step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3635step1 = (fun i j => raw3635step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3635step1 raw3635step0; decide +kernel
      have hl : raw3635step1Labels = raw3635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3635step0 raw3635step0Labels permutation56 hz
    _ = mixedMoment B node1031 node1031Labels := by rfl

theorem canonical3636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3636 raw3636Labels = mixedMoment B node2013 node2013Labels := by
  calc
    mixedMoment B raw3636 raw3636Labels = mixedMoment B raw3636step0 raw3636step0Labels := by
      have ha : raw3636step0 = (fun i j => raw3636 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3636step0 raw3636; decide +kernel
      have hl : raw3636step0Labels = raw3636Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3636 raw3636Labels permutation184 permutation2
    _ = mixedMoment B node2013 node2013Labels := by rfl

theorem canonical3637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3637 raw3637Labels = mixedMoment B node2096 node2096Labels := by
  calc
    mixedMoment B raw3637 raw3637Labels = mixedMoment B raw3637step0 raw3637step0Labels := by
      have hz : ∀ j, raw3637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3637step0 = (fun i j => raw3637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3637step0 raw3637; decide +kernel
      have hl : raw3637step0Labels = raw3637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3637 raw3637Labels permutation346 hz
    mixedMoment B raw3637step0 raw3637step0Labels = mixedMoment B raw3637step1 raw3637step1Labels := by
      have ha : raw3637step1 = (fun i j => raw3637step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3637step1 raw3637step0; decide +kernel
      have hl : raw3637step1Labels = raw3637step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3637step0 raw3637step0Labels permutation40 permutation2
    _ = mixedMoment B node2096 node2096Labels := by rfl

theorem canonical3638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3638 raw3638Labels = mixedMoment B node2125 node2125Labels := by
  calc
    mixedMoment B raw3638 raw3638Labels = mixedMoment B raw3638step0 raw3638step0Labels := by
      have hz : ∀ j, raw3638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3638step0 = (fun i j => raw3638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3638step0 raw3638; decide +kernel
      have hl : raw3638step0Labels = raw3638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3638 raw3638Labels permutation346 hz
    mixedMoment B raw3638step0 raw3638step0Labels = mixedMoment B raw3638step1 raw3638step1Labels := by
      have ha : raw3638step1 = (fun i j => raw3638step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3638step1 raw3638step0; decide +kernel
      have hl : raw3638step1Labels = raw3638step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3638step0 raw3638step0Labels permutation46 permutation2
    _ = mixedMoment B node2125 node2125Labels := by rfl

theorem canonical3639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3639 raw3639Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw3639 raw3639Labels = mixedMoment B raw3639step0 raw3639step0Labels := by
      have hz : ∀ j, raw3639 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3639step0 = (fun i j => raw3639 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3639step0 raw3639; decide +kernel
      have hl : raw3639step0Labels = raw3639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3639 raw3639Labels permutation346 hz
    mixedMoment B raw3639step0 raw3639step0Labels = mixedMoment B raw3639step1 raw3639step1Labels := by
      have ha : raw3639step1 = (fun i j => raw3639step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3639step1 raw3639step0; decide +kernel
      have hl : raw3639step1Labels = raw3639step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3639step0 raw3639step0Labels permutation40 permutation2
    _ = mixedMoment B node2253 node2253Labels := by rfl

theorem canonical3640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3640 raw3640Labels = mixedMoment B node2013 node2013Labels := by
  calc
    mixedMoment B raw3640 raw3640Labels = mixedMoment B raw3640step0 raw3640step0Labels := by
      have ha : raw3640step0 = (fun i j => raw3640 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3640step0 raw3640; decide +kernel
      have hl : raw3640step0Labels = raw3640Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3640 raw3640Labels permutation160 permutation2
    _ = mixedMoment B node2013 node2013Labels := by rfl

theorem canonical3641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3641 raw3641Labels = mixedMoment B node2037 node2037Labels := by
  calc
    mixedMoment B raw3641 raw3641Labels = mixedMoment B raw3641step0 raw3641step0Labels := by
      have hz : ∀ j, raw3641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3641step0 = (fun i j => raw3641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3641step0 raw3641; decide +kernel
      have hl : raw3641step0Labels = raw3641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3641 raw3641Labels permutation346 hz
    mixedMoment B raw3641step0 raw3641step0Labels = mixedMoment B raw3641step1 raw3641step1Labels := by
      have ha : raw3641step1 = (fun i j => raw3641step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3641step1 raw3641step0; decide +kernel
      have hl : raw3641step1Labels = raw3641step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3641step0 raw3641step0Labels permutation34 permutation2
    _ = mixedMoment B node2037 node2037Labels := by rfl

theorem canonical3642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3642 raw3642Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw3642 raw3642Labels = mixedMoment B raw3642step0 raw3642step0Labels := by
      have hz : ∀ j, raw3642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3642step0 = (fun i j => raw3642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3642step0 raw3642; decide +kernel
      have hl : raw3642step0Labels = raw3642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3642 raw3642Labels permutation346 hz
    _ = mixedMoment B node2026 node2026Labels := by rfl

theorem canonical3643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3643 raw3643Labels = mixedMoment B node1458 node1458Labels := by
  calc
    mixedMoment B raw3643 raw3643Labels = mixedMoment B raw3643step0 raw3643step0Labels := by
      have hz : ∀ j, raw3643 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3643step0 = (fun i j => raw3643 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3643step0 raw3643; decide +kernel
      have hl : raw3643step0Labels = raw3643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3643 raw3643Labels permutation346 hz
    mixedMoment B raw3643step0 raw3643step0Labels = mixedMoment B raw3643step1 raw3643step1Labels := by
      have ha : raw3643step1 = (fun i j => raw3643step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3643step1 raw3643step0; decide +kernel
      have hl : raw3643step1Labels = raw3643step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3643step0 raw3643step0Labels permutation128 permutation4
    _ = mixedMoment B node1458 node1458Labels := by rfl

theorem canonical3644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3644 raw3644Labels = mixedMoment B node2037 node2037Labels := by
  calc
    mixedMoment B raw3644 raw3644Labels = mixedMoment B raw3644step0 raw3644step0Labels := by
      have hz : ∀ j, raw3644 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3644step0 = (fun i j => raw3644 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3644step0 raw3644; decide +kernel
      have hl : raw3644step0Labels = raw3644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3644 raw3644Labels permutation265 hz
    mixedMoment B raw3644step0 raw3644step0Labels = mixedMoment B raw3644step1 raw3644step1Labels := by
      have ha : raw3644step1 = (fun i j => raw3644step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3644step1 raw3644step0; decide +kernel
      have hl : raw3644step1Labels = raw3644step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3644step0 raw3644step0Labels permutation34 permutation2
    _ = mixedMoment B node2037 node2037Labels := by rfl

theorem canonical3645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3645 raw3645Labels = mixedMoment B node2136 node2136Labels := by
  calc
    mixedMoment B raw3645 raw3645Labels = mixedMoment B raw3645step0 raw3645step0Labels := by
      have hz : ∀ j, raw3645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3645step0 = (fun i j => raw3645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3645step0 raw3645; decide +kernel
      have hl : raw3645step0Labels = raw3645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3645 raw3645Labels permutation346 hz
    mixedMoment B raw3645step0 raw3645step0Labels = mixedMoment B raw3645step1 raw3645step1Labels := by
      have hz : ∀ j, raw3645step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3645step1 = (fun i j => raw3645step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3645step1 raw3645step0; decide +kernel
      have hl : raw3645step1Labels = raw3645step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3645step0 raw3645step0Labels permutation56 hz
    mixedMoment B raw3645step1 raw3645step1Labels = mixedMoment B raw3645step2 raw3645step2Labels := by
      have ha : raw3645step2 = (fun i j => raw3645step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3645step2 raw3645step1; decide +kernel
      have hl : raw3645step2Labels = raw3645step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3645step1 raw3645step1Labels permutation10 permutation2
    _ = mixedMoment B node2136 node2136Labels := by rfl

theorem canonical3646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3646 raw3646Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw3646 raw3646Labels = mixedMoment B raw3646step0 raw3646step0Labels := by
      have hz : ∀ j, raw3646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3646step0 = (fun i j => raw3646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3646step0 raw3646; decide +kernel
      have hl : raw3646step0Labels = raw3646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3646 raw3646Labels permutation346 hz
    mixedMoment B raw3646step0 raw3646step0Labels = mixedMoment B raw3646step1 raw3646step1Labels := by
      have hz : ∀ j, raw3646step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3646step1 = (fun i j => raw3646step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3646step1 raw3646step0; decide +kernel
      have hl : raw3646step1Labels = raw3646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3646step0 raw3646step0Labels permutation56 hz
    mixedMoment B raw3646step1 raw3646step1Labels = mixedMoment B raw3646step2 raw3646step2Labels := by
      have ha : raw3646step2 = (fun i j => raw3646step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3646step2 raw3646step1; decide +kernel
      have hl : raw3646step2Labels = raw3646step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3646step1 raw3646step1Labels permutation10 permutation2
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical3647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3647 raw3647Labels = mixedMoment B node2096 node2096Labels := by
  calc
    mixedMoment B raw3647 raw3647Labels = mixedMoment B raw3647step0 raw3647step0Labels := by
      have hz : ∀ j, raw3647 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3647step0 = (fun i j => raw3647 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3647step0 raw3647; decide +kernel
      have hl : raw3647step0Labels = raw3647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3647 raw3647Labels permutation265 hz
    mixedMoment B raw3647step0 raw3647step0Labels = mixedMoment B raw3647step1 raw3647step1Labels := by
      have ha : raw3647step1 = (fun i j => raw3647step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3647step1 raw3647step0; decide +kernel
      have hl : raw3647step1Labels = raw3647step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3647step0 raw3647step0Labels permutation40 permutation2
    _ = mixedMoment B node2096 node2096Labels := by rfl

theorem canonical3648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3648 raw3648Labels = mixedMoment B node2113 node2113Labels := by
  calc
    mixedMoment B raw3648 raw3648Labels = mixedMoment B raw3648step0 raw3648step0Labels := by
      have hz : ∀ j, raw3648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3648step0 = (fun i j => raw3648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3648step0 raw3648; decide +kernel
      have hl : raw3648step0Labels = raw3648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3648 raw3648Labels permutation346 hz
    mixedMoment B raw3648step0 raw3648step0Labels = mixedMoment B raw3648step1 raw3648step1Labels := by
      have hz : ∀ j, raw3648step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3648step1 = (fun i j => raw3648step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3648step1 raw3648step0; decide +kernel
      have hl : raw3648step1Labels = raw3648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3648step0 raw3648step0Labels permutation56 hz
    _ = mixedMoment B node2113 node2113Labels := by rfl

theorem canonical3649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3649 raw3649Labels = mixedMoment B node1462 node1462Labels := by
  calc
    mixedMoment B raw3649 raw3649Labels = mixedMoment B raw3649step0 raw3649step0Labels := by
      have hz : ∀ j, raw3649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3649step0 = (fun i j => raw3649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3649step0 raw3649; decide +kernel
      have hl : raw3649step0Labels = raw3649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3649 raw3649Labels permutation346 hz
    mixedMoment B raw3649step0 raw3649step0Labels = mixedMoment B raw3649step1 raw3649step1Labels := by
      have hz : ∀ j, raw3649step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3649step1 = (fun i j => raw3649step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3649step1 raw3649step0; decide +kernel
      have hl : raw3649step1Labels = raw3649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3649step0 raw3649step0Labels permutation56 hz
    mixedMoment B raw3649step1 raw3649step1Labels = mixedMoment B raw3649step2 raw3649step2Labels := by
      have ha : raw3649step2 = (fun i j => raw3649step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3649step2 raw3649step1; decide +kernel
      have hl : raw3649step2Labels = raw3649step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3649step1 raw3649step1Labels permutation26 permutation4
    _ = mixedMoment B node1462 node1462Labels := by rfl

theorem canonical3650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3650 raw3650Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw3650 raw3650Labels = mixedMoment B raw3650step0 raw3650step0Labels := by
      have hz : ∀ j, raw3650 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3650step0 = (fun i j => raw3650 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3650step0 raw3650; decide +kernel
      have hl : raw3650step0Labels = raw3650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3650 raw3650Labels permutation265 hz
    _ = mixedMoment B node2026 node2026Labels := by rfl

theorem canonical3651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3651 raw3651Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw3651 raw3651Labels = mixedMoment B raw3651step0 raw3651step0Labels := by
      have hz : ∀ j, raw3651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3651step0 = (fun i j => raw3651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3651step0 raw3651; decide +kernel
      have hl : raw3651step0Labels = raw3651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3651 raw3651Labels permutation346 hz
    mixedMoment B raw3651step0 raw3651step0Labels = mixedMoment B raw3651step1 raw3651step1Labels := by
      have hz : ∀ j, raw3651step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3651step1 = (fun i j => raw3651step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3651step1 raw3651step0; decide +kernel
      have hl : raw3651step1Labels = raw3651step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3651step0 raw3651step0Labels permutation56 hz
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical3652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3652 raw3652Labels = mixedMoment B node2125 node2125Labels := by
  calc
    mixedMoment B raw3652 raw3652Labels = mixedMoment B raw3652step0 raw3652step0Labels := by
      have hz : ∀ j, raw3652 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3652step0 = (fun i j => raw3652 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3652step0 raw3652; decide +kernel
      have hl : raw3652step0Labels = raw3652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3652 raw3652Labels permutation265 hz
    mixedMoment B raw3652step0 raw3652step0Labels = mixedMoment B raw3652step1 raw3652step1Labels := by
      have ha : raw3652step1 = (fun i j => raw3652step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3652step1 raw3652step0; decide +kernel
      have hl : raw3652step1Labels = raw3652step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3652step0 raw3652step0Labels permutation46 permutation2
    _ = mixedMoment B node2125 node2125Labels := by rfl

theorem canonical3653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3653 raw3653Labels = mixedMoment B node1461 node1461Labels := by
  calc
    mixedMoment B raw3653 raw3653Labels = mixedMoment B raw3653step0 raw3653step0Labels := by
      have hz : ∀ j, raw3653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3653step0 = (fun i j => raw3653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3653step0 raw3653; decide +kernel
      have hl : raw3653step0Labels = raw3653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3653 raw3653Labels permutation346 hz
    mixedMoment B raw3653step0 raw3653step0Labels = mixedMoment B raw3653step1 raw3653step1Labels := by
      have hz : ∀ j, raw3653step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3653step1 = (fun i j => raw3653step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3653step1 raw3653step0; decide +kernel
      have hl : raw3653step1Labels = raw3653step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3653step0 raw3653step0Labels permutation56 hz
    mixedMoment B raw3653step1 raw3653step1Labels = mixedMoment B raw3653step2 raw3653step2Labels := by
      have ha : raw3653step2 = (fun i j => raw3653step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3653step2 raw3653step1; decide +kernel
      have hl : raw3653step2Labels = raw3653step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3653step1 raw3653step1Labels permutation26 permutation4
    _ = mixedMoment B node1461 node1461Labels := by rfl

theorem canonical3654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3654 raw3654Labels = mixedMoment B node1458 node1458Labels := by
  calc
    mixedMoment B raw3654 raw3654Labels = mixedMoment B raw3654step0 raw3654step0Labels := by
      have hz : ∀ j, raw3654 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3654step0 = (fun i j => raw3654 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3654step0 raw3654; decide +kernel
      have hl : raw3654step0Labels = raw3654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3654 raw3654Labels permutation265 hz
    mixedMoment B raw3654step0 raw3654step0Labels = mixedMoment B raw3654step1 raw3654step1Labels := by
      have ha : raw3654step1 = (fun i j => raw3654step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3654step1 raw3654step0; decide +kernel
      have hl : raw3654step1Labels = raw3654step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3654step0 raw3654step0Labels permutation128 permutation4
    _ = mixedMoment B node1458 node1458Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3715 raw3715Labels = mixedMoment B node2284 node2284Labels := by
  calc
    mixedMoment B raw3715 raw3715Labels = mixedMoment B raw3715step0 raw3715step0Labels := by
      have hz : ∀ j, raw3715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3715step0 = (fun i j => raw3715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3715step0 raw3715; decide +kernel
      have hl : raw3715step0Labels = raw3715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3715 raw3715Labels permutation346 hz
    mixedMoment B raw3715step0 raw3715step0Labels = mixedMoment B raw3715step1 raw3715step1Labels := by
      have hz : ∀ j, raw3715step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3715step1 = (fun i j => raw3715step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3715step1 raw3715step0; decide +kernel
      have hl : raw3715step1Labels = raw3715step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3715step0 raw3715step0Labels permutation56 hz
    mixedMoment B raw3715step1 raw3715step1Labels = mixedMoment B raw3715step2 raw3715step2Labels := by
      have ha : raw3715step2 = (fun i j => raw3715step1 (permutation26 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3715step2 raw3715step1; decide +kernel
      have hl : raw3715step2Labels = raw3715step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3715step1 raw3715step1Labels permutation26 permutation2
    _ = mixedMoment B node2284 node2284Labels := by rfl

theorem canonical3716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3716 raw3716Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw3716 raw3716Labels = mixedMoment B raw3716step0 raw3716step0Labels := by
      have hz : ∀ j, raw3716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3716step0 = (fun i j => raw3716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3716step0 raw3716; decide +kernel
      have hl : raw3716step0Labels = raw3716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3716 raw3716Labels permutation346 hz
    mixedMoment B raw3716step0 raw3716step0Labels = mixedMoment B raw3716step1 raw3716step1Labels := by
      have ha : raw3716step1 = (fun i j => raw3716step0 (permutation136 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3716step1 raw3716step0; decide +kernel
      have hl : raw3716step1Labels = raw3716step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3716step0 raw3716step0Labels permutation136 permutation2
    _ = mixedMoment B node2055 node2055Labels := by rfl

theorem canonical3717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3717 raw3717Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw3717 raw3717Labels = mixedMoment B raw3717step0 raw3717step0Labels := by
      have hz : ∀ j, raw3717 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3717step0 = (fun i j => raw3717 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3717step0 raw3717; decide +kernel
      have hl : raw3717step0Labels = raw3717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3717 raw3717Labels permutation265 hz
    mixedMoment B raw3717step0 raw3717step0Labels = mixedMoment B raw3717step1 raw3717step1Labels := by
      have ha : raw3717step1 = (fun i j => raw3717step0 (permutation136 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3717step1 raw3717step0; decide +kernel
      have hl : raw3717step1Labels = raw3717step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3717step0 raw3717step0Labels permutation136 permutation2
    _ = mixedMoment B node2055 node2055Labels := by rfl

theorem canonical3718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3718 raw3718Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw3718 raw3718Labels = mixedMoment B raw3718step0 raw3718step0Labels := by
      have hz : ∀ j, raw3718 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3718step0 = (fun i j => raw3718 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3718step0 raw3718; decide +kernel
      have hl : raw3718step0Labels = raw3718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3718 raw3718Labels permutation434 hz
    mixedMoment B raw3718step0 raw3718step0Labels = mixedMoment B raw3718step1 raw3718step1Labels := by
      have hz : ∀ j, raw3718step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3718step1 = (fun i j => raw3718step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3718step1 raw3718step0; decide +kernel
      have hl : raw3718step1Labels = raw3718step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3718step0 raw3718step0Labels permutation80 hz
    mixedMoment B raw3718step1 raw3718step1Labels = mixedMoment B raw3718step2 raw3718step2Labels := by
      have hz : ∀ j, raw3718step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3718step2 = (fun i j => raw3718step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3718step2 raw3718step1; decide +kernel
      have hl : raw3718step2Labels = raw3718step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3718step1 raw3718step1Labels permutation14 hz
    mixedMoment B raw3718step2 raw3718step2Labels = mixedMoment B raw3718step3 raw3718step3Labels := by
      have ha : raw3718step3 = (fun i j => raw3718step2 (permutation6 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3718step3 raw3718step2; decide +kernel
      have hl : raw3718step3Labels = raw3718step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3718step2 raw3718step2Labels permutation6 permutation2
    _ = mixedMoment B node2294 node2294Labels := by rfl

theorem canonical3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3719 raw3719Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw3719 raw3719Labels = mixedMoment B raw3719step0 raw3719step0Labels := by
      have hz : ∀ j, raw3719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3719step0 = (fun i j => raw3719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3719step0 raw3719; decide +kernel
      have hl : raw3719step0Labels = raw3719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3719 raw3719Labels permutation346 hz
    mixedMoment B raw3719step0 raw3719step0Labels = mixedMoment B raw3719step1 raw3719step1Labels := by
      have hz : ∀ j, raw3719step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3719step1 = (fun i j => raw3719step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3719step1 raw3719step0; decide +kernel
      have hl : raw3719step1Labels = raw3719step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3719step0 raw3719step0Labels permutation56 hz
    mixedMoment B raw3719step1 raw3719step1Labels = mixedMoment B raw3719step2 raw3719step2Labels := by
      have ha : raw3719step2 = (fun i j => raw3719step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3719step2 raw3719step1; decide +kernel
      have hl : raw3719step2Labels = raw3719step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3719step1 raw3719step1Labels permutation29 permutation2
    _ = mixedMoment B node2290 node2290Labels := by rfl

theorem canonical3720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3720 raw3720Labels = mixedMoment B node1084 node1084Labels := by
  calc
    mixedMoment B raw3720 raw3720Labels = mixedMoment B raw3720step0 raw3720step0Labels := by
      have hz : ∀ j, raw3720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3720step0 = (fun i j => raw3720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3720step0 raw3720; decide +kernel
      have hl : raw3720step0Labels = raw3720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3720 raw3720Labels permutation346 hz
    mixedMoment B raw3720step0 raw3720step0Labels = mixedMoment B raw3720step1 raw3720step1Labels := by
      have hz : ∀ j, raw3720step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3720step1 = (fun i j => raw3720step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3720step1 raw3720step0; decide +kernel
      have hl : raw3720step1Labels = raw3720step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3720step0 raw3720step0Labels permutation56 hz
    mixedMoment B raw3720step1 raw3720step1Labels = mixedMoment B raw3720step2 raw3720step2Labels := by
      have ha : raw3720step2 = (fun i j => raw3720step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3720step2 raw3720step1; decide +kernel
      have hl : raw3720step2Labels = raw3720step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3720step1 raw3720step1Labels permutation28 permutation2
    _ = mixedMoment B node1084 node1084Labels := by rfl

theorem canonical3721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3721 raw3721Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw3721 raw3721Labels = mixedMoment B raw3721step0 raw3721step0Labels := by
      have hz : ∀ j, raw3721 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3721step0 = (fun i j => raw3721 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3721step0 raw3721; decide +kernel
      have hl : raw3721step0Labels = raw3721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721 raw3721Labels permutation520 hz
    mixedMoment B raw3721step0 raw3721step0Labels = mixedMoment B raw3721step1 raw3721step1Labels := by
      have hz : ∀ j, raw3721step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3721step1 = (fun i j => raw3721step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3721step1 raw3721step0; decide +kernel
      have hl : raw3721step1Labels = raw3721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step0 raw3721step0Labels permutation104 hz
    mixedMoment B raw3721step1 raw3721step1Labels = mixedMoment B raw3721step2 raw3721step2Labels := by
      have hz : ∀ j, raw3721step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3721step2 = (fun i j => raw3721step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3721step2 raw3721step1; decide +kernel
      have hl : raw3721step2Labels = raw3721step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step1 raw3721step1Labels permutation20 hz
    mixedMoment B raw3721step2 raw3721step2Labels = mixedMoment B raw3721step3 raw3721step3Labels := by
      have hz : ∀ j, raw3721step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3721step3 = (fun i j => raw3721step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3721step3 raw3721step2; decide +kernel
      have hl : raw3721step3Labels = raw3721step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step2 raw3721step2Labels permutation4 hz
    mixedMoment B raw3721step3 raw3721step3Labels = mixedMoment B raw3721step4 raw3721step4Labels := by
      have ha : raw3721step4 = (fun i j => raw3721step3 (permutation1 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3721step4 raw3721step3; decide +kernel
      have hl : raw3721step4Labels = raw3721step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3721step3 raw3721step3Labels permutation1 permutation0
    _ = mixedMoment B node4085 node4085Labels := by rfl

theorem canonical3722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3722 raw3722Labels = mixedMoment B node1066 node1066Labels := by
  calc
    mixedMoment B raw3722 raw3722Labels = mixedMoment B raw3722step0 raw3722step0Labels := by
      have hz : ∀ j, raw3722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3722step0 = (fun i j => raw3722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3722step0 raw3722; decide +kernel
      have hl : raw3722step0Labels = raw3722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3722 raw3722Labels permutation346 hz
    mixedMoment B raw3722step0 raw3722step0Labels = mixedMoment B raw3722step1 raw3722step1Labels := by
      have ha : raw3722step1 = (fun i j => raw3722step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3722step1 raw3722step0; decide +kernel
      have hl : raw3722step1Labels = raw3722step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3722step0 raw3722step0Labels permutation50 permutation4
    mixedMoment B raw3722step1 raw3722step1Labels = mixedMoment B raw3722step2 raw3722step2Labels := by
      have ha : raw3722step2 = -raw3722step1 := by apply Matrix.ext; change ∀ i j, raw3722step2 i j = -(raw3722step1 i j); unfold raw3722step2 raw3722step1; decide +kernel
      have hl : raw3722step2Labels = raw3722step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1066 node1066Labels := by rfl

theorem canonical3723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3723 raw3723Labels = mixedMoment B node1066 node1066Labels := by
  calc
    mixedMoment B raw3723 raw3723Labels = mixedMoment B raw3723step0 raw3723step0Labels := by
      have hz : ∀ j, raw3723 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3723step0 = (fun i j => raw3723 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3723step0 raw3723; decide +kernel
      have hl : raw3723step0Labels = raw3723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3723 raw3723Labels permutation265 hz
    mixedMoment B raw3723step0 raw3723step0Labels = mixedMoment B raw3723step1 raw3723step1Labels := by
      have ha : raw3723step1 = (fun i j => raw3723step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3723step1 raw3723step0; decide +kernel
      have hl : raw3723step1Labels = raw3723step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3723step0 raw3723step0Labels permutation50 permutation4
    mixedMoment B raw3723step1 raw3723step1Labels = mixedMoment B raw3723step2 raw3723step2Labels := by
      have ha : raw3723step2 = -raw3723step1 := by apply Matrix.ext; change ∀ i j, raw3723step2 i j = -(raw3723step1 i j); unfold raw3723step2 raw3723step1; decide +kernel
      have hl : raw3723step2Labels = raw3723step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1066 node1066Labels := by rfl

theorem canonical3724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3724 raw3724Labels = mixedMoment B node1068 node1068Labels := by
  calc
    mixedMoment B raw3724 raw3724Labels = mixedMoment B raw3724step0 raw3724step0Labels := by
      have hz : ∀ j, raw3724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3724step0 = (fun i j => raw3724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3724step0 raw3724; decide +kernel
      have hl : raw3724step0Labels = raw3724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3724 raw3724Labels permutation346 hz
    mixedMoment B raw3724step0 raw3724step0Labels = mixedMoment B raw3724step1 raw3724step1Labels := by
      have hz : ∀ j, raw3724step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3724step1 = (fun i j => raw3724step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3724step1 raw3724step0; decide +kernel
      have hl : raw3724step1Labels = raw3724step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3724step0 raw3724step0Labels permutation56 hz
    mixedMoment B raw3724step1 raw3724step1Labels = mixedMoment B raw3724step2 raw3724step2Labels := by
      have ha : raw3724step2 = (fun i j => raw3724step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3724step2 raw3724step1; decide +kernel
      have hl : raw3724step2Labels = raw3724step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3724step1 raw3724step1Labels permutation12 permutation4
    mixedMoment B raw3724step2 raw3724step2Labels = mixedMoment B raw3724step3 raw3724step3Labels := by
      have ha : raw3724step3 = -raw3724step2 := by apply Matrix.ext; change ∀ i j, raw3724step3 i j = -(raw3724step2 i j); unfold raw3724step3 raw3724step2; decide +kernel
      have hl : raw3724step3Labels = raw3724step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1068 node1068Labels := by rfl

theorem canonical3725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3725 raw3725Labels = mixedMoment B node1067 node1067Labels := by
  calc
    mixedMoment B raw3725 raw3725Labels = mixedMoment B raw3725step0 raw3725step0Labels := by
      have hz : ∀ j, raw3725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3725step0 = (fun i j => raw3725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3725step0 raw3725; decide +kernel
      have hl : raw3725step0Labels = raw3725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3725 raw3725Labels permutation346 hz
    mixedMoment B raw3725step0 raw3725step0Labels = mixedMoment B raw3725step1 raw3725step1Labels := by
      have hz : ∀ j, raw3725step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3725step1 = (fun i j => raw3725step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3725step1 raw3725step0; decide +kernel
      have hl : raw3725step1Labels = raw3725step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3725step0 raw3725step0Labels permutation56 hz
    mixedMoment B raw3725step1 raw3725step1Labels = mixedMoment B raw3725step2 raw3725step2Labels := by
      have ha : raw3725step2 = (fun i j => raw3725step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3725step2 raw3725step1; decide +kernel
      have hl : raw3725step2Labels = raw3725step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3725step1 raw3725step1Labels permutation12 permutation4
    mixedMoment B raw3725step2 raw3725step2Labels = mixedMoment B raw3725step3 raw3725step3Labels := by
      have ha : raw3725step3 = -raw3725step2 := by apply Matrix.ext; change ∀ i j, raw3725step3 i j = -(raw3725step2 i j); unfold raw3725step3 raw3725step2; decide +kernel
      have hl : raw3725step3Labels = raw3725step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1067 node1067Labels := by rfl

theorem canonical3726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3726 raw3726Labels = mixedMoment B node1084 node1084Labels := by
  calc
    mixedMoment B raw3726 raw3726Labels = mixedMoment B raw3726step0 raw3726step0Labels := by
      have hz : ∀ j, raw3726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3726step0 = (fun i j => raw3726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3726step0 raw3726; decide +kernel
      have hl : raw3726step0Labels = raw3726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3726 raw3726Labels permutation346 hz
    mixedMoment B raw3726step0 raw3726step0Labels = mixedMoment B raw3726step1 raw3726step1Labels := by
      have hz : ∀ j, raw3726step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3726step1 = (fun i j => raw3726step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3726step1 raw3726step0; decide +kernel
      have hl : raw3726step1Labels = raw3726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3726step0 raw3726step0Labels permutation56 hz
    mixedMoment B raw3726step1 raw3726step1Labels = mixedMoment B raw3726step2 raw3726step2Labels := by
      have ha : raw3726step2 = (fun i j => raw3726step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3726step2 raw3726step1; decide +kernel
      have hl : raw3726step2Labels = raw3726step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3726step1 raw3726step1Labels permutation9 permutation4
    mixedMoment B raw3726step2 raw3726step2Labels = mixedMoment B raw3726step3 raw3726step3Labels := by
      have ha : raw3726step3 = -raw3726step2 := by apply Matrix.ext; change ∀ i j, raw3726step3 i j = -(raw3726step2 i j); unfold raw3726step3 raw3726step2; decide +kernel
      have hl : raw3726step3Labels = raw3726step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1084 node1084Labels := by rfl

theorem canonical3727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3727 raw3727Labels = mixedMoment B node2040 node2040Labels := by
  calc
    mixedMoment B raw3727 raw3727Labels = mixedMoment B raw3727step0 raw3727step0Labels := by
      have ha : raw3727step0 = (fun i j => raw3727 (permutation623 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3727step0 raw3727; decide +kernel
      have hl : raw3727step0Labels = raw3727Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3727 raw3727Labels permutation623 permutation2
    _ = mixedMoment B node2040 node2040Labels := by rfl

theorem canonical3728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3728 raw3728Labels = mixedMoment B node2284 node2284Labels := by
  calc
    mixedMoment B raw3728 raw3728Labels = mixedMoment B raw3728step0 raw3728step0Labels := by
      have hz : ∀ j, raw3728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3728step0 = (fun i j => raw3728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3728step0 raw3728; decide +kernel
      have hl : raw3728step0Labels = raw3728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3728 raw3728Labels permutation434 hz
    mixedMoment B raw3728step0 raw3728step0Labels = mixedMoment B raw3728step1 raw3728step1Labels := by
      have hz : ∀ j, raw3728step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3728step1 = (fun i j => raw3728step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3728step1 raw3728step0; decide +kernel
      have hl : raw3728step1Labels = raw3728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3728step0 raw3728step0Labels permutation80 hz
    mixedMoment B raw3728step1 raw3728step1Labels = mixedMoment B raw3728step2 raw3728step2Labels := by
      have ha : raw3728step2 = (fun i j => raw3728step1 (permutation26 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3728step2 raw3728step1; decide +kernel
      have hl : raw3728step2Labels = raw3728step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3728step1 raw3728step1Labels permutation26 permutation2
    _ = mixedMoment B node2284 node2284Labels := by rfl

theorem canonical3729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3729 raw3729Labels = mixedMoment B node2283 node2283Labels := by
  calc
    mixedMoment B raw3729 raw3729Labels = mixedMoment B raw3729step0 raw3729step0Labels := by
      have hz : ∀ j, raw3729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3729step0 = (fun i j => raw3729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3729step0 raw3729; decide +kernel
      have hl : raw3729step0Labels = raw3729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3729 raw3729Labels permutation346 hz
    mixedMoment B raw3729step0 raw3729step0Labels = mixedMoment B raw3729step1 raw3729step1Labels := by
      have ha : raw3729step1 = (fun i j => raw3729step0 (permutation128 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3729step1 raw3729step0; decide +kernel
      have hl : raw3729step1Labels = raw3729step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3729step0 raw3729step0Labels permutation128 permutation2
    _ = mixedMoment B node2283 node2283Labels := by rfl

theorem canonical3730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3730 raw3730Labels = mixedMoment B node1066 node1066Labels := by
  calc
    mixedMoment B raw3730 raw3730Labels = mixedMoment B raw3730step0 raw3730step0Labels := by
      have hz : ∀ j, raw3730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3730step0 = (fun i j => raw3730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3730step0 raw3730; decide +kernel
      have hl : raw3730step0Labels = raw3730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3730 raw3730Labels permutation346 hz
    mixedMoment B raw3730step0 raw3730step0Labels = mixedMoment B raw3730step1 raw3730step1Labels := by
      have ha : raw3730step1 = (fun i j => raw3730step0 (permutation128 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3730step1 raw3730step0; decide +kernel
      have hl : raw3730step1Labels = raw3730step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3730step0 raw3730step0Labels permutation128 permutation2
    _ = mixedMoment B node1066 node1066Labels := by rfl

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

theorem canonical472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw472 raw472Labels = mixedMoment B node3224 node3224Labels := by
  calc
    mixedMoment B raw472 raw472Labels = mixedMoment B raw472step0 raw472step0Labels := by
      have ha : raw472step0 = (fun i j => raw472 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw472step0 raw472; decide +kernel
      have hl : raw472step0Labels = raw472Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw472 raw472Labels permutation8 permutation5
    mixedMoment B raw472step0 raw472step0Labels = mixedMoment B raw472step1 raw472step1Labels := by
      have ha : raw472step1 = raw472step0 := by apply Matrix.ext; unfold raw472step1 raw472step0; decide +kernel
      have hl : raw472step0Labels = labelEmbedding1 ∘ raw472step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw472step0 raw472step0Labels raw472step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3224 node3224Labels := by rfl

theorem canonical473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw473 raw473Labels = mixedMoment B node269 node269Labels := by
  calc
    mixedMoment B raw473 raw473Labels = mixedMoment B raw473step0 raw473step0Labels := by
      have ha : raw473step0 = (fun i j => raw473 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw473step0 raw473; decide +kernel
      have hl : raw473step0Labels = raw473Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw473 raw473Labels permutation8 permutation4
    _ = mixedMoment B node269 node269Labels := by rfl

theorem canonical474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw474 raw474Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw474 raw474Labels = mixedMoment B raw474step0 raw474step0Labels := by
      have ha : raw474step0 = (fun i j => raw474 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw474step0 raw474; decide +kernel
      have hl : raw474step0Labels = raw474Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw474 raw474Labels permutation8 permutation5
    mixedMoment B raw474step0 raw474step0Labels = mixedMoment B raw474step1 raw474step1Labels := by
      have ha : raw474step1 = raw474step0 := by apply Matrix.ext; unfold raw474step1 raw474step0; decide +kernel
      have hl : raw474step0Labels = labelEmbedding1 ∘ raw474step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw474step0 raw474step0Labels raw474step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3225 node3225Labels := by rfl

theorem canonical475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw475 raw475Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw475 raw475Labels = mixedMoment B raw475step0 raw475step0Labels := by
      have ha : raw475step0 = (fun i j => raw475 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw475step0 raw475; decide +kernel
      have hl : raw475step0Labels = raw475Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw475 raw475Labels permutation11 permutation6
    mixedMoment B raw475step0 raw475step0Labels = mixedMoment B raw475step1 raw475step1Labels := by
      have ha : raw475step1 = -raw475step0 := by apply Matrix.ext; change ∀ i j, raw475step1 i j = -(raw475step0 i j); unfold raw475step1 raw475step0; decide +kernel
      have hl : raw475step1Labels = raw475step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node268 node268Labels := by rfl

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

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical538 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw538 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw538 = injectiveMoment H raw538step0 := by
      have heq : raw538step0 = (fun i j => raw538 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw538 permutation28 permutation6
    _ = injectiveMoment H node215 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical553 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw553 = injectiveMoment H node204 := by
  calc
    injectiveMoment H raw553 = injectiveMoment H raw553step0 := by
      have heq : raw553step0 = (fun i j => raw553 (permutation31 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw553 permutation31 permutation6
    _ = injectiveMoment H node204 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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

theorem canonical918 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw918 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw918 = injectiveMoment H raw918step0 := by
      have hz : ∀ j, raw918 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw918step0 = (fun i j => raw918 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw918 permutation27 hz
    _ = injectiveMoment H node10 := by rfl

theorem canonical925 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw925 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw925 = injectiveMoment H raw925step0 := by
      have hz : ∀ j, raw925 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw925step0 = (fun i j => raw925 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw925 permutation27 hz
    injectiveMoment H raw925step0 = injectiveMoment H raw925step1 := by
      have heq : raw925step1 = (fun i j => raw925step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw925step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

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

theorem canonical8972 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8972 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8972 = injectiveMoment H raw8972step0 := by
      have hz : ∀ j, raw8972 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw8972step0 = (fun i j => raw8972 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8972 permutation21 hz
    injectiveMoment H raw8972step0 = injectiveMoment H raw8972step1 := by
      have hz : ∀ j, raw8972step0 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8972step1 = (fun i j => raw8972step0 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8972step0 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

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

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound37 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node37 = Sparse.eval value37 (momentVector H) := by
  have hc : momentVector H 13 = injectiveMoment H node37 := rfl
  simp [value37, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

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

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

theorem canonical4147 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4147 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw4147 = injectiveMoment H raw4147step0 := by
      have heq : raw4147step0 = -raw4147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4147).symm
    injectiveMoment H raw4147step0 = injectiveMoment H raw4147step1 := by
      have heq : raw4147step1 = (fun i j => raw4147step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4147step0 permutation8 permutation4
    _ = injectiveMoment H node37 := by rfl

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

theorem canonical4161 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4161 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4161 = injectiveMoment H raw4161step0 := by
      have heq : raw4161step0 = -raw4161 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4161).symm
    injectiveMoment H raw4161step0 = injectiveMoment H raw4161step1 := by
      have heq : raw4161step1 = (fun i j => raw4161step0 (permutation5 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4161step0 permutation5 permutation5
    _ = injectiveMoment H node36 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound204 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node204 = Sparse.eval value204 (momentVector H) := by
  have heq : pivotMatrix204 = (fun u v => node204 (pivotPermutation204 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node204 = injectiveMoment H pivotMatrix204 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix204 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix204 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix204 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix204 (0 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix204 (1 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix204 (1 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix204 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix204 (2 : Fin 3) = raw4147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4147 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node204 + (injectiveMoment H (mergeFirst pivotMatrix204 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix204 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix204 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value204, value37, value41, Sparse.eval] at hc ⊢
  linarith

theorem sound215 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node215 = Sparse.eval value215 (momentVector H) := by
  have heq : pivotMatrix215 = (fun u v => node215 (pivotPermutation215 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node215 = injectiveMoment H pivotMatrix215 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix215 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix215 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix215 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix215 (0 : Fin 3) = raw6870 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6870 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix215 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix215 (1 : Fin 3) = raw4161 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4161 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix215 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix215 (2 : Fin 3) = raw4147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4147 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node215 + (injectiveMoment H (mergeFirst pivotMatrix215 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix215 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix215 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value215, value36, value37, value63, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair268 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node268 node268Labels = Sparse.eval singlePairValue268 (familyPairVector B) := by
  have hp := single_label_three B hB node268
  have hl : node268Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node268 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node268 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node268 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node268 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node268 (EqualityPatterns.family3.label 1) = PairSemantics.raw918 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node268 PairSemantics.raw918; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical918 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node268 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node268 (EqualityPatterns.family3.label 2) = PairSemantics.raw9013 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node268 PairSemantics.raw9013; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9013 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node268 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node268 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node268 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node268 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value215 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node268 (EqualityPatterns.family3.label 4) = PairSemantics.raw538 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node268 PairSemantics.raw538; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical538 hH).trans (PairSemantics.sound215 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue268, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value215, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair269 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node269 node269Labels = Sparse.eval singlePairValue269 (familyPairVector B) := by
  have hp := single_label_three B hB node269
  have hl : node269Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node269 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node269 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node269 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node269 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node269 (EqualityPatterns.family3.label 1) = PairSemantics.raw925 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node269 PairSemantics.raw925; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical925 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node269 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node269 (EqualityPatterns.family3.label 2) = PairSemantics.raw8972 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node269 PairSemantics.raw8972; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8972 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node269 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node269 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node269 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node269 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value204 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node269 (EqualityPatterns.family3.label 4) = PairSemantics.raw553 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node269 PairSemantics.raw553; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical553 hH).trans (PairSemantics.sound204 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue269, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value204, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3224 node3224Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node269 node269Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw472 singletonSmall3224
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3224) = raw472Labels := by decide +kernel
  rw [hl, canonical472 B hB] at h
  have hc0 : mixedMoment B raw472 (Fin.cases (0 : Fin 1) singletonSmall3224) =
      mixedMoment B node269 node269Labels := by
    have ha : raw472 = raw473 := by apply Matrix.ext; unfold raw472 raw473; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3224 = raw473Labels := by decide +kernel
    rw [ha, hj, canonical473 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton3225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3225 node3225Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node268 node268Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw474 singletonSmall3225
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3225) = raw474Labels := by decide +kernel
  rw [hl, canonical474 B hB] at h
  have hc0 : mixedMoment B raw474 (Fin.cases (0 : Fin 1) singletonSmall3225) =
      mixedMoment B node268 node268Labels := by
    have ha : raw474 = raw475 := by apply Matrix.ext; unfold raw474 raw475; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3225 = raw475Labels := by decide +kernel
    rw [ha, hj, canonical475 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem sound2279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2279 node2279Labels = Sparse.eval nodeValue2279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2279) = mixedMoment B node2279 node2279Labels := rfl
  simpa [nodeValue2279, Sparse.eval] using hc.symm

theorem sound2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2294 node2294Labels = Sparse.eval nodeValue2294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2294) = mixedMoment B node2294 node2294Labels := rfl
  simpa [nodeValue2294, Sparse.eval] using hc.symm

theorem sound3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3054 node3054Labels = Sparse.eval nodeValue3054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3054) = mixedMoment B node3054 node3054Labels := rfl
  simpa [nodeValue3054, Sparse.eval] using hc.symm

theorem sound3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3626 node3626Labels = Sparse.eval nodeValue3626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3626) = mixedMoment B node3626 node3626Labels := rfl
  simpa [nodeValue3626, Sparse.eval] using hc.symm

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

theorem sound795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node795 node795Labels = Sparse.eval nodeValue795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 795) = mixedMoment B node795 node795Labels := rfl
  simpa [nodeValue795, Sparse.eval] using hc.symm

theorem sound797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node797 node797Labels = Sparse.eval nodeValue797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 797) = mixedMoment B node797 node797Labels := rfl
  simpa [nodeValue797, Sparse.eval] using hc.symm

theorem sound814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node814 node814Labels = Sparse.eval nodeValue814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 814) = mixedMoment B node814 node814Labels := rfl
  simpa [nodeValue814, Sparse.eval] using hc.symm

theorem sound829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node829 node829Labels = Sparse.eval nodeValue829 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 829) = mixedMoment B node829 node829Labels := rfl
  simpa [nodeValue829, Sparse.eval] using hc.symm

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

theorem sound1029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1029 node1029Labels = Sparse.eval nodeValue1029 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1029) = mixedMoment B node1029 node1029Labels := rfl
  simpa [nodeValue1029, Sparse.eval] using hc.symm

theorem sound1031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1031 node1031Labels = Sparse.eval nodeValue1031 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1031) = mixedMoment B node1031 node1031Labels := rfl
  simpa [nodeValue1031, Sparse.eval] using hc.symm

theorem sound1047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1047 node1047Labels = Sparse.eval nodeValue1047 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1047) = mixedMoment B node1047 node1047Labels := rfl
  simpa [nodeValue1047, Sparse.eval] using hc.symm

theorem sound1061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1061 node1061Labels = Sparse.eval nodeValue1061 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1061) = mixedMoment B node1061 node1061Labels := rfl
  simpa [nodeValue1061, Sparse.eval] using hc.symm

theorem sound1066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1066 node1066Labels = Sparse.eval nodeValue1066 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1066) = mixedMoment B node1066 node1066Labels := rfl
  simpa [nodeValue1066, Sparse.eval] using hc.symm

theorem sound1067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1067 node1067Labels = Sparse.eval nodeValue1067 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1067) = mixedMoment B node1067 node1067Labels := rfl
  simpa [nodeValue1067, Sparse.eval] using hc.symm

theorem sound1068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1068 node1068Labels = Sparse.eval nodeValue1068 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1068) = mixedMoment B node1068 node1068Labels := rfl
  simpa [nodeValue1068, Sparse.eval] using hc.symm

theorem sound1069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1069 node1069Labels = Sparse.eval nodeValue1069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1069) = mixedMoment B node1069 node1069Labels := rfl
  simpa [nodeValue1069, Sparse.eval] using hc.symm

theorem sound1084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1084 node1084Labels = Sparse.eval nodeValue1084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1084) = mixedMoment B node1084 node1084Labels := rfl
  simpa [nodeValue1084, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1355 node1355Labels = Sparse.eval nodeValue1355 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1355) = mixedMoment B node1355 node1355Labels := rfl
  simpa [nodeValue1355, Sparse.eval] using hc.symm

theorem sound1369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1369 node1369Labels = Sparse.eval nodeValue1369 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1369) = mixedMoment B node1369 node1369Labels := rfl
  simpa [nodeValue1369, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1408 node1408Labels = Sparse.eval nodeValue1408 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1408) = mixedMoment B node1408 node1408Labels := rfl
  simpa [nodeValue1408, Sparse.eval] using hc.symm

theorem sound1458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1458 node1458Labels = Sparse.eval nodeValue1458 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1458) = mixedMoment B node1458 node1458Labels := rfl
  simpa [nodeValue1458, Sparse.eval] using hc.symm

theorem sound1459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1459 node1459Labels = Sparse.eval nodeValue1459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1459) = mixedMoment B node1459 node1459Labels := rfl
  simpa [nodeValue1459, Sparse.eval] using hc.symm

theorem sound1461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1461 node1461Labels = Sparse.eval nodeValue1461 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1461) = mixedMoment B node1461 node1461Labels := rfl
  simpa [nodeValue1461, Sparse.eval] using hc.symm

theorem sound1462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1462 node1462Labels = Sparse.eval nodeValue1462 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1462) = mixedMoment B node1462 node1462Labels := rfl
  simpa [nodeValue1462, Sparse.eval] using hc.symm

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

theorem sound1903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1903 node1903Labels = Sparse.eval nodeValue1903 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1903) = mixedMoment B node1903 node1903Labels := rfl
  simpa [nodeValue1903, Sparse.eval] using hc.symm

theorem sound1916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1916 node1916Labels = Sparse.eval nodeValue1916 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1916) = mixedMoment B node1916 node1916Labels := rfl
  simpa [nodeValue1916, Sparse.eval] using hc.symm

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

theorem sound1927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1927 node1927Labels = Sparse.eval nodeValue1927 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1927) = mixedMoment B node1927 node1927Labels := rfl
  simpa [nodeValue1927, Sparse.eval] using hc.symm

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

theorem sound2013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2013 node2013Labels = Sparse.eval nodeValue2013 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2013) = mixedMoment B node2013 node2013Labels := rfl
  simpa [nodeValue2013, Sparse.eval] using hc.symm

theorem sound2026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2026 node2026Labels = Sparse.eval nodeValue2026 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2026) = mixedMoment B node2026 node2026Labels := rfl
  simpa [nodeValue2026, Sparse.eval] using hc.symm

theorem sound2037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2037 node2037Labels = Sparse.eval nodeValue2037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2037) = mixedMoment B node2037 node2037Labels := rfl
  simpa [nodeValue2037, Sparse.eval] using hc.symm

theorem sound2040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2040 node2040Labels = Sparse.eval nodeValue2040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2040) = mixedMoment B node2040 node2040Labels := rfl
  simpa [nodeValue2040, Sparse.eval] using hc.symm

theorem sound2041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2041 node2041Labels = Sparse.eval nodeValue2041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2041) = mixedMoment B node2041 node2041Labels := rfl
  simpa [nodeValue2041, Sparse.eval] using hc.symm

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

theorem sound2055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2055 node2055Labels = Sparse.eval nodeValue2055 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2055) = mixedMoment B node2055 node2055Labels := rfl
  simpa [nodeValue2055, Sparse.eval] using hc.symm

theorem sound2063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2063 node2063Labels = Sparse.eval nodeValue2063 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2063) = mixedMoment B node2063 node2063Labels := rfl
  simpa [nodeValue2063, Sparse.eval] using hc.symm

theorem sound2092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2092 node2092Labels = Sparse.eval nodeValue2092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2092) = mixedMoment B node2092 node2092Labels := rfl
  simpa [nodeValue2092, Sparse.eval] using hc.symm

theorem sound2096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2096 node2096Labels = Sparse.eval nodeValue2096 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2096) = mixedMoment B node2096 node2096Labels := rfl
  simpa [nodeValue2096, Sparse.eval] using hc.symm

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

theorem sound2125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2125 node2125Labels = Sparse.eval nodeValue2125 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2125) = mixedMoment B node2125 node2125Labels := rfl
  simpa [nodeValue2125, Sparse.eval] using hc.symm

theorem sound2136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2136 node2136Labels = Sparse.eval nodeValue2136 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2136) = mixedMoment B node2136 node2136Labels := rfl
  simpa [nodeValue2136, Sparse.eval] using hc.symm

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

theorem sound2253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2253 node2253Labels = Sparse.eval nodeValue2253 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2253) = mixedMoment B node2253 node2253Labels := rfl
  simpa [nodeValue2253, Sparse.eval] using hc.symm

theorem sound2254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2254 node2254Labels = Sparse.eval nodeValue2254 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2254) = mixedMoment B node2254 node2254Labels := rfl
  simpa [nodeValue2254, Sparse.eval] using hc.symm

theorem sound2255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2255 node2255Labels = Sparse.eval nodeValue2255 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2255) = mixedMoment B node2255 node2255Labels := rfl
  simpa [nodeValue2255, Sparse.eval] using hc.symm

theorem sound2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2266 node2266Labels = Sparse.eval nodeValue2266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2266) = mixedMoment B node2266 node2266Labels := rfl
  simpa [nodeValue2266, Sparse.eval] using hc.symm

theorem sound2267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2267 node2267Labels = Sparse.eval nodeValue2267 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2267) = mixedMoment B node2267 node2267Labels := rfl
  simpa [nodeValue2267, Sparse.eval] using hc.symm

theorem sound2280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2280 node2280Labels = Sparse.eval nodeValue2280 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2280) = mixedMoment B node2280 node2280Labels := rfl
  simpa [nodeValue2280, Sparse.eval] using hc.symm

theorem sound2283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2283 node2283Labels = Sparse.eval nodeValue2283 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2283) = mixedMoment B node2283 node2283Labels := rfl
  simpa [nodeValue2283, Sparse.eval] using hc.symm

theorem sound2284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2284 node2284Labels = Sparse.eval nodeValue2284 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2284) = mixedMoment B node2284 node2284Labels := rfl
  simpa [nodeValue2284, Sparse.eval] using hc.symm

theorem sound2285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2285 node2285Labels = Sparse.eval nodeValue2285 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2285) = mixedMoment B node2285 node2285Labels := rfl
  simpa [nodeValue2285, Sparse.eval] using hc.symm

theorem sound2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2290 node2290Labels = Sparse.eval nodeValue2290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2290) = mixedMoment B node2290 node2290Labels := rfl
  simpa [nodeValue2290, Sparse.eval] using hc.symm

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

theorem sound268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node268 node268Labels = Sparse.eval nodeValue268 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue268 (familyPairVector B) := singlePair268 B _hB
    _ = _ := by norm_num [singlePairValue268, nodeValue268, Sparse.eval, mixedVector] <;> ring

theorem sound269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node269 node269Labels = Sparse.eval nodeValue269 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue269 (familyPairVector B) := singlePair269 B _hB
    _ = _ := by norm_num [singlePairValue269, nodeValue269, Sparse.eval, mixedVector] <;> ring

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

theorem sound2520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2520 node2520Labels = Sparse.eval nodeValue2520 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2520) = mixedMoment B node2520 node2520Labels := rfl
  simpa [nodeValue2520, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3156 node3156Labels = Sparse.eval nodeValue3156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3156) = mixedMoment B node3156 node3156Labels := rfl
  simpa [nodeValue3156, Sparse.eval] using hc.symm

theorem sound3161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3161 node3161Labels = Sparse.eval nodeValue3161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3161) = mixedMoment B node3161 node3161Labels := rfl
  simpa [nodeValue3161, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3222 node3222Labels = Sparse.eval nodeValue3222 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3222) = mixedMoment B node3222 node3222Labels := rfl
  simpa [nodeValue3222, Sparse.eval] using hc.symm

theorem sound3224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3224 node3224Labels = Sparse.eval nodeValue3224 (mixedVector B) := by
  have h := singleton3224 B _hB
  rw [sound269 B _hB _hF] at h
  norm_num [nodeValue3224, nodeValue269, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3225 node3225Labels = Sparse.eval nodeValue3225 (mixedVector B) := by
  have h := singleton3225 B _hB
  rw [sound268 B _hB _hF] at h
  norm_num [nodeValue3225, nodeValue268, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources1
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq34 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm34 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA34 + difference 1 0) (sourceB34 + difference 0 1) sourceC34) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1067) := by
    have ha : (tripleCharges (sourceA34 + difference 1 0) (sourceB34 + difference 0 1) sourceC34) = raw3518 := by
      apply Matrix.ext; unfold tripleCharges sourceA34 sourceB34 sourceC34 difference raw3518; decide +kernel
    rw [ha]
    exact (canonical3518 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA34 + difference 1 1) (sourceB34 + difference 1 1) sourceC34) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2285) := by
    have ha : (tripleCharges (sourceA34 + difference 1 1) (sourceB34 + difference 1 1) sourceC34) = raw3511 := by
      apply Matrix.ext; unfold tripleCharges sourceA34 sourceB34 sourceC34 difference raw3511; decide +kernel
    rw [ha]
    exact (canonical3511 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA34 + difference 1 2) (sourceB34 + difference 2 1) sourceC34) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2041) := by
    have ha : (tripleCharges (sourceA34 + difference 1 2) (sourceB34 + difference 2 1) sourceC34) = raw3523 := by
      apply Matrix.ext; unfold tripleCharges sourceA34 sourceB34 sourceC34 difference raw3523; decide +kernel
    rw [ha]
    exact (canonical3523 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA34 + difference 1 3) (sourceB34 + difference 3 1) sourceC34) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2041) := by
    have ha : (tripleCharges (sourceA34 + difference 1 3) (sourceB34 + difference 3 1) sourceC34) = raw3524 := by
      apply Matrix.ext; unfold tripleCharges sourceA34 sourceB34 sourceC34 difference raw3524; decide +kernel
    rw [ha]
    exact (canonical3524 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA34 + difference 1 4) (sourceB34 + difference 4 1) sourceC34) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1067) := by
    have ha : (tripleCharges (sourceA34 + difference 1 4) (sourceB34 + difference 4 1) sourceC34) = raw3525 := by
      apply Matrix.ext; unfold tripleCharges sourceA34 sourceB34 sourceC34 difference raw3525; decide +kernel
    rw [ha]
    exact (canonical3525 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA34 + difference 1 5) (sourceB34 + difference 5 1) sourceC34) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA34 + difference 1 5) (sourceB34 + difference 5 1) sourceC34) = raw3526 := by
      apply Matrix.ext; unfold tripleCharges sourceA34 sourceB34 sourceC34 difference raw3526; decide +kernel
    rw [ha]
    exact (canonical3526 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA34 + sourceB34) sourceC34) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA34 + sourceB34) sourceC34) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA34 sourceB34 sourceC34 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA34 sourceB34 sourceC34
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm34, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq35 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm35 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA35 + difference 0 1) (sourceB35 + difference 1 0) sourceC35) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA35 + difference 0 1) (sourceB35 + difference 1 0) sourceC35) = raw3512 := by
      apply Matrix.ext; unfold tripleCharges sourceA35 sourceB35 sourceC35 difference raw3512; decide +kernel
    rw [ha]
    exact (canonical3512 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA35 + difference 1 1) (sourceB35 + difference 1 1) sourceC35) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2285) := by
    have ha : (tripleCharges (sourceA35 + difference 1 1) (sourceB35 + difference 1 1) sourceC35) = raw3511 := by
      apply Matrix.ext; unfold tripleCharges sourceA35 sourceB35 sourceC35 difference raw3511; decide +kernel
    rw [ha]
    exact (canonical3511 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA35 + difference 2 1) (sourceB35 + difference 1 2) sourceC35) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2041) := by
    have ha : (tripleCharges (sourceA35 + difference 2 1) (sourceB35 + difference 1 2) sourceC35) = raw3527 := by
      apply Matrix.ext; unfold tripleCharges sourceA35 sourceB35 sourceC35 difference raw3527; decide +kernel
    rw [ha]
    exact (canonical3527 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA35 + difference 3 1) (sourceB35 + difference 1 3) sourceC35) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2041) := by
    have ha : (tripleCharges (sourceA35 + difference 3 1) (sourceB35 + difference 1 3) sourceC35) = raw3528 := by
      apply Matrix.ext; unfold tripleCharges sourceA35 sourceB35 sourceC35 difference raw3528; decide +kernel
    rw [ha]
    exact (canonical3528 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA35 + difference 4 1) (sourceB35 + difference 1 4) sourceC35) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA35 + difference 4 1) (sourceB35 + difference 1 4) sourceC35) = raw3529 := by
      apply Matrix.ext; unfold tripleCharges sourceA35 sourceB35 sourceC35 difference raw3529; decide +kernel
    rw [ha]
    exact (canonical3529 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA35 + difference 5 1) (sourceB35 + difference 1 5) sourceC35) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1459) := by
    have ha : (tripleCharges (sourceA35 + difference 5 1) (sourceB35 + difference 1 5) sourceC35) = raw3530 := by
      apply Matrix.ext; unfold tripleCharges sourceA35 sourceB35 sourceC35 difference raw3530; decide +kernel
    rw [ha]
    exact (canonical3530 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA35 + sourceB35) sourceC35) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA35 + sourceB35) sourceC35) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA35 sourceB35 sourceC35 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA35 sourceB35 sourceC35
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm35, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq36 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm36 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA36 + difference 5 0) (sourceB36 + difference 0 5) sourceC36) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1069) := by
    have ha : (tripleCharges (sourceA36 + difference 5 0) (sourceB36 + difference 0 5) sourceC36) = raw3522 := by
      apply Matrix.ext; unfold tripleCharges sourceA36 sourceB36 sourceC36 difference raw3522; decide +kernel
    rw [ha]
    exact (canonical3522 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA36 + difference 5 1) (sourceB36 + difference 1 5) sourceC36) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1459) := by
    have ha : (tripleCharges (sourceA36 + difference 5 1) (sourceB36 + difference 1 5) sourceC36) = raw3530 := by
      apply Matrix.ext; unfold tripleCharges sourceA36 sourceB36 sourceC36 difference raw3530; decide +kernel
    rw [ha]
    exact (canonical3530 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA36 + difference 5 2) (sourceB36 + difference 2 5) sourceC36) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1459) := by
    have ha : (tripleCharges (sourceA36 + difference 5 2) (sourceB36 + difference 2 5) sourceC36) = raw3531 := by
      apply Matrix.ext; unfold tripleCharges sourceA36 sourceB36 sourceC36 difference raw3531; decide +kernel
    rw [ha]
    exact (canonical3531 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA36 + difference 5 3) (sourceB36 + difference 3 5) sourceC36) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1459) := by
    have ha : (tripleCharges (sourceA36 + difference 5 3) (sourceB36 + difference 3 5) sourceC36) = raw3532 := by
      apply Matrix.ext; unfold tripleCharges sourceA36 sourceB36 sourceC36 difference raw3532; decide +kernel
    rw [ha]
    exact (canonical3532 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA36 + difference 5 4) (sourceB36 + difference 4 5) sourceC36) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1069) := by
    have ha : (tripleCharges (sourceA36 + difference 5 4) (sourceB36 + difference 4 5) sourceC36) = raw3533 := by
      apply Matrix.ext; unfold tripleCharges sourceA36 sourceB36 sourceC36 difference raw3533; decide +kernel
    rw [ha]
    exact (canonical3533 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA36 + difference 5 5) (sourceB36 + difference 5 5) sourceC36) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2285) := by
    have ha : (tripleCharges (sourceA36 + difference 5 5) (sourceB36 + difference 5 5) sourceC36) = raw3511 := by
      apply Matrix.ext; unfold tripleCharges sourceA36 sourceB36 sourceC36 difference raw3511; decide +kernel
    rw [ha]
    exact (canonical3511 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA36 + sourceB36) sourceC36) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA36 + sourceB36) sourceC36) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA36 sourceB36 sourceC36 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA36 sourceB36 sourceC36
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm36, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq38 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm38 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA38 + difference 0 1) (sourceB38 + difference 1 0) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA38 + difference 0 1) (sourceB38 + difference 1 0) sourceC38) = raw3564 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3564; decide +kernel
    rw [ha]
    exact (canonical3564 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA38 + difference 0 2) (sourceB38 + difference 2 0) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA38 + difference 0 2) (sourceB38 + difference 2 0) sourceC38) = raw3565 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3565; decide +kernel
    rw [ha]
    exact (canonical3565 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA38 + difference 0 3) (sourceB38 + difference 3 0) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA38 + difference 0 3) (sourceB38 + difference 3 0) sourceC38) = raw3566 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3566; decide +kernel
    rw [ha]
    exact (canonical3566 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA38 + difference 0 4) (sourceB38 + difference 4 0) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA38 + difference 0 4) (sourceB38 + difference 4 0) sourceC38) = raw3567 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3567; decide +kernel
    rw [ha]
    exact (canonical3567 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA38 + difference 0 5) (sourceB38 + difference 5 0) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA38 + difference 0 5) (sourceB38 + difference 5 0) sourceC38) = raw3568 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3568; decide +kernel
    rw [ha]
    exact (canonical3568 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA38 + difference 1 0) (sourceB38 + difference 0 1) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1355) := by
    have ha : (tripleCharges (sourceA38 + difference 1 0) (sourceB38 + difference 0 1) sourceC38) = raw3569 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3569; decide +kernel
    rw [ha]
    exact (canonical3569 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA38 + difference 1 2) (sourceB38 + difference 2 1) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1903) := by
    have ha : (tripleCharges (sourceA38 + difference 1 2) (sourceB38 + difference 2 1) sourceC38) = raw3570 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3570; decide +kernel
    rw [ha]
    exact (canonical3570 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA38 + difference 1 3) (sourceB38 + difference 3 1) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1927) := by
    have ha : (tripleCharges (sourceA38 + difference 1 3) (sourceB38 + difference 3 1) sourceC38) = raw3571 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3571; decide +kernel
    rw [ha]
    exact (canonical3571 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA38 + difference 1 4) (sourceB38 + difference 4 1) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1916) := by
    have ha : (tripleCharges (sourceA38 + difference 1 4) (sourceB38 + difference 4 1) sourceC38) = raw3572 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3572; decide +kernel
    rw [ha]
    exact (canonical3572 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA38 + difference 1 5) (sourceB38 + difference 5 1) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA38 + difference 1 5) (sourceB38 + difference 5 1) sourceC38) = raw3573 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3573; decide +kernel
    rw [ha]
    exact (canonical3573 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA38 + difference 2 0) (sourceB38 + difference 0 2) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1355) := by
    have ha : (tripleCharges (sourceA38 + difference 2 0) (sourceB38 + difference 0 2) sourceC38) = raw3574 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3574; decide +kernel
    rw [ha]
    exact (canonical3574 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA38 + difference 2 1) (sourceB38 + difference 1 2) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1903) := by
    have ha : (tripleCharges (sourceA38 + difference 2 1) (sourceB38 + difference 1 2) sourceC38) = raw3575 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3575; decide +kernel
    rw [ha]
    exact (canonical3575 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA38 + difference 2 3) (sourceB38 + difference 3 2) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1927) := by
    have ha : (tripleCharges (sourceA38 + difference 2 3) (sourceB38 + difference 3 2) sourceC38) = raw3576 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3576; decide +kernel
    rw [ha]
    exact (canonical3576 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA38 + difference 2 4) (sourceB38 + difference 4 2) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1916) := by
    have ha : (tripleCharges (sourceA38 + difference 2 4) (sourceB38 + difference 4 2) sourceC38) = raw3577 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3577; decide +kernel
    rw [ha]
    exact (canonical3577 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA38 + difference 2 5) (sourceB38 + difference 5 2) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA38 + difference 2 5) (sourceB38 + difference 5 2) sourceC38) = raw3578 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3578; decide +kernel
    rw [ha]
    exact (canonical3578 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA38 + difference 3 0) (sourceB38 + difference 0 3) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1369) := by
    have ha : (tripleCharges (sourceA38 + difference 3 0) (sourceB38 + difference 0 3) sourceC38) = raw3579 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3579; decide +kernel
    rw [ha]
    exact (canonical3579 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA38 + difference 3 1) (sourceB38 + difference 1 3) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2037) := by
    have ha : (tripleCharges (sourceA38 + difference 3 1) (sourceB38 + difference 1 3) sourceC38) = raw3580 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3580; decide +kernel
    rw [ha]
    exact (canonical3580 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA38 + difference 3 2) (sourceB38 + difference 2 3) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2037) := by
    have ha : (tripleCharges (sourceA38 + difference 3 2) (sourceB38 + difference 2 3) sourceC38) = raw3581 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3581; decide +kernel
    rw [ha]
    exact (canonical3581 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA38 + difference 3 4) (sourceB38 + difference 4 3) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA38 + difference 3 4) (sourceB38 + difference 4 3) sourceC38) = raw3582 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3582; decide +kernel
    rw [ha]
    exact (canonical3582 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA38 + difference 3 5) (sourceB38 + difference 5 3) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3224) := by
    have ha : (tripleCharges (sourceA38 + difference 3 5) (sourceB38 + difference 5 3) sourceC38) = raw3583 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3583; decide +kernel
    rw [ha]
    exact (canonical3583 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA38 + difference 4 0) (sourceB38 + difference 0 4) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA38 + difference 4 0) (sourceB38 + difference 0 4) sourceC38) = raw3584 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3584; decide +kernel
    rw [ha]
    exact (canonical3584 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA38 + difference 4 1) (sourceB38 + difference 1 4) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA38 + difference 4 1) (sourceB38 + difference 1 4) sourceC38) = raw3585 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3585; decide +kernel
    rw [ha]
    exact (canonical3585 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA38 + difference 4 2) (sourceB38 + difference 2 4) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA38 + difference 4 2) (sourceB38 + difference 2 4) sourceC38) = raw3586 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3586; decide +kernel
    rw [ha]
    exact (canonical3586 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA38 + difference 4 3) (sourceB38 + difference 3 4) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA38 + difference 4 3) (sourceB38 + difference 3 4) sourceC38) = raw3587 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3587; decide +kernel
    rw [ha]
    exact (canonical3587 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA38 + difference 4 5) (sourceB38 + difference 5 4) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA38 + difference 4 5) (sourceB38 + difference 5 4) sourceC38) = raw3588 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3588; decide +kernel
    rw [ha]
    exact (canonical3588 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA38 + difference 5 0) (sourceB38 + difference 0 5) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 797) := by
    have ha : (tripleCharges (sourceA38 + difference 5 0) (sourceB38 + difference 0 5) sourceC38) = raw3589 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3589; decide +kernel
    rw [ha]
    exact (canonical3589 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA38 + difference 5 1) (sourceB38 + difference 1 5) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 795) := by
    have ha : (tripleCharges (sourceA38 + difference 5 1) (sourceB38 + difference 1 5) sourceC38) = raw3590 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3590; decide +kernel
    rw [ha]
    exact (canonical3590 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA38 + difference 5 2) (sourceB38 + difference 2 5) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 795) := by
    have ha : (tripleCharges (sourceA38 + difference 5 2) (sourceB38 + difference 2 5) sourceC38) = raw3591 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3591; decide +kernel
    rw [ha]
    exact (canonical3591 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA38 + difference 5 3) (sourceB38 + difference 3 5) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 829) := by
    have ha : (tripleCharges (sourceA38 + difference 5 3) (sourceB38 + difference 3 5) sourceC38) = raw3592 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3592; decide +kernel
    rw [ha]
    exact (canonical3592 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA38 + difference 5 4) (sourceB38 + difference 4 5) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 814) := by
    have ha : (tripleCharges (sourceA38 + difference 5 4) (sourceB38 + difference 4 5) sourceC38) = raw3593 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3593; decide +kernel
    rw [ha]
    exact (canonical3593 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA38 sourceB38 sourceC38
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm38, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq40 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm40 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA40 + difference 0 0) (sourceB40 + difference 0 0) sourceC40) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA40 + difference 0 0) (sourceB40 + difference 0 0) sourceC40) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA40 sourceB40 sourceC40 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA40 + difference 0 1) (sourceB40 + difference 1 0) sourceC40) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3156) := by
    have ha : (tripleCharges (sourceA40 + difference 0 1) (sourceB40 + difference 1 0) sourceC40) = raw3625 := by
      apply Matrix.ext; unfold tripleCharges sourceA40 sourceB40 sourceC40 difference raw3625; decide +kernel
    rw [ha]
    exact (canonical3625 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA40 + difference 0 2) (sourceB40 + difference 2 0) sourceC40) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3156) := by
    have ha : (tripleCharges (sourceA40 + difference 0 2) (sourceB40 + difference 2 0) sourceC40) = raw3626 := by
      apply Matrix.ext; unfold tripleCharges sourceA40 sourceB40 sourceC40 difference raw3626; decide +kernel
    rw [ha]
    exact (canonical3626 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA40 + difference 0 3) (sourceB40 + difference 3 0) sourceC40) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3161) := by
    have ha : (tripleCharges (sourceA40 + difference 0 3) (sourceB40 + difference 3 0) sourceC40) = raw3627 := by
      apply Matrix.ext; unfold tripleCharges sourceA40 sourceB40 sourceC40 difference raw3627; decide +kernel
    rw [ha]
    exact (canonical3627 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA40 + difference 0 4) (sourceB40 + difference 4 0) sourceC40) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA40 + difference 0 4) (sourceB40 + difference 4 0) sourceC40) = raw3628 := by
      apply Matrix.ext; unfold tripleCharges sourceA40 sourceB40 sourceC40 difference raw3628; decide +kernel
    rw [ha]
    exact (canonical3628 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA40 + difference 0 5) (sourceB40 + difference 5 0) sourceC40) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA40 + difference 0 5) (sourceB40 + difference 5 0) sourceC40) = raw3629 := by
      apply Matrix.ext; unfold tripleCharges sourceA40 sourceB40 sourceC40 difference raw3629; decide +kernel
    rw [ha]
    exact (canonical3629 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA40 + sourceB40) sourceC40) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA40 + sourceB40) sourceC40) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA40 sourceB40 sourceC40 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA40 sourceB40 sourceC40
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm40, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq41 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm41 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA41 + difference 0 0) (sourceB41 + difference 0 0) sourceC41) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA41 + difference 0 0) (sourceB41 + difference 0 0) sourceC41) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA41 sourceB41 sourceC41 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA41 + difference 1 0) (sourceB41 + difference 0 1) sourceC41) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1029) := by
    have ha : (tripleCharges (sourceA41 + difference 1 0) (sourceB41 + difference 0 1) sourceC41) = raw3631 := by
      apply Matrix.ext; unfold tripleCharges sourceA41 sourceB41 sourceC41 difference raw3631; decide +kernel
    rw [ha]
    exact (canonical3631 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA41 + difference 2 0) (sourceB41 + difference 0 2) sourceC41) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1029) := by
    have ha : (tripleCharges (sourceA41 + difference 2 0) (sourceB41 + difference 0 2) sourceC41) = raw3632 := by
      apply Matrix.ext; unfold tripleCharges sourceA41 sourceB41 sourceC41 difference raw3632; decide +kernel
    rw [ha]
    exact (canonical3632 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA41 + difference 3 0) (sourceB41 + difference 0 3) sourceC41) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1061) := by
    have ha : (tripleCharges (sourceA41 + difference 3 0) (sourceB41 + difference 0 3) sourceC41) = raw3633 := by
      apply Matrix.ext; unfold tripleCharges sourceA41 sourceB41 sourceC41 difference raw3633; decide +kernel
    rw [ha]
    exact (canonical3633 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA41 + difference 4 0) (sourceB41 + difference 0 4) sourceC41) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA41 + difference 4 0) (sourceB41 + difference 0 4) sourceC41) = raw3634 := by
      apply Matrix.ext; unfold tripleCharges sourceA41 sourceB41 sourceC41 difference raw3634; decide +kernel
    rw [ha]
    exact (canonical3634 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA41 + difference 5 0) (sourceB41 + difference 0 5) sourceC41) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1031) := by
    have ha : (tripleCharges (sourceA41 + difference 5 0) (sourceB41 + difference 0 5) sourceC41) = raw3635 := by
      apply Matrix.ext; unfold tripleCharges sourceA41 sourceB41 sourceC41 difference raw3635; decide +kernel
    rw [ha]
    exact (canonical3635 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA41 + sourceB41) sourceC41) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA41 + sourceB41) sourceC41) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA41 sourceB41 sourceC41 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA41 sourceB41 sourceC41
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm41, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq42 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm42 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA42 + difference 1 0) (sourceB42 + difference 0 1) sourceC42) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1029) := by
    have ha : (tripleCharges (sourceA42 + difference 1 0) (sourceB42 + difference 0 1) sourceC42) = raw3631 := by
      apply Matrix.ext; unfold tripleCharges sourceA42 sourceB42 sourceC42 difference raw3631; decide +kernel
    rw [ha]
    exact (canonical3631 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA42 + difference 1 1) (sourceB42 + difference 1 1) sourceC42) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA42 + difference 1 1) (sourceB42 + difference 1 1) sourceC42) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA42 sourceB42 sourceC42 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA42 + difference 1 2) (sourceB42 + difference 2 1) sourceC42) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2013) := by
    have ha : (tripleCharges (sourceA42 + difference 1 2) (sourceB42 + difference 2 1) sourceC42) = raw3636 := by
      apply Matrix.ext; unfold tripleCharges sourceA42 sourceB42 sourceC42 difference raw3636; decide +kernel
    rw [ha]
    exact (canonical3636 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA42 + difference 1 3) (sourceB42 + difference 3 1) sourceC42) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2096) := by
    have ha : (tripleCharges (sourceA42 + difference 1 3) (sourceB42 + difference 3 1) sourceC42) = raw3637 := by
      apply Matrix.ext; unfold tripleCharges sourceA42 sourceB42 sourceC42 difference raw3637; decide +kernel
    rw [ha]
    exact (canonical3637 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA42 + difference 1 4) (sourceB42 + difference 4 1) sourceC42) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2125) := by
    have ha : (tripleCharges (sourceA42 + difference 1 4) (sourceB42 + difference 4 1) sourceC42) = raw3638 := by
      apply Matrix.ext; unfold tripleCharges sourceA42 sourceB42 sourceC42 difference raw3638; decide +kernel
    rw [ha]
    exact (canonical3638 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA42 + difference 1 5) (sourceB42 + difference 5 1) sourceC42) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA42 + difference 1 5) (sourceB42 + difference 5 1) sourceC42) = raw3639 := by
      apply Matrix.ext; unfold tripleCharges sourceA42 sourceB42 sourceC42 difference raw3639; decide +kernel
    rw [ha]
    exact (canonical3639 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA42 + sourceB42) sourceC42) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA42 + sourceB42) sourceC42) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA42 sourceB42 sourceC42 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA42 sourceB42 sourceC42
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm42, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq43 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm43 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA43 + difference 0 1) (sourceB43 + difference 1 0) sourceC43) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3156) := by
    have ha : (tripleCharges (sourceA43 + difference 0 1) (sourceB43 + difference 1 0) sourceC43) = raw3625 := by
      apply Matrix.ext; unfold tripleCharges sourceA43 sourceB43 sourceC43 difference raw3625; decide +kernel
    rw [ha]
    exact (canonical3625 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA43 + difference 1 1) (sourceB43 + difference 1 1) sourceC43) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA43 + difference 1 1) (sourceB43 + difference 1 1) sourceC43) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA43 sourceB43 sourceC43 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA43 + difference 2 1) (sourceB43 + difference 1 2) sourceC43) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2013) := by
    have ha : (tripleCharges (sourceA43 + difference 2 1) (sourceB43 + difference 1 2) sourceC43) = raw3640 := by
      apply Matrix.ext; unfold tripleCharges sourceA43 sourceB43 sourceC43 difference raw3640; decide +kernel
    rw [ha]
    exact (canonical3640 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA43 + difference 3 1) (sourceB43 + difference 1 3) sourceC43) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2037) := by
    have ha : (tripleCharges (sourceA43 + difference 3 1) (sourceB43 + difference 1 3) sourceC43) = raw3641 := by
      apply Matrix.ext; unfold tripleCharges sourceA43 sourceB43 sourceC43 difference raw3641; decide +kernel
    rw [ha]
    exact (canonical3641 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA43 + difference 4 1) (sourceB43 + difference 1 4) sourceC43) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA43 + difference 4 1) (sourceB43 + difference 1 4) sourceC43) = raw3642 := by
      apply Matrix.ext; unfold tripleCharges sourceA43 sourceB43 sourceC43 difference raw3642; decide +kernel
    rw [ha]
    exact (canonical3642 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA43 + difference 5 1) (sourceB43 + difference 1 5) sourceC43) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1458) := by
    have ha : (tripleCharges (sourceA43 + difference 5 1) (sourceB43 + difference 1 5) sourceC43) = raw3643 := by
      apply Matrix.ext; unfold tripleCharges sourceA43 sourceB43 sourceC43 difference raw3643; decide +kernel
    rw [ha]
    exact (canonical3643 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA43 + sourceB43) sourceC43) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA43 + sourceB43) sourceC43) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA43 sourceB43 sourceC43 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA43 sourceB43 sourceC43
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm43, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq44 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm44 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA44 + difference 3 0) (sourceB44 + difference 0 3) sourceC44) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1061) := by
    have ha : (tripleCharges (sourceA44 + difference 3 0) (sourceB44 + difference 0 3) sourceC44) = raw3633 := by
      apply Matrix.ext; unfold tripleCharges sourceA44 sourceB44 sourceC44 difference raw3633; decide +kernel
    rw [ha]
    exact (canonical3633 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA44 + difference 3 1) (sourceB44 + difference 1 3) sourceC44) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2037) := by
    have ha : (tripleCharges (sourceA44 + difference 3 1) (sourceB44 + difference 1 3) sourceC44) = raw3641 := by
      apply Matrix.ext; unfold tripleCharges sourceA44 sourceB44 sourceC44 difference raw3641; decide +kernel
    rw [ha]
    exact (canonical3641 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA44 + difference 3 2) (sourceB44 + difference 2 3) sourceC44) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2037) := by
    have ha : (tripleCharges (sourceA44 + difference 3 2) (sourceB44 + difference 2 3) sourceC44) = raw3644 := by
      apply Matrix.ext; unfold tripleCharges sourceA44 sourceB44 sourceC44 difference raw3644; decide +kernel
    rw [ha]
    exact (canonical3644 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA44 + difference 3 3) (sourceB44 + difference 3 3) sourceC44) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA44 + difference 3 3) (sourceB44 + difference 3 3) sourceC44) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA44 sourceB44 sourceC44 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA44 + difference 3 4) (sourceB44 + difference 4 3) sourceC44) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA44 + difference 3 4) (sourceB44 + difference 4 3) sourceC44) = raw3645 := by
      apply Matrix.ext; unfold tripleCharges sourceA44 sourceB44 sourceC44 difference raw3645; decide +kernel
    rw [ha]
    exact (canonical3645 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA44 + difference 3 5) (sourceB44 + difference 5 3) sourceC44) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA44 + difference 3 5) (sourceB44 + difference 5 3) sourceC44) = raw3646 := by
      apply Matrix.ext; unfold tripleCharges sourceA44 sourceB44 sourceC44 difference raw3646; decide +kernel
    rw [ha]
    exact (canonical3646 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA44 + sourceB44) sourceC44) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA44 + sourceB44) sourceC44) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA44 sourceB44 sourceC44 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA44 sourceB44 sourceC44
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm44, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq45 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm45 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA45 + difference 0 3) (sourceB45 + difference 3 0) sourceC45) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3161) := by
    have ha : (tripleCharges (sourceA45 + difference 0 3) (sourceB45 + difference 3 0) sourceC45) = raw3627 := by
      apply Matrix.ext; unfold tripleCharges sourceA45 sourceB45 sourceC45 difference raw3627; decide +kernel
    rw [ha]
    exact (canonical3627 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA45 + difference 1 3) (sourceB45 + difference 3 1) sourceC45) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2096) := by
    have ha : (tripleCharges (sourceA45 + difference 1 3) (sourceB45 + difference 3 1) sourceC45) = raw3637 := by
      apply Matrix.ext; unfold tripleCharges sourceA45 sourceB45 sourceC45 difference raw3637; decide +kernel
    rw [ha]
    exact (canonical3637 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA45 + difference 2 3) (sourceB45 + difference 3 2) sourceC45) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2096) := by
    have ha : (tripleCharges (sourceA45 + difference 2 3) (sourceB45 + difference 3 2) sourceC45) = raw3647 := by
      apply Matrix.ext; unfold tripleCharges sourceA45 sourceB45 sourceC45 difference raw3647; decide +kernel
    rw [ha]
    exact (canonical3647 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA45 + difference 3 3) (sourceB45 + difference 3 3) sourceC45) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA45 + difference 3 3) (sourceB45 + difference 3 3) sourceC45) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA45 sourceB45 sourceC45 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA45 + difference 4 3) (sourceB45 + difference 3 4) sourceC45) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA45 + difference 4 3) (sourceB45 + difference 3 4) sourceC45) = raw3648 := by
      apply Matrix.ext; unfold tripleCharges sourceA45 sourceB45 sourceC45 difference raw3648; decide +kernel
    rw [ha]
    exact (canonical3648 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA45 + difference 5 3) (sourceB45 + difference 3 5) sourceC45) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1462) := by
    have ha : (tripleCharges (sourceA45 + difference 5 3) (sourceB45 + difference 3 5) sourceC45) = raw3649 := by
      apply Matrix.ext; unfold tripleCharges sourceA45 sourceB45 sourceC45 difference raw3649; decide +kernel
    rw [ha]
    exact (canonical3649 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA45 + sourceB45) sourceC45) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA45 + sourceB45) sourceC45) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA45 sourceB45 sourceC45 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA45 sourceB45 sourceC45
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm45, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq46 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm46 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA46 + difference 4 0) (sourceB46 + difference 0 4) sourceC46) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA46 + difference 4 0) (sourceB46 + difference 0 4) sourceC46) = raw3634 := by
      apply Matrix.ext; unfold tripleCharges sourceA46 sourceB46 sourceC46 difference raw3634; decide +kernel
    rw [ha]
    exact (canonical3634 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA46 + difference 4 1) (sourceB46 + difference 1 4) sourceC46) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA46 + difference 4 1) (sourceB46 + difference 1 4) sourceC46) = raw3642 := by
      apply Matrix.ext; unfold tripleCharges sourceA46 sourceB46 sourceC46 difference raw3642; decide +kernel
    rw [ha]
    exact (canonical3642 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA46 + difference 4 2) (sourceB46 + difference 2 4) sourceC46) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA46 + difference 4 2) (sourceB46 + difference 2 4) sourceC46) = raw3650 := by
      apply Matrix.ext; unfold tripleCharges sourceA46 sourceB46 sourceC46 difference raw3650; decide +kernel
    rw [ha]
    exact (canonical3650 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA46 + difference 4 3) (sourceB46 + difference 3 4) sourceC46) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA46 + difference 4 3) (sourceB46 + difference 3 4) sourceC46) = raw3648 := by
      apply Matrix.ext; unfold tripleCharges sourceA46 sourceB46 sourceC46 difference raw3648; decide +kernel
    rw [ha]
    exact (canonical3648 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA46 + difference 4 4) (sourceB46 + difference 4 4) sourceC46) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA46 + difference 4 4) (sourceB46 + difference 4 4) sourceC46) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA46 sourceB46 sourceC46 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA46 + difference 4 5) (sourceB46 + difference 5 4) sourceC46) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA46 + difference 4 5) (sourceB46 + difference 5 4) sourceC46) = raw3651 := by
      apply Matrix.ext; unfold tripleCharges sourceA46 sourceB46 sourceC46 difference raw3651; decide +kernel
    rw [ha]
    exact (canonical3651 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA46 + sourceB46) sourceC46) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA46 + sourceB46) sourceC46) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA46 sourceB46 sourceC46 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA46 sourceB46 sourceC46
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm46, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq47 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm47 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA47 + difference 0 4) (sourceB47 + difference 4 0) sourceC47) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA47 + difference 0 4) (sourceB47 + difference 4 0) sourceC47) = raw3628 := by
      apply Matrix.ext; unfold tripleCharges sourceA47 sourceB47 sourceC47 difference raw3628; decide +kernel
    rw [ha]
    exact (canonical3628 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA47 + difference 1 4) (sourceB47 + difference 4 1) sourceC47) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2125) := by
    have ha : (tripleCharges (sourceA47 + difference 1 4) (sourceB47 + difference 4 1) sourceC47) = raw3638 := by
      apply Matrix.ext; unfold tripleCharges sourceA47 sourceB47 sourceC47 difference raw3638; decide +kernel
    rw [ha]
    exact (canonical3638 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA47 + difference 2 4) (sourceB47 + difference 4 2) sourceC47) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2125) := by
    have ha : (tripleCharges (sourceA47 + difference 2 4) (sourceB47 + difference 4 2) sourceC47) = raw3652 := by
      apply Matrix.ext; unfold tripleCharges sourceA47 sourceB47 sourceC47 difference raw3652; decide +kernel
    rw [ha]
    exact (canonical3652 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA47 + difference 3 4) (sourceB47 + difference 4 3) sourceC47) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA47 + difference 3 4) (sourceB47 + difference 4 3) sourceC47) = raw3645 := by
      apply Matrix.ext; unfold tripleCharges sourceA47 sourceB47 sourceC47 difference raw3645; decide +kernel
    rw [ha]
    exact (canonical3645 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA47 + difference 4 4) (sourceB47 + difference 4 4) sourceC47) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA47 + difference 4 4) (sourceB47 + difference 4 4) sourceC47) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA47 sourceB47 sourceC47 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA47 + difference 5 4) (sourceB47 + difference 4 5) sourceC47) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1461) := by
    have ha : (tripleCharges (sourceA47 + difference 5 4) (sourceB47 + difference 4 5) sourceC47) = raw3653 := by
      apply Matrix.ext; unfold tripleCharges sourceA47 sourceB47 sourceC47 difference raw3653; decide +kernel
    rw [ha]
    exact (canonical3653 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA47 + sourceB47) sourceC47) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA47 + sourceB47) sourceC47) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA47 sourceB47 sourceC47 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA47 sourceB47 sourceC47
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm47, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq48 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm48 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA48 + difference 5 0) (sourceB48 + difference 0 5) sourceC48) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1031) := by
    have ha : (tripleCharges (sourceA48 + difference 5 0) (sourceB48 + difference 0 5) sourceC48) = raw3635 := by
      apply Matrix.ext; unfold tripleCharges sourceA48 sourceB48 sourceC48 difference raw3635; decide +kernel
    rw [ha]
    exact (canonical3635 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA48 + difference 5 1) (sourceB48 + difference 1 5) sourceC48) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1458) := by
    have ha : (tripleCharges (sourceA48 + difference 5 1) (sourceB48 + difference 1 5) sourceC48) = raw3643 := by
      apply Matrix.ext; unfold tripleCharges sourceA48 sourceB48 sourceC48 difference raw3643; decide +kernel
    rw [ha]
    exact (canonical3643 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA48 + difference 5 2) (sourceB48 + difference 2 5) sourceC48) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1458) := by
    have ha : (tripleCharges (sourceA48 + difference 5 2) (sourceB48 + difference 2 5) sourceC48) = raw3654 := by
      apply Matrix.ext; unfold tripleCharges sourceA48 sourceB48 sourceC48 difference raw3654; decide +kernel
    rw [ha]
    exact (canonical3654 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA48 + difference 5 3) (sourceB48 + difference 3 5) sourceC48) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1462) := by
    have ha : (tripleCharges (sourceA48 + difference 5 3) (sourceB48 + difference 3 5) sourceC48) = raw3649 := by
      apply Matrix.ext; unfold tripleCharges sourceA48 sourceB48 sourceC48 difference raw3649; decide +kernel
    rw [ha]
    exact (canonical3649 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA48 + difference 5 4) (sourceB48 + difference 4 5) sourceC48) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1461) := by
    have ha : (tripleCharges (sourceA48 + difference 5 4) (sourceB48 + difference 4 5) sourceC48) = raw3653 := by
      apply Matrix.ext; unfold tripleCharges sourceA48 sourceB48 sourceC48 difference raw3653; decide +kernel
    rw [ha]
    exact (canonical3653 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA48 + difference 5 5) (sourceB48 + difference 5 5) sourceC48) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA48 + difference 5 5) (sourceB48 + difference 5 5) sourceC48) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA48 sourceB48 sourceC48 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA48 + sourceB48) sourceC48) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA48 + sourceB48) sourceC48) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA48 sourceB48 sourceC48 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA48 sourceB48 sourceC48
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm48, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq51 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm51 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA51 + difference 0 0) (sourceB51 + difference 0 0) sourceC51) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA51 + difference 0 0) (sourceB51 + difference 0 0) sourceC51) = raw3715 := by
      apply Matrix.ext; unfold tripleCharges sourceA51 sourceB51 sourceC51 difference raw3715; decide +kernel
    rw [ha]
    exact (canonical3715 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA51 + difference 0 1) (sourceB51 + difference 1 0) sourceC51) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA51 + difference 0 1) (sourceB51 + difference 1 0) sourceC51) = raw3716 := by
      apply Matrix.ext; unfold tripleCharges sourceA51 sourceB51 sourceC51 difference raw3716; decide +kernel
    rw [ha]
    exact (canonical3716 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA51 + difference 0 2) (sourceB51 + difference 2 0) sourceC51) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA51 + difference 0 2) (sourceB51 + difference 2 0) sourceC51) = raw3717 := by
      apply Matrix.ext; unfold tripleCharges sourceA51 sourceB51 sourceC51 difference raw3717; decide +kernel
    rw [ha]
    exact (canonical3717 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA51 + difference 0 3) (sourceB51 + difference 3 0) sourceC51) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA51 + difference 0 3) (sourceB51 + difference 3 0) sourceC51) = raw3718 := by
      apply Matrix.ext; unfold tripleCharges sourceA51 sourceB51 sourceC51 difference raw3718; decide +kernel
    rw [ha]
    exact (canonical3718 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA51 + difference 0 4) (sourceB51 + difference 4 0) sourceC51) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA51 + difference 0 4) (sourceB51 + difference 4 0) sourceC51) = raw3719 := by
      apply Matrix.ext; unfold tripleCharges sourceA51 sourceB51 sourceC51 difference raw3719; decide +kernel
    rw [ha]
    exact (canonical3719 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA51 + difference 0 5) (sourceB51 + difference 5 0) sourceC51) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1084) := by
    have ha : (tripleCharges (sourceA51 + difference 0 5) (sourceB51 + difference 5 0) sourceC51) = raw3720 := by
      apply Matrix.ext; unfold tripleCharges sourceA51 sourceB51 sourceC51 difference raw3720; decide +kernel
    rw [ha]
    exact (canonical3720 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA51 + sourceB51) sourceC51) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA51 + sourceB51) sourceC51) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA51 sourceB51 sourceC51 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA51 sourceB51 sourceC51
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm51, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq52 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm52 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA52 + difference 0 0) (sourceB52 + difference 0 0) sourceC52) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA52 + difference 0 0) (sourceB52 + difference 0 0) sourceC52) = raw3715 := by
      apply Matrix.ext; unfold tripleCharges sourceA52 sourceB52 sourceC52 difference raw3715; decide +kernel
    rw [ha]
    exact (canonical3715 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA52 + difference 1 0) (sourceB52 + difference 0 1) sourceC52) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1066) := by
    have ha : (tripleCharges (sourceA52 + difference 1 0) (sourceB52 + difference 0 1) sourceC52) = raw3722 := by
      apply Matrix.ext; unfold tripleCharges sourceA52 sourceB52 sourceC52 difference raw3722; decide +kernel
    rw [ha]
    exact (canonical3722 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA52 + difference 2 0) (sourceB52 + difference 0 2) sourceC52) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1066) := by
    have ha : (tripleCharges (sourceA52 + difference 2 0) (sourceB52 + difference 0 2) sourceC52) = raw3723 := by
      apply Matrix.ext; unfold tripleCharges sourceA52 sourceB52 sourceC52 difference raw3723; decide +kernel
    rw [ha]
    exact (canonical3723 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA52 + difference 3 0) (sourceB52 + difference 0 3) sourceC52) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1068) := by
    have ha : (tripleCharges (sourceA52 + difference 3 0) (sourceB52 + difference 0 3) sourceC52) = raw3724 := by
      apply Matrix.ext; unfold tripleCharges sourceA52 sourceB52 sourceC52 difference raw3724; decide +kernel
    rw [ha]
    exact (canonical3724 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA52 + difference 4 0) (sourceB52 + difference 0 4) sourceC52) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1067) := by
    have ha : (tripleCharges (sourceA52 + difference 4 0) (sourceB52 + difference 0 4) sourceC52) = raw3725 := by
      apply Matrix.ext; unfold tripleCharges sourceA52 sourceB52 sourceC52 difference raw3725; decide +kernel
    rw [ha]
    exact (canonical3725 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA52 + difference 5 0) (sourceB52 + difference 0 5) sourceC52) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1084) := by
    have ha : (tripleCharges (sourceA52 + difference 5 0) (sourceB52 + difference 0 5) sourceC52) = raw3726 := by
      apply Matrix.ext; unfold tripleCharges sourceA52 sourceB52 sourceC52 difference raw3726; decide +kernel
    rw [ha]
    exact (canonical3726 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA52 + sourceB52) sourceC52) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA52 + sourceB52) sourceC52) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA52 sourceB52 sourceC52 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA52 sourceB52 sourceC52
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm52, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq53 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm53 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA53 + difference 1 0) (sourceB53 + difference 0 1) sourceC53) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1066) := by
    have ha : (tripleCharges (sourceA53 + difference 1 0) (sourceB53 + difference 0 1) sourceC53) = raw3722 := by
      apply Matrix.ext; unfold tripleCharges sourceA53 sourceB53 sourceC53 difference raw3722; decide +kernel
    rw [ha]
    exact (canonical3722 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA53 + difference 1 1) (sourceB53 + difference 1 1) sourceC53) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA53 + difference 1 1) (sourceB53 + difference 1 1) sourceC53) = raw3715 := by
      apply Matrix.ext; unfold tripleCharges sourceA53 sourceB53 sourceC53 difference raw3715; decide +kernel
    rw [ha]
    exact (canonical3715 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA53 + difference 1 2) (sourceB53 + difference 2 1) sourceC53) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2040) := by
    have ha : (tripleCharges (sourceA53 + difference 1 2) (sourceB53 + difference 2 1) sourceC53) = raw3727 := by
      apply Matrix.ext; unfold tripleCharges sourceA53 sourceB53 sourceC53 difference raw3727; decide +kernel
    rw [ha]
    exact (canonical3727 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA53 + difference 1 3) (sourceB53 + difference 3 1) sourceC53) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA53 + difference 1 3) (sourceB53 + difference 3 1) sourceC53) = raw3728 := by
      apply Matrix.ext; unfold tripleCharges sourceA53 sourceB53 sourceC53 difference raw3728; decide +kernel
    rw [ha]
    exact (canonical3728 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA53 + difference 1 4) (sourceB53 + difference 4 1) sourceC53) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2283) := by
    have ha : (tripleCharges (sourceA53 + difference 1 4) (sourceB53 + difference 4 1) sourceC53) = raw3729 := by
      apply Matrix.ext; unfold tripleCharges sourceA53 sourceB53 sourceC53 difference raw3729; decide +kernel
    rw [ha]
    exact (canonical3729 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA53 + difference 1 5) (sourceB53 + difference 5 1) sourceC53) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1066) := by
    have ha : (tripleCharges (sourceA53 + difference 1 5) (sourceB53 + difference 5 1) sourceC53) = raw3730 := by
      apply Matrix.ext; unfold tripleCharges sourceA53 sourceB53 sourceC53 difference raw3730; decide +kernel
    rw [ha]
    exact (canonical3730 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA53 + sourceB53) sourceC53) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA53 + sourceB53) sourceC53) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA53 sourceB53 sourceC53 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA53 sourceB53 sourceC53
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm53, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck32 : Integer.Sparse.reindex keyMap MixedData.row32 = numericRow32 := by decide +kernel

theorem numericCheck32 (x : Master → ℝ) : Integer.Sparse.eval numericRow32 x =
    (1 : ℝ) * reducedSource32 x := by
  norm_num [numericRow32, reducedSource32, Integer.Sparse.eval, Sparse.eval, nodeValue1067, nodeValue2041, nodeValue2284, nodeValue2285, nodeValue4085]

theorem reindexCheck33 : Integer.Sparse.reindex keyMap MixedData.row33 = numericRow33 := by decide +kernel

theorem numericCheck33 (x : Master → ℝ) : Integer.Sparse.eval numericRow33 x =
    (1 : ℝ) * reducedSource33 x := by
  norm_num [numericRow33, reducedSource33, Integer.Sparse.eval, Sparse.eval, nodeValue1459, nodeValue2041, nodeValue2063, nodeValue2285, nodeValue4085]

theorem reindexCheck34 : Integer.Sparse.reindex keyMap MixedData.row34 = numericRow34 := by decide +kernel

theorem numericCheck34 (x : Master → ℝ) : Integer.Sparse.eval numericRow34 x =
    (1 : ℝ) * reducedSource34 x := by
  norm_num [numericRow34, reducedSource34, Integer.Sparse.eval, Sparse.eval, nodeValue1069, nodeValue1459, nodeValue2285, nodeValue4085]

theorem reindexCheck35 : Integer.Sparse.reindex keyMap MixedData.row35 = numericRow35 := by decide +kernel

theorem numericCheck35 (x : Master → ℝ) : Integer.Sparse.eval numericRow35 x =
    (2160 : ℝ) * reducedSource35 x := by
  norm_num [numericRow35, reducedSource35, Integer.Sparse.eval, Sparse.eval, nodeValue795, nodeValue797, nodeValue814, nodeValue829, nodeValue1355, nodeValue1369, nodeValue1408, nodeValue1903, nodeValue1916, nodeValue1927, nodeValue2037, nodeValue2063, nodeValue2092, nodeValue2113, nodeValue2254, nodeValue2267, nodeValue2280, nodeValue3054, nodeValue3222, nodeValue3224, nodeValue3225]
  ring

theorem reindexCheck36 : Integer.Sparse.reindex keyMap MixedData.row36 = numericRow36 := by decide +kernel

theorem numericCheck36 (x : Master → ℝ) : Integer.Sparse.eval numericRow36 x =
    (1 : ℝ) * reducedSource36 x := by
  norm_num [numericRow36, reducedSource36, Integer.Sparse.eval, Sparse.eval, nodeValue2255, nodeValue2520, nodeValue3156, nodeValue3161, nodeValue3626, nodeValue4084]

theorem reindexCheck37 : Integer.Sparse.reindex keyMap MixedData.row37 = numericRow37 := by decide +kernel

theorem numericCheck37 (x : Master → ℝ) : Integer.Sparse.eval numericRow37 x =
    (1 : ℝ) * reducedSource37 x := by
  norm_num [numericRow37, reducedSource37, Integer.Sparse.eval, Sparse.eval, nodeValue1029, nodeValue1031, nodeValue1047, nodeValue1061, nodeValue2255, nodeValue4084]

theorem reindexCheck38 : Integer.Sparse.reindex keyMap MixedData.row38 = numericRow38 := by decide +kernel

theorem numericCheck38 (x : Master → ℝ) : Integer.Sparse.eval numericRow38 x =
    (1 : ℝ) * reducedSource38 x := by
  norm_num [numericRow38, reducedSource38, Integer.Sparse.eval, Sparse.eval, nodeValue1029, nodeValue2013, nodeValue2096, nodeValue2125, nodeValue2253, nodeValue2255, nodeValue4084]

theorem reindexCheck39 : Integer.Sparse.reindex keyMap MixedData.row39 = numericRow39 := by decide +kernel

theorem numericCheck39 (x : Master → ℝ) : Integer.Sparse.eval numericRow39 x =
    (1 : ℝ) * reducedSource39 x := by
  norm_num [numericRow39, reducedSource39, Integer.Sparse.eval, Sparse.eval, nodeValue1458, nodeValue2013, nodeValue2026, nodeValue2037, nodeValue2255, nodeValue3156, nodeValue4084]

theorem reindexCheck40 : Integer.Sparse.reindex keyMap MixedData.row40 = numericRow40 := by decide +kernel

theorem numericCheck40 (x : Master → ℝ) : Integer.Sparse.eval numericRow40 x =
    (1 : ℝ) * reducedSource40 x := by
  norm_num [numericRow40, reducedSource40, Integer.Sparse.eval, Sparse.eval, nodeValue1061, nodeValue2037, nodeValue2136, nodeValue2255, nodeValue2279, nodeValue4084]

theorem reindexCheck41 : Integer.Sparse.reindex keyMap MixedData.row41 = numericRow41 := by decide +kernel

theorem numericCheck41 (x : Master → ℝ) : Integer.Sparse.eval numericRow41 x =
    (1 : ℝ) * reducedSource41 x := by
  norm_num [numericRow41, reducedSource41, Integer.Sparse.eval, Sparse.eval, nodeValue1462, nodeValue2096, nodeValue2113, nodeValue2255, nodeValue3161, nodeValue4084]

theorem reindexCheck42 : Integer.Sparse.reindex keyMap MixedData.row42 = numericRow42 := by decide +kernel

theorem numericCheck42 (x : Master → ℝ) : Integer.Sparse.eval numericRow42 x =
    (1 : ℝ) * reducedSource42 x := by
  norm_num [numericRow42, reducedSource42, Integer.Sparse.eval, Sparse.eval, nodeValue1047, nodeValue2026, nodeValue2113, nodeValue2255, nodeValue2266, nodeValue4084]

theorem reindexCheck43 : Integer.Sparse.reindex keyMap MixedData.row43 = numericRow43 := by decide +kernel

theorem numericCheck43 (x : Master → ℝ) : Integer.Sparse.eval numericRow43 x =
    (1 : ℝ) * reducedSource43 x := by
  norm_num [numericRow43, reducedSource43, Integer.Sparse.eval, Sparse.eval, nodeValue1461, nodeValue2125, nodeValue2136, nodeValue2255, nodeValue2520, nodeValue4084]

theorem reindexCheck44 : Integer.Sparse.reindex keyMap MixedData.row44 = numericRow44 := by decide +kernel

theorem numericCheck44 (x : Master → ℝ) : Integer.Sparse.eval numericRow44 x =
    (1 : ℝ) * reducedSource44 x := by
  norm_num [numericRow44, reducedSource44, Integer.Sparse.eval, Sparse.eval, nodeValue1031, nodeValue1458, nodeValue1461, nodeValue1462, nodeValue2255, nodeValue4084]

theorem reindexCheck45 : Integer.Sparse.reindex keyMap MixedData.row45 = numericRow45 := by decide +kernel

theorem numericCheck45 (x : Master → ℝ) : Integer.Sparse.eval numericRow45 x =
    (1 : ℝ) * reducedSource45 x := by
  norm_num [numericRow45, reducedSource45, Integer.Sparse.eval, Sparse.eval, nodeValue1084, nodeValue2055, nodeValue2284, nodeValue2290, nodeValue2294, nodeValue4085]

theorem reindexCheck46 : Integer.Sparse.reindex keyMap MixedData.row46 = numericRow46 := by decide +kernel

theorem numericCheck46 (x : Master → ℝ) : Integer.Sparse.eval numericRow46 x =
    (1 : ℝ) * reducedSource46 x := by
  norm_num [numericRow46, reducedSource46, Integer.Sparse.eval, Sparse.eval, nodeValue1066, nodeValue1067, nodeValue1068, nodeValue1084, nodeValue2284, nodeValue4085]

theorem reindexCheck47 : Integer.Sparse.reindex keyMap MixedData.row47 = numericRow47 := by decide +kernel

theorem numericCheck47 (x : Master → ℝ) : Integer.Sparse.eval numericRow47 x =
    (1 : ℝ) * reducedSource47 x := by
  norm_num [numericRow47, reducedSource47, Integer.Sparse.eval, Sparse.eval, nodeValue1066, nodeValue2040, nodeValue2283, nodeValue2284, nodeValue4085]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero32 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource32 (mixedVector B) = 0 := by
  have h1067 : mixedVector B (Sum.inr 1067) = Sparse.eval nodeValue1067 (mixedVector B) := by
    change mixedMoment B node1067 node1067Labels = _
    exact sound1067 B hB hF
  have h2041 : mixedVector B (Sum.inr 2041) = Sparse.eval nodeValue2041 (mixedVector B) := by
    change mixedMoment B node2041 node2041Labels = _
    exact sound2041 B hB hF
  have h2284 : mixedVector B (Sum.inr 2284) = Sparse.eval nodeValue2284 (mixedVector B) := by
    change mixedMoment B node2284 node2284Labels = _
    exact sound2284 B hB hF
  have h2285 : mixedVector B (Sum.inr 2285) = Sparse.eval nodeValue2285 (mixedVector B) := by
    change mixedMoment B node2285 node2285Labels = _
    exact sound2285 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm34, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1067, h2041, h2284, h2285, h4085, reducedSource32] using sourceEq34 B hB

theorem rowSound32 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row32 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck32, numericCheck32, reducedZero32 B hB hF, mul_zero]

theorem reducedZero33 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource33 (mixedVector B) = 0 := by
  have h1459 : mixedVector B (Sum.inr 1459) = Sparse.eval nodeValue1459 (mixedVector B) := by
    change mixedMoment B node1459 node1459Labels = _
    exact sound1459 B hB hF
  have h2041 : mixedVector B (Sum.inr 2041) = Sparse.eval nodeValue2041 (mixedVector B) := by
    change mixedMoment B node2041 node2041Labels = _
    exact sound2041 B hB hF
  have h2063 : mixedVector B (Sum.inr 2063) = Sparse.eval nodeValue2063 (mixedVector B) := by
    change mixedMoment B node2063 node2063Labels = _
    exact sound2063 B hB hF
  have h2285 : mixedVector B (Sum.inr 2285) = Sparse.eval nodeValue2285 (mixedVector B) := by
    change mixedMoment B node2285 node2285Labels = _
    exact sound2285 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm35, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1459, h2041, h2063, h2285, h4085, reducedSource33] using sourceEq35 B hB

theorem rowSound33 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row33 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck33, numericCheck33, reducedZero33 B hB hF, mul_zero]

theorem reducedZero34 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource34 (mixedVector B) = 0 := by
  have h1069 : mixedVector B (Sum.inr 1069) = Sparse.eval nodeValue1069 (mixedVector B) := by
    change mixedMoment B node1069 node1069Labels = _
    exact sound1069 B hB hF
  have h1459 : mixedVector B (Sum.inr 1459) = Sparse.eval nodeValue1459 (mixedVector B) := by
    change mixedMoment B node1459 node1459Labels = _
    exact sound1459 B hB hF
  have h2285 : mixedVector B (Sum.inr 2285) = Sparse.eval nodeValue2285 (mixedVector B) := by
    change mixedMoment B node2285 node2285Labels = _
    exact sound2285 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm36, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1069, h1459, h2285, h4085, reducedSource34] using sourceEq36 B hB

theorem rowSound34 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row34 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck34, numericCheck34, reducedZero34 B hB hF, mul_zero]

theorem reducedZero35 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource35 (mixedVector B) = 0 := by
  have h795 : mixedVector B (Sum.inr 795) = Sparse.eval nodeValue795 (mixedVector B) := by
    change mixedMoment B node795 node795Labels = _
    exact sound795 B hB hF
  have h797 : mixedVector B (Sum.inr 797) = Sparse.eval nodeValue797 (mixedVector B) := by
    change mixedMoment B node797 node797Labels = _
    exact sound797 B hB hF
  have h814 : mixedVector B (Sum.inr 814) = Sparse.eval nodeValue814 (mixedVector B) := by
    change mixedMoment B node814 node814Labels = _
    exact sound814 B hB hF
  have h829 : mixedVector B (Sum.inr 829) = Sparse.eval nodeValue829 (mixedVector B) := by
    change mixedMoment B node829 node829Labels = _
    exact sound829 B hB hF
  have h1355 : mixedVector B (Sum.inr 1355) = Sparse.eval nodeValue1355 (mixedVector B) := by
    change mixedMoment B node1355 node1355Labels = _
    exact sound1355 B hB hF
  have h1369 : mixedVector B (Sum.inr 1369) = Sparse.eval nodeValue1369 (mixedVector B) := by
    change mixedMoment B node1369 node1369Labels = _
    exact sound1369 B hB hF
  have h1408 : mixedVector B (Sum.inr 1408) = Sparse.eval nodeValue1408 (mixedVector B) := by
    change mixedMoment B node1408 node1408Labels = _
    exact sound1408 B hB hF
  have h1903 : mixedVector B (Sum.inr 1903) = Sparse.eval nodeValue1903 (mixedVector B) := by
    change mixedMoment B node1903 node1903Labels = _
    exact sound1903 B hB hF
  have h1916 : mixedVector B (Sum.inr 1916) = Sparse.eval nodeValue1916 (mixedVector B) := by
    change mixedMoment B node1916 node1916Labels = _
    exact sound1916 B hB hF
  have h1927 : mixedVector B (Sum.inr 1927) = Sparse.eval nodeValue1927 (mixedVector B) := by
    change mixedMoment B node1927 node1927Labels = _
    exact sound1927 B hB hF
  have h2037 : mixedVector B (Sum.inr 2037) = Sparse.eval nodeValue2037 (mixedVector B) := by
    change mixedMoment B node2037 node2037Labels = _
    exact sound2037 B hB hF
  have h2063 : mixedVector B (Sum.inr 2063) = Sparse.eval nodeValue2063 (mixedVector B) := by
    change mixedMoment B node2063 node2063Labels = _
    exact sound2063 B hB hF
  have h2092 : mixedVector B (Sum.inr 2092) = Sparse.eval nodeValue2092 (mixedVector B) := by
    change mixedMoment B node2092 node2092Labels = _
    exact sound2092 B hB hF
  have h2113 : mixedVector B (Sum.inr 2113) = Sparse.eval nodeValue2113 (mixedVector B) := by
    change mixedMoment B node2113 node2113Labels = _
    exact sound2113 B hB hF
  have h2254 : mixedVector B (Sum.inr 2254) = Sparse.eval nodeValue2254 (mixedVector B) := by
    change mixedMoment B node2254 node2254Labels = _
    exact sound2254 B hB hF
  have h2267 : mixedVector B (Sum.inr 2267) = Sparse.eval nodeValue2267 (mixedVector B) := by
    change mixedMoment B node2267 node2267Labels = _
    exact sound2267 B hB hF
  have h2280 : mixedVector B (Sum.inr 2280) = Sparse.eval nodeValue2280 (mixedVector B) := by
    change mixedMoment B node2280 node2280Labels = _
    exact sound2280 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h3224 : mixedVector B (Sum.inr 3224) = Sparse.eval nodeValue3224 (mixedVector B) := by
    change mixedMoment B node3224 node3224Labels = _
    exact sound3224 B hB hF
  have h3225 : mixedVector B (Sum.inr 3225) = Sparse.eval nodeValue3225 (mixedVector B) := by
    change mixedMoment B node3225 node3225Labels = _
    exact sound3225 B hB hF
  simpa only [sourceForm38, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h795, h797, h814, h829, h1355, h1369, h1408, h1903, h1916, h1927, h2037, h2063, h2092, h2113, h2254, h2267, h2280, h3054, h3222, h3224, h3225, reducedSource35] using sourceEq38 B hB

theorem rowSound35 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row35 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck35, numericCheck35, reducedZero35 B hB hF, mul_zero]

theorem reducedZero36 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource36 (mixedVector B) = 0 := by
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h2520 : mixedVector B (Sum.inr 2520) = Sparse.eval nodeValue2520 (mixedVector B) := by
    change mixedMoment B node2520 node2520Labels = _
    exact sound2520 B hB hF
  have h3156 : mixedVector B (Sum.inr 3156) = Sparse.eval nodeValue3156 (mixedVector B) := by
    change mixedMoment B node3156 node3156Labels = _
    exact sound3156 B hB hF
  have h3161 : mixedVector B (Sum.inr 3161) = Sparse.eval nodeValue3161 (mixedVector B) := by
    change mixedMoment B node3161 node3161Labels = _
    exact sound3161 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm40, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2255, h2520, h3156, h3161, h3626, h4084, reducedSource36] using sourceEq40 B hB

theorem rowSound36 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row36 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck36, numericCheck36, reducedZero36 B hB hF, mul_zero]

theorem reducedZero37 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource37 (mixedVector B) = 0 := by
  have h1029 : mixedVector B (Sum.inr 1029) = Sparse.eval nodeValue1029 (mixedVector B) := by
    change mixedMoment B node1029 node1029Labels = _
    exact sound1029 B hB hF
  have h1031 : mixedVector B (Sum.inr 1031) = Sparse.eval nodeValue1031 (mixedVector B) := by
    change mixedMoment B node1031 node1031Labels = _
    exact sound1031 B hB hF
  have h1047 : mixedVector B (Sum.inr 1047) = Sparse.eval nodeValue1047 (mixedVector B) := by
    change mixedMoment B node1047 node1047Labels = _
    exact sound1047 B hB hF
  have h1061 : mixedVector B (Sum.inr 1061) = Sparse.eval nodeValue1061 (mixedVector B) := by
    change mixedMoment B node1061 node1061Labels = _
    exact sound1061 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm41, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1029, h1031, h1047, h1061, h2255, h4084, reducedSource37] using sourceEq41 B hB

theorem rowSound37 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row37 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck37, numericCheck37, reducedZero37 B hB hF, mul_zero]

theorem reducedZero38 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource38 (mixedVector B) = 0 := by
  have h1029 : mixedVector B (Sum.inr 1029) = Sparse.eval nodeValue1029 (mixedVector B) := by
    change mixedMoment B node1029 node1029Labels = _
    exact sound1029 B hB hF
  have h2013 : mixedVector B (Sum.inr 2013) = Sparse.eval nodeValue2013 (mixedVector B) := by
    change mixedMoment B node2013 node2013Labels = _
    exact sound2013 B hB hF
  have h2096 : mixedVector B (Sum.inr 2096) = Sparse.eval nodeValue2096 (mixedVector B) := by
    change mixedMoment B node2096 node2096Labels = _
    exact sound2096 B hB hF
  have h2125 : mixedVector B (Sum.inr 2125) = Sparse.eval nodeValue2125 (mixedVector B) := by
    change mixedMoment B node2125 node2125Labels = _
    exact sound2125 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm42, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1029, h2013, h2096, h2125, h2253, h2255, h4084, reducedSource38] using sourceEq42 B hB

theorem rowSound38 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row38 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck38, numericCheck38, reducedZero38 B hB hF, mul_zero]

theorem reducedZero39 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource39 (mixedVector B) = 0 := by
  have h1458 : mixedVector B (Sum.inr 1458) = Sparse.eval nodeValue1458 (mixedVector B) := by
    change mixedMoment B node1458 node1458Labels = _
    exact sound1458 B hB hF
  have h2013 : mixedVector B (Sum.inr 2013) = Sparse.eval nodeValue2013 (mixedVector B) := by
    change mixedMoment B node2013 node2013Labels = _
    exact sound2013 B hB hF
  have h2026 : mixedVector B (Sum.inr 2026) = Sparse.eval nodeValue2026 (mixedVector B) := by
    change mixedMoment B node2026 node2026Labels = _
    exact sound2026 B hB hF
  have h2037 : mixedVector B (Sum.inr 2037) = Sparse.eval nodeValue2037 (mixedVector B) := by
    change mixedMoment B node2037 node2037Labels = _
    exact sound2037 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h3156 : mixedVector B (Sum.inr 3156) = Sparse.eval nodeValue3156 (mixedVector B) := by
    change mixedMoment B node3156 node3156Labels = _
    exact sound3156 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm43, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1458, h2013, h2026, h2037, h2255, h3156, h4084, reducedSource39] using sourceEq43 B hB

theorem rowSound39 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row39 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck39, numericCheck39, reducedZero39 B hB hF, mul_zero]

theorem reducedZero40 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource40 (mixedVector B) = 0 := by
  have h1061 : mixedVector B (Sum.inr 1061) = Sparse.eval nodeValue1061 (mixedVector B) := by
    change mixedMoment B node1061 node1061Labels = _
    exact sound1061 B hB hF
  have h2037 : mixedVector B (Sum.inr 2037) = Sparse.eval nodeValue2037 (mixedVector B) := by
    change mixedMoment B node2037 node2037Labels = _
    exact sound2037 B hB hF
  have h2136 : mixedVector B (Sum.inr 2136) = Sparse.eval nodeValue2136 (mixedVector B) := by
    change mixedMoment B node2136 node2136Labels = _
    exact sound2136 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm44, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1061, h2037, h2136, h2255, h2279, h4084, reducedSource40] using sourceEq44 B hB

theorem rowSound40 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row40 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck40, numericCheck40, reducedZero40 B hB hF, mul_zero]

theorem reducedZero41 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource41 (mixedVector B) = 0 := by
  have h1462 : mixedVector B (Sum.inr 1462) = Sparse.eval nodeValue1462 (mixedVector B) := by
    change mixedMoment B node1462 node1462Labels = _
    exact sound1462 B hB hF
  have h2096 : mixedVector B (Sum.inr 2096) = Sparse.eval nodeValue2096 (mixedVector B) := by
    change mixedMoment B node2096 node2096Labels = _
    exact sound2096 B hB hF
  have h2113 : mixedVector B (Sum.inr 2113) = Sparse.eval nodeValue2113 (mixedVector B) := by
    change mixedMoment B node2113 node2113Labels = _
    exact sound2113 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h3161 : mixedVector B (Sum.inr 3161) = Sparse.eval nodeValue3161 (mixedVector B) := by
    change mixedMoment B node3161 node3161Labels = _
    exact sound3161 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm45, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1462, h2096, h2113, h2255, h3161, h4084, reducedSource41] using sourceEq45 B hB

theorem rowSound41 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row41 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck41, numericCheck41, reducedZero41 B hB hF, mul_zero]

theorem reducedZero42 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource42 (mixedVector B) = 0 := by
  have h1047 : mixedVector B (Sum.inr 1047) = Sparse.eval nodeValue1047 (mixedVector B) := by
    change mixedMoment B node1047 node1047Labels = _
    exact sound1047 B hB hF
  have h2026 : mixedVector B (Sum.inr 2026) = Sparse.eval nodeValue2026 (mixedVector B) := by
    change mixedMoment B node2026 node2026Labels = _
    exact sound2026 B hB hF
  have h2113 : mixedVector B (Sum.inr 2113) = Sparse.eval nodeValue2113 (mixedVector B) := by
    change mixedMoment B node2113 node2113Labels = _
    exact sound2113 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm46, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1047, h2026, h2113, h2255, h2266, h4084, reducedSource42] using sourceEq46 B hB

theorem rowSound42 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row42 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck42, numericCheck42, reducedZero42 B hB hF, mul_zero]

theorem reducedZero43 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource43 (mixedVector B) = 0 := by
  have h1461 : mixedVector B (Sum.inr 1461) = Sparse.eval nodeValue1461 (mixedVector B) := by
    change mixedMoment B node1461 node1461Labels = _
    exact sound1461 B hB hF
  have h2125 : mixedVector B (Sum.inr 2125) = Sparse.eval nodeValue2125 (mixedVector B) := by
    change mixedMoment B node2125 node2125Labels = _
    exact sound2125 B hB hF
  have h2136 : mixedVector B (Sum.inr 2136) = Sparse.eval nodeValue2136 (mixedVector B) := by
    change mixedMoment B node2136 node2136Labels = _
    exact sound2136 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h2520 : mixedVector B (Sum.inr 2520) = Sparse.eval nodeValue2520 (mixedVector B) := by
    change mixedMoment B node2520 node2520Labels = _
    exact sound2520 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm47, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1461, h2125, h2136, h2255, h2520, h4084, reducedSource43] using sourceEq47 B hB

theorem rowSound43 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row43 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck43, numericCheck43, reducedZero43 B hB hF, mul_zero]

theorem reducedZero44 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource44 (mixedVector B) = 0 := by
  have h1031 : mixedVector B (Sum.inr 1031) = Sparse.eval nodeValue1031 (mixedVector B) := by
    change mixedMoment B node1031 node1031Labels = _
    exact sound1031 B hB hF
  have h1458 : mixedVector B (Sum.inr 1458) = Sparse.eval nodeValue1458 (mixedVector B) := by
    change mixedMoment B node1458 node1458Labels = _
    exact sound1458 B hB hF
  have h1461 : mixedVector B (Sum.inr 1461) = Sparse.eval nodeValue1461 (mixedVector B) := by
    change mixedMoment B node1461 node1461Labels = _
    exact sound1461 B hB hF
  have h1462 : mixedVector B (Sum.inr 1462) = Sparse.eval nodeValue1462 (mixedVector B) := by
    change mixedMoment B node1462 node1462Labels = _
    exact sound1462 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm48, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1031, h1458, h1461, h1462, h2255, h4084, reducedSource44] using sourceEq48 B hB

theorem rowSound44 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row44 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck44, numericCheck44, reducedZero44 B hB hF, mul_zero]

theorem reducedZero45 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource45 (mixedVector B) = 0 := by
  have h1084 : mixedVector B (Sum.inr 1084) = Sparse.eval nodeValue1084 (mixedVector B) := by
    change mixedMoment B node1084 node1084Labels = _
    exact sound1084 B hB hF
  have h2055 : mixedVector B (Sum.inr 2055) = Sparse.eval nodeValue2055 (mixedVector B) := by
    change mixedMoment B node2055 node2055Labels = _
    exact sound2055 B hB hF
  have h2284 : mixedVector B (Sum.inr 2284) = Sparse.eval nodeValue2284 (mixedVector B) := by
    change mixedMoment B node2284 node2284Labels = _
    exact sound2284 B hB hF
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm51, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1084, h2055, h2284, h2290, h2294, h4085, reducedSource45] using sourceEq51 B hB

theorem rowSound45 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row45 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck45, numericCheck45, reducedZero45 B hB hF, mul_zero]

theorem reducedZero46 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource46 (mixedVector B) = 0 := by
  have h1066 : mixedVector B (Sum.inr 1066) = Sparse.eval nodeValue1066 (mixedVector B) := by
    change mixedMoment B node1066 node1066Labels = _
    exact sound1066 B hB hF
  have h1067 : mixedVector B (Sum.inr 1067) = Sparse.eval nodeValue1067 (mixedVector B) := by
    change mixedMoment B node1067 node1067Labels = _
    exact sound1067 B hB hF
  have h1068 : mixedVector B (Sum.inr 1068) = Sparse.eval nodeValue1068 (mixedVector B) := by
    change mixedMoment B node1068 node1068Labels = _
    exact sound1068 B hB hF
  have h1084 : mixedVector B (Sum.inr 1084) = Sparse.eval nodeValue1084 (mixedVector B) := by
    change mixedMoment B node1084 node1084Labels = _
    exact sound1084 B hB hF
  have h2284 : mixedVector B (Sum.inr 2284) = Sparse.eval nodeValue2284 (mixedVector B) := by
    change mixedMoment B node2284 node2284Labels = _
    exact sound2284 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm52, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1066, h1067, h1068, h1084, h2284, h4085, reducedSource46] using sourceEq52 B hB

theorem rowSound46 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row46 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck46, numericCheck46, reducedZero46 B hB hF, mul_zero]

theorem reducedZero47 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource47 (mixedVector B) = 0 := by
  have h1066 : mixedVector B (Sum.inr 1066) = Sparse.eval nodeValue1066 (mixedVector B) := by
    change mixedMoment B node1066 node1066Labels = _
    exact sound1066 B hB hF
  have h2040 : mixedVector B (Sum.inr 2040) = Sparse.eval nodeValue2040 (mixedVector B) := by
    change mixedMoment B node2040 node2040Labels = _
    exact sound2040 B hB hF
  have h2283 : mixedVector B (Sum.inr 2283) = Sparse.eval nodeValue2283 (mixedVector B) := by
    change mixedMoment B node2283 node2283Labels = _
    exact sound2283 B hB hF
  have h2284 : mixedVector B (Sum.inr 2284) = Sparse.eval nodeValue2284 (mixedVector B) := by
    change mixedMoment B node2284 node2284Labels = _
    exact sound2284 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm53, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1066, h2040, h2283, h2284, h4085, reducedSource47] using sourceEq53 B hB

theorem rowSound47 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row47 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck47, numericCheck47, reducedZero47 B hB hF, mul_zero]

theorem sourceRowsAt32 : MixedData.sourceRows (32 : Fin 2425) =
    MixedData.row32 := by decide +kernel

theorem sourceRowsAt33 : MixedData.sourceRows (33 : Fin 2425) =
    MixedData.row33 := by decide +kernel

theorem sourceRowsAt34 : MixedData.sourceRows (34 : Fin 2425) =
    MixedData.row34 := by decide +kernel

theorem sourceRowsAt35 : MixedData.sourceRows (35 : Fin 2425) =
    MixedData.row35 := by decide +kernel

theorem sourceRowsAt36 : MixedData.sourceRows (36 : Fin 2425) =
    MixedData.row36 := by decide +kernel

theorem sourceRowsAt37 : MixedData.sourceRows (37 : Fin 2425) =
    MixedData.row37 := by decide +kernel

theorem sourceRowsAt38 : MixedData.sourceRows (38 : Fin 2425) =
    MixedData.row38 := by decide +kernel

theorem sourceRowsAt39 : MixedData.sourceRows (39 : Fin 2425) =
    MixedData.row39 := by decide +kernel

theorem sourceRowsAt40 : MixedData.sourceRows (40 : Fin 2425) =
    MixedData.row40 := by decide +kernel

theorem sourceRowsAt41 : MixedData.sourceRows (41 : Fin 2425) =
    MixedData.row41 := by decide +kernel

theorem sourceRowsAt42 : MixedData.sourceRows (42 : Fin 2425) =
    MixedData.row42 := by decide +kernel

theorem sourceRowsAt43 : MixedData.sourceRows (43 : Fin 2425) =
    MixedData.row43 := by decide +kernel

theorem sourceRowsAt44 : MixedData.sourceRows (44 : Fin 2425) =
    MixedData.row44 := by decide +kernel

theorem sourceRowsAt45 : MixedData.sourceRows (45 : Fin 2425) =
    MixedData.row45 := by decide +kernel

theorem sourceRowsAt46 : MixedData.sourceRows (46 : Fin 2425) =
    MixedData.row46 := by decide +kernel

theorem sourceRowsAt47 : MixedData.sourceRows (47 : Fin 2425) =
    MixedData.row47 := by decide +kernel

theorem chunkSound2_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 2) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 32 ∨ k.val = 33 ∨ k.val = 34 ∨ k.val = 35 ∨ k.val = 36 ∨ k.val = 37 ∨ k.val = 38 ∨ k.val = 39 ∨ k.val = 40 ∨ k.val = 41 ∨ k.val = 42 ∨ k.val = 43 ∨ k.val = 44 ∨ k.val = 45 ∨ k.val = 46 ∨ k.val = 47 := by omega
  rcases heq with h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47
  · have he : k = (32 : Fin 2425) := Fin.ext h32
    subst k
    rw [sourceRowsAt32]
    exact rowSound32 B hB hF
  · have he : k = (33 : Fin 2425) := Fin.ext h33
    subst k
    rw [sourceRowsAt33]
    exact rowSound33 B hB hF
  · have he : k = (34 : Fin 2425) := Fin.ext h34
    subst k
    rw [sourceRowsAt34]
    exact rowSound34 B hB hF
  · have he : k = (35 : Fin 2425) := Fin.ext h35
    subst k
    rw [sourceRowsAt35]
    exact rowSound35 B hB hF
  · have he : k = (36 : Fin 2425) := Fin.ext h36
    subst k
    rw [sourceRowsAt36]
    exact rowSound36 B hB hF
  · have he : k = (37 : Fin 2425) := Fin.ext h37
    subst k
    rw [sourceRowsAt37]
    exact rowSound37 B hB hF
  · have he : k = (38 : Fin 2425) := Fin.ext h38
    subst k
    rw [sourceRowsAt38]
    exact rowSound38 B hB hF
  · have he : k = (39 : Fin 2425) := Fin.ext h39
    subst k
    rw [sourceRowsAt39]
    exact rowSound39 B hB hF
  · have he : k = (40 : Fin 2425) := Fin.ext h40
    subst k
    rw [sourceRowsAt40]
    exact rowSound40 B hB hF
  · have he : k = (41 : Fin 2425) := Fin.ext h41
    subst k
    rw [sourceRowsAt41]
    exact rowSound41 B hB hF
  · have he : k = (42 : Fin 2425) := Fin.ext h42
    subst k
    rw [sourceRowsAt42]
    exact rowSound42 B hB hF
  · have he : k = (43 : Fin 2425) := Fin.ext h43
    subst k
    rw [sourceRowsAt43]
    exact rowSound43 B hB hF
  · have he : k = (44 : Fin 2425) := Fin.ext h44
    subst k
    rw [sourceRowsAt44]
    exact rowSound44 B hB hF
  · have he : k = (45 : Fin 2425) := Fin.ext h45
    subst k
    rw [sourceRowsAt45]
    exact rowSound45 B hB hF
  · have he : k = (46 : Fin 2425) := Fin.ext h46
    subst k
    rw [sourceRowsAt46]
    exact rowSound46 B hB hF
  · have he : k = (47 : Fin 2425) := Fin.ext h47
    subst k
    rw [sourceRowsAt47]
    exact rowSound47 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e_oai
