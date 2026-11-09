-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T19:31:19.533916+00:00
-- url     : https://prove2.me/submissions/ea5784a8-59ba-475d-a7d6-a42fb6a6faef

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E111
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E124
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12 raw12Labels = mixedMoment B node650 node650Labels := by
  calc
    mixedMoment B raw12 raw12Labels = mixedMoment B raw12step0 raw12step0Labels := by
      have ha : raw12step0 = (fun i j => raw12 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12step0 raw12; decide +kernel
      have hl : raw12step0Labels = raw12Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12 raw12Labels permutation2 permutation5
    mixedMoment B raw12step0 raw12step0Labels = mixedMoment B raw12step1 raw12step1Labels := by
      have ha : raw12step1 = raw12step0 := by apply Matrix.ext; unfold raw12step1 raw12step0; decide +kernel
      have hl : raw12step0Labels = labelEmbedding1 ∘ raw12step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12step0 raw12step0Labels raw12step1Labels labelEmbedding1 hl
    _ = mixedMoment B node650 node650Labels := by rfl

theorem canonical13 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13 raw13Labels = mixedMoment B node35 node35Labels := by
  calc
    mixedMoment B raw13 raw13Labels = mixedMoment B raw13step0 raw13step0Labels := by
      have ha : raw13step0 = (fun i j => raw13 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13step0 raw13; decide +kernel
      have hl : raw13step0Labels = raw13Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13 raw13Labels permutation2 permutation4
    _ = mixedMoment B node35 node35Labels := by rfl

theorem canonical38 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38 raw38Labels = mixedMoment B node1173 node1173Labels := by
  calc
    mixedMoment B raw38 raw38Labels = mixedMoment B raw38step0 raw38step0Labels := by
      have ha : raw38step0 = (fun i j => raw38 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw38step0 raw38; decide +kernel
      have hl : raw38step0Labels = raw38Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38 raw38Labels permutation8 permutation5
    mixedMoment B raw38step0 raw38step0Labels = mixedMoment B raw38step1 raw38step1Labels := by
      have ha : raw38step1 = raw38step0 := by apply Matrix.ext; unfold raw38step1 raw38step0; decide +kernel
      have hl : raw38step0Labels = labelEmbedding1 ∘ raw38step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38step0 raw38step0Labels raw38step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1173 node1173Labels := by rfl

theorem canonical39 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39 raw39Labels = mixedMoment B node70 node70Labels := by
  calc
    mixedMoment B raw39 raw39Labels = mixedMoment B raw39step0 raw39step0Labels := by
      have ha : raw39step0 = (fun i j => raw39 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39step0 raw39; decide +kernel
      have hl : raw39step0Labels = raw39Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39 raw39Labels permutation31 permutation4
    mixedMoment B raw39step0 raw39step0Labels = mixedMoment B raw39step1 raw39step1Labels := by
      have ha : raw39step1 = -raw39step0 := by apply Matrix.ext; change ∀ i j, raw39step1 i j = -(raw39step0 i j); unfold raw39step1 raw39step0; decide +kernel
      have hl : raw39step1Labels = raw39step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node70 node70Labels := by rfl

theorem canonical60 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw60 raw60Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw60 raw60Labels = mixedMoment B raw60step0 raw60step0Labels := by
      have ha : raw60step0 = (fun i j => raw60 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw60step0 raw60; decide +kernel
      have hl : raw60step0Labels = raw60Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw60 raw60Labels permutation8 permutation5
    mixedMoment B raw60step0 raw60step0Labels = mixedMoment B raw60step1 raw60step1Labels := by
      have ha : raw60step1 = raw60step0 := by apply Matrix.ext; unfold raw60step1 raw60step0; decide +kernel
      have hl : raw60step0Labels = labelEmbedding1 ∘ raw60step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw60step0 raw60step0Labels raw60step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1271 node1271Labels := by rfl

theorem canonical61 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw61 raw61Labels = mixedMoment B node143 node143Labels := by
  calc
    mixedMoment B raw61 raw61Labels = mixedMoment B raw61step0 raw61step0Labels := by
      have ha : raw61step0 = (fun i j => raw61 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw61step0 raw61; decide +kernel
      have hl : raw61step0Labels = raw61Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw61 raw61Labels permutation8 permutation4
    _ = mixedMoment B node143 node143Labels := by rfl

theorem canonical88 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw88 raw88Labels = mixedMoment B node1308 node1308Labels := by
  calc
    mixedMoment B raw88 raw88Labels = mixedMoment B raw88step0 raw88step0Labels := by
      have ha : raw88step0 = (fun i j => raw88 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw88step0 raw88; decide +kernel
      have hl : raw88step0Labels = raw88Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw88 raw88Labels permutation2 permutation5
    mixedMoment B raw88step0 raw88step0Labels = mixedMoment B raw88step1 raw88step1Labels := by
      have ha : raw88step1 = raw88step0 := by apply Matrix.ext; unfold raw88step1 raw88step0; decide +kernel
      have hl : raw88step0Labels = labelEmbedding1 ∘ raw88step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw88step0 raw88step0Labels raw88step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1308 node1308Labels := by rfl

theorem canonical89 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw89 raw89Labels = mixedMoment B node154 node154Labels := by
  calc
    mixedMoment B raw89 raw89Labels = mixedMoment B raw89step0 raw89step0Labels := by
      have ha : raw89step0 = (fun i j => raw89 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw89step0 raw89; decide +kernel
      have hl : raw89step0Labels = raw89Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw89 raw89Labels permutation2 permutation4
    _ = mixedMoment B node154 node154Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw136 raw136Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw136 raw136Labels = mixedMoment B raw136step0 raw136step0Labels := by
      have ha : raw136step0 = (fun i j => raw136 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw136step0 raw136; decide +kernel
      have hl : raw136step0Labels = raw136Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw136 raw136Labels permutation8 permutation5
    mixedMoment B raw136step0 raw136step0Labels = mixedMoment B raw136step1 raw136step1Labels := by
      have ha : raw136step1 = raw136step0 := by apply Matrix.ext; unfold raw136step1 raw136step0; decide +kernel
      have hl : raw136step0Labels = labelEmbedding1 ∘ raw136step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw136step0 raw136step0Labels raw136step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1416 node1416Labels := by rfl

theorem canonical137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw137 raw137Labels = mixedMoment B node94 node94Labels := by
  calc
    mixedMoment B raw137 raw137Labels = mixedMoment B raw137step0 raw137step0Labels := by
      have ha : raw137step0 = (fun i j => raw137 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw137step0 raw137; decide +kernel
      have hl : raw137step0Labels = raw137Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw137 raw137Labels permutation8 permutation4
    _ = mixedMoment B node94 node94Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19640 raw19640Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw19640 raw19640Labels = mixedMoment B raw19640step0 raw19640step0Labels := by
      have hz : ∀ j, raw19640 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19640step0 = (fun i j => raw19640 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19640step0 raw19640; decide +kernel
      have hl : raw19640step0Labels = raw19640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19640 raw19640Labels permutation434 hz
    mixedMoment B raw19640step0 raw19640step0Labels = mixedMoment B raw19640step1 raw19640step1Labels := by
      have hz : ∀ j, raw19640step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19640step1 = (fun i j => raw19640step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19640step1 raw19640step0; decide +kernel
      have hl : raw19640step1Labels = raw19640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19640step0 raw19640step0Labels permutation80 hz
    mixedMoment B raw19640step1 raw19640step1Labels = mixedMoment B raw19640step2 raw19640step2Labels := by
      have ha : raw19640step2 = (fun i j => raw19640step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19640step2 raw19640step1; decide +kernel
      have hl : raw19640step2Labels = raw19640step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19640step1 raw19640step1Labels permutation31 permutation3
    mixedMoment B raw19640step2 raw19640step2Labels = mixedMoment B raw19640step3 raw19640step3Labels := by
      have ha : raw19640step3 = -raw19640step2 := by apply Matrix.ext; change ∀ i j, raw19640step3 i j = -(raw19640step2 i j); unfold raw19640step3 raw19640step2; decide +kernel
      have hl : raw19640step3Labels = raw19640step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1416 node1416Labels := by rfl

theorem canonical19641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19641 raw19641Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw19641 raw19641Labels = mixedMoment B raw19641step0 raw19641step0Labels := by
      have hz : ∀ j, raw19641 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19641step0 = (fun i j => raw19641 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19641step0 raw19641; decide +kernel
      have hl : raw19641step0Labels = raw19641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19641 raw19641Labels permutation434 hz
    mixedMoment B raw19641step0 raw19641step0Labels = mixedMoment B raw19641step1 raw19641step1Labels := by
      have hz : ∀ j, raw19641step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19641step1 = (fun i j => raw19641step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19641step1 raw19641step0; decide +kernel
      have hl : raw19641step1Labels = raw19641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19641step0 raw19641step0Labels permutation56 hz
    mixedMoment B raw19641step1 raw19641step1Labels = mixedMoment B raw19641step2 raw19641step2Labels := by
      have ha : raw19641step2 = (fun i j => raw19641step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19641step2 raw19641step1; decide +kernel
      have hl : raw19641step2Labels = raw19641step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19641step1 raw19641step1Labels permutation31 permutation3
    mixedMoment B raw19641step2 raw19641step2Labels = mixedMoment B raw19641step3 raw19641step3Labels := by
      have ha : raw19641step3 = -raw19641step2 := by apply Matrix.ext; change ∀ i j, raw19641step3 i j = -(raw19641step2 i j); unfold raw19641step3 raw19641step2; decide +kernel
      have hl : raw19641step3Labels = raw19641step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1416 node1416Labels := by rfl

theorem canonical19642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19642 raw19642Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw19642 raw19642Labels = mixedMoment B raw19642step0 raw19642step0Labels := by
      have hz : ∀ j, raw19642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19642step0 = (fun i j => raw19642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19642step0 raw19642; decide +kernel
      have hl : raw19642step0Labels = raw19642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19642 raw19642Labels permutation346 hz
    mixedMoment B raw19642step0 raw19642step0Labels = mixedMoment B raw19642step1 raw19642step1Labels := by
      have hz : ∀ j, raw19642step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19642step1 = (fun i j => raw19642step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19642step1 raw19642step0; decide +kernel
      have hl : raw19642step1Labels = raw19642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19642step0 raw19642step0Labels permutation56 hz
    mixedMoment B raw19642step1 raw19642step1Labels = mixedMoment B raw19642step2 raw19642step2Labels := by
      have ha : raw19642step2 = (fun i j => raw19642step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19642step2 raw19642step1; decide +kernel
      have hl : raw19642step2Labels = raw19642step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19642step1 raw19642step1Labels permutation31 permutation3
    mixedMoment B raw19642step2 raw19642step2Labels = mixedMoment B raw19642step3 raw19642step3Labels := by
      have ha : raw19642step3 = -raw19642step2 := by apply Matrix.ext; change ∀ i j, raw19642step3 i j = -(raw19642step2 i j); unfold raw19642step3 raw19642step2; decide +kernel
      have hl : raw19642step3Labels = raw19642step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1416 node1416Labels := by rfl

theorem canonical19643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19643 raw19643Labels = mixedMoment B node1450 node1450Labels := by
  calc
    mixedMoment B raw19643 raw19643Labels = mixedMoment B raw19643step0 raw19643step0Labels := by
      have hz : ∀ j, raw19643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19643step0 = (fun i j => raw19643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19643step0 raw19643; decide +kernel
      have hl : raw19643step0Labels = raw19643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19643 raw19643Labels permutation434 hz
    mixedMoment B raw19643step0 raw19643step0Labels = mixedMoment B raw19643step1 raw19643step1Labels := by
      have hz : ∀ j, raw19643step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19643step1 = (fun i j => raw19643step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19643step1 raw19643step0; decide +kernel
      have hl : raw19643step1Labels = raw19643step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19643step0 raw19643step0Labels permutation80 hz
    mixedMoment B raw19643step1 raw19643step1Labels = mixedMoment B raw19643step2 raw19643step2Labels := by
      have hz : ∀ j, raw19643step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19643step2 = (fun i j => raw19643step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19643step2 raw19643step1; decide +kernel
      have hl : raw19643step2Labels = raw19643step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19643step1 raw19643step1Labels permutation14 hz
    mixedMoment B raw19643step2 raw19643step2Labels = mixedMoment B raw19643step3 raw19643step3Labels := by
      have ha : raw19643step3 = (fun i j => raw19643step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19643step3 raw19643step2; decide +kernel
      have hl : raw19643step3Labels = raw19643step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19643step2 raw19643step2Labels permutation7 permutation3
    mixedMoment B raw19643step3 raw19643step3Labels = mixedMoment B raw19643step4 raw19643step4Labels := by
      have ha : raw19643step4 = -raw19643step3 := by apply Matrix.ext; change ∀ i j, raw19643step4 i j = -(raw19643step3 i j); unfold raw19643step4 raw19643step3; decide +kernel
      have hl : raw19643step4Labels = raw19643step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1450 node1450Labels := by rfl

theorem canonical19644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19644 raw19644Labels = mixedMoment B node587 node587Labels := by
  calc
    mixedMoment B raw19644 raw19644Labels = mixedMoment B raw19644step0 raw19644step0Labels := by
      have hz : ∀ j, raw19644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19644step0 = (fun i j => raw19644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19644step0 raw19644; decide +kernel
      have hl : raw19644step0Labels = raw19644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19644 raw19644Labels permutation434 hz
    mixedMoment B raw19644step0 raw19644step0Labels = mixedMoment B raw19644step1 raw19644step1Labels := by
      have hz : ∀ j, raw19644step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19644step1 = (fun i j => raw19644step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19644step1 raw19644step0; decide +kernel
      have hl : raw19644step1Labels = raw19644step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19644step0 raw19644step0Labels permutation80 hz
    mixedMoment B raw19644step1 raw19644step1Labels = mixedMoment B raw19644step2 raw19644step2Labels := by
      have ha : raw19644step2 = (fun i j => raw19644step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19644step2 raw19644step1; decide +kernel
      have hl : raw19644step2Labels = raw19644step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19644step1 raw19644step1Labels permutation10 permutation3
    _ = mixedMoment B node587 node587Labels := by rfl

theorem canonical19645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19645 raw19645Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw19645 raw19645Labels = mixedMoment B raw19645step0 raw19645step0Labels := by
      have hz : ∀ j, raw19645 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19645step0 = (fun i j => raw19645 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19645step0 raw19645; decide +kernel
      have hl : raw19645step0Labels = raw19645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19645 raw19645Labels permutation434 hz
    mixedMoment B raw19645step0 raw19645step0Labels = mixedMoment B raw19645step1 raw19645step1Labels := by
      have ha : raw19645step1 = (fun i j => raw19645step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19645step1 raw19645step0; decide +kernel
      have hl : raw19645step1Labels = raw19645step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19645step0 raw19645step0Labels permutation40 permutation3
    _ = mixedMoment B node1118 node1118Labels := by rfl

theorem canonical19646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19646 raw19646Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw19646 raw19646Labels = mixedMoment B raw19646step0 raw19646step0Labels := by
      have hz : ∀ j, raw19646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19646step0 = (fun i j => raw19646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19646step0 raw19646; decide +kernel
      have hl : raw19646step0Labels = raw19646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19646 raw19646Labels permutation346 hz
    mixedMoment B raw19646step0 raw19646step0Labels = mixedMoment B raw19646step1 raw19646step1Labels := by
      have ha : raw19646step1 = (fun i j => raw19646step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19646step1 raw19646step0; decide +kernel
      have hl : raw19646step1Labels = raw19646step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19646step0 raw19646step0Labels permutation40 permutation3
    _ = mixedMoment B node1118 node1118Labels := by rfl

theorem canonical19647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19647 raw19647Labels = mixedMoment B node1173 node1173Labels := by
  calc
    mixedMoment B raw19647 raw19647Labels = mixedMoment B raw19647step0 raw19647step0Labels := by
      have hz : ∀ j, raw19647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19647step0 = (fun i j => raw19647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19647step0 raw19647; decide +kernel
      have hl : raw19647step0Labels = raw19647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19647 raw19647Labels permutation434 hz
    mixedMoment B raw19647step0 raw19647step0Labels = mixedMoment B raw19647step1 raw19647step1Labels := by
      have hz : ∀ j, raw19647step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19647step1 = (fun i j => raw19647step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19647step1 raw19647step0; decide +kernel
      have hl : raw19647step1Labels = raw19647step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19647step0 raw19647step0Labels permutation80 hz
    mixedMoment B raw19647step1 raw19647step1Labels = mixedMoment B raw19647step2 raw19647step2Labels := by
      have ha : raw19647step2 = (fun i j => raw19647step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19647step2 raw19647step1; decide +kernel
      have hl : raw19647step2Labels = raw19647step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19647step1 raw19647step1Labels permutation10 permutation3
    _ = mixedMoment B node1173 node1173Labels := by rfl

theorem canonical19648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19648 raw19648Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw19648 raw19648Labels = mixedMoment B raw19648step0 raw19648step0Labels := by
      have hz : ∀ j, raw19648 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19648step0 = (fun i j => raw19648 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19648step0 raw19648; decide +kernel
      have hl : raw19648step0Labels = raw19648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19648 raw19648Labels permutation434 hz
    mixedMoment B raw19648step0 raw19648step0Labels = mixedMoment B raw19648step1 raw19648step1Labels := by
      have hz : ∀ j, raw19648step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19648step1 = (fun i j => raw19648step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19648step1 raw19648step0; decide +kernel
      have hl : raw19648step1Labels = raw19648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19648step0 raw19648step0Labels permutation80 hz
    mixedMoment B raw19648step1 raw19648step1Labels = mixedMoment B raw19648step2 raw19648step2Labels := by
      have ha : raw19648step2 = (fun i j => raw19648step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19648step2 raw19648step1; decide +kernel
      have hl : raw19648step2Labels = raw19648step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19648step1 raw19648step1Labels permutation10 permutation3
    _ = mixedMoment B node1271 node1271Labels := by rfl

theorem canonical19649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19649 raw19649Labels = mixedMoment B node587 node587Labels := by
  calc
    mixedMoment B raw19649 raw19649Labels = mixedMoment B raw19649step0 raw19649step0Labels := by
      have hz : ∀ j, raw19649 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19649step0 = (fun i j => raw19649 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19649step0 raw19649; decide +kernel
      have hl : raw19649step0Labels = raw19649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19649 raw19649Labels permutation434 hz
    mixedMoment B raw19649step0 raw19649step0Labels = mixedMoment B raw19649step1 raw19649step1Labels := by
      have hz : ∀ j, raw19649step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19649step1 = (fun i j => raw19649step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19649step1 raw19649step0; decide +kernel
      have hl : raw19649step1Labels = raw19649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19649step0 raw19649step0Labels permutation56 hz
    mixedMoment B raw19649step1 raw19649step1Labels = mixedMoment B raw19649step2 raw19649step2Labels := by
      have ha : raw19649step2 = (fun i j => raw19649step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19649step2 raw19649step1; decide +kernel
      have hl : raw19649step2Labels = raw19649step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19649step1 raw19649step1Labels permutation10 permutation3
    _ = mixedMoment B node587 node587Labels := by rfl

theorem canonical19650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19650 raw19650Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw19650 raw19650Labels = mixedMoment B raw19650step0 raw19650step0Labels := by
      have hz : ∀ j, raw19650 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19650step0 = (fun i j => raw19650 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19650step0 raw19650; decide +kernel
      have hl : raw19650step0Labels = raw19650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19650 raw19650Labels permutation434 hz
    mixedMoment B raw19650step0 raw19650step0Labels = mixedMoment B raw19650step1 raw19650step1Labels := by
      have ha : raw19650step1 = (fun i j => raw19650step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19650step1 raw19650step0; decide +kernel
      have hl : raw19650step1Labels = raw19650step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19650step0 raw19650step0Labels permutation34 permutation3
    _ = mixedMoment B node1118 node1118Labels := by rfl

theorem canonical19651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19651 raw19651Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw19651 raw19651Labels = mixedMoment B raw19651step0 raw19651step0Labels := by
      have hz : ∀ j, raw19651 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19651step0 = (fun i j => raw19651 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19651step0 raw19651; decide +kernel
      have hl : raw19651step0Labels = raw19651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19651 raw19651Labels permutation265 hz
    mixedMoment B raw19651step0 raw19651step0Labels = mixedMoment B raw19651step1 raw19651step1Labels := by
      have ha : raw19651step1 = (fun i j => raw19651step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19651step1 raw19651step0; decide +kernel
      have hl : raw19651step1Labels = raw19651step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19651step0 raw19651step0Labels permutation40 permutation3
    _ = mixedMoment B node1118 node1118Labels := by rfl

theorem canonical19652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19652 raw19652Labels = mixedMoment B node1173 node1173Labels := by
  calc
    mixedMoment B raw19652 raw19652Labels = mixedMoment B raw19652step0 raw19652step0Labels := by
      have hz : ∀ j, raw19652 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19652step0 = (fun i j => raw19652 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19652step0 raw19652; decide +kernel
      have hl : raw19652step0Labels = raw19652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19652 raw19652Labels permutation434 hz
    mixedMoment B raw19652step0 raw19652step0Labels = mixedMoment B raw19652step1 raw19652step1Labels := by
      have hz : ∀ j, raw19652step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19652step1 = (fun i j => raw19652step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19652step1 raw19652step0; decide +kernel
      have hl : raw19652step1Labels = raw19652step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19652step0 raw19652step0Labels permutation56 hz
    mixedMoment B raw19652step1 raw19652step1Labels = mixedMoment B raw19652step2 raw19652step2Labels := by
      have ha : raw19652step2 = (fun i j => raw19652step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19652step2 raw19652step1; decide +kernel
      have hl : raw19652step2Labels = raw19652step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19652step1 raw19652step1Labels permutation10 permutation3
    _ = mixedMoment B node1173 node1173Labels := by rfl

theorem canonical19653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19653 raw19653Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw19653 raw19653Labels = mixedMoment B raw19653step0 raw19653step0Labels := by
      have hz : ∀ j, raw19653 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19653step0 = (fun i j => raw19653 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19653step0 raw19653; decide +kernel
      have hl : raw19653step0Labels = raw19653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19653 raw19653Labels permutation434 hz
    mixedMoment B raw19653step0 raw19653step0Labels = mixedMoment B raw19653step1 raw19653step1Labels := by
      have hz : ∀ j, raw19653step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19653step1 = (fun i j => raw19653step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19653step1 raw19653step0; decide +kernel
      have hl : raw19653step1Labels = raw19653step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19653step0 raw19653step0Labels permutation56 hz
    mixedMoment B raw19653step1 raw19653step1Labels = mixedMoment B raw19653step2 raw19653step2Labels := by
      have ha : raw19653step2 = (fun i j => raw19653step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19653step2 raw19653step1; decide +kernel
      have hl : raw19653step2Labels = raw19653step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19653step1 raw19653step1Labels permutation10 permutation3
    _ = mixedMoment B node1271 node1271Labels := by rfl

theorem canonical19654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19654 raw19654Labels = mixedMoment B node587 node587Labels := by
  calc
    mixedMoment B raw19654 raw19654Labels = mixedMoment B raw19654step0 raw19654step0Labels := by
      have hz : ∀ j, raw19654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19654step0 = (fun i j => raw19654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19654step0 raw19654; decide +kernel
      have hl : raw19654step0Labels = raw19654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19654 raw19654Labels permutation346 hz
    mixedMoment B raw19654step0 raw19654step0Labels = mixedMoment B raw19654step1 raw19654step1Labels := by
      have hz : ∀ j, raw19654step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19654step1 = (fun i j => raw19654step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19654step1 raw19654step0; decide +kernel
      have hl : raw19654step1Labels = raw19654step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19654step0 raw19654step0Labels permutation56 hz
    mixedMoment B raw19654step1 raw19654step1Labels = mixedMoment B raw19654step2 raw19654step2Labels := by
      have ha : raw19654step2 = (fun i j => raw19654step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19654step2 raw19654step1; decide +kernel
      have hl : raw19654step2Labels = raw19654step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19654step1 raw19654step1Labels permutation10 permutation3
    _ = mixedMoment B node587 node587Labels := by rfl

theorem canonical19655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19655 raw19655Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw19655 raw19655Labels = mixedMoment B raw19655step0 raw19655step0Labels := by
      have hz : ∀ j, raw19655 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19655step0 = (fun i j => raw19655 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19655step0 raw19655; decide +kernel
      have hl : raw19655step0Labels = raw19655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19655 raw19655Labels permutation346 hz
    mixedMoment B raw19655step0 raw19655step0Labels = mixedMoment B raw19655step1 raw19655step1Labels := by
      have ha : raw19655step1 = (fun i j => raw19655step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19655step1 raw19655step0; decide +kernel
      have hl : raw19655step1Labels = raw19655step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19655step0 raw19655step0Labels permutation34 permutation3
    _ = mixedMoment B node1118 node1118Labels := by rfl

theorem canonical19656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19656 raw19656Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw19656 raw19656Labels = mixedMoment B raw19656step0 raw19656step0Labels := by
      have hz : ∀ j, raw19656 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19656step0 = (fun i j => raw19656 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19656step0 raw19656; decide +kernel
      have hl : raw19656step0Labels = raw19656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19656 raw19656Labels permutation265 hz
    mixedMoment B raw19656step0 raw19656step0Labels = mixedMoment B raw19656step1 raw19656step1Labels := by
      have ha : raw19656step1 = (fun i j => raw19656step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19656step1 raw19656step0; decide +kernel
      have hl : raw19656step1Labels = raw19656step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19656step0 raw19656step0Labels permutation34 permutation3
    _ = mixedMoment B node1118 node1118Labels := by rfl

theorem canonical19657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19657 raw19657Labels = mixedMoment B node1173 node1173Labels := by
  calc
    mixedMoment B raw19657 raw19657Labels = mixedMoment B raw19657step0 raw19657step0Labels := by
      have hz : ∀ j, raw19657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19657step0 = (fun i j => raw19657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19657step0 raw19657; decide +kernel
      have hl : raw19657step0Labels = raw19657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19657 raw19657Labels permutation346 hz
    mixedMoment B raw19657step0 raw19657step0Labels = mixedMoment B raw19657step1 raw19657step1Labels := by
      have hz : ∀ j, raw19657step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19657step1 = (fun i j => raw19657step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19657step1 raw19657step0; decide +kernel
      have hl : raw19657step1Labels = raw19657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19657step0 raw19657step0Labels permutation56 hz
    mixedMoment B raw19657step1 raw19657step1Labels = mixedMoment B raw19657step2 raw19657step2Labels := by
      have ha : raw19657step2 = (fun i j => raw19657step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19657step2 raw19657step1; decide +kernel
      have hl : raw19657step2Labels = raw19657step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19657step1 raw19657step1Labels permutation10 permutation3
    _ = mixedMoment B node1173 node1173Labels := by rfl

theorem canonical19658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19658 raw19658Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw19658 raw19658Labels = mixedMoment B raw19658step0 raw19658step0Labels := by
      have hz : ∀ j, raw19658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19658step0 = (fun i j => raw19658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19658step0 raw19658; decide +kernel
      have hl : raw19658step0Labels = raw19658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19658 raw19658Labels permutation346 hz
    mixedMoment B raw19658step0 raw19658step0Labels = mixedMoment B raw19658step1 raw19658step1Labels := by
      have hz : ∀ j, raw19658step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19658step1 = (fun i j => raw19658step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19658step1 raw19658step0; decide +kernel
      have hl : raw19658step1Labels = raw19658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19658step0 raw19658step0Labels permutation56 hz
    mixedMoment B raw19658step1 raw19658step1Labels = mixedMoment B raw19658step2 raw19658step2Labels := by
      have ha : raw19658step2 = (fun i j => raw19658step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19658step2 raw19658step1; decide +kernel
      have hl : raw19658step2Labels = raw19658step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19658step1 raw19658step1Labels permutation10 permutation3
    _ = mixedMoment B node1271 node1271Labels := by rfl

theorem canonical19659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19659 raw19659Labels = mixedMoment B node617 node617Labels := by
  calc
    mixedMoment B raw19659 raw19659Labels = mixedMoment B raw19659step0 raw19659step0Labels := by
      have hz : ∀ j, raw19659 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19659step0 = (fun i j => raw19659 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19659step0 raw19659; decide +kernel
      have hl : raw19659step0Labels = raw19659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19659 raw19659Labels permutation434 hz
    mixedMoment B raw19659step0 raw19659step0Labels = mixedMoment B raw19659step1 raw19659step1Labels := by
      have hz : ∀ j, raw19659step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19659step1 = (fun i j => raw19659step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19659step1 raw19659step0; decide +kernel
      have hl : raw19659step1Labels = raw19659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19659step0 raw19659step0Labels permutation80 hz
    mixedMoment B raw19659step1 raw19659step1Labels = mixedMoment B raw19659step2 raw19659step2Labels := by
      have hz : ∀ j, raw19659step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19659step2 = (fun i j => raw19659step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19659step2 raw19659step1; decide +kernel
      have hl : raw19659step2Labels = raw19659step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19659step1 raw19659step1Labels permutation14 hz
    mixedMoment B raw19659step2 raw19659step2Labels = mixedMoment B raw19659step3 raw19659step3Labels := by
      have ha : raw19659step3 = (fun i j => raw19659step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19659step3 raw19659step2; decide +kernel
      have hl : raw19659step3Labels = raw19659step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19659step2 raw19659step2Labels permutation2 permutation3
    _ = mixedMoment B node617 node617Labels := by rfl

theorem canonical19660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19660 raw19660Labels = mixedMoment B node1142 node1142Labels := by
  calc
    mixedMoment B raw19660 raw19660Labels = mixedMoment B raw19660step0 raw19660step0Labels := by
      have hz : ∀ j, raw19660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19660step0 = (fun i j => raw19660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19660step0 raw19660; decide +kernel
      have hl : raw19660step0Labels = raw19660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19660 raw19660Labels permutation434 hz
    mixedMoment B raw19660step0 raw19660step0Labels = mixedMoment B raw19660step1 raw19660step1Labels := by
      have hz : ∀ j, raw19660step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19660step1 = (fun i j => raw19660step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19660step1 raw19660step0; decide +kernel
      have hl : raw19660step1Labels = raw19660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19660step0 raw19660step0Labels permutation80 hz
    mixedMoment B raw19660step1 raw19660step1Labels = mixedMoment B raw19660step2 raw19660step2Labels := by
      have ha : raw19660step2 = (fun i j => raw19660step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19660step2 raw19660step1; decide +kernel
      have hl : raw19660step2Labels = raw19660step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19660step1 raw19660step1Labels permutation8 permutation3
    _ = mixedMoment B node1142 node1142Labels := by rfl

theorem canonical19661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19661 raw19661Labels = mixedMoment B node1142 node1142Labels := by
  calc
    mixedMoment B raw19661 raw19661Labels = mixedMoment B raw19661step0 raw19661step0Labels := by
      have hz : ∀ j, raw19661 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19661step0 = (fun i j => raw19661 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19661step0 raw19661; decide +kernel
      have hl : raw19661step0Labels = raw19661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19661 raw19661Labels permutation434 hz
    mixedMoment B raw19661step0 raw19661step0Labels = mixedMoment B raw19661step1 raw19661step1Labels := by
      have hz : ∀ j, raw19661step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19661step1 = (fun i j => raw19661step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19661step1 raw19661step0; decide +kernel
      have hl : raw19661step1Labels = raw19661step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19661step0 raw19661step0Labels permutation56 hz
    mixedMoment B raw19661step1 raw19661step1Labels = mixedMoment B raw19661step2 raw19661step2Labels := by
      have ha : raw19661step2 = (fun i j => raw19661step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19661step2 raw19661step1; decide +kernel
      have hl : raw19661step2Labels = raw19661step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19661step1 raw19661step1Labels permutation8 permutation3
    _ = mixedMoment B node1142 node1142Labels := by rfl

theorem canonical19662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19662 raw19662Labels = mixedMoment B node1142 node1142Labels := by
  calc
    mixedMoment B raw19662 raw19662Labels = mixedMoment B raw19662step0 raw19662step0Labels := by
      have hz : ∀ j, raw19662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19662step0 = (fun i j => raw19662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19662step0 raw19662; decide +kernel
      have hl : raw19662step0Labels = raw19662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19662 raw19662Labels permutation346 hz
    mixedMoment B raw19662step0 raw19662step0Labels = mixedMoment B raw19662step1 raw19662step1Labels := by
      have hz : ∀ j, raw19662step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19662step1 = (fun i j => raw19662step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19662step1 raw19662step0; decide +kernel
      have hl : raw19662step1Labels = raw19662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19662step0 raw19662step0Labels permutation56 hz
    mixedMoment B raw19662step1 raw19662step1Labels = mixedMoment B raw19662step2 raw19662step2Labels := by
      have ha : raw19662step2 = (fun i j => raw19662step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19662step2 raw19662step1; decide +kernel
      have hl : raw19662step2Labels = raw19662step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19662step1 raw19662step1Labels permutation8 permutation3
    _ = mixedMoment B node1142 node1142Labels := by rfl

theorem canonical19663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19663 raw19663Labels = mixedMoment B node591 node591Labels := by
  calc
    mixedMoment B raw19663 raw19663Labels = mixedMoment B raw19663step0 raw19663step0Labels := by
      have hz : ∀ j, raw19663 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19663step0 = (fun i j => raw19663 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19663step0 raw19663; decide +kernel
      have hl : raw19663step0Labels = raw19663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19663 raw19663Labels permutation434 hz
    mixedMoment B raw19663step0 raw19663step0Labels = mixedMoment B raw19663step1 raw19663step1Labels := by
      have hz : ∀ j, raw19663step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19663step1 = (fun i j => raw19663step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19663step1 raw19663step0; decide +kernel
      have hl : raw19663step1Labels = raw19663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19663step0 raw19663step0Labels permutation80 hz
    mixedMoment B raw19663step1 raw19663step1Labels = mixedMoment B raw19663step2 raw19663step2Labels := by
      have hz : ∀ j, raw19663step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19663step2 = (fun i j => raw19663step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19663step2 raw19663step1; decide +kernel
      have hl : raw19663step2Labels = raw19663step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19663step1 raw19663step1Labels permutation14 hz
    mixedMoment B raw19663step2 raw19663step2Labels = mixedMoment B raw19663step3 raw19663step3Labels := by
      have ha : raw19663step3 = (fun i j => raw19663step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19663step3 raw19663step2; decide +kernel
      have hl : raw19663step3Labels = raw19663step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19663step2 raw19663step2Labels permutation2 permutation3
    _ = mixedMoment B node591 node591Labels := by rfl

theorem canonical19664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19664 raw19664Labels = mixedMoment B node633 node633Labels := by
  calc
    mixedMoment B raw19664 raw19664Labels = mixedMoment B raw19664step0 raw19664step0Labels := by
      have hz : ∀ j, raw19664 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19664step0 = (fun i j => raw19664 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19664step0 raw19664; decide +kernel
      have hl : raw19664step0Labels = raw19664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19664 raw19664Labels permutation434 hz
    mixedMoment B raw19664step0 raw19664step0Labels = mixedMoment B raw19664step1 raw19664step1Labels := by
      have hz : ∀ j, raw19664step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19664step1 = (fun i j => raw19664step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19664step1 raw19664step0; decide +kernel
      have hl : raw19664step1Labels = raw19664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19664step0 raw19664step0Labels permutation80 hz
    mixedMoment B raw19664step1 raw19664step1Labels = mixedMoment B raw19664step2 raw19664step2Labels := by
      have ha : raw19664step2 = (fun i j => raw19664step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19664step2 raw19664step1; decide +kernel
      have hl : raw19664step2Labels = raw19664step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19664step1 raw19664step1Labels permutation31 permutation3
    mixedMoment B raw19664step2 raw19664step2Labels = mixedMoment B raw19664step3 raw19664step3Labels := by
      have ha : raw19664step3 = -raw19664step2 := by apply Matrix.ext; change ∀ i j, raw19664step3 i j = -(raw19664step2 i j); unfold raw19664step3 raw19664step2; decide +kernel
      have hl : raw19664step3Labels = raw19664step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node633 node633Labels := by rfl

theorem canonical19665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19665 raw19665Labels = mixedMoment B node633 node633Labels := by
  calc
    mixedMoment B raw19665 raw19665Labels = mixedMoment B raw19665step0 raw19665step0Labels := by
      have hz : ∀ j, raw19665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19665step0 = (fun i j => raw19665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19665step0 raw19665; decide +kernel
      have hl : raw19665step0Labels = raw19665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19665 raw19665Labels permutation434 hz
    mixedMoment B raw19665step0 raw19665step0Labels = mixedMoment B raw19665step1 raw19665step1Labels := by
      have hz : ∀ j, raw19665step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19665step1 = (fun i j => raw19665step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19665step1 raw19665step0; decide +kernel
      have hl : raw19665step1Labels = raw19665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19665step0 raw19665step0Labels permutation56 hz
    mixedMoment B raw19665step1 raw19665step1Labels = mixedMoment B raw19665step2 raw19665step2Labels := by
      have ha : raw19665step2 = (fun i j => raw19665step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19665step2 raw19665step1; decide +kernel
      have hl : raw19665step2Labels = raw19665step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19665step1 raw19665step1Labels permutation31 permutation3
    mixedMoment B raw19665step2 raw19665step2Labels = mixedMoment B raw19665step3 raw19665step3Labels := by
      have ha : raw19665step3 = -raw19665step2 := by apply Matrix.ext; change ∀ i j, raw19665step3 i j = -(raw19665step2 i j); unfold raw19665step3 raw19665step2; decide +kernel
      have hl : raw19665step3Labels = raw19665step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node633 node633Labels := by rfl

theorem canonical19666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19666 raw19666Labels = mixedMoment B node633 node633Labels := by
  calc
    mixedMoment B raw19666 raw19666Labels = mixedMoment B raw19666step0 raw19666step0Labels := by
      have hz : ∀ j, raw19666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19666step0 = (fun i j => raw19666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19666step0 raw19666; decide +kernel
      have hl : raw19666step0Labels = raw19666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19666 raw19666Labels permutation346 hz
    mixedMoment B raw19666step0 raw19666step0Labels = mixedMoment B raw19666step1 raw19666step1Labels := by
      have hz : ∀ j, raw19666step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19666step1 = (fun i j => raw19666step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19666step1 raw19666step0; decide +kernel
      have hl : raw19666step1Labels = raw19666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19666step0 raw19666step0Labels permutation56 hz
    mixedMoment B raw19666step1 raw19666step1Labels = mixedMoment B raw19666step2 raw19666step2Labels := by
      have ha : raw19666step2 = (fun i j => raw19666step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19666step2 raw19666step1; decide +kernel
      have hl : raw19666step2Labels = raw19666step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19666step1 raw19666step1Labels permutation31 permutation3
    mixedMoment B raw19666step2 raw19666step2Labels = mixedMoment B raw19666step3 raw19666step3Labels := by
      have ha : raw19666step3 = -raw19666step2 := by apply Matrix.ext; change ∀ i j, raw19666step3 i j = -(raw19666step2 i j); unfold raw19666step3 raw19666step2; decide +kernel
      have hl : raw19666step3Labels = raw19666step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node633 node633Labels := by rfl

theorem canonical19667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19667 raw19667Labels = mixedMoment B node650 node650Labels := by
  calc
    mixedMoment B raw19667 raw19667Labels = mixedMoment B raw19667step0 raw19667step0Labels := by
      have hz : ∀ j, raw19667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19667step0 = (fun i j => raw19667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19667step0 raw19667; decide +kernel
      have hl : raw19667step0Labels = raw19667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19667 raw19667Labels permutation434 hz
    mixedMoment B raw19667step0 raw19667step0Labels = mixedMoment B raw19667step1 raw19667step1Labels := by
      have hz : ∀ j, raw19667step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19667step1 = (fun i j => raw19667step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19667step1 raw19667step0; decide +kernel
      have hl : raw19667step1Labels = raw19667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19667step0 raw19667step0Labels permutation80 hz
    mixedMoment B raw19667step1 raw19667step1Labels = mixedMoment B raw19667step2 raw19667step2Labels := by
      have hz : ∀ j, raw19667step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19667step2 = (fun i j => raw19667step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19667step2 raw19667step1; decide +kernel
      have hl : raw19667step2Labels = raw19667step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19667step1 raw19667step1Labels permutation14 hz
    mixedMoment B raw19667step2 raw19667step2Labels = mixedMoment B raw19667step3 raw19667step3Labels := by
      have ha : raw19667step3 = (fun i j => raw19667step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19667step3 raw19667step2; decide +kernel
      have hl : raw19667step3Labels = raw19667step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19667step2 raw19667step2Labels permutation7 permutation3
    mixedMoment B raw19667step3 raw19667step3Labels = mixedMoment B raw19667step4 raw19667step4Labels := by
      have ha : raw19667step4 = -raw19667step3 := by apply Matrix.ext; change ∀ i j, raw19667step4 i j = -(raw19667step3 i j); unfold raw19667step4 raw19667step3; decide +kernel
      have hl : raw19667step4Labels = raw19667step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node650 node650Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10285 raw10285Labels = mixedMoment B node1308 node1308Labels := by
  calc
    mixedMoment B raw10285 raw10285Labels = mixedMoment B raw10285step0 raw10285step0Labels := by
      have hz : ∀ j, raw10285 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10285step0 = (fun i j => raw10285 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10285step0 raw10285; decide +kernel
      have hl : raw10285step0Labels = raw10285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10285 raw10285Labels permutation434 hz
    mixedMoment B raw10285step0 raw10285step0Labels = mixedMoment B raw10285step1 raw10285step1Labels := by
      have hz : ∀ j, raw10285step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10285step1 = (fun i j => raw10285step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10285step1 raw10285step0; decide +kernel
      have hl : raw10285step1Labels = raw10285step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10285step0 raw10285step0Labels permutation80 hz
    mixedMoment B raw10285step1 raw10285step1Labels = mixedMoment B raw10285step2 raw10285step2Labels := by
      have hz : ∀ j, raw10285step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10285step2 = (fun i j => raw10285step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10285step2 raw10285step1; decide +kernel
      have hl : raw10285step2Labels = raw10285step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10285step1 raw10285step1Labels permutation14 hz
    mixedMoment B raw10285step2 raw10285step2Labels = mixedMoment B raw10285step3 raw10285step3Labels := by
      have ha : raw10285step3 = (fun i j => raw10285step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10285step3 raw10285step2; decide +kernel
      have hl : raw10285step3Labels = raw10285step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10285step2 raw10285step2Labels permutation2 permutation3
    _ = mixedMoment B node1308 node1308Labels := by rfl

theorem canonical10289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10289 raw10289Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw10289 raw10289Labels = mixedMoment B raw10289step0 raw10289step0Labels := by
      have hz : ∀ j, raw10289 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10289step0 = (fun i j => raw10289 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10289step0 raw10289; decide +kernel
      have hl : raw10289step0Labels = raw10289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10289 raw10289Labels permutation434 hz
    mixedMoment B raw10289step0 raw10289step0Labels = mixedMoment B raw10289step1 raw10289step1Labels := by
      have hz : ∀ j, raw10289step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10289step1 = (fun i j => raw10289step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10289step1 raw10289step0; decide +kernel
      have hl : raw10289step1Labels = raw10289step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10289step0 raw10289step0Labels permutation80 hz
    mixedMoment B raw10289step1 raw10289step1Labels = mixedMoment B raw10289step2 raw10289step2Labels := by
      have hz : ∀ j, raw10289step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10289step2 = (fun i j => raw10289step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10289step2 raw10289step1; decide +kernel
      have hl : raw10289step2Labels = raw10289step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10289step1 raw10289step1Labels permutation14 hz
    mixedMoment B raw10289step2 raw10289step2Labels = mixedMoment B raw10289step3 raw10289step3Labels := by
      have ha : raw10289step3 = (fun i j => raw10289step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10289step3 raw10289step2; decide +kernel
      have hl : raw10289step3Labels = raw10289step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10289step2 raw10289step2Labels permutation2 permutation3
    _ = mixedMoment B node3114 node3114Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical27 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw27 = injectiveMoment H node48 := by
  calc
    injectiveMoment H raw27 = injectiveMoment H raw27step0 := by
      have heq : raw27step0 = raw27.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw27).symm
    injectiveMoment H raw27step0 = injectiveMoment H raw27step1 := by
      have heq : raw27step1 = -raw27step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw27step0).symm
    injectiveMoment H raw27step1 = injectiveMoment H raw27step2 := by
      have heq : raw27step2 = (fun i j => raw27step1 (permutation3 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw27step1 permutation3 permutation6
    _ = injectiveMoment H node48 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical34 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw34 = injectiveMoment H node7 := by
  calc
    injectiveMoment H raw34 = injectiveMoment H raw34step0 := by
      have heq : raw34step0 = raw34.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw34).symm
    _ = injectiveMoment H node7 := by rfl

theorem canonical35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw35 = injectiveMoment H node7 := by
  calc
    injectiveMoment H raw35 = injectiveMoment H raw35step0 := by
      have heq : raw35step0 = raw35.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw35).symm
    injectiveMoment H raw35step0 = injectiveMoment H raw35step1 := by
      have heq : raw35step1 = (fun i j => raw35step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw35step0 permutation4 permutation1
    _ = injectiveMoment H node7 := by rfl

theorem canonical48 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw48 = injectiveMoment H node6 := by
  rfl

theorem canonical53 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw53 = injectiveMoment H node1 := by
  rfl

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

theorem canonical5132 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5132 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5132 = injectiveMoment H raw5132step0 := by
      have hz : ∀ j, raw5132 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5132step0 = (fun i j => raw5132 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5132 permutation21 hz
    injectiveMoment H raw5132step0 = injectiveMoment H raw5132step1 := by
      have heq : raw5132step1 = (fun i j => raw5132step0 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5132step0 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

theorem canonical5151 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5151 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5151 = injectiveMoment H raw5151step0 := by
      have heq : raw5151step0 = (fun i j => raw5151 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5151 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

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

theorem canonical5214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5214 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5214 = injectiveMoment H raw5214step0 := by
      have hz : ∀ j, raw5214 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw5214step0 = (fun i j => raw5214 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5214 permutation7 hz
    _ = injectiveMoment H node4 := by rfl

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

theorem canonical7979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7979 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7979 = injectiveMoment H raw7979step0 := by
      have hz : ∀ j, raw7979 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7979step0 = (fun i j => raw7979 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979 permutation7 hz
    injectiveMoment H raw7979step0 = injectiveMoment H raw7979step1 := by
      have hz : ∀ j, raw7979step0 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7979step1 = (fun i j => raw7979step0 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step0 permutation2 hz
    injectiveMoment H raw7979step1 = injectiveMoment H raw7979step2 := by
      have hz : ∀ j, raw7979step1 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7979step2 = (fun i j => raw7979step1 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step1 permutation0 hz
    injectiveMoment H raw7979step2 = injectiveMoment H raw7979step3 := by
      have hz : ∀ i, raw7979step2 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7979step3 = (fun i j => raw7979step2 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7979step2 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical909 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw909 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw909 = injectiveMoment H raw909step0 := by
      have hz : ∀ j, raw909 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw909step0 = (fun i j => raw909 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw909 permutation21 hz
    _ = injectiveMoment H node10 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5459 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5459 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw5459 = injectiveMoment H raw5459step0 := by
      have heq : raw5459step0 = raw5459.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5459).symm
    injectiveMoment H raw5459step0 = injectiveMoment H raw5459step1 := by
      have heq : raw5459step1 = (fun i j => raw5459step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5459step0 permutation5 permutation2
    _ = injectiveMoment H node9 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5540 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5540 = injectiveMoment H node51 := by
  rfl

theorem canonical5550 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5550 = injectiveMoment H node53 := by
  rfl

theorem canonical5554 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5554 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw5554 = injectiveMoment H raw5554step0 := by
      have heq : raw5554step0 = (fun i j => raw5554 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5554 permutation4 permutation3
    _ = injectiveMoment H node53 := by rfl

theorem canonical5556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5556 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw5556 = injectiveMoment H raw5556step0 := by
      have heq : raw5556step0 = raw5556.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5556).symm
    injectiveMoment H raw5556step0 = injectiveMoment H raw5556step1 := by
      have heq : raw5556step1 = (fun i j => raw5556step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5556step0 permutation7 permutation2
    _ = injectiveMoment H node8 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical250
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8005 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8005 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw8005 = injectiveMoment H raw8005step0 := by
      have hz : ∀ i, raw8005 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8005step0 = (fun i j => raw8005 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8005 permutation3 hz
    _ = injectiveMoment H node3 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical928 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw928 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw928 = injectiveMoment H raw928step0 := by
      have heq : raw928step0 = raw928.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw928).symm
    injectiveMoment H raw928step0 = injectiveMoment H raw928step1 := by
      have heq : raw928step1 = (fun i j => raw928step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw928step0 permutation6 permutation2
    _ = injectiveMoment H node8 := by rfl

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

theorem canonical161 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw161 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw161 = injectiveMoment H raw161step0 := by
      have heq : raw161step0 = -raw161 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw161).symm
    injectiveMoment H raw161step0 = injectiveMoment H raw161step1 := by
      have heq : raw161step1 = (fun i j => raw161step0 (permutation13 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw161step0 permutation13 permutation6
    _ = injectiveMoment H node155 := by rfl

theorem canonical172 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw172 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw172 = injectiveMoment H raw172step0 := by
      have heq : raw172step0 = -raw172 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw172).symm
    injectiveMoment H raw172step0 = injectiveMoment H raw172step1 := by
      have heq : raw172step1 = (fun i j => raw172step0 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw172step0 permutation4 permutation6
    _ = injectiveMoment H node32 := by rfl

theorem canonical180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw180 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw180 = injectiveMoment H raw180step0 := by
      have heq : raw180step0 = raw180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw180).symm
    _ = injectiveMoment H node9 := by rfl

theorem canonical182 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw182 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw182 = injectiveMoment H raw182step0 := by
      have heq : raw182step0 = raw182.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw182).symm
    injectiveMoment H raw182step0 = injectiveMoment H raw182step1 := by
      have heq : raw182step1 = (fun i j => raw182step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw182step0 permutation4 permutation1
    _ = injectiveMoment H node8 := by rfl

theorem canonical190 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw190 = injectiveMoment H node14 := by
  rfl

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

theorem canonical198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw198 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw198 = injectiveMoment H raw198step0 := by
      have hz : ∀ j, raw198 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw198step0 = (fun i j => raw198 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw198 permutation15 hz
    _ = injectiveMoment H node8 := by rfl

theorem canonical200 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw200 = injectiveMoment H node2 := by
  calc
    injectiveMoment H raw200 = injectiveMoment H raw200step0 := by
      have hz : ∀ j, raw200 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw200step0 = (fun i j => raw200 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw200 permutation5 hz
    _ = injectiveMoment H node2 := by rfl

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

theorem sound1 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node1 = Sparse.eval value1 (momentVector H) := by
  have hc : momentVector H 58 = injectiveMoment H node1 := rfl
  simp [value1, Sparse.eval, hc]

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

theorem sound6 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node6 = Sparse.eval value6 (momentVector H) := by
  have heq : pivotMatrix6 = (fun u v => node6 (pivotPermutation6 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node6 = injectiveMoment H pivotMatrix6 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix6 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix6 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix6 (0 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix6 (0 : Fin 2) = raw215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical215 hH).trans (sound2 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix6 (1 : Fin 2)) =
      Sparse.eval value1 (momentVector H) := by
    have heq : mergeFirst pivotMatrix6 (1 : Fin 2) = raw53 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical53 hH).trans (sound1 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node6 + (injectiveMoment H (mergeFirst pivotMatrix6 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix6 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value6, value1, value2, Sparse.eval] at hc ⊢
  linarith

theorem sound7 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node7 = Sparse.eval value7 (momentVector H) := by
  have hc : momentVector H 9 = injectiveMoment H node7 := rfl
  simp [value7, Sparse.eval, hc]

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

theorem sound14 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node14 = Sparse.eval value14 (momentVector H) := by
  have heq : pivotMatrix14 = (fun u v => node14 (pivotPermutation14 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node14 = injectiveMoment H pivotMatrix14 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix14 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix14 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix14 (0 : Fin 3)) =
      Sparse.eval value6 (momentVector H) := by
    have heq : mergeFirst pivotMatrix14 (0 : Fin 3) = raw48 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical48 hH).trans (sound6 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix14 (1 : Fin 3)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix14 (1 : Fin 3) = raw200 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical200 hH).trans (sound2 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix14 (2 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix14 (2 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node14 + (injectiveMoment H (mergeFirst pivotMatrix14 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix14 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix14 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value14, value2, value6, value8, Sparse.eval] at hc ⊢
  linarith

theorem sound32 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node32 = Sparse.eval value32 (momentVector H) := by
  have hc : momentVector H 35 = injectiveMoment H node32 := rfl
  simp [value32, Sparse.eval, hc]

theorem sound48 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node48 = Sparse.eval value48 (momentVector H) := by
  have heq : pivotMatrix48 = (fun u v => node48.transpose (pivotPermutation48 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node48 = injectiveMoment H pivotMatrix48 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix48 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix48 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix48 (0 : Fin 2)) =
      Sparse.eval value7 (momentVector H) := by
    have heq : mergeFirst pivotMatrix48 (0 : Fin 2) = raw34 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical34 hH).trans (sound7 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix48 (1 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix48 (1 : Fin 2) = raw180 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical180 hH).trans (sound9 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node48 + (injectiveMoment H (mergeFirst pivotMatrix48 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix48 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value48, value7, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound49 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node49 = Sparse.eval value49 (momentVector H) := by
  have heq : pivotMatrix49 = (fun u v => node49.transpose (pivotPermutation49 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node49 = injectiveMoment H pivotMatrix49 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix49 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix49 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix49 (0 : Fin 2)) =
      Sparse.eval value7 (momentVector H) := by
    have heq : mergeFirst pivotMatrix49 (0 : Fin 2) = raw35 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical35 hH).trans (sound7 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix49 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix49 (1 : Fin 2) = raw182 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical182 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node49 + (injectiveMoment H (mergeFirst pivotMatrix49 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix49 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value49, value7, value8, Sparse.eval] at hc ⊢
  linarith

theorem sound51 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node51 = Sparse.eval value51 (momentVector H) := by
  have heq : pivotMatrix51 = (fun u v => node51 (pivotPermutation51 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node51 = injectiveMoment H pivotMatrix51 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix51 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix51 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix51 (0 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix51 (0 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix51 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix51 (1 : Fin 2) = raw5556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5556 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node51 + (injectiveMoment H (mergeFirst pivotMatrix51 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix51 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value51, value10, value8, Sparse.eval] at hc ⊢
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

theorem sound53 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node53 = Sparse.eval value53 (momentVector H) := by
  have heq : pivotMatrix53 = (fun u v => node53 (pivotPermutation53 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node53 = injectiveMoment H pivotMatrix53 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix53 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix53 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix53 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix53 (0 : Fin 2) = raw8005 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8005 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix53 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix53 (1 : Fin 2) = raw5556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5556 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node53 + (injectiveMoment H (mergeFirst pivotMatrix53 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix53 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value53, value3, value8, Sparse.eval] at hc ⊢
  linarith

theorem sound59 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node59 = Sparse.eval value59 (momentVector H) := by
  have heq : pivotMatrix59 = (fun u v => node59.transpose (pivotPermutation59 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node59 = injectiveMoment H pivotMatrix59 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix59 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix59 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix59 (0 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix59 (0 : Fin 2) = raw928 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical928 hH).trans (sound8 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix59 (1 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix59 (1 : Fin 2) = raw5459 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5459 hH).trans (sound9 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node59 + (injectiveMoment H (mergeFirst pivotMatrix59 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix59 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value59, value8, value9, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical962 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw962 = injectiveMoment H node49 := by
  calc
    injectiveMoment H raw962 = injectiveMoment H raw962step0 := by
      have heq : raw962step0 = raw962.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw962).symm
    injectiveMoment H raw962step0 = injectiveMoment H raw962step1 := by
      have heq : raw962step1 = (fun i j => raw962step0 (permutation8 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw962step0 permutation8 permutation6
    _ = injectiveMoment H node49 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1439 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1439 = injectiveMoment H node32 := by
  rfl

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

theorem canonical1446 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1446 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw1446 = injectiveMoment H raw1446step0 := by
      have heq : raw1446step0 = raw1446.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1446).symm
    injectiveMoment H raw1446step0 = injectiveMoment H raw1446step1 := by
      have heq : raw1446step1 = (fun i j => raw1446step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1446step0 permutation6 permutation5
    _ = injectiveMoment H node59 := by rfl

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

theorem canonical1450 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1450 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1450 = injectiveMoment H raw1450step0 := by
      have heq : raw1450step0 = raw1450.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1450).symm
    injectiveMoment H raw1450step0 = injectiveMoment H raw1450step1 := by
      have heq : raw1450step1 = (fun i j => raw1450step0 (permutation8 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1450step0 permutation8 permutation8
    _ = injectiveMoment H node52 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound143 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node143 = Sparse.eval value143 (momentVector H) := by
  have heq : pivotMatrix143 = (fun u v => node143 (pivotPermutation143 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node143 = injectiveMoment H pivotMatrix143 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix143 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix143 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix143 (0 : Fin 3)) =
      Sparse.eval value49 (momentVector H) := by
    have heq : mergeFirst pivotMatrix143 (0 : Fin 3) = raw962 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical962 hH).trans (sound49 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix143 (1 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix143 (1 : Fin 3) = raw1446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1446 hH).trans (sound59 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix143 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix143 (2 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node143 + (injectiveMoment H (mergeFirst pivotMatrix143 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix143 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix143 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value143, value49, value52, value59, Sparse.eval] at hc ⊢
  linarith

theorem sound155 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node155 = Sparse.eval value155 (momentVector H) := by
  have heq : pivotMatrix155 = (fun u v => node155 (pivotPermutation155 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node155 = injectiveMoment H pivotMatrix155 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix155 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix155 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix155 (0 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix155 (0 : Fin 3) = raw5550 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5550 hH).trans (sound53 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix155 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix155 (1 : Fin 3) = raw1450 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1450 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix155 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix155 (2 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node155 + (injectiveMoment H (mergeFirst pivotMatrix155 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix155 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix155 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value155, value32, value52, value53, Sparse.eval] at hc ⊢
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

theorem sound243 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node243 = Sparse.eval value243 (momentVector H) := by
  have heq : pivotMatrix243 = (fun u v => node243 (pivotPermutation243 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node243 = injectiveMoment H pivotMatrix243 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix243 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix243 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix243 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix243 (0 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix243 (1 : Fin 3)) =
      Sparse.eval value51 (momentVector H) := by
    have heq : mergeFirst pivotMatrix243 (1 : Fin 3) = raw5540 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5540 hH).trans (sound51 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix243 (2 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix243 (2 : Fin 3) = raw5554 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5554 hH).trans (sound53 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node243 + (injectiveMoment H (mergeFirst pivotMatrix243 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix243 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix243 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value243, value51, value52, value53, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair35 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node35 node35Labels = Sparse.eval singlePairValue35 (familyPairVector B) := by
  have hp := single_label_three B hB node35
  have hl : node35Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node35 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node35 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node35 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node35 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node35 (EqualityPatterns.family3.label 1) = PairSemantics.raw917 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node35 PairSemantics.raw917; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical917 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node35 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node35 (EqualityPatterns.family3.label 2) = PairSemantics.raw5183 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node35 PairSemantics.raw5183; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5183 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node35 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value6 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node35 (EqualityPatterns.family3.label 3) = PairSemantics.raw48 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node35 PairSemantics.raw48; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical48 hH).trans (PairSemantics.sound6 hH)
  have hm4 : familyPairMoment B (groupedColumns node35 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value48 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node35 (EqualityPatterns.family3.label 4) = PairSemantics.raw27 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node35 PairSemantics.raw27; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical27 hH).trans (PairSemantics.sound48 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue35, PairSemantics.value0, PairSemantics.value4, PairSemantics.value6, PairSemantics.value10, PairSemantics.value48, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical88 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw88 = injectiveMoment H node143 := by
  calc
    injectiveMoment H raw88 = injectiveMoment H raw88step0 := by
      have heq : raw88step0 = (fun i j => raw88 (permutation32 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw88 permutation32 permutation6
    _ = injectiveMoment H node143 := by rfl

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

theorem canonical7678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7678 = injectiveMoment H node65 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair70 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node70 node70Labels = Sparse.eval singlePairValue70 (familyPairVector B) := by
  have hp := single_label_three B hB node70
  have hl : node70Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node70 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node70 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node70 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node70 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node70 (EqualityPatterns.family3.label 1) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node70 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node70 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node70 (EqualityPatterns.family3.label 2) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node70 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node70 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value14 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node70 (EqualityPatterns.family3.label 3) = PairSemantics.raw190 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node70 PairSemantics.raw190; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical190 hH).trans (PairSemantics.sound14 hH)
  have hm4 : familyPairMoment B (groupedColumns node70 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value143 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node70 (EqualityPatterns.family3.label 4) = PairSemantics.raw88 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node70 PairSemantics.raw88; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical88 hH).trans (PairSemantics.sound143 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue70, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value14, PairSemantics.value143, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical112 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw112 = injectiveMoment H node243 := by
  calc
    injectiveMoment H raw112 = injectiveMoment H raw112step0 := by
      have heq : raw112step0 = -raw112 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw112).symm
    injectiveMoment H raw112step0 = injectiveMoment H raw112step1 := by
      have heq : raw112step1 = (fun i j => raw112step0 (permutation9 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw112step0 permutation9 permutation6
    _ = injectiveMoment H node243 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair94 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node94 node94Labels = Sparse.eval singlePairValue94 (familyPairVector B) := by
  have hp := single_label_three B hB node94
  have hl : node94Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node94 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node94 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node94 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node94 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node94 (EqualityPatterns.family3.label 1) = PairSemantics.raw909 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node94 PairSemantics.raw909; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical909 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node94 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node94 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node94 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node94 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node94 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node94 PairSemantics.raw198; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node94 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value243 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node94 (EqualityPatterns.family3.label 4) = PairSemantics.raw112 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node94 PairSemantics.raw112; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical112 hH).trans (PairSemantics.sound243 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue94, PairSemantics.value0, PairSemantics.value8, PairSemantics.value10, PairSemantics.value65, PairSemantics.value243, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node143 node143Labels = Sparse.eval singlePairValue143 (familyPairVector B) := by
  have hp := single_label_three B hB node143
  have hl : node143Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node143 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 1) = PairSemantics.raw5132 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node143 PairSemantics.raw5132
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5132 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 2) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node143 PairSemantics.raw5204
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node143 PairSemantics.raw198
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value155 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 4) = PairSemantics.raw161 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node143 PairSemantics.raw161
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical161 hH).trans (PairSemantics.sound155 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue143, PairSemantics.value0, PairSemantics.value8, PairSemantics.value10, PairSemantics.value11, PairSemantics.value155, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair154 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node154 node154Labels = Sparse.eval singlePairValue154 (familyPairVector B) := by
  have hp := single_label_three B hB node154
  have hl : node154Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node154 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node154 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node154 PairSemantics.raw7979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node154 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node154 (EqualityPatterns.family3.label 1) = PairSemantics.raw5151 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node154 PairSemantics.raw5151
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5151 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node154 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node154 (EqualityPatterns.family3.label 2) = PairSemantics.raw5214 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node154 PairSemantics.raw5214
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5214 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node154 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node154 (EqualityPatterns.family3.label 3) = PairSemantics.raw211 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node154 PairSemantics.raw211
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical211 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node154 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value32 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node154 (EqualityPatterns.family3.label 4) = PairSemantics.raw172 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node154 PairSemantics.raw172
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical172 hH).trans (PairSemantics.sound32 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue154, PairSemantics.value0, PairSemantics.value4, PairSemantics.value8, PairSemantics.value10, PairSemantics.value32, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton650 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node650 node650Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node35 node35Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw12 singletonSmall650
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall650) = raw12Labels := by decide +kernel
  rw [hl, canonical12 B hB] at h
  have hc0 : mixedMoment B raw12 (Fin.cases (0 : Fin 1) singletonSmall650) =
      mixedMoment B node35 node35Labels := by
    have ha : raw12 = raw13 := by apply Matrix.ext; unfold raw12 raw13; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall650 = raw13Labels := by decide +kernel
    rw [ha, hj, canonical13 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1173 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1173 node1173Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node70 node70Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw38 singletonSmall1173
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1173) = raw38Labels := by decide +kernel
  rw [hl, canonical38 B hB] at h
  have hc0 : mixedMoment B raw38 (Fin.cases (0 : Fin 1) singletonSmall1173) =
      mixedMoment B node70 node70Labels := by
    have ha : raw38 = raw39 := by apply Matrix.ext; unfold raw38 raw39; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1173 = raw39Labels := by decide +kernel
    rw [ha, hj, canonical39 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1271 node1271Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node143 node143Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw60 singletonSmall1271
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1271) = raw60Labels := by decide +kernel
  rw [hl, canonical60 B hB] at h
  have hc0 : mixedMoment B raw60 (Fin.cases (0 : Fin 1) singletonSmall1271) =
      mixedMoment B node143 node143Labels := by
    have ha : raw60 = raw61 := by apply Matrix.ext; unfold raw60 raw61; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1271 = raw61Labels := by decide +kernel
    rw [ha, hj, canonical61 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1308 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1308 node1308Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node154 node154Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw88 singletonSmall1308
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1308) = raw88Labels := by decide +kernel
  rw [hl, canonical88 B hB] at h
  have hc0 : mixedMoment B raw88 (Fin.cases (0 : Fin 1) singletonSmall1308) =
      mixedMoment B node154 node154Labels := by
    have ha : raw88 = raw89 := by apply Matrix.ext; unfold raw88 raw89; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1308 = raw89Labels := by decide +kernel
    rw [ha, hj, canonical89 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1416 node1416Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node94 node94Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw136 singletonSmall1416
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1416) = raw136Labels := by decide +kernel
  rw [hl, canonical136 B hB] at h
  have hc0 : mixedMoment B raw136 (Fin.cases (0 : Fin 1) singletonSmall1416) =
      mixedMoment B node94 node94Labels := by
    have ha : raw136 = raw137 := by apply Matrix.ext; unfold raw136 raw137; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1416 = raw137Labels := by decide +kernel
    rw [ha, hj, canonical137 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound35 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node35 node35Labels = Sparse.eval nodeValue35 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue35 (familyPairVector B) := singlePair35 B _hB
    _ = _ := by norm_num [singlePairValue35, nodeValue35, Sparse.eval, mixedVector] <;> ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound70 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node70 node70Labels = Sparse.eval nodeValue70 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue70 (familyPairVector B) := singlePair70 B _hB
    _ = _ := by norm_num [singlePairValue70, nodeValue70, Sparse.eval, mixedVector] <;> ring

theorem sound94 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node94 node94Labels = Sparse.eval nodeValue94 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue94 (familyPairVector B) := singlePair94 B _hB
    _ = _ := by norm_num [singlePairValue94, nodeValue94, Sparse.eval, mixedVector] <;> ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node650 node650Labels = Sparse.eval nodeValue650 (mixedVector B) := by
  have h := singleton650 B _hB
  rw [sound35 B _hB _hF] at h
  norm_num [nodeValue650, nodeValue35, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1118 node1118Labels = Sparse.eval nodeValue1118 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1118) = mixedMoment B node1118 node1118Labels := rfl
  simpa [nodeValue1118, Sparse.eval] using hc.symm

theorem sound1142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1142 node1142Labels = Sparse.eval nodeValue1142 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1142) = mixedMoment B node1142 node1142Labels := rfl
  simpa [nodeValue1142, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node143 node143Labels = Sparse.eval nodeValue143 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue143 (familyPairVector B) := singlePair143 B _hB
    _ = _ := by
      norm_num [singlePairValue143, nodeValue143, Sparse.eval, mixedVector]
      ring

theorem sound154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node154 node154Labels = Sparse.eval nodeValue154 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue154 (familyPairVector B) := singlePair154 B _hB
    _ = _ := by
      norm_num [singlePairValue154, nodeValue154, Sparse.eval, mixedVector]
      ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1173 node1173Labels = Sparse.eval nodeValue1173 (mixedVector B) := by
  have h := singleton1173 B _hB
  rw [sound70 B _hB _hF] at h
  norm_num [nodeValue1173, nodeValue70, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1271 node1271Labels = Sparse.eval nodeValue1271 (mixedVector B) := by
  have h := singleton1271 B _hB
  rw [sound143 B _hB _hF] at h
  norm_num [nodeValue1271, nodeValue143, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1308 node1308Labels = Sparse.eval nodeValue1308 (mixedVector B) := by
  have h := singleton1308 B _hB
  rw [sound154 B _hB _hF] at h
  norm_num [nodeValue1308, nodeValue154, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1450 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1450 node1450Labels = 0 := by
  exact mixedMoment_order_one B hB node1450 node1450Labels 2
    (by decide +kernel) (by decide +kernel)

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

theorem sound1416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1416 node1416Labels = Sparse.eval nodeValue1416 (mixedVector B) := by
  have h := singleton1416 B _hB
  rw [sound94 B _hB _hF] at h
  norm_num [nodeValue1416, nodeValue94, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1450 node1450Labels = Sparse.eval nodeValue1450 (mixedVector B) := by
  simpa only [nodeValue1450, Sparse.eval_nil] using zero1450 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3114 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3114 node3114Labels = 0 := by
  exact mixedMoment_order_one B hB node3114 node3114Labels 2
    (by decide +kernel) (by decide +kernel)

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

theorem sound3114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3114 node3114Labels = Sparse.eval nodeValue3114 (mixedVector B) := by
  simpa only [nodeValue3114, Sparse.eval_nil] using zero3114 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node587 node587Labels = Sparse.eval nodeValue587 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 587) = mixedMoment B node587 node587Labels := rfl
  simpa [nodeValue587, Sparse.eval] using hc.symm

theorem sound591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node591 node591Labels = Sparse.eval nodeValue591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 591) = mixedMoment B node591 node591Labels := rfl
  simpa [nodeValue591, Sparse.eval] using hc.symm

theorem sound617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node617 node617Labels = Sparse.eval nodeValue617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 617) = mixedMoment B node617 node617Labels := rfl
  simpa [nodeValue617, Sparse.eval] using hc.symm

theorem sound633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node633 node633Labels = Sparse.eval nodeValue633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 633) = mixedMoment B node633 node633Labels := rfl
  simpa [nodeValue633, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources36
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1165 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1165 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1165 + difference 0 1) (sourceB1165 + difference 1 0) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1165 + difference 0 1) (sourceB1165 + difference 1 0) sourceC1165) = raw19640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19640; decide +kernel
    rw [ha]
    exact (canonical19640 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1165 + difference 0 2) (sourceB1165 + difference 2 0) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1165 + difference 0 2) (sourceB1165 + difference 2 0) sourceC1165) = raw19641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19641; decide +kernel
    rw [ha]
    exact (canonical19641 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1165 + difference 0 3) (sourceB1165 + difference 3 0) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1165 + difference 0 3) (sourceB1165 + difference 3 0) sourceC1165) = raw19642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19642; decide +kernel
    rw [ha]
    exact (canonical19642 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1165 + difference 0 4) (sourceB1165 + difference 4 0) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1450) := by
    have ha : (tripleCharges (sourceA1165 + difference 0 4) (sourceB1165 + difference 4 0) sourceC1165) = raw19643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19643; decide +kernel
    rw [ha]
    exact (canonical19643 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1165 + difference 0 5) (sourceB1165 + difference 5 0) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA1165 + difference 0 5) (sourceB1165 + difference 5 0) sourceC1165) = raw10289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw10289; decide +kernel
    rw [ha]
    exact (canonical10289 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1165 + difference 1 0) (sourceB1165 + difference 0 1) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 587) := by
    have ha : (tripleCharges (sourceA1165 + difference 1 0) (sourceB1165 + difference 0 1) sourceC1165) = raw19644 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19644; decide +kernel
    rw [ha]
    exact (canonical19644 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1165 + difference 1 2) (sourceB1165 + difference 2 1) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1165 + difference 1 2) (sourceB1165 + difference 2 1) sourceC1165) = raw19645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19645; decide +kernel
    rw [ha]
    exact (canonical19645 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1165 + difference 1 3) (sourceB1165 + difference 3 1) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1165 + difference 1 3) (sourceB1165 + difference 3 1) sourceC1165) = raw19646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19646; decide +kernel
    rw [ha]
    exact (canonical19646 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1165 + difference 1 4) (sourceB1165 + difference 4 1) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1173) := by
    have ha : (tripleCharges (sourceA1165 + difference 1 4) (sourceB1165 + difference 4 1) sourceC1165) = raw19647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19647; decide +kernel
    rw [ha]
    exact (canonical19647 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1165 + difference 1 5) (sourceB1165 + difference 5 1) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1165 + difference 1 5) (sourceB1165 + difference 5 1) sourceC1165) = raw19648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19648; decide +kernel
    rw [ha]
    exact (canonical19648 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1165 + difference 2 0) (sourceB1165 + difference 0 2) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 587) := by
    have ha : (tripleCharges (sourceA1165 + difference 2 0) (sourceB1165 + difference 0 2) sourceC1165) = raw19649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19649; decide +kernel
    rw [ha]
    exact (canonical19649 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1165 + difference 2 1) (sourceB1165 + difference 1 2) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1165 + difference 2 1) (sourceB1165 + difference 1 2) sourceC1165) = raw19650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19650; decide +kernel
    rw [ha]
    exact (canonical19650 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1165 + difference 2 3) (sourceB1165 + difference 3 2) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1165 + difference 2 3) (sourceB1165 + difference 3 2) sourceC1165) = raw19651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19651; decide +kernel
    rw [ha]
    exact (canonical19651 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1165 + difference 2 4) (sourceB1165 + difference 4 2) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1173) := by
    have ha : (tripleCharges (sourceA1165 + difference 2 4) (sourceB1165 + difference 4 2) sourceC1165) = raw19652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19652; decide +kernel
    rw [ha]
    exact (canonical19652 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1165 + difference 2 5) (sourceB1165 + difference 5 2) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1165 + difference 2 5) (sourceB1165 + difference 5 2) sourceC1165) = raw19653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19653; decide +kernel
    rw [ha]
    exact (canonical19653 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1165 + difference 3 0) (sourceB1165 + difference 0 3) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 587) := by
    have ha : (tripleCharges (sourceA1165 + difference 3 0) (sourceB1165 + difference 0 3) sourceC1165) = raw19654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19654; decide +kernel
    rw [ha]
    exact (canonical19654 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1165 + difference 3 1) (sourceB1165 + difference 1 3) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1165 + difference 3 1) (sourceB1165 + difference 1 3) sourceC1165) = raw19655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19655; decide +kernel
    rw [ha]
    exact (canonical19655 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1165 + difference 3 2) (sourceB1165 + difference 2 3) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1165 + difference 3 2) (sourceB1165 + difference 2 3) sourceC1165) = raw19656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19656; decide +kernel
    rw [ha]
    exact (canonical19656 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1165 + difference 3 4) (sourceB1165 + difference 4 3) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1173) := by
    have ha : (tripleCharges (sourceA1165 + difference 3 4) (sourceB1165 + difference 4 3) sourceC1165) = raw19657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19657; decide +kernel
    rw [ha]
    exact (canonical19657 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1165 + difference 3 5) (sourceB1165 + difference 5 3) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1165 + difference 3 5) (sourceB1165 + difference 5 3) sourceC1165) = raw19658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19658; decide +kernel
    rw [ha]
    exact (canonical19658 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1165 + difference 4 0) (sourceB1165 + difference 0 4) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 617) := by
    have ha : (tripleCharges (sourceA1165 + difference 4 0) (sourceB1165 + difference 0 4) sourceC1165) = raw19659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19659; decide +kernel
    rw [ha]
    exact (canonical19659 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1165 + difference 4 1) (sourceB1165 + difference 1 4) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1142) := by
    have ha : (tripleCharges (sourceA1165 + difference 4 1) (sourceB1165 + difference 1 4) sourceC1165) = raw19660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19660; decide +kernel
    rw [ha]
    exact (canonical19660 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1165 + difference 4 2) (sourceB1165 + difference 2 4) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1142) := by
    have ha : (tripleCharges (sourceA1165 + difference 4 2) (sourceB1165 + difference 2 4) sourceC1165) = raw19661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19661; decide +kernel
    rw [ha]
    exact (canonical19661 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1165 + difference 4 3) (sourceB1165 + difference 3 4) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1142) := by
    have ha : (tripleCharges (sourceA1165 + difference 4 3) (sourceB1165 + difference 3 4) sourceC1165) = raw19662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19662; decide +kernel
    rw [ha]
    exact (canonical19662 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1165 + difference 4 5) (sourceB1165 + difference 5 4) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1308) := by
    have ha : (tripleCharges (sourceA1165 + difference 4 5) (sourceB1165 + difference 5 4) sourceC1165) = raw10285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw10285; decide +kernel
    rw [ha]
    exact (canonical10285 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1165 + difference 5 0) (sourceB1165 + difference 0 5) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 591) := by
    have ha : (tripleCharges (sourceA1165 + difference 5 0) (sourceB1165 + difference 0 5) sourceC1165) = raw19663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19663; decide +kernel
    rw [ha]
    exact (canonical19663 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1165 + difference 5 1) (sourceB1165 + difference 1 5) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 633) := by
    have ha : (tripleCharges (sourceA1165 + difference 5 1) (sourceB1165 + difference 1 5) sourceC1165) = raw19664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19664; decide +kernel
    rw [ha]
    exact (canonical19664 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1165 + difference 5 2) (sourceB1165 + difference 2 5) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 633) := by
    have ha : (tripleCharges (sourceA1165 + difference 5 2) (sourceB1165 + difference 2 5) sourceC1165) = raw19665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19665; decide +kernel
    rw [ha]
    exact (canonical19665 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1165 + difference 5 3) (sourceB1165 + difference 3 5) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 633) := by
    have ha : (tripleCharges (sourceA1165 + difference 5 3) (sourceB1165 + difference 3 5) sourceC1165) = raw19666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19666; decide +kernel
    rw [ha]
    exact (canonical19666 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1165 + difference 5 4) (sourceB1165 + difference 4 5) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 650) := by
    have ha : (tripleCharges (sourceA1165 + difference 5 4) (sourceB1165 + difference 4 5) sourceC1165) = raw19667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19667; decide +kernel
    rw [ha]
    exact (canonical19667 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1165 sourceB1165 sourceC1165
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1165, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1013 : Integer.Sparse.reindex keyMap MixedData.row1013 = numericRow1013 := by decide +kernel

theorem numericCheck1013 (x : Master → ℝ) : Integer.Sparse.eval numericRow1013 x =
    (240 : ℝ) * reducedSource1013 x := by
  norm_num [numericRow1013, reducedSource1013, Integer.Sparse.eval, Sparse.eval, nodeValue587, nodeValue591, nodeValue617, nodeValue633, nodeValue650, nodeValue1118, nodeValue1142, nodeValue1173, nodeValue1271, nodeValue1308, nodeValue1416, nodeValue1450, nodeValue3114] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1013 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1013 (mixedVector B) = 0 := by
  have h587 : mixedVector B (Sum.inr 587) = Sparse.eval nodeValue587 (mixedVector B) := by
    change mixedMoment B node587 node587Labels = _
    exact sound587 B hB hF
  have h591 : mixedVector B (Sum.inr 591) = Sparse.eval nodeValue591 (mixedVector B) := by
    change mixedMoment B node591 node591Labels = _
    exact sound591 B hB hF
  have h617 : mixedVector B (Sum.inr 617) = Sparse.eval nodeValue617 (mixedVector B) := by
    change mixedMoment B node617 node617Labels = _
    exact sound617 B hB hF
  have h633 : mixedVector B (Sum.inr 633) = Sparse.eval nodeValue633 (mixedVector B) := by
    change mixedMoment B node633 node633Labels = _
    exact sound633 B hB hF
  have h650 : mixedVector B (Sum.inr 650) = Sparse.eval nodeValue650 (mixedVector B) := by
    change mixedMoment B node650 node650Labels = _
    exact sound650 B hB hF
  have h1118 : mixedVector B (Sum.inr 1118) = Sparse.eval nodeValue1118 (mixedVector B) := by
    change mixedMoment B node1118 node1118Labels = _
    exact sound1118 B hB hF
  have h1142 : mixedVector B (Sum.inr 1142) = Sparse.eval nodeValue1142 (mixedVector B) := by
    change mixedMoment B node1142 node1142Labels = _
    exact sound1142 B hB hF
  have h1173 : mixedVector B (Sum.inr 1173) = Sparse.eval nodeValue1173 (mixedVector B) := by
    change mixedMoment B node1173 node1173Labels = _
    exact sound1173 B hB hF
  have h1271 : mixedVector B (Sum.inr 1271) = Sparse.eval nodeValue1271 (mixedVector B) := by
    change mixedMoment B node1271 node1271Labels = _
    exact sound1271 B hB hF
  have h1308 : mixedVector B (Sum.inr 1308) = Sparse.eval nodeValue1308 (mixedVector B) := by
    change mixedMoment B node1308 node1308Labels = _
    exact sound1308 B hB hF
  have h1416 : mixedVector B (Sum.inr 1416) = Sparse.eval nodeValue1416 (mixedVector B) := by
    change mixedMoment B node1416 node1416Labels = _
    exact sound1416 B hB hF
  have h1450 : mixedVector B (Sum.inr 1450) = Sparse.eval nodeValue1450 (mixedVector B) := by
    change mixedMoment B node1450 node1450Labels = _
    exact sound1450 B hB hF
  have h3114 : mixedVector B (Sum.inr 3114) = Sparse.eval nodeValue3114 (mixedVector B) := by
    change mixedMoment B node3114 node3114Labels = _
    exact sound3114 B hB hF
  simpa only [sourceForm1165, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h587, h591, h617, h633, h650, h1118, h1142, h1173, h1271, h1308, h1416, h1450, h3114, reducedSource1013] using sourceEq1165 B hB

theorem rowSound1013_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1013 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1013, numericCheck1013, reducedZero1013 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e_oai
