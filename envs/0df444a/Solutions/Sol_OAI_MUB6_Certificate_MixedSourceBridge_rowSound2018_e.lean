-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:03:25.357989+00:00
-- url     : https://prove2.me/submissions/99d3e0fb-54b5-4058-949e-bebb7d959fd9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5172_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5485_e

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

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13578 raw13578Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw13578 raw13578Labels = mixedMoment B raw13578step0 raw13578step0Labels := by
      have ha : raw13578step0 = (fun i j => raw13578 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13578step0 raw13578; decide +kernel
      have hl : raw13578step0Labels = raw13578Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13578 raw13578Labels permutation170 permutation3
    mixedMoment B raw13578step0 raw13578step0Labels = mixedMoment B raw13578step1 raw13578step1Labels := by
      have ha : raw13578step1 = raw13578step0 := by apply Matrix.ext; unfold raw13578step1 raw13578step0; decide +kernel
      have hl : raw13578step0Labels = labelEmbedding6 ∘ raw13578step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13578step0 raw13578step0Labels raw13578step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

theorem canonical13580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13580 raw13580Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw13580 raw13580Labels = mixedMoment B raw13580step0 raw13580step0Labels := by
      have hz : ∀ j, raw13580 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13580step0 = (fun i j => raw13580 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13580step0 raw13580; decide +kernel
      have hl : raw13580step0Labels = raw13580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13580 raw13580Labels permutation520 hz
    mixedMoment B raw13580step0 raw13580step0Labels = mixedMoment B raw13580step1 raw13580step1Labels := by
      have ha : raw13580step1 = (fun i j => raw13580step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13580step1 raw13580step0; decide +kernel
      have hl : raw13580step1Labels = raw13580step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13580step0 raw13580step0Labels permutation36 permutation3
    mixedMoment B raw13580step1 raw13580step1Labels = mixedMoment B raw13580step2 raw13580step2Labels := by
      have ha : raw13580step2 = raw13580step1 := by apply Matrix.ext; unfold raw13580step2 raw13580step1; decide +kernel
      have hl : raw13580step1Labels = labelEmbedding6 ∘ raw13580step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13580step1 raw13580step1Labels raw13580step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical13581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13581 raw13581Labels = mixedMoment B node5227 node5227Labels := by
  calc
    mixedMoment B raw13581 raw13581Labels = mixedMoment B raw13581step0 raw13581step0Labels := by
      have ha : raw13581step0 = (fun i j => raw13581 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13581step0 raw13581; decide +kernel
      have hl : raw13581step0Labels = raw13581Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13581 raw13581Labels permutation246 permutation3
    mixedMoment B raw13581step0 raw13581step0Labels = mixedMoment B raw13581step1 raw13581step1Labels := by
      have ha : raw13581step1 = raw13581step0 := by apply Matrix.ext; unfold raw13581step1 raw13581step0; decide +kernel
      have hl : raw13581step0Labels = labelEmbedding6 ∘ raw13581step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13581step0 raw13581step0Labels raw13581step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5227 node5227Labels := by rfl

theorem canonical13583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13583 raw13583Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw13583 raw13583Labels = mixedMoment B raw13583step0 raw13583step0Labels := by
      have hz : ∀ j, raw13583 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13583step0 = (fun i j => raw13583 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13583step0 raw13583; decide +kernel
      have hl : raw13583step0Labels = raw13583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13583 raw13583Labels permutation346 hz
    mixedMoment B raw13583step0 raw13583step0Labels = mixedMoment B raw13583step1 raw13583step1Labels := by
      have ha : raw13583step1 = (fun i j => raw13583step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13583step1 raw13583step0; decide +kernel
      have hl : raw13583step1Labels = raw13583step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13583step0 raw13583step0Labels permutation37 permutation3
    mixedMoment B raw13583step1 raw13583step1Labels = mixedMoment B raw13583step2 raw13583step2Labels := by
      have ha : raw13583step2 = raw13583step1 := by apply Matrix.ext; unfold raw13583step2 raw13583step1; decide +kernel
      have hl : raw13583step1Labels = labelEmbedding6 ∘ raw13583step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13583step1 raw13583step1Labels raw13583step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

theorem canonical13588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13588 raw13588Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw13588 raw13588Labels = mixedMoment B raw13588step0 raw13588step0Labels := by
      have hz : ∀ j, raw13588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13588step0 = (fun i j => raw13588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13588step0 raw13588; decide +kernel
      have hl : raw13588step0Labels = raw13588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13588 raw13588Labels permutation346 hz
    mixedMoment B raw13588step0 raw13588step0Labels = mixedMoment B raw13588step1 raw13588step1Labels := by
      have ha : raw13588step1 = (fun i j => raw13588step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13588step1 raw13588step0; decide +kernel
      have hl : raw13588step1Labels = raw13588step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13588step0 raw13588step0Labels permutation36 permutation3
    mixedMoment B raw13588step1 raw13588step1Labels = mixedMoment B raw13588step2 raw13588step2Labels := by
      have ha : raw13588step2 = raw13588step1 := by apply Matrix.ext; unfold raw13588step2 raw13588step1; decide +kernel
      have hl : raw13588step1Labels = labelEmbedding6 ∘ raw13588step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13588step1 raw13588step1Labels raw13588step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

theorem canonical13592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13592 raw13592Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw13592 raw13592Labels = mixedMoment B raw13592step0 raw13592step0Labels := by
      have hz : ∀ j, raw13592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13592step0 = (fun i j => raw13592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13592step0 raw13592; decide +kernel
      have hl : raw13592step0Labels = raw13592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13592 raw13592Labels permutation346 hz
    mixedMoment B raw13592step0 raw13592step0Labels = mixedMoment B raw13592step1 raw13592step1Labels := by
      have ha : raw13592step1 = (fun i j => raw13592step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13592step1 raw13592step0; decide +kernel
      have hl : raw13592step1Labels = raw13592step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13592step0 raw13592step0Labels permutation32 permutation3
    mixedMoment B raw13592step1 raw13592step1Labels = mixedMoment B raw13592step2 raw13592step2Labels := by
      have ha : raw13592step2 = raw13592step1 := by apply Matrix.ext; unfold raw13592step2 raw13592step1; decide +kernel
      have hl : raw13592step1Labels = labelEmbedding6 ∘ raw13592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13592step1 raw13592step1Labels raw13592step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17687 raw17687Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw17687 raw17687Labels = mixedMoment B raw17687step0 raw17687step0Labels := by
      have hz : ∀ j, raw17687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17687step0 = (fun i j => raw17687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17687step0 raw17687; decide +kernel
      have hl : raw17687step0Labels = raw17687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17687 raw17687Labels permutation434 hz
    mixedMoment B raw17687step0 raw17687step0Labels = mixedMoment B raw17687step1 raw17687step1Labels := by
      have ha : raw17687step1 = (fun i j => raw17687step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17687step1 raw17687step0; decide +kernel
      have hl : raw17687step1Labels = raw17687step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17687step0 raw17687step0Labels permutation32 permutation3
    mixedMoment B raw17687step1 raw17687step1Labels = mixedMoment B raw17687step2 raw17687step2Labels := by
      have ha : raw17687step2 = raw17687step1 := by apply Matrix.ext; unfold raw17687step2 raw17687step1; decide +kernel
      have hl : raw17687step1Labels = labelEmbedding6 ∘ raw17687step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17687step1 raw17687step1Labels raw17687step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

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

theorem canonical1914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1914 raw1914Labels = mixedMoment B node4947 node4947Labels := by
  calc
    mixedMoment B raw1914 raw1914Labels = mixedMoment B raw1914step0 raw1914step0Labels := by
      have ha : raw1914step0 = (fun i j => raw1914 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1914step0 raw1914; decide +kernel
      have hl : raw1914step0Labels = raw1914Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1914 raw1914Labels permutation152 permutation4
    mixedMoment B raw1914step0 raw1914step0Labels = mixedMoment B raw1914step1 raw1914step1Labels := by
      have ha : raw1914step1 = raw1914step0 := by apply Matrix.ext; unfold raw1914step1 raw1914step0; decide +kernel
      have hl : raw1914step0Labels = labelEmbedding7 ∘ raw1914step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1914step0 raw1914step0Labels raw1914step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4947 node4947Labels := by rfl

theorem canonical1915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1915 raw1915Labels = mixedMoment B node2338 node2338Labels := by
  calc
    mixedMoment B raw1915 raw1915Labels = mixedMoment B raw1915step0 raw1915step0Labels := by
      have ha : raw1915step0 = (fun i j => raw1915 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1915step0 raw1915; decide +kernel
      have hl : raw1915step0Labels = raw1915Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1915 raw1915Labels permutation152 permutation4
    _ = mixedMoment B node2338 node2338Labels := by rfl

theorem canonical1916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1916 raw1916Labels = mixedMoment B node3416 node3416Labels := by
  calc
    mixedMoment B raw1916 raw1916Labels = mixedMoment B raw1916step0 raw1916step0Labels := by
      have ha : raw1916step0 = (fun i j => raw1916 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1916step0 raw1916; decide +kernel
      have hl : raw1916step0Labels = raw1916Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1916 raw1916Labels permutation170 permutation6
    mixedMoment B raw1916step0 raw1916step0Labels = mixedMoment B raw1916step1 raw1916step1Labels := by
      have ha : raw1916step1 = -raw1916step0 := by apply Matrix.ext; change ∀ i j, raw1916step1 i j = -(raw1916step0 i j); unfold raw1916step1 raw1916step0; decide +kernel
      have hl : raw1916step1Labels = raw1916step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1916step1 raw1916step1Labels = mixedMoment B raw1916step2 raw1916step2Labels := by
      have ha : raw1916step2 = raw1916step1 := by apply Matrix.ext; unfold raw1916step2 raw1916step1; decide +kernel
      have hl : raw1916step1Labels = labelEmbedding1 ∘ raw1916step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1916step1 raw1916step1Labels raw1916step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3416 node3416Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical145
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18654 raw18654Labels = mixedMoment B node5462 node5462Labels := by
  calc
    mixedMoment B raw18654 raw18654Labels = mixedMoment B raw18654step0 raw18654step0Labels := by
      have ha : raw18654step0 = (fun i j => raw18654 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18654step0 raw18654; decide +kernel
      have hl : raw18654step0Labels = raw18654Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18654 raw18654Labels permutation170 permutation3
    mixedMoment B raw18654step0 raw18654step0Labels = mixedMoment B raw18654step1 raw18654step1Labels := by
      have ha : raw18654step1 = raw18654step0 := by apply Matrix.ext; unfold raw18654step1 raw18654step0; decide +kernel
      have hl : raw18654step0Labels = labelEmbedding6 ∘ raw18654step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18654step0 raw18654step0Labels raw18654step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5462 node5462Labels := by rfl

theorem canonical18655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18655 raw18655Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18655 raw18655Labels = mixedMoment B raw18655step0 raw18655step0Labels := by
      have hz : ∀ j, raw18655 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18655step0 = (fun i j => raw18655 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18655step0 raw18655; decide +kernel
      have hl : raw18655step0Labels = raw18655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18655 raw18655Labels permutation520 hz
    _ = mixedMoment B node5485 node5485Labels := by rfl

theorem canonical18656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18656 raw18656Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw18656 raw18656Labels = mixedMoment B raw18656step0 raw18656step0Labels := by
      have ha : raw18656step0 = (fun i j => raw18656 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18656step0 raw18656; decide +kernel
      have hl : raw18656step0Labels = raw18656Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18656 raw18656Labels permutation590 permutation4
    mixedMoment B raw18656step0 raw18656step0Labels = mixedMoment B raw18656step1 raw18656step1Labels := by
      have ha : raw18656step1 = -raw18656step0 := by apply Matrix.ext; change ∀ i j, raw18656step1 i j = -(raw18656step0 i j); unfold raw18656step1 raw18656step0; decide +kernel
      have hl : raw18656step1Labels = raw18656step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18656step1 raw18656step1Labels = mixedMoment B raw18656step2 raw18656step2Labels := by
      have ha : raw18656step2 = raw18656step1 := by apply Matrix.ext; unfold raw18656step2 raw18656step1; decide +kernel
      have hl : raw18656step1Labels = labelEmbedding7 ∘ raw18656step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18656step1 raw18656step1Labels raw18656step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

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

theorem canonical2154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2154 raw2154Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw2154 raw2154Labels = mixedMoment B raw2154step0 raw2154step0Labels := by
      have ha : raw2154step0 = (fun i j => raw2154 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2154step0 raw2154; decide +kernel
      have hl : raw2154step0Labels = raw2154Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2154 raw2154Labels permutation152 permutation4
    mixedMoment B raw2154step0 raw2154step0Labels = mixedMoment B raw2154step1 raw2154step1Labels := by
      have ha : raw2154step1 = raw2154step0 := by apply Matrix.ext; unfold raw2154step1 raw2154step0; decide +kernel
      have hl : raw2154step0Labels = labelEmbedding7 ∘ raw2154step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2154step0 raw2154step0Labels raw2154step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

theorem canonical2155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2155 raw2155Labels = mixedMoment B node2536 node2536Labels := by
  calc
    mixedMoment B raw2155 raw2155Labels = mixedMoment B raw2155step0 raw2155step0Labels := by
      have ha : raw2155step0 = (fun i j => raw2155 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2155step0 raw2155; decide +kernel
      have hl : raw2155step0Labels = raw2155Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2155 raw2155Labels permutation152 permutation4
    _ = mixedMoment B node2536 node2536Labels := by rfl

theorem canonical2156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2156 raw2156Labels = mixedMoment B node3370 node3370Labels := by
  calc
    mixedMoment B raw2156 raw2156Labels = mixedMoment B raw2156step0 raw2156step0Labels := by
      have ha : raw2156step0 = (fun i j => raw2156 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2156step0 raw2156; decide +kernel
      have hl : raw2156step0Labels = raw2156Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2156 raw2156Labels permutation176 permutation6
    mixedMoment B raw2156step0 raw2156step0Labels = mixedMoment B raw2156step1 raw2156step1Labels := by
      have ha : raw2156step1 = -raw2156step0 := by apply Matrix.ext; change ∀ i j, raw2156step1 i j = -(raw2156step0 i j); unfold raw2156step1 raw2156step0; decide +kernel
      have hl : raw2156step1Labels = raw2156step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2156step1 raw2156step1Labels = mixedMoment B raw2156step2 raw2156step2Labels := by
      have ha : raw2156step2 = raw2156step1 := by apply Matrix.ext; unfold raw2156step2 raw2156step1; decide +kernel
      have hl : raw2156step1Labels = labelEmbedding1 ∘ raw2156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2156step1 raw2156step1Labels raw2156step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3370 node3370Labels := by rfl

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

theorem canonical2190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2190 raw2190Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw2190 raw2190Labels = mixedMoment B raw2190step0 raw2190step0Labels := by
      have ha : raw2190step0 = (fun i j => raw2190 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2190step0 raw2190; decide +kernel
      have hl : raw2190step0Labels = raw2190Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2190 raw2190Labels permutation32 permutation4
    mixedMoment B raw2190step0 raw2190step0Labels = mixedMoment B raw2190step1 raw2190step1Labels := by
      have ha : raw2190step1 = raw2190step0 := by apply Matrix.ext; unfold raw2190step1 raw2190step0; decide +kernel
      have hl : raw2190step0Labels = labelEmbedding7 ∘ raw2190step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2190step0 raw2190step0Labels raw2190step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

theorem canonical2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2191 raw2191Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw2191 raw2191Labels = mixedMoment B raw2191step0 raw2191step0Labels := by
      have ha : raw2191step0 = (fun i j => raw2191 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2191step0 raw2191; decide +kernel
      have hl : raw2191step0Labels = raw2191Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2191 raw2191Labels permutation32 permutation4
    _ = mixedMoment B node2590 node2590Labels := by rfl

theorem canonical2192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2192 raw2192Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw2192 raw2192Labels = mixedMoment B raw2192step0 raw2192step0Labels := by
      have ha : raw2192step0 = (fun i j => raw2192 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2192step0 raw2192; decide +kernel
      have hl : raw2192step0Labels = raw2192Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2192 raw2192Labels permutation38 permutation6
    mixedMoment B raw2192step0 raw2192step0Labels = mixedMoment B raw2192step1 raw2192step1Labels := by
      have ha : raw2192step1 = -raw2192step0 := by apply Matrix.ext; change ∀ i j, raw2192step1 i j = -(raw2192step0 i j); unfold raw2192step1 raw2192step0; decide +kernel
      have hl : raw2192step1Labels = raw2192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2192step1 raw2192step1Labels = mixedMoment B raw2192step2 raw2192step2Labels := by
      have ha : raw2192step2 = raw2192step1 := by apply Matrix.ext; unfold raw2192step2 raw2192step1; decide +kernel
      have hl : raw2192step1Labels = labelEmbedding1 ∘ raw2192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2192step1 raw2192step1Labels raw2192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

theorem canonical2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2247 raw2247Labels = mixedMoment B node5227 node5227Labels := by
  calc
    mixedMoment B raw2247 raw2247Labels = mixedMoment B raw2247step0 raw2247step0Labels := by
      have ha : raw2247step0 = (fun i j => raw2247 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2247step0 raw2247; decide +kernel
      have hl : raw2247step0Labels = raw2247Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2247 raw2247Labels permutation152 permutation4
    mixedMoment B raw2247step0 raw2247step0Labels = mixedMoment B raw2247step1 raw2247step1Labels := by
      have ha : raw2247step1 = raw2247step0 := by apply Matrix.ext; unfold raw2247step1 raw2247step0; decide +kernel
      have hl : raw2247step0Labels = labelEmbedding7 ∘ raw2247step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2247step0 raw2247step0Labels raw2247step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5227 node5227Labels := by rfl

theorem canonical2248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2248 raw2248Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw2248 raw2248Labels = mixedMoment B raw2248step0 raw2248step0Labels := by
      have ha : raw2248step0 = (fun i j => raw2248 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2248step0 raw2248; decide +kernel
      have hl : raw2248step0Labels = raw2248Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2248 raw2248Labels permutation152 permutation4
    _ = mixedMoment B node2671 node2671Labels := by rfl

theorem canonical2249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2249 raw2249Labels = mixedMoment B node3390 node3390Labels := by
  calc
    mixedMoment B raw2249 raw2249Labels = mixedMoment B raw2249step0 raw2249step0Labels := by
      have ha : raw2249step0 = (fun i j => raw2249 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2249step0 raw2249; decide +kernel
      have hl : raw2249step0Labels = raw2249Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2249 raw2249Labels permutation152 permutation6
    mixedMoment B raw2249step0 raw2249step0Labels = mixedMoment B raw2249step1 raw2249step1Labels := by
      have ha : raw2249step1 = -raw2249step0 := by apply Matrix.ext; change ∀ i j, raw2249step1 i j = -(raw2249step0 i j); unfold raw2249step1 raw2249step0; decide +kernel
      have hl : raw2249step1Labels = raw2249step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2249step1 raw2249step1Labels = mixedMoment B raw2249step2 raw2249step2Labels := by
      have ha : raw2249step2 = raw2249step1 := by apply Matrix.ext; unfold raw2249step2 raw2249step1; decide +kernel
      have hl : raw2249step1Labels = labelEmbedding1 ∘ raw2249step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2249step1 raw2249step1Labels raw2249step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3390 node3390Labels := by rfl

theorem canonical2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2292 raw2292Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw2292 raw2292Labels = mixedMoment B raw2292step0 raw2292step0Labels := by
      have ha : raw2292step0 = (fun i j => raw2292 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2292step0 raw2292; decide +kernel
      have hl : raw2292step0Labels = raw2292Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2292 raw2292Labels permutation32 permutation4
    mixedMoment B raw2292step0 raw2292step0Labels = mixedMoment B raw2292step1 raw2292step1Labels := by
      have ha : raw2292step1 = raw2292step0 := by apply Matrix.ext; unfold raw2292step1 raw2292step0; decide +kernel
      have hl : raw2292step0Labels = labelEmbedding7 ∘ raw2292step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2292step0 raw2292step0Labels raw2292step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2293 raw2293Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw2293 raw2293Labels = mixedMoment B raw2293step0 raw2293step0Labels := by
      have ha : raw2293step0 = (fun i j => raw2293 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2293step0 raw2293; decide +kernel
      have hl : raw2293step0Labels = raw2293Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2293 raw2293Labels permutation32 permutation4
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2294 raw2294Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw2294 raw2294Labels = mixedMoment B raw2294step0 raw2294step0Labels := by
      have ha : raw2294step0 = (fun i j => raw2294 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2294step0 raw2294; decide +kernel
      have hl : raw2294step0Labels = raw2294Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2294 raw2294Labels permutation38 permutation6
    mixedMoment B raw2294step0 raw2294step0Labels = mixedMoment B raw2294step1 raw2294step1Labels := by
      have ha : raw2294step1 = -raw2294step0 := by apply Matrix.ext; change ∀ i j, raw2294step1 i j = -(raw2294step0 i j); unfold raw2294step1 raw2294step0; decide +kernel
      have hl : raw2294step1Labels = raw2294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2294step1 raw2294step1Labels = mixedMoment B raw2294step2 raw2294step2Labels := by
      have ha : raw2294step2 = raw2294step1 := by apply Matrix.ext; unfold raw2294step2 raw2294step1; decide +kernel
      have hl : raw2294step1Labels = labelEmbedding1 ∘ raw2294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2294step1 raw2294step1Labels raw2294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical195
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25071 raw25071Labels = mixedMoment B node4351 node4351Labels := by
  calc
    mixedMoment B raw25071 raw25071Labels = mixedMoment B raw25071step0 raw25071step0Labels := by
      have ha : raw25071step0 = (fun i j => raw25071 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25071step0 raw25071; decide +kernel
      have hl : raw25071step0Labels = raw25071Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25071 raw25071Labels permutation152 permutation3
    mixedMoment B raw25071step0 raw25071step0Labels = mixedMoment B raw25071step1 raw25071step1Labels := by
      have ha : raw25071step1 = raw25071step0 := by apply Matrix.ext; unfold raw25071step1 raw25071step0; decide +kernel
      have hl : raw25071step0Labels = labelEmbedding6 ∘ raw25071step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25071step0 raw25071step0Labels raw25071step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4351 node4351Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3039 raw3039Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw3039 raw3039Labels = mixedMoment B raw3039step0 raw3039step0Labels := by
      have hz : ∀ j, raw3039 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3039step0 = (fun i j => raw3039 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3039step0 raw3039; decide +kernel
      have hl : raw3039step0Labels = raw3039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3039 raw3039Labels permutation434 hz
    mixedMoment B raw3039step0 raw3039step0Labels = mixedMoment B raw3039step1 raw3039step1Labels := by
      have ha : raw3039step1 = (fun i j => raw3039step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3039step1 raw3039step0; decide +kernel
      have hl : raw3039step1Labels = raw3039step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3039step0 raw3039step0Labels permutation36 permutation3
    mixedMoment B raw3039step1 raw3039step1Labels = mixedMoment B raw3039step2 raw3039step2Labels := by
      have ha : raw3039step2 = raw3039step1 := by apply Matrix.ext; unfold raw3039step2 raw3039step1; decide +kernel
      have hl : raw3039step1Labels = labelEmbedding6 ∘ raw3039step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3039step1 raw3039step1Labels raw3039step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical3040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3040 raw3040Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw3040 raw3040Labels = mixedMoment B raw3040step0 raw3040step0Labels := by
      have hz : ∀ j, raw3040 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3040step0 = (fun i j => raw3040 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3040step0 raw3040; decide +kernel
      have hl : raw3040step0Labels = raw3040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3040 raw3040Labels permutation434 hz
    _ = mixedMoment B node5485 node5485Labels := by rfl

theorem canonical3044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3044 raw3044Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw3044 raw3044Labels = mixedMoment B raw3044step0 raw3044step0Labels := by
      have hz : ∀ j, raw3044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3044step0 = (fun i j => raw3044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3044step0 raw3044; decide +kernel
      have hl : raw3044step0Labels = raw3044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3044 raw3044Labels permutation346 hz
    mixedMoment B raw3044step0 raw3044step0Labels = mixedMoment B raw3044step1 raw3044step1Labels := by
      have ha : raw3044step1 = (fun i j => raw3044step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3044step1 raw3044step0; decide +kernel
      have hl : raw3044step1Labels = raw3044step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3044step0 raw3044step0Labels permutation36 permutation3
    mixedMoment B raw3044step1 raw3044step1Labels = mixedMoment B raw3044step2 raw3044step2Labels := by
      have ha : raw3044step2 = raw3044step1 := by apply Matrix.ext; unfold raw3044step2 raw3044step1; decide +kernel
      have hl : raw3044step1Labels = labelEmbedding6 ∘ raw3044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3044step1 raw3044step1Labels raw3044step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical3045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3045 raw3045Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw3045 raw3045Labels = mixedMoment B raw3045step0 raw3045step0Labels := by
      have hz : ∀ j, raw3045 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3045step0 = (fun i j => raw3045 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3045step0 raw3045; decide +kernel
      have hl : raw3045step0Labels = raw3045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3045 raw3045Labels permutation346 hz
    _ = mixedMoment B node5485 node5485Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical251
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32201 raw32201Labels = mixedMoment B node4947 node4947Labels := by
  calc
    mixedMoment B raw32201 raw32201Labels = mixedMoment B raw32201step0 raw32201step0Labels := by
      have ha : raw32201step0 = (fun i j => raw32201 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32201step0 raw32201; decide +kernel
      have hl : raw32201step0Labels = raw32201Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32201 raw32201Labels permutation152 permutation3
    mixedMoment B raw32201step0 raw32201step0Labels = mixedMoment B raw32201step1 raw32201step1Labels := by
      have ha : raw32201step1 = raw32201step0 := by apply Matrix.ext; unfold raw32201step1 raw32201step0; decide +kernel
      have hl : raw32201step0Labels = labelEmbedding6 ∘ raw32201step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32201step0 raw32201step0Labels raw32201step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4947 node4947Labels := by rfl

theorem canonical32202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32202 raw32202Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw32202 raw32202Labels = mixedMoment B raw32202step0 raw32202step0Labels := by
      have hz : ∀ j, raw32202 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32202step0 = (fun i j => raw32202 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32202step0 raw32202; decide +kernel
      have hl : raw32202step0Labels = raw32202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32202 raw32202Labels permutation520 hz
    mixedMoment B raw32202step0 raw32202step0Labels = mixedMoment B raw32202step1 raw32202step1Labels := by
      have ha : raw32202step1 = (fun i j => raw32202step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32202step1 raw32202step0; decide +kernel
      have hl : raw32202step1Labels = raw32202step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32202step0 raw32202step0Labels permutation32 permutation3
    mixedMoment B raw32202step1 raw32202step1Labels = mixedMoment B raw32202step2 raw32202step2Labels := by
      have ha : raw32202step2 = raw32202step1 := by apply Matrix.ext; unfold raw32202step2 raw32202step1; decide +kernel
      have hl : raw32202step1Labels = labelEmbedding6 ∘ raw32202step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32202step1 raw32202step1Labels raw32202step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

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

theorem canonical34518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34518 raw34518Labels = mixedMoment B node4337 node4337Labels := by
  calc
    mixedMoment B raw34518 raw34518Labels = mixedMoment B raw34518step0 raw34518step0Labels := by
      have ha : raw34518step0 = (fun i j => raw34518 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34518step0 raw34518; decide +kernel
      have hl : raw34518step0Labels = raw34518Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34518 raw34518Labels permutation173 permutation3
    mixedMoment B raw34518step0 raw34518step0Labels = mixedMoment B raw34518step1 raw34518step1Labels := by
      have ha : raw34518step1 = raw34518step0 := by apply Matrix.ext; unfold raw34518step1 raw34518step0; decide +kernel
      have hl : raw34518step0Labels = labelEmbedding6 ∘ raw34518step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34518step0 raw34518step0Labels raw34518step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4337 node4337Labels := by rfl

theorem canonical34519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34519 raw34519Labels = mixedMoment B node4936 node4936Labels := by
  calc
    mixedMoment B raw34519 raw34519Labels = mixedMoment B raw34519step0 raw34519step0Labels := by
      have ha : raw34519step0 = (fun i j => raw34519 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34519step0 raw34519; decide +kernel
      have hl : raw34519step0Labels = raw34519Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34519 raw34519Labels permutation173 permutation3
    mixedMoment B raw34519step0 raw34519step0Labels = mixedMoment B raw34519step1 raw34519step1Labels := by
      have ha : raw34519step1 = raw34519step0 := by apply Matrix.ext; unfold raw34519step1 raw34519step0; decide +kernel
      have hl : raw34519step0Labels = labelEmbedding6 ∘ raw34519step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34519step0 raw34519step0Labels raw34519step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4936 node4936Labels := by rfl

theorem canonical34520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34520 raw34520Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw34520 raw34520Labels = mixedMoment B raw34520step0 raw34520step0Labels := by
      have hz : ∀ j, raw34520 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34520step0 = (fun i j => raw34520 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34520step0 raw34520; decide +kernel
      have hl : raw34520step0Labels = raw34520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34520 raw34520Labels permutation434 hz
    mixedMoment B raw34520step0 raw34520step0Labels = mixedMoment B raw34520step1 raw34520step1Labels := by
      have ha : raw34520step1 = (fun i j => raw34520step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34520step1 raw34520step0; decide +kernel
      have hl : raw34520step1Labels = raw34520step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34520step0 raw34520step0Labels permutation37 permutation3
    mixedMoment B raw34520step1 raw34520step1Labels = mixedMoment B raw34520step2 raw34520step2Labels := by
      have ha : raw34520step2 = raw34520step1 := by apply Matrix.ext; unfold raw34520step2 raw34520step1; decide +kernel
      have hl : raw34520step1Labels = labelEmbedding6 ∘ raw34520step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34520step1 raw34520step1Labels raw34520step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

theorem canonical34521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34521 raw34521Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw34521 raw34521Labels = mixedMoment B raw34521step0 raw34521step0Labels := by
      have hz : ∀ j, raw34521 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34521step0 = (fun i j => raw34521 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34521step0 raw34521; decide +kernel
      have hl : raw34521step0Labels = raw34521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34521 raw34521Labels permutation520 hz
    mixedMoment B raw34521step0 raw34521step0Labels = mixedMoment B raw34521step1 raw34521step1Labels := by
      have ha : raw34521step1 = (fun i j => raw34521step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34521step1 raw34521step0; decide +kernel
      have hl : raw34521step1Labels = raw34521step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34521step0 raw34521step0Labels permutation37 permutation3
    mixedMoment B raw34521step1 raw34521step1Labels = mixedMoment B raw34521step2 raw34521step2Labels := by
      have ha : raw34521step2 = raw34521step1 := by apply Matrix.ext; unfold raw34521step2 raw34521step1; decide +kernel
      have hl : raw34521step1Labels = labelEmbedding6 ∘ raw34521step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34521step1 raw34521step1Labels raw34521step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

theorem canonical34522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34522 raw34522Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw34522 raw34522Labels = mixedMoment B raw34522step0 raw34522step0Labels := by
      have ha : raw34522step0 = (fun i j => raw34522 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34522step0 raw34522; decide +kernel
      have hl : raw34522step0Labels = raw34522Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34522 raw34522Labels permutation173 permutation3
    mixedMoment B raw34522step0 raw34522step0Labels = mixedMoment B raw34522step1 raw34522step1Labels := by
      have ha : raw34522step1 = raw34522step0 := by apply Matrix.ext; unfold raw34522step1 raw34522step0; decide +kernel
      have hl : raw34522step0Labels = labelEmbedding6 ∘ raw34522step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34522step0 raw34522step0Labels raw34522step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

theorem canonical34523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34523 raw34523Labels = mixedMoment B node4337 node4337Labels := by
  calc
    mixedMoment B raw34523 raw34523Labels = mixedMoment B raw34523step0 raw34523step0Labels := by
      have ha : raw34523step0 = (fun i j => raw34523 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34523step0 raw34523; decide +kernel
      have hl : raw34523step0Labels = raw34523Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34523 raw34523Labels permutation171 permutation3
    mixedMoment B raw34523step0 raw34523step0Labels = mixedMoment B raw34523step1 raw34523step1Labels := by
      have ha : raw34523step1 = raw34523step0 := by apply Matrix.ext; unfold raw34523step1 raw34523step0; decide +kernel
      have hl : raw34523step0Labels = labelEmbedding6 ∘ raw34523step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34523step0 raw34523step0Labels raw34523step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4337 node4337Labels := by rfl

theorem canonical34524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34524 raw34524Labels = mixedMoment B node4936 node4936Labels := by
  calc
    mixedMoment B raw34524 raw34524Labels = mixedMoment B raw34524step0 raw34524step0Labels := by
      have ha : raw34524step0 = (fun i j => raw34524 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34524step0 raw34524; decide +kernel
      have hl : raw34524step0Labels = raw34524Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34524 raw34524Labels permutation171 permutation3
    mixedMoment B raw34524step0 raw34524step0Labels = mixedMoment B raw34524step1 raw34524step1Labels := by
      have ha : raw34524step1 = raw34524step0 := by apply Matrix.ext; unfold raw34524step1 raw34524step0; decide +kernel
      have hl : raw34524step0Labels = labelEmbedding6 ∘ raw34524step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34524step0 raw34524step0Labels raw34524step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4936 node4936Labels := by rfl

theorem canonical34525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34525 raw34525Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw34525 raw34525Labels = mixedMoment B raw34525step0 raw34525step0Labels := by
      have hz : ∀ j, raw34525 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34525step0 = (fun i j => raw34525 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34525step0 raw34525; decide +kernel
      have hl : raw34525step0Labels = raw34525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34525 raw34525Labels permutation520 hz
    mixedMoment B raw34525step0 raw34525step0Labels = mixedMoment B raw34525step1 raw34525step1Labels := by
      have ha : raw34525step1 = (fun i j => raw34525step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34525step1 raw34525step0; decide +kernel
      have hl : raw34525step1Labels = raw34525step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34525step0 raw34525step0Labels permutation36 permutation3
    mixedMoment B raw34525step1 raw34525step1Labels = mixedMoment B raw34525step2 raw34525step2Labels := by
      have ha : raw34525step2 = raw34525step1 := by apply Matrix.ext; unfold raw34525step2 raw34525step1; decide +kernel
      have hl : raw34525step1Labels = labelEmbedding6 ∘ raw34525step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34525step1 raw34525step1Labels raw34525step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

theorem canonical34526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34526 raw34526Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw34526 raw34526Labels = mixedMoment B raw34526step0 raw34526step0Labels := by
      have ha : raw34526step0 = (fun i j => raw34526 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34526step0 raw34526; decide +kernel
      have hl : raw34526step0Labels = raw34526Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34526 raw34526Labels permutation171 permutation3
    mixedMoment B raw34526step0 raw34526step0Labels = mixedMoment B raw34526step1 raw34526step1Labels := by
      have ha : raw34526step1 = raw34526step0 := by apply Matrix.ext; unfold raw34526step1 raw34526step0; decide +kernel
      have hl : raw34526step0Labels = labelEmbedding6 ∘ raw34526step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34526step0 raw34526step0Labels raw34526step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

theorem canonical34527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34527 raw34527Labels = mixedMoment B node4337 node4337Labels := by
  calc
    mixedMoment B raw34527 raw34527Labels = mixedMoment B raw34527step0 raw34527step0Labels := by
      have ha : raw34527step0 = (fun i j => raw34527 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34527step0 raw34527; decide +kernel
      have hl : raw34527step0Labels = raw34527Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34527 raw34527Labels permutation170 permutation3
    mixedMoment B raw34527step0 raw34527step0Labels = mixedMoment B raw34527step1 raw34527step1Labels := by
      have ha : raw34527step1 = raw34527step0 := by apply Matrix.ext; unfold raw34527step1 raw34527step0; decide +kernel
      have hl : raw34527step0Labels = labelEmbedding6 ∘ raw34527step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34527step0 raw34527step0Labels raw34527step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4337 node4337Labels := by rfl

theorem canonical34528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34528 raw34528Labels = mixedMoment B node4936 node4936Labels := by
  calc
    mixedMoment B raw34528 raw34528Labels = mixedMoment B raw34528step0 raw34528step0Labels := by
      have ha : raw34528step0 = (fun i j => raw34528 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34528step0 raw34528; decide +kernel
      have hl : raw34528step0Labels = raw34528Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34528 raw34528Labels permutation170 permutation3
    mixedMoment B raw34528step0 raw34528step0Labels = mixedMoment B raw34528step1 raw34528step1Labels := by
      have ha : raw34528step1 = raw34528step0 := by apply Matrix.ext; unfold raw34528step1 raw34528step0; decide +kernel
      have hl : raw34528step0Labels = labelEmbedding6 ∘ raw34528step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34528step0 raw34528step0Labels raw34528step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4936 node4936Labels := by rfl

theorem canonical34529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34529 raw34529Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw34529 raw34529Labels = mixedMoment B raw34529step0 raw34529step0Labels := by
      have hz : ∀ j, raw34529 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34529step0 = (fun i j => raw34529 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34529step0 raw34529; decide +kernel
      have hl : raw34529step0Labels = raw34529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34529 raw34529Labels permutation434 hz
    mixedMoment B raw34529step0 raw34529step0Labels = mixedMoment B raw34529step1 raw34529step1Labels := by
      have ha : raw34529step1 = (fun i j => raw34529step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34529step1 raw34529step0; decide +kernel
      have hl : raw34529step1Labels = raw34529step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34529step0 raw34529step0Labels permutation36 permutation3
    mixedMoment B raw34529step1 raw34529step1Labels = mixedMoment B raw34529step2 raw34529step2Labels := by
      have ha : raw34529step2 = raw34529step1 := by apply Matrix.ext; unfold raw34529step2 raw34529step1; decide +kernel
      have hl : raw34529step1Labels = labelEmbedding6 ∘ raw34529step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34529step1 raw34529step1Labels raw34529step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

theorem canonical34530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34530 raw34530Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw34530 raw34530Labels = mixedMoment B raw34530step0 raw34530step0Labels := by
      have ha : raw34530step0 = (fun i j => raw34530 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34530step0 raw34530; decide +kernel
      have hl : raw34530step0Labels = raw34530Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34530 raw34530Labels permutation170 permutation3
    mixedMoment B raw34530step0 raw34530step0Labels = mixedMoment B raw34530step1 raw34530step1Labels := by
      have ha : raw34530step1 = raw34530step0 := by apply Matrix.ext; unfold raw34530step1 raw34530step0; decide +kernel
      have hl : raw34530step0Labels = labelEmbedding6 ∘ raw34530step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34530step0 raw34530step0Labels raw34530step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1113 raw1113Labels = mixedMoment B node4337 node4337Labels := by
  calc
    mixedMoment B raw1113 raw1113Labels = mixedMoment B raw1113step0 raw1113step0Labels := by
      have ha : raw1113step0 = (fun i j => raw1113 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1113step0 raw1113; decide +kernel
      have hl : raw1113step0Labels = raw1113Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1113 raw1113Labels permutation152 permutation4
    mixedMoment B raw1113step0 raw1113step0Labels = mixedMoment B raw1113step1 raw1113step1Labels := by
      have ha : raw1113step1 = raw1113step0 := by apply Matrix.ext; unfold raw1113step1 raw1113step0; decide +kernel
      have hl : raw1113step0Labels = labelEmbedding7 ∘ raw1113step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1113step0 raw1113step0Labels raw1113step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4337 node4337Labels := by rfl

theorem canonical1114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1114 raw1114Labels = mixedMoment B node915 node915Labels := by
  calc
    mixedMoment B raw1114 raw1114Labels = mixedMoment B raw1114step0 raw1114step0Labels := by
      have ha : raw1114step0 = (fun i j => raw1114 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1114step0 raw1114; decide +kernel
      have hl : raw1114step0Labels = raw1114Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1114 raw1114Labels permutation152 permutation4
    _ = mixedMoment B node915 node915Labels := by rfl

theorem canonical1115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1115 raw1115Labels = mixedMoment B node1632 node1632Labels := by
  calc
    mixedMoment B raw1115 raw1115Labels = mixedMoment B raw1115step0 raw1115step0Labels := by
      have ha : raw1115step0 = (fun i j => raw1115 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1115step0 raw1115; decide +kernel
      have hl : raw1115step0Labels = raw1115Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1115 raw1115Labels permutation176 permutation6
    mixedMoment B raw1115step0 raw1115step0Labels = mixedMoment B raw1115step1 raw1115step1Labels := by
      have ha : raw1115step1 = -raw1115step0 := by apply Matrix.ext; change ∀ i j, raw1115step1 i j = -(raw1115step0 i j); unfold raw1115step1 raw1115step0; decide +kernel
      have hl : raw1115step1Labels = raw1115step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1115step1 raw1115step1Labels = mixedMoment B raw1115step2 raw1115step2Labels := by
      have ha : raw1115step2 = raw1115step1 := by apply Matrix.ext; unfold raw1115step2 raw1115step1; decide +kernel
      have hl : raw1115step1Labels = labelEmbedding1 ∘ raw1115step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1115step1 raw1115step1Labels raw1115step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1632 node1632Labels := by rfl

theorem canonical1140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1140 raw1140Labels = mixedMoment B node4351 node4351Labels := by
  calc
    mixedMoment B raw1140 raw1140Labels = mixedMoment B raw1140step0 raw1140step0Labels := by
      have ha : raw1140step0 = (fun i j => raw1140 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1140step0 raw1140; decide +kernel
      have hl : raw1140step0Labels = raw1140Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1140 raw1140Labels permutation152 permutation4
    mixedMoment B raw1140step0 raw1140step0Labels = mixedMoment B raw1140step1 raw1140step1Labels := by
      have ha : raw1140step1 = raw1140step0 := by apply Matrix.ext; unfold raw1140step1 raw1140step0; decide +kernel
      have hl : raw1140step0Labels = labelEmbedding7 ∘ raw1140step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1140step0 raw1140step0Labels raw1140step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4351 node4351Labels := by rfl

theorem canonical1141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1141 raw1141Labels = mixedMoment B node929 node929Labels := by
  calc
    mixedMoment B raw1141 raw1141Labels = mixedMoment B raw1141step0 raw1141step0Labels := by
      have ha : raw1141step0 = (fun i j => raw1141 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1141step0 raw1141; decide +kernel
      have hl : raw1141step0Labels = raw1141Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1141 raw1141Labels permutation152 permutation4
    _ = mixedMoment B node929 node929Labels := by rfl

theorem canonical1142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1142 raw1142Labels = mixedMoment B node1680 node1680Labels := by
  calc
    mixedMoment B raw1142 raw1142Labels = mixedMoment B raw1142step0 raw1142step0Labels := by
      have ha : raw1142step0 = (fun i j => raw1142 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1142step0 raw1142; decide +kernel
      have hl : raw1142step0Labels = raw1142Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1142 raw1142Labels permutation170 permutation6
    mixedMoment B raw1142step0 raw1142step0Labels = mixedMoment B raw1142step1 raw1142step1Labels := by
      have ha : raw1142step1 = -raw1142step0 := by apply Matrix.ext; change ∀ i j, raw1142step1 i j = -(raw1142step0 i j); unfold raw1142step1 raw1142step0; decide +kernel
      have hl : raw1142step1Labels = raw1142step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1142step1 raw1142step1Labels = mixedMoment B raw1142step2 raw1142step2Labels := by
      have ha : raw1142step2 = raw1142step1 := by apply Matrix.ext; unfold raw1142step2 raw1142step1; decide +kernel
      have hl : raw1142step1Labels = labelEmbedding1 ∘ raw1142step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1142step1 raw1142step1Labels raw1142step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1680 node1680Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4337 node4337Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node915 node915Labels + mixedMoment B node1632 node1632Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1113 singletonSmall4337
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4337) = raw1113Labels := by decide +kernel
  rw [hl, canonical1113 B hB] at h
  have hc0 : mixedMoment B raw1113 (Fin.cases (0 : Fin 2) singletonSmall4337) =
      mixedMoment B node915 node915Labels := by
    have ha : raw1113 = raw1114 := by apply Matrix.ext; unfold raw1113 raw1114; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4337 = raw1114Labels := by decide +kernel
    rw [ha, hj, canonical1114 B hB]
  have hc1 : mixedMoment B raw1113 (Fin.cases (1 : Fin 2) singletonSmall4337) =
      mixedMoment B node1632 node1632Labels := by
    have ha : raw1113 = raw1115 := by apply Matrix.ext; unfold raw1113 raw1115; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4337 = raw1115Labels := by decide +kernel
    rw [ha, hj, canonical1115 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4351 node4351Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node929 node929Labels + mixedMoment B node1680 node1680Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1140 singletonSmall4351
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4351) = raw1140Labels := by decide +kernel
  rw [hl, canonical1140 B hB] at h
  have hc0 : mixedMoment B raw1140 (Fin.cases (0 : Fin 2) singletonSmall4351) =
      mixedMoment B node929 node929Labels := by
    have ha : raw1140 = raw1141 := by apply Matrix.ext; unfold raw1140 raw1141; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4351 = raw1141Labels := by decide +kernel
    rw [ha, hj, canonical1141 B hB]
  have hc1 : mixedMoment B raw1140 (Fin.cases (1 : Fin 2) singletonSmall4351) =
      mixedMoment B node1680 node1680Labels := by
    have ha : raw1140 = raw1142 := by apply Matrix.ext; unfold raw1140 raw1142; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4351 = raw1142Labels := by decide +kernel
    rw [ha, hj, canonical1142 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem singleton4947 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4947 node4947Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2338 node2338Labels + mixedMoment B node3416 node3416Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1914 singletonSmall4947
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4947) = raw1914Labels := by decide +kernel
  rw [hl, canonical1914 B hB] at h
  have hc0 : mixedMoment B raw1914 (Fin.cases (0 : Fin 2) singletonSmall4947) =
      mixedMoment B node2338 node2338Labels := by
    have ha : raw1914 = raw1915 := by apply Matrix.ext; unfold raw1914 raw1915; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4947 = raw1915Labels := by decide +kernel
    rw [ha, hj, canonical1915 B hB]
  have hc1 : mixedMoment B raw1914 (Fin.cases (1 : Fin 2) singletonSmall4947) =
      mixedMoment B node3416 node3416Labels := by
    have ha : raw1914 = raw1916 := by apply Matrix.ext; unfold raw1914 raw1916; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4947 = raw1916Labels := by decide +kernel
    rw [ha, hj, canonical1916 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5123 node5123Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2536 node2536Labels + mixedMoment B node3370 node3370Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2154 singletonSmall5123
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5123) = raw2154Labels := by decide +kernel
  rw [hl, canonical2154 B hB] at h
  have hc0 : mixedMoment B raw2154 (Fin.cases (0 : Fin 2) singletonSmall5123) =
      mixedMoment B node2536 node2536Labels := by
    have ha : raw2154 = raw2155 := by apply Matrix.ext; unfold raw2154 raw2155; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5123 = raw2155Labels := by decide +kernel
    rw [ha, hj, canonical2155 B hB]
  have hc1 : mixedMoment B raw2154 (Fin.cases (1 : Fin 2) singletonSmall5123) =
      mixedMoment B node3370 node3370Labels := by
    have ha : raw2154 = raw2156 := by apply Matrix.ext; unfold raw2154 raw2156; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5123 = raw2156Labels := by decide +kernel
    rw [ha, hj, canonical2156 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5163 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5163 node5163Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2590 node2590Labels + mixedMoment B node3564 node3564Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2190 singletonSmall5163
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5163) = raw2190Labels := by decide +kernel
  rw [hl, canonical2190 B hB] at h
  have hc0 : mixedMoment B raw2190 (Fin.cases (0 : Fin 2) singletonSmall5163) =
      mixedMoment B node2590 node2590Labels := by
    have ha : raw2190 = raw2191 := by apply Matrix.ext; unfold raw2190 raw2191; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5163 = raw2191Labels := by decide +kernel
    rw [ha, hj, canonical2191 B hB]
  have hc1 : mixedMoment B raw2190 (Fin.cases (1 : Fin 2) singletonSmall5163) =
      mixedMoment B node3564 node3564Labels := by
    have ha : raw2190 = raw2192 := by apply Matrix.ext; unfold raw2190 raw2192; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5163 = raw2192Labels := by decide +kernel
    rw [ha, hj, canonical2192 B hB]
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

theorem singleton5227 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5227 node5227Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2671 node2671Labels + mixedMoment B node3390 node3390Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2247 singletonSmall5227
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5227) = raw2247Labels := by decide +kernel
  rw [hl, canonical2247 B hB] at h
  have hc0 : mixedMoment B raw2247 (Fin.cases (0 : Fin 2) singletonSmall5227) =
      mixedMoment B node2671 node2671Labels := by
    have ha : raw2247 = raw2248 := by apply Matrix.ext; unfold raw2247 raw2248; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5227 = raw2248Labels := by decide +kernel
    rw [ha, hj, canonical2248 B hB]
  have hc1 : mixedMoment B raw2247 (Fin.cases (1 : Fin 2) singletonSmall5227) =
      mixedMoment B node3390 node3390Labels := by
    have ha : raw2247 = raw2249 := by apply Matrix.ext; unfold raw2247 raw2249; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5227 = raw2249Labels := by decide +kernel
    rw [ha, hj, canonical2249 B hB]
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

theorem singleton5290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5290 node5290Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2764 node2764Labels + mixedMoment B node3581 node3581Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2292 singletonSmall5290
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5290) = raw2292Labels := by decide +kernel
  rw [hl, canonical2292 B hB] at h
  have hc0 : mixedMoment B raw2292 (Fin.cases (0 : Fin 2) singletonSmall5290) =
      mixedMoment B node2764 node2764Labels := by
    have ha : raw2292 = raw2293 := by apply Matrix.ext; unfold raw2292 raw2293; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5290 = raw2293Labels := by decide +kernel
    rw [ha, hj, canonical2293 B hB]
  have hc1 : mixedMoment B raw2292 (Fin.cases (1 : Fin 2) singletonSmall5290) =
      mixedMoment B node3581 node3581Labels := by
    have ha : raw2292 = raw2294 := by apply Matrix.ext; unfold raw2292 raw2294; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5290 = raw2294Labels := by decide +kernel
    rw [ha, hj, canonical2294 B hB]
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

theorem zero5462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5462 node5462Labels = 0 := by
  exact mixedMoment_alpha B hF node5462 node5462Labels 2 permutation152
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node915 node915Labels = Sparse.eval nodeValue915 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 915) = mixedMoment B node915 node915Labels := rfl
  simpa [nodeValue915, Sparse.eval] using hc.symm

theorem sound929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node929 node929Labels = Sparse.eval nodeValue929 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 929) = mixedMoment B node929 node929Labels := rfl
  simpa [nodeValue929, Sparse.eval] using hc.symm

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

theorem sound1632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1632 node1632Labels = Sparse.eval nodeValue1632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1632) = mixedMoment B node1632 node1632Labels := rfl
  simpa [nodeValue1632, Sparse.eval] using hc.symm

theorem sound1644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1644 node1644Labels = Sparse.eval nodeValue1644 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1644) = mixedMoment B node1644 node1644Labels := rfl
  simpa [nodeValue1644, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1680 node1680Labels = Sparse.eval nodeValue1680 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1680) = mixedMoment B node1680 node1680Labels := rfl
  simpa [nodeValue1680, Sparse.eval] using hc.symm

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

theorem sound2328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2328 node2328Labels = Sparse.eval nodeValue2328 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2328) = mixedMoment B node2328 node2328Labels := rfl
  simpa [nodeValue2328, Sparse.eval] using hc.symm

theorem sound2338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2338 node2338Labels = Sparse.eval nodeValue2338 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2338) = mixedMoment B node2338 node2338Labels := rfl
  simpa [nodeValue2338, Sparse.eval] using hc.symm

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

theorem sound2536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2536 node2536Labels = Sparse.eval nodeValue2536 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2536) = mixedMoment B node2536 node2536Labels := rfl
  simpa [nodeValue2536, Sparse.eval] using hc.symm

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

theorem sound2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2590 node2590Labels = Sparse.eval nodeValue2590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2590) = mixedMoment B node2590 node2590Labels := rfl
  simpa [nodeValue2590, Sparse.eval] using hc.symm

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

theorem sound2671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2671 node2671Labels = Sparse.eval nodeValue2671 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2671) = mixedMoment B node2671 node2671Labels := rfl
  simpa [nodeValue2671, Sparse.eval] using hc.symm

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

theorem sound2764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2764 node2764Labels = Sparse.eval nodeValue2764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2764) = mixedMoment B node2764 node2764Labels := rfl
  simpa [nodeValue2764, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3370 node3370Labels = Sparse.eval nodeValue3370 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3370) = mixedMoment B node3370 node3370Labels := rfl
  simpa [nodeValue3370, Sparse.eval] using hc.symm

theorem sound3390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3390 node3390Labels = Sparse.eval nodeValue3390 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3390) = mixedMoment B node3390 node3390Labels := rfl
  simpa [nodeValue3390, Sparse.eval] using hc.symm

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

theorem sound3401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3401 node3401Labels = Sparse.eval nodeValue3401 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3401) = mixedMoment B node3401 node3401Labels := rfl
  simpa [nodeValue3401, Sparse.eval] using hc.symm

theorem sound3416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3416 node3416Labels = Sparse.eval nodeValue3416 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3416) = mixedMoment B node3416 node3416Labels := rfl
  simpa [nodeValue3416, Sparse.eval] using hc.symm

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

theorem sound3564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3564 node3564Labels = Sparse.eval nodeValue3564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3564) = mixedMoment B node3564 node3564Labels := rfl
  simpa [nodeValue3564, Sparse.eval] using hc.symm

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4337 node4337Labels = Sparse.eval nodeValue4337 (mixedVector B) := by
  have h := singleton4337 B _hB
  rw [sound915 B _hB _hF, sound1632 B _hB _hF] at h
  norm_num [nodeValue4337, nodeValue915, nodeValue1632, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4351 node4351Labels = Sparse.eval nodeValue4351 (mixedVector B) := by
  have h := singleton4351 B _hB
  rw [sound929 B _hB _hF, sound1680 B _hB _hF] at h
  norm_num [nodeValue4351, nodeValue929, nodeValue1680, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4936 node4936Labels = Sparse.eval nodeValue4936 (mixedVector B) := by
  have h := singleton4936 B _hB
  rw [sound2328 B _hB _hF, sound3401 B _hB _hF] at h
  norm_num [nodeValue4936, nodeValue2328, nodeValue3401, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4947 node4947Labels = Sparse.eval nodeValue4947 (mixedVector B) := by
  have h := singleton4947 B _hB
  rw [sound2338 B _hB _hF, sound3416 B _hB _hF] at h
  norm_num [nodeValue4947, nodeValue2338, nodeValue3416, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5123 node5123Labels = Sparse.eval nodeValue5123 (mixedVector B) := by
  have h := singleton5123 B _hB
  rw [sound2536 B _hB _hF, sound3370 B _hB _hF] at h
  norm_num [nodeValue5123, nodeValue2536, nodeValue3370, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5163 node5163Labels = Sparse.eval nodeValue5163 (mixedVector B) := by
  have h := singleton5163 B _hB
  rw [sound2590 B _hB _hF, sound3564 B _hB _hF] at h
  norm_num [nodeValue5163, nodeValue2590, nodeValue3564, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5227 node5227Labels = Sparse.eval nodeValue5227 (mixedVector B) := by
  have h := singleton5227 B _hB
  rw [sound2671 B _hB _hF, sound3390 B _hB _hF] at h
  norm_num [nodeValue5227, nodeValue2671, nodeValue3390, Sparse.eval] at h ⊢
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

theorem sound5290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5290 node5290Labels = Sparse.eval nodeValue5290 (mixedVector B) := by
  have h := singleton5290 B _hB
  rw [sound2764 B _hB _hF, sound3581 B _hB _hF] at h
  norm_num [nodeValue5290, nodeValue2764, nodeValue3581, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5462 node5462Labels = Sparse.eval nodeValue5462 (mixedVector B) := by
  simpa only [nodeValue5462, Sparse.eval_nil] using zero5462 B _hB _hF

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

theorem sourceEq2504 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2504 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2504 + difference 0 1) (sourceB2504 + difference 1 0) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5462) := by
    have ha : (tripleCharges (sourceA2504 + difference 0 1) (sourceB2504 + difference 1 0) sourceC2504) = raw18654 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw18654; decide +kernel
    rw [ha]
    exact (canonical18654 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2504 + difference 0 2) (sourceB2504 + difference 2 0) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2504 + difference 0 2) (sourceB2504 + difference 2 0) sourceC2504) = raw3045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw3045; decide +kernel
    rw [ha]
    exact (canonical3045 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2504 + difference 0 3) (sourceB2504 + difference 3 0) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2504 + difference 0 3) (sourceB2504 + difference 3 0) sourceC2504) = raw3040 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw3040; decide +kernel
    rw [ha]
    exact (canonical3040 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2504 + difference 0 4) (sourceB2504 + difference 4 0) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2504 + difference 0 4) (sourceB2504 + difference 4 0) sourceC2504) = raw18655 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw18655; decide +kernel
    rw [ha]
    exact (canonical18655 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2504 + difference 0 5) (sourceB2504 + difference 5 0) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA2504 + difference 0 5) (sourceB2504 + difference 5 0) sourceC2504) = raw18656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw18656; decide +kernel
    rw [ha]
    exact (canonical18656 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2504 + difference 1 0) (sourceB2504 + difference 0 1) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA2504 + difference 1 0) (sourceB2504 + difference 0 1) sourceC2504) = raw13578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw13578; decide +kernel
    rw [ha]
    exact (canonical13578 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2504 + difference 1 2) (sourceB2504 + difference 2 1) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA2504 + difference 1 2) (sourceB2504 + difference 2 1) sourceC2504) = raw3044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw3044; decide +kernel
    rw [ha]
    exact (canonical3044 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2504 + difference 1 3) (sourceB2504 + difference 3 1) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA2504 + difference 1 3) (sourceB2504 + difference 3 1) sourceC2504) = raw3039 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw3039; decide +kernel
    rw [ha]
    exact (canonical3039 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2504 + difference 1 4) (sourceB2504 + difference 4 1) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA2504 + difference 1 4) (sourceB2504 + difference 4 1) sourceC2504) = raw13580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw13580; decide +kernel
    rw [ha]
    exact (canonical13580 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2504 + difference 1 5) (sourceB2504 + difference 5 1) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5227) := by
    have ha : (tripleCharges (sourceA2504 + difference 1 5) (sourceB2504 + difference 5 1) sourceC2504) = raw13581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw13581; decide +kernel
    rw [ha]
    exact (canonical13581 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2504 + difference 2 0) (sourceB2504 + difference 0 2) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4337) := by
    have ha : (tripleCharges (sourceA2504 + difference 2 0) (sourceB2504 + difference 0 2) sourceC2504) = raw34518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw34518; decide +kernel
    rw [ha]
    exact (canonical34518 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2504 + difference 2 1) (sourceB2504 + difference 1 2) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4936) := by
    have ha : (tripleCharges (sourceA2504 + difference 2 1) (sourceB2504 + difference 1 2) sourceC2504) = raw34519 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw34519; decide +kernel
    rw [ha]
    exact (canonical34519 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2504 + difference 2 3) (sourceB2504 + difference 3 2) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2504 + difference 2 3) (sourceB2504 + difference 3 2) sourceC2504) = raw34520 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw34520; decide +kernel
    rw [ha]
    exact (canonical34520 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2504 + difference 2 4) (sourceB2504 + difference 4 2) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2504 + difference 2 4) (sourceB2504 + difference 4 2) sourceC2504) = raw34521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw34521; decide +kernel
    rw [ha]
    exact (canonical34521 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2504 + difference 2 5) (sourceB2504 + difference 5 2) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2504 + difference 2 5) (sourceB2504 + difference 5 2) sourceC2504) = raw34522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw34522; decide +kernel
    rw [ha]
    exact (canonical34522 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2504 + difference 3 0) (sourceB2504 + difference 0 3) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4337) := by
    have ha : (tripleCharges (sourceA2504 + difference 3 0) (sourceB2504 + difference 0 3) sourceC2504) = raw34523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw34523; decide +kernel
    rw [ha]
    exact (canonical34523 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2504 + difference 3 1) (sourceB2504 + difference 1 3) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4936) := by
    have ha : (tripleCharges (sourceA2504 + difference 3 1) (sourceB2504 + difference 1 3) sourceC2504) = raw34524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw34524; decide +kernel
    rw [ha]
    exact (canonical34524 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2504 + difference 3 2) (sourceB2504 + difference 2 3) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2504 + difference 3 2) (sourceB2504 + difference 2 3) sourceC2504) = raw13583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw13583; decide +kernel
    rw [ha]
    exact (canonical13583 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2504 + difference 3 4) (sourceB2504 + difference 4 3) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2504 + difference 3 4) (sourceB2504 + difference 4 3) sourceC2504) = raw34525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw34525; decide +kernel
    rw [ha]
    exact (canonical34525 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2504 + difference 3 5) (sourceB2504 + difference 5 3) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2504 + difference 3 5) (sourceB2504 + difference 5 3) sourceC2504) = raw34526 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw34526; decide +kernel
    rw [ha]
    exact (canonical34526 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2504 + difference 4 0) (sourceB2504 + difference 0 4) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4337) := by
    have ha : (tripleCharges (sourceA2504 + difference 4 0) (sourceB2504 + difference 0 4) sourceC2504) = raw34527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw34527; decide +kernel
    rw [ha]
    exact (canonical34527 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2504 + difference 4 1) (sourceB2504 + difference 1 4) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4936) := by
    have ha : (tripleCharges (sourceA2504 + difference 4 1) (sourceB2504 + difference 1 4) sourceC2504) = raw34528 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw34528; decide +kernel
    rw [ha]
    exact (canonical34528 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2504 + difference 4 2) (sourceB2504 + difference 2 4) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2504 + difference 4 2) (sourceB2504 + difference 2 4) sourceC2504) = raw13588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw13588; decide +kernel
    rw [ha]
    exact (canonical13588 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2504 + difference 4 3) (sourceB2504 + difference 3 4) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2504 + difference 4 3) (sourceB2504 + difference 3 4) sourceC2504) = raw34529 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw34529; decide +kernel
    rw [ha]
    exact (canonical34529 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2504 + difference 4 5) (sourceB2504 + difference 5 4) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2504 + difference 4 5) (sourceB2504 + difference 5 4) sourceC2504) = raw34530 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw34530; decide +kernel
    rw [ha]
    exact (canonical34530 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2504 + difference 5 0) (sourceB2504 + difference 0 5) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4351) := by
    have ha : (tripleCharges (sourceA2504 + difference 5 0) (sourceB2504 + difference 0 5) sourceC2504) = raw25071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw25071; decide +kernel
    rw [ha]
    exact (canonical25071 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2504 + difference 5 1) (sourceB2504 + difference 1 5) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4947) := by
    have ha : (tripleCharges (sourceA2504 + difference 5 1) (sourceB2504 + difference 1 5) sourceC2504) = raw32201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw32201; decide +kernel
    rw [ha]
    exact (canonical32201 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2504 + difference 5 2) (sourceB2504 + difference 2 5) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2504 + difference 5 2) (sourceB2504 + difference 2 5) sourceC2504) = raw13592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw13592; decide +kernel
    rw [ha]
    exact (canonical13592 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2504 + difference 5 3) (sourceB2504 + difference 3 5) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2504 + difference 5 3) (sourceB2504 + difference 3 5) sourceC2504) = raw17687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw17687; decide +kernel
    rw [ha]
    exact (canonical17687 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2504 + difference 5 4) (sourceB2504 + difference 4 5) sourceC2504) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2504 + difference 5 4) (sourceB2504 + difference 4 5) sourceC2504) = raw32202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2504 sourceB2504 sourceC2504 difference raw32202; decide +kernel
    rw [ha]
    exact (canonical32202 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2504 sourceB2504 sourceC2504
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2504, Integer.Sparse.eval]
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

theorem reindexCheck2018 : Integer.Sparse.reindex keyMap MixedData.row2018 = numericRow2018 := by decide +kernel

theorem numericCheck2018 (x : Master → ℝ) : Integer.Sparse.eval numericRow2018 x =
    (5760 : ℝ) * reducedSource2018 x := by
  norm_num [numericRow2018, reducedSource2018, Integer.Sparse.eval, Sparse.eval, nodeValue4337, nodeValue4351, nodeValue4451, nodeValue4936, nodeValue4947, nodeValue5123, nodeValue5163, nodeValue5172, nodeValue5227, nodeValue5290, nodeValue5447, nodeValue5462, nodeValue5485]
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

theorem reducedZero2018 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2018 (mixedVector B) = 0 := by
  have h4337 : mixedVector B (Sum.inr 4337) = Sparse.eval nodeValue4337 (mixedVector B) := by
    change mixedMoment B node4337 node4337Labels = _
    exact sound4337 B hB hF
  have h4351 : mixedVector B (Sum.inr 4351) = Sparse.eval nodeValue4351 (mixedVector B) := by
    change mixedMoment B node4351 node4351Labels = _
    exact sound4351 B hB hF
  have h4451 : mixedVector B (Sum.inr 4451) = Sparse.eval nodeValue4451 (mixedVector B) := by
    change mixedMoment B node4451 node4451Labels = _
    exact sound4451 B hB hF
  have h4936 : mixedVector B (Sum.inr 4936) = Sparse.eval nodeValue4936 (mixedVector B) := by
    change mixedMoment B node4936 node4936Labels = _
    exact sound4936 B hB hF
  have h4947 : mixedVector B (Sum.inr 4947) = Sparse.eval nodeValue4947 (mixedVector B) := by
    change mixedMoment B node4947 node4947Labels = _
    exact sound4947 B hB hF
  have h5123 : mixedVector B (Sum.inr 5123) = Sparse.eval nodeValue5123 (mixedVector B) := by
    change mixedMoment B node5123 node5123Labels = _
    exact sound5123 B hB hF
  have h5163 : mixedVector B (Sum.inr 5163) = Sparse.eval nodeValue5163 (mixedVector B) := by
    change mixedMoment B node5163 node5163Labels = _
    exact sound5163 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172_e B hB hF
  have h5227 : mixedVector B (Sum.inr 5227) = Sparse.eval nodeValue5227 (mixedVector B) := by
    change mixedMoment B node5227 node5227Labels = _
    exact sound5227 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  have h5462 : mixedVector B (Sum.inr 5462) = Sparse.eval nodeValue5462 (mixedVector B) := by
    change mixedMoment B node5462 node5462Labels = _
    exact sound5462 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485_e B hB hF
  simpa only [sourceForm2504, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4337, h4351, h4451, h4936, h4947, h5123, h5163, h5172, h5227, h5290, h5447, h5462, h5485, reducedSource2018] using sourceEq2504 B hB

theorem rowSound2018_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2018 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2018, numericCheck2018, reducedZero2018 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e_oai
