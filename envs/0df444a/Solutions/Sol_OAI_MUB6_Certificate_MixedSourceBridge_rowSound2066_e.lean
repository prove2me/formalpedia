-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:57:44.283182+00:00
-- url     : https://prove2.me/submissions/ab112ec4-ebac-4776-8785-7f7ff5ff9817

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5386_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5388_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5433_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1536 raw1536Labels = mixedMoment B node4660 node4660Labels := by
  calc
    mixedMoment B raw1536 raw1536Labels = mixedMoment B raw1536step0 raw1536step0Labels := by
      have ha : raw1536step0 = (fun i j => raw1536 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1536step0 raw1536; decide +kernel
      have hl : raw1536step0Labels = raw1536Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1536 raw1536Labels permutation152 permutation4
    mixedMoment B raw1536step0 raw1536step0Labels = mixedMoment B raw1536step1 raw1536step1Labels := by
      have ha : raw1536step1 = raw1536step0 := by apply Matrix.ext; unfold raw1536step1 raw1536step0; decide +kernel
      have hl : raw1536step0Labels = labelEmbedding7 ∘ raw1536step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1536step0 raw1536step0Labels raw1536step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4660 node4660Labels := by rfl

theorem canonical1537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1537 raw1537Labels = mixedMoment B node1786 node1786Labels := by
  calc
    mixedMoment B raw1537 raw1537Labels = mixedMoment B raw1537step0 raw1537step0Labels := by
      have ha : raw1537step0 = (fun i j => raw1537 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1537step0 raw1537; decide +kernel
      have hl : raw1537step0Labels = raw1537Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1537 raw1537Labels permutation152 permutation4
    _ = mixedMoment B node1786 node1786Labels := by rfl

theorem canonical1538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1538 raw1538Labels = mixedMoment B node1982 node1982Labels := by
  calc
    mixedMoment B raw1538 raw1538Labels = mixedMoment B raw1538step0 raw1538step0Labels := by
      have ha : raw1538step0 = (fun i j => raw1538 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1538step0 raw1538; decide +kernel
      have hl : raw1538step0Labels = raw1538Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1538 raw1538Labels permutation176 permutation6
    mixedMoment B raw1538step0 raw1538step0Labels = mixedMoment B raw1538step1 raw1538step1Labels := by
      have ha : raw1538step1 = -raw1538step0 := by apply Matrix.ext; change ∀ i j, raw1538step1 i j = -(raw1538step0 i j); unfold raw1538step1 raw1538step0; decide +kernel
      have hl : raw1538step1Labels = raw1538step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1538step1 raw1538step1Labels = mixedMoment B raw1538step2 raw1538step2Labels := by
      have ha : raw1538step2 = raw1538step1 := by apply Matrix.ext; unfold raw1538step2 raw1538step1; decide +kernel
      have hl : raw1538step1Labels = labelEmbedding1 ∘ raw1538step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1538step1 raw1538step1Labels raw1538step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1982 node1982Labels := by rfl

theorem canonical1539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1539 raw1539Labels = mixedMoment B node4661 node4661Labels := by
  calc
    mixedMoment B raw1539 raw1539Labels = mixedMoment B raw1539step0 raw1539step0Labels := by
      have ha : raw1539step0 = (fun i j => raw1539 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1539step0 raw1539; decide +kernel
      have hl : raw1539step0Labels = raw1539Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1539 raw1539Labels permutation152 permutation4
    mixedMoment B raw1539step0 raw1539step0Labels = mixedMoment B raw1539step1 raw1539step1Labels := by
      have ha : raw1539step1 = raw1539step0 := by apply Matrix.ext; unfold raw1539step1 raw1539step0; decide +kernel
      have hl : raw1539step0Labels = labelEmbedding7 ∘ raw1539step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1539step0 raw1539step0Labels raw1539step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4661 node4661Labels := by rfl

theorem canonical1540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1540 raw1540Labels = mixedMoment B node1787 node1787Labels := by
  calc
    mixedMoment B raw1540 raw1540Labels = mixedMoment B raw1540step0 raw1540step0Labels := by
      have ha : raw1540step0 = (fun i j => raw1540 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1540step0 raw1540; decide +kernel
      have hl : raw1540step0Labels = raw1540Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1540 raw1540Labels permutation152 permutation4
    _ = mixedMoment B node1787 node1787Labels := by rfl

theorem canonical1541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1541 raw1541Labels = mixedMoment B node1983 node1983Labels := by
  calc
    mixedMoment B raw1541 raw1541Labels = mixedMoment B raw1541step0 raw1541step0Labels := by
      have ha : raw1541step0 = (fun i j => raw1541 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1541step0 raw1541; decide +kernel
      have hl : raw1541step0Labels = raw1541Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1541 raw1541Labels permutation176 permutation6
    mixedMoment B raw1541step0 raw1541step0Labels = mixedMoment B raw1541step1 raw1541step1Labels := by
      have ha : raw1541step1 = -raw1541step0 := by apply Matrix.ext; change ∀ i j, raw1541step1 i j = -(raw1541step0 i j); unfold raw1541step1 raw1541step0; decide +kernel
      have hl : raw1541step1Labels = raw1541step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1541step1 raw1541step1Labels = mixedMoment B raw1541step2 raw1541step2Labels := by
      have ha : raw1541step2 = raw1541step1 := by apply Matrix.ext; unfold raw1541step2 raw1541step1; decide +kernel
      have hl : raw1541step1Labels = labelEmbedding1 ∘ raw1541step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1541step1 raw1541step1Labels raw1541step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1983 node1983Labels := by rfl

theorem canonical1560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1560 raw1560Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw1560 raw1560Labels = mixedMoment B raw1560step0 raw1560step0Labels := by
      have ha : raw1560step0 = (fun i j => raw1560 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1560step0 raw1560; decide +kernel
      have hl : raw1560step0Labels = raw1560Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1560 raw1560Labels permutation152 permutation4
    mixedMoment B raw1560step0 raw1560step0Labels = mixedMoment B raw1560step1 raw1560step1Labels := by
      have ha : raw1560step1 = raw1560step0 := by apply Matrix.ext; unfold raw1560step1 raw1560step0; decide +kernel
      have hl : raw1560step0Labels = labelEmbedding7 ∘ raw1560step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1560step0 raw1560step0Labels raw1560step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4679 node4679Labels := by rfl

theorem canonical1561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1561 raw1561Labels = mixedMoment B node1805 node1805Labels := by
  calc
    mixedMoment B raw1561 raw1561Labels = mixedMoment B raw1561step0 raw1561step0Labels := by
      have ha : raw1561step0 = (fun i j => raw1561 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1561step0 raw1561; decide +kernel
      have hl : raw1561step0Labels = raw1561Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1561 raw1561Labels permutation152 permutation4
    _ = mixedMoment B node1805 node1805Labels := by rfl

theorem canonical1562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1562 raw1562Labels = mixedMoment B node2150 node2150Labels := by
  calc
    mixedMoment B raw1562 raw1562Labels = mixedMoment B raw1562step0 raw1562step0Labels := by
      have ha : raw1562step0 = (fun i j => raw1562 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1562step0 raw1562; decide +kernel
      have hl : raw1562step0Labels = raw1562Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1562 raw1562Labels permutation152 permutation6
    mixedMoment B raw1562step0 raw1562step0Labels = mixedMoment B raw1562step1 raw1562step1Labels := by
      have ha : raw1562step1 = -raw1562step0 := by apply Matrix.ext; change ∀ i j, raw1562step1 i j = -(raw1562step0 i j); unfold raw1562step1 raw1562step0; decide +kernel
      have hl : raw1562step1Labels = raw1562step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1562step1 raw1562step1Labels = mixedMoment B raw1562step2 raw1562step2Labels := by
      have ha : raw1562step2 = raw1562step1 := by apply Matrix.ext; unfold raw1562step2 raw1562step1; decide +kernel
      have hl : raw1562step1Labels = labelEmbedding1 ∘ raw1562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1562step1 raw1562step1Labels raw1562step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2150 node2150Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1752 raw1752Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw1752 raw1752Labels = mixedMoment B raw1752step0 raw1752step0Labels := by
      have ha : raw1752step0 = (fun i j => raw1752 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1752step0 raw1752; decide +kernel
      have hl : raw1752step0Labels = raw1752Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1752 raw1752Labels permutation152 permutation4
    mixedMoment B raw1752step0 raw1752step0Labels = mixedMoment B raw1752step1 raw1752step1Labels := by
      have ha : raw1752step1 = raw1752step0 := by apply Matrix.ext; unfold raw1752step1 raw1752step0; decide +kernel
      have hl : raw1752step0Labels = labelEmbedding7 ∘ raw1752step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1752step0 raw1752step0Labels raw1752step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

theorem canonical1753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1753 raw1753Labels = mixedMoment B node2046 node2046Labels := by
  calc
    mixedMoment B raw1753 raw1753Labels = mixedMoment B raw1753step0 raw1753step0Labels := by
      have ha : raw1753step0 = (fun i j => raw1753 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1753step0 raw1753; decide +kernel
      have hl : raw1753step0Labels = raw1753Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1753 raw1753Labels permutation152 permutation4
    _ = mixedMoment B node2046 node2046Labels := by rfl

theorem canonical1754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1754 raw1754Labels = mixedMoment B node2077 node2077Labels := by
  calc
    mixedMoment B raw1754 raw1754Labels = mixedMoment B raw1754step0 raw1754step0Labels := by
      have ha : raw1754step0 = (fun i j => raw1754 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1754step0 raw1754; decide +kernel
      have hl : raw1754step0Labels = raw1754Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1754 raw1754Labels permutation176 permutation6
    mixedMoment B raw1754step0 raw1754step0Labels = mixedMoment B raw1754step1 raw1754step1Labels := by
      have ha : raw1754step1 = -raw1754step0 := by apply Matrix.ext; change ∀ i j, raw1754step1 i j = -(raw1754step0 i j); unfold raw1754step1 raw1754step0; decide +kernel
      have hl : raw1754step1Labels = raw1754step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1754step1 raw1754step1Labels = mixedMoment B raw1754step2 raw1754step2Labels := by
      have ha : raw1754step2 = raw1754step1 := by apply Matrix.ext; unfold raw1754step2 raw1754step1; decide +kernel
      have hl : raw1754step1Labels = labelEmbedding1 ∘ raw1754step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1754step1 raw1754step1Labels raw1754step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2077 node2077Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18359 raw18359Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18359 raw18359Labels = mixedMoment B raw18359step0 raw18359step0Labels := by
      have ha : raw18359step0 = (fun i j => raw18359 (permutation303 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18359step0 raw18359; decide +kernel
      have hl : raw18359step0Labels = raw18359Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18359 raw18359Labels permutation303 permutation5
    mixedMoment B raw18359step0 raw18359step0Labels = mixedMoment B raw18359step1 raw18359step1Labels := by
      have ha : raw18359step1 = -raw18359step0 := by apply Matrix.ext; change ∀ i j, raw18359step1 i j = -(raw18359step0 i j); unfold raw18359step1 raw18359step0; decide +kernel
      have hl : raw18359step1Labels = raw18359step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18359step1 raw18359step1Labels = mixedMoment B raw18359step2 raw18359step2Labels := by
      have ha : raw18359step2 = raw18359step1 := by apply Matrix.ext; unfold raw18359step2 raw18359step1; decide +kernel
      have hl : raw18359step1Labels = labelEmbedding8 ∘ raw18359step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18359step1 raw18359step1Labels raw18359step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical18365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18365 raw18365Labels = mixedMoment B node5386 node5386Labels := by
  calc
    mixedMoment B raw18365 raw18365Labels = mixedMoment B raw18365step0 raw18365step0Labels := by
      have ha : raw18365step0 = (fun i j => raw18365 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18365step0 raw18365; decide +kernel
      have hl : raw18365step0Labels = raw18365Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18365 raw18365Labels permutation160 permutation2
    _ = mixedMoment B node5386 node5386Labels := by rfl

theorem canonical18369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18369 raw18369Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw18369 raw18369Labels = mixedMoment B raw18369step0 raw18369step0Labels := by
      have ha : raw18369step0 = (fun i j => raw18369 (permutation270 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18369step0 raw18369; decide +kernel
      have hl : raw18369step0Labels = raw18369Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18369 raw18369Labels permutation270 permutation3
    mixedMoment B raw18369step0 raw18369step0Labels = mixedMoment B raw18369step1 raw18369step1Labels := by
      have ha : raw18369step1 = raw18369step0 := by apply Matrix.ext; unfold raw18369step1 raw18369step0; decide +kernel
      have hl : raw18369step0Labels = labelEmbedding6 ∘ raw18369step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18369step0 raw18369step0Labels raw18369step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical18373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18373 raw18373Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw18373 raw18373Labels = mixedMoment B raw18373step0 raw18373step0Labels := by
      have ha : raw18373step0 = (fun i j => raw18373 (permutation269 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18373step0 raw18373; decide +kernel
      have hl : raw18373step0Labels = raw18373Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18373 raw18373Labels permutation269 permutation3
    mixedMoment B raw18373step0 raw18373step0Labels = mixedMoment B raw18373step1 raw18373step1Labels := by
      have ha : raw18373step1 = raw18373step0 := by apply Matrix.ext; unfold raw18373step1 raw18373step0; decide +kernel
      have hl : raw18373step0Labels = labelEmbedding6 ∘ raw18373step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18373step0 raw18373step0Labels raw18373step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical18378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18378 raw18378Labels = mixedMoment B node5422 node5422Labels := by
  calc
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical18379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18379 raw18379Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18379 raw18379Labels = mixedMoment B raw18379step0 raw18379step0Labels := by
      have hz : ∀ j, raw18379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18379step0 = (fun i j => raw18379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18379step0 raw18379; decide +kernel
      have hl : raw18379step0Labels = raw18379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18379 raw18379Labels permutation434 hz
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical18380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18380 raw18380Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18380 raw18380Labels = mixedMoment B raw18380step0 raw18380step0Labels := by
      have hz : ∀ j, raw18380 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18380step0 = (fun i j => raw18380 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18380step0 raw18380; decide +kernel
      have hl : raw18380step0Labels = raw18380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18380 raw18380Labels permutation520 hz
    _ = mixedMoment B node5434 node5434Labels := by rfl

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

theorem canonical1944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1944 raw1944Labels = mixedMoment B node4968 node4968Labels := by
  calc
    mixedMoment B raw1944 raw1944Labels = mixedMoment B raw1944step0 raw1944step0Labels := by
      have ha : raw1944step0 = (fun i j => raw1944 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1944step0 raw1944; decide +kernel
      have hl : raw1944step0Labels = raw1944Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1944 raw1944Labels permutation152 permutation5
    mixedMoment B raw1944step0 raw1944step0Labels = mixedMoment B raw1944step1 raw1944step1Labels := by
      have ha : raw1944step1 = raw1944step0 := by apply Matrix.ext; unfold raw1944step1 raw1944step0; decide +kernel
      have hl : raw1944step0Labels = labelEmbedding8 ∘ raw1944step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1944step0 raw1944step0Labels raw1944step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4968 node4968Labels := by rfl

theorem canonical1945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1945 raw1945Labels = mixedMoment B node2809 node2809Labels := by
  calc
    mixedMoment B raw1945 raw1945Labels = mixedMoment B raw1945step0 raw1945step0Labels := by
      have ha : raw1945step0 = (fun i j => raw1945 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1945step0 raw1945; decide +kernel
      have hl : raw1945step0Labels = raw1945Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1945 raw1945Labels permutation164 permutation4
    _ = mixedMoment B node2809 node2809Labels := by rfl

theorem canonical1946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1946 raw1946Labels = mixedMoment B node3587 node3587Labels := by
  calc
    mixedMoment B raw1946 raw1946Labels = mixedMoment B raw1946step0 raw1946step0Labels := by
      have ha : raw1946step0 = (fun i j => raw1946 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1946step0 raw1946; decide +kernel
      have hl : raw1946step0Labels = raw1946Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1946 raw1946Labels permutation152 permutation3
    mixedMoment B raw1946step0 raw1946step0Labels = mixedMoment B raw1946step1 raw1946step1Labels := by
      have ha : raw1946step1 = -raw1946step0 := by apply Matrix.ext; change ∀ i j, raw1946step1 i j = -(raw1946step0 i j); unfold raw1946step1 raw1946step0; decide +kernel
      have hl : raw1946step1Labels = raw1946step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1946step1 raw1946step1Labels = mixedMoment B raw1946step2 raw1946step2Labels := by
      have ha : raw1946step2 = raw1946step1 := by apply Matrix.ext; unfold raw1946step2 raw1946step1; decide +kernel
      have hl : raw1946step1Labels = labelEmbedding1 ∘ raw1946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1946step1 raw1946step1Labels raw1946step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3587 node3587Labels := by rfl

theorem canonical2043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2043 raw2043Labels = mixedMoment B node5030 node5030Labels := by
  calc
    mixedMoment B raw2043 raw2043Labels = mixedMoment B raw2043step0 raw2043step0Labels := by
      have ha : raw2043step0 = (fun i j => raw2043 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2043step0 raw2043; decide +kernel
      have hl : raw2043step0Labels = raw2043Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2043 raw2043Labels permutation152 permutation4
    mixedMoment B raw2043step0 raw2043step0Labels = mixedMoment B raw2043step1 raw2043step1Labels := by
      have ha : raw2043step1 = raw2043step0 := by apply Matrix.ext; unfold raw2043step1 raw2043step0; decide +kernel
      have hl : raw2043step0Labels = labelEmbedding7 ∘ raw2043step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2043step0 raw2043step0Labels raw2043step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5030 node5030Labels := by rfl

theorem canonical2044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2044 raw2044Labels = mixedMoment B node2419 node2419Labels := by
  calc
    mixedMoment B raw2044 raw2044Labels = mixedMoment B raw2044step0 raw2044step0Labels := by
      have ha : raw2044step0 = (fun i j => raw2044 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2044step0 raw2044; decide +kernel
      have hl : raw2044step0Labels = raw2044Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2044 raw2044Labels permutation152 permutation4
    _ = mixedMoment B node2419 node2419Labels := by rfl

theorem canonical2045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2045 raw2045Labels = mixedMoment B node3425 node3425Labels := by
  calc
    mixedMoment B raw2045 raw2045Labels = mixedMoment B raw2045step0 raw2045step0Labels := by
      have ha : raw2045step0 = (fun i j => raw2045 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2045step0 raw2045; decide +kernel
      have hl : raw2045step0Labels = raw2045Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2045 raw2045Labels permutation154 permutation6
    mixedMoment B raw2045step0 raw2045step0Labels = mixedMoment B raw2045step1 raw2045step1Labels := by
      have ha : raw2045step1 = -raw2045step0 := by apply Matrix.ext; change ∀ i j, raw2045step1 i j = -(raw2045step0 i j); unfold raw2045step1 raw2045step0; decide +kernel
      have hl : raw2045step1Labels = raw2045step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2045step1 raw2045step1Labels = mixedMoment B raw2045step2 raw2045step2Labels := by
      have ha : raw2045step2 = raw2045step1 := by apply Matrix.ext; unfold raw2045step2 raw2045step1; decide +kernel
      have hl : raw2045step1Labels = labelEmbedding1 ∘ raw2045step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2045step1 raw2045step1Labels raw2045step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3425 node3425Labels := by rfl

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

theorem canonical2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2106 raw2106Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw2106 raw2106Labels = mixedMoment B raw2106step0 raw2106step0Labels := by
      have ha : raw2106step0 = (fun i j => raw2106 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2106step0 raw2106; decide +kernel
      have hl : raw2106step0Labels = raw2106Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2106 raw2106Labels permutation32 permutation4
    mixedMoment B raw2106step0 raw2106step0Labels = mixedMoment B raw2106step1 raw2106step1Labels := by
      have ha : raw2106step1 = raw2106step0 := by apply Matrix.ext; unfold raw2106step1 raw2106step0; decide +kernel
      have hl : raw2106step0Labels = labelEmbedding7 ∘ raw2106step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2106step0 raw2106step0Labels raw2106step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

theorem canonical2107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2107 raw2107Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw2107 raw2107Labels = mixedMoment B raw2107step0 raw2107step0Labels := by
      have ha : raw2107step0 = (fun i j => raw2107 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2107step0 raw2107; decide +kernel
      have hl : raw2107step0Labels = raw2107Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2107 raw2107Labels permutation32 permutation4
    _ = mixedMoment B node2488 node2488Labels := by rfl

theorem canonical2108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2108 raw2108Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw2108 raw2108Labels = mixedMoment B raw2108step0 raw2108step0Labels := by
      have ha : raw2108step0 = (fun i j => raw2108 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2108step0 raw2108; decide +kernel
      have hl : raw2108step0Labels = raw2108Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2108 raw2108Labels permutation34 permutation6
    mixedMoment B raw2108step0 raw2108step0Labels = mixedMoment B raw2108step1 raw2108step1Labels := by
      have ha : raw2108step1 = -raw2108step0 := by apply Matrix.ext; change ∀ i j, raw2108step1 i j = -(raw2108step0 i j); unfold raw2108step1 raw2108step0; decide +kernel
      have hl : raw2108step1Labels = raw2108step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2108step1 raw2108step1Labels = mixedMoment B raw2108step2 raw2108step2Labels := by
      have ha : raw2108step2 = raw2108step1 := by apply Matrix.ext; unfold raw2108step2 raw2108step1; decide +kernel
      have hl : raw2108step1Labels = labelEmbedding1 ∘ raw2108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2108step1 raw2108step1Labels raw2108step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

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

theorem canonical2364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2364 raw2364Labels = mixedMoment B node5333 node5333Labels := by
  calc
    mixedMoment B raw2364 raw2364Labels = mixedMoment B raw2364step0 raw2364step0Labels := by
      have ha : raw2364step0 = (fun i j => raw2364 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2364step0 raw2364; decide +kernel
      have hl : raw2364step0Labels = raw2364Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2364 raw2364Labels permutation152 permutation4
    mixedMoment B raw2364step0 raw2364step0Labels = mixedMoment B raw2364step1 raw2364step1Labels := by
      have ha : raw2364step1 = raw2364step0 := by apply Matrix.ext; unfold raw2364step1 raw2364step0; decide +kernel
      have hl : raw2364step0Labels = labelEmbedding7 ∘ raw2364step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2364step0 raw2364step0Labels raw2364step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5333 node5333Labels := by rfl

theorem canonical2365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2365 raw2365Labels = mixedMoment B node3668 node3668Labels := by
  calc
    mixedMoment B raw2365 raw2365Labels = mixedMoment B raw2365step0 raw2365step0Labels := by
      have ha : raw2365step0 = (fun i j => raw2365 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2365step0 raw2365; decide +kernel
      have hl : raw2365step0Labels = raw2365Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2365 raw2365Labels permutation152 permutation4
    _ = mixedMoment B node3668 node3668Labels := by rfl

theorem canonical2366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2366 raw2366Labels = mixedMoment B node3677 node3677Labels := by
  calc
    mixedMoment B raw2366 raw2366Labels = mixedMoment B raw2366step0 raw2366step0Labels := by
      have ha : raw2366step0 = (fun i j => raw2366 (permutation664 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2366step0 raw2366; decide +kernel
      have hl : raw2366step0Labels = raw2366Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2366 raw2366Labels permutation664 permutation6
    mixedMoment B raw2366step0 raw2366step0Labels = mixedMoment B raw2366step1 raw2366step1Labels := by
      have ha : raw2366step1 = raw2366step0 := by apply Matrix.ext; unfold raw2366step1 raw2366step0; decide +kernel
      have hl : raw2366step0Labels = labelEmbedding1 ∘ raw2366step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2366step0 raw2366step0Labels raw2366step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3677 node3677Labels := by rfl

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

theorem canonical2430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2430 raw2430Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw2430 raw2430Labels = mixedMoment B raw2430step0 raw2430step0Labels := by
      have ha : raw2430step0 = (fun i j => raw2430 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2430step0 raw2430; decide +kernel
      have hl : raw2430step0Labels = raw2430Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2430 raw2430Labels permutation152 permutation4
    mixedMoment B raw2430step0 raw2430step0Labels = mixedMoment B raw2430step1 raw2430step1Labels := by
      have ha : raw2430step1 = raw2430step0 := by apply Matrix.ext; unfold raw2430step1 raw2430step0; decide +kernel
      have hl : raw2430step0Labels = labelEmbedding7 ∘ raw2430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2430step0 raw2430step0Labels raw2430step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical2431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2431 raw2431Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw2431 raw2431Labels = mixedMoment B raw2431step0 raw2431step0Labels := by
      have ha : raw2431step0 = (fun i j => raw2431 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2431step0 raw2431; decide +kernel
      have hl : raw2431step0Labels = raw2431Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2431 raw2431Labels permutation152 permutation4
    _ = mixedMoment B node3719 node3719Labels := by rfl

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

theorem canonical2432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2432 raw2432Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw2432 raw2432Labels = mixedMoment B raw2432step0 raw2432step0Labels := by
      have ha : raw2432step0 = (fun i j => raw2432 (permutation686 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2432step0 raw2432; decide +kernel
      have hl : raw2432step0Labels = raw2432Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2432 raw2432Labels permutation686 permutation6
    mixedMoment B raw2432step0 raw2432step0Labels = mixedMoment B raw2432step1 raw2432step1Labels := by
      have ha : raw2432step1 = raw2432step0 := by apply Matrix.ext; unfold raw2432step1 raw2432step0; decide +kernel
      have hl : raw2432step0Labels = labelEmbedding1 ∘ raw2432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2432step0 raw2432step0Labels raw2432step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

theorem canonical2508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2508 raw2508Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw2508 raw2508Labels = mixedMoment B raw2508step0 raw2508step0Labels := by
      have ha : raw2508step0 = (fun i j => raw2508 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2508step0 raw2508; decide +kernel
      have hl : raw2508step0Labels = raw2508Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2508 raw2508Labels permutation152 permutation5
    mixedMoment B raw2508step0 raw2508step0Labels = mixedMoment B raw2508step1 raw2508step1Labels := by
      have ha : raw2508step1 = raw2508step0 := by apply Matrix.ext; unfold raw2508step1 raw2508step0; decide +kernel
      have hl : raw2508step0Labels = labelEmbedding8 ∘ raw2508step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2508step0 raw2508step0Labels raw2508step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical2509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2509 raw2509Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw2509 raw2509Labels = mixedMoment B raw2509step0 raw2509step0Labels := by
      have ha : raw2509step0 = (fun i j => raw2509 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2509step0 raw2509; decide +kernel
      have hl : raw2509step0Labels = raw2509Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2509 raw2509Labels permutation662 permutation4
    mixedMoment B raw2509step0 raw2509step0Labels = mixedMoment B raw2509step1 raw2509step1Labels := by
      have ha : raw2509step1 = -raw2509step0 := by apply Matrix.ext; change ∀ i j, raw2509step1 i j = -(raw2509step0 i j); unfold raw2509step1 raw2509step0; decide +kernel
      have hl : raw2509step1Labels = raw2509step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3964 node3964Labels := by rfl

theorem canonical2510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2510 raw2510Labels = mixedMoment B node3900 node3900Labels := by
  calc
    mixedMoment B raw2510 raw2510Labels = mixedMoment B raw2510step0 raw2510step0Labels := by
      have ha : raw2510step0 = (fun i j => raw2510 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2510step0 raw2510; decide +kernel
      have hl : raw2510step0Labels = raw2510Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2510 raw2510Labels permutation160 permutation3
    mixedMoment B raw2510step0 raw2510step0Labels = mixedMoment B raw2510step1 raw2510step1Labels := by
      have ha : raw2510step1 = -raw2510step0 := by apply Matrix.ext; change ∀ i j, raw2510step1 i j = -(raw2510step0 i j); unfold raw2510step1 raw2510step0; decide +kernel
      have hl : raw2510step1Labels = raw2510step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2510step1 raw2510step1Labels = mixedMoment B raw2510step2 raw2510step2Labels := by
      have ha : raw2510step2 = raw2510step1 := by apply Matrix.ext; unfold raw2510step2 raw2510step1; decide +kernel
      have hl : raw2510step1Labels = labelEmbedding1 ∘ raw2510step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2510step1 raw2510step1Labels raw2510step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3900 node3900Labels := by rfl

theorem canonical2520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2520 raw2520Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw2520 raw2520Labels = mixedMoment B raw2520step0 raw2520step0Labels := by
      have ha : raw2520step0 = (fun i j => raw2520 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2520step0 raw2520; decide +kernel
      have hl : raw2520step0Labels = raw2520Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2520 raw2520Labels permutation152 permutation4
    mixedMoment B raw2520step0 raw2520step0Labels = mixedMoment B raw2520step1 raw2520step1Labels := by
      have ha : raw2520step1 = raw2520step0 := by apply Matrix.ext; unfold raw2520step1 raw2520step0; decide +kernel
      have hl : raw2520step0Labels = labelEmbedding7 ∘ raw2520step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2520step0 raw2520step0Labels raw2520step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical2521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2521 raw2521Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw2521 raw2521Labels = mixedMoment B raw2521step0 raw2521step0Labels := by
      have ha : raw2521step0 = (fun i j => raw2521 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2521step0 raw2521; decide +kernel
      have hl : raw2521step0Labels = raw2521Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2521 raw2521Labels permutation152 permutation4
    _ = mixedMoment B node3849 node3849Labels := by rfl

theorem canonical2522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2522 raw2522Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw2522 raw2522Labels = mixedMoment B raw2522step0 raw2522step0Labels := by
      have ha : raw2522step0 = (fun i j => raw2522 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2522step0 raw2522; decide +kernel
      have hl : raw2522step0Labels = raw2522Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2522 raw2522Labels permutation200 permutation6
    mixedMoment B raw2522step0 raw2522step0Labels = mixedMoment B raw2522step1 raw2522step1Labels := by
      have ha : raw2522step1 = -raw2522step0 := by apply Matrix.ext; change ∀ i j, raw2522step1 i j = -(raw2522step0 i j); unfold raw2522step1 raw2522step0; decide +kernel
      have hl : raw2522step1Labels = raw2522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2522step1 raw2522step1Labels = mixedMoment B raw2522step2 raw2522step2Labels := by
      have ha : raw2522step2 = raw2522step1 := by apply Matrix.ext; unfold raw2522step2 raw2522step1; decide +kernel
      have hl : raw2522step1Labels = labelEmbedding1 ∘ raw2522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2522step1 raw2522step1Labels raw2522step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

theorem canonical2538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2538 raw2538Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw2538 raw2538Labels = mixedMoment B raw2538step0 raw2538step0Labels := by
      have ha : raw2538step0 = (fun i j => raw2538 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2538step0 raw2538; decide +kernel
      have hl : raw2538step0Labels = raw2538Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2538 raw2538Labels permutation32 permutation4
    mixedMoment B raw2538step0 raw2538step0Labels = mixedMoment B raw2538step1 raw2538step1Labels := by
      have ha : raw2538step1 = raw2538step0 := by apply Matrix.ext; unfold raw2538step1 raw2538step0; decide +kernel
      have hl : raw2538step0Labels = labelEmbedding7 ∘ raw2538step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2538step0 raw2538step0Labels raw2538step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical2539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2539 raw2539Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw2539 raw2539Labels = mixedMoment B raw2539step0 raw2539step0Labels := by
      have ha : raw2539step0 = (fun i j => raw2539 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2539step0 raw2539; decide +kernel
      have hl : raw2539step0Labels = raw2539Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2539 raw2539Labels permutation32 permutation4
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical2540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2540 raw2540Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw2540 raw2540Labels = mixedMoment B raw2540step0 raw2540step0Labels := by
      have ha : raw2540step0 = (fun i j => raw2540 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2540step0 raw2540; decide +kernel
      have hl : raw2540step0Labels = raw2540Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2540 raw2540Labels permutation38 permutation6
    mixedMoment B raw2540step0 raw2540step0Labels = mixedMoment B raw2540step1 raw2540step1Labels := by
      have ha : raw2540step1 = -raw2540step0 := by apply Matrix.ext; change ∀ i j, raw2540step1 i j = -(raw2540step0 i j); unfold raw2540step1 raw2540step0; decide +kernel
      have hl : raw2540step1Labels = raw2540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2540step1 raw2540step1Labels = mixedMoment B raw2540step2 raw2540step2Labels := by
      have ha : raw2540step2 = raw2540step1 := by apply Matrix.ext; unfold raw2540step2 raw2540step1; decide +kernel
      have hl : raw2540step1Labels = labelEmbedding1 ∘ raw2540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2540step1 raw2540step1Labels raw2540step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

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

theorem canonical32282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32282 raw32282Labels = mixedMoment B node4968 node4968Labels := by
  calc
    mixedMoment B raw32282 raw32282Labels = mixedMoment B raw32282step0 raw32282step0Labels := by
      have ha : raw32282step0 = (fun i j => raw32282 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32282step0 raw32282; decide +kernel
      have hl : raw32282step0Labels = raw32282Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32282 raw32282Labels permutation160 permutation2
    _ = mixedMoment B node4968 node4968Labels := by rfl

theorem canonical32285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32285 raw32285Labels = mixedMoment B node4961 node4961Labels := by
  calc
    mixedMoment B raw32285 raw32285Labels = mixedMoment B raw32285step0 raw32285step0Labels := by
      have ha : raw32285step0 = (fun i j => raw32285 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32285step0 raw32285; decide +kernel
      have hl : raw32285step0Labels = raw32285Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32285 raw32285Labels permutation154 permutation2
    _ = mixedMoment B node4961 node4961Labels := by rfl

theorem canonical32288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32288 raw32288Labels = mixedMoment B node4961 node4961Labels := by
  calc
    _ = mixedMoment B node4961 node4961Labels := by rfl

theorem canonical32291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32291 raw32291Labels = mixedMoment B node4960 node4960Labels := by
  calc
    _ = mixedMoment B node4960 node4960Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical279
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35752 raw35752Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw35752 raw35752Labels = mixedMoment B raw35752step0 raw35752step0Labels := by
      have ha : raw35752step0 = (fun i j => raw35752 (permutation289 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35752step0 raw35752; decide +kernel
      have hl : raw35752step0Labels = raw35752Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35752 raw35752Labels permutation289 permutation5
    mixedMoment B raw35752step0 raw35752step0Labels = mixedMoment B raw35752step1 raw35752step1Labels := by
      have ha : raw35752step1 = -raw35752step0 := by apply Matrix.ext; change ∀ i j, raw35752step1 i j = -(raw35752step0 i j); unfold raw35752step1 raw35752step0; decide +kernel
      have hl : raw35752step1Labels = raw35752step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35752step1 raw35752step1Labels = mixedMoment B raw35752step2 raw35752step2Labels := by
      have ha : raw35752step2 = raw35752step1 := by apply Matrix.ext; unfold raw35752step2 raw35752step1; decide +kernel
      have hl : raw35752step1Labels = labelEmbedding8 ∘ raw35752step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35752step1 raw35752step1Labels raw35752step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

theorem canonical35753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35753 raw35753Labels = mixedMoment B node5363 node5363Labels := by
  calc
    mixedMoment B raw35753 raw35753Labels = mixedMoment B raw35753step0 raw35753step0Labels := by
      have ha : raw35753step0 = (fun i j => raw35753 (permutation289 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35753step0 raw35753; decide +kernel
      have hl : raw35753step0Labels = raw35753Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35753 raw35753Labels permutation289 permutation5
    mixedMoment B raw35753step0 raw35753step0Labels = mixedMoment B raw35753step1 raw35753step1Labels := by
      have ha : raw35753step1 = -raw35753step0 := by apply Matrix.ext; change ∀ i j, raw35753step1 i j = -(raw35753step0 i j); unfold raw35753step1 raw35753step0; decide +kernel
      have hl : raw35753step1Labels = raw35753step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35753step1 raw35753step1Labels = mixedMoment B raw35753step2 raw35753step2Labels := by
      have ha : raw35753step2 = raw35753step1 := by apply Matrix.ext; unfold raw35753step2 raw35753step1; decide +kernel
      have hl : raw35753step1Labels = labelEmbedding8 ∘ raw35753step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35753step1 raw35753step1Labels raw35753step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5363 node5363Labels := by rfl

theorem canonical35754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35754 raw35754Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw35754 raw35754Labels = mixedMoment B raw35754step0 raw35754step0Labels := by
      have hz : ∀ j, raw35754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35754step0 = (fun i j => raw35754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35754step0 raw35754; decide +kernel
      have hl : raw35754step0Labels = raw35754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35754 raw35754Labels permutation434 hz
    mixedMoment B raw35754step0 raw35754step0Labels = mixedMoment B raw35754step1 raw35754step1Labels := by
      have ha : raw35754step1 = (fun i j => raw35754step0 (permutation62 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35754step1 raw35754step0; decide +kernel
      have hl : raw35754step1Labels = raw35754step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35754step0 raw35754step0Labels permutation62 permutation5
    mixedMoment B raw35754step1 raw35754step1Labels = mixedMoment B raw35754step2 raw35754step2Labels := by
      have ha : raw35754step2 = -raw35754step1 := by apply Matrix.ext; change ∀ i j, raw35754step2 i j = -(raw35754step1 i j); unfold raw35754step2 raw35754step1; decide +kernel
      have hl : raw35754step2Labels = raw35754step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35754step2 raw35754step2Labels = mixedMoment B raw35754step3 raw35754step3Labels := by
      have ha : raw35754step3 = raw35754step2 := by apply Matrix.ext; unfold raw35754step3 raw35754step2; decide +kernel
      have hl : raw35754step2Labels = labelEmbedding8 ∘ raw35754step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35754step2 raw35754step2Labels raw35754step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical35755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35755 raw35755Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw35755 raw35755Labels = mixedMoment B raw35755step0 raw35755step0Labels := by
      have hz : ∀ j, raw35755 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35755step0 = (fun i j => raw35755 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35755step0 raw35755; decide +kernel
      have hl : raw35755step0Labels = raw35755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35755 raw35755Labels permutation520 hz
    mixedMoment B raw35755step0 raw35755step0Labels = mixedMoment B raw35755step1 raw35755step1Labels := by
      have ha : raw35755step1 = (fun i j => raw35755step0 (permutation62 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35755step1 raw35755step0; decide +kernel
      have hl : raw35755step1Labels = raw35755step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35755step0 raw35755step0Labels permutation62 permutation5
    mixedMoment B raw35755step1 raw35755step1Labels = mixedMoment B raw35755step2 raw35755step2Labels := by
      have ha : raw35755step2 = -raw35755step1 := by apply Matrix.ext; change ∀ i j, raw35755step2 i j = -(raw35755step1 i j); unfold raw35755step2 raw35755step1; decide +kernel
      have hl : raw35755step2Labels = raw35755step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35755step2 raw35755step2Labels = mixedMoment B raw35755step3 raw35755step3Labels := by
      have ha : raw35755step3 = raw35755step2 := by apply Matrix.ext; unfold raw35755step3 raw35755step2; decide +kernel
      have hl : raw35755step2Labels = labelEmbedding8 ∘ raw35755step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35755step2 raw35755step2Labels raw35755step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical35756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35756 raw35756Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw35756 raw35756Labels = mixedMoment B raw35756step0 raw35756step0Labels := by
      have ha : raw35756step0 = (fun i j => raw35756 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35756step0 raw35756; decide +kernel
      have hl : raw35756step0Labels = raw35756Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35756 raw35756Labels permutation265 permutation3
    mixedMoment B raw35756step0 raw35756step0Labels = mixedMoment B raw35756step1 raw35756step1Labels := by
      have ha : raw35756step1 = raw35756step0 := by apply Matrix.ext; unfold raw35756step1 raw35756step0; decide +kernel
      have hl : raw35756step0Labels = labelEmbedding6 ∘ raw35756step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35756step0 raw35756step0Labels raw35756step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4679 node4679Labels := by rfl

theorem canonical35757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35757 raw35757Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw35757 raw35757Labels = mixedMoment B raw35757step0 raw35757step0Labels := by
      have hz : ∀ j, raw35757 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35757step0 = (fun i j => raw35757 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35757step0 raw35757; decide +kernel
      have hl : raw35757step0Labels = raw35757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35757 raw35757Labels permutation434 hz
    mixedMoment B raw35757step0 raw35757step0Labels = mixedMoment B raw35757step1 raw35757step1Labels := by
      have ha : raw35757step1 = (fun i j => raw35757step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35757step1 raw35757step0; decide +kernel
      have hl : raw35757step1Labels = raw35757step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35757step0 raw35757step0Labels permutation34 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

theorem canonical35758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35758 raw35758Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw35758 raw35758Labels = mixedMoment B raw35758step0 raw35758step0Labels := by
      have hz : ∀ j, raw35758 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35758step0 = (fun i j => raw35758 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35758step0 raw35758; decide +kernel
      have hl : raw35758step0Labels = raw35758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35758 raw35758Labels permutation520 hz
    mixedMoment B raw35758step0 raw35758step0Labels = mixedMoment B raw35758step1 raw35758step1Labels := by
      have ha : raw35758step1 = (fun i j => raw35758step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35758step1 raw35758step0; decide +kernel
      have hl : raw35758step1Labels = raw35758step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35758step0 raw35758step0Labels permutation34 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

theorem canonical35759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35759 raw35759Labels = mixedMoment B node4661 node4661Labels := by
  calc
    mixedMoment B raw35759 raw35759Labels = mixedMoment B raw35759step0 raw35759step0Labels := by
      have ha : raw35759step0 = (fun i j => raw35759 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35759step0 raw35759; decide +kernel
      have hl : raw35759step0Labels = raw35759Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35759 raw35759Labels permutation268 permutation3
    mixedMoment B raw35759step0 raw35759step0Labels = mixedMoment B raw35759step1 raw35759step1Labels := by
      have ha : raw35759step1 = raw35759step0 := by apply Matrix.ext; unfold raw35759step1 raw35759step0; decide +kernel
      have hl : raw35759step0Labels = labelEmbedding6 ∘ raw35759step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35759step0 raw35759step0Labels raw35759step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4661 node4661Labels := by rfl

theorem canonical35760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35760 raw35760Labels = mixedMoment B node5333 node5333Labels := by
  calc
    mixedMoment B raw35760 raw35760Labels = mixedMoment B raw35760step0 raw35760step0Labels := by
      have ha : raw35760step0 = (fun i j => raw35760 (permutation518 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35760step0 raw35760; decide +kernel
      have hl : raw35760step0Labels = raw35760Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35760 raw35760Labels permutation518 permutation3
    mixedMoment B raw35760step0 raw35760step0Labels = mixedMoment B raw35760step1 raw35760step1Labels := by
      have ha : raw35760step1 = -raw35760step0 := by apply Matrix.ext; change ∀ i j, raw35760step1 i j = -(raw35760step0 i j); unfold raw35760step1 raw35760step0; decide +kernel
      have hl : raw35760step1Labels = raw35760step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35760step1 raw35760step1Labels = mixedMoment B raw35760step2 raw35760step2Labels := by
      have ha : raw35760step2 = raw35760step1 := by apply Matrix.ext; unfold raw35760step2 raw35760step1; decide +kernel
      have hl : raw35760step1Labels = labelEmbedding6 ∘ raw35760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35760step1 raw35760step1Labels raw35760step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5333 node5333Labels := by rfl

theorem canonical35761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35761 raw35761Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw35761 raw35761Labels = mixedMoment B raw35761step0 raw35761step0Labels := by
      have hz : ∀ j, raw35761 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35761step0 = (fun i j => raw35761 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35761step0 raw35761; decide +kernel
      have hl : raw35761step0Labels = raw35761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35761 raw35761Labels permutation520 hz
    mixedMoment B raw35761step0 raw35761step0Labels = mixedMoment B raw35761step1 raw35761step1Labels := by
      have ha : raw35761step1 = (fun i j => raw35761step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35761step1 raw35761step0; decide +kernel
      have hl : raw35761step1Labels = raw35761step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35761step0 raw35761step0Labels permutation126 permutation3
    mixedMoment B raw35761step1 raw35761step1Labels = mixedMoment B raw35761step2 raw35761step2Labels := by
      have ha : raw35761step2 = -raw35761step1 := by apply Matrix.ext; change ∀ i j, raw35761step2 i j = -(raw35761step1 i j); unfold raw35761step2 raw35761step1; decide +kernel
      have hl : raw35761step2Labels = raw35761step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35761step2 raw35761step2Labels = mixedMoment B raw35761step3 raw35761step3Labels := by
      have ha : raw35761step3 = raw35761step2 := by apply Matrix.ext; unfold raw35761step3 raw35761step2; decide +kernel
      have hl : raw35761step2Labels = labelEmbedding6 ∘ raw35761step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35761step2 raw35761step2Labels raw35761step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical35762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35762 raw35762Labels = mixedMoment B node4661 node4661Labels := by
  calc
    mixedMoment B raw35762 raw35762Labels = mixedMoment B raw35762step0 raw35762step0Labels := by
      have ha : raw35762step0 = (fun i j => raw35762 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35762step0 raw35762; decide +kernel
      have hl : raw35762step0Labels = raw35762Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35762 raw35762Labels permutation266 permutation3
    mixedMoment B raw35762step0 raw35762step0Labels = mixedMoment B raw35762step1 raw35762step1Labels := by
      have ha : raw35762step1 = raw35762step0 := by apply Matrix.ext; unfold raw35762step1 raw35762step0; decide +kernel
      have hl : raw35762step0Labels = labelEmbedding6 ∘ raw35762step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35762step0 raw35762step0Labels raw35762step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4661 node4661Labels := by rfl

theorem canonical35763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35763 raw35763Labels = mixedMoment B node5333 node5333Labels := by
  calc
    mixedMoment B raw35763 raw35763Labels = mixedMoment B raw35763step0 raw35763step0Labels := by
      have ha : raw35763step0 = (fun i j => raw35763 (permutation588 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35763step0 raw35763; decide +kernel
      have hl : raw35763step0Labels = raw35763Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35763 raw35763Labels permutation588 permutation3
    mixedMoment B raw35763step0 raw35763step0Labels = mixedMoment B raw35763step1 raw35763step1Labels := by
      have ha : raw35763step1 = -raw35763step0 := by apply Matrix.ext; change ∀ i j, raw35763step1 i j = -(raw35763step0 i j); unfold raw35763step1 raw35763step0; decide +kernel
      have hl : raw35763step1Labels = raw35763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35763step1 raw35763step1Labels = mixedMoment B raw35763step2 raw35763step2Labels := by
      have ha : raw35763step2 = raw35763step1 := by apply Matrix.ext; unfold raw35763step2 raw35763step1; decide +kernel
      have hl : raw35763step1Labels = labelEmbedding6 ∘ raw35763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35763step1 raw35763step1Labels raw35763step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5333 node5333Labels := by rfl

theorem canonical35764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35764 raw35764Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw35764 raw35764Labels = mixedMoment B raw35764step0 raw35764step0Labels := by
      have hz : ∀ j, raw35764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35764step0 = (fun i j => raw35764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35764step0 raw35764; decide +kernel
      have hl : raw35764step0Labels = raw35764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35764 raw35764Labels permutation434 hz
    mixedMoment B raw35764step0 raw35764step0Labels = mixedMoment B raw35764step1 raw35764step1Labels := by
      have ha : raw35764step1 = (fun i j => raw35764step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35764step1 raw35764step0; decide +kernel
      have hl : raw35764step1Labels = raw35764step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35764step0 raw35764step0Labels permutation126 permutation3
    mixedMoment B raw35764step1 raw35764step1Labels = mixedMoment B raw35764step2 raw35764step2Labels := by
      have ha : raw35764step2 = -raw35764step1 := by apply Matrix.ext; change ∀ i j, raw35764step2 i j = -(raw35764step1 i j); unfold raw35764step2 raw35764step1; decide +kernel
      have hl : raw35764step2Labels = raw35764step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35764step2 raw35764step2Labels = mixedMoment B raw35764step3 raw35764step3Labels := by
      have ha : raw35764step3 = raw35764step2 := by apply Matrix.ext; unfold raw35764step3 raw35764step2; decide +kernel
      have hl : raw35764step2Labels = labelEmbedding6 ∘ raw35764step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35764step2 raw35764step2Labels raw35764step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical35765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35765 raw35765Labels = mixedMoment B node4660 node4660Labels := by
  calc
    mixedMoment B raw35765 raw35765Labels = mixedMoment B raw35765step0 raw35765step0Labels := by
      have ha : raw35765step0 = (fun i j => raw35765 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35765step0 raw35765; decide +kernel
      have hl : raw35765step0Labels = raw35765Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35765 raw35765Labels permutation265 permutation3
    mixedMoment B raw35765step0 raw35765step0Labels = mixedMoment B raw35765step1 raw35765step1Labels := by
      have ha : raw35765step1 = raw35765step0 := by apply Matrix.ext; unfold raw35765step1 raw35765step0; decide +kernel
      have hl : raw35765step0Labels = labelEmbedding6 ∘ raw35765step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35765step0 raw35765step0Labels raw35765step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4660 node4660Labels := by rfl

theorem canonical35766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35766 raw35766Labels = mixedMoment B node5030 node5030Labels := by
  calc
    mixedMoment B raw35766 raw35766Labels = mixedMoment B raw35766step0 raw35766step0Labels := by
      have ha : raw35766step0 = (fun i j => raw35766 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35766step0 raw35766; decide +kernel
      have hl : raw35766step0Labels = raw35766Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35766 raw35766Labels permutation663 permutation3
    mixedMoment B raw35766step0 raw35766step0Labels = mixedMoment B raw35766step1 raw35766step1Labels := by
      have ha : raw35766step1 = -raw35766step0 := by apply Matrix.ext; change ∀ i j, raw35766step1 i j = -(raw35766step0 i j); unfold raw35766step1 raw35766step0; decide +kernel
      have hl : raw35766step1Labels = raw35766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35766step1 raw35766step1Labels = mixedMoment B raw35766step2 raw35766step2Labels := by
      have ha : raw35766step2 = raw35766step1 := by apply Matrix.ext; unfold raw35766step2 raw35766step1; decide +kernel
      have hl : raw35766step1Labels = labelEmbedding6 ∘ raw35766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35766step1 raw35766step1Labels raw35766step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5030 node5030Labels := by rfl

theorem canonical35767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35767 raw35767Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw35767 raw35767Labels = mixedMoment B raw35767step0 raw35767step0Labels := by
      have hz : ∀ j, raw35767 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35767step0 = (fun i j => raw35767 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35767step0 raw35767; decide +kernel
      have hl : raw35767step0Labels = raw35767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35767 raw35767Labels permutation434 hz
    mixedMoment B raw35767step0 raw35767step0Labels = mixedMoment B raw35767step1 raw35767step1Labels := by
      have ha : raw35767step1 = (fun i j => raw35767step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35767step1 raw35767step0; decide +kernel
      have hl : raw35767step1Labels = raw35767step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35767step0 raw35767step0Labels permutation150 permutation3
    mixedMoment B raw35767step1 raw35767step1Labels = mixedMoment B raw35767step2 raw35767step2Labels := by
      have ha : raw35767step2 = -raw35767step1 := by apply Matrix.ext; change ∀ i j, raw35767step2 i j = -(raw35767step1 i j); unfold raw35767step2 raw35767step1; decide +kernel
      have hl : raw35767step2Labels = raw35767step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35767step2 raw35767step2Labels = mixedMoment B raw35767step3 raw35767step3Labels := by
      have ha : raw35767step3 = raw35767step2 := by apply Matrix.ext; unfold raw35767step3 raw35767step2; decide +kernel
      have hl : raw35767step2Labels = labelEmbedding6 ∘ raw35767step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35767step2 raw35767step2Labels raw35767step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

theorem canonical35768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35768 raw35768Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw35768 raw35768Labels = mixedMoment B raw35768step0 raw35768step0Labels := by
      have hz : ∀ j, raw35768 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35768step0 = (fun i j => raw35768 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35768step0 raw35768; decide +kernel
      have hl : raw35768step0Labels = raw35768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35768 raw35768Labels permutation520 hz
    mixedMoment B raw35768step0 raw35768step0Labels = mixedMoment B raw35768step1 raw35768step1Labels := by
      have ha : raw35768step1 = (fun i j => raw35768step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35768step1 raw35768step0; decide +kernel
      have hl : raw35768step1Labels = raw35768step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35768step0 raw35768step0Labels permutation150 permutation3
    mixedMoment B raw35768step1 raw35768step1Labels = mixedMoment B raw35768step2 raw35768step2Labels := by
      have ha : raw35768step2 = -raw35768step1 := by apply Matrix.ext; change ∀ i j, raw35768step2 i j = -(raw35768step1 i j); unfold raw35768step2 raw35768step1; decide +kernel
      have hl : raw35768step2Labels = raw35768step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35768step2 raw35768step2Labels = mixedMoment B raw35768step3 raw35768step3Labels := by
      have ha : raw35768step3 = raw35768step2 := by apply Matrix.ext; unfold raw35768step3 raw35768step2; decide +kernel
      have hl : raw35768step2Labels = labelEmbedding6 ∘ raw35768step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35768step2 raw35768step2Labels raw35768step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12531 raw12531Labels = mixedMoment B node5433 node5433Labels := by
  calc
    _ = mixedMoment B node5433 node5433Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12557 raw12557Labels = mixedMoment B node5148 node5148Labels := by
  calc
    _ = mixedMoment B node5148 node5148Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4660 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4660 node4660Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1786 node1786Labels + mixedMoment B node1982 node1982Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1536 singletonSmall4660
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4660) = raw1536Labels := by decide +kernel
  rw [hl, canonical1536 B hB] at h
  have hc0 : mixedMoment B raw1536 (Fin.cases (0 : Fin 2) singletonSmall4660) =
      mixedMoment B node1786 node1786Labels := by
    have ha : raw1536 = raw1537 := by apply Matrix.ext; unfold raw1536 raw1537; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4660 = raw1537Labels := by decide +kernel
    rw [ha, hj, canonical1537 B hB]
  have hc1 : mixedMoment B raw1536 (Fin.cases (1 : Fin 2) singletonSmall4660) =
      mixedMoment B node1982 node1982Labels := by
    have ha : raw1536 = raw1538 := by apply Matrix.ext; unfold raw1536 raw1538; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4660 = raw1538Labels := by decide +kernel
    rw [ha, hj, canonical1538 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4661 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4661 node4661Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1787 node1787Labels + mixedMoment B node1983 node1983Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1539 singletonSmall4661
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4661) = raw1539Labels := by decide +kernel
  rw [hl, canonical1539 B hB] at h
  have hc0 : mixedMoment B raw1539 (Fin.cases (0 : Fin 2) singletonSmall4661) =
      mixedMoment B node1787 node1787Labels := by
    have ha : raw1539 = raw1540 := by apply Matrix.ext; unfold raw1539 raw1540; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4661 = raw1540Labels := by decide +kernel
    rw [ha, hj, canonical1540 B hB]
  have hc1 : mixedMoment B raw1539 (Fin.cases (1 : Fin 2) singletonSmall4661) =
      mixedMoment B node1983 node1983Labels := by
    have ha : raw1539 = raw1541 := by apply Matrix.ext; unfold raw1539 raw1541; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4661 = raw1541Labels := by decide +kernel
    rw [ha, hj, canonical1541 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4679 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4679 node4679Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1805 node1805Labels + mixedMoment B node2150 node2150Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1560 singletonSmall4679
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4679) = raw1560Labels := by decide +kernel
  rw [hl, canonical1560 B hB] at h
  have hc0 : mixedMoment B raw1560 (Fin.cases (0 : Fin 2) singletonSmall4679) =
      mixedMoment B node1805 node1805Labels := by
    have ha : raw1560 = raw1561 := by apply Matrix.ext; unfold raw1560 raw1561; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4679 = raw1561Labels := by decide +kernel
    rw [ha, hj, canonical1561 B hB]
  have hc1 : mixedMoment B raw1560 (Fin.cases (1 : Fin 2) singletonSmall4679) =
      mixedMoment B node2150 node2150Labels := by
    have ha : raw1560 = raw1562 := by apply Matrix.ext; unfold raw1560 raw1562; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4679 = raw1562Labels := by decide +kernel
    rw [ha, hj, canonical1562 B hB]
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

theorem singleton4826 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4826 node4826Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2046 node2046Labels + mixedMoment B node2077 node2077Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1752 singletonSmall4826
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4826) = raw1752Labels := by decide +kernel
  rw [hl, canonical1752 B hB] at h
  have hc0 : mixedMoment B raw1752 (Fin.cases (0 : Fin 2) singletonSmall4826) =
      mixedMoment B node2046 node2046Labels := by
    have ha : raw1752 = raw1753 := by apply Matrix.ext; unfold raw1752 raw1753; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4826 = raw1753Labels := by decide +kernel
    rw [ha, hj, canonical1753 B hB]
  have hc1 : mixedMoment B raw1752 (Fin.cases (1 : Fin 2) singletonSmall4826) =
      mixedMoment B node2077 node2077Labels := by
    have ha : raw1752 = raw1754 := by apply Matrix.ext; unfold raw1752 raw1754; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4826 = raw1754Labels := by decide +kernel
    rw [ha, hj, canonical1754 B hB]
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

theorem singleton4968 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4968 node4968Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2809 node2809Labels + mixedMoment B node3587 node3587Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1944 singletonSmall4968
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4968) = raw1944Labels := by decide +kernel
  rw [hl, canonical1944 B hB] at h
  have hc0 : mixedMoment B raw1944 (Fin.cases (0 : Fin 2) singletonSmall4968) =
      mixedMoment B node2809 node2809Labels := by
    have ha : raw1944 = raw1945 := by apply Matrix.ext; unfold raw1944 raw1945; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4968 = raw1945Labels := by decide +kernel
    rw [ha, hj, canonical1945 B hB]
  have hc1 : mixedMoment B raw1944 (Fin.cases (1 : Fin 2) singletonSmall4968) =
      mixedMoment B node3587 node3587Labels := by
    have ha : raw1944 = raw1946 := by apply Matrix.ext; unfold raw1944 raw1946; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4968 = raw1946Labels := by decide +kernel
    rw [ha, hj, canonical1946 B hB]
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

theorem singleton5030 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5030 node5030Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2419 node2419Labels + mixedMoment B node3425 node3425Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2043 singletonSmall5030
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5030) = raw2043Labels := by decide +kernel
  rw [hl, canonical2043 B hB] at h
  have hc0 : mixedMoment B raw2043 (Fin.cases (0 : Fin 2) singletonSmall5030) =
      mixedMoment B node2419 node2419Labels := by
    have ha : raw2043 = raw2044 := by apply Matrix.ext; unfold raw2043 raw2044; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5030 = raw2044Labels := by decide +kernel
    rw [ha, hj, canonical2044 B hB]
  have hc1 : mixedMoment B raw2043 (Fin.cases (1 : Fin 2) singletonSmall5030) =
      mixedMoment B node3425 node3425Labels := by
    have ha : raw2043 = raw2045 := by apply Matrix.ext; unfold raw2043 raw2045; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5030 = raw2045Labels := by decide +kernel
    rw [ha, hj, canonical2045 B hB]
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

theorem singleton5080 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5080 node5080Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2488 node2488Labels + mixedMoment B node3478 node3478Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2106 singletonSmall5080
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5080) = raw2106Labels := by decide +kernel
  rw [hl, canonical2106 B hB] at h
  have hc0 : mixedMoment B raw2106 (Fin.cases (0 : Fin 2) singletonSmall5080) =
      mixedMoment B node2488 node2488Labels := by
    have ha : raw2106 = raw2107 := by apply Matrix.ext; unfold raw2106 raw2107; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5080 = raw2107Labels := by decide +kernel
    rw [ha, hj, canonical2107 B hB]
  have hc1 : mixedMoment B raw2106 (Fin.cases (1 : Fin 2) singletonSmall5080) =
      mixedMoment B node3478 node3478Labels := by
    have ha : raw2106 = raw2108 := by apply Matrix.ext; unfold raw2106 raw2108; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5080 = raw2108Labels := by decide +kernel
    rw [ha, hj, canonical2108 B hB]
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

theorem singleton5333 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5333 node5333Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3668 node3668Labels + mixedMoment B node3677 node3677Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2364 singletonSmall5333
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5333) = raw2364Labels := by decide +kernel
  rw [hl, canonical2364 B hB] at h
  have hc0 : mixedMoment B raw2364 (Fin.cases (0 : Fin 2) singletonSmall5333) =
      mixedMoment B node3668 node3668Labels := by
    have ha : raw2364 = raw2365 := by apply Matrix.ext; unfold raw2364 raw2365; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5333 = raw2365Labels := by decide +kernel
    rw [ha, hj, canonical2365 B hB]
  have hc1 : mixedMoment B raw2364 (Fin.cases (1 : Fin 2) singletonSmall5333) =
      mixedMoment B node3677 node3677Labels := by
    have ha : raw2364 = raw2366 := by apply Matrix.ext; unfold raw2364 raw2366; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5333 = raw2366Labels := by decide +kernel
    rw [ha, hj, canonical2366 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5378 node5378Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3719 node3719Labels + mixedMoment B node3795 node3795Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2430 singletonSmall5378
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5378) = raw2430Labels := by decide +kernel
  rw [hl, canonical2430 B hB] at h
  have hc0 : mixedMoment B raw2430 (Fin.cases (0 : Fin 2) singletonSmall5378) =
      mixedMoment B node3719 node3719Labels := by
    have ha : raw2430 = raw2431 := by apply Matrix.ext; unfold raw2430 raw2431; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5378 = raw2431Labels := by decide +kernel
    rw [ha, hj, canonical2431 B hB]
  have hc1 : mixedMoment B raw2430 (Fin.cases (1 : Fin 2) singletonSmall5378) =
      mixedMoment B node3795 node3795Labels := by
    have ha : raw2430 = raw2432 := by apply Matrix.ext; unfold raw2430 raw2432; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5378 = raw2432Labels := by decide +kernel
    rw [ha, hj, canonical2432 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5422 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5422 node5422Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3964 node3964Labels + mixedMoment B node3900 node3900Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2508 singletonSmall5422
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5422) = raw2508Labels := by decide +kernel
  rw [hl, canonical2508 B hB] at h
  have hc0 : mixedMoment B raw2508 (Fin.cases (0 : Fin 2) singletonSmall5422) =
      mixedMoment B node3964 node3964Labels := by
    have ha : raw2508 = raw2509 := by apply Matrix.ext; unfold raw2508 raw2509; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5422 = raw2509Labels := by decide +kernel
    rw [ha, hj, canonical2509 B hB]
  have hc1 : mixedMoment B raw2508 (Fin.cases (1 : Fin 2) singletonSmall5422) =
      mixedMoment B node3900 node3900Labels := by
    have ha : raw2508 = raw2510 := by apply Matrix.ext; unfold raw2508 raw2510; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5422 = raw2510Labels := by decide +kernel
    rw [ha, hj, canonical2510 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5431 node5431Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3849 node3849Labels + mixedMoment B node3875 node3875Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2520 singletonSmall5431
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5431) = raw2520Labels := by decide +kernel
  rw [hl, canonical2520 B hB] at h
  have hc0 : mixedMoment B raw2520 (Fin.cases (0 : Fin 2) singletonSmall5431) =
      mixedMoment B node3849 node3849Labels := by
    have ha : raw2520 = raw2521 := by apply Matrix.ext; unfold raw2520 raw2521; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5431 = raw2521Labels := by decide +kernel
    rw [ha, hj, canonical2521 B hB]
  have hc1 : mixedMoment B raw2520 (Fin.cases (1 : Fin 2) singletonSmall5431) =
      mixedMoment B node3875 node3875Labels := by
    have ha : raw2520 = raw2522 := by apply Matrix.ext; unfold raw2520 raw2522; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5431 = raw2522Labels := by decide +kernel
    rw [ha, hj, canonical2522 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5438 node5438Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3857 node3857Labels + mixedMoment B node3876 node3876Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2538 singletonSmall5438
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5438) = raw2538Labels := by decide +kernel
  rw [hl, canonical2538 B hB] at h
  have hc0 : mixedMoment B raw2538 (Fin.cases (0 : Fin 2) singletonSmall5438) =
      mixedMoment B node3857 node3857Labels := by
    have ha : raw2538 = raw2539 := by apply Matrix.ext; unfold raw2538 raw2539; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5438 = raw2539Labels := by decide +kernel
    rw [ha, hj, canonical2539 B hB]
  have hc1 : mixedMoment B raw2538 (Fin.cases (1 : Fin 2) singletonSmall5438) =
      mixedMoment B node3876 node3876Labels := by
    have ha : raw2538 = raw2540 := by apply Matrix.ext; unfold raw2538 raw2540; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5438 = raw2540Labels := by decide +kernel
    rw [ha, hj, canonical2540 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1786 node1786Labels = Sparse.eval nodeValue1786 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1786) = mixedMoment B node1786 node1786Labels := rfl
  simpa [nodeValue1786, Sparse.eval] using hc.symm

theorem sound1787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1787 node1787Labels = Sparse.eval nodeValue1787 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1787) = mixedMoment B node1787 node1787Labels := rfl
  simpa [nodeValue1787, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1805 node1805Labels = Sparse.eval nodeValue1805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1805) = mixedMoment B node1805 node1805Labels := rfl
  simpa [nodeValue1805, Sparse.eval] using hc.symm

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

theorem sound1982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1982 node1982Labels = Sparse.eval nodeValue1982 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1982) = mixedMoment B node1982 node1982Labels := rfl
  simpa [nodeValue1982, Sparse.eval] using hc.symm

theorem sound1983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1983 node1983Labels = Sparse.eval nodeValue1983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1983) = mixedMoment B node1983 node1983Labels := rfl
  simpa [nodeValue1983, Sparse.eval] using hc.symm

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

theorem sound2046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2046 node2046Labels = Sparse.eval nodeValue2046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2046) = mixedMoment B node2046 node2046Labels := rfl
  simpa [nodeValue2046, Sparse.eval] using hc.symm

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

theorem sound2077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2077 node2077Labels = Sparse.eval nodeValue2077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2077) = mixedMoment B node2077 node2077Labels := rfl
  simpa [nodeValue2077, Sparse.eval] using hc.symm

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

theorem sound2150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2150 node2150Labels = Sparse.eval nodeValue2150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2150) = mixedMoment B node2150 node2150Labels := rfl
  simpa [nodeValue2150, Sparse.eval] using hc.symm

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

theorem sound2419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2419 node2419Labels = Sparse.eval nodeValue2419 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2419) = mixedMoment B node2419 node2419Labels := rfl
  simpa [nodeValue2419, Sparse.eval] using hc.symm

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

theorem sound2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2488 node2488Labels = Sparse.eval nodeValue2488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2488) = mixedMoment B node2488 node2488Labels := rfl
  simpa [nodeValue2488, Sparse.eval] using hc.symm

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

theorem sound2809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2809 node2809Labels = Sparse.eval nodeValue2809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2809) = mixedMoment B node2809 node2809Labels := rfl
  simpa [nodeValue2809, Sparse.eval] using hc.symm

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

theorem sound3425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3425 node3425Labels = Sparse.eval nodeValue3425 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3425) = mixedMoment B node3425 node3425Labels := rfl
  simpa [nodeValue3425, Sparse.eval] using hc.symm

theorem sound3426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3426 node3426Labels = Sparse.eval nodeValue3426 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3426) = mixedMoment B node3426 node3426Labels := rfl
  simpa [nodeValue3426, Sparse.eval] using hc.symm

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

theorem sound3478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3478 node3478Labels = Sparse.eval nodeValue3478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3478) = mixedMoment B node3478 node3478Labels := rfl
  simpa [nodeValue3478, Sparse.eval] using hc.symm

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

theorem sound3587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3587 node3587Labels = Sparse.eval nodeValue3587 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3587) = mixedMoment B node3587 node3587Labels := rfl
  simpa [nodeValue3587, Sparse.eval] using hc.symm

theorem sound3589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3589 node3589Labels = Sparse.eval nodeValue3589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3589) = mixedMoment B node3589 node3589Labels := rfl
  simpa [nodeValue3589, Sparse.eval] using hc.symm

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

theorem sound3668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3668 node3668Labels = Sparse.eval nodeValue3668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3668) = mixedMoment B node3668 node3668Labels := rfl
  simpa [nodeValue3668, Sparse.eval] using hc.symm

theorem sound3677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3677 node3677Labels = Sparse.eval nodeValue3677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3677) = mixedMoment B node3677 node3677Labels := rfl
  simpa [nodeValue3677, Sparse.eval] using hc.symm

theorem sound3693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3693 node3693Labels = Sparse.eval nodeValue3693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3693) = mixedMoment B node3693 node3693Labels := rfl
  simpa [nodeValue3693, Sparse.eval] using hc.symm

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

theorem sound3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3719 node3719Labels = Sparse.eval nodeValue3719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3719) = mixedMoment B node3719 node3719Labels := rfl
  simpa [nodeValue3719, Sparse.eval] using hc.symm

theorem sound3751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3751 node3751Labels = Sparse.eval nodeValue3751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3751) = mixedMoment B node3751 node3751Labels := rfl
  simpa [nodeValue3751, Sparse.eval] using hc.symm

theorem sound3770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3770 node3770Labels = Sparse.eval nodeValue3770 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3770) = mixedMoment B node3770 node3770Labels := rfl
  simpa [nodeValue3770, Sparse.eval] using hc.symm

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

theorem sound3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3795 node3795Labels = Sparse.eval nodeValue3795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3795) = mixedMoment B node3795 node3795Labels := rfl
  simpa [nodeValue3795, Sparse.eval] using hc.symm

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

theorem sound3849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3849 node3849Labels = Sparse.eval nodeValue3849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3849) = mixedMoment B node3849 node3849Labels := rfl
  simpa [nodeValue3849, Sparse.eval] using hc.symm

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

theorem sound3875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3875 node3875Labels = Sparse.eval nodeValue3875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3875) = mixedMoment B node3875 node3875Labels := rfl
  simpa [nodeValue3875, Sparse.eval] using hc.symm

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

theorem sound3900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3900 node3900Labels = Sparse.eval nodeValue3900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3900) = mixedMoment B node3900 node3900Labels := rfl
  simpa [nodeValue3900, Sparse.eval] using hc.symm

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

theorem sound3964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3964 node3964Labels = Sparse.eval nodeValue3964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3964) = mixedMoment B node3964 node3964Labels := rfl
  simpa [nodeValue3964, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4660 node4660Labels = Sparse.eval nodeValue4660 (mixedVector B) := by
  have h := singleton4660 B _hB
  rw [sound1786 B _hB _hF, sound1982 B _hB _hF] at h
  norm_num [nodeValue4660, nodeValue1786, nodeValue1982, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4661 node4661Labels = Sparse.eval nodeValue4661 (mixedVector B) := by
  have h := singleton4661 B _hB
  rw [sound1787 B _hB _hF, sound1983 B _hB _hF] at h
  norm_num [nodeValue4661, nodeValue1787, nodeValue1983, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4679 node4679Labels = Sparse.eval nodeValue4679 (mixedVector B) := by
  have h := singleton4679 B _hB
  rw [sound1805 B _hB _hF, sound2150 B _hB _hF] at h
  norm_num [nodeValue4679, nodeValue1805, nodeValue2150, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4826 node4826Labels = Sparse.eval nodeValue4826 (mixedVector B) := by
  have h := singleton4826 B _hB
  rw [sound2046 B _hB _hF, sound2077 B _hB _hF] at h
  norm_num [nodeValue4826, nodeValue2046, nodeValue2077, Sparse.eval] at h ⊢
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

theorem sound4968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4968 node4968Labels = Sparse.eval nodeValue4968 (mixedVector B) := by
  have h := singleton4968 B _hB
  rw [sound2809 B _hB _hF, sound3587 B _hB _hF] at h
  norm_num [nodeValue4968, nodeValue2809, nodeValue3587, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5030 node5030Labels = Sparse.eval nodeValue5030 (mixedVector B) := by
  have h := singleton5030 B _hB
  rw [sound2419 B _hB _hF, sound3425 B _hB _hF] at h
  norm_num [nodeValue5030, nodeValue2419, nodeValue3425, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5080 node5080Labels = Sparse.eval nodeValue5080 (mixedVector B) := by
  have h := singleton5080 B _hB
  rw [sound2488 B _hB _hF, sound3478 B _hB _hF] at h
  norm_num [nodeValue5080, nodeValue2488, nodeValue3478, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5148 node5148Labels = 0 := by
  exact mixedMoment_alpha B hF node5148 node5148Labels 1 permutation152
    (by decide +kernel)

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

theorem sound5148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5148 node5148Labels = Sparse.eval nodeValue5148 (mixedVector B) := by
  simpa only [nodeValue5148, Sparse.eval_nil] using zero5148 B _hB _hF

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

theorem sound5333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5333 node5333Labels = Sparse.eval nodeValue5333 (mixedVector B) := by
  have h := singleton5333 B _hB
  rw [sound3668 B _hB _hF, sound3677 B _hB _hF] at h
  norm_num [nodeValue5333, nodeValue3668, nodeValue3677, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5355 node5355Labels = Sparse.eval nodeValue5355 (mixedVector B) := by
  have h := singleton5355 B _hB
  rw [sound3693 B _hB _hF, sound3770 B _hB _hF] at h
  norm_num [nodeValue5355, nodeValue3693, nodeValue3770, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5378 node5378Labels = Sparse.eval nodeValue5378 (mixedVector B) := by
  have h := singleton5378 B _hB
  rw [sound3719 B _hB _hF, sound3795 B _hB _hF] at h
  norm_num [nodeValue5378, nodeValue3719, nodeValue3795, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5422 node5422Labels = Sparse.eval nodeValue5422 (mixedVector B) := by
  have h := singleton5422 B _hB
  rw [sound3900 B _hB _hF, sound3964 B _hB _hF] at h
  norm_num [nodeValue5422, nodeValue3900, nodeValue3964, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5431 node5431Labels = Sparse.eval nodeValue5431 (mixedVector B) := by
  have h := singleton5431 B _hB
  rw [sound3849 B _hB _hF, sound3875 B _hB _hF] at h
  norm_num [nodeValue5431, nodeValue3849, nodeValue3875, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5438 node5438Labels = Sparse.eval nodeValue5438 (mixedVector B) := by
  have h := singleton5438 B _hB
  rw [sound3857 B _hB _hF, sound3876 B _hB _hF] at h
  norm_num [nodeValue5438, nodeValue3857, nodeValue3876, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources80
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2582 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2582 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2582 + difference 0 1) (sourceB2582 + difference 1 0) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA2582 + difference 0 1) (sourceB2582 + difference 1 0) sourceC2582) = raw35752 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35752; decide +kernel
    rw [ha]
    exact (canonical35752 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2582 + difference 0 2) (sourceB2582 + difference 2 0) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5363) := by
    have ha : (tripleCharges (sourceA2582 + difference 0 2) (sourceB2582 + difference 2 0) sourceC2582) = raw35753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35753; decide +kernel
    rw [ha]
    exact (canonical35753 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2582 + difference 0 3) (sourceB2582 + difference 3 0) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA2582 + difference 0 3) (sourceB2582 + difference 3 0) sourceC2582) = raw35754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35754; decide +kernel
    rw [ha]
    exact (canonical35754 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2582 + difference 0 4) (sourceB2582 + difference 4 0) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA2582 + difference 0 4) (sourceB2582 + difference 4 0) sourceC2582) = raw35755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35755; decide +kernel
    rw [ha]
    exact (canonical35755 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2582 + difference 0 5) (sourceB2582 + difference 5 0) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA2582 + difference 0 5) (sourceB2582 + difference 5 0) sourceC2582) = raw18359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw18359; decide +kernel
    rw [ha]
    exact (canonical18359 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2582 + difference 1 0) (sourceB2582 + difference 0 1) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA2582 + difference 1 0) (sourceB2582 + difference 0 1) sourceC2582) = raw12557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw12557; decide +kernel
    rw [ha]
    exact (canonical12557 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2582 + difference 1 2) (sourceB2582 + difference 2 1) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA2582 + difference 1 2) (sourceB2582 + difference 2 1) sourceC2582) = raw18378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw18378; decide +kernel
    rw [ha]
    exact (canonical18378 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2582 + difference 1 3) (sourceB2582 + difference 3 1) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2582 + difference 1 3) (sourceB2582 + difference 3 1) sourceC2582) = raw18379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw18379; decide +kernel
    rw [ha]
    exact (canonical18379 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2582 + difference 1 4) (sourceB2582 + difference 4 1) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2582 + difference 1 4) (sourceB2582 + difference 4 1) sourceC2582) = raw18380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw18380; decide +kernel
    rw [ha]
    exact (canonical18380 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2582 + difference 1 5) (sourceB2582 + difference 5 1) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2582 + difference 1 5) (sourceB2582 + difference 5 1) sourceC2582) = raw12531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw12531; decide +kernel
    rw [ha]
    exact (canonical12531 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2582 + difference 2 0) (sourceB2582 + difference 0 2) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4968) := by
    have ha : (tripleCharges (sourceA2582 + difference 2 0) (sourceB2582 + difference 0 2) sourceC2582) = raw32282 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw32282; decide +kernel
    rw [ha]
    exact (canonical32282 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2582 + difference 2 1) (sourceB2582 + difference 1 2) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2582 + difference 2 1) (sourceB2582 + difference 1 2) sourceC2582) = raw35756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35756; decide +kernel
    rw [ha]
    exact (canonical35756 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2582 + difference 2 3) (sourceB2582 + difference 3 2) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2582 + difference 2 3) (sourceB2582 + difference 3 2) sourceC2582) = raw35757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35757; decide +kernel
    rw [ha]
    exact (canonical35757 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2582 + difference 2 4) (sourceB2582 + difference 4 2) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2582 + difference 2 4) (sourceB2582 + difference 4 2) sourceC2582) = raw35758 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35758; decide +kernel
    rw [ha]
    exact (canonical35758 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2582 + difference 2 5) (sourceB2582 + difference 5 2) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5386) := by
    have ha : (tripleCharges (sourceA2582 + difference 2 5) (sourceB2582 + difference 5 2) sourceC2582) = raw18365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw18365; decide +kernel
    rw [ha]
    exact (canonical18365 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2582 + difference 3 0) (sourceB2582 + difference 0 3) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4961) := by
    have ha : (tripleCharges (sourceA2582 + difference 3 0) (sourceB2582 + difference 0 3) sourceC2582) = raw32285 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw32285; decide +kernel
    rw [ha]
    exact (canonical32285 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2582 + difference 3 1) (sourceB2582 + difference 1 3) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4661) := by
    have ha : (tripleCharges (sourceA2582 + difference 3 1) (sourceB2582 + difference 1 3) sourceC2582) = raw35759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35759; decide +kernel
    rw [ha]
    exact (canonical35759 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2582 + difference 3 2) (sourceB2582 + difference 2 3) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5333) := by
    have ha : (tripleCharges (sourceA2582 + difference 3 2) (sourceB2582 + difference 2 3) sourceC2582) = raw35760 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35760; decide +kernel
    rw [ha]
    exact (canonical35760 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2582 + difference 3 4) (sourceB2582 + difference 4 3) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2582 + difference 3 4) (sourceB2582 + difference 4 3) sourceC2582) = raw35761 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35761; decide +kernel
    rw [ha]
    exact (canonical35761 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2582 + difference 3 5) (sourceB2582 + difference 5 3) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2582 + difference 3 5) (sourceB2582 + difference 5 3) sourceC2582) = raw18369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw18369; decide +kernel
    rw [ha]
    exact (canonical18369 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2582 + difference 4 0) (sourceB2582 + difference 0 4) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4961) := by
    have ha : (tripleCharges (sourceA2582 + difference 4 0) (sourceB2582 + difference 0 4) sourceC2582) = raw32288 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw32288; decide +kernel
    rw [ha]
    exact (canonical32288 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2582 + difference 4 1) (sourceB2582 + difference 1 4) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4661) := by
    have ha : (tripleCharges (sourceA2582 + difference 4 1) (sourceB2582 + difference 1 4) sourceC2582) = raw35762 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35762; decide +kernel
    rw [ha]
    exact (canonical35762 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2582 + difference 4 2) (sourceB2582 + difference 2 4) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5333) := by
    have ha : (tripleCharges (sourceA2582 + difference 4 2) (sourceB2582 + difference 2 4) sourceC2582) = raw35763 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35763; decide +kernel
    rw [ha]
    exact (canonical35763 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2582 + difference 4 3) (sourceB2582 + difference 3 4) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2582 + difference 4 3) (sourceB2582 + difference 3 4) sourceC2582) = raw35764 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35764; decide +kernel
    rw [ha]
    exact (canonical35764 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2582 + difference 4 5) (sourceB2582 + difference 5 4) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2582 + difference 4 5) (sourceB2582 + difference 5 4) sourceC2582) = raw18373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw18373; decide +kernel
    rw [ha]
    exact (canonical18373 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2582 + difference 5 0) (sourceB2582 + difference 0 5) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4960) := by
    have ha : (tripleCharges (sourceA2582 + difference 5 0) (sourceB2582 + difference 0 5) sourceC2582) = raw32291 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw32291; decide +kernel
    rw [ha]
    exact (canonical32291 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2582 + difference 5 1) (sourceB2582 + difference 1 5) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4660) := by
    have ha : (tripleCharges (sourceA2582 + difference 5 1) (sourceB2582 + difference 1 5) sourceC2582) = raw35765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35765; decide +kernel
    rw [ha]
    exact (canonical35765 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2582 + difference 5 2) (sourceB2582 + difference 2 5) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5030) := by
    have ha : (tripleCharges (sourceA2582 + difference 5 2) (sourceB2582 + difference 2 5) sourceC2582) = raw35766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35766; decide +kernel
    rw [ha]
    exact (canonical35766 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2582 + difference 5 3) (sourceB2582 + difference 3 5) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2582 + difference 5 3) (sourceB2582 + difference 3 5) sourceC2582) = raw35767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35767; decide +kernel
    rw [ha]
    exact (canonical35767 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2582 + difference 5 4) (sourceB2582 + difference 4 5) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2582 + difference 5 4) (sourceB2582 + difference 4 5) sourceC2582) = raw35768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35768; decide +kernel
    rw [ha]
    exact (canonical35768 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2582 sourceB2582 sourceC2582
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2582, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2066 : Integer.Sparse.reindex keyMap MixedData.row2066 = numericRow2066 := by decide +kernel

theorem numericCheck2066 (x : Master → ℝ) : Integer.Sparse.eval numericRow2066 x =
    (51840 : ℝ) * reducedSource2066 x := by
  norm_num [numericRow2066, reducedSource2066, Integer.Sparse.eval, Sparse.eval, nodeValue4660, nodeValue4661, nodeValue4679, nodeValue4826, nodeValue4960, nodeValue4961, nodeValue4968, nodeValue5030, nodeValue5080, nodeValue5148, nodeValue5333, nodeValue5355, nodeValue5363, nodeValue5378, nodeValue5386, nodeValue5388, nodeValue5422, nodeValue5431, nodeValue5433, nodeValue5434, nodeValue5438]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2066 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2066 (mixedVector B) = 0 := by
  have h4660 : mixedVector B (Sum.inr 4660) = Sparse.eval nodeValue4660 (mixedVector B) := by
    change mixedMoment B node4660 node4660Labels = _
    exact sound4660 B hB hF
  have h4661 : mixedVector B (Sum.inr 4661) = Sparse.eval nodeValue4661 (mixedVector B) := by
    change mixedMoment B node4661 node4661Labels = _
    exact sound4661 B hB hF
  have h4679 : mixedVector B (Sum.inr 4679) = Sparse.eval nodeValue4679 (mixedVector B) := by
    change mixedMoment B node4679 node4679Labels = _
    exact sound4679 B hB hF
  have h4826 : mixedVector B (Sum.inr 4826) = Sparse.eval nodeValue4826 (mixedVector B) := by
    change mixedMoment B node4826 node4826Labels = _
    exact sound4826 B hB hF
  have h4960 : mixedVector B (Sum.inr 4960) = Sparse.eval nodeValue4960 (mixedVector B) := by
    change mixedMoment B node4960 node4960Labels = _
    exact sound4960 B hB hF
  have h4961 : mixedVector B (Sum.inr 4961) = Sparse.eval nodeValue4961 (mixedVector B) := by
    change mixedMoment B node4961 node4961Labels = _
    exact sound4961 B hB hF
  have h4968 : mixedVector B (Sum.inr 4968) = Sparse.eval nodeValue4968 (mixedVector B) := by
    change mixedMoment B node4968 node4968Labels = _
    exact sound4968 B hB hF
  have h5030 : mixedVector B (Sum.inr 5030) = Sparse.eval nodeValue5030 (mixedVector B) := by
    change mixedMoment B node5030 node5030Labels = _
    exact sound5030 B hB hF
  have h5080 : mixedVector B (Sum.inr 5080) = Sparse.eval nodeValue5080 (mixedVector B) := by
    change mixedMoment B node5080 node5080Labels = _
    exact sound5080 B hB hF
  have h5148 : mixedVector B (Sum.inr 5148) = Sparse.eval nodeValue5148 (mixedVector B) := by
    change mixedMoment B node5148 node5148Labels = _
    exact sound5148 B hB hF
  have h5333 : mixedVector B (Sum.inr 5333) = Sparse.eval nodeValue5333 (mixedVector B) := by
    change mixedMoment B node5333 node5333Labels = _
    exact sound5333 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5363 : mixedVector B (Sum.inr 5363) = Sparse.eval nodeValue5363 (mixedVector B) := by
    change mixedMoment B node5363 node5363Labels = _
    exact sound5363 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5386 : mixedVector B (Sum.inr 5386) = Sparse.eval nodeValue5386 (mixedVector B) := by
    change mixedMoment B node5386 node5386Labels = _
    exact sound5386_e B hB hF
  have h5388 : mixedVector B (Sum.inr 5388) = Sparse.eval nodeValue5388 (mixedVector B) := by
    change mixedMoment B node5388 node5388Labels = _
    exact sound5388_e B hB hF
  have h5422 : mixedVector B (Sum.inr 5422) = Sparse.eval nodeValue5422 (mixedVector B) := by
    change mixedMoment B node5422 node5422Labels = _
    exact sound5422 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  simpa only [sourceForm2582, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4660, h4661, h4679, h4826, h4960, h4961, h4968, h5030, h5080, h5148, h5333, h5355, h5363, h5378, h5386, h5388, h5422, h5431, h5433, h5434, h5438, reducedSource2066] using sourceEq2582 B hB

theorem rowSound2066_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2066 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2066, numericCheck2066, reducedZero2066 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e_oai
