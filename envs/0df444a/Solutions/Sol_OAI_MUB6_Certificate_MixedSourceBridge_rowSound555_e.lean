-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T02:08:05.439466+00:00
-- url     : https://prove2.me/submissions/d6368069-b697-41bf-9257-9032415cef75

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E114
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3206_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3210_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3227_e

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

theorem canonical140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw140 raw140Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw140 raw140Labels = mixedMoment B raw140step0 raw140step0Labels := by
      have ha : raw140step0 = (fun i j => raw140 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw140step0 raw140; decide +kernel
      have hl : raw140step0Labels = raw140Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw140 raw140Labels permutation8 permutation5
    mixedMoment B raw140step0 raw140step0Labels = mixedMoment B raw140step1 raw140step1Labels := by
      have ha : raw140step1 = raw140step0 := by apply Matrix.ext; unfold raw140step1 raw140step0; decide +kernel
      have hl : raw140step0Labels = labelEmbedding1 ∘ raw140step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw140step0 raw140step0Labels raw140step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1419 node1419Labels := by rfl

theorem canonical141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw141 raw141Labels = mixedMoment B node98 node98Labels := by
  calc
    mixedMoment B raw141 raw141Labels = mixedMoment B raw141step0 raw141step0Labels := by
      have ha : raw141step0 = (fun i j => raw141 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw141step0 raw141; decide +kernel
      have hl : raw141step0Labels = raw141Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw141 raw141Labels permutation9 permutation4
    _ = mixedMoment B node98 node98Labels := by rfl

theorem canonical154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw154 raw154Labels = mixedMoment B node1442 node1442Labels := by
  calc
    mixedMoment B raw154 raw154Labels = mixedMoment B raw154step0 raw154step0Labels := by
      have ha : raw154step0 = (fun i j => raw154 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw154step0 raw154; decide +kernel
      have hl : raw154step0Labels = raw154Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw154 raw154Labels permutation8 permutation5
    mixedMoment B raw154step0 raw154step0Labels = mixedMoment B raw154step1 raw154step1Labels := by
      have ha : raw154step1 = raw154step0 := by apply Matrix.ext; unfold raw154step1 raw154step0; decide +kernel
      have hl : raw154step0Labels = labelEmbedding1 ∘ raw154step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw154step0 raw154step0Labels raw154step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1442 node1442Labels := by rfl

theorem canonical155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw155 raw155Labels = mixedMoment B node111 node111Labels := by
  calc
    mixedMoment B raw155 raw155Labels = mixedMoment B raw155step0 raw155step0Labels := by
      have ha : raw155step0 = (fun i j => raw155 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw155step0 raw155; decide +kernel
      have hl : raw155step0Labels = raw155Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw155 raw155Labels permutation10 permutation4
    _ = mixedMoment B node111 node111Labels := by rfl

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

theorem canonical382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw382 raw382Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw382 raw382Labels = mixedMoment B raw382step0 raw382step0Labels := by
      have ha : raw382step0 = (fun i j => raw382 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw382step0 raw382; decide +kernel
      have hl : raw382step0Labels = raw382Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw382 raw382Labels permutation8 permutation5
    mixedMoment B raw382step0 raw382step0Labels = mixedMoment B raw382step1 raw382step1Labels := by
      have ha : raw382step1 = raw382step0 := by apply Matrix.ext; unfold raw382step1 raw382step0; decide +kernel
      have hl : raw382step0Labels = labelEmbedding1 ∘ raw382step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw382step0 raw382step0Labels raw382step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3102 node3102Labels := by rfl

theorem canonical383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw383 raw383Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw383 raw383Labels = mixedMoment B raw383step0 raw383step0Labels := by
      have ha : raw383step0 = (fun i j => raw383 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw383step0 raw383; decide +kernel
      have hl : raw383step0Labels = raw383Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw383 raw383Labels permutation8 permutation4
    _ = mixedMoment B node404 node404Labels := by rfl

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

theorem canonical436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw436 raw436Labels = mixedMoment B node3187 node3187Labels := by
  calc
    mixedMoment B raw436 raw436Labels = mixedMoment B raw436step0 raw436step0Labels := by
      have ha : raw436step0 = (fun i j => raw436 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw436step0 raw436; decide +kernel
      have hl : raw436step0Labels = raw436Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw436 raw436Labels permutation8 permutation5
    mixedMoment B raw436step0 raw436step0Labels = mixedMoment B raw436step1 raw436step1Labels := by
      have ha : raw436step1 = raw436step0 := by apply Matrix.ext; unfold raw436step1 raw436step0; decide +kernel
      have hl : raw436step0Labels = labelEmbedding1 ∘ raw436step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw436step0 raw436step0Labels raw436step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3187 node3187Labels := by rfl

theorem canonical437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw437 raw437Labels = mixedMoment B node251 node251Labels := by
  calc
    mixedMoment B raw437 raw437Labels = mixedMoment B raw437step0 raw437step0Labels := by
      have ha : raw437step0 = (fun i j => raw437 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw437step0 raw437; decide +kernel
      have hl : raw437step0Labels = raw437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw437 raw437Labels permutation9 permutation4
    _ = mixedMoment B node251 node251Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5724 raw5724Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5724 raw5724Labels = mixedMoment B raw5724step0 raw5724step0Labels := by
      have hz : ∀ j, raw5724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5724step0 = (fun i j => raw5724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5724step0 raw5724; decide +kernel
      have hl : raw5724step0Labels = raw5724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5724 raw5724Labels permutation346 hz
    mixedMoment B raw5724step0 raw5724step0Labels = mixedMoment B raw5724step1 raw5724step1Labels := by
      have ha : raw5724step1 = (fun i j => raw5724step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5724step1 raw5724step0; decide +kernel
      have hl : raw5724step1Labels = raw5724step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5724step0 raw5724step0Labels permutation55 permutation5
    mixedMoment B raw5724step1 raw5724step1Labels = mixedMoment B raw5724step2 raw5724step2Labels := by
      have ha : raw5724step2 = -raw5724step1 := by apply Matrix.ext; change ∀ i j, raw5724step2 i j = -(raw5724step1 i j); unfold raw5724step2 raw5724step1; decide +kernel
      have hl : raw5724step2Labels = raw5724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5724step2 raw5724step2Labels = mixedMoment B raw5724step3 raw5724step3Labels := by
      have ha : raw5724step3 = raw5724step2 := by apply Matrix.ext; unfold raw5724step3 raw5724step2; decide +kernel
      have hl : raw5724step2Labels = labelEmbedding1 ∘ raw5724step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5724step2 raw5724step2Labels raw5724step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3222 node3222Labels := by rfl

theorem canonical5725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5725 raw5725Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5725 raw5725Labels = mixedMoment B raw5725step0 raw5725step0Labels := by
      have hz : ∀ j, raw5725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5725step0 = (fun i j => raw5725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5725step0 raw5725; decide +kernel
      have hl : raw5725step0Labels = raw5725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5725 raw5725Labels permutation434 hz
    mixedMoment B raw5725step0 raw5725step0Labels = mixedMoment B raw5725step1 raw5725step1Labels := by
      have ha : raw5725step1 = (fun i j => raw5725step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5725step1 raw5725step0; decide +kernel
      have hl : raw5725step1Labels = raw5725step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5725step0 raw5725step0Labels permutation55 permutation5
    mixedMoment B raw5725step1 raw5725step1Labels = mixedMoment B raw5725step2 raw5725step2Labels := by
      have ha : raw5725step2 = -raw5725step1 := by apply Matrix.ext; change ∀ i j, raw5725step2 i j = -(raw5725step1 i j); unfold raw5725step2 raw5725step1; decide +kernel
      have hl : raw5725step2Labels = raw5725step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5725step2 raw5725step2Labels = mixedMoment B raw5725step3 raw5725step3Labels := by
      have ha : raw5725step3 = raw5725step2 := by apply Matrix.ext; unfold raw5725step3 raw5725step2; decide +kernel
      have hl : raw5725step2Labels = labelEmbedding1 ∘ raw5725step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5725step2 raw5725step2Labels raw5725step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3222 node3222Labels := by rfl

theorem canonical5745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5745 raw5745Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw5745 raw5745Labels = mixedMoment B raw5745step0 raw5745step0Labels := by
      have hz : ∀ j, raw5745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5745step0 = (fun i j => raw5745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5745step0 raw5745; decide +kernel
      have hl : raw5745step0Labels = raw5745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5745 raw5745Labels permutation346 hz
    mixedMoment B raw5745step0 raw5745step0Labels = mixedMoment B raw5745step1 raw5745step1Labels := by
      have ha : raw5745step1 = (fun i j => raw5745step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5745step1 raw5745step0; decide +kernel
      have hl : raw5745step1Labels = raw5745step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5745step0 raw5745step0Labels permutation32 permutation7
    mixedMoment B raw5745step1 raw5745step1Labels = mixedMoment B raw5745step2 raw5745step2Labels := by
      have ha : raw5745step2 = raw5745step1 := by apply Matrix.ext; unfold raw5745step2 raw5745step1; decide +kernel
      have hl : raw5745step1Labels = labelEmbedding1 ∘ raw5745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5745step1 raw5745step1Labels raw5745step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

theorem canonical5746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5746 raw5746Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw5746 raw5746Labels = mixedMoment B raw5746step0 raw5746step0Labels := by
      have hz : ∀ j, raw5746 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5746step0 = (fun i j => raw5746 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5746step0 raw5746; decide +kernel
      have hl : raw5746step0Labels = raw5746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5746 raw5746Labels permutation434 hz
    mixedMoment B raw5746step0 raw5746step0Labels = mixedMoment B raw5746step1 raw5746step1Labels := by
      have ha : raw5746step1 = (fun i j => raw5746step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5746step1 raw5746step0; decide +kernel
      have hl : raw5746step1Labels = raw5746step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5746step0 raw5746step0Labels permutation32 permutation7
    mixedMoment B raw5746step1 raw5746step1Labels = mixedMoment B raw5746step2 raw5746step2Labels := by
      have ha : raw5746step2 = raw5746step1 := by apply Matrix.ext; unfold raw5746step2 raw5746step1; decide +kernel
      have hl : raw5746step1Labels = labelEmbedding1 ∘ raw5746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5746step1 raw5746step1Labels raw5746step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7949 raw7949Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw7949 raw7949Labels = mixedMoment B raw7949step0 raw7949step0Labels := by
      have hz : ∀ j, raw7949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7949step0 = (fun i j => raw7949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7949step0 raw7949; decide +kernel
      have hl : raw7949step0Labels = raw7949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7949 raw7949Labels permutation434 hz
    mixedMoment B raw7949step0 raw7949step0Labels = mixedMoment B raw7949step1 raw7949step1Labels := by
      have hz : ∀ j, raw7949step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7949step1 = (fun i j => raw7949step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7949step1 raw7949step0; decide +kernel
      have hl : raw7949step1Labels = raw7949step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7949step0 raw7949step0Labels permutation80 hz
    mixedMoment B raw7949step1 raw7949step1Labels = mixedMoment B raw7949step2 raw7949step2Labels := by
      have ha : raw7949step2 = (fun i j => raw7949step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7949step2 raw7949step1; decide +kernel
      have hl : raw7949step2Labels = raw7949step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7949step1 raw7949step1Labels permutation8 permutation7
    mixedMoment B raw7949step2 raw7949step2Labels = mixedMoment B raw7949step3 raw7949step3Labels := by
      have ha : raw7949step3 = raw7949step2 := by apply Matrix.ext; unfold raw7949step3 raw7949step2; decide +kernel
      have hl : raw7949step2Labels = labelEmbedding1 ∘ raw7949step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7949step2 raw7949step2Labels raw7949step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3102 node3102Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9705 raw9705Labels = mixedMoment B node3187 node3187Labels := by
  calc
    mixedMoment B raw9705 raw9705Labels = mixedMoment B raw9705step0 raw9705step0Labels := by
      have hz : ∀ j, raw9705 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9705step0 = (fun i j => raw9705 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9705step0 raw9705; decide +kernel
      have hl : raw9705step0Labels = raw9705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9705 raw9705Labels permutation434 hz
    mixedMoment B raw9705step0 raw9705step0Labels = mixedMoment B raw9705step1 raw9705step1Labels := by
      have hz : ∀ j, raw9705step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9705step1 = (fun i j => raw9705step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9705step1 raw9705step0; decide +kernel
      have hl : raw9705step1Labels = raw9705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9705step0 raw9705step0Labels permutation80 hz
    mixedMoment B raw9705step1 raw9705step1Labels = mixedMoment B raw9705step2 raw9705step2Labels := by
      have ha : raw9705step2 = (fun i j => raw9705step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9705step2 raw9705step1; decide +kernel
      have hl : raw9705step2Labels = raw9705step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9705step1 raw9705step1Labels permutation11 permutation5
    mixedMoment B raw9705step2 raw9705step2Labels = mixedMoment B raw9705step3 raw9705step3Labels := by
      have ha : raw9705step3 = -raw9705step2 := by apply Matrix.ext; change ∀ i j, raw9705step3 i j = -(raw9705step2 i j); unfold raw9705step3 raw9705step2; decide +kernel
      have hl : raw9705step3Labels = raw9705step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9705step3 raw9705step3Labels = mixedMoment B raw9705step4 raw9705step4Labels := by
      have ha : raw9705step4 = raw9705step3 := by apply Matrix.ext; unfold raw9705step4 raw9705step3; decide +kernel
      have hl : raw9705step3Labels = labelEmbedding1 ∘ raw9705step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9705step3 raw9705step3Labels raw9705step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3187 node3187Labels := by rfl

theorem canonical9709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9709 raw9709Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw9709 raw9709Labels = mixedMoment B raw9709step0 raw9709step0Labels := by
      have hz : ∀ j, raw9709 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9709step0 = (fun i j => raw9709 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9709step0 raw9709; decide +kernel
      have hl : raw9709step0Labels = raw9709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9709 raw9709Labels permutation434 hz
    mixedMoment B raw9709step0 raw9709step0Labels = mixedMoment B raw9709step1 raw9709step1Labels := by
      have hz : ∀ j, raw9709step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9709step1 = (fun i j => raw9709step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9709step1 raw9709step0; decide +kernel
      have hl : raw9709step1Labels = raw9709step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9709step0 raw9709step0Labels permutation80 hz
    mixedMoment B raw9709step1 raw9709step1Labels = mixedMoment B raw9709step2 raw9709step2Labels := by
      have ha : raw9709step2 = (fun i j => raw9709step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9709step2 raw9709step1; decide +kernel
      have hl : raw9709step2Labels = raw9709step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9709step1 raw9709step1Labels permutation8 permutation7
    mixedMoment B raw9709step2 raw9709step2Labels = mixedMoment B raw9709step3 raw9709step3Labels := by
      have ha : raw9709step3 = raw9709step2 := by apply Matrix.ext; unfold raw9709step3 raw9709step2; decide +kernel
      have hl : raw9709step2Labels = labelEmbedding1 ∘ raw9709step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9709step2 raw9709step2Labels raw9709step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3055 node3055Labels := by rfl

theorem canonical9716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9716 raw9716Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw9716 raw9716Labels = mixedMoment B raw9716step0 raw9716step0Labels := by
      have hz : ∀ j, raw9716 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9716step0 = (fun i j => raw9716 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9716step0 raw9716; decide +kernel
      have hl : raw9716step0Labels = raw9716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9716 raw9716Labels permutation434 hz
    mixedMoment B raw9716step0 raw9716step0Labels = mixedMoment B raw9716step1 raw9716step1Labels := by
      have hz : ∀ j, raw9716step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9716step1 = (fun i j => raw9716step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9716step1 raw9716step0; decide +kernel
      have hl : raw9716step1Labels = raw9716step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9716step0 raw9716step0Labels permutation80 hz
    mixedMoment B raw9716step1 raw9716step1Labels = mixedMoment B raw9716step2 raw9716step2Labels := by
      have ha : raw9716step2 = (fun i j => raw9716step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9716step2 raw9716step1; decide +kernel
      have hl : raw9716step2Labels = raw9716step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9716step1 raw9716step1Labels permutation10 permutation5
    mixedMoment B raw9716step2 raw9716step2Labels = mixedMoment B raw9716step3 raw9716step3Labels := by
      have ha : raw9716step3 = -raw9716step2 := by apply Matrix.ext; change ∀ i j, raw9716step3 i j = -(raw9716step2 i j); unfold raw9716step3 raw9716step2; decide +kernel
      have hl : raw9716step3Labels = raw9716step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9716step3 raw9716step3Labels = mixedMoment B raw9716step4 raw9716step4Labels := by
      have ha : raw9716step4 = raw9716step3 := by apply Matrix.ext; unfold raw9716step4 raw9716step3; decide +kernel
      have hl : raw9716step3Labels = labelEmbedding1 ∘ raw9716step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9716step3 raw9716step3Labels raw9716step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3230 node3230Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9944 raw9944Labels = mixedMoment B node3210 node3210Labels := by
  calc
    mixedMoment B raw9944 raw9944Labels = mixedMoment B raw9944step0 raw9944step0Labels := by
      have hz : ∀ j, raw9944 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9944step0 = (fun i j => raw9944 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9944step0 raw9944; decide +kernel
      have hl : raw9944step0Labels = raw9944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9944 raw9944Labels permutation346 hz
    mixedMoment B raw9944step0 raw9944step0Labels = mixedMoment B raw9944step1 raw9944step1Labels := by
      have ha : raw9944step1 = (fun i j => raw9944step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9944step1 raw9944step0; decide +kernel
      have hl : raw9944step1Labels = raw9944step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9944step0 raw9944step0Labels permutation43 permutation5
    mixedMoment B raw9944step1 raw9944step1Labels = mixedMoment B raw9944step2 raw9944step2Labels := by
      have ha : raw9944step2 = -raw9944step1 := by apply Matrix.ext; change ∀ i j, raw9944step2 i j = -(raw9944step1 i j); unfold raw9944step2 raw9944step1; decide +kernel
      have hl : raw9944step2Labels = raw9944step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9944step2 raw9944step2Labels = mixedMoment B raw9944step3 raw9944step3Labels := by
      have ha : raw9944step3 = raw9944step2 := by apply Matrix.ext; unfold raw9944step3 raw9944step2; decide +kernel
      have hl : raw9944step2Labels = labelEmbedding1 ∘ raw9944step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9944step2 raw9944step2Labels raw9944step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3210 node3210Labels := by rfl

theorem canonical9947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9947 raw9947Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw9947 raw9947Labels = mixedMoment B raw9947step0 raw9947step0Labels := by
      have hz : ∀ j, raw9947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9947step0 = (fun i j => raw9947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9947step0 raw9947; decide +kernel
      have hl : raw9947step0Labels = raw9947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9947 raw9947Labels permutation346 hz
    mixedMoment B raw9947step0 raw9947step0Labels = mixedMoment B raw9947step1 raw9947step1Labels := by
      have ha : raw9947step1 = (fun i j => raw9947step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9947step1 raw9947step0; decide +kernel
      have hl : raw9947step1Labels = raw9947step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9947step0 raw9947step0Labels permutation32 permutation7
    mixedMoment B raw9947step1 raw9947step1Labels = mixedMoment B raw9947step2 raw9947step2Labels := by
      have ha : raw9947step2 = raw9947step1 := by apply Matrix.ext; unfold raw9947step2 raw9947step1; decide +kernel
      have hl : raw9947step1Labels = labelEmbedding1 ∘ raw9947step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9947step1 raw9947step1Labels raw9947step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

theorem canonical9954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9954 raw9954Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw9954 raw9954Labels = mixedMoment B raw9954step0 raw9954step0Labels := by
      have hz : ∀ j, raw9954 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9954step0 = (fun i j => raw9954 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9954step0 raw9954; decide +kernel
      have hl : raw9954step0Labels = raw9954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9954 raw9954Labels permutation434 hz
    mixedMoment B raw9954step0 raw9954step0Labels = mixedMoment B raw9954step1 raw9954step1Labels := by
      have hz : ∀ j, raw9954step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9954step1 = (fun i j => raw9954step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9954step1 raw9954step0; decide +kernel
      have hl : raw9954step1Labels = raw9954step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9954step0 raw9954step0Labels permutation80 hz
    mixedMoment B raw9954step1 raw9954step1Labels = mixedMoment B raw9954step2 raw9954step2Labels := by
      have ha : raw9954step2 = (fun i j => raw9954step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9954step2 raw9954step1; decide +kernel
      have hl : raw9954step2Labels = raw9954step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9954step1 raw9954step1Labels permutation8 permutation7
    mixedMoment B raw9954step2 raw9954step2Labels = mixedMoment B raw9954step3 raw9954step3Labels := by
      have ha : raw9954step3 = raw9954step2 := by apply Matrix.ext; unfold raw9954step3 raw9954step2; decide +kernel
      have hl : raw9954step2Labels = labelEmbedding1 ∘ raw9954step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9954step2 raw9954step2Labels raw9954step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3229 node3229Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10178 raw10178Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw10178 raw10178Labels = mixedMoment B raw10178step0 raw10178step0Labels := by
      have hz : ∀ j, raw10178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10178step0 = (fun i j => raw10178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10178step0 raw10178; decide +kernel
      have hl : raw10178step0Labels = raw10178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10178 raw10178Labels permutation346 hz
    mixedMoment B raw10178step0 raw10178step0Labels = mixedMoment B raw10178step1 raw10178step1Labels := by
      have ha : raw10178step1 = (fun i j => raw10178step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10178step1 raw10178step0; decide +kernel
      have hl : raw10178step1Labels = raw10178step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10178step0 raw10178step0Labels permutation41 permutation5
    mixedMoment B raw10178step1 raw10178step1Labels = mixedMoment B raw10178step2 raw10178step2Labels := by
      have ha : raw10178step2 = -raw10178step1 := by apply Matrix.ext; change ∀ i j, raw10178step2 i j = -(raw10178step1 i j); unfold raw10178step2 raw10178step1; decide +kernel
      have hl : raw10178step2Labels = raw10178step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10178step2 raw10178step2Labels = mixedMoment B raw10178step3 raw10178step3Labels := by
      have ha : raw10178step3 = raw10178step2 := by apply Matrix.ext; unfold raw10178step3 raw10178step2; decide +kernel
      have hl : raw10178step2Labels = labelEmbedding1 ∘ raw10178step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10178step2 raw10178step2Labels raw10178step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3206 node3206Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10996 raw10996Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw10996 raw10996Labels = mixedMoment B raw10996step0 raw10996step0Labels := by
      have hz : ∀ j, raw10996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10996step0 = (fun i j => raw10996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10996step0 raw10996; decide +kernel
      have hl : raw10996step0Labels = raw10996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10996 raw10996Labels permutation434 hz
    mixedMoment B raw10996step0 raw10996step0Labels = mixedMoment B raw10996step1 raw10996step1Labels := by
      have ha : raw10996step1 = (fun i j => raw10996step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10996step1 raw10996step0; decide +kernel
      have hl : raw10996step1Labels = raw10996step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10996step0 raw10996step0Labels permutation32 permutation7
    mixedMoment B raw10996step1 raw10996step1Labels = mixedMoment B raw10996step2 raw10996step2Labels := by
      have ha : raw10996step2 = raw10996step1 := by apply Matrix.ext; unfold raw10996step2 raw10996step1; decide +kernel
      have hl : raw10996step1Labels = labelEmbedding1 ∘ raw10996step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10996step1 raw10996step1Labels raw10996step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

theorem canonical10997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10997 raw10997Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw10997 raw10997Labels = mixedMoment B raw10997step0 raw10997step0Labels := by
      have hz : ∀ j, raw10997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10997step0 = (fun i j => raw10997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10997step0 raw10997; decide +kernel
      have hl : raw10997step0Labels = raw10997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10997 raw10997Labels permutation434 hz
    mixedMoment B raw10997step0 raw10997step0Labels = mixedMoment B raw10997step1 raw10997step1Labels := by
      have hz : ∀ j, raw10997step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10997step1 = (fun i j => raw10997step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10997step1 raw10997step0; decide +kernel
      have hl : raw10997step1Labels = raw10997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10997step0 raw10997step0Labels permutation80 hz
    mixedMoment B raw10997step1 raw10997step1Labels = mixedMoment B raw10997step2 raw10997step2Labels := by
      have ha : raw10997step2 = (fun i j => raw10997step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10997step2 raw10997step1; decide +kernel
      have hl : raw10997step2Labels = raw10997step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10997step1 raw10997step1Labels permutation8 permutation7
    mixedMoment B raw10997step2 raw10997step2Labels = mixedMoment B raw10997step3 raw10997step3Labels := by
      have ha : raw10997step3 = raw10997step2 := by apply Matrix.ext; unfold raw10997step3 raw10997step2; decide +kernel
      have hl : raw10997step2Labels = labelEmbedding1 ∘ raw10997step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10997step2 raw10997step2Labels raw10997step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical10998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10998 raw10998Labels = mixedMoment B node1408 node1408Labels := by
  calc
    mixedMoment B raw10998 raw10998Labels = mixedMoment B raw10998step0 raw10998step0Labels := by
      have hz : ∀ j, raw10998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10998step0 = (fun i j => raw10998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10998step0 raw10998; decide +kernel
      have hl : raw10998step0Labels = raw10998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10998 raw10998Labels permutation434 hz
    mixedMoment B raw10998step0 raw10998step0Labels = mixedMoment B raw10998step1 raw10998step1Labels := by
      have hz : ∀ j, raw10998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10998step1 = (fun i j => raw10998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10998step1 raw10998step0; decide +kernel
      have hl : raw10998step1Labels = raw10998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10998step0 raw10998step0Labels permutation80 hz
    mixedMoment B raw10998step1 raw10998step1Labels = mixedMoment B raw10998step2 raw10998step2Labels := by
      have ha : raw10998step2 = (fun i j => raw10998step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10998step2 raw10998step1; decide +kernel
      have hl : raw10998step2Labels = raw10998step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10998step1 raw10998step1Labels permutation11 permutation5
    mixedMoment B raw10998step2 raw10998step2Labels = mixedMoment B raw10998step3 raw10998step3Labels := by
      have ha : raw10998step3 = -raw10998step2 := by apply Matrix.ext; change ∀ i j, raw10998step3 i j = -(raw10998step2 i j); unfold raw10998step3 raw10998step2; decide +kernel
      have hl : raw10998step3Labels = raw10998step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10998step3 raw10998step3Labels = mixedMoment B raw10998step4 raw10998step4Labels := by
      have ha : raw10998step4 = raw10998step3 := by apply Matrix.ext; unfold raw10998step4 raw10998step3; decide +kernel
      have hl : raw10998step3Labels = labelEmbedding1 ∘ raw10998step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10998step3 raw10998step3Labels raw10998step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1408 node1408Labels := by rfl

theorem canonical10999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10999 raw10999Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw10999 raw10999Labels = mixedMoment B raw10999step0 raw10999step0Labels := by
      have hz : ∀ j, raw10999 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10999step0 = (fun i j => raw10999 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10999step0 raw10999; decide +kernel
      have hl : raw10999step0Labels = raw10999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10999 raw10999Labels permutation434 hz
    mixedMoment B raw10999step0 raw10999step0Labels = mixedMoment B raw10999step1 raw10999step1Labels := by
      have ha : raw10999step1 = (fun i j => raw10999step0 (permutation79 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10999step1 raw10999step0; decide +kernel
      have hl : raw10999step1Labels = raw10999step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10999step0 raw10999step0Labels permutation79 permutation5
    mixedMoment B raw10999step1 raw10999step1Labels = mixedMoment B raw10999step2 raw10999step2Labels := by
      have ha : raw10999step2 = raw10999step1 := by apply Matrix.ext; unfold raw10999step2 raw10999step1; decide +kernel
      have hl : raw10999step1Labels = labelEmbedding1 ∘ raw10999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10999step1 raw10999step1Labels raw10999step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2092 node2092Labels := by rfl

theorem canonical11000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11000 raw11000Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw11000 raw11000Labels = mixedMoment B raw11000step0 raw11000step0Labels := by
      have hz : ∀ j, raw11000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11000step0 = (fun i j => raw11000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11000step0 raw11000; decide +kernel
      have hl : raw11000step0Labels = raw11000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11000 raw11000Labels permutation346 hz
    mixedMoment B raw11000step0 raw11000step0Labels = mixedMoment B raw11000step1 raw11000step1Labels := by
      have ha : raw11000step1 = (fun i j => raw11000step0 (permutation79 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11000step1 raw11000step0; decide +kernel
      have hl : raw11000step1Labels = raw11000step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11000step0 raw11000step0Labels permutation79 permutation5
    mixedMoment B raw11000step1 raw11000step1Labels = mixedMoment B raw11000step2 raw11000step2Labels := by
      have ha : raw11000step2 = raw11000step1 := by apply Matrix.ext; unfold raw11000step2 raw11000step1; decide +kernel
      have hl : raw11000step1Labels = labelEmbedding1 ∘ raw11000step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11000step1 raw11000step1Labels raw11000step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2092 node2092Labels := by rfl

theorem canonical11001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11001 raw11001Labels = mixedMoment B node2113 node2113Labels := by
  calc
    mixedMoment B raw11001 raw11001Labels = mixedMoment B raw11001step0 raw11001step0Labels := by
      have hz : ∀ j, raw11001 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11001step0 = (fun i j => raw11001 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11001step0 raw11001; decide +kernel
      have hl : raw11001step0Labels = raw11001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11001 raw11001Labels permutation434 hz
    mixedMoment B raw11001step0 raw11001step0Labels = mixedMoment B raw11001step1 raw11001step1Labels := by
      have hz : ∀ j, raw11001step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11001step1 = (fun i j => raw11001step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11001step1 raw11001step0; decide +kernel
      have hl : raw11001step1Labels = raw11001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11001step0 raw11001step0Labels permutation80 hz
    mixedMoment B raw11001step1 raw11001step1Labels = mixedMoment B raw11001step2 raw11001step2Labels := by
      have ha : raw11001step2 = (fun i j => raw11001step1 (permutation19 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11001step2 raw11001step1; decide +kernel
      have hl : raw11001step2Labels = raw11001step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11001step1 raw11001step1Labels permutation19 permutation5
    mixedMoment B raw11001step2 raw11001step2Labels = mixedMoment B raw11001step3 raw11001step3Labels := by
      have ha : raw11001step3 = raw11001step2 := by apply Matrix.ext; unfold raw11001step3 raw11001step2; decide +kernel
      have hl : raw11001step2Labels = labelEmbedding1 ∘ raw11001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11001step2 raw11001step2Labels raw11001step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2113 node2113Labels := by rfl

theorem canonical11002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11002 raw11002Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw11002 raw11002Labels = mixedMoment B raw11002step0 raw11002step0Labels := by
      have hz : ∀ j, raw11002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11002step0 = (fun i j => raw11002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11002step0 raw11002; decide +kernel
      have hl : raw11002step0Labels = raw11002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11002 raw11002Labels permutation434 hz
    mixedMoment B raw11002step0 raw11002step0Labels = mixedMoment B raw11002step1 raw11002step1Labels := by
      have hz : ∀ j, raw11002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11002step1 = (fun i j => raw11002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11002step1 raw11002step0; decide +kernel
      have hl : raw11002step1Labels = raw11002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11002step0 raw11002step0Labels permutation80 hz
    mixedMoment B raw11002step1 raw11002step1Labels = mixedMoment B raw11002step2 raw11002step2Labels := by
      have ha : raw11002step2 = (fun i j => raw11002step1 (permutation17 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11002step2 raw11002step1; decide +kernel
      have hl : raw11002step2Labels = raw11002step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11002step1 raw11002step1Labels permutation17 permutation5
    mixedMoment B raw11002step2 raw11002step2Labels = mixedMoment B raw11002step3 raw11002step3Labels := by
      have ha : raw11002step3 = raw11002step2 := by apply Matrix.ext; unfold raw11002step3 raw11002step2; decide +kernel
      have hl : raw11002step2Labels = labelEmbedding1 ∘ raw11002step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11002step2 raw11002step2Labels raw11002step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2255 node2255Labels := by rfl

theorem canonical11003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11003 raw11003Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw11003 raw11003Labels = mixedMoment B raw11003step0 raw11003step0Labels := by
      have hz : ∀ j, raw11003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11003step0 = (fun i j => raw11003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11003step0 raw11003; decide +kernel
      have hl : raw11003step0Labels = raw11003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11003 raw11003Labels permutation434 hz
    mixedMoment B raw11003step0 raw11003step0Labels = mixedMoment B raw11003step1 raw11003step1Labels := by
      have ha : raw11003step1 = (fun i j => raw11003step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11003step1 raw11003step0; decide +kernel
      have hl : raw11003step1Labels = raw11003step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11003step0 raw11003step0Labels permutation49 permutation5
    mixedMoment B raw11003step1 raw11003step1Labels = mixedMoment B raw11003step2 raw11003step2Labels := by
      have ha : raw11003step2 = -raw11003step1 := by apply Matrix.ext; change ∀ i j, raw11003step2 i j = -(raw11003step1 i j); unfold raw11003step2 raw11003step1; decide +kernel
      have hl : raw11003step2Labels = raw11003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11003step2 raw11003step2Labels = mixedMoment B raw11003step3 raw11003step3Labels := by
      have ha : raw11003step3 = raw11003step2 := by apply Matrix.ext; unfold raw11003step3 raw11003step2; decide +kernel
      have hl : raw11003step2Labels = labelEmbedding1 ∘ raw11003step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11003step2 raw11003step2Labels raw11003step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1406 node1406Labels := by rfl

theorem canonical11004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11004 raw11004Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw11004 raw11004Labels = mixedMoment B raw11004step0 raw11004step0Labels := by
      have ha : raw11004step0 = (fun i j => raw11004 (permutation217 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11004step0 raw11004; decide +kernel
      have hl : raw11004step0Labels = raw11004Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11004 raw11004Labels permutation217 permutation5
    mixedMoment B raw11004step0 raw11004step0Labels = mixedMoment B raw11004step1 raw11004step1Labels := by
      have ha : raw11004step1 = -raw11004step0 := by apply Matrix.ext; change ∀ i j, raw11004step1 i j = -(raw11004step0 i j); unfold raw11004step1 raw11004step0; decide +kernel
      have hl : raw11004step1Labels = raw11004step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11004step1 raw11004step1Labels = mixedMoment B raw11004step2 raw11004step2Labels := by
      have ha : raw11004step2 = raw11004step1 := by apply Matrix.ext; unfold raw11004step2 raw11004step1; decide +kernel
      have hl : raw11004step1Labels = labelEmbedding1 ∘ raw11004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11004step1 raw11004step1Labels raw11004step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3202 node3202Labels := by rfl

theorem canonical11005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11005 raw11005Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw11005 raw11005Labels = mixedMoment B raw11005step0 raw11005step0Labels := by
      have hz : ∀ j, raw11005 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11005step0 = (fun i j => raw11005 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11005step0 raw11005; decide +kernel
      have hl : raw11005step0Labels = raw11005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11005 raw11005Labels permutation434 hz
    mixedMoment B raw11005step0 raw11005step0Labels = mixedMoment B raw11005step1 raw11005step1Labels := by
      have ha : raw11005step1 = (fun i j => raw11005step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11005step1 raw11005step0; decide +kernel
      have hl : raw11005step1Labels = raw11005step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11005step0 raw11005step0Labels permutation49 permutation5
    mixedMoment B raw11005step1 raw11005step1Labels = mixedMoment B raw11005step2 raw11005step2Labels := by
      have ha : raw11005step2 = -raw11005step1 := by apply Matrix.ext; change ∀ i j, raw11005step2 i j = -(raw11005step1 i j); unfold raw11005step2 raw11005step1; decide +kernel
      have hl : raw11005step2Labels = raw11005step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11005step2 raw11005step2Labels = mixedMoment B raw11005step3 raw11005step3Labels := by
      have ha : raw11005step3 = raw11005step2 := by apply Matrix.ext; unfold raw11005step3 raw11005step2; decide +kernel
      have hl : raw11005step2Labels = labelEmbedding1 ∘ raw11005step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11005step2 raw11005step2Labels raw11005step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3180 node3180Labels := by rfl

theorem canonical11006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11006 raw11006Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw11006 raw11006Labels = mixedMoment B raw11006step0 raw11006step0Labels := by
      have hz : ∀ j, raw11006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11006step0 = (fun i j => raw11006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11006step0 raw11006; decide +kernel
      have hl : raw11006step0Labels = raw11006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11006 raw11006Labels permutation346 hz
    mixedMoment B raw11006step0 raw11006step0Labels = mixedMoment B raw11006step1 raw11006step1Labels := by
      have ha : raw11006step1 = (fun i j => raw11006step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11006step1 raw11006step0; decide +kernel
      have hl : raw11006step1Labels = raw11006step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11006step0 raw11006step0Labels permutation49 permutation5
    mixedMoment B raw11006step1 raw11006step1Labels = mixedMoment B raw11006step2 raw11006step2Labels := by
      have ha : raw11006step2 = -raw11006step1 := by apply Matrix.ext; change ∀ i j, raw11006step2 i j = -(raw11006step1 i j); unfold raw11006step2 raw11006step1; decide +kernel
      have hl : raw11006step2Labels = raw11006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11006step2 raw11006step2Labels = mixedMoment B raw11006step3 raw11006step3Labels := by
      have ha : raw11006step3 = raw11006step2 := by apply Matrix.ext; unfold raw11006step3 raw11006step2; decide +kernel
      have hl : raw11006step2Labels = labelEmbedding1 ∘ raw11006step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11006step2 raw11006step2Labels raw11006step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1406 node1406Labels := by rfl

theorem canonical11007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11007 raw11007Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw11007 raw11007Labels = mixedMoment B raw11007step0 raw11007step0Labels := by
      have ha : raw11007step0 = (fun i j => raw11007 (permutation193 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11007step0 raw11007; decide +kernel
      have hl : raw11007step0Labels = raw11007Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11007 raw11007Labels permutation193 permutation5
    mixedMoment B raw11007step0 raw11007step0Labels = mixedMoment B raw11007step1 raw11007step1Labels := by
      have ha : raw11007step1 = -raw11007step0 := by apply Matrix.ext; change ∀ i j, raw11007step1 i j = -(raw11007step0 i j); unfold raw11007step1 raw11007step0; decide +kernel
      have hl : raw11007step1Labels = raw11007step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11007step1 raw11007step1Labels = mixedMoment B raw11007step2 raw11007step2Labels := by
      have ha : raw11007step2 = raw11007step1 := by apply Matrix.ext; unfold raw11007step2 raw11007step1; decide +kernel
      have hl : raw11007step1Labels = labelEmbedding1 ∘ raw11007step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11007step1 raw11007step1Labels raw11007step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3202 node3202Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11008 raw11008Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw11008 raw11008Labels = mixedMoment B raw11008step0 raw11008step0Labels := by
      have hz : ∀ j, raw11008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11008step0 = (fun i j => raw11008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11008step0 raw11008; decide +kernel
      have hl : raw11008step0Labels = raw11008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11008 raw11008Labels permutation346 hz
    mixedMoment B raw11008step0 raw11008step0Labels = mixedMoment B raw11008step1 raw11008step1Labels := by
      have ha : raw11008step1 = (fun i j => raw11008step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11008step1 raw11008step0; decide +kernel
      have hl : raw11008step1Labels = raw11008step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11008step0 raw11008step0Labels permutation49 permutation5
    mixedMoment B raw11008step1 raw11008step1Labels = mixedMoment B raw11008step2 raw11008step2Labels := by
      have ha : raw11008step2 = -raw11008step1 := by apply Matrix.ext; change ∀ i j, raw11008step2 i j = -(raw11008step1 i j); unfold raw11008step2 raw11008step1; decide +kernel
      have hl : raw11008step2Labels = raw11008step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11008step2 raw11008step2Labels = mixedMoment B raw11008step3 raw11008step3Labels := by
      have ha : raw11008step3 = raw11008step2 := by apply Matrix.ext; unfold raw11008step3 raw11008step2; decide +kernel
      have hl : raw11008step2Labels = labelEmbedding1 ∘ raw11008step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11008step2 raw11008step2Labels raw11008step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3180 node3180Labels := by rfl

theorem canonical11009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11009 raw11009Labels = mixedMoment B node1442 node1442Labels := by
  calc
    mixedMoment B raw11009 raw11009Labels = mixedMoment B raw11009step0 raw11009step0Labels := by
      have hz : ∀ j, raw11009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11009step0 = (fun i j => raw11009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11009step0 raw11009; decide +kernel
      have hl : raw11009step0Labels = raw11009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11009 raw11009Labels permutation434 hz
    mixedMoment B raw11009step0 raw11009step0Labels = mixedMoment B raw11009step1 raw11009step1Labels := by
      have hz : ∀ j, raw11009step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11009step1 = (fun i j => raw11009step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11009step1 raw11009step0; decide +kernel
      have hl : raw11009step1Labels = raw11009step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11009step0 raw11009step0Labels permutation80 hz
    mixedMoment B raw11009step1 raw11009step1Labels = mixedMoment B raw11009step2 raw11009step2Labels := by
      have ha : raw11009step2 = (fun i j => raw11009step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11009step2 raw11009step1; decide +kernel
      have hl : raw11009step2Labels = raw11009step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11009step1 raw11009step1Labels permutation13 permutation5
    mixedMoment B raw11009step2 raw11009step2Labels = mixedMoment B raw11009step3 raw11009step3Labels := by
      have ha : raw11009step3 = -raw11009step2 := by apply Matrix.ext; change ∀ i j, raw11009step3 i j = -(raw11009step2 i j); unfold raw11009step3 raw11009step2; decide +kernel
      have hl : raw11009step3Labels = raw11009step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11009step3 raw11009step3Labels = mixedMoment B raw11009step4 raw11009step4Labels := by
      have ha : raw11009step4 = raw11009step3 := by apply Matrix.ext; unfold raw11009step4 raw11009step3; decide +kernel
      have hl : raw11009step3Labels = labelEmbedding1 ∘ raw11009step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11009step3 raw11009step3Labels raw11009step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1442 node1442Labels := by rfl

theorem canonical11010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11010 raw11010Labels = mixedMoment B node3210 node3210Labels := by
  calc
    mixedMoment B raw11010 raw11010Labels = mixedMoment B raw11010step0 raw11010step0Labels := by
      have hz : ∀ j, raw11010 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11010step0 = (fun i j => raw11010 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11010step0 raw11010; decide +kernel
      have hl : raw11010step0Labels = raw11010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11010 raw11010Labels permutation434 hz
    mixedMoment B raw11010step0 raw11010step0Labels = mixedMoment B raw11010step1 raw11010step1Labels := by
      have ha : raw11010step1 = (fun i j => raw11010step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11010step1 raw11010step0; decide +kernel
      have hl : raw11010step1Labels = raw11010step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11010step0 raw11010step0Labels permutation43 permutation5
    mixedMoment B raw11010step1 raw11010step1Labels = mixedMoment B raw11010step2 raw11010step2Labels := by
      have ha : raw11010step2 = -raw11010step1 := by apply Matrix.ext; change ∀ i j, raw11010step2 i j = -(raw11010step1 i j); unfold raw11010step2 raw11010step1; decide +kernel
      have hl : raw11010step2Labels = raw11010step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11010step2 raw11010step2Labels = mixedMoment B raw11010step3 raw11010step3Labels := by
      have ha : raw11010step3 = raw11010step2 := by apply Matrix.ext; unfold raw11010step3 raw11010step2; decide +kernel
      have hl : raw11010step2Labels = labelEmbedding1 ∘ raw11010step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11010step2 raw11010step2Labels raw11010step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3210 node3210Labels := by rfl

theorem canonical11011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11011 raw11011Labels = mixedMoment B node3224 node3224Labels := by
  calc
    mixedMoment B raw11011 raw11011Labels = mixedMoment B raw11011step0 raw11011step0Labels := by
      have hz : ∀ j, raw11011 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11011step0 = (fun i j => raw11011 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11011step0 raw11011; decide +kernel
      have hl : raw11011step0Labels = raw11011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11011 raw11011Labels permutation434 hz
    mixedMoment B raw11011step0 raw11011step0Labels = mixedMoment B raw11011step1 raw11011step1Labels := by
      have hz : ∀ j, raw11011step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11011step1 = (fun i j => raw11011step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11011step1 raw11011step0; decide +kernel
      have hl : raw11011step1Labels = raw11011step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11011step0 raw11011step0Labels permutation80 hz
    mixedMoment B raw11011step1 raw11011step1Labels = mixedMoment B raw11011step2 raw11011step2Labels := by
      have ha : raw11011step2 = (fun i j => raw11011step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11011step2 raw11011step1; decide +kernel
      have hl : raw11011step2Labels = raw11011step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11011step1 raw11011step1Labels permutation13 permutation5
    mixedMoment B raw11011step2 raw11011step2Labels = mixedMoment B raw11011step3 raw11011step3Labels := by
      have ha : raw11011step3 = -raw11011step2 := by apply Matrix.ext; change ∀ i j, raw11011step3 i j = -(raw11011step2 i j); unfold raw11011step3 raw11011step2; decide +kernel
      have hl : raw11011step3Labels = raw11011step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11011step3 raw11011step3Labels = mixedMoment B raw11011step4 raw11011step4Labels := by
      have ha : raw11011step4 = raw11011step3 := by apply Matrix.ext; unfold raw11011step4 raw11011step3; decide +kernel
      have hl : raw11011step3Labels = labelEmbedding1 ∘ raw11011step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11011step3 raw11011step3Labels raw11011step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3224 node3224Labels := by rfl

theorem canonical11012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11012 raw11012Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw11012 raw11012Labels = mixedMoment B raw11012step0 raw11012step0Labels := by
      have hz : ∀ j, raw11012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11012step0 = (fun i j => raw11012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11012step0 raw11012; decide +kernel
      have hl : raw11012step0Labels = raw11012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11012 raw11012Labels permutation434 hz
    mixedMoment B raw11012step0 raw11012step0Labels = mixedMoment B raw11012step1 raw11012step1Labels := by
      have hz : ∀ j, raw11012step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11012step1 = (fun i j => raw11012step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11012step1 raw11012step0; decide +kernel
      have hl : raw11012step1Labels = raw11012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11012step0 raw11012step0Labels permutation80 hz
    mixedMoment B raw11012step1 raw11012step1Labels = mixedMoment B raw11012step2 raw11012step2Labels := by
      have ha : raw11012step2 = (fun i j => raw11012step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11012step2 raw11012step1; decide +kernel
      have hl : raw11012step2Labels = raw11012step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11012step1 raw11012step1Labels permutation11 permutation5
    mixedMoment B raw11012step2 raw11012step2Labels = mixedMoment B raw11012step3 raw11012step3Labels := by
      have ha : raw11012step3 = -raw11012step2 := by apply Matrix.ext; change ∀ i j, raw11012step3 i j = -(raw11012step2 i j); unfold raw11012step3 raw11012step2; decide +kernel
      have hl : raw11012step3Labels = raw11012step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11012step3 raw11012step3Labels = mixedMoment B raw11012step4 raw11012step4Labels := by
      have ha : raw11012step4 = raw11012step3 := by apply Matrix.ext; unfold raw11012step4 raw11012step3; decide +kernel
      have hl : raw11012step3Labels = labelEmbedding1 ∘ raw11012step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11012step3 raw11012step3Labels raw11012step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1419 node1419Labels := by rfl

theorem canonical11013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11013 raw11013Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw11013 raw11013Labels = mixedMoment B raw11013step0 raw11013step0Labels := by
      have hz : ∀ j, raw11013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11013step0 = (fun i j => raw11013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11013step0 raw11013; decide +kernel
      have hl : raw11013step0Labels = raw11013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11013 raw11013Labels permutation434 hz
    mixedMoment B raw11013step0 raw11013step0Labels = mixedMoment B raw11013step1 raw11013step1Labels := by
      have ha : raw11013step1 = (fun i j => raw11013step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11013step1 raw11013step0; decide +kernel
      have hl : raw11013step1Labels = raw11013step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11013step0 raw11013step0Labels permutation41 permutation5
    mixedMoment B raw11013step1 raw11013step1Labels = mixedMoment B raw11013step2 raw11013step2Labels := by
      have ha : raw11013step2 = -raw11013step1 := by apply Matrix.ext; change ∀ i j, raw11013step2 i j = -(raw11013step1 i j); unfold raw11013step2 raw11013step1; decide +kernel
      have hl : raw11013step2Labels = raw11013step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11013step2 raw11013step2Labels = mixedMoment B raw11013step3 raw11013step3Labels := by
      have ha : raw11013step3 = raw11013step2 := by apply Matrix.ext; unfold raw11013step3 raw11013step2; decide +kernel
      have hl : raw11013step2Labels = labelEmbedding1 ∘ raw11013step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11013step2 raw11013step2Labels raw11013step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3206 node3206Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical456 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw456 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw456 = injectiveMoment H raw456step0 := by
      have heq : raw456step0 = (fun i j => raw456 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw456 permutation25 permutation6
    _ = injectiveMoment H node198 := by rfl

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

theorem canonical872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw872 = injectiveMoment H node25 := by
  rfl

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

theorem canonical918 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw918 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw918 = injectiveMoment H raw918step0 := by
      have hz : ∀ j, raw918 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw918step0 = (fun i j => raw918 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw918 permutation27 hz
    _ = injectiveMoment H node10 := by rfl

theorem canonical924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw924 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw924 = injectiveMoment H raw924step0 := by
      have heq : raw924step0 = (fun i j => raw924 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw924 permutation4 permutation1
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

theorem canonical8987 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8987 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8987 = injectiveMoment H raw8987step0 := by
      have hz : ∀ j, raw8987 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw8987step0 = (fun i j => raw8987 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8987 permutation27 hz
    injectiveMoment H raw8987step0 = injectiveMoment H raw8987step1 := by
      have hz : ∀ j, raw8987step0 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8987step1 = (fun i j => raw8987step0 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8987step0 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

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

theorem canonical5197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5197 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5197 = injectiveMoment H raw5197step0 := by
      have hz : ∀ j, raw5197 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5197step0 = (fun i j => raw5197 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5197 permutation21 hz
    _ = injectiveMoment H node11 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8215 = injectiveMoment H raw8215step0 := by
      have hz : ∀ i, raw8215 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8215step0 = (fun i j => raw8215 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8215 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

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

theorem canonical199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw199 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw199 = injectiveMoment H raw199step0 := by
      have hz : ∀ j, raw199 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw199step0 = (fun i j => raw199 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw199 permutation15 hz
    _ = injectiveMoment H node9 := by rfl

theorem canonical208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw208 = injectiveMoment H node16 := by
  rfl

theorem canonical211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw211 = injectiveMoment H node8 := by
  rfl

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
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

theorem sound16 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node16 = Sparse.eval value16 (momentVector H) := by
  have heq : pivotMatrix16 = (fun u v => node16 (pivotPermutation16 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node16 = injectiveMoment H pivotMatrix16 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix16 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix16 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (1 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (2 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node16 + (injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value16, value10, value8, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound25 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node25 = Sparse.eval value25 (momentVector H) := by
  have heq : pivotMatrix25 = (fun u v => node25 (pivotPermutation25 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node25 = injectiveMoment H pivotMatrix25 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix25 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix25 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix25 (0 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (0 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix25 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (1 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix25 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (2 : Fin 3) = raw924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical924 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node25 + (injectiveMoment H (mergeFirst pivotMatrix25 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix25 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix25 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value25, value10, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

theorem sound32 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node32 = Sparse.eval value32 (momentVector H) := by
  have hc : momentVector H 35 = injectiveMoment H node32 := rfl
  simp [value32, Sparse.eval, hc]

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

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

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

theorem sound62 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node62 = Sparse.eval value62 (momentVector H) := by
  have heq : pivotMatrix62 = (fun u v => node62 (pivotPermutation62 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node62 = injectiveMoment H pivotMatrix62 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix62 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix62 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node62 + (injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value62, value11, value4, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4048 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4048 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw4048 = injectiveMoment H raw4048step0 := by
      have heq : raw4048step0 = -raw4048 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4048).symm
    injectiveMoment H raw4048step0 = injectiveMoment H raw4048step1 := by
      have heq : raw4048step1 = (fun i j => raw4048step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4048step0 permutation8 permutation3
    _ = injectiveMoment H node31 := by rfl

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

theorem canonical4157 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4157 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw4157 = injectiveMoment H raw4157step0 := by
      have heq : raw4157step0 = raw4157.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4157).symm
    injectiveMoment H raw4157step0 = injectiveMoment H raw4157step1 := by
      have heq : raw4157step1 = -raw4157step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4157step0).symm
    injectiveMoment H raw4157step1 = injectiveMoment H raw4157step2 := by
      have heq : raw4157step2 = (fun i j => raw4157step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4157step1 permutation8 permutation3
    _ = injectiveMoment H node32 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical781 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw781 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw781 = injectiveMoment H raw781step0 := by
      have heq : raw781step0 = -raw781 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw781).symm
    injectiveMoment H raw781step0 = injectiveMoment H raw781step1 := by
      have heq : raw781step1 = (fun i j => raw781step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw781step0 permutation11 permutation8
    _ = injectiveMoment H node181 := by rfl

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

theorem canonical7685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7685 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7685 = injectiveMoment H raw7685step0 := by
      have hz : ∀ j, raw7685 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7685step0 = (fun i j => raw7685 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7685 permutation27 hz
    injectiveMoment H raw7685step0 = injectiveMoment H raw7685step1 := by
      have heq : raw7685step1 = (fun i j => raw7685step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7685step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical212
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6789 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6789 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw6789 = injectiveMoment H raw6789step0 := by
      have heq : raw6789step0 = -raw6789 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6789).symm
    injectiveMoment H raw6789step0 = injectiveMoment H raw6789step1 := by
      have heq : raw6789step1 = (fun i j => raw6789step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6789step0 permutation8 permutation3
    _ = injectiveMoment H node52 := by rfl

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

theorem canonical4160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4160 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4160 = injectiveMoment H raw4160step0 := by
      have heq : raw4160step0 = -raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4160).symm
    injectiveMoment H raw4160step0 = injectiveMoment H raw4160step1 := by
      have heq : raw4160step1 = (fun i j => raw4160step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4160step0 permutation7 permutation5
    _ = injectiveMoment H node62 := by rfl

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

theorem sound181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node181 = Sparse.eval value181 (momentVector H) := by
  have heq : pivotMatrix181 = (fun u v => node181 (pivotPermutation181 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node181 = injectiveMoment H pivotMatrix181 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix181 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix181 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (0 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (1 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (2 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node181 + (injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value181, value56, value62, value63, Sparse.eval] at hc ⊢
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

theorem sound198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node198 = Sparse.eval value198 (momentVector H) := by
  have hc : momentVector H 54 = injectiveMoment H node198 := rfl
  simp [value198, Sparse.eval, hc]

theorem sound201 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node201 = Sparse.eval value201 (momentVector H) := by
  have heq : pivotMatrix201 = (fun u v => node201 (pivotPermutation201 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node201 = injectiveMoment H pivotMatrix201 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix201 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix201 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix201 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix201 (0 : Fin 3) = raw6789 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6789 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix201 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix201 (1 : Fin 3) = raw4157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4157 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix201 (2 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix201 (2 : Fin 3) = raw4048 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4048 hH).trans (sound31 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node201 + (injectiveMoment H (mergeFirst pivotMatrix201 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix201 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix201 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value201, value31, value32, value52, Sparse.eval] at hc ⊢
  linarith

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

theorem sound206 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node206 = Sparse.eval value206 (momentVector H) := by
  have heq : pivotMatrix206 = (fun u v => node206 (pivotPermutation206 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node206 = injectiveMoment H pivotMatrix206 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix206 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix206 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix206 (0 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix206 (0 : Fin 3) = raw2860 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2860 hH).trans (sound40 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix206 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix206 (1 : Fin 3) = raw4157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4157 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix206 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix206 (2 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node206 + (injectiveMoment H (mergeFirst pivotMatrix206 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix206 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix206 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value206, value32, value36, value40, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical7678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7678 = injectiveMoment H node65 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node251 node251Labels = Sparse.eval singlePairValue251 (familyPairVector B) := by
  have hp := single_label_three B hB node251
  have hl : node251Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node251 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node251 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node251 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node251 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node251 (EqualityPatterns.family3.label 1) = PairSemantics.raw909 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node251 PairSemantics.raw909
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical909 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node251 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node251 (EqualityPatterns.family3.label 2) = PairSemantics.raw8987 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node251 PairSemantics.raw8987
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8987 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node251 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node251 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node251 PairSemantics.raw872
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node251 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value198 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node251 (EqualityPatterns.family3.label 4) = PairSemantics.raw456 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node251 PairSemantics.raw456
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical456 hH).trans (PairSemantics.sound198 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue251, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value25, PairSemantics.value198, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node404 node404Labels = Sparse.eval singlePairValue404 (familyPairVector B) := by
  have hp := single_label_three B hB node404
  have hl : node404Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node404 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 1) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node404 PairSemantics.raw5197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node404 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node404 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value181 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 4) = PairSemantics.raw781 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node404 PairSemantics.raw781; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical781 hH).trans (PairSemantics.sound181 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue404, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value65, PairSemantics.value181, Sparse.eval] at hp ⊢
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

theorem canonical116 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw116 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw116 = injectiveMoment H raw116step0 := by
      have heq : raw116step0 = (fun i j => raw116 (permutation26 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw116 permutation26 permutation6
    _ = injectiveMoment H node201 := by rfl

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

theorem singlePair98 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node98 node98Labels = Sparse.eval singlePairValue98 (familyPairVector B) := by
  have hp := single_label_three B hB node98
  have hl : node98Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node98 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node98 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node98 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node98 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node98 (EqualityPatterns.family3.label 1) = PairSemantics.raw909 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node98 PairSemantics.raw909; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical909 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node98 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node98 (EqualityPatterns.family3.label 2) = PairSemantics.raw7685 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node98 PairSemantics.raw7685; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7685 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node98 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node98 (EqualityPatterns.family3.label 3) = PairSemantics.raw199 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node98 PairSemantics.raw199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical199 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node98 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value201 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node98 (EqualityPatterns.family3.label 4) = PairSemantics.raw116 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node98 PairSemantics.raw116; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical116 hH).trans (PairSemantics.sound201 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue98, PairSemantics.value0, PairSemantics.value9, PairSemantics.value10, PairSemantics.value11, PairSemantics.value201, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical129 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw129 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw129 = injectiveMoment H raw129step0 := by
      have heq : raw129step0 = (fun i j => raw129 (permutation30 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw129 permutation30 permutation6
    _ = injectiveMoment H node206 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair111 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node111 node111Labels = Sparse.eval singlePairValue111 (familyPairVector B) := by
  have hp := single_label_three B hB node111
  have hl : node111Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node111 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node111 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node111 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node111 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node111 (EqualityPatterns.family3.label 1) = PairSemantics.raw918 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node111 PairSemantics.raw918; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical918 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node111 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node111 (EqualityPatterns.family3.label 2) = PairSemantics.raw7705 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node111 PairSemantics.raw7705; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7705 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node111 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node111 (EqualityPatterns.family3.label 3) = PairSemantics.raw208 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node111 PairSemantics.raw208; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical208 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node111 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value206 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node111 (EqualityPatterns.family3.label 4) = PairSemantics.raw129 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node111 PairSemantics.raw129; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical129 hH).trans (PairSemantics.sound206 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue111, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value16, PairSemantics.value206, Sparse.eval] at hp ⊢
  linarith only [hp]

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

theorem singleton1419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1419 node1419Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node98 node98Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw140 singletonSmall1419
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1419) = raw140Labels := by decide +kernel
  rw [hl, canonical140 B hB] at h
  have hc0 : mixedMoment B raw140 (Fin.cases (0 : Fin 1) singletonSmall1419) =
      mixedMoment B node98 node98Labels := by
    have ha : raw140 = raw141 := by apply Matrix.ext; unfold raw140 raw141; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1419 = raw141Labels := by decide +kernel
    rw [ha, hj, canonical141 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton1442 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1442 node1442Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node111 node111Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw154 singletonSmall1442
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1442) = raw154Labels := by decide +kernel
  rw [hl, canonical154 B hB] at h
  have hc0 : mixedMoment B raw154 (Fin.cases (0 : Fin 1) singletonSmall1442) =
      mixedMoment B node111 node111Labels := by
    have ha : raw154 = raw155 := by apply Matrix.ext; unfold raw154 raw155; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1442 = raw155Labels := by decide +kernel
    rw [ha, hj, canonical155 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3102 node3102Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node404 node404Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw382 singletonSmall3102
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3102) = raw382Labels := by decide +kernel
  rw [hl, canonical382 B hB] at h
  have hc0 : mixedMoment B raw382 (Fin.cases (0 : Fin 1) singletonSmall3102) =
      mixedMoment B node404 node404Labels := by
    have ha : raw382 = raw383 := by apply Matrix.ext; unfold raw382 raw383; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3102 = raw383Labels := by decide +kernel
    rw [ha, hj, canonical383 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3187 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3187 node3187Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node251 node251Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw436 singletonSmall3187
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3187) = raw436Labels := by decide +kernel
  rw [hl, canonical436 B hB] at h
  have hc0 : mixedMoment B raw436 (Fin.cases (0 : Fin 1) singletonSmall3187) =
      mixedMoment B node251 node251Labels := by
    have ha : raw436 = raw437 := by apply Matrix.ext; unfold raw436 raw437; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3187 = raw437Labels := by decide +kernel
    rw [ha, hj, canonical437 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem sound3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3054 node3054Labels = Sparse.eval nodeValue3054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3054) = mixedMoment B node3054 node3054Labels := rfl
  simpa [nodeValue3054, Sparse.eval] using hc.symm

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

theorem sound98 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node98 node98Labels = Sparse.eval nodeValue98 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue98 (familyPairVector B) := singlePair98 B _hB
    _ = _ := by norm_num [singlePairValue98, nodeValue98, Sparse.eval, mixedVector] <;> ring

theorem sound111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node111 node111Labels = Sparse.eval nodeValue111 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue111 (familyPairVector B) := singlePair111 B _hB
    _ = _ := by norm_num [singlePairValue111, nodeValue111, Sparse.eval, mixedVector] <;> ring

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

theorem sound1406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1406 node1406Labels = Sparse.eval nodeValue1406 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1406) = mixedMoment B node1406 node1406Labels := rfl
  simpa [nodeValue1406, Sparse.eval] using hc.symm

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

theorem sound1419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1419 node1419Labels = Sparse.eval nodeValue1419 (mixedVector B) := by
  have h := singleton1419 B _hB
  rw [sound98 B _hB _hF] at h
  norm_num [nodeValue1419, nodeValue98, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1442 node1442Labels = Sparse.eval nodeValue1442 (mixedVector B) := by
  have h := singleton1442 B _hB
  rw [sound111 B _hB _hF] at h
  norm_num [nodeValue1442, nodeValue111, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node251 node251Labels = Sparse.eval nodeValue251 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue251 (familyPairVector B) := singlePair251 B _hB
    _ = _ := by norm_num [singlePairValue251, nodeValue251, Sparse.eval, mixedVector] <;> ring

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

theorem sound2092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2092 node2092Labels = Sparse.eval nodeValue2092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2092) = mixedMoment B node2092 node2092Labels := rfl
  simpa [nodeValue2092, Sparse.eval] using hc.symm

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

theorem sound2255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2255 node2255Labels = Sparse.eval nodeValue2255 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2255) = mixedMoment B node2255 node2255Labels := rfl
  simpa [nodeValue2255, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3039 node3039Labels = Sparse.eval nodeValue3039 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3039) = mixedMoment B node3039 node3039Labels := rfl
  simpa [nodeValue3039, Sparse.eval] using hc.symm

theorem sound3055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3055 node3055Labels = Sparse.eval nodeValue3055 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3055) = mixedMoment B node3055 node3055Labels := rfl
  simpa [nodeValue3055, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node404 node404Labels = Sparse.eval nodeValue404 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue404 (familyPairVector B) := singlePair404 B _hB
    _ = _ := by
      norm_num [singlePairValue404, nodeValue404, Sparse.eval, mixedVector]
      ring

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

theorem sound3102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3102 node3102Labels = Sparse.eval nodeValue3102 (mixedVector B) := by
  have h := singleton3102 B _hB
  rw [sound404 B _hB _hF] at h
  norm_num [nodeValue3102, nodeValue404, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3180 node3180Labels = Sparse.eval nodeValue3180 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3180) = mixedMoment B node3180 node3180Labels := rfl
  simpa [nodeValue3180, Sparse.eval] using hc.symm

theorem sound3187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3187 node3187Labels = Sparse.eval nodeValue3187 (mixedVector B) := by
  have h := singleton3187 B _hB
  rw [sound251 B _hB _hF] at h
  norm_num [nodeValue3187, nodeValue251, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3229 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3229 node3229Labels = 0 := by
  exact mixedMoment_order_one B hB node3229 node3229Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3230 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3230 node3230Labels = 0 := by
  exact mixedMoment_order_one B hB node3230 node3230Labels 2
    (by decide +kernel) (by decide +kernel)

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

theorem sound3202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3202 node3202Labels = Sparse.eval nodeValue3202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3202) = mixedMoment B node3202 node3202Labels := rfl
  simpa [nodeValue3202, Sparse.eval] using hc.symm

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

theorem sound3229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3229 node3229Labels = Sparse.eval nodeValue3229 (mixedVector B) := by
  simpa only [nodeValue3229, Sparse.eval_nil] using zero3229 B _hB _hF

theorem sound3230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3230 node3230Labels = Sparse.eval nodeValue3230 (mixedVector B) := by
  simpa only [nodeValue3230, Sparse.eval_nil] using zero3230 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources20
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq646 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm646 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA646 + difference 0 1) (sourceB646 + difference 1 0) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA646 + difference 0 1) (sourceB646 + difference 1 0) sourceC646) = raw7949 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw7949; decide +kernel
    rw [ha]
    exact (canonical7949 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA646 + difference 0 2) (sourceB646 + difference 2 0) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA646 + difference 0 2) (sourceB646 + difference 2 0) sourceC646) = raw10996 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw10996; decide +kernel
    rw [ha]
    exact (canonical10996 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA646 + difference 0 3) (sourceB646 + difference 3 0) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA646 + difference 0 3) (sourceB646 + difference 3 0) sourceC646) = raw9947 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw9947; decide +kernel
    rw [ha]
    exact (canonical9947 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA646 + difference 0 4) (sourceB646 + difference 4 0) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA646 + difference 0 4) (sourceB646 + difference 4 0) sourceC646) = raw9709 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw9709; decide +kernel
    rw [ha]
    exact (canonical9709 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA646 + difference 0 5) (sourceB646 + difference 5 0) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA646 + difference 0 5) (sourceB646 + difference 5 0) sourceC646) = raw10997 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw10997; decide +kernel
    rw [ha]
    exact (canonical10997 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA646 + difference 1 0) (sourceB646 + difference 0 1) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA646 + difference 1 0) (sourceB646 + difference 0 1) sourceC646) = raw10998 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw10998; decide +kernel
    rw [ha]
    exact (canonical10998 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA646 + difference 1 2) (sourceB646 + difference 2 1) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA646 + difference 1 2) (sourceB646 + difference 2 1) sourceC646) = raw10999 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw10999; decide +kernel
    rw [ha]
    exact (canonical10999 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA646 + difference 1 3) (sourceB646 + difference 3 1) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA646 + difference 1 3) (sourceB646 + difference 3 1) sourceC646) = raw11000 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11000; decide +kernel
    rw [ha]
    exact (canonical11000 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA646 + difference 1 4) (sourceB646 + difference 4 1) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA646 + difference 1 4) (sourceB646 + difference 4 1) sourceC646) = raw11001 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11001; decide +kernel
    rw [ha]
    exact (canonical11001 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA646 + difference 1 5) (sourceB646 + difference 5 1) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA646 + difference 1 5) (sourceB646 + difference 5 1) sourceC646) = raw11002 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11002; decide +kernel
    rw [ha]
    exact (canonical11002 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA646 + difference 2 0) (sourceB646 + difference 0 2) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA646 + difference 2 0) (sourceB646 + difference 0 2) sourceC646) = raw11003 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11003; decide +kernel
    rw [ha]
    exact (canonical11003 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA646 + difference 2 1) (sourceB646 + difference 1 2) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA646 + difference 2 1) (sourceB646 + difference 1 2) sourceC646) = raw5746 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw5746; decide +kernel
    rw [ha]
    exact (canonical5746 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA646 + difference 2 3) (sourceB646 + difference 3 2) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA646 + difference 2 3) (sourceB646 + difference 3 2) sourceC646) = raw11004 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11004; decide +kernel
    rw [ha]
    exact (canonical11004 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA646 + difference 2 4) (sourceB646 + difference 4 2) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA646 + difference 2 4) (sourceB646 + difference 4 2) sourceC646) = raw11005 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11005; decide +kernel
    rw [ha]
    exact (canonical11005 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA646 + difference 2 5) (sourceB646 + difference 5 2) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA646 + difference 2 5) (sourceB646 + difference 5 2) sourceC646) = raw5725 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw5725; decide +kernel
    rw [ha]
    exact (canonical5725 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA646 + difference 3 0) (sourceB646 + difference 0 3) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA646 + difference 3 0) (sourceB646 + difference 0 3) sourceC646) = raw11006 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11006; decide +kernel
    rw [ha]
    exact (canonical11006 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA646 + difference 3 1) (sourceB646 + difference 1 3) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA646 + difference 3 1) (sourceB646 + difference 1 3) sourceC646) = raw5745 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw5745; decide +kernel
    rw [ha]
    exact (canonical5745 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA646 + difference 3 2) (sourceB646 + difference 2 3) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA646 + difference 3 2) (sourceB646 + difference 2 3) sourceC646) = raw11007 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11007; decide +kernel
    rw [ha]
    exact (canonical11007 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA646 + difference 3 4) (sourceB646 + difference 4 3) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA646 + difference 3 4) (sourceB646 + difference 4 3) sourceC646) = raw11008 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11008; decide +kernel
    rw [ha]
    exact (canonical11008 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA646 + difference 3 5) (sourceB646 + difference 5 3) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA646 + difference 3 5) (sourceB646 + difference 5 3) sourceC646) = raw5724 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw5724; decide +kernel
    rw [ha]
    exact (canonical5724 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA646 + difference 4 0) (sourceB646 + difference 0 4) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1442) := by
    have ha : (tripleCharges (sourceA646 + difference 4 0) (sourceB646 + difference 0 4) sourceC646) = raw11009 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11009; decide +kernel
    rw [ha]
    exact (canonical11009 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA646 + difference 4 1) (sourceB646 + difference 1 4) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA646 + difference 4 1) (sourceB646 + difference 1 4) sourceC646) = raw9954 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw9954; decide +kernel
    rw [ha]
    exact (canonical9954 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA646 + difference 4 2) (sourceB646 + difference 2 4) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3210) := by
    have ha : (tripleCharges (sourceA646 + difference 4 2) (sourceB646 + difference 2 4) sourceC646) = raw11010 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11010; decide +kernel
    rw [ha]
    exact (canonical11010 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA646 + difference 4 3) (sourceB646 + difference 3 4) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3210) := by
    have ha : (tripleCharges (sourceA646 + difference 4 3) (sourceB646 + difference 3 4) sourceC646) = raw9944 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw9944; decide +kernel
    rw [ha]
    exact (canonical9944 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA646 + difference 4 5) (sourceB646 + difference 5 4) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3224) := by
    have ha : (tripleCharges (sourceA646 + difference 4 5) (sourceB646 + difference 5 4) sourceC646) = raw11011 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11011; decide +kernel
    rw [ha]
    exact (canonical11011 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA646 + difference 5 0) (sourceB646 + difference 0 5) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA646 + difference 5 0) (sourceB646 + difference 0 5) sourceC646) = raw11012 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11012; decide +kernel
    rw [ha]
    exact (canonical11012 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA646 + difference 5 1) (sourceB646 + difference 1 5) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA646 + difference 5 1) (sourceB646 + difference 1 5) sourceC646) = raw9716 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw9716; decide +kernel
    rw [ha]
    exact (canonical9716 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA646 + difference 5 2) (sourceB646 + difference 2 5) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA646 + difference 5 2) (sourceB646 + difference 2 5) sourceC646) = raw11013 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11013; decide +kernel
    rw [ha]
    exact (canonical11013 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA646 + difference 5 3) (sourceB646 + difference 3 5) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA646 + difference 5 3) (sourceB646 + difference 3 5) sourceC646) = raw10178 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw10178; decide +kernel
    rw [ha]
    exact (canonical10178 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA646 + difference 5 4) (sourceB646 + difference 4 5) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3187) := by
    have ha : (tripleCharges (sourceA646 + difference 5 4) (sourceB646 + difference 4 5) sourceC646) = raw9705 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw9705; decide +kernel
    rw [ha]
    exact (canonical9705 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA646 sourceB646 sourceC646
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm646, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck555 : Integer.Sparse.reindex keyMap MixedData.row555 = numericRow555 := by decide +kernel

theorem numericCheck555 (x : Master → ℝ) : Integer.Sparse.eval numericRow555 x =
    (720 : ℝ) * reducedSource555 x := by
  norm_num [numericRow555, reducedSource555, Integer.Sparse.eval, Sparse.eval, nodeValue1406, nodeValue1408, nodeValue1419, nodeValue1442, nodeValue2092, nodeValue2113, nodeValue2255, nodeValue3039, nodeValue3054, nodeValue3055, nodeValue3102, nodeValue3180, nodeValue3187, nodeValue3202, nodeValue3206, nodeValue3210, nodeValue3222, nodeValue3224, nodeValue3227, nodeValue3229, nodeValue3230]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero555 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource555 (mixedVector B) = 0 := by
  have h1406 : mixedVector B (Sum.inr 1406) = Sparse.eval nodeValue1406 (mixedVector B) := by
    change mixedMoment B node1406 node1406Labels = _
    exact sound1406 B hB hF
  have h1408 : mixedVector B (Sum.inr 1408) = Sparse.eval nodeValue1408 (mixedVector B) := by
    change mixedMoment B node1408 node1408Labels = _
    exact sound1408 B hB hF
  have h1419 : mixedVector B (Sum.inr 1419) = Sparse.eval nodeValue1419 (mixedVector B) := by
    change mixedMoment B node1419 node1419Labels = _
    exact sound1419 B hB hF
  have h1442 : mixedVector B (Sum.inr 1442) = Sparse.eval nodeValue1442 (mixedVector B) := by
    change mixedMoment B node1442 node1442Labels = _
    exact sound1442 B hB hF
  have h2092 : mixedVector B (Sum.inr 2092) = Sparse.eval nodeValue2092 (mixedVector B) := by
    change mixedMoment B node2092 node2092Labels = _
    exact sound2092 B hB hF
  have h2113 : mixedVector B (Sum.inr 2113) = Sparse.eval nodeValue2113 (mixedVector B) := by
    change mixedMoment B node2113 node2113Labels = _
    exact sound2113 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3102 : mixedVector B (Sum.inr 3102) = Sparse.eval nodeValue3102 (mixedVector B) := by
    change mixedMoment B node3102 node3102Labels = _
    exact sound3102 B hB hF
  have h3180 : mixedVector B (Sum.inr 3180) = Sparse.eval nodeValue3180 (mixedVector B) := by
    change mixedMoment B node3180 node3180Labels = _
    exact sound3180 B hB hF
  have h3187 : mixedVector B (Sum.inr 3187) = Sparse.eval nodeValue3187 (mixedVector B) := by
    change mixedMoment B node3187 node3187Labels = _
    exact sound3187 B hB hF
  have h3202 : mixedVector B (Sum.inr 3202) = Sparse.eval nodeValue3202 (mixedVector B) := by
    change mixedMoment B node3202 node3202Labels = _
    exact sound3202 B hB hF
  have h3206 : mixedVector B (Sum.inr 3206) = Sparse.eval nodeValue3206 (mixedVector B) := by
    change mixedMoment B node3206 node3206Labels = _
    exact sound3206_e B hB hF
  have h3210 : mixedVector B (Sum.inr 3210) = Sparse.eval nodeValue3210 (mixedVector B) := by
    change mixedMoment B node3210 node3210Labels = _
    exact sound3210_e B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h3224 : mixedVector B (Sum.inr 3224) = Sparse.eval nodeValue3224 (mixedVector B) := by
    change mixedMoment B node3224 node3224Labels = _
    exact sound3224 B hB hF
  have h3227 : mixedVector B (Sum.inr 3227) = Sparse.eval nodeValue3227 (mixedVector B) := by
    change mixedMoment B node3227 node3227Labels = _
    exact sound3227_e B hB hF
  have h3229 : mixedVector B (Sum.inr 3229) = Sparse.eval nodeValue3229 (mixedVector B) := by
    change mixedMoment B node3229 node3229Labels = _
    exact sound3229 B hB hF
  have h3230 : mixedVector B (Sum.inr 3230) = Sparse.eval nodeValue3230 (mixedVector B) := by
    change mixedMoment B node3230 node3230Labels = _
    exact sound3230 B hB hF
  simpa only [sourceForm646, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1406, h1408, h1419, h1442, h2092, h2113, h2255, h3039, h3054, h3055, h3102, h3180, h3187, h3202, h3206, h3210, h3222, h3224, h3227, h3229, h3230, reducedSource555] using sourceEq646 B hB

theorem rowSound555_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row555 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck555, numericCheck555, reducedZero555 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e_oai
