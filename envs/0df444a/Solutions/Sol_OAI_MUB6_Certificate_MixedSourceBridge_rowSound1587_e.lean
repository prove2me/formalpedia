-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:25:13.328205+00:00
-- url     : https://prove2.me/submissions/5e64db67-2655-4a2e-8739-9e71dd6d5bd2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5167_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5292_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1293 raw1293Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw1293 raw1293Labels = mixedMoment B raw1293step0 raw1293step0Labels := by
      have ha : raw1293step0 = (fun i j => raw1293 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1293step0 raw1293; decide +kernel
      have hl : raw1293step0Labels = raw1293Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1293 raw1293Labels permutation32 permutation4
    mixedMoment B raw1293step0 raw1293step0Labels = mixedMoment B raw1293step1 raw1293step1Labels := by
      have ha : raw1293step1 = raw1293step0 := by apply Matrix.ext; unfold raw1293step1 raw1293step0; decide +kernel
      have hl : raw1293step0Labels = labelEmbedding7 ∘ raw1293step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1293step0 raw1293step0Labels raw1293step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical1294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1294 raw1294Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw1294 raw1294Labels = mixedMoment B raw1294step0 raw1294step0Labels := by
      have ha : raw1294step0 = (fun i j => raw1294 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1294step0 raw1294; decide +kernel
      have hl : raw1294step0Labels = raw1294Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1294 raw1294Labels permutation32 permutation4
    _ = mixedMoment B node1079 node1079Labels := by rfl

theorem canonical1295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1295 raw1295Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw1295 raw1295Labels = mixedMoment B raw1295step0 raw1295step0Labels := by
      have ha : raw1295step0 = (fun i j => raw1295 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1295step0 raw1295; decide +kernel
      have hl : raw1295step0Labels = raw1295Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1295 raw1295Labels permutation32 permutation6
    mixedMoment B raw1295step0 raw1295step0Labels = mixedMoment B raw1295step1 raw1295step1Labels := by
      have ha : raw1295step1 = -raw1295step0 := by apply Matrix.ext; change ∀ i j, raw1295step1 i j = -(raw1295step0 i j); unfold raw1295step1 raw1295step0; decide +kernel
      have hl : raw1295step1Labels = raw1295step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1295step1 raw1295step1Labels = mixedMoment B raw1295step2 raw1295step2Labels := by
      have ha : raw1295step2 = raw1295step1 := by apply Matrix.ext; unfold raw1295step2 raw1295step1; decide +kernel
      have hl : raw1295step1Labels = labelEmbedding1 ∘ raw1295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1295step1 raw1295step1Labels raw1295step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical167
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21485 raw21485Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw21485 raw21485Labels = mixedMoment B raw21485step0 raw21485step0Labels := by
      have hz : ∀ j, raw21485 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21485step0 = (fun i j => raw21485 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21485step0 raw21485; decide +kernel
      have hl : raw21485step0Labels = raw21485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21485 raw21485Labels permutation434 hz
    mixedMoment B raw21485step0 raw21485step0Labels = mixedMoment B raw21485step1 raw21485step1Labels := by
      have ha : raw21485step1 = (fun i j => raw21485step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21485step1 raw21485step0; decide +kernel
      have hl : raw21485step1Labels = raw21485step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21485step0 raw21485step0Labels permutation34 permutation3
    mixedMoment B raw21485step1 raw21485step1Labels = mixedMoment B raw21485step2 raw21485step2Labels := by
      have ha : raw21485step2 = raw21485step1 := by apply Matrix.ext; unfold raw21485step2 raw21485step1; decide +kernel
      have hl : raw21485step1Labels = labelEmbedding6 ∘ raw21485step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21485step1 raw21485step1Labels raw21485step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical21489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21489 raw21489Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw21489 raw21489Labels = mixedMoment B raw21489step0 raw21489step0Labels := by
      have hz : ∀ j, raw21489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21489step0 = (fun i j => raw21489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21489step0 raw21489; decide +kernel
      have hl : raw21489step0Labels = raw21489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21489 raw21489Labels permutation346 hz
    mixedMoment B raw21489step0 raw21489step0Labels = mixedMoment B raw21489step1 raw21489step1Labels := by
      have ha : raw21489step1 = (fun i j => raw21489step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21489step1 raw21489step0; decide +kernel
      have hl : raw21489step1Labels = raw21489step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21489step0 raw21489step0Labels permutation34 permutation3
    mixedMoment B raw21489step1 raw21489step1Labels = mixedMoment B raw21489step2 raw21489step2Labels := by
      have ha : raw21489step2 = raw21489step1 := by apply Matrix.ext; unfold raw21489step2 raw21489step1; decide +kernel
      have hl : raw21489step1Labels = labelEmbedding6 ∘ raw21489step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21489step1 raw21489step1Labels raw21489step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

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

theorem canonical2268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2268 raw2268Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw2268 raw2268Labels = mixedMoment B raw2268step0 raw2268step0Labels := by
      have ha : raw2268step0 = (fun i j => raw2268 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2268step0 raw2268; decide +kernel
      have hl : raw2268step0Labels = raw2268Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2268 raw2268Labels permutation152 permutation4
    mixedMoment B raw2268step0 raw2268step0Labels = mixedMoment B raw2268step1 raw2268step1Labels := by
      have ha : raw2268step1 = raw2268step0 := by apply Matrix.ext; unfold raw2268step1 raw2268step0; decide +kernel
      have hl : raw2268step0Labels = labelEmbedding7 ∘ raw2268step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2268step0 raw2268step0Labels raw2268step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical2269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2269 raw2269Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw2269 raw2269Labels = mixedMoment B raw2269step0 raw2269step0Labels := by
      have ha : raw2269step0 = (fun i j => raw2269 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2269step0 raw2269; decide +kernel
      have hl : raw2269step0Labels = raw2269Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2269 raw2269Labels permutation152 permutation4
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical2270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2270 raw2270Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw2270 raw2270Labels = mixedMoment B raw2270step0 raw2270step0Labels := by
      have ha : raw2270step0 = (fun i j => raw2270 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2270step0 raw2270; decide +kernel
      have hl : raw2270step0Labels = raw2270Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2270 raw2270Labels permutation158 permutation6
    mixedMoment B raw2270step0 raw2270step0Labels = mixedMoment B raw2270step1 raw2270step1Labels := by
      have ha : raw2270step1 = -raw2270step0 := by apply Matrix.ext; change ∀ i j, raw2270step1 i j = -(raw2270step0 i j); unfold raw2270step1 raw2270step0; decide +kernel
      have hl : raw2270step1Labels = raw2270step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2270step1 raw2270step1Labels = mixedMoment B raw2270step2 raw2270step2Labels := by
      have ha : raw2270step2 = raw2270step1 := by apply Matrix.ext; unfold raw2270step2 raw2270step1; decide +kernel
      have hl : raw2270step1Labels = labelEmbedding1 ∘ raw2270step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2270step1 raw2270step1Labels raw2270step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23229 raw23229Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw23229 raw23229Labels = mixedMoment B raw23229step0 raw23229step0Labels := by
      have hz : ∀ j, raw23229 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23229step0 = (fun i j => raw23229 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23229step0 raw23229; decide +kernel
      have hl : raw23229step0Labels = raw23229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23229 raw23229Labels permutation434 hz
    mixedMoment B raw23229step0 raw23229step0Labels = mixedMoment B raw23229step1 raw23229step1Labels := by
      have ha : raw23229step1 = (fun i j => raw23229step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23229step1 raw23229step0; decide +kernel
      have hl : raw23229step1Labels = raw23229step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23229step0 raw23229step0Labels permutation36 permutation3
    mixedMoment B raw23229step1 raw23229step1Labels = mixedMoment B raw23229step2 raw23229step2Labels := by
      have ha : raw23229step2 = raw23229step1 := by apply Matrix.ext; unfold raw23229step2 raw23229step1; decide +kernel
      have hl : raw23229step1Labels = labelEmbedding6 ∘ raw23229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23229step1 raw23229step1Labels raw23229step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical23233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23233 raw23233Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw23233 raw23233Labels = mixedMoment B raw23233step0 raw23233step0Labels := by
      have hz : ∀ j, raw23233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23233step0 = (fun i j => raw23233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23233step0 raw23233; decide +kernel
      have hl : raw23233step0Labels = raw23233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23233 raw23233Labels permutation346 hz
    mixedMoment B raw23233step0 raw23233step0Labels = mixedMoment B raw23233step1 raw23233step1Labels := by
      have ha : raw23233step1 = (fun i j => raw23233step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23233step1 raw23233step0; decide +kernel
      have hl : raw23233step1Labels = raw23233step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23233step0 raw23233step0Labels permutation36 permutation3
    mixedMoment B raw23233step1 raw23233step1Labels = mixedMoment B raw23233step2 raw23233step2Labels := by
      have ha : raw23233step2 = raw23233step1 := by apply Matrix.ext; unfold raw23233step2 raw23233step1; decide +kernel
      have hl : raw23233step1Labels = labelEmbedding6 ∘ raw23233step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23233step1 raw23233step1Labels raw23233step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical197
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25242 raw25242Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw25242 raw25242Labels = mixedMoment B raw25242step0 raw25242step0Labels := by
      have hz : ∀ j, raw25242 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25242step0 = (fun i j => raw25242 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25242step0 raw25242; decide +kernel
      have hl : raw25242step0Labels = raw25242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25242 raw25242Labels permutation346 hz
    mixedMoment B raw25242step0 raw25242step0Labels = mixedMoment B raw25242step1 raw25242step1Labels := by
      have ha : raw25242step1 = (fun i j => raw25242step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25242step1 raw25242step0; decide +kernel
      have hl : raw25242step1Labels = raw25242step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25242step0 raw25242step0Labels permutation35 permutation3
    mixedMoment B raw25242step1 raw25242step1Labels = mixedMoment B raw25242step2 raw25242step2Labels := by
      have ha : raw25242step2 = raw25242step1 := by apply Matrix.ext; unfold raw25242step2 raw25242step1; decide +kernel
      have hl : raw25242step1Labels = labelEmbedding6 ∘ raw25242step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25242step1 raw25242step1Labels raw25242step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical25246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25246 raw25246Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25246 raw25246Labels = mixedMoment B raw25246step0 raw25246step0Labels := by
      have hz : ∀ j, raw25246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25246step0 = (fun i j => raw25246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25246step0 raw25246; decide +kernel
      have hl : raw25246step0Labels = raw25246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25246 raw25246Labels permutation346 hz
    mixedMoment B raw25246step0 raw25246step0Labels = mixedMoment B raw25246step1 raw25246step1Labels := by
      have ha : raw25246step1 = (fun i j => raw25246step0 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25246step1 raw25246step0; decide +kernel
      have hl : raw25246step1Labels = raw25246step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25246step0 raw25246step0Labels permutation49 permutation3
    mixedMoment B raw25246step1 raw25246step1Labels = mixedMoment B raw25246step2 raw25246step2Labels := by
      have ha : raw25246step2 = raw25246step1 := by apply Matrix.ext; unfold raw25246step2 raw25246step1; decide +kernel
      have hl : raw25246step1Labels = labelEmbedding6 ∘ raw25246step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25246step1 raw25246step1Labels raw25246step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical25247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25247 raw25247Labels = mixedMoment B node4100 node4100Labels := by
  calc
    mixedMoment B raw25247 raw25247Labels = mixedMoment B raw25247step0 raw25247step0Labels := by
      have ha : raw25247step0 = (fun i j => raw25247 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25247step0 raw25247; decide +kernel
      have hl : raw25247step0Labels = raw25247Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25247 raw25247Labels permutation164 permutation3
    mixedMoment B raw25247step0 raw25247step0Labels = mixedMoment B raw25247step1 raw25247step1Labels := by
      have ha : raw25247step1 = raw25247step0 := by apply Matrix.ext; unfold raw25247step1 raw25247step0; decide +kernel
      have hl : raw25247step0Labels = labelEmbedding6 ∘ raw25247step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25247step0 raw25247step0Labels raw25247step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4100 node4100Labels := by rfl

theorem canonical25248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25248 raw25248Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw25248 raw25248Labels = mixedMoment B raw25248step0 raw25248step0Labels := by
      have ha : raw25248step0 = (fun i j => raw25248 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25248step0 raw25248; decide +kernel
      have hl : raw25248step0Labels = raw25248Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25248 raw25248Labels permutation164 permutation3
    mixedMoment B raw25248step0 raw25248step0Labels = mixedMoment B raw25248step1 raw25248step1Labels := by
      have ha : raw25248step1 = raw25248step0 := by apply Matrix.ext; unfold raw25248step1 raw25248step0; decide +kernel
      have hl : raw25248step0Labels = labelEmbedding6 ∘ raw25248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25248step0 raw25248step0Labels raw25248step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4344 node4344Labels := by rfl

theorem canonical25249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25249 raw25249Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw25249 raw25249Labels = mixedMoment B raw25249step0 raw25249step0Labels := by
      have ha : raw25249step0 = (fun i j => raw25249 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25249step0 raw25249; decide +kernel
      have hl : raw25249step0Labels = raw25249Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25249 raw25249Labels permutation224 permutation3
    mixedMoment B raw25249step0 raw25249step0Labels = mixedMoment B raw25249step1 raw25249step1Labels := by
      have ha : raw25249step1 = raw25249step0 := by apply Matrix.ext; unfold raw25249step1 raw25249step0; decide +kernel
      have hl : raw25249step0Labels = labelEmbedding6 ∘ raw25249step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25249step0 raw25249step0Labels raw25249step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical25255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25255 raw25255Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw25255 raw25255Labels = mixedMoment B raw25255step0 raw25255step0Labels := by
      have hz : ∀ j, raw25255 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25255step0 = (fun i j => raw25255 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25255step0 raw25255; decide +kernel
      have hl : raw25255step0Labels = raw25255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25255 raw25255Labels permutation346 hz
    mixedMoment B raw25255step0 raw25255step0Labels = mixedMoment B raw25255step1 raw25255step1Labels := by
      have ha : raw25255step1 = (fun i j => raw25255step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25255step1 raw25255step0; decide +kernel
      have hl : raw25255step1Labels = raw25255step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25255step0 raw25255step0Labels permutation35 permutation3
    mixedMoment B raw25255step1 raw25255step1Labels = mixedMoment B raw25255step2 raw25255step2Labels := by
      have ha : raw25255step2 = raw25255step1 := by apply Matrix.ext; unfold raw25255step2 raw25255step1; decide +kernel
      have hl : raw25255step1Labels = labelEmbedding6 ∘ raw25255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25255step1 raw25255step1Labels raw25255step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical210
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26972 raw26972Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw26972 raw26972Labels = mixedMoment B raw26972step0 raw26972step0Labels := by
      have ha : raw26972step0 = (fun i j => raw26972 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26972step0 raw26972; decide +kernel
      have hl : raw26972step0Labels = raw26972Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26972 raw26972Labels permutation168 permutation3
    mixedMoment B raw26972step0 raw26972step0Labels = mixedMoment B raw26972step1 raw26972step1Labels := by
      have ha : raw26972step1 = raw26972step0 := by apply Matrix.ext; unfold raw26972step1 raw26972step0; decide +kernel
      have hl : raw26972step0Labels = labelEmbedding6 ∘ raw26972step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26972step0 raw26972step0Labels raw26972step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5167 node5167Labels := by rfl

theorem canonical26973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26973 raw26973Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw26973 raw26973Labels = mixedMoment B raw26973step0 raw26973step0Labels := by
      have hz : ∀ j, raw26973 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26973step0 = (fun i j => raw26973 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26973step0 raw26973; decide +kernel
      have hl : raw26973step0Labels = raw26973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26973 raw26973Labels permutation434 hz
    mixedMoment B raw26973step0 raw26973step0Labels = mixedMoment B raw26973step1 raw26973step1Labels := by
      have ha : raw26973step1 = (fun i j => raw26973step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26973step1 raw26973step0; decide +kernel
      have hl : raw26973step1Labels = raw26973step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26973step0 raw26973step0Labels permutation35 permutation3
    mixedMoment B raw26973step1 raw26973step1Labels = mixedMoment B raw26973step2 raw26973step2Labels := by
      have ha : raw26973step2 = raw26973step1 := by apply Matrix.ext; unfold raw26973step2 raw26973step1; decide +kernel
      have hl : raw26973step1Labels = labelEmbedding6 ∘ raw26973step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26973step1 raw26973step1Labels raw26973step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical26974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26974 raw26974Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw26974 raw26974Labels = mixedMoment B raw26974step0 raw26974step0Labels := by
      have ha : raw26974step0 = (fun i j => raw26974 (permutation228 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26974step0 raw26974; decide +kernel
      have hl : raw26974step0Labels = raw26974Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26974 raw26974Labels permutation228 permutation3
    mixedMoment B raw26974step0 raw26974step0Labels = mixedMoment B raw26974step1 raw26974step1Labels := by
      have ha : raw26974step1 = raw26974step0 := by apply Matrix.ext; unfold raw26974step1 raw26974step0; decide +kernel
      have hl : raw26974step0Labels = labelEmbedding6 ∘ raw26974step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26974step0 raw26974step0Labels raw26974step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical26975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26975 raw26975Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw26975 raw26975Labels = mixedMoment B raw26975step0 raw26975step0Labels := by
      have ha : raw26975step0 = (fun i j => raw26975 (permutation250 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26975step0 raw26975; decide +kernel
      have hl : raw26975step0Labels = raw26975Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26975 raw26975Labels permutation250 permutation3
    mixedMoment B raw26975step0 raw26975step0Labels = mixedMoment B raw26975step1 raw26975step1Labels := by
      have ha : raw26975step1 = raw26975step0 := by apply Matrix.ext; unfold raw26975step1 raw26975step0; decide +kernel
      have hl : raw26975step0Labels = labelEmbedding6 ∘ raw26975step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26975step0 raw26975step0Labels raw26975step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical26976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26976 raw26976Labels = mixedMoment B node4113 node4113Labels := by
  calc
    mixedMoment B raw26976 raw26976Labels = mixedMoment B raw26976step0 raw26976step0Labels := by
      have ha : raw26976step0 = (fun i j => raw26976 (permutation243 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26976step0 raw26976; decide +kernel
      have hl : raw26976step0Labels = raw26976Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26976 raw26976Labels permutation243 permutation3
    mixedMoment B raw26976step0 raw26976step0Labels = mixedMoment B raw26976step1 raw26976step1Labels := by
      have ha : raw26976step1 = raw26976step0 := by apply Matrix.ext; unfold raw26976step1 raw26976step0; decide +kernel
      have hl : raw26976step0Labels = labelEmbedding6 ∘ raw26976step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26976step0 raw26976step0Labels raw26976step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4113 node4113Labels := by rfl

theorem canonical26977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26977 raw26977Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw26977 raw26977Labels = mixedMoment B raw26977step0 raw26977step0Labels := by
      have hz : ∀ j, raw26977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26977step0 = (fun i j => raw26977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26977step0 raw26977; decide +kernel
      have hl : raw26977step0Labels = raw26977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26977 raw26977Labels permutation434 hz
    mixedMoment B raw26977step0 raw26977step0Labels = mixedMoment B raw26977step1 raw26977step1Labels := by
      have ha : raw26977step1 = (fun i j => raw26977step0 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26977step1 raw26977step0; decide +kernel
      have hl : raw26977step1Labels = raw26977step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26977step0 raw26977step0Labels permutation49 permutation3
    mixedMoment B raw26977step1 raw26977step1Labels = mixedMoment B raw26977step2 raw26977step2Labels := by
      have ha : raw26977step2 = raw26977step1 := by apply Matrix.ext; unfold raw26977step2 raw26977step1; decide +kernel
      have hl : raw26977step1Labels = labelEmbedding6 ∘ raw26977step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26977step1 raw26977step1Labels raw26977step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical26978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26978 raw26978Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw26978 raw26978Labels = mixedMoment B raw26978step0 raw26978step0Labels := by
      have ha : raw26978step0 = (fun i j => raw26978 (permutation243 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26978step0 raw26978; decide +kernel
      have hl : raw26978step0Labels = raw26978Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26978 raw26978Labels permutation243 permutation3
    mixedMoment B raw26978step0 raw26978step0Labels = mixedMoment B raw26978step1 raw26978step1Labels := by
      have ha : raw26978step1 = raw26978step0 := by apply Matrix.ext; unfold raw26978step1 raw26978step0; decide +kernel
      have hl : raw26978step0Labels = labelEmbedding6 ∘ raw26978step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26978step0 raw26978step0Labels raw26978step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

theorem canonical26979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26979 raw26979Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw26979 raw26979Labels = mixedMoment B raw26979step0 raw26979step0Labels := by
      have ha : raw26979step0 = (fun i j => raw26979 (permutation263 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26979step0 raw26979; decide +kernel
      have hl : raw26979step0Labels = raw26979Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26979 raw26979Labels permutation263 permutation3
    mixedMoment B raw26979step0 raw26979step0Labels = mixedMoment B raw26979step1 raw26979step1Labels := by
      have ha : raw26979step1 = raw26979step0 := by apply Matrix.ext; unfold raw26979step1 raw26979step0; decide +kernel
      have hl : raw26979step0Labels = labelEmbedding6 ∘ raw26979step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26979step0 raw26979step0Labels raw26979step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

theorem canonical26980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26980 raw26980Labels = mixedMoment B node4098 node4098Labels := by
  calc
    mixedMoment B raw26980 raw26980Labels = mixedMoment B raw26980step0 raw26980step0Labels := by
      have ha : raw26980step0 = (fun i j => raw26980 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26980step0 raw26980; decide +kernel
      have hl : raw26980step0Labels = raw26980Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26980 raw26980Labels permutation169 permutation3
    mixedMoment B raw26980step0 raw26980step0Labels = mixedMoment B raw26980step1 raw26980step1Labels := by
      have ha : raw26980step1 = raw26980step0 := by apply Matrix.ext; unfold raw26980step1 raw26980step0; decide +kernel
      have hl : raw26980step0Labels = labelEmbedding6 ∘ raw26980step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26980step0 raw26980step0Labels raw26980step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4098 node4098Labels := by rfl

theorem canonical26981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26981 raw26981Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw26981 raw26981Labels = mixedMoment B raw26981step0 raw26981step0Labels := by
      have ha : raw26981step0 = (fun i j => raw26981 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26981step0 raw26981; decide +kernel
      have hl : raw26981step0Labels = raw26981Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26981 raw26981Labels permutation169 permutation3
    mixedMoment B raw26981step0 raw26981step0Labels = mixedMoment B raw26981step1 raw26981step1Labels := by
      have ha : raw26981step1 = raw26981step0 := by apply Matrix.ext; unfold raw26981step1 raw26981step0; decide +kernel
      have hl : raw26981step0Labels = labelEmbedding6 ∘ raw26981step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26981step0 raw26981step0Labels raw26981step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4341 node4341Labels := by rfl

theorem canonical26982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26982 raw26982Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw26982 raw26982Labels = mixedMoment B raw26982step0 raw26982step0Labels := by
      have hz : ∀ j, raw26982 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26982step0 = (fun i j => raw26982 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26982step0 raw26982; decide +kernel
      have hl : raw26982step0Labels = raw26982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26982 raw26982Labels permutation434 hz
    mixedMoment B raw26982step0 raw26982step0Labels = mixedMoment B raw26982step1 raw26982step1Labels := by
      have ha : raw26982step1 = (fun i j => raw26982step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26982step1 raw26982step0; decide +kernel
      have hl : raw26982step1Labels = raw26982step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26982step0 raw26982step0Labels permutation35 permutation3
    mixedMoment B raw26982step1 raw26982step1Labels = mixedMoment B raw26982step2 raw26982step2Labels := by
      have ha : raw26982step2 = raw26982step1 := by apply Matrix.ext; unfold raw26982step2 raw26982step1; decide +kernel
      have hl : raw26982step1Labels = labelEmbedding6 ∘ raw26982step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26982step1 raw26982step1Labels raw26982step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

theorem canonical26983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26983 raw26983Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw26983 raw26983Labels = mixedMoment B raw26983step0 raw26983step0Labels := by
      have ha : raw26983step0 = (fun i j => raw26983 (permutation229 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26983step0 raw26983; decide +kernel
      have hl : raw26983step0Labels = raw26983Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26983 raw26983Labels permutation229 permutation3
    mixedMoment B raw26983step0 raw26983step0Labels = mixedMoment B raw26983step1 raw26983step1Labels := by
      have ha : raw26983step1 = raw26983step0 := by apply Matrix.ext; unfold raw26983step1 raw26983step0; decide +kernel
      have hl : raw26983step0Labels = labelEmbedding6 ∘ raw26983step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26983step0 raw26983step0Labels raw26983step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

theorem canonical26984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26984 raw26984Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw26984 raw26984Labels = mixedMoment B raw26984step0 raw26984step0Labels := by
      have ha : raw26984step0 = (fun i j => raw26984 (permutation251 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26984step0 raw26984; decide +kernel
      have hl : raw26984step0Labels = raw26984Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26984 raw26984Labels permutation251 permutation3
    mixedMoment B raw26984step0 raw26984step0Labels = mixedMoment B raw26984step1 raw26984step1Labels := by
      have ha : raw26984step1 = raw26984step0 := by apply Matrix.ext; unfold raw26984step1 raw26984step0; decide +kernel
      have hl : raw26984step0Labels = labelEmbedding6 ∘ raw26984step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26984step0 raw26984step0Labels raw26984step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

theorem canonical26985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26985 raw26985Labels = mixedMoment B node4098 node4098Labels := by
  calc
    mixedMoment B raw26985 raw26985Labels = mixedMoment B raw26985step0 raw26985step0Labels := by
      have ha : raw26985step0 = (fun i j => raw26985 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26985step0 raw26985; decide +kernel
      have hl : raw26985step0Labels = raw26985Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26985 raw26985Labels permutation168 permutation3
    mixedMoment B raw26985step0 raw26985step0Labels = mixedMoment B raw26985step1 raw26985step1Labels := by
      have ha : raw26985step1 = raw26985step0 := by apply Matrix.ext; unfold raw26985step1 raw26985step0; decide +kernel
      have hl : raw26985step0Labels = labelEmbedding6 ∘ raw26985step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26985step0 raw26985step0Labels raw26985step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4098 node4098Labels := by rfl

theorem canonical26986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26986 raw26986Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw26986 raw26986Labels = mixedMoment B raw26986step0 raw26986step0Labels := by
      have ha : raw26986step0 = (fun i j => raw26986 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26986step0 raw26986; decide +kernel
      have hl : raw26986step0Labels = raw26986Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26986 raw26986Labels permutation168 permutation3
    mixedMoment B raw26986step0 raw26986step0Labels = mixedMoment B raw26986step1 raw26986step1Labels := by
      have ha : raw26986step1 = raw26986step0 := by apply Matrix.ext; unfold raw26986step1 raw26986step0; decide +kernel
      have hl : raw26986step0Labels = labelEmbedding6 ∘ raw26986step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26986step0 raw26986step0Labels raw26986step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4341 node4341Labels := by rfl

theorem canonical26987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26987 raw26987Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw26987 raw26987Labels = mixedMoment B raw26987step0 raw26987step0Labels := by
      have ha : raw26987step0 = (fun i j => raw26987 (permutation228 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26987step0 raw26987; decide +kernel
      have hl : raw26987step0Labels = raw26987Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26987 raw26987Labels permutation228 permutation3
    mixedMoment B raw26987step0 raw26987step0Labels = mixedMoment B raw26987step1 raw26987step1Labels := by
      have ha : raw26987step1 = raw26987step0 := by apply Matrix.ext; unfold raw26987step1 raw26987step0; decide +kernel
      have hl : raw26987step0Labels = labelEmbedding6 ∘ raw26987step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26987step0 raw26987step0Labels raw26987step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

theorem canonical26988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26988 raw26988Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw26988 raw26988Labels = mixedMoment B raw26988step0 raw26988step0Labels := by
      have ha : raw26988step0 = (fun i j => raw26988 (permutation250 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26988step0 raw26988; decide +kernel
      have hl : raw26988step0Labels = raw26988Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26988 raw26988Labels permutation250 permutation3
    mixedMoment B raw26988step0 raw26988step0Labels = mixedMoment B raw26988step1 raw26988step1Labels := by
      have ha : raw26988step1 = raw26988step0 := by apply Matrix.ext; unfold raw26988step1 raw26988step0; decide +kernel
      have hl : raw26988step0Labels = labelEmbedding6 ∘ raw26988step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26988step0 raw26988step0Labels raw26988step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

theorem canonical26989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26989 raw26989Labels = mixedMoment B node4100 node4100Labels := by
  calc
    mixedMoment B raw26989 raw26989Labels = mixedMoment B raw26989step0 raw26989step0Labels := by
      have ha : raw26989step0 = (fun i j => raw26989 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26989step0 raw26989; decide +kernel
      have hl : raw26989step0Labels = raw26989Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26989 raw26989Labels permutation170 permutation3
    mixedMoment B raw26989step0 raw26989step0Labels = mixedMoment B raw26989step1 raw26989step1Labels := by
      have ha : raw26989step1 = raw26989step0 := by apply Matrix.ext; unfold raw26989step1 raw26989step0; decide +kernel
      have hl : raw26989step0Labels = labelEmbedding6 ∘ raw26989step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26989step0 raw26989step0Labels raw26989step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4100 node4100Labels := by rfl

theorem canonical26990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26990 raw26990Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw26990 raw26990Labels = mixedMoment B raw26990step0 raw26990step0Labels := by
      have ha : raw26990step0 = (fun i j => raw26990 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26990step0 raw26990; decide +kernel
      have hl : raw26990step0Labels = raw26990Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26990 raw26990Labels permutation170 permutation3
    mixedMoment B raw26990step0 raw26990step0Labels = mixedMoment B raw26990step1 raw26990step1Labels := by
      have ha : raw26990step1 = raw26990step0 := by apply Matrix.ext; unfold raw26990step1 raw26990step0; decide +kernel
      have hl : raw26990step0Labels = labelEmbedding6 ∘ raw26990step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26990step0 raw26990step0Labels raw26990step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4344 node4344Labels := by rfl

theorem canonical26991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26991 raw26991Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw26991 raw26991Labels = mixedMoment B raw26991step0 raw26991step0Labels := by
      have ha : raw26991step0 = (fun i j => raw26991 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26991step0 raw26991; decide +kernel
      have hl : raw26991step0Labels = raw26991Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26991 raw26991Labels permutation246 permutation3
    mixedMoment B raw26991step0 raw26991step0Labels = mixedMoment B raw26991step1 raw26991step1Labels := by
      have ha : raw26991step1 = raw26991step0 := by apply Matrix.ext; unfold raw26991step1 raw26991step0; decide +kernel
      have hl : raw26991step0Labels = labelEmbedding6 ∘ raw26991step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26991step0 raw26991step0Labels raw26991step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4399 node4399Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw666 raw666Labels = mixedMoment B node4098 node4098Labels := by
  calc
    mixedMoment B raw666 raw666Labels = mixedMoment B raw666step0 raw666step0Labels := by
      have ha : raw666step0 = (fun i j => raw666 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw666step0 raw666; decide +kernel
      have hl : raw666step0Labels = raw666Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw666 raw666Labels permutation152 permutation4
    mixedMoment B raw666step0 raw666step0Labels = mixedMoment B raw666step1 raw666step1Labels := by
      have ha : raw666step1 = raw666step0 := by apply Matrix.ext; unfold raw666step1 raw666step0; decide +kernel
      have hl : raw666step0Labels = labelEmbedding7 ∘ raw666step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw666step0 raw666step0Labels raw666step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4098 node4098Labels := by rfl

theorem canonical667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw667 raw667Labels = mixedMoment B node535 node535Labels := by
  calc
    mixedMoment B raw667 raw667Labels = mixedMoment B raw667step0 raw667step0Labels := by
      have ha : raw667step0 = (fun i j => raw667 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw667step0 raw667; decide +kernel
      have hl : raw667step0Labels = raw667Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw667 raw667Labels permutation152 permutation4
    _ = mixedMoment B node535 node535Labels := by rfl

theorem canonical668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw668 raw668Labels = mixedMoment B node656 node656Labels := by
  calc
    mixedMoment B raw668 raw668Labels = mixedMoment B raw668step0 raw668step0Labels := by
      have ha : raw668step0 = (fun i j => raw668 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw668step0 raw668; decide +kernel
      have hl : raw668step0Labels = raw668Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw668 raw668Labels permutation182 permutation6
    mixedMoment B raw668step0 raw668step0Labels = mixedMoment B raw668step1 raw668step1Labels := by
      have ha : raw668step1 = -raw668step0 := by apply Matrix.ext; change ∀ i j, raw668step1 i j = -(raw668step0 i j); unfold raw668step1 raw668step0; decide +kernel
      have hl : raw668step1Labels = raw668step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw668step1 raw668step1Labels = mixedMoment B raw668step2 raw668step2Labels := by
      have ha : raw668step2 = raw668step1 := by apply Matrix.ext; unfold raw668step2 raw668step1; decide +kernel
      have hl : raw668step1Labels = labelEmbedding1 ∘ raw668step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw668step1 raw668step1Labels raw668step2Labels labelEmbedding1 hl
    _ = mixedMoment B node656 node656Labels := by rfl

theorem canonical672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw672 raw672Labels = mixedMoment B node4100 node4100Labels := by
  calc
    mixedMoment B raw672 raw672Labels = mixedMoment B raw672step0 raw672step0Labels := by
      have ha : raw672step0 = (fun i j => raw672 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw672step0 raw672; decide +kernel
      have hl : raw672step0Labels = raw672Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw672 raw672Labels permutation152 permutation4
    mixedMoment B raw672step0 raw672step0Labels = mixedMoment B raw672step1 raw672step1Labels := by
      have ha : raw672step1 = raw672step0 := by apply Matrix.ext; unfold raw672step1 raw672step0; decide +kernel
      have hl : raw672step0Labels = labelEmbedding7 ∘ raw672step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw672step0 raw672step0Labels raw672step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4100 node4100Labels := by rfl

theorem canonical673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw673 raw673Labels = mixedMoment B node537 node537Labels := by
  calc
    mixedMoment B raw673 raw673Labels = mixedMoment B raw673step0 raw673step0Labels := by
      have ha : raw673step0 = (fun i j => raw673 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw673step0 raw673; decide +kernel
      have hl : raw673step0Labels = raw673Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw673 raw673Labels permutation152 permutation4
    _ = mixedMoment B node537 node537Labels := by rfl

theorem canonical674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw674 raw674Labels = mixedMoment B node662 node662Labels := by
  calc
    mixedMoment B raw674 raw674Labels = mixedMoment B raw674step0 raw674step0Labels := by
      have ha : raw674step0 = (fun i j => raw674 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw674step0 raw674; decide +kernel
      have hl : raw674step0Labels = raw674Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw674 raw674Labels permutation176 permutation6
    mixedMoment B raw674step0 raw674step0Labels = mixedMoment B raw674step1 raw674step1Labels := by
      have ha : raw674step1 = -raw674step0 := by apply Matrix.ext; change ∀ i j, raw674step1 i j = -(raw674step0 i j); unfold raw674step1 raw674step0; decide +kernel
      have hl : raw674step1Labels = raw674step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw674step1 raw674step1Labels = mixedMoment B raw674step2 raw674step2Labels := by
      have ha : raw674step2 = raw674step1 := by apply Matrix.ext; unfold raw674step2 raw674step1; decide +kernel
      have hl : raw674step1Labels = labelEmbedding1 ∘ raw674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw674step1 raw674step1Labels raw674step2Labels labelEmbedding1 hl
    _ = mixedMoment B node662 node662Labels := by rfl

theorem canonical711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw711 raw711Labels = mixedMoment B node4113 node4113Labels := by
  calc
    mixedMoment B raw711 raw711Labels = mixedMoment B raw711step0 raw711step0Labels := by
      have ha : raw711step0 = (fun i j => raw711 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw711step0 raw711; decide +kernel
      have hl : raw711step0Labels = raw711Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw711 raw711Labels permutation152 permutation4
    mixedMoment B raw711step0 raw711step0Labels = mixedMoment B raw711step1 raw711step1Labels := by
      have ha : raw711step1 = raw711step0 := by apply Matrix.ext; unfold raw711step1 raw711step0; decide +kernel
      have hl : raw711step0Labels = labelEmbedding7 ∘ raw711step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw711step0 raw711step0Labels raw711step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4113 node4113Labels := by rfl

theorem canonical712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw712 raw712Labels = mixedMoment B node550 node550Labels := by
  calc
    mixedMoment B raw712 raw712Labels = mixedMoment B raw712step0 raw712step0Labels := by
      have ha : raw712step0 = (fun i j => raw712 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw712step0 raw712; decide +kernel
      have hl : raw712step0Labels = raw712Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw712 raw712Labels permutation152 permutation4
    _ = mixedMoment B node550 node550Labels := by rfl

theorem canonical713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw713 raw713Labels = mixedMoment B node658 node658Labels := by
  calc
    mixedMoment B raw713 raw713Labels = mixedMoment B raw713step0 raw713step0Labels := by
      have ha : raw713step0 = (fun i j => raw713 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw713step0 raw713; decide +kernel
      have hl : raw713step0Labels = raw713Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw713 raw713Labels permutation152 permutation6
    mixedMoment B raw713step0 raw713step0Labels = mixedMoment B raw713step1 raw713step1Labels := by
      have ha : raw713step1 = -raw713step0 := by apply Matrix.ext; change ∀ i j, raw713step1 i j = -(raw713step0 i j); unfold raw713step1 raw713step0; decide +kernel
      have hl : raw713step1Labels = raw713step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw713step1 raw713step1Labels = mixedMoment B raw713step2 raw713step2Labels := by
      have ha : raw713step2 = raw713step1 := by apply Matrix.ext; unfold raw713step2 raw713step1; decide +kernel
      have hl : raw713step1Labels = labelEmbedding1 ∘ raw713step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw713step1 raw713step1Labels raw713step2Labels labelEmbedding1 hl
    _ = mixedMoment B node658 node658Labels := by rfl

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

theorem canonical1122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1122 raw1122Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw1122 raw1122Labels = mixedMoment B raw1122step0 raw1122step0Labels := by
      have ha : raw1122step0 = (fun i j => raw1122 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1122step0 raw1122; decide +kernel
      have hl : raw1122step0Labels = raw1122Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1122 raw1122Labels permutation152 permutation4
    mixedMoment B raw1122step0 raw1122step0Labels = mixedMoment B raw1122step1 raw1122step1Labels := by
      have ha : raw1122step1 = raw1122step0 := by apply Matrix.ext; unfold raw1122step1 raw1122step0; decide +kernel
      have hl : raw1122step0Labels = labelEmbedding7 ∘ raw1122step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1122step0 raw1122step0Labels raw1122step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4341 node4341Labels := by rfl

theorem canonical1123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1123 raw1123Labels = mixedMoment B node919 node919Labels := by
  calc
    mixedMoment B raw1123 raw1123Labels = mixedMoment B raw1123step0 raw1123step0Labels := by
      have ha : raw1123step0 = (fun i j => raw1123 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1123step0 raw1123; decide +kernel
      have hl : raw1123step0Labels = raw1123Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1123 raw1123Labels permutation152 permutation4
    _ = mixedMoment B node919 node919Labels := by rfl

theorem canonical1124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1124 raw1124Labels = mixedMoment B node1664 node1664Labels := by
  calc
    mixedMoment B raw1124 raw1124Labels = mixedMoment B raw1124step0 raw1124step0Labels := by
      have ha : raw1124step0 = (fun i j => raw1124 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1124step0 raw1124; decide +kernel
      have hl : raw1124step0Labels = raw1124Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1124 raw1124Labels permutation152 permutation6
    mixedMoment B raw1124step0 raw1124step0Labels = mixedMoment B raw1124step1 raw1124step1Labels := by
      have ha : raw1124step1 = -raw1124step0 := by apply Matrix.ext; change ∀ i j, raw1124step1 i j = -(raw1124step0 i j); unfold raw1124step1 raw1124step0; decide +kernel
      have hl : raw1124step1Labels = raw1124step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1124step1 raw1124step1Labels = mixedMoment B raw1124step2 raw1124step2Labels := by
      have ha : raw1124step2 = raw1124step1 := by apply Matrix.ext; unfold raw1124step2 raw1124step1; decide +kernel
      have hl : raw1124step1Labels = labelEmbedding1 ∘ raw1124step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1124step1 raw1124step1Labels raw1124step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1664 node1664Labels := by rfl

theorem canonical1128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1128 raw1128Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw1128 raw1128Labels = mixedMoment B raw1128step0 raw1128step0Labels := by
      have ha : raw1128step0 = (fun i j => raw1128 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1128step0 raw1128; decide +kernel
      have hl : raw1128step0Labels = raw1128Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1128 raw1128Labels permutation152 permutation4
    mixedMoment B raw1128step0 raw1128step0Labels = mixedMoment B raw1128step1 raw1128step1Labels := by
      have ha : raw1128step1 = raw1128step0 := by apply Matrix.ext; unfold raw1128step1 raw1128step0; decide +kernel
      have hl : raw1128step0Labels = labelEmbedding7 ∘ raw1128step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1128step0 raw1128step0Labels raw1128step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4344 node4344Labels := by rfl

theorem canonical1129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1129 raw1129Labels = mixedMoment B node922 node922Labels := by
  calc
    mixedMoment B raw1129 raw1129Labels = mixedMoment B raw1129step0 raw1129step0Labels := by
      have ha : raw1129step0 = (fun i j => raw1129 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1129step0 raw1129; decide +kernel
      have hl : raw1129step0Labels = raw1129Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1129 raw1129Labels permutation152 permutation4
    _ = mixedMoment B node922 node922Labels := by rfl

theorem canonical1130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1130 raw1130Labels = mixedMoment B node1673 node1673Labels := by
  calc
    mixedMoment B raw1130 raw1130Labels = mixedMoment B raw1130step0 raw1130step0Labels := by
      have ha : raw1130step0 = (fun i j => raw1130 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1130step0 raw1130; decide +kernel
      have hl : raw1130step0Labels = raw1130Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1130 raw1130Labels permutation152 permutation6
    mixedMoment B raw1130step0 raw1130step0Labels = mixedMoment B raw1130step1 raw1130step1Labels := by
      have ha : raw1130step1 = -raw1130step0 := by apply Matrix.ext; change ∀ i j, raw1130step1 i j = -(raw1130step0 i j); unfold raw1130step1 raw1130step0; decide +kernel
      have hl : raw1130step1Labels = raw1130step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1130step1 raw1130step1Labels = mixedMoment B raw1130step2 raw1130step2Labels := by
      have ha : raw1130step2 = raw1130step1 := by apply Matrix.ext; unfold raw1130step2 raw1130step1; decide +kernel
      have hl : raw1130step1Labels = labelEmbedding1 ∘ raw1130step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1130step1 raw1130step1Labels raw1130step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1673 node1673Labels := by rfl

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

theorem canonical1206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1206 raw1206Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw1206 raw1206Labels = mixedMoment B raw1206step0 raw1206step0Labels := by
      have ha : raw1206step0 = (fun i j => raw1206 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1206step0 raw1206; decide +kernel
      have hl : raw1206step0Labels = raw1206Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1206 raw1206Labels permutation152 permutation4
    mixedMoment B raw1206step0 raw1206step0Labels = mixedMoment B raw1206step1 raw1206step1Labels := by
      have ha : raw1206step1 = raw1206step0 := by apply Matrix.ext; unfold raw1206step1 raw1206step0; decide +kernel
      have hl : raw1206step0Labels = labelEmbedding7 ∘ raw1206step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1206step0 raw1206step0Labels raw1206step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

theorem canonical1207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1207 raw1207Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw1207 raw1207Labels = mixedMoment B raw1207step0 raw1207step0Labels := by
      have ha : raw1207step0 = (fun i j => raw1207 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1207step0 raw1207; decide +kernel
      have hl : raw1207step0Labels = raw1207Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1207 raw1207Labels permutation152 permutation4
    _ = mixedMoment B node977 node977Labels := by rfl

theorem canonical1208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1208 raw1208Labels = mixedMoment B node1597 node1597Labels := by
  calc
    mixedMoment B raw1208 raw1208Labels = mixedMoment B raw1208step0 raw1208step0Labels := by
      have ha : raw1208step0 = (fun i j => raw1208 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1208step0 raw1208; decide +kernel
      have hl : raw1208step0Labels = raw1208Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1208 raw1208Labels permutation158 permutation6
    mixedMoment B raw1208step0 raw1208step0Labels = mixedMoment B raw1208step1 raw1208step1Labels := by
      have ha : raw1208step1 = -raw1208step0 := by apply Matrix.ext; change ∀ i j, raw1208step1 i j = -(raw1208step0 i j); unfold raw1208step1 raw1208step0; decide +kernel
      have hl : raw1208step1Labels = raw1208step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1208step1 raw1208step1Labels = mixedMoment B raw1208step2 raw1208step2Labels := by
      have ha : raw1208step2 = raw1208step1 := by apply Matrix.ext; unfold raw1208step2 raw1208step1; decide +kernel
      have hl : raw1208step1Labels = labelEmbedding1 ∘ raw1208step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1208step1 raw1208step1Labels raw1208step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1597 node1597Labels := by rfl

theorem canonical1212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1212 raw1212Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw1212 raw1212Labels = mixedMoment B raw1212step0 raw1212step0Labels := by
      have ha : raw1212step0 = (fun i j => raw1212 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1212step0 raw1212; decide +kernel
      have hl : raw1212step0Labels = raw1212Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1212 raw1212Labels permutation152 permutation4
    mixedMoment B raw1212step0 raw1212step0Labels = mixedMoment B raw1212step1 raw1212step1Labels := by
      have ha : raw1212step1 = raw1212step0 := by apply Matrix.ext; unfold raw1212step1 raw1212step0; decide +kernel
      have hl : raw1212step0Labels = labelEmbedding7 ∘ raw1212step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1212step0 raw1212step0Labels raw1212step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical1213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1213 raw1213Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw1213 raw1213Labels = mixedMoment B raw1213step0 raw1213step0Labels := by
      have ha : raw1213step0 = (fun i j => raw1213 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1213step0 raw1213; decide +kernel
      have hl : raw1213step0Labels = raw1213Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1213 raw1213Labels permutation152 permutation4
    _ = mixedMoment B node980 node980Labels := by rfl

theorem canonical1214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1214 raw1214Labels = mixedMoment B node1616 node1616Labels := by
  calc
    mixedMoment B raw1214 raw1214Labels = mixedMoment B raw1214step0 raw1214step0Labels := by
      have ha : raw1214step0 = (fun i j => raw1214 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1214step0 raw1214; decide +kernel
      have hl : raw1214step0Labels = raw1214Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1214 raw1214Labels permutation152 permutation6
    mixedMoment B raw1214step0 raw1214step0Labels = mixedMoment B raw1214step1 raw1214step1Labels := by
      have ha : raw1214step1 = -raw1214step0 := by apply Matrix.ext; change ∀ i j, raw1214step1 i j = -(raw1214step0 i j); unfold raw1214step1 raw1214step0; decide +kernel
      have hl : raw1214step1Labels = raw1214step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1214step1 raw1214step1Labels = mixedMoment B raw1214step2 raw1214step2Labels := by
      have ha : raw1214step2 = raw1214step1 := by apply Matrix.ext; unfold raw1214step2 raw1214step1; decide +kernel
      have hl : raw1214step1Labels = labelEmbedding1 ∘ raw1214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1214step1 raw1214step1Labels raw1214step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1616 node1616Labels := by rfl

theorem canonical1224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1224 raw1224Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw1224 raw1224Labels = mixedMoment B raw1224step0 raw1224step0Labels := by
      have ha : raw1224step0 = (fun i j => raw1224 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1224step0 raw1224; decide +kernel
      have hl : raw1224step0Labels = raw1224Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1224 raw1224Labels permutation152 permutation4
    mixedMoment B raw1224step0 raw1224step0Labels = mixedMoment B raw1224step1 raw1224step1Labels := by
      have ha : raw1224step1 = raw1224step0 := by apply Matrix.ext; unfold raw1224step1 raw1224step0; decide +kernel
      have hl : raw1224step0Labels = labelEmbedding7 ∘ raw1224step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1224step0 raw1224step0Labels raw1224step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

theorem canonical1225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1225 raw1225Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw1225 raw1225Labels = mixedMoment B raw1225step0 raw1225step0Labels := by
      have ha : raw1225step0 = (fun i j => raw1225 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1225step0 raw1225; decide +kernel
      have hl : raw1225step0Labels = raw1225Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1225 raw1225Labels permutation152 permutation4
    _ = mixedMoment B node998 node998Labels := by rfl

theorem canonical1226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1226 raw1226Labels = mixedMoment B node1600 node1600Labels := by
  calc
    mixedMoment B raw1226 raw1226Labels = mixedMoment B raw1226step0 raw1226step0Labels := by
      have ha : raw1226step0 = (fun i j => raw1226 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1226step0 raw1226; decide +kernel
      have hl : raw1226step0Labels = raw1226Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1226 raw1226Labels permutation152 permutation6
    mixedMoment B raw1226step0 raw1226step0Labels = mixedMoment B raw1226step1 raw1226step1Labels := by
      have ha : raw1226step1 = -raw1226step0 := by apply Matrix.ext; change ∀ i j, raw1226step1 i j = -(raw1226step0 i j); unfold raw1226step1 raw1226step0; decide +kernel
      have hl : raw1226step1Labels = raw1226step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1226step1 raw1226step1Labels = mixedMoment B raw1226step2 raw1226step2Labels := by
      have ha : raw1226step2 = raw1226step1 := by apply Matrix.ext; unfold raw1226step2 raw1226step1; decide +kernel
      have hl : raw1226step1Labels = labelEmbedding1 ∘ raw1226step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1226step1 raw1226step1Labels raw1226step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1600 node1600Labels := by rfl

theorem canonical1257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1257 raw1257Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw1257 raw1257Labels = mixedMoment B raw1257step0 raw1257step0Labels := by
      have ha : raw1257step0 = (fun i j => raw1257 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1257step0 raw1257; decide +kernel
      have hl : raw1257step0Labels = raw1257Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1257 raw1257Labels permutation32 permutation4
    mixedMoment B raw1257step0 raw1257step0Labels = mixedMoment B raw1257step1 raw1257step1Labels := by
      have ha : raw1257step1 = raw1257step0 := by apply Matrix.ext; unfold raw1257step1 raw1257step0; decide +kernel
      have hl : raw1257step0Labels = labelEmbedding7 ∘ raw1257step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1257step0 raw1257step0Labels raw1257step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

theorem canonical1258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1258 raw1258Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw1258 raw1258Labels = mixedMoment B raw1258step0 raw1258step0Labels := by
      have ha : raw1258step0 = (fun i j => raw1258 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1258step0 raw1258; decide +kernel
      have hl : raw1258step0Labels = raw1258Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1258 raw1258Labels permutation32 permutation4
    _ = mixedMoment B node1040 node1040Labels := by rfl

theorem canonical1259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1259 raw1259Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw1259 raw1259Labels = mixedMoment B raw1259step0 raw1259step0Labels := by
      have ha : raw1259step0 = (fun i j => raw1259 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1259step0 raw1259; decide +kernel
      have hl : raw1259step0Labels = raw1259Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1259 raw1259Labels permutation40 permutation6
    mixedMoment B raw1259step0 raw1259step0Labels = mixedMoment B raw1259step1 raw1259step1Labels := by
      have ha : raw1259step1 = -raw1259step0 := by apply Matrix.ext; change ∀ i j, raw1259step1 i j = -(raw1259step0 i j); unfold raw1259step1 raw1259step0; decide +kernel
      have hl : raw1259step1Labels = raw1259step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1259step1 raw1259step1Labels = mixedMoment B raw1259step2 raw1259step2Labels := by
      have ha : raw1259step2 = raw1259step1 := by apply Matrix.ext; unfold raw1259step2 raw1259step1; decide +kernel
      have hl : raw1259step1Labels = labelEmbedding1 ∘ raw1259step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1259step1 raw1259step1Labels raw1259step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

theorem canonical1260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1260 raw1260Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw1260 raw1260Labels = mixedMoment B raw1260step0 raw1260step0Labels := by
      have ha : raw1260step0 = (fun i j => raw1260 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1260step0 raw1260; decide +kernel
      have hl : raw1260step0Labels = raw1260Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1260 raw1260Labels permutation32 permutation4
    mixedMoment B raw1260step0 raw1260step0Labels = mixedMoment B raw1260step1 raw1260step1Labels := by
      have ha : raw1260step1 = raw1260step0 := by apply Matrix.ext; unfold raw1260step1 raw1260step0; decide +kernel
      have hl : raw1260step0Labels = labelEmbedding7 ∘ raw1260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1260step0 raw1260step0Labels raw1260step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical1261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1261 raw1261Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw1261 raw1261Labels = mixedMoment B raw1261step0 raw1261step0Labels := by
      have ha : raw1261step0 = (fun i j => raw1261 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1261step0 raw1261; decide +kernel
      have hl : raw1261step0Labels = raw1261Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1261 raw1261Labels permutation32 permutation4
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical1262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1262 raw1262Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw1262 raw1262Labels = mixedMoment B raw1262step0 raw1262step0Labels := by
      have ha : raw1262step0 = (fun i j => raw1262 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1262step0 raw1262; decide +kernel
      have hl : raw1262step0Labels = raw1262Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1262 raw1262Labels permutation38 permutation6
    mixedMoment B raw1262step0 raw1262step0Labels = mixedMoment B raw1262step1 raw1262step1Labels := by
      have ha : raw1262step1 = -raw1262step0 := by apply Matrix.ext; change ∀ i j, raw1262step1 i j = -(raw1262step0 i j); unfold raw1262step1 raw1262step0; decide +kernel
      have hl : raw1262step1Labels = raw1262step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1262step1 raw1262step1Labels = mixedMoment B raw1262step2 raw1262step2Labels := by
      have ha : raw1262step2 = raw1262step1 := by apply Matrix.ext; unfold raw1262step2 raw1262step1; decide +kernel
      have hl : raw1262step1Labels = labelEmbedding1 ∘ raw1262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1262step1 raw1262step1Labels raw1262step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4098 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4098 node4098Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node535 node535Labels + mixedMoment B node656 node656Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw666 singletonSmall4098
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4098) = raw666Labels := by decide +kernel
  rw [hl, canonical666 B hB] at h
  have hc0 : mixedMoment B raw666 (Fin.cases (0 : Fin 2) singletonSmall4098) =
      mixedMoment B node535 node535Labels := by
    have ha : raw666 = raw667 := by apply Matrix.ext; unfold raw666 raw667; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4098 = raw667Labels := by decide +kernel
    rw [ha, hj, canonical667 B hB]
  have hc1 : mixedMoment B raw666 (Fin.cases (1 : Fin 2) singletonSmall4098) =
      mixedMoment B node656 node656Labels := by
    have ha : raw666 = raw668 := by apply Matrix.ext; unfold raw666 raw668; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4098 = raw668Labels := by decide +kernel
    rw [ha, hj, canonical668 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4100 node4100Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node537 node537Labels + mixedMoment B node662 node662Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw672 singletonSmall4100
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4100) = raw672Labels := by decide +kernel
  rw [hl, canonical672 B hB] at h
  have hc0 : mixedMoment B raw672 (Fin.cases (0 : Fin 2) singletonSmall4100) =
      mixedMoment B node537 node537Labels := by
    have ha : raw672 = raw673 := by apply Matrix.ext; unfold raw672 raw673; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4100 = raw673Labels := by decide +kernel
    rw [ha, hj, canonical673 B hB]
  have hc1 : mixedMoment B raw672 (Fin.cases (1 : Fin 2) singletonSmall4100) =
      mixedMoment B node662 node662Labels := by
    have ha : raw672 = raw674 := by apply Matrix.ext; unfold raw672 raw674; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4100 = raw674Labels := by decide +kernel
    rw [ha, hj, canonical674 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4113 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4113 node4113Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node550 node550Labels + mixedMoment B node658 node658Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw711 singletonSmall4113
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4113) = raw711Labels := by decide +kernel
  rw [hl, canonical711 B hB] at h
  have hc0 : mixedMoment B raw711 (Fin.cases (0 : Fin 2) singletonSmall4113) =
      mixedMoment B node550 node550Labels := by
    have ha : raw711 = raw712 := by apply Matrix.ext; unfold raw711 raw712; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4113 = raw712Labels := by decide +kernel
    rw [ha, hj, canonical712 B hB]
  have hc1 : mixedMoment B raw711 (Fin.cases (1 : Fin 2) singletonSmall4113) =
      mixedMoment B node658 node658Labels := by
    have ha : raw711 = raw713 := by apply Matrix.ext; unfold raw711 raw713; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4113 = raw713Labels := by decide +kernel
    rw [ha, hj, canonical713 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4341 node4341Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node919 node919Labels + mixedMoment B node1664 node1664Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1122 singletonSmall4341
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4341) = raw1122Labels := by decide +kernel
  rw [hl, canonical1122 B hB] at h
  have hc0 : mixedMoment B raw1122 (Fin.cases (0 : Fin 2) singletonSmall4341) =
      mixedMoment B node919 node919Labels := by
    have ha : raw1122 = raw1123 := by apply Matrix.ext; unfold raw1122 raw1123; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4341 = raw1123Labels := by decide +kernel
    rw [ha, hj, canonical1123 B hB]
  have hc1 : mixedMoment B raw1122 (Fin.cases (1 : Fin 2) singletonSmall4341) =
      mixedMoment B node1664 node1664Labels := by
    have ha : raw1122 = raw1124 := by apply Matrix.ext; unfold raw1122 raw1124; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4341 = raw1124Labels := by decide +kernel
    rw [ha, hj, canonical1124 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4344 node4344Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node922 node922Labels + mixedMoment B node1673 node1673Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1128 singletonSmall4344
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4344) = raw1128Labels := by decide +kernel
  rw [hl, canonical1128 B hB] at h
  have hc0 : mixedMoment B raw1128 (Fin.cases (0 : Fin 2) singletonSmall4344) =
      mixedMoment B node922 node922Labels := by
    have ha : raw1128 = raw1129 := by apply Matrix.ext; unfold raw1128 raw1129; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4344 = raw1129Labels := by decide +kernel
    rw [ha, hj, canonical1129 B hB]
  have hc1 : mixedMoment B raw1128 (Fin.cases (1 : Fin 2) singletonSmall4344) =
      mixedMoment B node1673 node1673Labels := by
    have ha : raw1128 = raw1130 := by apply Matrix.ext; unfold raw1128 raw1130; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4344 = raw1130Labels := by decide +kernel
    rw [ha, hj, canonical1130 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4396 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4396 node4396Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node977 node977Labels + mixedMoment B node1597 node1597Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1206 singletonSmall4396
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4396) = raw1206Labels := by decide +kernel
  rw [hl, canonical1206 B hB] at h
  have hc0 : mixedMoment B raw1206 (Fin.cases (0 : Fin 2) singletonSmall4396) =
      mixedMoment B node977 node977Labels := by
    have ha : raw1206 = raw1207 := by apply Matrix.ext; unfold raw1206 raw1207; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4396 = raw1207Labels := by decide +kernel
    rw [ha, hj, canonical1207 B hB]
  have hc1 : mixedMoment B raw1206 (Fin.cases (1 : Fin 2) singletonSmall4396) =
      mixedMoment B node1597 node1597Labels := by
    have ha : raw1206 = raw1208 := by apply Matrix.ext; unfold raw1206 raw1208; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4396 = raw1208Labels := by decide +kernel
    rw [ha, hj, canonical1208 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4399 node4399Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node980 node980Labels + mixedMoment B node1616 node1616Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1212 singletonSmall4399
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4399) = raw1212Labels := by decide +kernel
  rw [hl, canonical1212 B hB] at h
  have hc0 : mixedMoment B raw1212 (Fin.cases (0 : Fin 2) singletonSmall4399) =
      mixedMoment B node980 node980Labels := by
    have ha : raw1212 = raw1213 := by apply Matrix.ext; unfold raw1212 raw1213; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4399 = raw1213Labels := by decide +kernel
    rw [ha, hj, canonical1213 B hB]
  have hc1 : mixedMoment B raw1212 (Fin.cases (1 : Fin 2) singletonSmall4399) =
      mixedMoment B node1616 node1616Labels := by
    have ha : raw1212 = raw1214 := by apply Matrix.ext; unfold raw1212 raw1214; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4399 = raw1214Labels := by decide +kernel
    rw [ha, hj, canonical1214 B hB]
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

theorem singleton4417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4417 node4417Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node998 node998Labels + mixedMoment B node1600 node1600Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1224 singletonSmall4417
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4417) = raw1224Labels := by decide +kernel
  rw [hl, canonical1224 B hB] at h
  have hc0 : mixedMoment B raw1224 (Fin.cases (0 : Fin 2) singletonSmall4417) =
      mixedMoment B node998 node998Labels := by
    have ha : raw1224 = raw1225 := by apply Matrix.ext; unfold raw1224 raw1225; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4417 = raw1225Labels := by decide +kernel
    rw [ha, hj, canonical1225 B hB]
  have hc1 : mixedMoment B raw1224 (Fin.cases (1 : Fin 2) singletonSmall4417) =
      mixedMoment B node1600 node1600Labels := by
    have ha : raw1224 = raw1226 := by apply Matrix.ext; unfold raw1224 raw1226; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4417 = raw1226Labels := by decide +kernel
    rw [ha, hj, canonical1226 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4457 node4457Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1040 node1040Labels + mixedMoment B node1707 node1707Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1257 singletonSmall4457
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4457) = raw1257Labels := by decide +kernel
  rw [hl, canonical1257 B hB] at h
  have hc0 : mixedMoment B raw1257 (Fin.cases (0 : Fin 2) singletonSmall4457) =
      mixedMoment B node1040 node1040Labels := by
    have ha : raw1257 = raw1258 := by apply Matrix.ext; unfold raw1257 raw1258; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4457 = raw1258Labels := by decide +kernel
    rw [ha, hj, canonical1258 B hB]
  have hc1 : mixedMoment B raw1257 (Fin.cases (1 : Fin 2) singletonSmall4457) =
      mixedMoment B node1707 node1707Labels := by
    have ha : raw1257 = raw1259 := by apply Matrix.ext; unfold raw1257 raw1259; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4457 = raw1259Labels := by decide +kernel
    rw [ha, hj, canonical1259 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4458 node4458Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1041 node1041Labels + mixedMoment B node1724 node1724Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1260 singletonSmall4458
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4458) = raw1260Labels := by decide +kernel
  rw [hl, canonical1260 B hB] at h
  have hc0 : mixedMoment B raw1260 (Fin.cases (0 : Fin 2) singletonSmall4458) =
      mixedMoment B node1041 node1041Labels := by
    have ha : raw1260 = raw1261 := by apply Matrix.ext; unfold raw1260 raw1261; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4458 = raw1261Labels := by decide +kernel
    rw [ha, hj, canonical1261 B hB]
  have hc1 : mixedMoment B raw1260 (Fin.cases (1 : Fin 2) singletonSmall4458) =
      mixedMoment B node1724 node1724Labels := by
    have ha : raw1260 = raw1262 := by apply Matrix.ext; unfold raw1260 raw1262; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4458 = raw1262Labels := by decide +kernel
    rw [ha, hj, canonical1262 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4495 node4495Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1079 node1079Labels + mixedMoment B node1708 node1708Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1293 singletonSmall4495
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4495) = raw1293Labels := by decide +kernel
  rw [hl, canonical1293 B hB] at h
  have hc0 : mixedMoment B raw1293 (Fin.cases (0 : Fin 2) singletonSmall4495) =
      mixedMoment B node1079 node1079Labels := by
    have ha : raw1293 = raw1294 := by apply Matrix.ext; unfold raw1293 raw1294; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4495 = raw1294Labels := by decide +kernel
    rw [ha, hj, canonical1294 B hB]
  have hc1 : mixedMoment B raw1293 (Fin.cases (1 : Fin 2) singletonSmall4495) =
      mixedMoment B node1708 node1708Labels := by
    have ha : raw1293 = raw1295 := by apply Matrix.ext; unfold raw1293 raw1295; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4495 = raw1295Labels := by decide +kernel
    rw [ha, hj, canonical1295 B hB]
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

theorem singleton5257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5257 node5257Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2721 node2721Labels + mixedMoment B node3532 node3532Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2268 singletonSmall5257
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5257) = raw2268Labels := by decide +kernel
  rw [hl, canonical2268 B hB] at h
  have hc0 : mixedMoment B raw2268 (Fin.cases (0 : Fin 2) singletonSmall5257) =
      mixedMoment B node2721 node2721Labels := by
    have ha : raw2268 = raw2269 := by apply Matrix.ext; unfold raw2268 raw2269; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5257 = raw2269Labels := by decide +kernel
    rw [ha, hj, canonical2269 B hB]
  have hc1 : mixedMoment B raw2268 (Fin.cases (1 : Fin 2) singletonSmall5257) =
      mixedMoment B node3532 node3532Labels := by
    have ha : raw2268 = raw2270 := by apply Matrix.ext; unfold raw2268 raw2270; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5257 = raw2270Labels := by decide +kernel
    rw [ha, hj, canonical2270 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node656 node656Labels = Sparse.eval nodeValue656 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 656) = mixedMoment B node656 node656Labels := rfl
  simpa [nodeValue656, Sparse.eval] using hc.symm

theorem sound658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node658 node658Labels = Sparse.eval nodeValue658 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 658) = mixedMoment B node658 node658Labels := rfl
  simpa [nodeValue658, Sparse.eval] using hc.symm

theorem sound662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node662 node662Labels = Sparse.eval nodeValue662 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 662) = mixedMoment B node662 node662Labels := rfl
  simpa [nodeValue662, Sparse.eval] using hc.symm

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

theorem sound919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node919 node919Labels = Sparse.eval nodeValue919 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 919) = mixedMoment B node919 node919Labels := rfl
  simpa [nodeValue919, Sparse.eval] using hc.symm

theorem sound922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node922 node922Labels = Sparse.eval nodeValue922 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 922) = mixedMoment B node922 node922Labels := rfl
  simpa [nodeValue922, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node977 node977Labels = Sparse.eval nodeValue977 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 977) = mixedMoment B node977 node977Labels := rfl
  simpa [nodeValue977, Sparse.eval] using hc.symm

theorem sound980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node980 node980Labels = Sparse.eval nodeValue980 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 980) = mixedMoment B node980 node980Labels := rfl
  simpa [nodeValue980, Sparse.eval] using hc.symm

theorem sound998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node998 node998Labels = Sparse.eval nodeValue998 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 998) = mixedMoment B node998 node998Labels := rfl
  simpa [nodeValue998, Sparse.eval] using hc.symm

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

theorem sound1040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1040 node1040Labels = Sparse.eval nodeValue1040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1040) = mixedMoment B node1040 node1040Labels := rfl
  simpa [nodeValue1040, Sparse.eval] using hc.symm

theorem sound1041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1041 node1041Labels = Sparse.eval nodeValue1041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1041) = mixedMoment B node1041 node1041Labels := rfl
  simpa [nodeValue1041, Sparse.eval] using hc.symm

theorem sound1079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1079 node1079Labels = Sparse.eval nodeValue1079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1079) = mixedMoment B node1079 node1079Labels := rfl
  simpa [nodeValue1079, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1597 node1597Labels = Sparse.eval nodeValue1597 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1597) = mixedMoment B node1597 node1597Labels := rfl
  simpa [nodeValue1597, Sparse.eval] using hc.symm

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

theorem sound1600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1600 node1600Labels = Sparse.eval nodeValue1600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1600) = mixedMoment B node1600 node1600Labels := rfl
  simpa [nodeValue1600, Sparse.eval] using hc.symm

theorem sound1616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1616 node1616Labels = Sparse.eval nodeValue1616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1616) = mixedMoment B node1616 node1616Labels := rfl
  simpa [nodeValue1616, Sparse.eval] using hc.symm

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

theorem sound1664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1664 node1664Labels = Sparse.eval nodeValue1664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1664) = mixedMoment B node1664 node1664Labels := rfl
  simpa [nodeValue1664, Sparse.eval] using hc.symm

theorem sound1673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1673 node1673Labels = Sparse.eval nodeValue1673 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1673) = mixedMoment B node1673 node1673Labels := rfl
  simpa [nodeValue1673, Sparse.eval] using hc.symm

theorem sound1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1707 node1707Labels = Sparse.eval nodeValue1707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1707) = mixedMoment B node1707 node1707Labels := rfl
  simpa [nodeValue1707, Sparse.eval] using hc.symm

theorem sound1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1708 node1708Labels = Sparse.eval nodeValue1708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1708) = mixedMoment B node1708 node1708Labels := rfl
  simpa [nodeValue1708, Sparse.eval] using hc.symm

theorem sound1724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1724 node1724Labels = Sparse.eval nodeValue1724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1724) = mixedMoment B node1724 node1724Labels := rfl
  simpa [nodeValue1724, Sparse.eval] using hc.symm

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

theorem sound2721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2721 node2721Labels = Sparse.eval nodeValue2721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2721) = mixedMoment B node2721 node2721Labels := rfl
  simpa [nodeValue2721, Sparse.eval] using hc.symm

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

theorem sound3532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3532 node3532Labels = Sparse.eval nodeValue3532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3532) = mixedMoment B node3532 node3532Labels := rfl
  simpa [nodeValue3532, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node535 node535Labels = Sparse.eval nodeValue535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 535) = mixedMoment B node535 node535Labels := rfl
  simpa [nodeValue535, Sparse.eval] using hc.symm

theorem sound537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node537 node537Labels = Sparse.eval nodeValue537 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 537) = mixedMoment B node537 node537Labels := rfl
  simpa [nodeValue537, Sparse.eval] using hc.symm

theorem sound550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node550 node550Labels = Sparse.eval nodeValue550 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 550) = mixedMoment B node550 node550Labels := rfl
  simpa [nodeValue550, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4098 node4098Labels = Sparse.eval nodeValue4098 (mixedVector B) := by
  have h := singleton4098 B _hB
  rw [sound535 B _hB _hF, sound656 B _hB _hF] at h
  norm_num [nodeValue4098, nodeValue535, nodeValue656, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4100 node4100Labels = Sparse.eval nodeValue4100 (mixedVector B) := by
  have h := singleton4100 B _hB
  rw [sound537 B _hB _hF, sound662 B _hB _hF] at h
  norm_num [nodeValue4100, nodeValue537, nodeValue662, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4113 node4113Labels = Sparse.eval nodeValue4113 (mixedVector B) := by
  have h := singleton4113 B _hB
  rw [sound550 B _hB _hF, sound658 B _hB _hF] at h
  norm_num [nodeValue4113, nodeValue550, nodeValue658, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4341 node4341Labels = Sparse.eval nodeValue4341 (mixedVector B) := by
  have h := singleton4341 B _hB
  rw [sound919 B _hB _hF, sound1664 B _hB _hF] at h
  norm_num [nodeValue4341, nodeValue919, nodeValue1664, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4344 node4344Labels = Sparse.eval nodeValue4344 (mixedVector B) := by
  have h := singleton4344 B _hB
  rw [sound922 B _hB _hF, sound1673 B _hB _hF] at h
  norm_num [nodeValue4344, nodeValue922, nodeValue1673, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4396 node4396Labels = Sparse.eval nodeValue4396 (mixedVector B) := by
  have h := singleton4396 B _hB
  rw [sound977 B _hB _hF, sound1597 B _hB _hF] at h
  norm_num [nodeValue4396, nodeValue977, nodeValue1597, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4399 node4399Labels = Sparse.eval nodeValue4399 (mixedVector B) := by
  have h := singleton4399 B _hB
  rw [sound980 B _hB _hF, sound1616 B _hB _hF] at h
  norm_num [nodeValue4399, nodeValue980, nodeValue1616, Sparse.eval] at h ⊢
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

theorem sound4417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4417 node4417Labels = Sparse.eval nodeValue4417 (mixedVector B) := by
  have h := singleton4417 B _hB
  rw [sound998 B _hB _hF, sound1600 B _hB _hF] at h
  norm_num [nodeValue4417, nodeValue998, nodeValue1600, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4457 node4457Labels = Sparse.eval nodeValue4457 (mixedVector B) := by
  have h := singleton4457 B _hB
  rw [sound1040 B _hB _hF, sound1707 B _hB _hF] at h
  norm_num [nodeValue4457, nodeValue1040, nodeValue1707, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4458 node4458Labels = Sparse.eval nodeValue4458 (mixedVector B) := by
  have h := singleton4458 B _hB
  rw [sound1041 B _hB _hF, sound1724 B _hB _hF] at h
  norm_num [nodeValue4458, nodeValue1041, nodeValue1724, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4495 node4495Labels = Sparse.eval nodeValue4495 (mixedVector B) := by
  have h := singleton4495 B _hB
  rw [sound1079 B _hB _hF, sound1708 B _hB _hF] at h
  norm_num [nodeValue4495, nodeValue1079, nodeValue1708, Sparse.eval] at h ⊢
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

theorem sound5257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5257 node5257Labels = Sparse.eval nodeValue5257 (mixedVector B) := by
  have h := singleton5257 B _hB
  rw [sound2721 B _hB _hF, sound3532 B _hB _hF] at h
  norm_num [nodeValue5257, nodeValue2721, nodeValue3532, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources58
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1874 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1874 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1874 + difference 0 1) (sourceB1874 + difference 1 0) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA1874 + difference 0 1) (sourceB1874 + difference 1 0) sourceC1874) = raw26972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26972; decide +kernel
    rw [ha]
    exact (canonical26972 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1874 + difference 0 2) (sourceB1874 + difference 2 0) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1874 + difference 0 2) (sourceB1874 + difference 2 0) sourceC1874) = raw25242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw25242; decide +kernel
    rw [ha]
    exact (canonical25242 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1874 + difference 0 3) (sourceB1874 + difference 3 0) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1874 + difference 0 3) (sourceB1874 + difference 3 0) sourceC1874) = raw26973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26973; decide +kernel
    rw [ha]
    exact (canonical26973 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1874 + difference 0 4) (sourceB1874 + difference 4 0) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1874 + difference 0 4) (sourceB1874 + difference 4 0) sourceC1874) = raw26974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26974; decide +kernel
    rw [ha]
    exact (canonical26974 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1874 + difference 0 5) (sourceB1874 + difference 5 0) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1874 + difference 0 5) (sourceB1874 + difference 5 0) sourceC1874) = raw26975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26975; decide +kernel
    rw [ha]
    exact (canonical26975 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1874 + difference 1 0) (sourceB1874 + difference 0 1) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4113) := by
    have ha : (tripleCharges (sourceA1874 + difference 1 0) (sourceB1874 + difference 0 1) sourceC1874) = raw26976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26976; decide +kernel
    rw [ha]
    exact (canonical26976 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1874 + difference 1 2) (sourceB1874 + difference 2 1) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1874 + difference 1 2) (sourceB1874 + difference 2 1) sourceC1874) = raw25246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw25246; decide +kernel
    rw [ha]
    exact (canonical25246 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1874 + difference 1 3) (sourceB1874 + difference 3 1) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1874 + difference 1 3) (sourceB1874 + difference 3 1) sourceC1874) = raw26977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26977; decide +kernel
    rw [ha]
    exact (canonical26977 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1874 + difference 1 4) (sourceB1874 + difference 4 1) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1874 + difference 1 4) (sourceB1874 + difference 4 1) sourceC1874) = raw26978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26978; decide +kernel
    rw [ha]
    exact (canonical26978 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1874 + difference 1 5) (sourceB1874 + difference 5 1) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1874 + difference 1 5) (sourceB1874 + difference 5 1) sourceC1874) = raw26979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26979; decide +kernel
    rw [ha]
    exact (canonical26979 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1874 + difference 2 0) (sourceB1874 + difference 0 2) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4098) := by
    have ha : (tripleCharges (sourceA1874 + difference 2 0) (sourceB1874 + difference 0 2) sourceC1874) = raw26980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26980; decide +kernel
    rw [ha]
    exact (canonical26980 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1874 + difference 2 1) (sourceB1874 + difference 1 2) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA1874 + difference 2 1) (sourceB1874 + difference 1 2) sourceC1874) = raw26981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26981; decide +kernel
    rw [ha]
    exact (canonical26981 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1874 + difference 2 3) (sourceB1874 + difference 3 2) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1874 + difference 2 3) (sourceB1874 + difference 3 2) sourceC1874) = raw26982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26982; decide +kernel
    rw [ha]
    exact (canonical26982 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1874 + difference 2 4) (sourceB1874 + difference 4 2) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1874 + difference 2 4) (sourceB1874 + difference 4 2) sourceC1874) = raw26983 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26983; decide +kernel
    rw [ha]
    exact (canonical26983 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1874 + difference 2 5) (sourceB1874 + difference 5 2) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1874 + difference 2 5) (sourceB1874 + difference 5 2) sourceC1874) = raw26984 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26984; decide +kernel
    rw [ha]
    exact (canonical26984 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1874 + difference 3 0) (sourceB1874 + difference 0 3) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4098) := by
    have ha : (tripleCharges (sourceA1874 + difference 3 0) (sourceB1874 + difference 0 3) sourceC1874) = raw26985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26985; decide +kernel
    rw [ha]
    exact (canonical26985 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1874 + difference 3 1) (sourceB1874 + difference 1 3) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA1874 + difference 3 1) (sourceB1874 + difference 1 3) sourceC1874) = raw26986 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26986; decide +kernel
    rw [ha]
    exact (canonical26986 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1874 + difference 3 2) (sourceB1874 + difference 2 3) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1874 + difference 3 2) (sourceB1874 + difference 2 3) sourceC1874) = raw25255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw25255; decide +kernel
    rw [ha]
    exact (canonical25255 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1874 + difference 3 4) (sourceB1874 + difference 4 3) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1874 + difference 3 4) (sourceB1874 + difference 4 3) sourceC1874) = raw26987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26987; decide +kernel
    rw [ha]
    exact (canonical26987 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1874 + difference 3 5) (sourceB1874 + difference 5 3) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1874 + difference 3 5) (sourceB1874 + difference 5 3) sourceC1874) = raw26988 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26988; decide +kernel
    rw [ha]
    exact (canonical26988 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1874 + difference 4 0) (sourceB1874 + difference 0 4) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4100) := by
    have ha : (tripleCharges (sourceA1874 + difference 4 0) (sourceB1874 + difference 0 4) sourceC1874) = raw26989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26989; decide +kernel
    rw [ha]
    exact (canonical26989 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1874 + difference 4 1) (sourceB1874 + difference 1 4) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA1874 + difference 4 1) (sourceB1874 + difference 1 4) sourceC1874) = raw26990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26990; decide +kernel
    rw [ha]
    exact (canonical26990 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1874 + difference 4 2) (sourceB1874 + difference 2 4) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1874 + difference 4 2) (sourceB1874 + difference 2 4) sourceC1874) = raw23233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw23233; decide +kernel
    rw [ha]
    exact (canonical23233 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1874 + difference 4 3) (sourceB1874 + difference 3 4) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1874 + difference 4 3) (sourceB1874 + difference 3 4) sourceC1874) = raw23229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw23229; decide +kernel
    rw [ha]
    exact (canonical23229 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1874 + difference 4 5) (sourceB1874 + difference 5 4) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1874 + difference 4 5) (sourceB1874 + difference 5 4) sourceC1874) = raw26991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26991; decide +kernel
    rw [ha]
    exact (canonical26991 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1874 + difference 5 0) (sourceB1874 + difference 0 5) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4100) := by
    have ha : (tripleCharges (sourceA1874 + difference 5 0) (sourceB1874 + difference 0 5) sourceC1874) = raw25247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw25247; decide +kernel
    rw [ha]
    exact (canonical25247 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1874 + difference 5 1) (sourceB1874 + difference 1 5) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA1874 + difference 5 1) (sourceB1874 + difference 1 5) sourceC1874) = raw25248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw25248; decide +kernel
    rw [ha]
    exact (canonical25248 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1874 + difference 5 2) (sourceB1874 + difference 2 5) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1874 + difference 5 2) (sourceB1874 + difference 2 5) sourceC1874) = raw21489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw21489; decide +kernel
    rw [ha]
    exact (canonical21489 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1874 + difference 5 3) (sourceB1874 + difference 3 5) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1874 + difference 5 3) (sourceB1874 + difference 3 5) sourceC1874) = raw21485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw21485; decide +kernel
    rw [ha]
    exact (canonical21485 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1874 + difference 5 4) (sourceB1874 + difference 4 5) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1874 + difference 5 4) (sourceB1874 + difference 4 5) sourceC1874) = raw25249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw25249; decide +kernel
    rw [ha]
    exact (canonical25249 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1874 sourceB1874 sourceC1874
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1874, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1587 : Integer.Sparse.reindex keyMap MixedData.row1587 = numericRow1587 := by decide +kernel

theorem numericCheck1587 (x : Master → ℝ) : Integer.Sparse.eval numericRow1587 x =
    (17280 : ℝ) * reducedSource1587 x := by
  norm_num [numericRow1587, reducedSource1587, Integer.Sparse.eval, Sparse.eval, nodeValue4098, nodeValue4100, nodeValue4113, nodeValue4341, nodeValue4344, nodeValue4396, nodeValue4399, nodeValue4417, nodeValue4457, nodeValue4458, nodeValue4495, nodeValue5167, nodeValue5257, nodeValue5292]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1587 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1587 (mixedVector B) = 0 := by
  have h4098 : mixedVector B (Sum.inr 4098) = Sparse.eval nodeValue4098 (mixedVector B) := by
    change mixedMoment B node4098 node4098Labels = _
    exact sound4098 B hB hF
  have h4100 : mixedVector B (Sum.inr 4100) = Sparse.eval nodeValue4100 (mixedVector B) := by
    change mixedMoment B node4100 node4100Labels = _
    exact sound4100 B hB hF
  have h4113 : mixedVector B (Sum.inr 4113) = Sparse.eval nodeValue4113 (mixedVector B) := by
    change mixedMoment B node4113 node4113Labels = _
    exact sound4113 B hB hF
  have h4341 : mixedVector B (Sum.inr 4341) = Sparse.eval nodeValue4341 (mixedVector B) := by
    change mixedMoment B node4341 node4341Labels = _
    exact sound4341 B hB hF
  have h4344 : mixedVector B (Sum.inr 4344) = Sparse.eval nodeValue4344 (mixedVector B) := by
    change mixedMoment B node4344 node4344Labels = _
    exact sound4344 B hB hF
  have h4396 : mixedVector B (Sum.inr 4396) = Sparse.eval nodeValue4396 (mixedVector B) := by
    change mixedMoment B node4396 node4396Labels = _
    exact sound4396 B hB hF
  have h4399 : mixedVector B (Sum.inr 4399) = Sparse.eval nodeValue4399 (mixedVector B) := by
    change mixedMoment B node4399 node4399Labels = _
    exact sound4399 B hB hF
  have h4417 : mixedVector B (Sum.inr 4417) = Sparse.eval nodeValue4417 (mixedVector B) := by
    change mixedMoment B node4417 node4417Labels = _
    exact sound4417 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167_e B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  simpa only [sourceForm1874, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4098, h4100, h4113, h4341, h4344, h4396, h4399, h4417, h4457, h4458, h4495, h5167, h5257, h5292, reducedSource1587] using sourceEq1874 B hB

theorem rowSound1587_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1587 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1587, numericCheck1587, reducedZero1587 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587_e_oai
