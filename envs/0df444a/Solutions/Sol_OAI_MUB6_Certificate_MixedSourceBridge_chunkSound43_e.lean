-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound43_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:17:15.921621+00:00
-- url     : https://prove2.me/submissions/d425b780-d342-46cb-8580-4ce68416a56d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5485_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound688_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound694_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound695_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound700_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12926 raw12926Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw12926 raw12926Labels = mixedMoment B raw12926step0 raw12926step0Labels := by
      have ha : raw12926step0 = (fun i j => raw12926 (permutation213 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12926step0 raw12926; decide +kernel
      have hl : raw12926step0Labels = raw12926Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12926 raw12926Labels permutation213 permutation4
    mixedMoment B raw12926step0 raw12926step0Labels = mixedMoment B raw12926step1 raw12926step1Labels := by
      have ha : raw12926step1 = -raw12926step0 := by apply Matrix.ext; change ∀ i j, raw12926step1 i j = -(raw12926step0 i j); unfold raw12926step1 raw12926step0; decide +kernel
      have hl : raw12926step1Labels = raw12926step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2089 node2089Labels := by rfl

theorem canonical12927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12927 raw12927Labels = mixedMoment B node2926 node2926Labels := by
  calc
    mixedMoment B raw12927 raw12927Labels = mixedMoment B raw12927step0 raw12927step0Labels := by
      have ha : raw12927step0 = (fun i j => raw12927 (permutation501 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12927step0 raw12927; decide +kernel
      have hl : raw12927step0Labels = raw12927Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12927 raw12927Labels permutation501 permutation2
    _ = mixedMoment B node2926 node2926Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13189 raw13189Labels = mixedMoment B node2750 node2750Labels := by
  calc
    _ = mixedMoment B node2750 node2750Labels := by rfl

theorem canonical13190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13190 raw13190Labels = mixedMoment B node3880 node3880Labels := by
  calc
    _ = mixedMoment B node3880 node3880Labels := by rfl

theorem canonical13191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13191 raw13191Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw13191 raw13191Labels = mixedMoment B raw13191step0 raw13191step0Labels := by
      have ha : raw13191step0 = (fun i j => raw13191 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13191step0 raw13191; decide +kernel
      have hl : raw13191step0Labels = raw13191Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13191 raw13191Labels permutation176 permutation2
    _ = mixedMoment B node3880 node3880Labels := by rfl

theorem canonical13192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13192 raw13192Labels = mixedMoment B node3901 node3901Labels := by
  calc
    mixedMoment B raw13192 raw13192Labels = mixedMoment B raw13192step0 raw13192step0Labels := by
      have ha : raw13192step0 = (fun i j => raw13192 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13192step0 raw13192; decide +kernel
      have hl : raw13192step0Labels = raw13192Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13192 raw13192Labels permutation200 permutation2
    _ = mixedMoment B node3901 node3901Labels := by rfl

theorem canonical13193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13193 raw13193Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw13193 raw13193Labels = mixedMoment B raw13193step0 raw13193step0Labels := by
      have hz : ∀ j, raw13193 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13193step0 = (fun i j => raw13193 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13193step0 raw13193; decide +kernel
      have hl : raw13193step0Labels = raw13193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13193 raw13193Labels permutation520 hz
    _ = mixedMoment B node3910 node3910Labels := by rfl

theorem canonical13194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13194 raw13194Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw13194 raw13194Labels = mixedMoment B raw13194step0 raw13194step0Labels := by
      have ha : raw13194step0 = (fun i j => raw13194 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13194step0 raw13194; decide +kernel
      have hl : raw13194step0Labels = raw13194Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13194 raw13194Labels permutation156 permutation2
    _ = mixedMoment B node3909 node3909Labels := by rfl

theorem canonical13195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13195 raw13195Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw13195 raw13195Labels = mixedMoment B raw13195step0 raw13195step0Labels := by
      have hz : ∀ j, raw13195 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13195step0 = (fun i j => raw13195 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13195step0 raw13195; decide +kernel
      have hl : raw13195step0Labels = raw13195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13195 raw13195Labels permutation520 hz
    mixedMoment B raw13195step0 raw13195step0Labels = mixedMoment B raw13195step1 raw13195step1Labels := by
      have ha : raw13195step1 = (fun i j => raw13195step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw13195step1 raw13195step0; decide +kernel
      have hl : raw13195step1Labels = raw13195step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13195step0 raw13195step0Labels permutation44 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical13196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13196 raw13196Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw13196 raw13196Labels = mixedMoment B raw13196step0 raw13196step0Labels := by
      have ha : raw13196step0 = (fun i j => raw13196 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13196step0 raw13196; decide +kernel
      have hl : raw13196step0Labels = raw13196Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13196 raw13196Labels permutation184 permutation2
    _ = mixedMoment B node1260 node1260Labels := by rfl

theorem canonical13197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13197 raw13197Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw13197 raw13197Labels = mixedMoment B raw13197step0 raw13197step0Labels := by
      have ha : raw13197step0 = (fun i j => raw13197 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13197step0 raw13197; decide +kernel
      have hl : raw13197step0Labels = raw13197Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13197 raw13197Labels permutation160 permutation2
    _ = mixedMoment B node1260 node1260Labels := by rfl

theorem canonical13198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13198 raw13198Labels = mixedMoment B node1250 node1250Labels := by
  calc
    mixedMoment B raw13198 raw13198Labels = mixedMoment B raw13198step0 raw13198step0Labels := by
      have ha : raw13198step0 = (fun i j => raw13198 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13198step0 raw13198; decide +kernel
      have hl : raw13198step0Labels = raw13198Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13198 raw13198Labels permutation155 permutation2
    _ = mixedMoment B node1250 node1250Labels := by rfl

theorem canonical13199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13199 raw13199Labels = mixedMoment B node1248 node1248Labels := by
  calc
    mixedMoment B raw13199 raw13199Labels = mixedMoment B raw13199step0 raw13199step0Labels := by
      have ha : raw13199step0 = (fun i j => raw13199 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13199step0 raw13199; decide +kernel
      have hl : raw13199step0Labels = raw13199Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13199 raw13199Labels permutation153 permutation2
    _ = mixedMoment B node1248 node1248Labels := by rfl

theorem canonical13200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13200 raw13200Labels = mixedMoment B node1247 node1247Labels := by
  calc
    _ = mixedMoment B node1247 node1247Labels := by rfl

theorem canonical13201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13201 raw13201Labels = mixedMoment B node2631 node2631Labels := by
  calc
    mixedMoment B raw13201 raw13201Labels = mixedMoment B raw13201step0 raw13201step0Labels := by
      have ha : raw13201step0 = (fun i j => raw13201 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13201step0 raw13201; decide +kernel
      have hl : raw13201step0Labels = raw13201Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13201 raw13201Labels permutation184 permutation2
    _ = mixedMoment B node2631 node2631Labels := by rfl

theorem canonical13202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13202 raw13202Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw13202 raw13202Labels = mixedMoment B raw13202step0 raw13202step0Labels := by
      have ha : raw13202step0 = (fun i j => raw13202 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13202step0 raw13202; decide +kernel
      have hl : raw13202step0Labels = raw13202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13202 raw13202Labels permutation208 permutation2
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical13203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13203 raw13203Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw13203 raw13203Labels = mixedMoment B raw13203step0 raw13203step0Labels := by
      have hz : ∀ j, raw13203 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13203step0 = (fun i j => raw13203 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13203step0 raw13203; decide +kernel
      have hl : raw13203step0Labels = raw13203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13203 raw13203Labels permutation520 hz
    mixedMoment B raw13203step0 raw13203step0Labels = mixedMoment B raw13203step1 raw13203step1Labels := by
      have ha : raw13203step1 = (fun i j => raw13203step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13203step1 raw13203step0; decide +kernel
      have hl : raw13203step1Labels = raw13203step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13203step0 raw13203step0Labels permutation40 permutation2
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical13204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13204 raw13204Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw13204 raw13204Labels = mixedMoment B raw13204step0 raw13204step0Labels := by
      have ha : raw13204step0 = (fun i j => raw13204 (permutation197 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13204step0 raw13204; decide +kernel
      have hl : raw13204step0Labels = raw13204Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13204 raw13204Labels permutation197 permutation2
    _ = mixedMoment B node2750 node2750Labels := by rfl

theorem canonical13205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13205 raw13205Labels = mixedMoment B node2631 node2631Labels := by
  calc
    mixedMoment B raw13205 raw13205Labels = mixedMoment B raw13205step0 raw13205step0Labels := by
      have ha : raw13205step0 = (fun i j => raw13205 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13205step0 raw13205; decide +kernel
      have hl : raw13205step0Labels = raw13205Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13205 raw13205Labels permutation160 permutation2
    _ = mixedMoment B node2631 node2631Labels := by rfl

theorem canonical13206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13206 raw13206Labels = mixedMoment B node2625 node2625Labels := by
  calc
    mixedMoment B raw13206 raw13206Labels = mixedMoment B raw13206step0 raw13206step0Labels := by
      have ha : raw13206step0 = (fun i j => raw13206 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13206step0 raw13206; decide +kernel
      have hl : raw13206step0Labels = raw13206Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13206 raw13206Labels permutation155 permutation2
    _ = mixedMoment B node2625 node2625Labels := by rfl

theorem canonical13207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13207 raw13207Labels = mixedMoment B node2623 node2623Labels := by
  calc
    mixedMoment B raw13207 raw13207Labels = mixedMoment B raw13207step0 raw13207step0Labels := by
      have ha : raw13207step0 = (fun i j => raw13207 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13207step0 raw13207; decide +kernel
      have hl : raw13207step0Labels = raw13207Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13207 raw13207Labels permutation153 permutation2
    _ = mixedMoment B node2623 node2623Labels := by rfl

theorem canonical13208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13208 raw13208Labels = mixedMoment B node2622 node2622Labels := by
  calc
    _ = mixedMoment B node2622 node2622Labels := by rfl

theorem canonical13209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13209 raw13209Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw13209 raw13209Labels = mixedMoment B raw13209step0 raw13209step0Labels := by
      have ha : raw13209step0 = (fun i j => raw13209 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13209step0 raw13209; decide +kernel
      have hl : raw13209step0Labels = raw13209Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13209 raw13209Labels permutation157 permutation2
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical13210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13210 raw13210Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw13210 raw13210Labels = mixedMoment B raw13210step0 raw13210step0Labels := by
      have ha : raw13210step0 = (fun i j => raw13210 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13210step0 raw13210; decide +kernel
      have hl : raw13210step0Labels = raw13210Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13210 raw13210Labels permutation181 permutation2
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical13211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13211 raw13211Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw13211 raw13211Labels = mixedMoment B raw13211step0 raw13211step0Labels := by
      have ha : raw13211step0 = (fun i j => raw13211 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13211step0 raw13211; decide +kernel
      have hl : raw13211step0Labels = raw13211Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13211 raw13211Labels permutation499 permutation6
    mixedMoment B raw13211step0 raw13211step0Labels = mixedMoment B raw13211step1 raw13211step1Labels := by
      have ha : raw13211step1 = raw13211step0 := by apply Matrix.ext; unfold raw13211step1 raw13211step0; decide +kernel
      have hl : raw13211step0Labels = labelEmbedding9 ∘ raw13211step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13211step0 raw13211step0Labels raw13211step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical13212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13212 raw13212Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw13212 raw13212Labels = mixedMoment B raw13212step0 raw13212step0Labels := by
      have ha : raw13212step0 = (fun i j => raw13212 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13212step0 raw13212; decide +kernel
      have hl : raw13212step0Labels = raw13212Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13212 raw13212Labels permutation499 permutation6
    mixedMoment B raw13212step0 raw13212step0Labels = mixedMoment B raw13212step1 raw13212step1Labels := by
      have ha : raw13212step1 = raw13212step0 := by apply Matrix.ext; unfold raw13212step1 raw13212step0; decide +kernel
      have hl : raw13212step0Labels = labelEmbedding9 ∘ raw13212step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13212step0 raw13212step0Labels raw13212step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

theorem canonical13213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13213 raw13213Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw13213 raw13213Labels = mixedMoment B raw13213step0 raw13213step0Labels := by
      have hz : ∀ j, raw13213 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13213step0 = (fun i j => raw13213 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13213step0 raw13213; decide +kernel
      have hl : raw13213step0Labels = raw13213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13213 raw13213Labels permutation590 hz
    mixedMoment B raw13213step0 raw13213step0Labels = mixedMoment B raw13213step1 raw13213step1Labels := by
      have ha : raw13213step1 = (fun i j => raw13213step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13213step1 raw13213step0; decide +kernel
      have hl : raw13213step1Labels = raw13213step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13213step0 raw13213step0Labels permutation125 permutation7
    mixedMoment B raw13213step1 raw13213step1Labels = mixedMoment B raw13213step2 raw13213step2Labels := by
      have ha : raw13213step2 = raw13213step1 := by apply Matrix.ext; unfold raw13213step2 raw13213step1; decide +kernel
      have hl : raw13213step1Labels = labelEmbedding10 ∘ raw13213step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13213step1 raw13213step1Labels raw13213step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

theorem canonical13214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13214 raw13214Labels = mixedMoment B node4449 node4449Labels := by
  calc
    mixedMoment B raw13214 raw13214Labels = mixedMoment B raw13214step0 raw13214step0Labels := by
      have ha : raw13214step0 = (fun i j => raw13214 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13214step0 raw13214; decide +kernel
      have hl : raw13214step0Labels = raw13214Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13214 raw13214Labels permutation185 permutation3
    mixedMoment B raw13214step0 raw13214step0Labels = mixedMoment B raw13214step1 raw13214step1Labels := by
      have ha : raw13214step1 = raw13214step0 := by apply Matrix.ext; unfold raw13214step1 raw13214step0; decide +kernel
      have hl : raw13214step0Labels = labelEmbedding6 ∘ raw13214step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13214step0 raw13214step0Labels raw13214step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4449 node4449Labels := by rfl

theorem canonical13215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13215 raw13215Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw13215 raw13215Labels = mixedMoment B raw13215step0 raw13215step0Labels := by
      have ha : raw13215step0 = (fun i j => raw13215 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13215step0 raw13215; decide +kernel
      have hl : raw13215step0Labels = raw13215Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13215 raw13215Labels permutation185 permutation3
    mixedMoment B raw13215step0 raw13215step0Labels = mixedMoment B raw13215step1 raw13215step1Labels := by
      have ha : raw13215step1 = raw13215step0 := by apply Matrix.ext; unfold raw13215step1 raw13215step0; decide +kernel
      have hl : raw13215step0Labels = labelEmbedding6 ∘ raw13215step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13215step0 raw13215step0Labels raw13215step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

theorem canonical13216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13216 raw13216Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw13216 raw13216Labels = mixedMoment B raw13216step0 raw13216step0Labels := by
      have ha : raw13216step0 = (fun i j => raw13216 (permutation209 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13216step0 raw13216; decide +kernel
      have hl : raw13216step0Labels = raw13216Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13216 raw13216Labels permutation209 permutation3
    mixedMoment B raw13216step0 raw13216step0Labels = mixedMoment B raw13216step1 raw13216step1Labels := by
      have ha : raw13216step1 = raw13216step0 := by apply Matrix.ext; unfold raw13216step1 raw13216step0; decide +kernel
      have hl : raw13216step0Labels = labelEmbedding6 ∘ raw13216step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13216step0 raw13216step0Labels raw13216step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

theorem canonical13217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13217 raw13217Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw13217 raw13217Labels = mixedMoment B raw13217step0 raw13217step0Labels := by
      have ha : raw13217step0 = (fun i j => raw13217 (permutation233 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13217step0 raw13217; decide +kernel
      have hl : raw13217step0Labels = raw13217Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13217 raw13217Labels permutation233 permutation3
    mixedMoment B raw13217step0 raw13217step0Labels = mixedMoment B raw13217step1 raw13217step1Labels := by
      have ha : raw13217step1 = raw13217step0 := by apply Matrix.ext; unfold raw13217step1 raw13217step0; decide +kernel
      have hl : raw13217step0Labels = labelEmbedding6 ∘ raw13217step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13217step0 raw13217step0Labels raw13217step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

theorem canonical13218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13218 raw13218Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw13218 raw13218Labels = mixedMoment B raw13218step0 raw13218step0Labels := by
      have hz : ∀ j, raw13218 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13218step0 = (fun i j => raw13218 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13218step0 raw13218; decide +kernel
      have hl : raw13218step0Labels = raw13218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13218 raw13218Labels permutation590 hz
    mixedMoment B raw13218step0 raw13218step0Labels = mixedMoment B raw13218step1 raw13218step1Labels := by
      have ha : raw13218step1 = (fun i j => raw13218step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13218step1 raw13218step0; decide +kernel
      have hl : raw13218step1Labels = raw13218step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13218step0 raw13218step0Labels permutation41 permutation3
    mixedMoment B raw13218step1 raw13218step1Labels = mixedMoment B raw13218step2 raw13218step2Labels := by
      have ha : raw13218step2 = raw13218step1 := by apply Matrix.ext; unfold raw13218step2 raw13218step1; decide +kernel
      have hl : raw13218step1Labels = labelEmbedding6 ∘ raw13218step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13218step1 raw13218step1Labels raw13218step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical13219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13219 raw13219Labels = mixedMoment B node4449 node4449Labels := by
  calc
    mixedMoment B raw13219 raw13219Labels = mixedMoment B raw13219step0 raw13219step0Labels := by
      have ha : raw13219step0 = (fun i j => raw13219 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13219step0 raw13219; decide +kernel
      have hl : raw13219step0Labels = raw13219Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13219 raw13219Labels permutation161 permutation3
    mixedMoment B raw13219step0 raw13219step0Labels = mixedMoment B raw13219step1 raw13219step1Labels := by
      have ha : raw13219step1 = raw13219step0 := by apply Matrix.ext; unfold raw13219step1 raw13219step0; decide +kernel
      have hl : raw13219step0Labels = labelEmbedding6 ∘ raw13219step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13219step0 raw13219step0Labels raw13219step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4449 node4449Labels := by rfl

theorem canonical13220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13220 raw13220Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw13220 raw13220Labels = mixedMoment B raw13220step0 raw13220step0Labels := by
      have ha : raw13220step0 = (fun i j => raw13220 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13220step0 raw13220; decide +kernel
      have hl : raw13220step0Labels = raw13220Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13220 raw13220Labels permutation161 permutation3
    mixedMoment B raw13220step0 raw13220step0Labels = mixedMoment B raw13220step1 raw13220step1Labels := by
      have ha : raw13220step1 = raw13220step0 := by apply Matrix.ext; unfold raw13220step1 raw13220step0; decide +kernel
      have hl : raw13220step0Labels = labelEmbedding6 ∘ raw13220step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13220step0 raw13220step0Labels raw13220step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

theorem canonical13221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13221 raw13221Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw13221 raw13221Labels = mixedMoment B raw13221step0 raw13221step0Labels := by
      have ha : raw13221step0 = (fun i j => raw13221 (permutation203 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13221step0 raw13221; decide +kernel
      have hl : raw13221step0Labels = raw13221Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13221 raw13221Labels permutation203 permutation3
    mixedMoment B raw13221step0 raw13221step0Labels = mixedMoment B raw13221step1 raw13221step1Labels := by
      have ha : raw13221step1 = raw13221step0 := by apply Matrix.ext; unfold raw13221step1 raw13221step0; decide +kernel
      have hl : raw13221step0Labels = labelEmbedding6 ∘ raw13221step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13221step0 raw13221step0Labels raw13221step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

theorem canonical13222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13222 raw13222Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw13222 raw13222Labels = mixedMoment B raw13222step0 raw13222step0Labels := by
      have ha : raw13222step0 = (fun i j => raw13222 (permutation227 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13222step0 raw13222; decide +kernel
      have hl : raw13222step0Labels = raw13222Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13222 raw13222Labels permutation227 permutation3
    mixedMoment B raw13222step0 raw13222step0Labels = mixedMoment B raw13222step1 raw13222step1Labels := by
      have ha : raw13222step1 = raw13222step0 := by apply Matrix.ext; unfold raw13222step1 raw13222step0; decide +kernel
      have hl : raw13222step0Labels = labelEmbedding6 ∘ raw13222step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13222step0 raw13222step0Labels raw13222step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

theorem canonical13223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13223 raw13223Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw13223 raw13223Labels = mixedMoment B raw13223step0 raw13223step0Labels := by
      have hz : ∀ j, raw13223 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13223step0 = (fun i j => raw13223 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13223step0 raw13223; decide +kernel
      have hl : raw13223step0Labels = raw13223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13223 raw13223Labels permutation590 hz
    mixedMoment B raw13223step0 raw13223step0Labels = mixedMoment B raw13223step1 raw13223step1Labels := by
      have ha : raw13223step1 = (fun i j => raw13223step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13223step1 raw13223step0; decide +kernel
      have hl : raw13223step1Labels = raw13223step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13223step0 raw13223step0Labels permutation35 permutation3
    mixedMoment B raw13223step1 raw13223step1Labels = mixedMoment B raw13223step2 raw13223step2Labels := by
      have ha : raw13223step2 = raw13223step1 := by apply Matrix.ext; unfold raw13223step2 raw13223step1; decide +kernel
      have hl : raw13223step1Labels = labelEmbedding6 ∘ raw13223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13223step1 raw13223step1Labels raw13223step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical13224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13224 raw13224Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw13224 raw13224Labels = mixedMoment B raw13224step0 raw13224step0Labels := by
      have ha : raw13224step0 = (fun i j => raw13224 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13224step0 raw13224; decide +kernel
      have hl : raw13224step0Labels = raw13224Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13224 raw13224Labels permutation155 permutation3
    mixedMoment B raw13224step0 raw13224step0Labels = mixedMoment B raw13224step1 raw13224step1Labels := by
      have ha : raw13224step1 = raw13224step0 := by apply Matrix.ext; unfold raw13224step1 raw13224step0; decide +kernel
      have hl : raw13224step0Labels = labelEmbedding6 ∘ raw13224step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13224step0 raw13224step0Labels raw13224step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4439 node4439Labels := by rfl

theorem canonical13225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13225 raw13225Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw13225 raw13225Labels = mixedMoment B raw13225step0 raw13225step0Labels := by
      have ha : raw13225step0 = (fun i j => raw13225 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13225step0 raw13225; decide +kernel
      have hl : raw13225step0Labels = raw13225Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13225 raw13225Labels permutation155 permutation3
    mixedMoment B raw13225step0 raw13225step0Labels = mixedMoment B raw13225step1 raw13225step1Labels := by
      have ha : raw13225step1 = raw13225step0 := by apply Matrix.ext; unfold raw13225step1 raw13225step0; decide +kernel
      have hl : raw13225step0Labels = labelEmbedding6 ∘ raw13225step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13225step0 raw13225step0Labels raw13225step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

theorem canonical13226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13226 raw13226Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw13226 raw13226Labels = mixedMoment B raw13226step0 raw13226step0Labels := by
      have ha : raw13226step0 = (fun i j => raw13226 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13226step0 raw13226; decide +kernel
      have hl : raw13226step0Labels = raw13226Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13226 raw13226Labels permutation179 permutation3
    mixedMoment B raw13226step0 raw13226step0Labels = mixedMoment B raw13226step1 raw13226step1Labels := by
      have ha : raw13226step1 = raw13226step0 := by apply Matrix.ext; unfold raw13226step1 raw13226step0; decide +kernel
      have hl : raw13226step0Labels = labelEmbedding6 ∘ raw13226step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13226step0 raw13226step0Labels raw13226step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

theorem canonical13227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13227 raw13227Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw13227 raw13227Labels = mixedMoment B raw13227step0 raw13227step0Labels := by
      have ha : raw13227step0 = (fun i j => raw13227 (permutation225 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13227step0 raw13227; decide +kernel
      have hl : raw13227step0Labels = raw13227Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13227 raw13227Labels permutation225 permutation3
    mixedMoment B raw13227step0 raw13227step0Labels = mixedMoment B raw13227step1 raw13227step1Labels := by
      have ha : raw13227step1 = raw13227step0 := by apply Matrix.ext; unfold raw13227step1 raw13227step0; decide +kernel
      have hl : raw13227step0Labels = labelEmbedding6 ∘ raw13227step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13227step0 raw13227step0Labels raw13227step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical13228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13228 raw13228Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw13228 raw13228Labels = mixedMoment B raw13228step0 raw13228step0Labels := by
      have hz : ∀ j, raw13228 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13228step0 = (fun i j => raw13228 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13228step0 raw13228; decide +kernel
      have hl : raw13228step0Labels = raw13228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13228 raw13228Labels permutation590 hz
    mixedMoment B raw13228step0 raw13228step0Labels = mixedMoment B raw13228step1 raw13228step1Labels := by
      have ha : raw13228step1 = (fun i j => raw13228step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13228step1 raw13228step0; decide +kernel
      have hl : raw13228step1Labels = raw13228step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13228step0 raw13228step0Labels permutation33 permutation3
    mixedMoment B raw13228step1 raw13228step1Labels = mixedMoment B raw13228step2 raw13228step2Labels := by
      have ha : raw13228step2 = raw13228step1 := by apply Matrix.ext; unfold raw13228step2 raw13228step1; decide +kernel
      have hl : raw13228step1Labels = labelEmbedding6 ∘ raw13228step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13228step1 raw13228step1Labels raw13228step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical13229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13229 raw13229Labels = mixedMoment B node4436 node4436Labels := by
  calc
    mixedMoment B raw13229 raw13229Labels = mixedMoment B raw13229step0 raw13229step0Labels := by
      have ha : raw13229step0 = (fun i j => raw13229 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13229step0 raw13229; decide +kernel
      have hl : raw13229step0Labels = raw13229Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13229 raw13229Labels permutation153 permutation3
    mixedMoment B raw13229step0 raw13229step0Labels = mixedMoment B raw13229step1 raw13229step1Labels := by
      have ha : raw13229step1 = raw13229step0 := by apply Matrix.ext; unfold raw13229step1 raw13229step0; decide +kernel
      have hl : raw13229step0Labels = labelEmbedding6 ∘ raw13229step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13229step0 raw13229step0Labels raw13229step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4436 node4436Labels := by rfl

theorem canonical13230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13230 raw13230Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw13230 raw13230Labels = mixedMoment B raw13230step0 raw13230step0Labels := by
      have ha : raw13230step0 = (fun i j => raw13230 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13230step0 raw13230; decide +kernel
      have hl : raw13230step0Labels = raw13230Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13230 raw13230Labels permutation153 permutation3
    mixedMoment B raw13230step0 raw13230step0Labels = mixedMoment B raw13230step1 raw13230step1Labels := by
      have ha : raw13230step1 = raw13230step0 := by apply Matrix.ext; unfold raw13230step1 raw13230step0; decide +kernel
      have hl : raw13230step0Labels = labelEmbedding6 ∘ raw13230step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13230step0 raw13230step0Labels raw13230step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

theorem canonical13231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13231 raw13231Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw13231 raw13231Labels = mixedMoment B raw13231step0 raw13231step0Labels := by
      have ha : raw13231step0 = (fun i j => raw13231 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13231step0 raw13231; decide +kernel
      have hl : raw13231step0Labels = raw13231Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13231 raw13231Labels permutation177 permutation3
    mixedMoment B raw13231step0 raw13231step0Labels = mixedMoment B raw13231step1 raw13231step1Labels := by
      have ha : raw13231step1 = raw13231step0 := by apply Matrix.ext; unfold raw13231step1 raw13231step0; decide +kernel
      have hl : raw13231step0Labels = labelEmbedding6 ∘ raw13231step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13231step0 raw13231step0Labels raw13231step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

theorem canonical13232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13232 raw13232Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw13232 raw13232Labels = mixedMoment B raw13232step0 raw13232step0Labels := by
      have ha : raw13232step0 = (fun i j => raw13232 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13232step0 raw13232; decide +kernel
      have hl : raw13232step0Labels = raw13232Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13232 raw13232Labels permutation201 permutation3
    mixedMoment B raw13232step0 raw13232step0Labels = mixedMoment B raw13232step1 raw13232step1Labels := by
      have ha : raw13232step1 = raw13232step0 := by apply Matrix.ext; unfold raw13232step1 raw13232step0; decide +kernel
      have hl : raw13232step0Labels = labelEmbedding6 ∘ raw13232step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13232step0 raw13232step0Labels raw13232step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

theorem canonical13233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13233 raw13233Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw13233 raw13233Labels = mixedMoment B raw13233step0 raw13233step0Labels := by
      have hz : ∀ j, raw13233 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13233step0 = (fun i j => raw13233 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13233step0 raw13233; decide +kernel
      have hl : raw13233step0Labels = raw13233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13233 raw13233Labels permutation590 hz
    mixedMoment B raw13233step0 raw13233step0Labels = mixedMoment B raw13233step1 raw13233step1Labels := by
      have ha : raw13233step1 = (fun i j => raw13233step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13233step1 raw13233step0; decide +kernel
      have hl : raw13233step1Labels = raw13233step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13233step0 raw13233step0Labels permutation32 permutation3
    mixedMoment B raw13233step1 raw13233step1Labels = mixedMoment B raw13233step2 raw13233step2Labels := by
      have ha : raw13233step2 = raw13233step1 := by apply Matrix.ext; unfold raw13233step2 raw13233step1; decide +kernel
      have hl : raw13233step1Labels = labelEmbedding6 ∘ raw13233step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13233step1 raw13233step1Labels raw13233step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

theorem canonical13234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13234 raw13234Labels = mixedMoment B node4435 node4435Labels := by
  calc
    mixedMoment B raw13234 raw13234Labels = mixedMoment B raw13234step0 raw13234step0Labels := by
      have ha : raw13234step0 = (fun i j => raw13234 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13234step0 raw13234; decide +kernel
      have hl : raw13234step0Labels = raw13234Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13234 raw13234Labels permutation152 permutation3
    mixedMoment B raw13234step0 raw13234step0Labels = mixedMoment B raw13234step1 raw13234step1Labels := by
      have ha : raw13234step1 = raw13234step0 := by apply Matrix.ext; unfold raw13234step1 raw13234step0; decide +kernel
      have hl : raw13234step0Labels = labelEmbedding6 ∘ raw13234step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13234step0 raw13234step0Labels raw13234step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4435 node4435Labels := by rfl

theorem canonical13235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13235 raw13235Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw13235 raw13235Labels = mixedMoment B raw13235step0 raw13235step0Labels := by
      have ha : raw13235step0 = (fun i j => raw13235 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13235step0 raw13235; decide +kernel
      have hl : raw13235step0Labels = raw13235Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13235 raw13235Labels permutation152 permutation3
    mixedMoment B raw13235step0 raw13235step0Labels = mixedMoment B raw13235step1 raw13235step1Labels := by
      have ha : raw13235step1 = raw13235step0 := by apply Matrix.ext; unfold raw13235step1 raw13235step0; decide +kernel
      have hl : raw13235step0Labels = labelEmbedding6 ∘ raw13235step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13235step0 raw13235step0Labels raw13235step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5144 node5144Labels := by rfl

theorem canonical13236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13236 raw13236Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw13236 raw13236Labels = mixedMoment B raw13236step0 raw13236step0Labels := by
      have ha : raw13236step0 = (fun i j => raw13236 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13236step0 raw13236; decide +kernel
      have hl : raw13236step0Labels = raw13236Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13236 raw13236Labels permutation176 permutation3
    mixedMoment B raw13236step0 raw13236step0Labels = mixedMoment B raw13236step1 raw13236step1Labels := by
      have ha : raw13236step1 = raw13236step0 := by apply Matrix.ext; unfold raw13236step1 raw13236step0; decide +kernel
      have hl : raw13236step0Labels = labelEmbedding6 ∘ raw13236step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13236step0 raw13236step0Labels raw13236step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5144 node5144Labels := by rfl

theorem canonical13237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13237 raw13237Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw13237 raw13237Labels = mixedMoment B raw13237step0 raw13237step0Labels := by
      have ha : raw13237step0 = (fun i j => raw13237 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13237step0 raw13237; decide +kernel
      have hl : raw13237step0Labels = raw13237Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13237 raw13237Labels permutation200 permutation3
    mixedMoment B raw13237step0 raw13237step0Labels = mixedMoment B raw13237step1 raw13237step1Labels := by
      have ha : raw13237step1 = raw13237step0 := by apply Matrix.ext; unfold raw13237step1 raw13237step0; decide +kernel
      have hl : raw13237step0Labels = labelEmbedding6 ∘ raw13237step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13237step0 raw13237step0Labels raw13237step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

theorem canonical13238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13238 raw13238Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw13238 raw13238Labels = mixedMoment B raw13238step0 raw13238step0Labels := by
      have ha : raw13238step0 = (fun i j => raw13238 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13238step0 raw13238; decide +kernel
      have hl : raw13238step0Labels = raw13238Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13238 raw13238Labels permutation224 permutation3
    mixedMoment B raw13238step0 raw13238step0Labels = mixedMoment B raw13238step1 raw13238step1Labels := by
      have ha : raw13238step1 = raw13238step0 := by apply Matrix.ext; unfold raw13238step1 raw13238step0; decide +kernel
      have hl : raw13238step0Labels = labelEmbedding6 ∘ raw13238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13238step0 raw13238step0Labels raw13238step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

theorem canonical13299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13299 raw13299Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13299 raw13299Labels = mixedMoment B raw13299step0 raw13299step0Labels := by
      have ha : raw13299step0 = (fun i j => raw13299 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13299step0 raw13299; decide +kernel
      have hl : raw13299step0Labels = raw13299Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13299 raw13299Labels permutation157 permutation2
    _ = mixedMoment B node3074 node3074Labels := by rfl

theorem canonical13300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13300 raw13300Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw13300 raw13300Labels = mixedMoment B raw13300step0 raw13300step0Labels := by
      have ha : raw13300step0 = (fun i j => raw13300 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13300step0 raw13300; decide +kernel
      have hl : raw13300step0Labels = raw13300Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13300 raw13300Labels permutation157 permutation2
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical13301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13301 raw13301Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw13301 raw13301Labels = mixedMoment B raw13301step0 raw13301step0Labels := by
      have ha : raw13301step0 = (fun i j => raw13301 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13301step0 raw13301; decide +kernel
      have hl : raw13301step0Labels = raw13301Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13301 raw13301Labels permutation181 permutation2
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical13302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13302 raw13302Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw13302 raw13302Labels = mixedMoment B raw13302step0 raw13302step0Labels := by
      have ha : raw13302step0 = (fun i j => raw13302 (permutation446 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13302step0 raw13302; decide +kernel
      have hl : raw13302step0Labels = raw13302Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13302 raw13302Labels permutation446 permutation4
    mixedMoment B raw13302step0 raw13302step0Labels = mixedMoment B raw13302step1 raw13302step1Labels := by
      have ha : raw13302step1 = -raw13302step0 := by apply Matrix.ext; change ∀ i j, raw13302step1 i j = -(raw13302step0 i j); unfold raw13302step1 raw13302step0; decide +kernel
      have hl : raw13302step1Labels = raw13302step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3875 node3875Labels := by rfl

theorem canonical13303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13303 raw13303Labels = mixedMoment B node4008 node4008Labels := by
  calc
    mixedMoment B raw13303 raw13303Labels = mixedMoment B raw13303step0 raw13303step0Labels := by
      have ha : raw13303step0 = (fun i j => raw13303 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13303step0 raw13303; decide +kernel
      have hl : raw13303step0Labels = raw13303Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13303 raw13303Labels permutation155 permutation2
    _ = mixedMoment B node4008 node4008Labels := by rfl

theorem canonical13304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13304 raw13304Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw13304 raw13304Labels = mixedMoment B raw13304step0 raw13304step0Labels := by
      have hz : ∀ j, raw13304 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13304step0 = (fun i j => raw13304 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13304step0 raw13304; decide +kernel
      have hl : raw13304step0Labels = raw13304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13304 raw13304Labels permutation590 hz
    mixedMoment B raw13304step0 raw13304step0Labels = mixedMoment B raw13304step1 raw13304step1Labels := by
      have ha : raw13304step1 = (fun i j => raw13304step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13304step1 raw13304step0; decide +kernel
      have hl : raw13304step1Labels = raw13304step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13304step0 raw13304step0Labels permutation33 permutation2
    _ = mixedMoment B node4010 node4010Labels := by rfl

theorem canonical13305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13305 raw13305Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw13305 raw13305Labels = mixedMoment B raw13305step0 raw13305step0Labels := by
      have hz : ∀ j, raw13305 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13305step0 = (fun i j => raw13305 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13305step0 raw13305; decide +kernel
      have hl : raw13305step0Labels = raw13305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13305 raw13305Labels permutation590 hz
    mixedMoment B raw13305step0 raw13305step0Labels = mixedMoment B raw13305step1 raw13305step1Labels := by
      have ha : raw13305step1 = (fun i j => raw13305step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw13305step1 raw13305step0; decide +kernel
      have hl : raw13305step1Labels = raw13305step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13305step0 raw13305step0Labels permutation122 permutation0
    mixedMoment B raw13305step1 raw13305step1Labels = mixedMoment B raw13305step2 raw13305step2Labels := by
      have ha : raw13305step2 = -raw13305step1 := by apply Matrix.ext; change ∀ i j, raw13305step2 i j = -(raw13305step1 i j); unfold raw13305step2 raw13305step1; decide +kernel
      have hl : raw13305step2Labels = raw13305step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical13306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13306 raw13306Labels = mixedMoment B node1403 node1403Labels := by
  calc
    mixedMoment B raw13306 raw13306Labels = mixedMoment B raw13306step0 raw13306step0Labels := by
      have ha : raw13306step0 = (fun i j => raw13306 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13306step0 raw13306; decide +kernel
      have hl : raw13306step0Labels = raw13306Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13306 raw13306Labels permutation181 permutation2
    _ = mixedMoment B node1403 node1403Labels := by rfl

theorem canonical13307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13307 raw13307Labels = mixedMoment B node1403 node1403Labels := by
  calc
    mixedMoment B raw13307 raw13307Labels = mixedMoment B raw13307step0 raw13307step0Labels := by
      have ha : raw13307step0 = (fun i j => raw13307 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13307step0 raw13307; decide +kernel
      have hl : raw13307step0Labels = raw13307Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13307 raw13307Labels permutation157 permutation2
    _ = mixedMoment B node1403 node1403Labels := by rfl

theorem canonical13308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13308 raw13308Labels = mixedMoment B node1383 node1383Labels := by
  calc
    mixedMoment B raw13308 raw13308Labels = mixedMoment B raw13308step0 raw13308step0Labels := by
      have ha : raw13308step0 = (fun i j => raw13308 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13308step0 raw13308; decide +kernel
      have hl : raw13308step0Labels = raw13308Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13308 raw13308Labels permutation157 permutation2
    _ = mixedMoment B node1383 node1383Labels := by rfl

theorem canonical13309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13309 raw13309Labels = mixedMoment B node1384 node1384Labels := by
  calc
    mixedMoment B raw13309 raw13309Labels = mixedMoment B raw13309step0 raw13309step0Labels := by
      have ha : raw13309step0 = (fun i j => raw13309 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13309step0 raw13309; decide +kernel
      have hl : raw13309step0Labels = raw13309Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13309 raw13309Labels permutation156 permutation2
    _ = mixedMoment B node1384 node1384Labels := by rfl

theorem canonical13310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13310 raw13310Labels = mixedMoment B node1387 node1387Labels := by
  calc
    mixedMoment B raw13310 raw13310Labels = mixedMoment B raw13310step0 raw13310step0Labels := by
      have ha : raw13310step0 = (fun i j => raw13310 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13310step0 raw13310; decide +kernel
      have hl : raw13310step0Labels = raw13310Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13310 raw13310Labels permutation154 permutation2
    _ = mixedMoment B node1387 node1387Labels := by rfl

theorem canonical13311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13311 raw13311Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw13311 raw13311Labels = mixedMoment B raw13311step0 raw13311step0Labels := by
      have ha : raw13311step0 = (fun i j => raw13311 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13311step0 raw13311; decide +kernel
      have hl : raw13311step0Labels = raw13311Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13311 raw13311Labels permutation157 permutation2
    _ = mixedMoment B node2951 node2951Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13312 raw13312Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw13312 raw13312Labels = mixedMoment B raw13312step0 raw13312step0Labels := by
      have ha : raw13312step0 = (fun i j => raw13312 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13312step0 raw13312; decide +kernel
      have hl : raw13312step0Labels = raw13312Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13312 raw13312Labels permutation157 permutation2
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical13313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13313 raw13313Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw13313 raw13313Labels = mixedMoment B raw13313step0 raw13313step0Labels := by
      have ha : raw13313step0 = (fun i j => raw13313 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13313step0 raw13313; decide +kernel
      have hl : raw13313step0Labels = raw13313Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13313 raw13313Labels permutation156 permutation2
    _ = mixedMoment B node2925 node2925Labels := by rfl

theorem canonical13314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13314 raw13314Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw13314 raw13314Labels = mixedMoment B raw13314step0 raw13314step0Labels := by
      have ha : raw13314step0 = (fun i j => raw13314 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13314step0 raw13314; decide +kernel
      have hl : raw13314step0Labels = raw13314Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13314 raw13314Labels permutation154 permutation2
    _ = mixedMoment B node2928 node2928Labels := by rfl

theorem canonical13315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13315 raw13315Labels = mixedMoment B node3091 node3091Labels := by
  calc
    mixedMoment B raw13315 raw13315Labels = mixedMoment B raw13315step0 raw13315step0Labels := by
      have ha : raw13315step0 = (fun i j => raw13315 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13315step0 raw13315; decide +kernel
      have hl : raw13315step0Labels = raw13315Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13315 raw13315Labels permutation183 permutation2
    _ = mixedMoment B node3091 node3091Labels := by rfl

theorem canonical13316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13316 raw13316Labels = mixedMoment B node3091 node3091Labels := by
  calc
    mixedMoment B raw13316 raw13316Labels = mixedMoment B raw13316step0 raw13316step0Labels := by
      have ha : raw13316step0 = (fun i j => raw13316 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13316step0 raw13316; decide +kernel
      have hl : raw13316step0Labels = raw13316Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13316 raw13316Labels permutation159 permutation2
    _ = mixedMoment B node3091 node3091Labels := by rfl

theorem canonical13317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13317 raw13317Labels = mixedMoment B node3068 node3068Labels := by
  calc
    mixedMoment B raw13317 raw13317Labels = mixedMoment B raw13317step0 raw13317step0Labels := by
      have ha : raw13317step0 = (fun i j => raw13317 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13317step0 raw13317; decide +kernel
      have hl : raw13317step0Labels = raw13317Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13317 raw13317Labels permutation153 permutation2
    _ = mixedMoment B node3068 node3068Labels := by rfl

theorem canonical13318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13318 raw13318Labels = mixedMoment B node3069 node3069Labels := by
  calc
    _ = mixedMoment B node3069 node3069Labels := by rfl

theorem canonical13364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13364 raw13364Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw13364 raw13364Labels = mixedMoment B raw13364step0 raw13364step0Labels := by
      have hz : ∀ j, raw13364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13364step0 = (fun i j => raw13364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13364step0 raw13364; decide +kernel
      have hl : raw13364step0Labels = raw13364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13364 raw13364Labels permutation346 hz
    mixedMoment B raw13364step0 raw13364step0Labels = mixedMoment B raw13364step1 raw13364step1Labels := by
      have ha : raw13364step1 = (fun i j => raw13364step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13364step1 raw13364step0; decide +kernel
      have hl : raw13364step1Labels = raw13364step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13364step0 raw13364step0Labels permutation37 permutation2
    mixedMoment B raw13364step1 raw13364step1Labels = mixedMoment B raw13364step2 raw13364step2Labels := by
      have ha : raw13364step2 = -raw13364step1 := by apply Matrix.ext; change ∀ i j, raw13364step2 i j = -(raw13364step1 i j); unfold raw13364step2 raw13364step1; decide +kernel
      have hl : raw13364step2Labels = raw13364step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical13365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13365 raw13365Labels = mixedMoment B node2923 node2923Labels := by
  calc
    mixedMoment B raw13365 raw13365Labels = mixedMoment B raw13365step0 raw13365step0Labels := by
      have ha : raw13365step0 = (fun i j => raw13365 (permutation502 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13365step0 raw13365; decide +kernel
      have hl : raw13365step0Labels = raw13365Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13365 raw13365Labels permutation502 permutation2
    _ = mixedMoment B node2923 node2923Labels := by rfl

theorem canonical13366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13366 raw13366Labels = mixedMoment B node3489 node3489Labels := by
  calc
    mixedMoment B raw13366 raw13366Labels = mixedMoment B raw13366step0 raw13366step0Labels := by
      have ha : raw13366step0 = (fun i j => raw13366 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13366step0 raw13366; decide +kernel
      have hl : raw13366step0Labels = raw13366Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13366 raw13366Labels permutation156 permutation2
    mixedMoment B raw13366step0 raw13366step0Labels = mixedMoment B raw13366step1 raw13366step1Labels := by
      have ha : raw13366step1 = -raw13366step0 := by apply Matrix.ext; change ∀ i j, raw13366step1 i j = -(raw13366step0 i j); unfold raw13366step1 raw13366step0; decide +kernel
      have hl : raw13366step1Labels = raw13366step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3489 node3489Labels := by rfl

theorem canonical13367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13367 raw13367Labels = mixedMoment B node3496 node3496Labels := by
  calc
    mixedMoment B raw13367 raw13367Labels = mixedMoment B raw13367step0 raw13367step0Labels := by
      have ha : raw13367step0 = (fun i j => raw13367 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13367step0 raw13367; decide +kernel
      have hl : raw13367step0Labels = raw13367Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13367 raw13367Labels permutation155 permutation2
    mixedMoment B raw13367step0 raw13367step0Labels = mixedMoment B raw13367step1 raw13367step1Labels := by
      have ha : raw13367step1 = -raw13367step0 := by apply Matrix.ext; change ∀ i j, raw13367step1 i j = -(raw13367step0 i j); unfold raw13367step1 raw13367step0; decide +kernel
      have hl : raw13367step1Labels = raw13367step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3496 node3496Labels := by rfl

theorem canonical13368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13368 raw13368Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw13368 raw13368Labels = mixedMoment B raw13368step0 raw13368step0Labels := by
      have ha : raw13368step0 = (fun i j => raw13368 (permutation215 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13368step0 raw13368; decide +kernel
      have hl : raw13368step0Labels = raw13368Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13368 raw13368Labels permutation215 permutation4
    mixedMoment B raw13368step0 raw13368step0Labels = mixedMoment B raw13368step1 raw13368step1Labels := by
      have ha : raw13368step1 = -raw13368step0 := by apply Matrix.ext; change ∀ i j, raw13368step1 i j = -(raw13368step0 i j); unfold raw13368step1 raw13368step0; decide +kernel
      have hl : raw13368step1Labels = raw13368step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2089 node2089Labels := by rfl

theorem canonical13369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13369 raw13369Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw13369 raw13369Labels = mixedMoment B raw13369step0 raw13369step0Labels := by
      have ha : raw13369step0 = (fun i j => raw13369 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13369step0 raw13369; decide +kernel
      have hl : raw13369step0Labels = raw13369Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13369 raw13369Labels permutation200 permutation4
    mixedMoment B raw13369step0 raw13369step0Labels = mixedMoment B raw13369step1 raw13369step1Labels := by
      have ha : raw13369step1 = -raw13369step0 := by apply Matrix.ext; change ∀ i j, raw13369step1 i j = -(raw13369step0 i j); unfold raw13369step1 raw13369step0; decide +kernel
      have hl : raw13369step1Labels = raw13369step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2105 node2105Labels := by rfl

theorem canonical13370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13370 raw13370Labels = mixedMoment B node2926 node2926Labels := by
  calc
    mixedMoment B raw13370 raw13370Labels = mixedMoment B raw13370step0 raw13370step0Labels := by
      have ha : raw13370step0 = (fun i j => raw13370 (permutation503 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13370step0 raw13370; decide +kernel
      have hl : raw13370step0Labels = raw13370Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13370 raw13370Labels permutation503 permutation2
    _ = mixedMoment B node2926 node2926Labels := by rfl

theorem canonical13371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13371 raw13371Labels = mixedMoment B node3073 node3073Labels := by
  calc
    mixedMoment B raw13371 raw13371Labels = mixedMoment B raw13371step0 raw13371step0Labels := by
      have ha : raw13371step0 = (fun i j => raw13371 (permutation502 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13371step0 raw13371; decide +kernel
      have hl : raw13371step0Labels = raw13371Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13371 raw13371Labels permutation502 permutation2
    _ = mixedMoment B node3073 node3073Labels := by rfl

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

theorem canonical2175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2175 raw2175Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw2175 raw2175Labels = mixedMoment B raw2175step0 raw2175step0Labels := by
      have ha : raw2175step0 = (fun i j => raw2175 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2175step0 raw2175; decide +kernel
      have hl : raw2175step0Labels = raw2175Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2175 raw2175Labels permutation152 permutation5
    mixedMoment B raw2175step0 raw2175step0Labels = mixedMoment B raw2175step1 raw2175step1Labels := by
      have ha : raw2175step1 = raw2175step0 := by apply Matrix.ext; unfold raw2175step1 raw2175step0; decide +kernel
      have hl : raw2175step0Labels = labelEmbedding8 ∘ raw2175step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2175step0 raw2175step0Labels raw2175step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

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

theorem canonical2176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2176 raw2176Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw2176 raw2176Labels = mixedMoment B raw2176step0 raw2176step0Labels := by
      have ha : raw2176step0 = (fun i j => raw2176 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2176step0 raw2176; decide +kernel
      have hl : raw2176step0Labels = raw2176Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2176 raw2176Labels permutation154 permutation4
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical2177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2177 raw2177Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw2177 raw2177Labels = mixedMoment B raw2177step0 raw2177step0Labels := by
      have ha : raw2177step0 = (fun i j => raw2177 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2177step0 raw2177; decide +kernel
      have hl : raw2177step0Labels = raw2177Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2177 raw2177Labels permutation162 permutation3
    mixedMoment B raw2177step0 raw2177step0Labels = mixedMoment B raw2177step1 raw2177step1Labels := by
      have ha : raw2177step1 = -raw2177step0 := by apply Matrix.ext; change ∀ i j, raw2177step1 i j = -(raw2177step0 i j); unfold raw2177step1 raw2177step0; decide +kernel
      have hl : raw2177step1Labels = raw2177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2177step1 raw2177step1Labels = mixedMoment B raw2177step2 raw2177step2Labels := by
      have ha : raw2177step2 = raw2177step1 := by apply Matrix.ext; unfold raw2177step2 raw2177step1; decide +kernel
      have hl : raw2177step1Labels = labelEmbedding1 ∘ raw2177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2177step1 raw2177step1Labels raw2177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem canonical2598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2598 raw2598Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw2598 raw2598Labels = mixedMoment B raw2598step0 raw2598step0Labels := by
      have ha : raw2598step0 = (fun i j => raw2598 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2598step0 raw2598; decide +kernel
      have hl : raw2598step0Labels = raw2598Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2598 raw2598Labels permutation152 permutation4
    mixedMoment B raw2598step0 raw2598step0Labels = mixedMoment B raw2598step1 raw2598step1Labels := by
      have ha : raw2598step1 = raw2598step0 := by apply Matrix.ext; unfold raw2598step1 raw2598step0; decide +kernel
      have hl : raw2598step0Labels = labelEmbedding7 ∘ raw2598step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2598step0 raw2598step0Labels raw2598step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical2599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2599 raw2599Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw2599 raw2599Labels = mixedMoment B raw2599step0 raw2599step0Labels := by
      have ha : raw2599step0 = (fun i j => raw2599 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2599step0 raw2599; decide +kernel
      have hl : raw2599step0Labels = raw2599Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2599 raw2599Labels permutation152 permutation4
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical2600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2600 raw2600Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw2600 raw2600Labels = mixedMoment B raw2600step0 raw2600step0Labels := by
      have ha : raw2600step0 = (fun i j => raw2600 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2600step0 raw2600; decide +kernel
      have hl : raw2600step0Labels = raw2600Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2600 raw2600Labels permutation688 permutation6
    mixedMoment B raw2600step0 raw2600step0Labels = mixedMoment B raw2600step1 raw2600step1Labels := by
      have ha : raw2600step1 = raw2600step0 := by apply Matrix.ext; unfold raw2600step1 raw2600step0; decide +kernel
      have hl : raw2600step0Labels = labelEmbedding1 ∘ raw2600step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2600step0 raw2600step0Labels raw2600step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11756 raw11756Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11756 raw11756Labels = mixedMoment B raw11756step0 raw11756step0Labels := by
      have hz : ∀ j, raw11756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11756step0 = (fun i j => raw11756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11756step0 raw11756; decide +kernel
      have hl : raw11756step0Labels = raw11756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11756 raw11756Labels permutation346 hz
    mixedMoment B raw11756step0 raw11756step0Labels = mixedMoment B raw11756step1 raw11756step1Labels := by
      have hz : ∀ j, raw11756step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11756step1 = (fun i j => raw11756step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11756step1 raw11756step0; decide +kernel
      have hl : raw11756step1Labels = raw11756step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11756step0 raw11756step0Labels permutation56 hz
    mixedMoment B raw11756step1 raw11756step1Labels = mixedMoment B raw11756step2 raw11756step2Labels := by
      have ha : raw11756step2 = -raw11756step1 := by apply Matrix.ext; change ∀ i j, raw11756step2 i j = -(raw11756step1 i j); unfold raw11756step2 raw11756step1; decide +kernel
      have hl : raw11756step2Labels = raw11756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

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

theorem canonical12515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12515 raw12515Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw12515 raw12515Labels = mixedMoment B raw12515step0 raw12515step0Labels := by
      have hz : ∀ j, raw12515 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12515step0 = (fun i j => raw12515 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12515step0 raw12515; decide +kernel
      have hl : raw12515step0Labels = raw12515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12515 raw12515Labels permutation265 hz
    mixedMoment B raw12515step0 raw12515step0Labels = mixedMoment B raw12515step1 raw12515step1Labels := by
      have ha : raw12515step1 = (fun i j => raw12515step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12515step1 raw12515step0; decide +kernel
      have hl : raw12515step1Labels = raw12515step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12515step0 raw12515step0Labels permutation37 permutation2
    mixedMoment B raw12515step1 raw12515step1Labels = mixedMoment B raw12515step2 raw12515step2Labels := by
      have ha : raw12515step2 = -raw12515step1 := by apply Matrix.ext; change ∀ i j, raw12515step2 i j = -(raw12515step1 i j); unfold raw12515step2 raw12515step1; decide +kernel
      have hl : raw12515step2Labels = raw12515step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical12516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12516 raw12516Labels = mixedMoment B node2088 node2088Labels := by
  calc
    mixedMoment B raw12516 raw12516Labels = mixedMoment B raw12516step0 raw12516step0Labels := by
      have ha : raw12516step0 = (fun i j => raw12516 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12516step0 raw12516; decide +kernel
      have hl : raw12516step0Labels = raw12516Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12516 raw12516Labels permutation212 permutation4
    mixedMoment B raw12516step0 raw12516step0Labels = mixedMoment B raw12516step1 raw12516step1Labels := by
      have ha : raw12516step1 = -raw12516step0 := by apply Matrix.ext; change ∀ i j, raw12516step1 i j = -(raw12516step0 i j); unfold raw12516step1 raw12516step0; decide +kernel
      have hl : raw12516step1Labels = raw12516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2088 node2088Labels := by rfl

theorem canonical12518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12518 raw12518Labels = mixedMoment B node2950 node2950Labels := by
  calc
    mixedMoment B raw12518 raw12518Labels = mixedMoment B raw12518step0 raw12518step0Labels := by
      have ha : raw12518step0 = (fun i j => raw12518 (permutation502 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12518step0 raw12518; decide +kernel
      have hl : raw12518step0Labels = raw12518Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12518 raw12518Labels permutation502 permutation2
    _ = mixedMoment B node2950 node2950Labels := by rfl

theorem canonical12520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12520 raw12520Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw12520 raw12520Labels = mixedMoment B raw12520step0 raw12520step0Labels := by
      have ha : raw12520step0 = (fun i j => raw12520 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12520step0 raw12520; decide +kernel
      have hl : raw12520step0Labels = raw12520Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12520 raw12520Labels permutation212 permutation4
    mixedMoment B raw12520step0 raw12520step0Labels = mixedMoment B raw12520step1 raw12520step1Labels := by
      have ha : raw12520step1 = -raw12520step0 := by apply Matrix.ext; change ∀ i j, raw12520step1 i j = -(raw12520step0 i j); unfold raw12520step1 raw12520step0; decide +kernel
      have hl : raw12520step1Labels = raw12520step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3571 node3571Labels := by rfl

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

theorem canonical12664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12664 raw12664Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw12664 raw12664Labels = mixedMoment B raw12664step0 raw12664step0Labels := by
      have ha : raw12664step0 = (fun i j => raw12664 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12664step0 raw12664; decide +kernel
      have hl : raw12664step0Labels = raw12664Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12664 raw12664Labels permutation212 permutation4
    mixedMoment B raw12664step0 raw12664step0Labels = mixedMoment B raw12664step1 raw12664step1Labels := by
      have ha : raw12664step1 = -raw12664step0 := by apply Matrix.ext; change ∀ i j, raw12664step1 i j = -(raw12664step0 i j); unfold raw12664step1 raw12664step0; decide +kernel
      have hl : raw12664step1Labels = raw12664step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2243 node2243Labels := by rfl

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

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ac_rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5149 node5149Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2924 node2924Labels + mixedMoment B node3605 node3605Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2175 singletonSmall5149
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5149) = raw2175Labels := by decide +kernel
  rw [hl, canonical2175 B hB] at h
  have hc0 : mixedMoment B raw2175 (Fin.cases (0 : Fin 2) singletonSmall5149) =
      mixedMoment B node2924 node2924Labels := by
    have ha : raw2175 = raw2176 := by apply Matrix.ext; unfold raw2175 raw2176; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5149 = raw2176Labels := by decide +kernel
    rw [ha, hj, canonical2176 B hB]
  have hc1 : mixedMoment B raw2175 (Fin.cases (1 : Fin 2) singletonSmall5149) =
      mixedMoment B node3605 node3605Labels := by
    have ha : raw2175 = raw2177 := by apply Matrix.ext; unfold raw2175 raw2177; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5149 = raw2177Labels := by decide +kernel
    rw [ha, hj, canonical2177 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem singleton5478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5478 node5478Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3974 node3974Labels + mixedMoment B node3974 node3974Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2598 singletonSmall5478
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5478) = raw2598Labels := by decide +kernel
  rw [hl, canonical2598 B hB] at h
  have hc0 : mixedMoment B raw2598 (Fin.cases (0 : Fin 2) singletonSmall5478) =
      mixedMoment B node3974 node3974Labels := by
    have ha : raw2598 = raw2599 := by apply Matrix.ext; unfold raw2598 raw2599; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5478 = raw2599Labels := by decide +kernel
    rw [ha, hj, canonical2599 B hB]
  have hc1 : mixedMoment B raw2598 (Fin.cases (1 : Fin 2) singletonSmall5478) =
      mixedMoment B node3974 node3974Labels := by
    have ha : raw2598 = raw2600 := by apply Matrix.ext; unfold raw2598 raw2600; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5478 = raw2600Labels := by decide +kernel
    rw [ha, hj, canonical2600 B hB]
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

theorem zero5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5481 node5481Labels = 0 := by
  exact mixedMoment_alpha B hF node5481 node5481Labels 2 permutation158
    (by decide +kernel)

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

theorem sound1247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1247 node1247Labels = Sparse.eval nodeValue1247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1247) = mixedMoment B node1247 node1247Labels := rfl
  simpa [nodeValue1247, Sparse.eval] using hc.symm

theorem sound1248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1248 node1248Labels = Sparse.eval nodeValue1248 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1248) = mixedMoment B node1248 node1248Labels := rfl
  simpa [nodeValue1248, Sparse.eval] using hc.symm

theorem sound1250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1250 node1250Labels = Sparse.eval nodeValue1250 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1250) = mixedMoment B node1250 node1250Labels := rfl
  simpa [nodeValue1250, Sparse.eval] using hc.symm

theorem sound1260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1260 node1260Labels = Sparse.eval nodeValue1260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1260) = mixedMoment B node1260 node1260Labels := rfl
  simpa [nodeValue1260, Sparse.eval] using hc.symm

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

theorem sound1383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1383 node1383Labels = Sparse.eval nodeValue1383 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1383) = mixedMoment B node1383 node1383Labels := rfl
  simpa [nodeValue1383, Sparse.eval] using hc.symm

theorem sound1384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1384 node1384Labels = Sparse.eval nodeValue1384 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1384) = mixedMoment B node1384 node1384Labels := rfl
  simpa [nodeValue1384, Sparse.eval] using hc.symm

theorem sound1387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1387 node1387Labels = Sparse.eval nodeValue1387 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1387) = mixedMoment B node1387 node1387Labels := rfl
  simpa [nodeValue1387, Sparse.eval] using hc.symm

theorem sound1403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1403 node1403Labels = Sparse.eval nodeValue1403 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1403) = mixedMoment B node1403 node1403Labels := rfl
  simpa [nodeValue1403, Sparse.eval] using hc.symm

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

theorem sound2088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2088 node2088Labels = Sparse.eval nodeValue2088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2088) = mixedMoment B node2088 node2088Labels := rfl
  simpa [nodeValue2088, Sparse.eval] using hc.symm

theorem sound2089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2089 node2089Labels = Sparse.eval nodeValue2089 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2089) = mixedMoment B node2089 node2089Labels := rfl
  simpa [nodeValue2089, Sparse.eval] using hc.symm

theorem sound2105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2105 node2105Labels = Sparse.eval nodeValue2105 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2105) = mixedMoment B node2105 node2105Labels := rfl
  simpa [nodeValue2105, Sparse.eval] using hc.symm

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

theorem sound2243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2243 node2243Labels = Sparse.eval nodeValue2243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2243) = mixedMoment B node2243 node2243Labels := rfl
  simpa [nodeValue2243, Sparse.eval] using hc.symm

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

theorem sound2622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2622 node2622Labels = Sparse.eval nodeValue2622 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2622) = mixedMoment B node2622 node2622Labels := rfl
  simpa [nodeValue2622, Sparse.eval] using hc.symm

theorem sound2623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2623 node2623Labels = Sparse.eval nodeValue2623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2623) = mixedMoment B node2623 node2623Labels := rfl
  simpa [nodeValue2623, Sparse.eval] using hc.symm

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

theorem sound2625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2625 node2625Labels = Sparse.eval nodeValue2625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2625) = mixedMoment B node2625 node2625Labels := rfl
  simpa [nodeValue2625, Sparse.eval] using hc.symm

theorem sound2631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2631 node2631Labels = Sparse.eval nodeValue2631 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2631) = mixedMoment B node2631 node2631Labels := rfl
  simpa [nodeValue2631, Sparse.eval] using hc.symm

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

theorem sound2750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2750 node2750Labels = Sparse.eval nodeValue2750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2750) = mixedMoment B node2750 node2750Labels := rfl
  simpa [nodeValue2750, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2923 node2923Labels = Sparse.eval nodeValue2923 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2923) = mixedMoment B node2923 node2923Labels := rfl
  simpa [nodeValue2923, Sparse.eval] using hc.symm

theorem sound2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2924 node2924Labels = Sparse.eval nodeValue2924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2924) = mixedMoment B node2924 node2924Labels := rfl
  simpa [nodeValue2924, Sparse.eval] using hc.symm

theorem sound2925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2925 node2925Labels = Sparse.eval nodeValue2925 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2925) = mixedMoment B node2925 node2925Labels := rfl
  simpa [nodeValue2925, Sparse.eval] using hc.symm

theorem sound2926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2926 node2926Labels = Sparse.eval nodeValue2926 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2926) = mixedMoment B node2926 node2926Labels := rfl
  simpa [nodeValue2926, Sparse.eval] using hc.symm

theorem sound2928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2928 node2928Labels = Sparse.eval nodeValue2928 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2928) = mixedMoment B node2928 node2928Labels := rfl
  simpa [nodeValue2928, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2950 node2950Labels = Sparse.eval nodeValue2950 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2950) = mixedMoment B node2950 node2950Labels := rfl
  simpa [nodeValue2950, Sparse.eval] using hc.symm

theorem sound2951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2951 node2951Labels = Sparse.eval nodeValue2951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2951) = mixedMoment B node2951 node2951Labels := rfl
  simpa [nodeValue2951, Sparse.eval] using hc.symm

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

theorem sound3068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3068 node3068Labels = Sparse.eval nodeValue3068 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3068) = mixedMoment B node3068 node3068Labels := rfl
  simpa [nodeValue3068, Sparse.eval] using hc.symm

theorem sound3069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3069 node3069Labels = Sparse.eval nodeValue3069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3069) = mixedMoment B node3069 node3069Labels := rfl
  simpa [nodeValue3069, Sparse.eval] using hc.symm

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

theorem sound3073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3073 node3073Labels = Sparse.eval nodeValue3073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3073) = mixedMoment B node3073 node3073Labels := rfl
  simpa [nodeValue3073, Sparse.eval] using hc.symm

theorem sound3074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3074 node3074Labels = Sparse.eval nodeValue3074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3074) = mixedMoment B node3074 node3074Labels := rfl
  simpa [nodeValue3074, Sparse.eval] using hc.symm

theorem sound3077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3077 node3077Labels = Sparse.eval nodeValue3077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3077) = mixedMoment B node3077 node3077Labels := rfl
  simpa [nodeValue3077, Sparse.eval] using hc.symm

theorem sound3091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3091 node3091Labels = Sparse.eval nodeValue3091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3091) = mixedMoment B node3091 node3091Labels := rfl
  simpa [nodeValue3091, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3489 node3489Labels = 0 := by
  exact mixedMoment_alpha B hF node3489 node3489Labels 1 permutation434
    (by decide +kernel)

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

theorem sound3489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3489 node3489Labels = Sparse.eval nodeValue3489 (mixedVector B) := by
  simpa only [nodeValue3489, Sparse.eval_nil] using zero3489 B _hB _hF

theorem sound3496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3496 node3496Labels = Sparse.eval nodeValue3496 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3496) = mixedMoment B node3496 node3496Labels := rfl
  simpa [nodeValue3496, Sparse.eval] using hc.symm

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

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

theorem sound3571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3571 node3571Labels = Sparse.eval nodeValue3571 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3571) = mixedMoment B node3571 node3571Labels := rfl
  simpa [nodeValue3571, Sparse.eval] using hc.symm

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

theorem sound3605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3605 node3605Labels = Sparse.eval nodeValue3605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3605) = mixedMoment B node3605 node3605Labels := rfl
  simpa [nodeValue3605, Sparse.eval] using hc.symm

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

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

theorem sound3875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3875 node3875Labels = Sparse.eval nodeValue3875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3875) = mixedMoment B node3875 node3875Labels := rfl
  simpa [nodeValue3875, Sparse.eval] using hc.symm

theorem sound3880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3880 node3880Labels = Sparse.eval nodeValue3880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3880) = mixedMoment B node3880 node3880Labels := rfl
  simpa [nodeValue3880, Sparse.eval] using hc.symm

theorem sound3901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3901 node3901Labels = Sparse.eval nodeValue3901 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3901) = mixedMoment B node3901 node3901Labels := rfl
  simpa [nodeValue3901, Sparse.eval] using hc.symm

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

theorem sound3910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3910 node3910Labels = Sparse.eval nodeValue3910 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3910) = mixedMoment B node3910 node3910Labels := rfl
  simpa [nodeValue3910, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4008 node4008Labels = 0 := by
  exact mixedMoment_alpha B hF node4008 node4008Labels 1 permutation213
    (by decide +kernel)

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

theorem sound3974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3974 node3974Labels = Sparse.eval nodeValue3974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3974) = mixedMoment B node3974 node3974Labels := rfl
  simpa [nodeValue3974, Sparse.eval] using hc.symm

theorem sound4008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4008 node4008Labels = Sparse.eval nodeValue4008 (mixedVector B) := by
  simpa only [nodeValue4008, Sparse.eval_nil] using zero4008 B _hB _hF

theorem sound4010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4010 node4010Labels = Sparse.eval nodeValue4010 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4010) = mixedMoment B node4010 node4010Labels := rfl
  simpa [nodeValue4010, Sparse.eval] using hc.symm

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

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

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

theorem sound4435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4435 node4435Labels = Sparse.eval nodeValue4435 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4435) = mixedMoment B node4435 node4435Labels := rfl
  simpa [nodeValue4435, Sparse.eval] using hc.symm

theorem sound4436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4436 node4436Labels = Sparse.eval nodeValue4436 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4436) = mixedMoment B node4436 node4436Labels := rfl
  simpa [nodeValue4436, Sparse.eval] using hc.symm

theorem sound4439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4439 node4439Labels = Sparse.eval nodeValue4439 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4439) = mixedMoment B node4439 node4439Labels := rfl
  simpa [nodeValue4439, Sparse.eval] using hc.symm

theorem sound4449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4449 node4449Labels = Sparse.eval nodeValue4449 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4449) = mixedMoment B node4449 node4449Labels := rfl
  simpa [nodeValue4449, Sparse.eval] using hc.symm

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

theorem sound5144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5144 node5144Labels = Sparse.eval nodeValue5144 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5144) = mixedMoment B node5144 node5144Labels := rfl
  simpa [nodeValue5144, Sparse.eval] using hc.symm

theorem sound5145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5145 node5145Labels = Sparse.eval nodeValue5145 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5145) = mixedMoment B node5145 node5145Labels := rfl
  simpa [nodeValue5145, Sparse.eval] using hc.symm

theorem sound5149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5149 node5149Labels = Sparse.eval nodeValue5149 (mixedVector B) := by
  have h := singleton5149 B _hB
  rw [sound2924 B _hB _hF, sound3605 B _hB _hF] at h
  norm_num [nodeValue5149, nodeValue2924, nodeValue3605, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5160 node5160Labels = Sparse.eval nodeValue5160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5160) = mixedMoment B node5160 node5160Labels := rfl
  simpa [nodeValue5160, Sparse.eval] using hc.symm

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

theorem sound5219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5219 node5219Labels = Sparse.eval nodeValue5219 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5219) = mixedMoment B node5219 node5219Labels := rfl
  simpa [nodeValue5219, Sparse.eval] using hc.symm

theorem sound5220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5220 node5220Labels = Sparse.eval nodeValue5220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5220) = mixedMoment B node5220 node5220Labels := rfl
  simpa [nodeValue5220, Sparse.eval] using hc.symm

theorem sound5226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5226 node5226Labels = Sparse.eval nodeValue5226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5226) = mixedMoment B node5226 node5226Labels := rfl
  simpa [nodeValue5226, Sparse.eval] using hc.symm

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

theorem sound5249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5249 node5249Labels = Sparse.eval nodeValue5249 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5249) = mixedMoment B node5249 node5249Labels := rfl
  simpa [nodeValue5249, Sparse.eval] using hc.symm

theorem sound5251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5251 node5251Labels = Sparse.eval nodeValue5251 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5251) = mixedMoment B node5251 node5251Labels := rfl
  simpa [nodeValue5251, Sparse.eval] using hc.symm

theorem sound5255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5255 node5255Labels = Sparse.eval nodeValue5255 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5255) = mixedMoment B node5255 node5255Labels := rfl
  simpa [nodeValue5255, Sparse.eval] using hc.symm

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

theorem sound5289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5289 node5289Labels = Sparse.eval nodeValue5289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5289) = mixedMoment B node5289 node5289Labels := rfl
  simpa [nodeValue5289, Sparse.eval] using hc.symm

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

theorem sound5431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5431 node5431Labels = Sparse.eval nodeValue5431 (mixedVector B) := by
  have h := singleton5431 B _hB
  rw [sound3849 B _hB _hF, sound3875 B _hB _hF] at h
  norm_num [nodeValue5431, nodeValue3849, nodeValue3875, Sparse.eval] at h ⊢
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

theorem sound5478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5478 node5478Labels = Sparse.eval nodeValue5478 (mixedVector B) := by
  have h := singleton5478 B _hB
  rw [sound3974 B _hB _hF] at h
  norm_num [nodeValue5478, nodeValue3974, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5481 node5481Labels = Sparse.eval nodeValue5481 (mixedVector B) := by
  simpa only [nodeValue5481, Sparse.eval_nil] using zero5481 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources24
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq797 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm797 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA797 + difference 0 0) (sourceB797 + difference 0 0) sourceC797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA797 + difference 0 0) (sourceB797 + difference 0 0) sourceC797) = raw13189 := by
      apply Matrix.ext; unfold tripleCharges sourceA797 sourceB797 sourceC797 difference raw13189; decide +kernel
    rw [ha]
    exact (canonical13189 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA797 + difference 0 1) (sourceB797 + difference 1 0) sourceC797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA797 + difference 0 1) (sourceB797 + difference 1 0) sourceC797) = raw13190 := by
      apply Matrix.ext; unfold tripleCharges sourceA797 sourceB797 sourceC797 difference raw13190; decide +kernel
    rw [ha]
    exact (canonical13190 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA797 + difference 0 2) (sourceB797 + difference 2 0) sourceC797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA797 + difference 0 2) (sourceB797 + difference 2 0) sourceC797) = raw13191 := by
      apply Matrix.ext; unfold tripleCharges sourceA797 sourceB797 sourceC797 difference raw13191; decide +kernel
    rw [ha]
    exact (canonical13191 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA797 + difference 0 3) (sourceB797 + difference 3 0) sourceC797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3901) := by
    have ha : (tripleCharges (sourceA797 + difference 0 3) (sourceB797 + difference 3 0) sourceC797) = raw13192 := by
      apply Matrix.ext; unfold tripleCharges sourceA797 sourceB797 sourceC797 difference raw13192; decide +kernel
    rw [ha]
    exact (canonical13192 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA797 + difference 0 4) (sourceB797 + difference 4 0) sourceC797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA797 + difference 0 4) (sourceB797 + difference 4 0) sourceC797) = raw13193 := by
      apply Matrix.ext; unfold tripleCharges sourceA797 sourceB797 sourceC797 difference raw13193; decide +kernel
    rw [ha]
    exact (canonical13193 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA797 + difference 0 5) (sourceB797 + difference 5 0) sourceC797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3909) := by
    have ha : (tripleCharges (sourceA797 + difference 0 5) (sourceB797 + difference 5 0) sourceC797) = raw13194 := by
      apply Matrix.ext; unfold tripleCharges sourceA797 sourceB797 sourceC797 difference raw13194; decide +kernel
    rw [ha]
    exact (canonical13194 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA797 + sourceB797) sourceC797) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA797 + sourceB797) sourceC797) = raw13195 := by
      apply Matrix.ext; unfold doubleCharges sourceA797 sourceB797 sourceC797 raw13195; decide +kernel
    rw [ha]
    exact (canonical13195 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA797 sourceB797 sourceC797
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm797, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq798 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm798 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA798 + difference 0 0) (sourceB798 + difference 0 0) sourceC798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA798 + difference 0 0) (sourceB798 + difference 0 0) sourceC798) = raw13189 := by
      apply Matrix.ext; unfold tripleCharges sourceA798 sourceB798 sourceC798 difference raw13189; decide +kernel
    rw [ha]
    exact (canonical13189 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA798 + difference 1 0) (sourceB798 + difference 0 1) sourceC798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA798 + difference 1 0) (sourceB798 + difference 0 1) sourceC798) = raw13196 := by
      apply Matrix.ext; unfold tripleCharges sourceA798 sourceB798 sourceC798 difference raw13196; decide +kernel
    rw [ha]
    exact (canonical13196 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA798 + difference 2 0) (sourceB798 + difference 0 2) sourceC798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA798 + difference 2 0) (sourceB798 + difference 0 2) sourceC798) = raw13197 := by
      apply Matrix.ext; unfold tripleCharges sourceA798 sourceB798 sourceC798 difference raw13197; decide +kernel
    rw [ha]
    exact (canonical13197 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA798 + difference 3 0) (sourceB798 + difference 0 3) sourceC798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1250) := by
    have ha : (tripleCharges (sourceA798 + difference 3 0) (sourceB798 + difference 0 3) sourceC798) = raw13198 := by
      apply Matrix.ext; unfold tripleCharges sourceA798 sourceB798 sourceC798 difference raw13198; decide +kernel
    rw [ha]
    exact (canonical13198 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA798 + difference 4 0) (sourceB798 + difference 0 4) sourceC798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1248) := by
    have ha : (tripleCharges (sourceA798 + difference 4 0) (sourceB798 + difference 0 4) sourceC798) = raw13199 := by
      apply Matrix.ext; unfold tripleCharges sourceA798 sourceB798 sourceC798 difference raw13199; decide +kernel
    rw [ha]
    exact (canonical13199 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA798 + difference 5 0) (sourceB798 + difference 0 5) sourceC798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1247) := by
    have ha : (tripleCharges (sourceA798 + difference 5 0) (sourceB798 + difference 0 5) sourceC798) = raw13200 := by
      apply Matrix.ext; unfold tripleCharges sourceA798 sourceB798 sourceC798 difference raw13200; decide +kernel
    rw [ha]
    exact (canonical13200 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA798 + sourceB798) sourceC798) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA798 + sourceB798) sourceC798) = raw13195 := by
      apply Matrix.ext; unfold doubleCharges sourceA798 sourceB798 sourceC798 raw13195; decide +kernel
    rw [ha]
    exact (canonical13195 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA798 sourceB798 sourceC798
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm798, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq799 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm799 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA799 + difference 1 0) (sourceB799 + difference 0 1) sourceC799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA799 + difference 1 0) (sourceB799 + difference 0 1) sourceC799) = raw13196 := by
      apply Matrix.ext; unfold tripleCharges sourceA799 sourceB799 sourceC799 difference raw13196; decide +kernel
    rw [ha]
    exact (canonical13196 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA799 + difference 1 1) (sourceB799 + difference 1 1) sourceC799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA799 + difference 1 1) (sourceB799 + difference 1 1) sourceC799) = raw13189 := by
      apply Matrix.ext; unfold tripleCharges sourceA799 sourceB799 sourceC799 difference raw13189; decide +kernel
    rw [ha]
    exact (canonical13189 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA799 + difference 1 2) (sourceB799 + difference 2 1) sourceC799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2631) := by
    have ha : (tripleCharges (sourceA799 + difference 1 2) (sourceB799 + difference 2 1) sourceC799) = raw13201 := by
      apply Matrix.ext; unfold tripleCharges sourceA799 sourceB799 sourceC799 difference raw13201; decide +kernel
    rw [ha]
    exact (canonical13201 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA799 + difference 1 3) (sourceB799 + difference 3 1) sourceC799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA799 + difference 1 3) (sourceB799 + difference 3 1) sourceC799) = raw13202 := by
      apply Matrix.ext; unfold tripleCharges sourceA799 sourceB799 sourceC799 difference raw13202; decide +kernel
    rw [ha]
    exact (canonical13202 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA799 + difference 1 4) (sourceB799 + difference 4 1) sourceC799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA799 + difference 1 4) (sourceB799 + difference 4 1) sourceC799) = raw13203 := by
      apply Matrix.ext; unfold tripleCharges sourceA799 sourceB799 sourceC799 difference raw13203; decide +kernel
    rw [ha]
    exact (canonical13203 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA799 + difference 1 5) (sourceB799 + difference 5 1) sourceC799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA799 + difference 1 5) (sourceB799 + difference 5 1) sourceC799) = raw13204 := by
      apply Matrix.ext; unfold tripleCharges sourceA799 sourceB799 sourceC799 difference raw13204; decide +kernel
    rw [ha]
    exact (canonical13204 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA799 + sourceB799) sourceC799) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA799 + sourceB799) sourceC799) = raw13195 := by
      apply Matrix.ext; unfold doubleCharges sourceA799 sourceB799 sourceC799 raw13195; decide +kernel
    rw [ha]
    exact (canonical13195 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA799 sourceB799 sourceC799
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm799, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources25
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq800 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm800 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA800 + difference 0 1) (sourceB800 + difference 1 0) sourceC800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA800 + difference 0 1) (sourceB800 + difference 1 0) sourceC800) = raw13190 := by
      apply Matrix.ext; unfold tripleCharges sourceA800 sourceB800 sourceC800 difference raw13190; decide +kernel
    rw [ha]
    exact (canonical13190 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA800 + difference 1 1) (sourceB800 + difference 1 1) sourceC800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA800 + difference 1 1) (sourceB800 + difference 1 1) sourceC800) = raw13189 := by
      apply Matrix.ext; unfold tripleCharges sourceA800 sourceB800 sourceC800 difference raw13189; decide +kernel
    rw [ha]
    exact (canonical13189 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA800 + difference 2 1) (sourceB800 + difference 1 2) sourceC800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2631) := by
    have ha : (tripleCharges (sourceA800 + difference 2 1) (sourceB800 + difference 1 2) sourceC800) = raw13205 := by
      apply Matrix.ext; unfold tripleCharges sourceA800 sourceB800 sourceC800 difference raw13205; decide +kernel
    rw [ha]
    exact (canonical13205 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA800 + difference 3 1) (sourceB800 + difference 1 3) sourceC800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2625) := by
    have ha : (tripleCharges (sourceA800 + difference 3 1) (sourceB800 + difference 1 3) sourceC800) = raw13206 := by
      apply Matrix.ext; unfold tripleCharges sourceA800 sourceB800 sourceC800 difference raw13206; decide +kernel
    rw [ha]
    exact (canonical13206 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA800 + difference 4 1) (sourceB800 + difference 1 4) sourceC800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2623) := by
    have ha : (tripleCharges (sourceA800 + difference 4 1) (sourceB800 + difference 1 4) sourceC800) = raw13207 := by
      apply Matrix.ext; unfold tripleCharges sourceA800 sourceB800 sourceC800 difference raw13207; decide +kernel
    rw [ha]
    exact (canonical13207 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA800 + difference 5 1) (sourceB800 + difference 1 5) sourceC800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2622) := by
    have ha : (tripleCharges (sourceA800 + difference 5 1) (sourceB800 + difference 1 5) sourceC800) = raw13208 := by
      apply Matrix.ext; unfold tripleCharges sourceA800 sourceB800 sourceC800 difference raw13208; decide +kernel
    rw [ha]
    exact (canonical13208 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA800 + sourceB800) sourceC800) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA800 + sourceB800) sourceC800) = raw13195 := by
      apply Matrix.ext; unfold doubleCharges sourceA800 sourceB800 sourceC800 raw13195; decide +kernel
    rw [ha]
    exact (canonical13195 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA800 sourceB800 sourceC800
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm800, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq801 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm801 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA801 + difference 0 1) (sourceB801 + difference 1 0) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA801 + difference 0 1) (sourceB801 + difference 1 0) sourceC801) = raw13209 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13209; decide +kernel
    rw [ha]
    exact (canonical13209 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA801 + difference 0 2) (sourceB801 + difference 2 0) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA801 + difference 0 2) (sourceB801 + difference 2 0) sourceC801) = raw13210 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13210; decide +kernel
    rw [ha]
    exact (canonical13210 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA801 + difference 0 3) (sourceB801 + difference 3 0) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA801 + difference 0 3) (sourceB801 + difference 3 0) sourceC801) = raw13211 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13211; decide +kernel
    rw [ha]
    exact (canonical13211 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA801 + difference 0 4) (sourceB801 + difference 4 0) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA801 + difference 0 4) (sourceB801 + difference 4 0) sourceC801) = raw13212 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13212; decide +kernel
    rw [ha]
    exact (canonical13212 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA801 + difference 0 5) (sourceB801 + difference 5 0) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA801 + difference 0 5) (sourceB801 + difference 5 0) sourceC801) = raw13213 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13213; decide +kernel
    rw [ha]
    exact (canonical13213 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA801 + difference 1 0) (sourceB801 + difference 0 1) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4449) := by
    have ha : (tripleCharges (sourceA801 + difference 1 0) (sourceB801 + difference 0 1) sourceC801) = raw13214 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13214; decide +kernel
    rw [ha]
    exact (canonical13214 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA801 + difference 1 2) (sourceB801 + difference 2 1) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA801 + difference 1 2) (sourceB801 + difference 2 1) sourceC801) = raw13215 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13215; decide +kernel
    rw [ha]
    exact (canonical13215 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA801 + difference 1 3) (sourceB801 + difference 3 1) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA801 + difference 1 3) (sourceB801 + difference 3 1) sourceC801) = raw13216 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13216; decide +kernel
    rw [ha]
    exact (canonical13216 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA801 + difference 1 4) (sourceB801 + difference 4 1) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA801 + difference 1 4) (sourceB801 + difference 4 1) sourceC801) = raw13217 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13217; decide +kernel
    rw [ha]
    exact (canonical13217 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA801 + difference 1 5) (sourceB801 + difference 5 1) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA801 + difference 1 5) (sourceB801 + difference 5 1) sourceC801) = raw13218 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13218; decide +kernel
    rw [ha]
    exact (canonical13218 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA801 + difference 2 0) (sourceB801 + difference 0 2) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4449) := by
    have ha : (tripleCharges (sourceA801 + difference 2 0) (sourceB801 + difference 0 2) sourceC801) = raw13219 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13219; decide +kernel
    rw [ha]
    exact (canonical13219 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA801 + difference 2 1) (sourceB801 + difference 1 2) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA801 + difference 2 1) (sourceB801 + difference 1 2) sourceC801) = raw13220 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13220; decide +kernel
    rw [ha]
    exact (canonical13220 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA801 + difference 2 3) (sourceB801 + difference 3 2) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA801 + difference 2 3) (sourceB801 + difference 3 2) sourceC801) = raw13221 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13221; decide +kernel
    rw [ha]
    exact (canonical13221 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA801 + difference 2 4) (sourceB801 + difference 4 2) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA801 + difference 2 4) (sourceB801 + difference 4 2) sourceC801) = raw13222 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13222; decide +kernel
    rw [ha]
    exact (canonical13222 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA801 + difference 2 5) (sourceB801 + difference 5 2) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA801 + difference 2 5) (sourceB801 + difference 5 2) sourceC801) = raw13223 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13223; decide +kernel
    rw [ha]
    exact (canonical13223 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA801 + difference 3 0) (sourceB801 + difference 0 3) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA801 + difference 3 0) (sourceB801 + difference 0 3) sourceC801) = raw13224 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13224; decide +kernel
    rw [ha]
    exact (canonical13224 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA801 + difference 3 1) (sourceB801 + difference 1 3) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA801 + difference 3 1) (sourceB801 + difference 1 3) sourceC801) = raw13225 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13225; decide +kernel
    rw [ha]
    exact (canonical13225 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA801 + difference 3 2) (sourceB801 + difference 2 3) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA801 + difference 3 2) (sourceB801 + difference 2 3) sourceC801) = raw13226 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13226; decide +kernel
    rw [ha]
    exact (canonical13226 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA801 + difference 3 4) (sourceB801 + difference 4 3) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA801 + difference 3 4) (sourceB801 + difference 4 3) sourceC801) = raw13227 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13227; decide +kernel
    rw [ha]
    exact (canonical13227 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA801 + difference 3 5) (sourceB801 + difference 5 3) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA801 + difference 3 5) (sourceB801 + difference 5 3) sourceC801) = raw13228 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13228; decide +kernel
    rw [ha]
    exact (canonical13228 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA801 + difference 4 0) (sourceB801 + difference 0 4) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4436) := by
    have ha : (tripleCharges (sourceA801 + difference 4 0) (sourceB801 + difference 0 4) sourceC801) = raw13229 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13229; decide +kernel
    rw [ha]
    exact (canonical13229 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA801 + difference 4 1) (sourceB801 + difference 1 4) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA801 + difference 4 1) (sourceB801 + difference 1 4) sourceC801) = raw13230 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13230; decide +kernel
    rw [ha]
    exact (canonical13230 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA801 + difference 4 2) (sourceB801 + difference 2 4) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA801 + difference 4 2) (sourceB801 + difference 2 4) sourceC801) = raw13231 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13231; decide +kernel
    rw [ha]
    exact (canonical13231 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA801 + difference 4 3) (sourceB801 + difference 3 4) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5220) := by
    have ha : (tripleCharges (sourceA801 + difference 4 3) (sourceB801 + difference 3 4) sourceC801) = raw13232 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13232; decide +kernel
    rw [ha]
    exact (canonical13232 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA801 + difference 4 5) (sourceB801 + difference 5 4) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA801 + difference 4 5) (sourceB801 + difference 5 4) sourceC801) = raw13233 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13233; decide +kernel
    rw [ha]
    exact (canonical13233 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA801 + difference 5 0) (sourceB801 + difference 0 5) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4435) := by
    have ha : (tripleCharges (sourceA801 + difference 5 0) (sourceB801 + difference 0 5) sourceC801) = raw13234 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13234; decide +kernel
    rw [ha]
    exact (canonical13234 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA801 + difference 5 1) (sourceB801 + difference 1 5) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA801 + difference 5 1) (sourceB801 + difference 1 5) sourceC801) = raw13235 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13235; decide +kernel
    rw [ha]
    exact (canonical13235 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA801 + difference 5 2) (sourceB801 + difference 2 5) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA801 + difference 5 2) (sourceB801 + difference 2 5) sourceC801) = raw13236 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13236; decide +kernel
    rw [ha]
    exact (canonical13236 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA801 + difference 5 3) (sourceB801 + difference 3 5) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5219) := by
    have ha : (tripleCharges (sourceA801 + difference 5 3) (sourceB801 + difference 3 5) sourceC801) = raw13237 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13237; decide +kernel
    rw [ha]
    exact (canonical13237 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA801 + difference 5 4) (sourceB801 + difference 4 5) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA801 + difference 5 4) (sourceB801 + difference 4 5) sourceC801) = raw13238 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13238; decide +kernel
    rw [ha]
    exact (canonical13238 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA801 sourceB801 sourceC801
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm801, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq804 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm804 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA804 + difference 0 0) (sourceB804 + difference 0 0) sourceC804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA804 + difference 0 0) (sourceB804 + difference 0 0) sourceC804) = raw13299 := by
      apply Matrix.ext; unfold tripleCharges sourceA804 sourceB804 sourceC804 difference raw13299; decide +kernel
    rw [ha]
    exact (canonical13299 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA804 + difference 0 1) (sourceB804 + difference 1 0) sourceC804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA804 + difference 0 1) (sourceB804 + difference 1 0) sourceC804) = raw13300 := by
      apply Matrix.ext; unfold tripleCharges sourceA804 sourceB804 sourceC804 difference raw13300; decide +kernel
    rw [ha]
    exact (canonical13300 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA804 + difference 0 2) (sourceB804 + difference 2 0) sourceC804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA804 + difference 0 2) (sourceB804 + difference 2 0) sourceC804) = raw13301 := by
      apply Matrix.ext; unfold tripleCharges sourceA804 sourceB804 sourceC804 difference raw13301; decide +kernel
    rw [ha]
    exact (canonical13301 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA804 + difference 0 3) (sourceB804 + difference 3 0) sourceC804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA804 + difference 0 3) (sourceB804 + difference 3 0) sourceC804) = raw13302 := by
      apply Matrix.ext; unfold tripleCharges sourceA804 sourceB804 sourceC804 difference raw13302; decide +kernel
    rw [ha]
    exact (canonical13302 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA804 + difference 0 4) (sourceB804 + difference 4 0) sourceC804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4008) := by
    have ha : (tripleCharges (sourceA804 + difference 0 4) (sourceB804 + difference 4 0) sourceC804) = raw13303 := by
      apply Matrix.ext; unfold tripleCharges sourceA804 sourceB804 sourceC804 difference raw13303; decide +kernel
    rw [ha]
    exact (canonical13303 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA804 + difference 0 5) (sourceB804 + difference 5 0) sourceC804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4010) := by
    have ha : (tripleCharges (sourceA804 + difference 0 5) (sourceB804 + difference 5 0) sourceC804) = raw13304 := by
      apply Matrix.ext; unfold tripleCharges sourceA804 sourceB804 sourceC804 difference raw13304; decide +kernel
    rw [ha]
    exact (canonical13304 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA804 + sourceB804) sourceC804) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA804 + sourceB804) sourceC804) = raw13305 := by
      apply Matrix.ext; unfold doubleCharges sourceA804 sourceB804 sourceC804 raw13305; decide +kernel
    rw [ha]
    exact (canonical13305 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA804 sourceB804 sourceC804
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm804, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq805 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm805 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA805 + difference 0 0) (sourceB805 + difference 0 0) sourceC805) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA805 + difference 0 0) (sourceB805 + difference 0 0) sourceC805) = raw13299 := by
      apply Matrix.ext; unfold tripleCharges sourceA805 sourceB805 sourceC805 difference raw13299; decide +kernel
    rw [ha]
    exact (canonical13299 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA805 + difference 1 0) (sourceB805 + difference 0 1) sourceC805) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1403) := by
    have ha : (tripleCharges (sourceA805 + difference 1 0) (sourceB805 + difference 0 1) sourceC805) = raw13306 := by
      apply Matrix.ext; unfold tripleCharges sourceA805 sourceB805 sourceC805 difference raw13306; decide +kernel
    rw [ha]
    exact (canonical13306 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA805 + difference 2 0) (sourceB805 + difference 0 2) sourceC805) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1403) := by
    have ha : (tripleCharges (sourceA805 + difference 2 0) (sourceB805 + difference 0 2) sourceC805) = raw13307 := by
      apply Matrix.ext; unfold tripleCharges sourceA805 sourceB805 sourceC805 difference raw13307; decide +kernel
    rw [ha]
    exact (canonical13307 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA805 + difference 3 0) (sourceB805 + difference 0 3) sourceC805) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1383) := by
    have ha : (tripleCharges (sourceA805 + difference 3 0) (sourceB805 + difference 0 3) sourceC805) = raw13308 := by
      apply Matrix.ext; unfold tripleCharges sourceA805 sourceB805 sourceC805 difference raw13308; decide +kernel
    rw [ha]
    exact (canonical13308 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA805 + difference 4 0) (sourceB805 + difference 0 4) sourceC805) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1384) := by
    have ha : (tripleCharges (sourceA805 + difference 4 0) (sourceB805 + difference 0 4) sourceC805) = raw13309 := by
      apply Matrix.ext; unfold tripleCharges sourceA805 sourceB805 sourceC805 difference raw13309; decide +kernel
    rw [ha]
    exact (canonical13309 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA805 + difference 5 0) (sourceB805 + difference 0 5) sourceC805) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1387) := by
    have ha : (tripleCharges (sourceA805 + difference 5 0) (sourceB805 + difference 0 5) sourceC805) = raw13310 := by
      apply Matrix.ext; unfold tripleCharges sourceA805 sourceB805 sourceC805 difference raw13310; decide +kernel
    rw [ha]
    exact (canonical13310 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA805 + sourceB805) sourceC805) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA805 + sourceB805) sourceC805) = raw13305 := by
      apply Matrix.ext; unfold doubleCharges sourceA805 sourceB805 sourceC805 raw13305; decide +kernel
    rw [ha]
    exact (canonical13305 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA805 sourceB805 sourceC805
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm805, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq806 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm806 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA806 + difference 0 1) (sourceB806 + difference 1 0) sourceC806) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA806 + difference 0 1) (sourceB806 + difference 1 0) sourceC806) = raw13300 := by
      apply Matrix.ext; unfold tripleCharges sourceA806 sourceB806 sourceC806 difference raw13300; decide +kernel
    rw [ha]
    exact (canonical13300 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA806 + difference 1 1) (sourceB806 + difference 1 1) sourceC806) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA806 + difference 1 1) (sourceB806 + difference 1 1) sourceC806) = raw13299 := by
      apply Matrix.ext; unfold tripleCharges sourceA806 sourceB806 sourceC806 difference raw13299; decide +kernel
    rw [ha]
    exact (canonical13299 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA806 + difference 2 1) (sourceB806 + difference 1 2) sourceC806) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA806 + difference 2 1) (sourceB806 + difference 1 2) sourceC806) = raw13311 := by
      apply Matrix.ext; unfold tripleCharges sourceA806 sourceB806 sourceC806 difference raw13311; decide +kernel
    rw [ha]
    exact (canonical13311 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA806 + difference 3 1) (sourceB806 + difference 1 3) sourceC806) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA806 + difference 3 1) (sourceB806 + difference 1 3) sourceC806) = raw13312 := by
      apply Matrix.ext; unfold tripleCharges sourceA806 sourceB806 sourceC806 difference raw13312; decide +kernel
    rw [ha]
    exact (canonical13312 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA806 + difference 4 1) (sourceB806 + difference 1 4) sourceC806) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA806 + difference 4 1) (sourceB806 + difference 1 4) sourceC806) = raw13313 := by
      apply Matrix.ext; unfold tripleCharges sourceA806 sourceB806 sourceC806 difference raw13313; decide +kernel
    rw [ha]
    exact (canonical13313 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA806 + difference 5 1) (sourceB806 + difference 1 5) sourceC806) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2928) := by
    have ha : (tripleCharges (sourceA806 + difference 5 1) (sourceB806 + difference 1 5) sourceC806) = raw13314 := by
      apply Matrix.ext; unfold tripleCharges sourceA806 sourceB806 sourceC806 difference raw13314; decide +kernel
    rw [ha]
    exact (canonical13314 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA806 + sourceB806) sourceC806) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA806 + sourceB806) sourceC806) = raw13305 := by
      apply Matrix.ext; unfold doubleCharges sourceA806 sourceB806 sourceC806 raw13305; decide +kernel
    rw [ha]
    exact (canonical13305 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA806 sourceB806 sourceC806
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm806, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm807 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA807 + difference 0 3) (sourceB807 + difference 3 0) sourceC807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA807 + difference 0 3) (sourceB807 + difference 3 0) sourceC807) = raw13302 := by
      apply Matrix.ext; unfold tripleCharges sourceA807 sourceB807 sourceC807 difference raw13302; decide +kernel
    rw [ha]
    exact (canonical13302 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA807 + difference 1 3) (sourceB807 + difference 3 1) sourceC807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA807 + difference 1 3) (sourceB807 + difference 3 1) sourceC807) = raw13315 := by
      apply Matrix.ext; unfold tripleCharges sourceA807 sourceB807 sourceC807 difference raw13315; decide +kernel
    rw [ha]
    exact (canonical13315 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA807 + difference 2 3) (sourceB807 + difference 3 2) sourceC807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA807 + difference 2 3) (sourceB807 + difference 3 2) sourceC807) = raw13316 := by
      apply Matrix.ext; unfold tripleCharges sourceA807 sourceB807 sourceC807 difference raw13316; decide +kernel
    rw [ha]
    exact (canonical13316 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA807 + difference 3 3) (sourceB807 + difference 3 3) sourceC807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA807 + difference 3 3) (sourceB807 + difference 3 3) sourceC807) = raw13299 := by
      apply Matrix.ext; unfold tripleCharges sourceA807 sourceB807 sourceC807 difference raw13299; decide +kernel
    rw [ha]
    exact (canonical13299 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA807 + difference 4 3) (sourceB807 + difference 3 4) sourceC807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3068) := by
    have ha : (tripleCharges (sourceA807 + difference 4 3) (sourceB807 + difference 3 4) sourceC807) = raw13317 := by
      apply Matrix.ext; unfold tripleCharges sourceA807 sourceB807 sourceC807 difference raw13317; decide +kernel
    rw [ha]
    exact (canonical13317 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA807 + difference 5 3) (sourceB807 + difference 3 5) sourceC807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3069) := by
    have ha : (tripleCharges (sourceA807 + difference 5 3) (sourceB807 + difference 3 5) sourceC807) = raw13318 := by
      apply Matrix.ext; unfold tripleCharges sourceA807 sourceB807 sourceC807 difference raw13318; decide +kernel
    rw [ha]
    exact (canonical13318 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA807 + sourceB807) sourceC807) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA807 + sourceB807) sourceC807) = raw13305 := by
      apply Matrix.ext; unfold doubleCharges sourceA807 sourceB807 sourceC807 raw13305; decide +kernel
    rw [ha]
    exact (canonical13305 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA807 sourceB807 sourceC807
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm807, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq811 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm811 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA811 + difference 0 0) (sourceB811 + difference 0 0) sourceC811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA811 + difference 0 0) (sourceB811 + difference 0 0) sourceC811) = raw12520 := by
      apply Matrix.ext; unfold tripleCharges sourceA811 sourceB811 sourceC811 difference raw12520; decide +kernel
    rw [ha]
    exact (canonical12520 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA811 + difference 0 1) (sourceB811 + difference 1 0) sourceC811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA811 + difference 0 1) (sourceB811 + difference 1 0) sourceC811) = raw12515 := by
      apply Matrix.ext; unfold tripleCharges sourceA811 sourceB811 sourceC811 difference raw12515; decide +kernel
    rw [ha]
    exact (canonical12515 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA811 + difference 0 2) (sourceB811 + difference 2 0) sourceC811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA811 + difference 0 2) (sourceB811 + difference 2 0) sourceC811) = raw13364 := by
      apply Matrix.ext; unfold tripleCharges sourceA811 sourceB811 sourceC811 difference raw13364; decide +kernel
    rw [ha]
    exact (canonical13364 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA811 + difference 0 3) (sourceB811 + difference 3 0) sourceC811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA811 + difference 0 3) (sourceB811 + difference 3 0) sourceC811) = raw13365 := by
      apply Matrix.ext; unfold tripleCharges sourceA811 sourceB811 sourceC811 difference raw13365; decide +kernel
    rw [ha]
    exact (canonical13365 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA811 + difference 0 4) (sourceB811 + difference 4 0) sourceC811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3489) := by
    have ha : (tripleCharges (sourceA811 + difference 0 4) (sourceB811 + difference 4 0) sourceC811) = raw13366 := by
      apply Matrix.ext; unfold tripleCharges sourceA811 sourceB811 sourceC811 difference raw13366; decide +kernel
    rw [ha]
    exact (canonical13366 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA811 + difference 0 5) (sourceB811 + difference 5 0) sourceC811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3496) := by
    have ha : (tripleCharges (sourceA811 + difference 0 5) (sourceB811 + difference 5 0) sourceC811) = raw13367 := by
      apply Matrix.ext; unfold tripleCharges sourceA811 sourceB811 sourceC811 difference raw13367; decide +kernel
    rw [ha]
    exact (canonical13367 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA811 + sourceB811) sourceC811) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA811 + sourceB811) sourceC811) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA811 sourceB811 sourceC811 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA811 sourceB811 sourceC811
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm811, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq812 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm812 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA812 + difference 0 0) (sourceB812 + difference 0 0) sourceC812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA812 + difference 0 0) (sourceB812 + difference 0 0) sourceC812) = raw12520 := by
      apply Matrix.ext; unfold tripleCharges sourceA812 sourceB812 sourceC812 difference raw12520; decide +kernel
    rw [ha]
    exact (canonical12520 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA812 + difference 1 0) (sourceB812 + difference 0 1) sourceC812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA812 + difference 1 0) (sourceB812 + difference 0 1) sourceC812) = raw13368 := by
      apply Matrix.ext; unfold tripleCharges sourceA812 sourceB812 sourceC812 difference raw13368; decide +kernel
    rw [ha]
    exact (canonical13368 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA812 + difference 2 0) (sourceB812 + difference 0 2) sourceC812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA812 + difference 2 0) (sourceB812 + difference 0 2) sourceC812) = raw12926 := by
      apply Matrix.ext; unfold tripleCharges sourceA812 sourceB812 sourceC812 difference raw12926; decide +kernel
    rw [ha]
    exact (canonical12926 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA812 + difference 3 0) (sourceB812 + difference 0 3) sourceC812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA812 + difference 3 0) (sourceB812 + difference 0 3) sourceC812) = raw12664 := by
      apply Matrix.ext; unfold tripleCharges sourceA812 sourceB812 sourceC812 difference raw12664; decide +kernel
    rw [ha]
    exact (canonical12664 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA812 + difference 4 0) (sourceB812 + difference 0 4) sourceC812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2105) := by
    have ha : (tripleCharges (sourceA812 + difference 4 0) (sourceB812 + difference 0 4) sourceC812) = raw13369 := by
      apply Matrix.ext; unfold tripleCharges sourceA812 sourceB812 sourceC812 difference raw13369; decide +kernel
    rw [ha]
    exact (canonical13369 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA812 + difference 5 0) (sourceB812 + difference 0 5) sourceC812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2088) := by
    have ha : (tripleCharges (sourceA812 + difference 5 0) (sourceB812 + difference 0 5) sourceC812) = raw12516 := by
      apply Matrix.ext; unfold tripleCharges sourceA812 sourceB812 sourceC812 difference raw12516; decide +kernel
    rw [ha]
    exact (canonical12516 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA812 + sourceB812) sourceC812) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA812 + sourceB812) sourceC812) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA812 sourceB812 sourceC812 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA812 sourceB812 sourceC812
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm812, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq813 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm813 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA813 + difference 0 3) (sourceB813 + difference 3 0) sourceC813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA813 + difference 0 3) (sourceB813 + difference 3 0) sourceC813) = raw13365 := by
      apply Matrix.ext; unfold tripleCharges sourceA813 sourceB813 sourceC813 difference raw13365; decide +kernel
    rw [ha]
    exact (canonical13365 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA813 + difference 1 3) (sourceB813 + difference 3 1) sourceC813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2926) := by
    have ha : (tripleCharges (sourceA813 + difference 1 3) (sourceB813 + difference 3 1) sourceC813) = raw13370 := by
      apply Matrix.ext; unfold tripleCharges sourceA813 sourceB813 sourceC813 difference raw13370; decide +kernel
    rw [ha]
    exact (canonical13370 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA813 + difference 2 3) (sourceB813 + difference 3 2) sourceC813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2926) := by
    have ha : (tripleCharges (sourceA813 + difference 2 3) (sourceB813 + difference 3 2) sourceC813) = raw12927 := by
      apply Matrix.ext; unfold tripleCharges sourceA813 sourceB813 sourceC813 difference raw12927; decide +kernel
    rw [ha]
    exact (canonical12927 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA813 + difference 3 3) (sourceB813 + difference 3 3) sourceC813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA813 + difference 3 3) (sourceB813 + difference 3 3) sourceC813) = raw12520 := by
      apply Matrix.ext; unfold tripleCharges sourceA813 sourceB813 sourceC813 difference raw12520; decide +kernel
    rw [ha]
    exact (canonical12520 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA813 + difference 4 3) (sourceB813 + difference 3 4) sourceC813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3073) := by
    have ha : (tripleCharges (sourceA813 + difference 4 3) (sourceB813 + difference 3 4) sourceC813) = raw13371 := by
      apply Matrix.ext; unfold tripleCharges sourceA813 sourceB813 sourceC813 difference raw13371; decide +kernel
    rw [ha]
    exact (canonical13371 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA813 + difference 5 3) (sourceB813 + difference 3 5) sourceC813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2950) := by
    have ha : (tripleCharges (sourceA813 + difference 5 3) (sourceB813 + difference 3 5) sourceC813) = raw12518 := by
      apply Matrix.ext; unfold tripleCharges sourceA813 sourceB813 sourceC813 difference raw12518; decide +kernel
    rw [ha]
    exact (canonical12518 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA813 + sourceB813) sourceC813) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA813 + sourceB813) sourceC813) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA813 sourceB813 sourceC813 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA813 sourceB813 sourceC813
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm813, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck689 : Integer.Sparse.reindex keyMap MixedData.row689 = numericRow689 := by decide +kernel

theorem numericCheck689 (x : Master → ℝ) : Integer.Sparse.eval numericRow689 x =
    (1 : ℝ) * reducedSource689 x := by
  norm_num [numericRow689, reducedSource689, Integer.Sparse.eval, Sparse.eval, nodeValue2750, nodeValue3880, nodeValue3901, nodeValue3909, nodeValue3910, nodeValue4091]

theorem reindexCheck690 : Integer.Sparse.reindex keyMap MixedData.row690 = numericRow690 := by decide +kernel

theorem numericCheck690 (x : Master → ℝ) : Integer.Sparse.eval numericRow690 x =
    (1 : ℝ) * reducedSource690 x := by
  norm_num [numericRow690, reducedSource690, Integer.Sparse.eval, Sparse.eval, nodeValue1247, nodeValue1248, nodeValue1250, nodeValue1260, nodeValue2750, nodeValue4091]

theorem reindexCheck691 : Integer.Sparse.reindex keyMap MixedData.row691 = numericRow691 := by decide +kernel

theorem numericCheck691 (x : Master → ℝ) : Integer.Sparse.eval numericRow691 x =
    (1 : ℝ) * reducedSource691 x := by
  norm_num [numericRow691, reducedSource691, Integer.Sparse.eval, Sparse.eval, nodeValue1260, nodeValue2631, nodeValue2721, nodeValue2750, nodeValue2764, nodeValue4091]

theorem reindexCheck692 : Integer.Sparse.reindex keyMap MixedData.row692 = numericRow692 := by decide +kernel

theorem numericCheck692 (x : Master → ℝ) : Integer.Sparse.eval numericRow692 x =
    (1 : ℝ) * reducedSource692 x := by
  norm_num [numericRow692, reducedSource692, Integer.Sparse.eval, Sparse.eval, nodeValue2622, nodeValue2623, nodeValue2625, nodeValue2631, nodeValue2750, nodeValue3880, nodeValue4091]

theorem reindexCheck693 : Integer.Sparse.reindex keyMap MixedData.row693 = numericRow693 := by decide +kernel

theorem numericCheck693 (x : Master → ℝ) : Integer.Sparse.eval numericRow693 x =
    (17280 : ℝ) * reducedSource693 x := by
  norm_num [numericRow693, reducedSource693, Integer.Sparse.eval, Sparse.eval, nodeValue4435, nodeValue4436, nodeValue4439, nodeValue4449, nodeValue5144, nodeValue5145, nodeValue5149, nodeValue5160, nodeValue5219, nodeValue5220, nodeValue5226, nodeValue5249, nodeValue5251, nodeValue5255, nodeValue5282, nodeValue5284, nodeValue5289, nodeValue5431, nodeValue5478, nodeValue5481, nodeValue5485]
  ring

theorem reindexCheck696 : Integer.Sparse.reindex keyMap MixedData.row696 = numericRow696 := by decide +kernel

theorem numericCheck696 (x : Master → ℝ) : Integer.Sparse.eval numericRow696 x =
    (1 : ℝ) * reducedSource696 x := by
  norm_num [numericRow696, reducedSource696, Integer.Sparse.eval, Sparse.eval, nodeValue3074, nodeValue3875, nodeValue3974, nodeValue4008, nodeValue4010, nodeValue4091]

theorem reindexCheck697 : Integer.Sparse.reindex keyMap MixedData.row697 = numericRow697 := by decide +kernel

theorem numericCheck697 (x : Master → ℝ) : Integer.Sparse.eval numericRow697 x =
    (1 : ℝ) * reducedSource697 x := by
  norm_num [numericRow697, reducedSource697, Integer.Sparse.eval, Sparse.eval, nodeValue1383, nodeValue1384, nodeValue1387, nodeValue1403, nodeValue3074, nodeValue4091]

theorem reindexCheck698 : Integer.Sparse.reindex keyMap MixedData.row698 = numericRow698 := by decide +kernel

theorem numericCheck698 (x : Master → ℝ) : Integer.Sparse.eval numericRow698 x =
    (1 : ℝ) * reducedSource698 x := by
  norm_num [numericRow698, reducedSource698, Integer.Sparse.eval, Sparse.eval, nodeValue2924, nodeValue2925, nodeValue2928, nodeValue2951, nodeValue3074, nodeValue3974, nodeValue4091]

theorem reindexCheck699 : Integer.Sparse.reindex keyMap MixedData.row699 = numericRow699 := by decide +kernel

theorem numericCheck699 (x : Master → ℝ) : Integer.Sparse.eval numericRow699 x =
    (1 : ℝ) * reducedSource699 x := by
  norm_num [numericRow699, reducedSource699, Integer.Sparse.eval, Sparse.eval, nodeValue3068, nodeValue3069, nodeValue3074, nodeValue3091, nodeValue3875, nodeValue4091]

theorem reindexCheck701 : Integer.Sparse.reindex keyMap MixedData.row701 = numericRow701 := by decide +kernel

theorem numericCheck701 (x : Master → ℝ) : Integer.Sparse.eval numericRow701 x =
    (1 : ℝ) * reducedSource701 x := by
  norm_num [numericRow701, reducedSource701, Integer.Sparse.eval, Sparse.eval, nodeValue2923, nodeValue3489, nodeValue3496, nodeValue3534, nodeValue3571, nodeValue4083]

theorem reindexCheck702 : Integer.Sparse.reindex keyMap MixedData.row702 = numericRow702 := by decide +kernel

theorem numericCheck702 (x : Master → ℝ) : Integer.Sparse.eval numericRow702 x =
    (1 : ℝ) * reducedSource702 x := by
  norm_num [numericRow702, reducedSource702, Integer.Sparse.eval, Sparse.eval, nodeValue2088, nodeValue2089, nodeValue2105, nodeValue2243, nodeValue3571, nodeValue4083]

theorem reindexCheck703 : Integer.Sparse.reindex keyMap MixedData.row703 = numericRow703 := by decide +kernel

theorem numericCheck703 (x : Master → ℝ) : Integer.Sparse.eval numericRow703 x =
    (1 : ℝ) * reducedSource703 x := by
  norm_num [numericRow703, reducedSource703, Integer.Sparse.eval, Sparse.eval, nodeValue2923, nodeValue2926, nodeValue2950, nodeValue3073, nodeValue3571, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero689 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource689 (mixedVector B) = 0 := by
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h3901 : mixedVector B (Sum.inr 3901) = Sparse.eval nodeValue3901 (mixedVector B) := by
    change mixedMoment B node3901 node3901Labels = _
    exact sound3901 B hB hF
  have h3909 : mixedVector B (Sum.inr 3909) = Sparse.eval nodeValue3909 (mixedVector B) := by
    change mixedMoment B node3909 node3909Labels = _
    exact sound3909 B hB hF
  have h3910 : mixedVector B (Sum.inr 3910) = Sparse.eval nodeValue3910 (mixedVector B) := by
    change mixedMoment B node3910 node3910Labels = _
    exact sound3910 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm797, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2750, h3880, h3901, h3909, h3910, h4091, reducedSource689] using sourceEq797 B hB

theorem rowSound689 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row689 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck689, numericCheck689, reducedZero689 B hB hF, mul_zero]

theorem reducedZero690 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource690 (mixedVector B) = 0 := by
  have h1247 : mixedVector B (Sum.inr 1247) = Sparse.eval nodeValue1247 (mixedVector B) := by
    change mixedMoment B node1247 node1247Labels = _
    exact sound1247 B hB hF
  have h1248 : mixedVector B (Sum.inr 1248) = Sparse.eval nodeValue1248 (mixedVector B) := by
    change mixedMoment B node1248 node1248Labels = _
    exact sound1248 B hB hF
  have h1250 : mixedVector B (Sum.inr 1250) = Sparse.eval nodeValue1250 (mixedVector B) := by
    change mixedMoment B node1250 node1250Labels = _
    exact sound1250 B hB hF
  have h1260 : mixedVector B (Sum.inr 1260) = Sparse.eval nodeValue1260 (mixedVector B) := by
    change mixedMoment B node1260 node1260Labels = _
    exact sound1260 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm798, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1247, h1248, h1250, h1260, h2750, h4091, reducedSource690] using sourceEq798 B hB

theorem rowSound690 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row690 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck690, numericCheck690, reducedZero690 B hB hF, mul_zero]

theorem reducedZero691 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource691 (mixedVector B) = 0 := by
  have h1260 : mixedVector B (Sum.inr 1260) = Sparse.eval nodeValue1260 (mixedVector B) := by
    change mixedMoment B node1260 node1260Labels = _
    exact sound1260 B hB hF
  have h2631 : mixedVector B (Sum.inr 2631) = Sparse.eval nodeValue2631 (mixedVector B) := by
    change mixedMoment B node2631 node2631Labels = _
    exact sound2631 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm799, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1260, h2631, h2721, h2750, h2764, h4091, reducedSource691] using sourceEq799 B hB

theorem rowSound691 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row691 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck691, numericCheck691, reducedZero691 B hB hF, mul_zero]

theorem reducedZero692 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource692 (mixedVector B) = 0 := by
  have h2622 : mixedVector B (Sum.inr 2622) = Sparse.eval nodeValue2622 (mixedVector B) := by
    change mixedMoment B node2622 node2622Labels = _
    exact sound2622 B hB hF
  have h2623 : mixedVector B (Sum.inr 2623) = Sparse.eval nodeValue2623 (mixedVector B) := by
    change mixedMoment B node2623 node2623Labels = _
    exact sound2623 B hB hF
  have h2625 : mixedVector B (Sum.inr 2625) = Sparse.eval nodeValue2625 (mixedVector B) := by
    change mixedMoment B node2625 node2625Labels = _
    exact sound2625 B hB hF
  have h2631 : mixedVector B (Sum.inr 2631) = Sparse.eval nodeValue2631 (mixedVector B) := by
    change mixedMoment B node2631 node2631Labels = _
    exact sound2631 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm800, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2622, h2623, h2625, h2631, h2750, h3880, h4091, reducedSource692] using sourceEq800 B hB

theorem rowSound692 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row692 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck692, numericCheck692, reducedZero692 B hB hF, mul_zero]

theorem reducedZero693 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource693 (mixedVector B) = 0 := by
  have h4435 : mixedVector B (Sum.inr 4435) = Sparse.eval nodeValue4435 (mixedVector B) := by
    change mixedMoment B node4435 node4435Labels = _
    exact sound4435 B hB hF
  have h4436 : mixedVector B (Sum.inr 4436) = Sparse.eval nodeValue4436 (mixedVector B) := by
    change mixedMoment B node4436 node4436Labels = _
    exact sound4436 B hB hF
  have h4439 : mixedVector B (Sum.inr 4439) = Sparse.eval nodeValue4439 (mixedVector B) := by
    change mixedMoment B node4439 node4439Labels = _
    exact sound4439 B hB hF
  have h4449 : mixedVector B (Sum.inr 4449) = Sparse.eval nodeValue4449 (mixedVector B) := by
    change mixedMoment B node4449 node4449Labels = _
    exact sound4449 B hB hF
  have h5144 : mixedVector B (Sum.inr 5144) = Sparse.eval nodeValue5144 (mixedVector B) := by
    change mixedMoment B node5144 node5144Labels = _
    exact sound5144 B hB hF
  have h5145 : mixedVector B (Sum.inr 5145) = Sparse.eval nodeValue5145 (mixedVector B) := by
    change mixedMoment B node5145 node5145Labels = _
    exact sound5145 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5160 : mixedVector B (Sum.inr 5160) = Sparse.eval nodeValue5160 (mixedVector B) := by
    change mixedMoment B node5160 node5160Labels = _
    exact sound5160 B hB hF
  have h5219 : mixedVector B (Sum.inr 5219) = Sparse.eval nodeValue5219 (mixedVector B) := by
    change mixedMoment B node5219 node5219Labels = _
    exact sound5219 B hB hF
  have h5220 : mixedVector B (Sum.inr 5220) = Sparse.eval nodeValue5220 (mixedVector B) := by
    change mixedMoment B node5220 node5220Labels = _
    exact sound5220 B hB hF
  have h5226 : mixedVector B (Sum.inr 5226) = Sparse.eval nodeValue5226 (mixedVector B) := by
    change mixedMoment B node5226 node5226Labels = _
    exact sound5226 B hB hF
  have h5249 : mixedVector B (Sum.inr 5249) = Sparse.eval nodeValue5249 (mixedVector B) := by
    change mixedMoment B node5249 node5249Labels = _
    exact sound5249 B hB hF
  have h5251 : mixedVector B (Sum.inr 5251) = Sparse.eval nodeValue5251 (mixedVector B) := by
    change mixedMoment B node5251 node5251Labels = _
    exact sound5251 B hB hF
  have h5255 : mixedVector B (Sum.inr 5255) = Sparse.eval nodeValue5255 (mixedVector B) := by
    change mixedMoment B node5255 node5255Labels = _
    exact sound5255 B hB hF
  have h5282 : mixedVector B (Sum.inr 5282) = Sparse.eval nodeValue5282 (mixedVector B) := by
    change mixedMoment B node5282 node5282Labels = _
    exact sound5282 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5289 : mixedVector B (Sum.inr 5289) = Sparse.eval nodeValue5289 (mixedVector B) := by
    change mixedMoment B node5289 node5289Labels = _
    exact sound5289 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5478 : mixedVector B (Sum.inr 5478) = Sparse.eval nodeValue5478 (mixedVector B) := by
    change mixedMoment B node5478 node5478Labels = _
    exact sound5478 B hB hF
  have h5481 : mixedVector B (Sum.inr 5481) = Sparse.eval nodeValue5481 (mixedVector B) := by
    change mixedMoment B node5481 node5481Labels = _
    exact sound5481 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485_e B hB hF
  simpa only [sourceForm801, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4435, h4436, h4439, h4449, h5144, h5145, h5149, h5160, h5219, h5220, h5226, h5249, h5251, h5255, h5282, h5284, h5289, h5431, h5478, h5481, h5485, reducedSource693] using sourceEq801 B hB

theorem rowSound693 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row693 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck693, numericCheck693, reducedZero693 B hB hF, mul_zero]

theorem reducedZero696 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource696 (mixedVector B) = 0 := by
  have h3074 : mixedVector B (Sum.inr 3074) = Sparse.eval nodeValue3074 (mixedVector B) := by
    change mixedMoment B node3074 node3074Labels = _
    exact sound3074 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  have h3974 : mixedVector B (Sum.inr 3974) = Sparse.eval nodeValue3974 (mixedVector B) := by
    change mixedMoment B node3974 node3974Labels = _
    exact sound3974 B hB hF
  have h4008 : mixedVector B (Sum.inr 4008) = Sparse.eval nodeValue4008 (mixedVector B) := by
    change mixedMoment B node4008 node4008Labels = _
    exact sound4008 B hB hF
  have h4010 : mixedVector B (Sum.inr 4010) = Sparse.eval nodeValue4010 (mixedVector B) := by
    change mixedMoment B node4010 node4010Labels = _
    exact sound4010 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm804, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3074, h3875, h3974, h4008, h4010, h4091, reducedSource696] using sourceEq804 B hB

theorem rowSound696 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row696 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck696, numericCheck696, reducedZero696 B hB hF, mul_zero]

theorem reducedZero697 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource697 (mixedVector B) = 0 := by
  have h1383 : mixedVector B (Sum.inr 1383) = Sparse.eval nodeValue1383 (mixedVector B) := by
    change mixedMoment B node1383 node1383Labels = _
    exact sound1383 B hB hF
  have h1384 : mixedVector B (Sum.inr 1384) = Sparse.eval nodeValue1384 (mixedVector B) := by
    change mixedMoment B node1384 node1384Labels = _
    exact sound1384 B hB hF
  have h1387 : mixedVector B (Sum.inr 1387) = Sparse.eval nodeValue1387 (mixedVector B) := by
    change mixedMoment B node1387 node1387Labels = _
    exact sound1387 B hB hF
  have h1403 : mixedVector B (Sum.inr 1403) = Sparse.eval nodeValue1403 (mixedVector B) := by
    change mixedMoment B node1403 node1403Labels = _
    exact sound1403 B hB hF
  have h3074 : mixedVector B (Sum.inr 3074) = Sparse.eval nodeValue3074 (mixedVector B) := by
    change mixedMoment B node3074 node3074Labels = _
    exact sound3074 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm805, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1383, h1384, h1387, h1403, h3074, h4091, reducedSource697] using sourceEq805 B hB

theorem rowSound697 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row697 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck697, numericCheck697, reducedZero697 B hB hF, mul_zero]

theorem reducedZero698 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource698 (mixedVector B) = 0 := by
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h2925 : mixedVector B (Sum.inr 2925) = Sparse.eval nodeValue2925 (mixedVector B) := by
    change mixedMoment B node2925 node2925Labels = _
    exact sound2925 B hB hF
  have h2928 : mixedVector B (Sum.inr 2928) = Sparse.eval nodeValue2928 (mixedVector B) := by
    change mixedMoment B node2928 node2928Labels = _
    exact sound2928 B hB hF
  have h2951 : mixedVector B (Sum.inr 2951) = Sparse.eval nodeValue2951 (mixedVector B) := by
    change mixedMoment B node2951 node2951Labels = _
    exact sound2951 B hB hF
  have h3074 : mixedVector B (Sum.inr 3074) = Sparse.eval nodeValue3074 (mixedVector B) := by
    change mixedMoment B node3074 node3074Labels = _
    exact sound3074 B hB hF
  have h3974 : mixedVector B (Sum.inr 3974) = Sparse.eval nodeValue3974 (mixedVector B) := by
    change mixedMoment B node3974 node3974Labels = _
    exact sound3974 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm806, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2924, h2925, h2928, h2951, h3074, h3974, h4091, reducedSource698] using sourceEq806 B hB

theorem rowSound698 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row698 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck698, numericCheck698, reducedZero698 B hB hF, mul_zero]

theorem reducedZero699 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource699 (mixedVector B) = 0 := by
  have h3068 : mixedVector B (Sum.inr 3068) = Sparse.eval nodeValue3068 (mixedVector B) := by
    change mixedMoment B node3068 node3068Labels = _
    exact sound3068 B hB hF
  have h3069 : mixedVector B (Sum.inr 3069) = Sparse.eval nodeValue3069 (mixedVector B) := by
    change mixedMoment B node3069 node3069Labels = _
    exact sound3069 B hB hF
  have h3074 : mixedVector B (Sum.inr 3074) = Sparse.eval nodeValue3074 (mixedVector B) := by
    change mixedMoment B node3074 node3074Labels = _
    exact sound3074 B hB hF
  have h3091 : mixedVector B (Sum.inr 3091) = Sparse.eval nodeValue3091 (mixedVector B) := by
    change mixedMoment B node3091 node3091Labels = _
    exact sound3091 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm807, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3068, h3069, h3074, h3091, h3875, h4091, reducedSource699] using sourceEq807 B hB

theorem rowSound699 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row699 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck699, numericCheck699, reducedZero699 B hB hF, mul_zero]

theorem reducedZero701 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource701 (mixedVector B) = 0 := by
  have h2923 : mixedVector B (Sum.inr 2923) = Sparse.eval nodeValue2923 (mixedVector B) := by
    change mixedMoment B node2923 node2923Labels = _
    exact sound2923 B hB hF
  have h3489 : mixedVector B (Sum.inr 3489) = Sparse.eval nodeValue3489 (mixedVector B) := by
    change mixedMoment B node3489 node3489Labels = _
    exact sound3489 B hB hF
  have h3496 : mixedVector B (Sum.inr 3496) = Sparse.eval nodeValue3496 (mixedVector B) := by
    change mixedMoment B node3496 node3496Labels = _
    exact sound3496 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm811, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2923, h3489, h3496, h3534, h3571, h4083, reducedSource701] using sourceEq811 B hB

theorem rowSound701 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row701 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck701, numericCheck701, reducedZero701 B hB hF, mul_zero]

theorem reducedZero702 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource702 (mixedVector B) = 0 := by
  have h2088 : mixedVector B (Sum.inr 2088) = Sparse.eval nodeValue2088 (mixedVector B) := by
    change mixedMoment B node2088 node2088Labels = _
    exact sound2088 B hB hF
  have h2089 : mixedVector B (Sum.inr 2089) = Sparse.eval nodeValue2089 (mixedVector B) := by
    change mixedMoment B node2089 node2089Labels = _
    exact sound2089 B hB hF
  have h2105 : mixedVector B (Sum.inr 2105) = Sparse.eval nodeValue2105 (mixedVector B) := by
    change mixedMoment B node2105 node2105Labels = _
    exact sound2105 B hB hF
  have h2243 : mixedVector B (Sum.inr 2243) = Sparse.eval nodeValue2243 (mixedVector B) := by
    change mixedMoment B node2243 node2243Labels = _
    exact sound2243 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm812, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2088, h2089, h2105, h2243, h3571, h4083, reducedSource702] using sourceEq812 B hB

theorem rowSound702 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row702 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck702, numericCheck702, reducedZero702 B hB hF, mul_zero]

theorem reducedZero703 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource703 (mixedVector B) = 0 := by
  have h2923 : mixedVector B (Sum.inr 2923) = Sparse.eval nodeValue2923 (mixedVector B) := by
    change mixedMoment B node2923 node2923Labels = _
    exact sound2923 B hB hF
  have h2926 : mixedVector B (Sum.inr 2926) = Sparse.eval nodeValue2926 (mixedVector B) := by
    change mixedMoment B node2926 node2926Labels = _
    exact sound2926 B hB hF
  have h2950 : mixedVector B (Sum.inr 2950) = Sparse.eval nodeValue2950 (mixedVector B) := by
    change mixedMoment B node2950 node2950Labels = _
    exact sound2950 B hB hF
  have h3073 : mixedVector B (Sum.inr 3073) = Sparse.eval nodeValue3073 (mixedVector B) := by
    change mixedMoment B node3073 node3073Labels = _
    exact sound3073 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm813, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2923, h2926, h2950, h3073, h3571, h4083, reducedSource703] using sourceEq813 B hB

theorem rowSound703 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row703 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck703, numericCheck703, reducedZero703 B hB hF, mul_zero]

theorem sourceRowsAt688 : MixedData.sourceRows (688 : Fin 2425) =
    MixedData.row688 := by decide +kernel

theorem sourceRowsAt689 : MixedData.sourceRows (689 : Fin 2425) =
    MixedData.row689 := by decide +kernel

theorem sourceRowsAt690 : MixedData.sourceRows (690 : Fin 2425) =
    MixedData.row690 := by decide +kernel

theorem sourceRowsAt691 : MixedData.sourceRows (691 : Fin 2425) =
    MixedData.row691 := by decide +kernel

theorem sourceRowsAt692 : MixedData.sourceRows (692 : Fin 2425) =
    MixedData.row692 := by decide +kernel

theorem sourceRowsAt693 : MixedData.sourceRows (693 : Fin 2425) =
    MixedData.row693 := by decide +kernel

theorem sourceRowsAt694 : MixedData.sourceRows (694 : Fin 2425) =
    MixedData.row694 := by decide +kernel

theorem sourceRowsAt695 : MixedData.sourceRows (695 : Fin 2425) =
    MixedData.row695 := by decide +kernel

theorem sourceRowsAt696 : MixedData.sourceRows (696 : Fin 2425) =
    MixedData.row696 := by decide +kernel

theorem sourceRowsAt697 : MixedData.sourceRows (697 : Fin 2425) =
    MixedData.row697 := by decide +kernel

theorem sourceRowsAt698 : MixedData.sourceRows (698 : Fin 2425) =
    MixedData.row698 := by decide +kernel

theorem sourceRowsAt699 : MixedData.sourceRows (699 : Fin 2425) =
    MixedData.row699 := by decide +kernel

theorem sourceRowsAt700 : MixedData.sourceRows (700 : Fin 2425) =
    MixedData.row700 := by decide +kernel

theorem sourceRowsAt701 : MixedData.sourceRows (701 : Fin 2425) =
    MixedData.row701 := by decide +kernel

theorem sourceRowsAt702 : MixedData.sourceRows (702 : Fin 2425) =
    MixedData.row702 := by decide +kernel

theorem sourceRowsAt703 : MixedData.sourceRows (703 : Fin 2425) =
    MixedData.row703 := by decide +kernel

theorem chunkSound43_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 43) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 688 ∨ k.val = 689 ∨ k.val = 690 ∨ k.val = 691 ∨ k.val = 692 ∨ k.val = 693 ∨ k.val = 694 ∨ k.val = 695 ∨ k.val = 696 ∨ k.val = 697 ∨ k.val = 698 ∨ k.val = 699 ∨ k.val = 700 ∨ k.val = 701 ∨ k.val = 702 ∨ k.val = 703 := by omega
  rcases heq with h688 | h689 | h690 | h691 | h692 | h693 | h694 | h695 | h696 | h697 | h698 | h699 | h700 | h701 | h702 | h703
  · have he : k = (688 : Fin 2425) := Fin.ext h688
    subst k
    rw [sourceRowsAt688]
    exact rowSound688_e B hB hF
  · have he : k = (689 : Fin 2425) := Fin.ext h689
    subst k
    rw [sourceRowsAt689]
    exact rowSound689 B hB hF
  · have he : k = (690 : Fin 2425) := Fin.ext h690
    subst k
    rw [sourceRowsAt690]
    exact rowSound690 B hB hF
  · have he : k = (691 : Fin 2425) := Fin.ext h691
    subst k
    rw [sourceRowsAt691]
    exact rowSound691 B hB hF
  · have he : k = (692 : Fin 2425) := Fin.ext h692
    subst k
    rw [sourceRowsAt692]
    exact rowSound692 B hB hF
  · have he : k = (693 : Fin 2425) := Fin.ext h693
    subst k
    rw [sourceRowsAt693]
    exact rowSound693 B hB hF
  · have he : k = (694 : Fin 2425) := Fin.ext h694
    subst k
    rw [sourceRowsAt694]
    exact rowSound694_e B hB hF
  · have he : k = (695 : Fin 2425) := Fin.ext h695
    subst k
    rw [sourceRowsAt695]
    exact rowSound695_e B hB hF
  · have he : k = (696 : Fin 2425) := Fin.ext h696
    subst k
    rw [sourceRowsAt696]
    exact rowSound696 B hB hF
  · have he : k = (697 : Fin 2425) := Fin.ext h697
    subst k
    rw [sourceRowsAt697]
    exact rowSound697 B hB hF
  · have he : k = (698 : Fin 2425) := Fin.ext h698
    subst k
    rw [sourceRowsAt698]
    exact rowSound698 B hB hF
  · have he : k = (699 : Fin 2425) := Fin.ext h699
    subst k
    rw [sourceRowsAt699]
    exact rowSound699 B hB hF
  · have he : k = (700 : Fin 2425) := Fin.ext h700
    subst k
    rw [sourceRowsAt700]
    exact rowSound700_e B hB hF
  · have he : k = (701 : Fin 2425) := Fin.ext h701
    subst k
    rw [sourceRowsAt701]
    exact rowSound701 B hB hF
  · have he : k = (702 : Fin 2425) := Fin.ext h702
    subst k
    rw [sourceRowsAt702]
    exact rowSound702 B hB hF
  · have he : k = (703 : Fin 2425) := Fin.ext h703
    subst k
    rw [sourceRowsAt703]
    exact rowSound703 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound43_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound43_e_oai
