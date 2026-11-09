-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound63_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:27:37.558241+00:00
-- url     : https://prove2.me/submissions/3cc46637-c384-49b7-8e24-b3071b8324e3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1008_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1010_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1013_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1020_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1021_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1280 raw1280Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw1280 raw1280Labels = mixedMoment B raw1280step0 raw1280step0Labels := by
      have ha : raw1280step0 = (fun i j => raw1280 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1280step0 raw1280; decide +kernel
      have hl : raw1280step0Labels = raw1280Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1280 raw1280Labels permutation2 permutation6
    mixedMoment B raw1280step0 raw1280step0Labels = mixedMoment B raw1280step1 raw1280step1Labels := by
      have ha : raw1280step1 = -raw1280step0 := by apply Matrix.ext; change ∀ i j, raw1280step1 i j = -(raw1280step0 i j); unfold raw1280step1 raw1280step0; decide +kernel
      have hl : raw1280step1Labels = raw1280step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1280step1 raw1280step1Labels = mixedMoment B raw1280step2 raw1280step2Labels := by
      have ha : raw1280step2 = raw1280step1 := by apply Matrix.ext; unfold raw1280step2 raw1280step1; decide +kernel
      have hl : raw1280step1Labels = labelEmbedding1 ∘ raw1280step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1280step1 raw1280step1Labels raw1280step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1752 node1752Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1428 raw1428Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw1428 raw1428Labels = mixedMoment B raw1428step0 raw1428step0Labels := by
      have ha : raw1428step0 = (fun i j => raw1428 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1428step0 raw1428; decide +kernel
      have hl : raw1428step0Labels = raw1428Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1428 raw1428Labels permutation8 permutation4
    mixedMoment B raw1428step0 raw1428step0Labels = mixedMoment B raw1428step1 raw1428step1Labels := by
      have ha : raw1428step1 = raw1428step0 := by apply Matrix.ext; unfold raw1428step1 raw1428step0; decide +kernel
      have hl : raw1428step0Labels = labelEmbedding7 ∘ raw1428step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1428step0 raw1428step0Labels raw1428step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical1429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1429 raw1429Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw1429 raw1429Labels = mixedMoment B raw1429step0 raw1429step0Labels := by
      have ha : raw1429step0 = (fun i j => raw1429 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1429step0 raw1429; decide +kernel
      have hl : raw1429step0Labels = raw1429Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1429 raw1429Labels permutation8 permutation4
    _ = mixedMoment B node1239 node1239Labels := by rfl

theorem canonical1430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1430 raw1430Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw1430 raw1430Labels = mixedMoment B raw1430step0 raw1430step0Labels := by
      have ha : raw1430step0 = (fun i j => raw1430 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1430step0 raw1430; decide +kernel
      have hl : raw1430step0Labels = raw1430Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1430 raw1430Labels permutation31 permutation6
    mixedMoment B raw1430step0 raw1430step0Labels = mixedMoment B raw1430step1 raw1430step1Labels := by
      have ha : raw1430step1 = raw1430step0 := by apply Matrix.ext; unfold raw1430step1 raw1430step0; decide +kernel
      have hl : raw1430step0Labels = labelEmbedding1 ∘ raw1430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1430step0 raw1430step0Labels raw1430step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical1446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1446 raw1446Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw1446 raw1446Labels = mixedMoment B raw1446step0 raw1446step0Labels := by
      have ha : raw1446step0 = (fun i j => raw1446 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1446step0 raw1446; decide +kernel
      have hl : raw1446step0Labels = raw1446Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1446 raw1446Labels permutation2 permutation4
    mixedMoment B raw1446step0 raw1446step0Labels = mixedMoment B raw1446step1 raw1446step1Labels := by
      have ha : raw1446step1 = raw1446step0 := by apply Matrix.ext; unfold raw1446step1 raw1446step0; decide +kernel
      have hl : raw1446step0Labels = labelEmbedding7 ∘ raw1446step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1446step0 raw1446step0Labels raw1446step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4621 node4621Labels := by rfl

theorem canonical1447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1447 raw1447Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw1447 raw1447Labels = mixedMoment B raw1447step0 raw1447step0Labels := by
      have ha : raw1447step0 = (fun i j => raw1447 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1447step0 raw1447; decide +kernel
      have hl : raw1447step0Labels = raw1447Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1447 raw1447Labels permutation2 permutation4
    _ = mixedMoment B node1297 node1297Labels := by rfl

theorem canonical1448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1448 raw1448Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw1448 raw1448Labels = mixedMoment B raw1448step0 raw1448step0Labels := by
      have ha : raw1448step0 = (fun i j => raw1448 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1448step0 raw1448; decide +kernel
      have hl : raw1448step0Labels = raw1448Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1448 raw1448Labels permutation7 permutation6
    mixedMoment B raw1448step0 raw1448step0Labels = mixedMoment B raw1448step1 raw1448step1Labels := by
      have ha : raw1448step1 = raw1448step0 := by apply Matrix.ext; unfold raw1448step1 raw1448step0; decide +kernel
      have hl : raw1448step0Labels = labelEmbedding1 ∘ raw1448step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1448step0 raw1448step0Labels raw1448step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2289 node2289Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19420 raw19420Labels = mixedMoment B node4072 node4072Labels := by
  calc
    mixedMoment B raw19420 raw19420Labels = mixedMoment B raw19420step0 raw19420step0Labels := by
      have hz : ∀ j, raw19420 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19420step0 = (fun i j => raw19420 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19420step0 raw19420; decide +kernel
      have hl : raw19420step0Labels = raw19420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19420 raw19420Labels permutation520 hz
    mixedMoment B raw19420step0 raw19420step0Labels = mixedMoment B raw19420step1 raw19420step1Labels := by
      have hz : ∀ j, raw19420step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19420step1 = (fun i j => raw19420step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19420step1 raw19420step0; decide +kernel
      have hl : raw19420step1Labels = raw19420step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19420step0 raw19420step0Labels permutation104 hz
    mixedMoment B raw19420step1 raw19420step1Labels = mixedMoment B raw19420step2 raw19420step2Labels := by
      have hz : ∀ j, raw19420step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19420step2 = (fun i j => raw19420step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19420step2 raw19420step1; decide +kernel
      have hl : raw19420step2Labels = raw19420step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19420step1 raw19420step1Labels permutation20 hz
    mixedMoment B raw19420step2 raw19420step2Labels = mixedMoment B raw19420step3 raw19420step3Labels := by
      have hz : ∀ j, raw19420step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19420step3 = (fun i j => raw19420step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19420step3 raw19420step2; decide +kernel
      have hl : raw19420step3Labels = raw19420step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19420step2 raw19420step2Labels permutation4 hz
    mixedMoment B raw19420step3 raw19420step3Labels = mixedMoment B raw19420step4 raw19420step4Labels := by
      have ha : raw19420step4 = (fun i j => raw19420step3 (permutation1 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19420step4 raw19420step3; decide +kernel
      have hl : raw19420step4Labels = raw19420step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19420step3 raw19420step3Labels permutation1 permutation0
    _ = mixedMoment B node4072 node4072Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical152
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19477 raw19477Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw19477 raw19477Labels = mixedMoment B raw19477step0 raw19477step0Labels := by
      have hz : ∀ j, raw19477 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19477step0 = (fun i j => raw19477 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19477step0 raw19477; decide +kernel
      have hl : raw19477step0Labels = raw19477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19477 raw19477Labels permutation520 hz
    mixedMoment B raw19477step0 raw19477step0Labels = mixedMoment B raw19477step1 raw19477step1Labels := by
      have hz : ∀ j, raw19477step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19477step1 = (fun i j => raw19477step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19477step1 raw19477step0; decide +kernel
      have hl : raw19477step1Labels = raw19477step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19477step0 raw19477step0Labels permutation104 hz
    mixedMoment B raw19477step1 raw19477step1Labels = mixedMoment B raw19477step2 raw19477step2Labels := by
      have hz : ∀ j, raw19477step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19477step2 = (fun i j => raw19477step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19477step2 raw19477step1; decide +kernel
      have hl : raw19477step2Labels = raw19477step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19477step1 raw19477step1Labels permutation20 hz
    mixedMoment B raw19477step2 raw19477step2Labels = mixedMoment B raw19477step3 raw19477step3Labels := by
      have ha : raw19477step3 = -raw19477step2 := by apply Matrix.ext; change ∀ i j, raw19477step3 i j = -(raw19477step2 i j); unfold raw19477step3 raw19477step2; decide +kernel
      have hl : raw19477step3Labels = raw19477step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1752 node1752Labels := by rfl

theorem canonical19481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19481 raw19481Labels = mixedMoment B node3313 node3313Labels := by
  calc
    mixedMoment B raw19481 raw19481Labels = mixedMoment B raw19481step0 raw19481step0Labels := by
      have hz : ∀ j, raw19481 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19481step0 = (fun i j => raw19481 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19481step0 raw19481; decide +kernel
      have hl : raw19481step0Labels = raw19481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19481 raw19481Labels permutation520 hz
    mixedMoment B raw19481step0 raw19481step0Labels = mixedMoment B raw19481step1 raw19481step1Labels := by
      have hz : ∀ j, raw19481step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19481step1 = (fun i j => raw19481step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19481step1 raw19481step0; decide +kernel
      have hl : raw19481step1Labels = raw19481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19481step0 raw19481step0Labels permutation104 hz
    mixedMoment B raw19481step1 raw19481step1Labels = mixedMoment B raw19481step2 raw19481step2Labels := by
      have hz : ∀ j, raw19481step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19481step2 = (fun i j => raw19481step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19481step2 raw19481step1; decide +kernel
      have hl : raw19481step2Labels = raw19481step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19481step1 raw19481step1Labels permutation20 hz
    mixedMoment B raw19481step2 raw19481step2Labels = mixedMoment B raw19481step3 raw19481step3Labels := by
      have hz : ∀ j, raw19481step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19481step3 = (fun i j => raw19481step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19481step3 raw19481step2; decide +kernel
      have hl : raw19481step3Labels = raw19481step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19481step2 raw19481step2Labels permutation4 hz
    mixedMoment B raw19481step3 raw19481step3Labels = mixedMoment B raw19481step4 raw19481step4Labels := by
      have ha : raw19481step4 = (fun i j => raw19481step3 (permutation1 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19481step4 raw19481step3; decide +kernel
      have hl : raw19481step4Labels = raw19481step3Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19481step3 raw19481step3Labels permutation1 permutation2
    _ = mixedMoment B node3313 node3313Labels := by rfl

theorem canonical19555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19555 raw19555Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19555 raw19555Labels = mixedMoment B raw19555step0 raw19555step0Labels := by
      have hz : ∀ j, raw19555 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19555step0 = (fun i j => raw19555 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19555step0 raw19555; decide +kernel
      have hl : raw19555step0Labels = raw19555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19555 raw19555Labels permutation520 hz
    mixedMoment B raw19555step0 raw19555step0Labels = mixedMoment B raw19555step1 raw19555step1Labels := by
      have hz : ∀ j, raw19555step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19555step1 = (fun i j => raw19555step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19555step1 raw19555step0; decide +kernel
      have hl : raw19555step1Labels = raw19555step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19555step0 raw19555step0Labels permutation104 hz
    mixedMoment B raw19555step1 raw19555step1Labels = mixedMoment B raw19555step2 raw19555step2Labels := by
      have hz : ∀ j, raw19555step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19555step2 = (fun i j => raw19555step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19555step2 raw19555step1; decide +kernel
      have hl : raw19555step2Labels = raw19555step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19555step1 raw19555step1Labels permutation20 hz
    mixedMoment B raw19555step2 raw19555step2Labels = mixedMoment B raw19555step3 raw19555step3Labels := by
      have ha : raw19555step3 = (fun i j => raw19555step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19555step3 raw19555step2; decide +kernel
      have hl : raw19555step3Labels = raw19555step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19555step2 raw19555step2Labels permutation2 permutation7
    mixedMoment B raw19555step3 raw19555step3Labels = mixedMoment B raw19555step4 raw19555step4Labels := by
      have ha : raw19555step4 = raw19555step3 := by apply Matrix.ext; unfold raw19555step4 raw19555step3; decide +kernel
      have hl : raw19555step3Labels = labelEmbedding10 ∘ raw19555step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19555step3 raw19555step3Labels raw19555step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical19556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19556 raw19556Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19556 raw19556Labels = mixedMoment B raw19556step0 raw19556step0Labels := by
      have hz : ∀ j, raw19556 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19556step0 = (fun i j => raw19556 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19556step0 raw19556; decide +kernel
      have hl : raw19556step0Labels = raw19556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19556 raw19556Labels permutation520 hz
    mixedMoment B raw19556step0 raw19556step0Labels = mixedMoment B raw19556step1 raw19556step1Labels := by
      have hz : ∀ j, raw19556step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19556step1 = (fun i j => raw19556step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19556step1 raw19556step0; decide +kernel
      have hl : raw19556step1Labels = raw19556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19556step0 raw19556step0Labels permutation104 hz
    mixedMoment B raw19556step1 raw19556step1Labels = mixedMoment B raw19556step2 raw19556step2Labels := by
      have hz : ∀ j, raw19556step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19556step2 = (fun i j => raw19556step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19556step2 raw19556step1; decide +kernel
      have hl : raw19556step2Labels = raw19556step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19556step1 raw19556step1Labels permutation14 hz
    mixedMoment B raw19556step2 raw19556step2Labels = mixedMoment B raw19556step3 raw19556step3Labels := by
      have ha : raw19556step3 = (fun i j => raw19556step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19556step3 raw19556step2; decide +kernel
      have hl : raw19556step3Labels = raw19556step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19556step2 raw19556step2Labels permutation2 permutation7
    mixedMoment B raw19556step3 raw19556step3Labels = mixedMoment B raw19556step4 raw19556step4Labels := by
      have ha : raw19556step4 = raw19556step3 := by apply Matrix.ext; unfold raw19556step4 raw19556step3; decide +kernel
      have hl : raw19556step3Labels = labelEmbedding10 ∘ raw19556step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19556step3 raw19556step3Labels raw19556step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical19557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19557 raw19557Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19557 raw19557Labels = mixedMoment B raw19557step0 raw19557step0Labels := by
      have hz : ∀ j, raw19557 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19557step0 = (fun i j => raw19557 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19557step0 raw19557; decide +kernel
      have hl : raw19557step0Labels = raw19557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19557 raw19557Labels permutation520 hz
    mixedMoment B raw19557step0 raw19557step0Labels = mixedMoment B raw19557step1 raw19557step1Labels := by
      have hz : ∀ j, raw19557step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19557step1 = (fun i j => raw19557step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19557step1 raw19557step0; decide +kernel
      have hl : raw19557step1Labels = raw19557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19557step0 raw19557step0Labels permutation80 hz
    mixedMoment B raw19557step1 raw19557step1Labels = mixedMoment B raw19557step2 raw19557step2Labels := by
      have hz : ∀ j, raw19557step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19557step2 = (fun i j => raw19557step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19557step2 raw19557step1; decide +kernel
      have hl : raw19557step2Labels = raw19557step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19557step1 raw19557step1Labels permutation14 hz
    mixedMoment B raw19557step2 raw19557step2Labels = mixedMoment B raw19557step3 raw19557step3Labels := by
      have ha : raw19557step3 = (fun i j => raw19557step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19557step3 raw19557step2; decide +kernel
      have hl : raw19557step3Labels = raw19557step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19557step2 raw19557step2Labels permutation2 permutation7
    mixedMoment B raw19557step3 raw19557step3Labels = mixedMoment B raw19557step4 raw19557step4Labels := by
      have ha : raw19557step4 = raw19557step3 := by apply Matrix.ext; unfold raw19557step4 raw19557step3; decide +kernel
      have hl : raw19557step3Labels = labelEmbedding10 ∘ raw19557step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19557step3 raw19557step3Labels raw19557step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical19558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19558 raw19558Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19558 raw19558Labels = mixedMoment B raw19558step0 raw19558step0Labels := by
      have hz : ∀ j, raw19558 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19558step0 = (fun i j => raw19558 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19558step0 raw19558; decide +kernel
      have hl : raw19558step0Labels = raw19558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19558 raw19558Labels permutation434 hz
    mixedMoment B raw19558step0 raw19558step0Labels = mixedMoment B raw19558step1 raw19558step1Labels := by
      have hz : ∀ j, raw19558step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19558step1 = (fun i j => raw19558step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19558step1 raw19558step0; decide +kernel
      have hl : raw19558step1Labels = raw19558step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19558step0 raw19558step0Labels permutation80 hz
    mixedMoment B raw19558step1 raw19558step1Labels = mixedMoment B raw19558step2 raw19558step2Labels := by
      have hz : ∀ j, raw19558step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19558step2 = (fun i j => raw19558step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19558step2 raw19558step1; decide +kernel
      have hl : raw19558step2Labels = raw19558step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19558step1 raw19558step1Labels permutation14 hz
    mixedMoment B raw19558step2 raw19558step2Labels = mixedMoment B raw19558step3 raw19558step3Labels := by
      have ha : raw19558step3 = (fun i j => raw19558step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19558step3 raw19558step2; decide +kernel
      have hl : raw19558step3Labels = raw19558step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19558step2 raw19558step2Labels permutation2 permutation7
    mixedMoment B raw19558step3 raw19558step3Labels = mixedMoment B raw19558step4 raw19558step4Labels := by
      have ha : raw19558step4 = raw19558step3 := by apply Matrix.ext; unfold raw19558step4 raw19558step3; decide +kernel
      have hl : raw19558step3Labels = labelEmbedding10 ∘ raw19558step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19558step3 raw19558step3Labels raw19558step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical19559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19559 raw19559Labels = mixedMoment B node4512 node4512Labels := by
  calc
    mixedMoment B raw19559 raw19559Labels = mixedMoment B raw19559step0 raw19559step0Labels := by
      have hz : ∀ j, raw19559 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19559step0 = (fun i j => raw19559 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19559step0 raw19559; decide +kernel
      have hl : raw19559step0Labels = raw19559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19559 raw19559Labels permutation520 hz
    mixedMoment B raw19559step0 raw19559step0Labels = mixedMoment B raw19559step1 raw19559step1Labels := by
      have hz : ∀ j, raw19559step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19559step1 = (fun i j => raw19559step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19559step1 raw19559step0; decide +kernel
      have hl : raw19559step1Labels = raw19559step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19559step0 raw19559step0Labels permutation104 hz
    mixedMoment B raw19559step1 raw19559step1Labels = mixedMoment B raw19559step2 raw19559step2Labels := by
      have hz : ∀ j, raw19559step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19559step2 = (fun i j => raw19559step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19559step2 raw19559step1; decide +kernel
      have hl : raw19559step2Labels = raw19559step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19559step1 raw19559step1Labels permutation20 hz
    mixedMoment B raw19559step2 raw19559step2Labels = mixedMoment B raw19559step3 raw19559step3Labels := by
      have hz : ∀ j, raw19559step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19559step3 = (fun i j => raw19559step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19559step3 raw19559step2; decide +kernel
      have hl : raw19559step3Labels = raw19559step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19559step2 raw19559step2Labels permutation4 hz
    mixedMoment B raw19559step3 raw19559step3Labels = mixedMoment B raw19559step4 raw19559step4Labels := by
      have ha : raw19559step4 = (fun i j => raw19559step3 (permutation0 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19559step4 raw19559step3; decide +kernel
      have hl : raw19559step4Labels = raw19559step3Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19559step3 raw19559step3Labels permutation0 permutation7
    mixedMoment B raw19559step4 raw19559step4Labels = mixedMoment B raw19559step5 raw19559step5Labels := by
      have ha : raw19559step5 = raw19559step4 := by apply Matrix.ext; unfold raw19559step5 raw19559step4; decide +kernel
      have hl : raw19559step4Labels = labelEmbedding10 ∘ raw19559step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19559step4 raw19559step4Labels raw19559step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4512 node4512Labels := by rfl

theorem canonical19560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19560 raw19560Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19560 raw19560Labels = mixedMoment B raw19560step0 raw19560step0Labels := by
      have hz : ∀ j, raw19560 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19560step0 = (fun i j => raw19560 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19560step0 raw19560; decide +kernel
      have hl : raw19560step0Labels = raw19560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19560 raw19560Labels permutation520 hz
    mixedMoment B raw19560step0 raw19560step0Labels = mixedMoment B raw19560step1 raw19560step1Labels := by
      have hz : ∀ j, raw19560step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19560step1 = (fun i j => raw19560step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19560step1 raw19560step0; decide +kernel
      have hl : raw19560step1Labels = raw19560step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19560step0 raw19560step0Labels permutation104 hz
    mixedMoment B raw19560step1 raw19560step1Labels = mixedMoment B raw19560step2 raw19560step2Labels := by
      have hz : ∀ j, raw19560step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19560step2 = (fun i j => raw19560step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19560step2 raw19560step1; decide +kernel
      have hl : raw19560step2Labels = raw19560step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19560step1 raw19560step1Labels permutation20 hz
    mixedMoment B raw19560step2 raw19560step2Labels = mixedMoment B raw19560step3 raw19560step3Labels := by
      have ha : raw19560step3 = (fun i j => raw19560step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19560step3 raw19560step2; decide +kernel
      have hl : raw19560step3Labels = raw19560step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19560step2 raw19560step2Labels permutation2 permutation6
    mixedMoment B raw19560step3 raw19560step3Labels = mixedMoment B raw19560step4 raw19560step4Labels := by
      have ha : raw19560step4 = raw19560step3 := by apply Matrix.ext; unfold raw19560step4 raw19560step3; decide +kernel
      have hl : raw19560step3Labels = labelEmbedding9 ∘ raw19560step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19560step3 raw19560step3Labels raw19560step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical19561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19561 raw19561Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19561 raw19561Labels = mixedMoment B raw19561step0 raw19561step0Labels := by
      have hz : ∀ j, raw19561 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19561step0 = (fun i j => raw19561 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19561step0 raw19561; decide +kernel
      have hl : raw19561step0Labels = raw19561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19561 raw19561Labels permutation520 hz
    mixedMoment B raw19561step0 raw19561step0Labels = mixedMoment B raw19561step1 raw19561step1Labels := by
      have hz : ∀ j, raw19561step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19561step1 = (fun i j => raw19561step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19561step1 raw19561step0; decide +kernel
      have hl : raw19561step1Labels = raw19561step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19561step0 raw19561step0Labels permutation104 hz
    mixedMoment B raw19561step1 raw19561step1Labels = mixedMoment B raw19561step2 raw19561step2Labels := by
      have ha : raw19561step2 = (fun i j => raw19561step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19561step2 raw19561step1; decide +kernel
      have hl : raw19561step2Labels = raw19561step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19561step1 raw19561step1Labels permutation10 permutation6
    mixedMoment B raw19561step2 raw19561step2Labels = mixedMoment B raw19561step3 raw19561step3Labels := by
      have ha : raw19561step3 = raw19561step2 := by apply Matrix.ext; unfold raw19561step3 raw19561step2; decide +kernel
      have hl : raw19561step2Labels = labelEmbedding9 ∘ raw19561step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19561step2 raw19561step2Labels raw19561step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

theorem canonical19562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19562 raw19562Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19562 raw19562Labels = mixedMoment B raw19562step0 raw19562step0Labels := by
      have hz : ∀ j, raw19562 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19562step0 = (fun i j => raw19562 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19562step0 raw19562; decide +kernel
      have hl : raw19562step0Labels = raw19562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19562 raw19562Labels permutation520 hz
    mixedMoment B raw19562step0 raw19562step0Labels = mixedMoment B raw19562step1 raw19562step1Labels := by
      have hz : ∀ j, raw19562step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19562step1 = (fun i j => raw19562step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19562step1 raw19562step0; decide +kernel
      have hl : raw19562step1Labels = raw19562step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19562step0 raw19562step0Labels permutation80 hz
    mixedMoment B raw19562step1 raw19562step1Labels = mixedMoment B raw19562step2 raw19562step2Labels := by
      have ha : raw19562step2 = (fun i j => raw19562step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19562step2 raw19562step1; decide +kernel
      have hl : raw19562step2Labels = raw19562step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19562step1 raw19562step1Labels permutation10 permutation6
    mixedMoment B raw19562step2 raw19562step2Labels = mixedMoment B raw19562step3 raw19562step3Labels := by
      have ha : raw19562step3 = raw19562step2 := by apply Matrix.ext; unfold raw19562step3 raw19562step2; decide +kernel
      have hl : raw19562step2Labels = labelEmbedding9 ∘ raw19562step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19562step2 raw19562step2Labels raw19562step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

theorem canonical19563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19563 raw19563Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19563 raw19563Labels = mixedMoment B raw19563step0 raw19563step0Labels := by
      have hz : ∀ j, raw19563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19563step0 = (fun i j => raw19563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19563step0 raw19563; decide +kernel
      have hl : raw19563step0Labels = raw19563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19563 raw19563Labels permutation434 hz
    mixedMoment B raw19563step0 raw19563step0Labels = mixedMoment B raw19563step1 raw19563step1Labels := by
      have hz : ∀ j, raw19563step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19563step1 = (fun i j => raw19563step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19563step1 raw19563step0; decide +kernel
      have hl : raw19563step1Labels = raw19563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19563step0 raw19563step0Labels permutation80 hz
    mixedMoment B raw19563step1 raw19563step1Labels = mixedMoment B raw19563step2 raw19563step2Labels := by
      have ha : raw19563step2 = (fun i j => raw19563step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19563step2 raw19563step1; decide +kernel
      have hl : raw19563step2Labels = raw19563step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19563step1 raw19563step1Labels permutation10 permutation6
    mixedMoment B raw19563step2 raw19563step2Labels = mixedMoment B raw19563step3 raw19563step3Labels := by
      have ha : raw19563step3 = raw19563step2 := by apply Matrix.ext; unfold raw19563step3 raw19563step2; decide +kernel
      have hl : raw19563step2Labels = labelEmbedding9 ∘ raw19563step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19563step2 raw19563step2Labels raw19563step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

theorem canonical19564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19564 raw19564Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19564 raw19564Labels = mixedMoment B raw19564step0 raw19564step0Labels := by
      have hz : ∀ j, raw19564 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19564step0 = (fun i j => raw19564 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19564step0 raw19564; decide +kernel
      have hl : raw19564step0Labels = raw19564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19564 raw19564Labels permutation520 hz
    mixedMoment B raw19564step0 raw19564step0Labels = mixedMoment B raw19564step1 raw19564step1Labels := by
      have hz : ∀ j, raw19564step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19564step1 = (fun i j => raw19564step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19564step1 raw19564step0; decide +kernel
      have hl : raw19564step1Labels = raw19564step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19564step0 raw19564step0Labels permutation104 hz
    mixedMoment B raw19564step1 raw19564step1Labels = mixedMoment B raw19564step2 raw19564step2Labels := by
      have hz : ∀ j, raw19564step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19564step2 = (fun i j => raw19564step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19564step2 raw19564step1; decide +kernel
      have hl : raw19564step2Labels = raw19564step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19564step1 raw19564step1Labels permutation20 hz
    mixedMoment B raw19564step2 raw19564step2Labels = mixedMoment B raw19564step3 raw19564step3Labels := by
      have ha : raw19564step3 = (fun i j => raw19564step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19564step3 raw19564step2; decide +kernel
      have hl : raw19564step3Labels = raw19564step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19564step2 raw19564step2Labels permutation7 permutation7
    mixedMoment B raw19564step3 raw19564step3Labels = mixedMoment B raw19564step4 raw19564step4Labels := by
      have ha : raw19564step4 = -raw19564step3 := by apply Matrix.ext; change ∀ i j, raw19564step4 i j = -(raw19564step3 i j); unfold raw19564step4 raw19564step3; decide +kernel
      have hl : raw19564step4Labels = raw19564step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19564step4 raw19564step4Labels = mixedMoment B raw19564step5 raw19564step5Labels := by
      have ha : raw19564step5 = raw19564step4 := by apply Matrix.ext; unfold raw19564step5 raw19564step4; decide +kernel
      have hl : raw19564step4Labels = labelEmbedding10 ∘ raw19564step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19564step4 raw19564step4Labels raw19564step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical19565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19565 raw19565Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19565 raw19565Labels = mixedMoment B raw19565step0 raw19565step0Labels := by
      have hz : ∀ j, raw19565 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19565step0 = (fun i j => raw19565 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19565step0 raw19565; decide +kernel
      have hl : raw19565step0Labels = raw19565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19565 raw19565Labels permutation520 hz
    mixedMoment B raw19565step0 raw19565step0Labels = mixedMoment B raw19565step1 raw19565step1Labels := by
      have hz : ∀ j, raw19565step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19565step1 = (fun i j => raw19565step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19565step1 raw19565step0; decide +kernel
      have hl : raw19565step1Labels = raw19565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19565step0 raw19565step0Labels permutation104 hz
    mixedMoment B raw19565step1 raw19565step1Labels = mixedMoment B raw19565step2 raw19565step2Labels := by
      have hz : ∀ j, raw19565step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19565step2 = (fun i j => raw19565step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19565step2 raw19565step1; decide +kernel
      have hl : raw19565step2Labels = raw19565step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19565step1 raw19565step1Labels permutation14 hz
    mixedMoment B raw19565step2 raw19565step2Labels = mixedMoment B raw19565step3 raw19565step3Labels := by
      have ha : raw19565step3 = (fun i j => raw19565step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19565step3 raw19565step2; decide +kernel
      have hl : raw19565step3Labels = raw19565step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19565step2 raw19565step2Labels permutation2 permutation6
    mixedMoment B raw19565step3 raw19565step3Labels = mixedMoment B raw19565step4 raw19565step4Labels := by
      have ha : raw19565step4 = raw19565step3 := by apply Matrix.ext; unfold raw19565step4 raw19565step3; decide +kernel
      have hl : raw19565step3Labels = labelEmbedding9 ∘ raw19565step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19565step3 raw19565step3Labels raw19565step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical19566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19566 raw19566Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19566 raw19566Labels = mixedMoment B raw19566step0 raw19566step0Labels := by
      have hz : ∀ j, raw19566 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19566step0 = (fun i j => raw19566 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19566step0 raw19566; decide +kernel
      have hl : raw19566step0Labels = raw19566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19566 raw19566Labels permutation520 hz
    mixedMoment B raw19566step0 raw19566step0Labels = mixedMoment B raw19566step1 raw19566step1Labels := by
      have hz : ∀ j, raw19566step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19566step1 = (fun i j => raw19566step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19566step1 raw19566step0; decide +kernel
      have hl : raw19566step1Labels = raw19566step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19566step0 raw19566step0Labels permutation104 hz
    mixedMoment B raw19566step1 raw19566step1Labels = mixedMoment B raw19566step2 raw19566step2Labels := by
      have ha : raw19566step2 = (fun i j => raw19566step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19566step2 raw19566step1; decide +kernel
      have hl : raw19566step2Labels = raw19566step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19566step1 raw19566step1Labels permutation8 permutation6
    mixedMoment B raw19566step2 raw19566step2Labels = mixedMoment B raw19566step3 raw19566step3Labels := by
      have ha : raw19566step3 = raw19566step2 := by apply Matrix.ext; unfold raw19566step3 raw19566step2; decide +kernel
      have hl : raw19566step2Labels = labelEmbedding9 ∘ raw19566step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19566step2 raw19566step2Labels raw19566step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

theorem canonical19567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19567 raw19567Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19567 raw19567Labels = mixedMoment B raw19567step0 raw19567step0Labels := by
      have hz : ∀ j, raw19567 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19567step0 = (fun i j => raw19567 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19567step0 raw19567; decide +kernel
      have hl : raw19567step0Labels = raw19567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19567 raw19567Labels permutation520 hz
    mixedMoment B raw19567step0 raw19567step0Labels = mixedMoment B raw19567step1 raw19567step1Labels := by
      have hz : ∀ j, raw19567step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19567step1 = (fun i j => raw19567step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19567step1 raw19567step0; decide +kernel
      have hl : raw19567step1Labels = raw19567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19567step0 raw19567step0Labels permutation56 hz
    mixedMoment B raw19567step1 raw19567step1Labels = mixedMoment B raw19567step2 raw19567step2Labels := by
      have ha : raw19567step2 = (fun i j => raw19567step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19567step2 raw19567step1; decide +kernel
      have hl : raw19567step2Labels = raw19567step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19567step1 raw19567step1Labels permutation10 permutation6
    mixedMoment B raw19567step2 raw19567step2Labels = mixedMoment B raw19567step3 raw19567step3Labels := by
      have ha : raw19567step3 = raw19567step2 := by apply Matrix.ext; unfold raw19567step3 raw19567step2; decide +kernel
      have hl : raw19567step2Labels = labelEmbedding9 ∘ raw19567step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19567step2 raw19567step2Labels raw19567step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

theorem canonical19568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19568 raw19568Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19568 raw19568Labels = mixedMoment B raw19568step0 raw19568step0Labels := by
      have hz : ∀ j, raw19568 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19568step0 = (fun i j => raw19568 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19568step0 raw19568; decide +kernel
      have hl : raw19568step0Labels = raw19568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19568 raw19568Labels permutation434 hz
    mixedMoment B raw19568step0 raw19568step0Labels = mixedMoment B raw19568step1 raw19568step1Labels := by
      have hz : ∀ j, raw19568step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19568step1 = (fun i j => raw19568step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19568step1 raw19568step0; decide +kernel
      have hl : raw19568step1Labels = raw19568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19568step0 raw19568step0Labels permutation56 hz
    mixedMoment B raw19568step1 raw19568step1Labels = mixedMoment B raw19568step2 raw19568step2Labels := by
      have ha : raw19568step2 = (fun i j => raw19568step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19568step2 raw19568step1; decide +kernel
      have hl : raw19568step2Labels = raw19568step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19568step1 raw19568step1Labels permutation10 permutation6
    mixedMoment B raw19568step2 raw19568step2Labels = mixedMoment B raw19568step3 raw19568step3Labels := by
      have ha : raw19568step3 = raw19568step2 := by apply Matrix.ext; unfold raw19568step3 raw19568step2; decide +kernel
      have hl : raw19568step2Labels = labelEmbedding9 ∘ raw19568step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19568step2 raw19568step2Labels raw19568step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

theorem canonical19569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19569 raw19569Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19569 raw19569Labels = mixedMoment B raw19569step0 raw19569step0Labels := by
      have hz : ∀ j, raw19569 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19569step0 = (fun i j => raw19569 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19569step0 raw19569; decide +kernel
      have hl : raw19569step0Labels = raw19569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19569 raw19569Labels permutation520 hz
    mixedMoment B raw19569step0 raw19569step0Labels = mixedMoment B raw19569step1 raw19569step1Labels := by
      have hz : ∀ j, raw19569step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19569step1 = (fun i j => raw19569step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19569step1 raw19569step0; decide +kernel
      have hl : raw19569step1Labels = raw19569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19569step0 raw19569step0Labels permutation104 hz
    mixedMoment B raw19569step1 raw19569step1Labels = mixedMoment B raw19569step2 raw19569step2Labels := by
      have hz : ∀ j, raw19569step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19569step2 = (fun i j => raw19569step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19569step2 raw19569step1; decide +kernel
      have hl : raw19569step2Labels = raw19569step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19569step1 raw19569step1Labels permutation14 hz
    mixedMoment B raw19569step2 raw19569step2Labels = mixedMoment B raw19569step3 raw19569step3Labels := by
      have ha : raw19569step3 = (fun i j => raw19569step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19569step3 raw19569step2; decide +kernel
      have hl : raw19569step3Labels = raw19569step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19569step2 raw19569step2Labels permutation7 permutation7
    mixedMoment B raw19569step3 raw19569step3Labels = mixedMoment B raw19569step4 raw19569step4Labels := by
      have ha : raw19569step4 = -raw19569step3 := by apply Matrix.ext; change ∀ i j, raw19569step4 i j = -(raw19569step3 i j); unfold raw19569step4 raw19569step3; decide +kernel
      have hl : raw19569step4Labels = raw19569step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19569step4 raw19569step4Labels = mixedMoment B raw19569step5 raw19569step5Labels := by
      have ha : raw19569step5 = raw19569step4 := by apply Matrix.ext; unfold raw19569step5 raw19569step4; decide +kernel
      have hl : raw19569step4Labels = labelEmbedding10 ∘ raw19569step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19569step4 raw19569step4Labels raw19569step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical19570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19570 raw19570Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19570 raw19570Labels = mixedMoment B raw19570step0 raw19570step0Labels := by
      have hz : ∀ j, raw19570 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19570step0 = (fun i j => raw19570 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19570step0 raw19570; decide +kernel
      have hl : raw19570step0Labels = raw19570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19570 raw19570Labels permutation520 hz
    mixedMoment B raw19570step0 raw19570step0Labels = mixedMoment B raw19570step1 raw19570step1Labels := by
      have hz : ∀ j, raw19570step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19570step1 = (fun i j => raw19570step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19570step1 raw19570step0; decide +kernel
      have hl : raw19570step1Labels = raw19570step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19570step0 raw19570step0Labels permutation80 hz
    mixedMoment B raw19570step1 raw19570step1Labels = mixedMoment B raw19570step2 raw19570step2Labels := by
      have hz : ∀ j, raw19570step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19570step2 = (fun i j => raw19570step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19570step2 raw19570step1; decide +kernel
      have hl : raw19570step2Labels = raw19570step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19570step1 raw19570step1Labels permutation14 hz
    mixedMoment B raw19570step2 raw19570step2Labels = mixedMoment B raw19570step3 raw19570step3Labels := by
      have ha : raw19570step3 = (fun i j => raw19570step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19570step3 raw19570step2; decide +kernel
      have hl : raw19570step3Labels = raw19570step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19570step2 raw19570step2Labels permutation2 permutation6
    mixedMoment B raw19570step3 raw19570step3Labels = mixedMoment B raw19570step4 raw19570step4Labels := by
      have ha : raw19570step4 = raw19570step3 := by apply Matrix.ext; unfold raw19570step4 raw19570step3; decide +kernel
      have hl : raw19570step3Labels = labelEmbedding9 ∘ raw19570step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19570step3 raw19570step3Labels raw19570step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical19571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19571 raw19571Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19571 raw19571Labels = mixedMoment B raw19571step0 raw19571step0Labels := by
      have hz : ∀ j, raw19571 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19571step0 = (fun i j => raw19571 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19571step0 raw19571; decide +kernel
      have hl : raw19571step0Labels = raw19571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19571 raw19571Labels permutation520 hz
    mixedMoment B raw19571step0 raw19571step0Labels = mixedMoment B raw19571step1 raw19571step1Labels := by
      have hz : ∀ j, raw19571step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19571step1 = (fun i j => raw19571step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19571step1 raw19571step0; decide +kernel
      have hl : raw19571step1Labels = raw19571step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19571step0 raw19571step0Labels permutation80 hz
    mixedMoment B raw19571step1 raw19571step1Labels = mixedMoment B raw19571step2 raw19571step2Labels := by
      have ha : raw19571step2 = (fun i j => raw19571step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19571step2 raw19571step1; decide +kernel
      have hl : raw19571step2Labels = raw19571step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19571step1 raw19571step1Labels permutation8 permutation6
    mixedMoment B raw19571step2 raw19571step2Labels = mixedMoment B raw19571step3 raw19571step3Labels := by
      have ha : raw19571step3 = raw19571step2 := by apply Matrix.ext; unfold raw19571step3 raw19571step2; decide +kernel
      have hl : raw19571step2Labels = labelEmbedding9 ∘ raw19571step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19571step2 raw19571step2Labels raw19571step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

theorem canonical19572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19572 raw19572Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19572 raw19572Labels = mixedMoment B raw19572step0 raw19572step0Labels := by
      have hz : ∀ j, raw19572 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19572step0 = (fun i j => raw19572 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19572step0 raw19572; decide +kernel
      have hl : raw19572step0Labels = raw19572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19572 raw19572Labels permutation520 hz
    mixedMoment B raw19572step0 raw19572step0Labels = mixedMoment B raw19572step1 raw19572step1Labels := by
      have hz : ∀ j, raw19572step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19572step1 = (fun i j => raw19572step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19572step1 raw19572step0; decide +kernel
      have hl : raw19572step1Labels = raw19572step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19572step0 raw19572step0Labels permutation56 hz
    mixedMoment B raw19572step1 raw19572step1Labels = mixedMoment B raw19572step2 raw19572step2Labels := by
      have ha : raw19572step2 = (fun i j => raw19572step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19572step2 raw19572step1; decide +kernel
      have hl : raw19572step2Labels = raw19572step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19572step1 raw19572step1Labels permutation8 permutation6
    mixedMoment B raw19572step2 raw19572step2Labels = mixedMoment B raw19572step3 raw19572step3Labels := by
      have ha : raw19572step3 = raw19572step2 := by apply Matrix.ext; unfold raw19572step3 raw19572step2; decide +kernel
      have hl : raw19572step2Labels = labelEmbedding9 ∘ raw19572step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19572step2 raw19572step2Labels raw19572step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

theorem canonical19573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19573 raw19573Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19573 raw19573Labels = mixedMoment B raw19573step0 raw19573step0Labels := by
      have hz : ∀ j, raw19573 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19573step0 = (fun i j => raw19573 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19573step0 raw19573; decide +kernel
      have hl : raw19573step0Labels = raw19573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19573 raw19573Labels permutation346 hz
    mixedMoment B raw19573step0 raw19573step0Labels = mixedMoment B raw19573step1 raw19573step1Labels := by
      have hz : ∀ j, raw19573step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19573step1 = (fun i j => raw19573step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19573step1 raw19573step0; decide +kernel
      have hl : raw19573step1Labels = raw19573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19573step0 raw19573step0Labels permutation56 hz
    mixedMoment B raw19573step1 raw19573step1Labels = mixedMoment B raw19573step2 raw19573step2Labels := by
      have ha : raw19573step2 = (fun i j => raw19573step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19573step2 raw19573step1; decide +kernel
      have hl : raw19573step2Labels = raw19573step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19573step1 raw19573step1Labels permutation10 permutation6
    mixedMoment B raw19573step2 raw19573step2Labels = mixedMoment B raw19573step3 raw19573step3Labels := by
      have ha : raw19573step3 = raw19573step2 := by apply Matrix.ext; unfold raw19573step3 raw19573step2; decide +kernel
      have hl : raw19573step2Labels = labelEmbedding9 ∘ raw19573step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19573step2 raw19573step2Labels raw19573step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

theorem canonical19574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19574 raw19574Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19574 raw19574Labels = mixedMoment B raw19574step0 raw19574step0Labels := by
      have hz : ∀ j, raw19574 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19574step0 = (fun i j => raw19574 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19574step0 raw19574; decide +kernel
      have hl : raw19574step0Labels = raw19574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19574 raw19574Labels permutation520 hz
    mixedMoment B raw19574step0 raw19574step0Labels = mixedMoment B raw19574step1 raw19574step1Labels := by
      have hz : ∀ j, raw19574step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19574step1 = (fun i j => raw19574step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19574step1 raw19574step0; decide +kernel
      have hl : raw19574step1Labels = raw19574step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19574step0 raw19574step0Labels permutation80 hz
    mixedMoment B raw19574step1 raw19574step1Labels = mixedMoment B raw19574step2 raw19574step2Labels := by
      have hz : ∀ j, raw19574step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19574step2 = (fun i j => raw19574step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19574step2 raw19574step1; decide +kernel
      have hl : raw19574step2Labels = raw19574step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19574step1 raw19574step1Labels permutation14 hz
    mixedMoment B raw19574step2 raw19574step2Labels = mixedMoment B raw19574step3 raw19574step3Labels := by
      have ha : raw19574step3 = (fun i j => raw19574step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19574step3 raw19574step2; decide +kernel
      have hl : raw19574step3Labels = raw19574step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19574step2 raw19574step2Labels permutation7 permutation7
    mixedMoment B raw19574step3 raw19574step3Labels = mixedMoment B raw19574step4 raw19574step4Labels := by
      have ha : raw19574step4 = -raw19574step3 := by apply Matrix.ext; change ∀ i j, raw19574step4 i j = -(raw19574step3 i j); unfold raw19574step4 raw19574step3; decide +kernel
      have hl : raw19574step4Labels = raw19574step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19574step4 raw19574step4Labels = mixedMoment B raw19574step5 raw19574step5Labels := by
      have ha : raw19574step5 = raw19574step4 := by apply Matrix.ext; unfold raw19574step5 raw19574step4; decide +kernel
      have hl : raw19574step4Labels = labelEmbedding10 ∘ raw19574step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19574step4 raw19574step4Labels raw19574step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical19575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19575 raw19575Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19575 raw19575Labels = mixedMoment B raw19575step0 raw19575step0Labels := by
      have hz : ∀ j, raw19575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19575step0 = (fun i j => raw19575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19575step0 raw19575; decide +kernel
      have hl : raw19575step0Labels = raw19575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19575 raw19575Labels permutation434 hz
    mixedMoment B raw19575step0 raw19575step0Labels = mixedMoment B raw19575step1 raw19575step1Labels := by
      have hz : ∀ j, raw19575step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19575step1 = (fun i j => raw19575step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19575step1 raw19575step0; decide +kernel
      have hl : raw19575step1Labels = raw19575step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19575step0 raw19575step0Labels permutation80 hz
    mixedMoment B raw19575step1 raw19575step1Labels = mixedMoment B raw19575step2 raw19575step2Labels := by
      have hz : ∀ j, raw19575step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19575step2 = (fun i j => raw19575step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19575step2 raw19575step1; decide +kernel
      have hl : raw19575step2Labels = raw19575step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19575step1 raw19575step1Labels permutation14 hz
    mixedMoment B raw19575step2 raw19575step2Labels = mixedMoment B raw19575step3 raw19575step3Labels := by
      have ha : raw19575step3 = (fun i j => raw19575step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19575step3 raw19575step2; decide +kernel
      have hl : raw19575step3Labels = raw19575step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19575step2 raw19575step2Labels permutation2 permutation6
    mixedMoment B raw19575step3 raw19575step3Labels = mixedMoment B raw19575step4 raw19575step4Labels := by
      have ha : raw19575step4 = raw19575step3 := by apply Matrix.ext; unfold raw19575step4 raw19575step3; decide +kernel
      have hl : raw19575step3Labels = labelEmbedding9 ∘ raw19575step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19575step3 raw19575step3Labels raw19575step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical19576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19576 raw19576Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19576 raw19576Labels = mixedMoment B raw19576step0 raw19576step0Labels := by
      have hz : ∀ j, raw19576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19576step0 = (fun i j => raw19576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19576step0 raw19576; decide +kernel
      have hl : raw19576step0Labels = raw19576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19576 raw19576Labels permutation434 hz
    mixedMoment B raw19576step0 raw19576step0Labels = mixedMoment B raw19576step1 raw19576step1Labels := by
      have hz : ∀ j, raw19576step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19576step1 = (fun i j => raw19576step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19576step1 raw19576step0; decide +kernel
      have hl : raw19576step1Labels = raw19576step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19576step0 raw19576step0Labels permutation80 hz
    mixedMoment B raw19576step1 raw19576step1Labels = mixedMoment B raw19576step2 raw19576step2Labels := by
      have ha : raw19576step2 = (fun i j => raw19576step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19576step2 raw19576step1; decide +kernel
      have hl : raw19576step2Labels = raw19576step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19576step1 raw19576step1Labels permutation8 permutation6
    mixedMoment B raw19576step2 raw19576step2Labels = mixedMoment B raw19576step3 raw19576step3Labels := by
      have ha : raw19576step3 = raw19576step2 := by apply Matrix.ext; unfold raw19576step3 raw19576step2; decide +kernel
      have hl : raw19576step2Labels = labelEmbedding9 ∘ raw19576step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19576step2 raw19576step2Labels raw19576step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

theorem canonical19577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19577 raw19577Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19577 raw19577Labels = mixedMoment B raw19577step0 raw19577step0Labels := by
      have hz : ∀ j, raw19577 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19577step0 = (fun i j => raw19577 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19577step0 raw19577; decide +kernel
      have hl : raw19577step0Labels = raw19577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19577 raw19577Labels permutation434 hz
    mixedMoment B raw19577step0 raw19577step0Labels = mixedMoment B raw19577step1 raw19577step1Labels := by
      have hz : ∀ j, raw19577step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19577step1 = (fun i j => raw19577step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19577step1 raw19577step0; decide +kernel
      have hl : raw19577step1Labels = raw19577step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19577step0 raw19577step0Labels permutation56 hz
    mixedMoment B raw19577step1 raw19577step1Labels = mixedMoment B raw19577step2 raw19577step2Labels := by
      have ha : raw19577step2 = (fun i j => raw19577step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19577step2 raw19577step1; decide +kernel
      have hl : raw19577step2Labels = raw19577step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19577step1 raw19577step1Labels permutation8 permutation6
    mixedMoment B raw19577step2 raw19577step2Labels = mixedMoment B raw19577step3 raw19577step3Labels := by
      have ha : raw19577step3 = raw19577step2 := by apply Matrix.ext; unfold raw19577step3 raw19577step2; decide +kernel
      have hl : raw19577step2Labels = labelEmbedding9 ∘ raw19577step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19577step2 raw19577step2Labels raw19577step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

theorem canonical19578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19578 raw19578Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19578 raw19578Labels = mixedMoment B raw19578step0 raw19578step0Labels := by
      have hz : ∀ j, raw19578 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19578step0 = (fun i j => raw19578 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19578step0 raw19578; decide +kernel
      have hl : raw19578step0Labels = raw19578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19578 raw19578Labels permutation346 hz
    mixedMoment B raw19578step0 raw19578step0Labels = mixedMoment B raw19578step1 raw19578step1Labels := by
      have hz : ∀ j, raw19578step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19578step1 = (fun i j => raw19578step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19578step1 raw19578step0; decide +kernel
      have hl : raw19578step1Labels = raw19578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19578step0 raw19578step0Labels permutation56 hz
    mixedMoment B raw19578step1 raw19578step1Labels = mixedMoment B raw19578step2 raw19578step2Labels := by
      have ha : raw19578step2 = (fun i j => raw19578step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19578step2 raw19578step1; decide +kernel
      have hl : raw19578step2Labels = raw19578step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19578step1 raw19578step1Labels permutation8 permutation6
    mixedMoment B raw19578step2 raw19578step2Labels = mixedMoment B raw19578step3 raw19578step3Labels := by
      have ha : raw19578step3 = raw19578step2 := by apply Matrix.ext; unfold raw19578step3 raw19578step2; decide +kernel
      have hl : raw19578step2Labels = labelEmbedding9 ∘ raw19578step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19578step2 raw19578step2Labels raw19578step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

theorem canonical19579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19579 raw19579Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19579 raw19579Labels = mixedMoment B raw19579step0 raw19579step0Labels := by
      have hz : ∀ j, raw19579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19579step0 = (fun i j => raw19579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19579step0 raw19579; decide +kernel
      have hl : raw19579step0Labels = raw19579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19579 raw19579Labels permutation434 hz
    mixedMoment B raw19579step0 raw19579step0Labels = mixedMoment B raw19579step1 raw19579step1Labels := by
      have hz : ∀ j, raw19579step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19579step1 = (fun i j => raw19579step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19579step1 raw19579step0; decide +kernel
      have hl : raw19579step1Labels = raw19579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19579step0 raw19579step0Labels permutation80 hz
    mixedMoment B raw19579step1 raw19579step1Labels = mixedMoment B raw19579step2 raw19579step2Labels := by
      have hz : ∀ j, raw19579step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19579step2 = (fun i j => raw19579step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19579step2 raw19579step1; decide +kernel
      have hl : raw19579step2Labels = raw19579step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19579step1 raw19579step1Labels permutation14 hz
    mixedMoment B raw19579step2 raw19579step2Labels = mixedMoment B raw19579step3 raw19579step3Labels := by
      have ha : raw19579step3 = (fun i j => raw19579step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19579step3 raw19579step2; decide +kernel
      have hl : raw19579step3Labels = raw19579step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19579step2 raw19579step2Labels permutation7 permutation7
    mixedMoment B raw19579step3 raw19579step3Labels = mixedMoment B raw19579step4 raw19579step4Labels := by
      have ha : raw19579step4 = -raw19579step3 := by apply Matrix.ext; change ∀ i j, raw19579step4 i j = -(raw19579step3 i j); unfold raw19579step4 raw19579step3; decide +kernel
      have hl : raw19579step4Labels = raw19579step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19579step4 raw19579step4Labels = mixedMoment B raw19579step5 raw19579step5Labels := by
      have ha : raw19579step5 = raw19579step4 := by apply Matrix.ext; unfold raw19579step5 raw19579step4; decide +kernel
      have hl : raw19579step4Labels = labelEmbedding10 ∘ raw19579step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19579step4 raw19579step4Labels raw19579step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical19580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19580 raw19580Labels = mixedMoment B node4512 node4512Labels := by
  calc
    mixedMoment B raw19580 raw19580Labels = mixedMoment B raw19580step0 raw19580step0Labels := by
      have hz : ∀ j, raw19580 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19580step0 = (fun i j => raw19580 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19580step0 raw19580; decide +kernel
      have hl : raw19580step0Labels = raw19580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19580 raw19580Labels permutation520 hz
    mixedMoment B raw19580step0 raw19580step0Labels = mixedMoment B raw19580step1 raw19580step1Labels := by
      have hz : ∀ j, raw19580step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19580step1 = (fun i j => raw19580step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19580step1 raw19580step0; decide +kernel
      have hl : raw19580step1Labels = raw19580step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19580step0 raw19580step0Labels permutation104 hz
    mixedMoment B raw19580step1 raw19580step1Labels = mixedMoment B raw19580step2 raw19580step2Labels := by
      have hz : ∀ j, raw19580step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19580step2 = (fun i j => raw19580step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19580step2 raw19580step1; decide +kernel
      have hl : raw19580step2Labels = raw19580step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19580step1 raw19580step1Labels permutation20 hz
    mixedMoment B raw19580step2 raw19580step2Labels = mixedMoment B raw19580step3 raw19580step3Labels := by
      have hz : ∀ j, raw19580step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19580step3 = (fun i j => raw19580step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19580step3 raw19580step2; decide +kernel
      have hl : raw19580step3Labels = raw19580step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19580step2 raw19580step2Labels permutation4 hz
    mixedMoment B raw19580step3 raw19580step3Labels = mixedMoment B raw19580step4 raw19580step4Labels := by
      have ha : raw19580step4 = (fun i j => raw19580step3 (permutation0 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19580step4 raw19580step3; decide +kernel
      have hl : raw19580step4Labels = raw19580step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19580step3 raw19580step3Labels permutation0 permutation6
    mixedMoment B raw19580step4 raw19580step4Labels = mixedMoment B raw19580step5 raw19580step5Labels := by
      have ha : raw19580step5 = raw19580step4 := by apply Matrix.ext; unfold raw19580step5 raw19580step4; decide +kernel
      have hl : raw19580step4Labels = labelEmbedding9 ∘ raw19580step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19580step4 raw19580step4Labels raw19580step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4512 node4512Labels := by rfl

theorem canonical19581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19581 raw19581Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19581 raw19581Labels = mixedMoment B raw19581step0 raw19581step0Labels := by
      have hz : ∀ j, raw19581 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19581step0 = (fun i j => raw19581 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19581step0 raw19581; decide +kernel
      have hl : raw19581step0Labels = raw19581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19581 raw19581Labels permutation520 hz
    mixedMoment B raw19581step0 raw19581step0Labels = mixedMoment B raw19581step1 raw19581step1Labels := by
      have hz : ∀ j, raw19581step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19581step1 = (fun i j => raw19581step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19581step1 raw19581step0; decide +kernel
      have hl : raw19581step1Labels = raw19581step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19581step0 raw19581step0Labels permutation104 hz
    mixedMoment B raw19581step1 raw19581step1Labels = mixedMoment B raw19581step2 raw19581step2Labels := by
      have hz : ∀ j, raw19581step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19581step2 = (fun i j => raw19581step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19581step2 raw19581step1; decide +kernel
      have hl : raw19581step2Labels = raw19581step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19581step1 raw19581step1Labels permutation20 hz
    mixedMoment B raw19581step2 raw19581step2Labels = mixedMoment B raw19581step3 raw19581step3Labels := by
      have ha : raw19581step3 = (fun i j => raw19581step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19581step3 raw19581step2; decide +kernel
      have hl : raw19581step3Labels = raw19581step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19581step2 raw19581step2Labels permutation7 permutation6
    mixedMoment B raw19581step3 raw19581step3Labels = mixedMoment B raw19581step4 raw19581step4Labels := by
      have ha : raw19581step4 = -raw19581step3 := by apply Matrix.ext; change ∀ i j, raw19581step4 i j = -(raw19581step3 i j); unfold raw19581step4 raw19581step3; decide +kernel
      have hl : raw19581step4Labels = raw19581step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19581step4 raw19581step4Labels = mixedMoment B raw19581step5 raw19581step5Labels := by
      have ha : raw19581step5 = raw19581step4 := by apply Matrix.ext; unfold raw19581step5 raw19581step4; decide +kernel
      have hl : raw19581step4Labels = labelEmbedding9 ∘ raw19581step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19581step4 raw19581step4Labels raw19581step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical19582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19582 raw19582Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19582 raw19582Labels = mixedMoment B raw19582step0 raw19582step0Labels := by
      have hz : ∀ j, raw19582 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19582step0 = (fun i j => raw19582 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19582step0 raw19582; decide +kernel
      have hl : raw19582step0Labels = raw19582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19582 raw19582Labels permutation520 hz
    mixedMoment B raw19582step0 raw19582step0Labels = mixedMoment B raw19582step1 raw19582step1Labels := by
      have hz : ∀ j, raw19582step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19582step1 = (fun i j => raw19582step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19582step1 raw19582step0; decide +kernel
      have hl : raw19582step1Labels = raw19582step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19582step0 raw19582step0Labels permutation104 hz
    mixedMoment B raw19582step1 raw19582step1Labels = mixedMoment B raw19582step2 raw19582step2Labels := by
      have hz : ∀ j, raw19582step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19582step2 = (fun i j => raw19582step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19582step2 raw19582step1; decide +kernel
      have hl : raw19582step2Labels = raw19582step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19582step1 raw19582step1Labels permutation14 hz
    mixedMoment B raw19582step2 raw19582step2Labels = mixedMoment B raw19582step3 raw19582step3Labels := by
      have ha : raw19582step3 = (fun i j => raw19582step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19582step3 raw19582step2; decide +kernel
      have hl : raw19582step3Labels = raw19582step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19582step2 raw19582step2Labels permutation7 permutation6
    mixedMoment B raw19582step3 raw19582step3Labels = mixedMoment B raw19582step4 raw19582step4Labels := by
      have ha : raw19582step4 = -raw19582step3 := by apply Matrix.ext; change ∀ i j, raw19582step4 i j = -(raw19582step3 i j); unfold raw19582step4 raw19582step3; decide +kernel
      have hl : raw19582step4Labels = raw19582step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19582step4 raw19582step4Labels = mixedMoment B raw19582step5 raw19582step5Labels := by
      have ha : raw19582step5 = raw19582step4 := by apply Matrix.ext; unfold raw19582step5 raw19582step4; decide +kernel
      have hl : raw19582step4Labels = labelEmbedding9 ∘ raw19582step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19582step4 raw19582step4Labels raw19582step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical19583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19583 raw19583Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19583 raw19583Labels = mixedMoment B raw19583step0 raw19583step0Labels := by
      have hz : ∀ j, raw19583 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19583step0 = (fun i j => raw19583 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19583step0 raw19583; decide +kernel
      have hl : raw19583step0Labels = raw19583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19583 raw19583Labels permutation520 hz
    mixedMoment B raw19583step0 raw19583step0Labels = mixedMoment B raw19583step1 raw19583step1Labels := by
      have hz : ∀ j, raw19583step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19583step1 = (fun i j => raw19583step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19583step1 raw19583step0; decide +kernel
      have hl : raw19583step1Labels = raw19583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19583step0 raw19583step0Labels permutation80 hz
    mixedMoment B raw19583step1 raw19583step1Labels = mixedMoment B raw19583step2 raw19583step2Labels := by
      have hz : ∀ j, raw19583step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19583step2 = (fun i j => raw19583step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19583step2 raw19583step1; decide +kernel
      have hl : raw19583step2Labels = raw19583step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19583step1 raw19583step1Labels permutation14 hz
    mixedMoment B raw19583step2 raw19583step2Labels = mixedMoment B raw19583step3 raw19583step3Labels := by
      have ha : raw19583step3 = (fun i j => raw19583step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19583step3 raw19583step2; decide +kernel
      have hl : raw19583step3Labels = raw19583step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19583step2 raw19583step2Labels permutation7 permutation6
    mixedMoment B raw19583step3 raw19583step3Labels = mixedMoment B raw19583step4 raw19583step4Labels := by
      have ha : raw19583step4 = -raw19583step3 := by apply Matrix.ext; change ∀ i j, raw19583step4 i j = -(raw19583step3 i j); unfold raw19583step4 raw19583step3; decide +kernel
      have hl : raw19583step4Labels = raw19583step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19583step4 raw19583step4Labels = mixedMoment B raw19583step5 raw19583step5Labels := by
      have ha : raw19583step5 = raw19583step4 := by apply Matrix.ext; unfold raw19583step5 raw19583step4; decide +kernel
      have hl : raw19583step4Labels = labelEmbedding9 ∘ raw19583step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19583step4 raw19583step4Labels raw19583step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

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

theorem canonical19584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19584 raw19584Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19584 raw19584Labels = mixedMoment B raw19584step0 raw19584step0Labels := by
      have hz : ∀ j, raw19584 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19584step0 = (fun i j => raw19584 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19584step0 raw19584; decide +kernel
      have hl : raw19584step0Labels = raw19584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19584 raw19584Labels permutation434 hz
    mixedMoment B raw19584step0 raw19584step0Labels = mixedMoment B raw19584step1 raw19584step1Labels := by
      have hz : ∀ j, raw19584step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19584step1 = (fun i j => raw19584step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19584step1 raw19584step0; decide +kernel
      have hl : raw19584step1Labels = raw19584step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19584step0 raw19584step0Labels permutation80 hz
    mixedMoment B raw19584step1 raw19584step1Labels = mixedMoment B raw19584step2 raw19584step2Labels := by
      have hz : ∀ j, raw19584step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19584step2 = (fun i j => raw19584step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19584step2 raw19584step1; decide +kernel
      have hl : raw19584step2Labels = raw19584step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19584step1 raw19584step1Labels permutation14 hz
    mixedMoment B raw19584step2 raw19584step2Labels = mixedMoment B raw19584step3 raw19584step3Labels := by
      have ha : raw19584step3 = (fun i j => raw19584step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19584step3 raw19584step2; decide +kernel
      have hl : raw19584step3Labels = raw19584step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19584step2 raw19584step2Labels permutation7 permutation6
    mixedMoment B raw19584step3 raw19584step3Labels = mixedMoment B raw19584step4 raw19584step4Labels := by
      have ha : raw19584step4 = -raw19584step3 := by apply Matrix.ext; change ∀ i j, raw19584step4 i j = -(raw19584step3 i j); unfold raw19584step4 raw19584step3; decide +kernel
      have hl : raw19584step4Labels = raw19584step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19584step4 raw19584step4Labels = mixedMoment B raw19584step5 raw19584step5Labels := by
      have ha : raw19584step5 = raw19584step4 := by apply Matrix.ext; unfold raw19584step5 raw19584step4; decide +kernel
      have hl : raw19584step4Labels = labelEmbedding9 ∘ raw19584step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19584step4 raw19584step4Labels raw19584step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical19615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19615 raw19615Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw19615 raw19615Labels = mixedMoment B raw19615step0 raw19615step0Labels := by
      have hz : ∀ j, raw19615 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19615step0 = (fun i j => raw19615 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19615step0 raw19615; decide +kernel
      have hl : raw19615step0Labels = raw19615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19615 raw19615Labels permutation520 hz
    mixedMoment B raw19615step0 raw19615step0Labels = mixedMoment B raw19615step1 raw19615step1Labels := by
      have hz : ∀ j, raw19615step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19615step1 = (fun i j => raw19615step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19615step1 raw19615step0; decide +kernel
      have hl : raw19615step1Labels = raw19615step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19615step0 raw19615step0Labels permutation104 hz
    mixedMoment B raw19615step1 raw19615step1Labels = mixedMoment B raw19615step2 raw19615step2Labels := by
      have hz : ∀ j, raw19615step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19615step2 = (fun i j => raw19615step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19615step2 raw19615step1; decide +kernel
      have hl : raw19615step2Labels = raw19615step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19615step1 raw19615step1Labels permutation14 hz
    mixedMoment B raw19615step2 raw19615step2Labels = mixedMoment B raw19615step3 raw19615step3Labels := by
      have ha : raw19615step3 = -raw19615step2 := by apply Matrix.ext; change ∀ i j, raw19615step3 i j = -(raw19615step2 i j); unfold raw19615step3 raw19615step2; decide +kernel
      have hl : raw19615step3Labels = raw19615step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1752 node1752Labels := by rfl

theorem canonical19616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19616 raw19616Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw19616 raw19616Labels = mixedMoment B raw19616step0 raw19616step0Labels := by
      have hz : ∀ j, raw19616 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19616step0 = (fun i j => raw19616 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19616step0 raw19616; decide +kernel
      have hl : raw19616step0Labels = raw19616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19616 raw19616Labels permutation520 hz
    mixedMoment B raw19616step0 raw19616step0Labels = mixedMoment B raw19616step1 raw19616step1Labels := by
      have hz : ∀ j, raw19616step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19616step1 = (fun i j => raw19616step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19616step1 raw19616step0; decide +kernel
      have hl : raw19616step1Labels = raw19616step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19616step0 raw19616step0Labels permutation80 hz
    mixedMoment B raw19616step1 raw19616step1Labels = mixedMoment B raw19616step2 raw19616step2Labels := by
      have hz : ∀ j, raw19616step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19616step2 = (fun i j => raw19616step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19616step2 raw19616step1; decide +kernel
      have hl : raw19616step2Labels = raw19616step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19616step1 raw19616step1Labels permutation14 hz
    mixedMoment B raw19616step2 raw19616step2Labels = mixedMoment B raw19616step3 raw19616step3Labels := by
      have ha : raw19616step3 = -raw19616step2 := by apply Matrix.ext; change ∀ i j, raw19616step3 i j = -(raw19616step2 i j); unfold raw19616step3 raw19616step2; decide +kernel
      have hl : raw19616step3Labels = raw19616step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1752 node1752Labels := by rfl

theorem canonical19617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19617 raw19617Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw19617 raw19617Labels = mixedMoment B raw19617step0 raw19617step0Labels := by
      have hz : ∀ j, raw19617 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19617step0 = (fun i j => raw19617 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19617step0 raw19617; decide +kernel
      have hl : raw19617step0Labels = raw19617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19617 raw19617Labels permutation434 hz
    mixedMoment B raw19617step0 raw19617step0Labels = mixedMoment B raw19617step1 raw19617step1Labels := by
      have hz : ∀ j, raw19617step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19617step1 = (fun i j => raw19617step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19617step1 raw19617step0; decide +kernel
      have hl : raw19617step1Labels = raw19617step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19617step0 raw19617step0Labels permutation80 hz
    mixedMoment B raw19617step1 raw19617step1Labels = mixedMoment B raw19617step2 raw19617step2Labels := by
      have hz : ∀ j, raw19617step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19617step2 = (fun i j => raw19617step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19617step2 raw19617step1; decide +kernel
      have hl : raw19617step2Labels = raw19617step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19617step1 raw19617step1Labels permutation14 hz
    mixedMoment B raw19617step2 raw19617step2Labels = mixedMoment B raw19617step3 raw19617step3Labels := by
      have ha : raw19617step3 = -raw19617step2 := by apply Matrix.ext; change ∀ i j, raw19617step3 i j = -(raw19617step2 i j); unfold raw19617step3 raw19617step2; decide +kernel
      have hl : raw19617step3Labels = raw19617step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1752 node1752Labels := by rfl

theorem canonical19618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19618 raw19618Labels = mixedMoment B node1758 node1758Labels := by
  calc
    mixedMoment B raw19618 raw19618Labels = mixedMoment B raw19618step0 raw19618step0Labels := by
      have hz : ∀ j, raw19618 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19618step0 = (fun i j => raw19618 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19618step0 raw19618; decide +kernel
      have hl : raw19618step0Labels = raw19618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19618 raw19618Labels permutation520 hz
    mixedMoment B raw19618step0 raw19618step0Labels = mixedMoment B raw19618step1 raw19618step1Labels := by
      have hz : ∀ j, raw19618step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19618step1 = (fun i j => raw19618step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19618step1 raw19618step0; decide +kernel
      have hl : raw19618step1Labels = raw19618step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19618step0 raw19618step0Labels permutation104 hz
    mixedMoment B raw19618step1 raw19618step1Labels = mixedMoment B raw19618step2 raw19618step2Labels := by
      have hz : ∀ j, raw19618step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19618step2 = (fun i j => raw19618step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19618step2 raw19618step1; decide +kernel
      have hl : raw19618step2Labels = raw19618step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19618step1 raw19618step1Labels permutation20 hz
    mixedMoment B raw19618step2 raw19618step2Labels = mixedMoment B raw19618step3 raw19618step3Labels := by
      have hz : ∀ j, raw19618step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19618step3 = (fun i j => raw19618step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19618step3 raw19618step2; decide +kernel
      have hl : raw19618step3Labels = raw19618step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19618step2 raw19618step2Labels permutation4 hz
    mixedMoment B raw19618step3 raw19618step3Labels = mixedMoment B raw19618step4 raw19618step4Labels := by
      have ha : raw19618step4 = (fun i j => raw19618step3 (permutation1 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19618step4 raw19618step3; decide +kernel
      have hl : raw19618step4Labels = raw19618step3Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19618step3 raw19618step3Labels permutation1 permutation2
    _ = mixedMoment B node1758 node1758Labels := by rfl

theorem canonical19619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19619 raw19619Labels = mixedMoment B node4159 node4159Labels := by
  calc
    mixedMoment B raw19619 raw19619Labels = mixedMoment B raw19619step0 raw19619step0Labels := by
      have hz : ∀ j, raw19619 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19619step0 = (fun i j => raw19619 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19619step0 raw19619; decide +kernel
      have hl : raw19619step0Labels = raw19619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19619 raw19619Labels permutation434 hz
    mixedMoment B raw19619step0 raw19619step0Labels = mixedMoment B raw19619step1 raw19619step1Labels := by
      have hz : ∀ j, raw19619step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19619step1 = (fun i j => raw19619step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19619step1 raw19619step0; decide +kernel
      have hl : raw19619step1Labels = raw19619step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19619step0 raw19619step0Labels permutation80 hz
    mixedMoment B raw19619step1 raw19619step1Labels = mixedMoment B raw19619step2 raw19619step2Labels := by
      have ha : raw19619step2 = (fun i j => raw19619step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19619step2 raw19619step1; decide +kernel
      have hl : raw19619step2Labels = raw19619step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19619step1 raw19619step1Labels permutation10 permutation3
    mixedMoment B raw19619step2 raw19619step2Labels = mixedMoment B raw19619step3 raw19619step3Labels := by
      have ha : raw19619step3 = raw19619step2 := by apply Matrix.ext; unfold raw19619step3 raw19619step2; decide +kernel
      have hl : raw19619step2Labels = labelEmbedding6 ∘ raw19619step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19619step2 raw19619step2Labels raw19619step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4159 node4159Labels := by rfl

theorem canonical19620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19620 raw19620Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw19620 raw19620Labels = mixedMoment B raw19620step0 raw19620step0Labels := by
      have hz : ∀ j, raw19620 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19620step0 = (fun i j => raw19620 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19620step0 raw19620; decide +kernel
      have hl : raw19620step0Labels = raw19620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19620 raw19620Labels permutation434 hz
    mixedMoment B raw19620step0 raw19620step0Labels = mixedMoment B raw19620step1 raw19620step1Labels := by
      have ha : raw19620step1 = (fun i j => raw19620step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19620step1 raw19620step0; decide +kernel
      have hl : raw19620step1Labels = raw19620step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19620step0 raw19620step0Labels permutation139 permutation2
    mixedMoment B raw19620step1 raw19620step1Labels = mixedMoment B raw19620step2 raw19620step2Labels := by
      have ha : raw19620step2 = -raw19620step1 := by apply Matrix.ext; change ∀ i j, raw19620step2 i j = -(raw19620step1 i j); unfold raw19620step2 raw19620step1; decide +kernel
      have hl : raw19620step2Labels = raw19620step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4330 node4330Labels := by rfl

theorem canonical19621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19621 raw19621Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw19621 raw19621Labels = mixedMoment B raw19621step0 raw19621step0Labels := by
      have hz : ∀ j, raw19621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19621step0 = (fun i j => raw19621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19621step0 raw19621; decide +kernel
      have hl : raw19621step0Labels = raw19621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19621 raw19621Labels permutation346 hz
    mixedMoment B raw19621step0 raw19621step0Labels = mixedMoment B raw19621step1 raw19621step1Labels := by
      have ha : raw19621step1 = (fun i j => raw19621step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19621step1 raw19621step0; decide +kernel
      have hl : raw19621step1Labels = raw19621step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19621step0 raw19621step0Labels permutation139 permutation2
    mixedMoment B raw19621step1 raw19621step1Labels = mixedMoment B raw19621step2 raw19621step2Labels := by
      have ha : raw19621step2 = -raw19621step1 := by apply Matrix.ext; change ∀ i j, raw19621step2 i j = -(raw19621step1 i j); unfold raw19621step2 raw19621step1; decide +kernel
      have hl : raw19621step2Labels = raw19621step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4330 node4330Labels := by rfl

theorem canonical19622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19622 raw19622Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw19622 raw19622Labels = mixedMoment B raw19622step0 raw19622step0Labels := by
      have hz : ∀ j, raw19622 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19622step0 = (fun i j => raw19622 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19622step0 raw19622; decide +kernel
      have hl : raw19622step0Labels = raw19622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19622 raw19622Labels permutation434 hz
    mixedMoment B raw19622step0 raw19622step0Labels = mixedMoment B raw19622step1 raw19622step1Labels := by
      have hz : ∀ j, raw19622step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19622step1 = (fun i j => raw19622step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19622step1 raw19622step0; decide +kernel
      have hl : raw19622step1Labels = raw19622step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19622step0 raw19622step0Labels permutation80 hz
    mixedMoment B raw19622step1 raw19622step1Labels = mixedMoment B raw19622step2 raw19622step2Labels := by
      have ha : raw19622step2 = (fun i j => raw19622step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19622step2 raw19622step1; decide +kernel
      have hl : raw19622step2Labels = raw19622step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19622step1 raw19622step1Labels permutation29 permutation2
    mixedMoment B raw19622step2 raw19622step2Labels = mixedMoment B raw19622step3 raw19622step3Labels := by
      have ha : raw19622step3 = -raw19622step2 := by apply Matrix.ext; change ∀ i j, raw19622step3 i j = -(raw19622step2 i j); unfold raw19622step3 raw19622step2; decide +kernel
      have hl : raw19622step3Labels = raw19622step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4356 node4356Labels := by rfl

theorem canonical19623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19623 raw19623Labels = mixedMoment B node4159 node4159Labels := by
  calc
    mixedMoment B raw19623 raw19623Labels = mixedMoment B raw19623step0 raw19623step0Labels := by
      have hz : ∀ j, raw19623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19623step0 = (fun i j => raw19623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19623step0 raw19623; decide +kernel
      have hl : raw19623step0Labels = raw19623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19623 raw19623Labels permutation434 hz
    mixedMoment B raw19623step0 raw19623step0Labels = mixedMoment B raw19623step1 raw19623step1Labels := by
      have hz : ∀ j, raw19623step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19623step1 = (fun i j => raw19623step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19623step1 raw19623step0; decide +kernel
      have hl : raw19623step1Labels = raw19623step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19623step0 raw19623step0Labels permutation56 hz
    mixedMoment B raw19623step1 raw19623step1Labels = mixedMoment B raw19623step2 raw19623step2Labels := by
      have ha : raw19623step2 = (fun i j => raw19623step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19623step2 raw19623step1; decide +kernel
      have hl : raw19623step2Labels = raw19623step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19623step1 raw19623step1Labels permutation10 permutation3
    mixedMoment B raw19623step2 raw19623step2Labels = mixedMoment B raw19623step3 raw19623step3Labels := by
      have ha : raw19623step3 = raw19623step2 := by apply Matrix.ext; unfold raw19623step3 raw19623step2; decide +kernel
      have hl : raw19623step2Labels = labelEmbedding6 ∘ raw19623step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19623step2 raw19623step2Labels raw19623step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4159 node4159Labels := by rfl

theorem canonical19624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19624 raw19624Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw19624 raw19624Labels = mixedMoment B raw19624step0 raw19624step0Labels := by
      have hz : ∀ j, raw19624 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19624step0 = (fun i j => raw19624 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19624step0 raw19624; decide +kernel
      have hl : raw19624step0Labels = raw19624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19624 raw19624Labels permutation434 hz
    mixedMoment B raw19624step0 raw19624step0Labels = mixedMoment B raw19624step1 raw19624step1Labels := by
      have ha : raw19624step1 = (fun i j => raw19624step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19624step1 raw19624step0; decide +kernel
      have hl : raw19624step1Labels = raw19624step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19624step0 raw19624step0Labels permutation145 permutation2
    mixedMoment B raw19624step1 raw19624step1Labels = mixedMoment B raw19624step2 raw19624step2Labels := by
      have ha : raw19624step2 = -raw19624step1 := by apply Matrix.ext; change ∀ i j, raw19624step2 i j = -(raw19624step1 i j); unfold raw19624step2 raw19624step1; decide +kernel
      have hl : raw19624step2Labels = raw19624step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4330 node4330Labels := by rfl

theorem canonical19625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19625 raw19625Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw19625 raw19625Labels = mixedMoment B raw19625step0 raw19625step0Labels := by
      have hz : ∀ j, raw19625 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19625step0 = (fun i j => raw19625 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19625step0 raw19625; decide +kernel
      have hl : raw19625step0Labels = raw19625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19625 raw19625Labels permutation265 hz
    mixedMoment B raw19625step0 raw19625step0Labels = mixedMoment B raw19625step1 raw19625step1Labels := by
      have ha : raw19625step1 = (fun i j => raw19625step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19625step1 raw19625step0; decide +kernel
      have hl : raw19625step1Labels = raw19625step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19625step0 raw19625step0Labels permutation139 permutation2
    mixedMoment B raw19625step1 raw19625step1Labels = mixedMoment B raw19625step2 raw19625step2Labels := by
      have ha : raw19625step2 = -raw19625step1 := by apply Matrix.ext; change ∀ i j, raw19625step2 i j = -(raw19625step1 i j); unfold raw19625step2 raw19625step1; decide +kernel
      have hl : raw19625step2Labels = raw19625step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4330 node4330Labels := by rfl

theorem canonical19626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19626 raw19626Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw19626 raw19626Labels = mixedMoment B raw19626step0 raw19626step0Labels := by
      have hz : ∀ j, raw19626 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19626step0 = (fun i j => raw19626 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19626step0 raw19626; decide +kernel
      have hl : raw19626step0Labels = raw19626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19626 raw19626Labels permutation434 hz
    mixedMoment B raw19626step0 raw19626step0Labels = mixedMoment B raw19626step1 raw19626step1Labels := by
      have hz : ∀ j, raw19626step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19626step1 = (fun i j => raw19626step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19626step1 raw19626step0; decide +kernel
      have hl : raw19626step1Labels = raw19626step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19626step0 raw19626step0Labels permutation56 hz
    mixedMoment B raw19626step1 raw19626step1Labels = mixedMoment B raw19626step2 raw19626step2Labels := by
      have ha : raw19626step2 = (fun i j => raw19626step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19626step2 raw19626step1; decide +kernel
      have hl : raw19626step2Labels = raw19626step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19626step1 raw19626step1Labels permutation29 permutation2
    mixedMoment B raw19626step2 raw19626step2Labels = mixedMoment B raw19626step3 raw19626step3Labels := by
      have ha : raw19626step3 = -raw19626step2 := by apply Matrix.ext; change ∀ i j, raw19626step3 i j = -(raw19626step2 i j); unfold raw19626step3 raw19626step2; decide +kernel
      have hl : raw19626step3Labels = raw19626step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4356 node4356Labels := by rfl

theorem canonical19627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19627 raw19627Labels = mixedMoment B node4159 node4159Labels := by
  calc
    mixedMoment B raw19627 raw19627Labels = mixedMoment B raw19627step0 raw19627step0Labels := by
      have hz : ∀ j, raw19627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19627step0 = (fun i j => raw19627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19627step0 raw19627; decide +kernel
      have hl : raw19627step0Labels = raw19627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19627 raw19627Labels permutation346 hz
    mixedMoment B raw19627step0 raw19627step0Labels = mixedMoment B raw19627step1 raw19627step1Labels := by
      have hz : ∀ j, raw19627step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19627step1 = (fun i j => raw19627step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19627step1 raw19627step0; decide +kernel
      have hl : raw19627step1Labels = raw19627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19627step0 raw19627step0Labels permutation56 hz
    mixedMoment B raw19627step1 raw19627step1Labels = mixedMoment B raw19627step2 raw19627step2Labels := by
      have ha : raw19627step2 = (fun i j => raw19627step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19627step2 raw19627step1; decide +kernel
      have hl : raw19627step2Labels = raw19627step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19627step1 raw19627step1Labels permutation10 permutation3
    mixedMoment B raw19627step2 raw19627step2Labels = mixedMoment B raw19627step3 raw19627step3Labels := by
      have ha : raw19627step3 = raw19627step2 := by apply Matrix.ext; unfold raw19627step3 raw19627step2; decide +kernel
      have hl : raw19627step2Labels = labelEmbedding6 ∘ raw19627step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19627step2 raw19627step2Labels raw19627step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4159 node4159Labels := by rfl

theorem canonical19628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19628 raw19628Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw19628 raw19628Labels = mixedMoment B raw19628step0 raw19628step0Labels := by
      have hz : ∀ j, raw19628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19628step0 = (fun i j => raw19628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19628step0 raw19628; decide +kernel
      have hl : raw19628step0Labels = raw19628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19628 raw19628Labels permutation346 hz
    mixedMoment B raw19628step0 raw19628step0Labels = mixedMoment B raw19628step1 raw19628step1Labels := by
      have ha : raw19628step1 = (fun i j => raw19628step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19628step1 raw19628step0; decide +kernel
      have hl : raw19628step1Labels = raw19628step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19628step0 raw19628step0Labels permutation145 permutation2
    mixedMoment B raw19628step1 raw19628step1Labels = mixedMoment B raw19628step2 raw19628step2Labels := by
      have ha : raw19628step2 = -raw19628step1 := by apply Matrix.ext; change ∀ i j, raw19628step2 i j = -(raw19628step1 i j); unfold raw19628step2 raw19628step1; decide +kernel
      have hl : raw19628step2Labels = raw19628step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4330 node4330Labels := by rfl

theorem canonical19629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19629 raw19629Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw19629 raw19629Labels = mixedMoment B raw19629step0 raw19629step0Labels := by
      have hz : ∀ j, raw19629 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19629step0 = (fun i j => raw19629 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19629step0 raw19629; decide +kernel
      have hl : raw19629step0Labels = raw19629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19629 raw19629Labels permutation265 hz
    mixedMoment B raw19629step0 raw19629step0Labels = mixedMoment B raw19629step1 raw19629step1Labels := by
      have ha : raw19629step1 = (fun i j => raw19629step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19629step1 raw19629step0; decide +kernel
      have hl : raw19629step1Labels = raw19629step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19629step0 raw19629step0Labels permutation145 permutation2
    mixedMoment B raw19629step1 raw19629step1Labels = mixedMoment B raw19629step2 raw19629step2Labels := by
      have ha : raw19629step2 = -raw19629step1 := by apply Matrix.ext; change ∀ i j, raw19629step2 i j = -(raw19629step1 i j); unfold raw19629step2 raw19629step1; decide +kernel
      have hl : raw19629step2Labels = raw19629step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4330 node4330Labels := by rfl

theorem canonical19630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19630 raw19630Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw19630 raw19630Labels = mixedMoment B raw19630step0 raw19630step0Labels := by
      have hz : ∀ j, raw19630 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19630step0 = (fun i j => raw19630 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19630step0 raw19630; decide +kernel
      have hl : raw19630step0Labels = raw19630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19630 raw19630Labels permutation346 hz
    mixedMoment B raw19630step0 raw19630step0Labels = mixedMoment B raw19630step1 raw19630step1Labels := by
      have hz : ∀ j, raw19630step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19630step1 = (fun i j => raw19630step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19630step1 raw19630step0; decide +kernel
      have hl : raw19630step1Labels = raw19630step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19630step0 raw19630step0Labels permutation56 hz
    mixedMoment B raw19630step1 raw19630step1Labels = mixedMoment B raw19630step2 raw19630step2Labels := by
      have ha : raw19630step2 = (fun i j => raw19630step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19630step2 raw19630step1; decide +kernel
      have hl : raw19630step2Labels = raw19630step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19630step1 raw19630step1Labels permutation29 permutation2
    mixedMoment B raw19630step2 raw19630step2Labels = mixedMoment B raw19630step3 raw19630step3Labels := by
      have ha : raw19630step3 = -raw19630step2 := by apply Matrix.ext; change ∀ i j, raw19630step3 i j = -(raw19630step2 i j); unfold raw19630step3 raw19630step2; decide +kernel
      have hl : raw19630step3Labels = raw19630step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4356 node4356Labels := by rfl

theorem canonical19631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19631 raw19631Labels = mixedMoment B node4189 node4189Labels := by
  calc
    mixedMoment B raw19631 raw19631Labels = mixedMoment B raw19631step0 raw19631step0Labels := by
      have hz : ∀ j, raw19631 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19631step0 = (fun i j => raw19631 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19631step0 raw19631; decide +kernel
      have hl : raw19631step0Labels = raw19631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19631 raw19631Labels permutation434 hz
    mixedMoment B raw19631step0 raw19631step0Labels = mixedMoment B raw19631step1 raw19631step1Labels := by
      have hz : ∀ j, raw19631step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19631step1 = (fun i j => raw19631step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19631step1 raw19631step0; decide +kernel
      have hl : raw19631step1Labels = raw19631step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19631step0 raw19631step0Labels permutation80 hz
    mixedMoment B raw19631step1 raw19631step1Labels = mixedMoment B raw19631step2 raw19631step2Labels := by
      have hz : ∀ j, raw19631step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19631step2 = (fun i j => raw19631step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19631step2 raw19631step1; decide +kernel
      have hl : raw19631step2Labels = raw19631step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19631step1 raw19631step1Labels permutation14 hz
    mixedMoment B raw19631step2 raw19631step2Labels = mixedMoment B raw19631step3 raw19631step3Labels := by
      have ha : raw19631step3 = (fun i j => raw19631step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19631step3 raw19631step2; decide +kernel
      have hl : raw19631step3Labels = raw19631step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19631step2 raw19631step2Labels permutation2 permutation3
    mixedMoment B raw19631step3 raw19631step3Labels = mixedMoment B raw19631step4 raw19631step4Labels := by
      have ha : raw19631step4 = raw19631step3 := by apply Matrix.ext; unfold raw19631step4 raw19631step3; decide +kernel
      have hl : raw19631step3Labels = labelEmbedding6 ∘ raw19631step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19631step3 raw19631step3Labels raw19631step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4189 node4189Labels := by rfl

theorem canonical19632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19632 raw19632Labels = mixedMoment B node4370 node4370Labels := by
  calc
    mixedMoment B raw19632 raw19632Labels = mixedMoment B raw19632step0 raw19632step0Labels := by
      have hz : ∀ j, raw19632 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19632step0 = (fun i j => raw19632 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19632step0 raw19632; decide +kernel
      have hl : raw19632step0Labels = raw19632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19632 raw19632Labels permutation434 hz
    mixedMoment B raw19632step0 raw19632step0Labels = mixedMoment B raw19632step1 raw19632step1Labels := by
      have hz : ∀ j, raw19632step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19632step1 = (fun i j => raw19632step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19632step1 raw19632step0; decide +kernel
      have hl : raw19632step1Labels = raw19632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19632step0 raw19632step0Labels permutation80 hz
    mixedMoment B raw19632step1 raw19632step1Labels = mixedMoment B raw19632step2 raw19632step2Labels := by
      have ha : raw19632step2 = (fun i j => raw19632step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19632step2 raw19632step1; decide +kernel
      have hl : raw19632step2Labels = raw19632step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19632step1 raw19632step1Labels permutation31 permutation2
    mixedMoment B raw19632step2 raw19632step2Labels = mixedMoment B raw19632step3 raw19632step3Labels := by
      have ha : raw19632step3 = -raw19632step2 := by apply Matrix.ext; change ∀ i j, raw19632step3 i j = -(raw19632step2 i j); unfold raw19632step3 raw19632step2; decide +kernel
      have hl : raw19632step3Labels = raw19632step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4370 node4370Labels := by rfl

theorem canonical19633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19633 raw19633Labels = mixedMoment B node4370 node4370Labels := by
  calc
    mixedMoment B raw19633 raw19633Labels = mixedMoment B raw19633step0 raw19633step0Labels := by
      have hz : ∀ j, raw19633 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19633step0 = (fun i j => raw19633 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19633step0 raw19633; decide +kernel
      have hl : raw19633step0Labels = raw19633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19633 raw19633Labels permutation434 hz
    mixedMoment B raw19633step0 raw19633step0Labels = mixedMoment B raw19633step1 raw19633step1Labels := by
      have hz : ∀ j, raw19633step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19633step1 = (fun i j => raw19633step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19633step1 raw19633step0; decide +kernel
      have hl : raw19633step1Labels = raw19633step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19633step0 raw19633step0Labels permutation56 hz
    mixedMoment B raw19633step1 raw19633step1Labels = mixedMoment B raw19633step2 raw19633step2Labels := by
      have ha : raw19633step2 = (fun i j => raw19633step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19633step2 raw19633step1; decide +kernel
      have hl : raw19633step2Labels = raw19633step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19633step1 raw19633step1Labels permutation31 permutation2
    mixedMoment B raw19633step2 raw19633step2Labels = mixedMoment B raw19633step3 raw19633step3Labels := by
      have ha : raw19633step3 = -raw19633step2 := by apply Matrix.ext; change ∀ i j, raw19633step3 i j = -(raw19633step2 i j); unfold raw19633step3 raw19633step2; decide +kernel
      have hl : raw19633step3Labels = raw19633step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4370 node4370Labels := by rfl

theorem canonical19634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19634 raw19634Labels = mixedMoment B node4370 node4370Labels := by
  calc
    mixedMoment B raw19634 raw19634Labels = mixedMoment B raw19634step0 raw19634step0Labels := by
      have hz : ∀ j, raw19634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19634step0 = (fun i j => raw19634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19634step0 raw19634; decide +kernel
      have hl : raw19634step0Labels = raw19634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19634 raw19634Labels permutation346 hz
    mixedMoment B raw19634step0 raw19634step0Labels = mixedMoment B raw19634step1 raw19634step1Labels := by
      have hz : ∀ j, raw19634step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19634step1 = (fun i j => raw19634step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19634step1 raw19634step0; decide +kernel
      have hl : raw19634step1Labels = raw19634step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19634step0 raw19634step0Labels permutation56 hz
    mixedMoment B raw19634step1 raw19634step1Labels = mixedMoment B raw19634step2 raw19634step2Labels := by
      have ha : raw19634step2 = (fun i j => raw19634step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19634step2 raw19634step1; decide +kernel
      have hl : raw19634step2Labels = raw19634step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19634step1 raw19634step1Labels permutation31 permutation2
    mixedMoment B raw19634step2 raw19634step2Labels = mixedMoment B raw19634step3 raw19634step3Labels := by
      have ha : raw19634step3 = -raw19634step2 := by apply Matrix.ext; change ∀ i j, raw19634step3 i j = -(raw19634step2 i j); unfold raw19634step3 raw19634step2; decide +kernel
      have hl : raw19634step3Labels = raw19634step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4370 node4370Labels := by rfl

theorem canonical19635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19635 raw19635Labels = mixedMoment B node4163 node4163Labels := by
  calc
    mixedMoment B raw19635 raw19635Labels = mixedMoment B raw19635step0 raw19635step0Labels := by
      have hz : ∀ j, raw19635 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19635step0 = (fun i j => raw19635 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19635step0 raw19635; decide +kernel
      have hl : raw19635step0Labels = raw19635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19635 raw19635Labels permutation434 hz
    mixedMoment B raw19635step0 raw19635step0Labels = mixedMoment B raw19635step1 raw19635step1Labels := by
      have hz : ∀ j, raw19635step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19635step1 = (fun i j => raw19635step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19635step1 raw19635step0; decide +kernel
      have hl : raw19635step1Labels = raw19635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19635step0 raw19635step0Labels permutation80 hz
    mixedMoment B raw19635step1 raw19635step1Labels = mixedMoment B raw19635step2 raw19635step2Labels := by
      have hz : ∀ j, raw19635step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19635step2 = (fun i j => raw19635step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19635step2 raw19635step1; decide +kernel
      have hl : raw19635step2Labels = raw19635step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19635step1 raw19635step1Labels permutation14 hz
    mixedMoment B raw19635step2 raw19635step2Labels = mixedMoment B raw19635step3 raw19635step3Labels := by
      have ha : raw19635step3 = (fun i j => raw19635step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19635step3 raw19635step2; decide +kernel
      have hl : raw19635step3Labels = raw19635step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19635step2 raw19635step2Labels permutation7 permutation2
    mixedMoment B raw19635step3 raw19635step3Labels = mixedMoment B raw19635step4 raw19635step4Labels := by
      have ha : raw19635step4 = -raw19635step3 := by apply Matrix.ext; change ∀ i j, raw19635step4 i j = -(raw19635step3 i j); unfold raw19635step4 raw19635step3; decide +kernel
      have hl : raw19635step4Labels = raw19635step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4163 node4163Labels := by rfl

theorem canonical19636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19636 raw19636Labels = mixedMoment B node4156 node4156Labels := by
  calc
    mixedMoment B raw19636 raw19636Labels = mixedMoment B raw19636step0 raw19636step0Labels := by
      have hz : ∀ j, raw19636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19636step0 = (fun i j => raw19636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19636step0 raw19636; decide +kernel
      have hl : raw19636step0Labels = raw19636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19636 raw19636Labels permutation434 hz
    mixedMoment B raw19636step0 raw19636step0Labels = mixedMoment B raw19636step1 raw19636step1Labels := by
      have hz : ∀ j, raw19636step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19636step1 = (fun i j => raw19636step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19636step1 raw19636step0; decide +kernel
      have hl : raw19636step1Labels = raw19636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19636step0 raw19636step0Labels permutation80 hz
    mixedMoment B raw19636step1 raw19636step1Labels = mixedMoment B raw19636step2 raw19636step2Labels := by
      have ha : raw19636step2 = (fun i j => raw19636step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19636step2 raw19636step1; decide +kernel
      have hl : raw19636step2Labels = raw19636step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19636step1 raw19636step1Labels permutation31 permutation2
    mixedMoment B raw19636step2 raw19636step2Labels = mixedMoment B raw19636step3 raw19636step3Labels := by
      have ha : raw19636step3 = -raw19636step2 := by apply Matrix.ext; change ∀ i j, raw19636step3 i j = -(raw19636step2 i j); unfold raw19636step3 raw19636step2; decide +kernel
      have hl : raw19636step3Labels = raw19636step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4156 node4156Labels := by rfl

theorem canonical19637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19637 raw19637Labels = mixedMoment B node4156 node4156Labels := by
  calc
    mixedMoment B raw19637 raw19637Labels = mixedMoment B raw19637step0 raw19637step0Labels := by
      have hz : ∀ j, raw19637 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19637step0 = (fun i j => raw19637 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19637step0 raw19637; decide +kernel
      have hl : raw19637step0Labels = raw19637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19637 raw19637Labels permutation434 hz
    mixedMoment B raw19637step0 raw19637step0Labels = mixedMoment B raw19637step1 raw19637step1Labels := by
      have hz : ∀ j, raw19637step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19637step1 = (fun i j => raw19637step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19637step1 raw19637step0; decide +kernel
      have hl : raw19637step1Labels = raw19637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19637step0 raw19637step0Labels permutation56 hz
    mixedMoment B raw19637step1 raw19637step1Labels = mixedMoment B raw19637step2 raw19637step2Labels := by
      have ha : raw19637step2 = (fun i j => raw19637step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19637step2 raw19637step1; decide +kernel
      have hl : raw19637step2Labels = raw19637step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19637step1 raw19637step1Labels permutation31 permutation2
    mixedMoment B raw19637step2 raw19637step2Labels = mixedMoment B raw19637step3 raw19637step3Labels := by
      have ha : raw19637step3 = -raw19637step2 := by apply Matrix.ext; change ∀ i j, raw19637step3 i j = -(raw19637step2 i j); unfold raw19637step3 raw19637step2; decide +kernel
      have hl : raw19637step3Labels = raw19637step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4156 node4156Labels := by rfl

theorem canonical19638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19638 raw19638Labels = mixedMoment B node4156 node4156Labels := by
  calc
    mixedMoment B raw19638 raw19638Labels = mixedMoment B raw19638step0 raw19638step0Labels := by
      have hz : ∀ j, raw19638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19638step0 = (fun i j => raw19638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19638step0 raw19638; decide +kernel
      have hl : raw19638step0Labels = raw19638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19638 raw19638Labels permutation346 hz
    mixedMoment B raw19638step0 raw19638step0Labels = mixedMoment B raw19638step1 raw19638step1Labels := by
      have hz : ∀ j, raw19638step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19638step1 = (fun i j => raw19638step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19638step1 raw19638step0; decide +kernel
      have hl : raw19638step1Labels = raw19638step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19638step0 raw19638step0Labels permutation56 hz
    mixedMoment B raw19638step1 raw19638step1Labels = mixedMoment B raw19638step2 raw19638step2Labels := by
      have ha : raw19638step2 = (fun i j => raw19638step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19638step2 raw19638step1; decide +kernel
      have hl : raw19638step2Labels = raw19638step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19638step1 raw19638step1Labels permutation31 permutation2
    mixedMoment B raw19638step2 raw19638step2Labels = mixedMoment B raw19638step3 raw19638step3Labels := by
      have ha : raw19638step3 = -raw19638step2 := by apply Matrix.ext; change ∀ i j, raw19638step3 i j = -(raw19638step2 i j); unfold raw19638step3 raw19638step2; decide +kernel
      have hl : raw19638step3Labels = raw19638step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4156 node4156Labels := by rfl

theorem canonical19639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19639 raw19639Labels = mixedMoment B node4187 node4187Labels := by
  calc
    mixedMoment B raw19639 raw19639Labels = mixedMoment B raw19639step0 raw19639step0Labels := by
      have hz : ∀ j, raw19639 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19639step0 = (fun i j => raw19639 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19639step0 raw19639; decide +kernel
      have hl : raw19639step0Labels = raw19639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19639 raw19639Labels permutation434 hz
    mixedMoment B raw19639step0 raw19639step0Labels = mixedMoment B raw19639step1 raw19639step1Labels := by
      have hz : ∀ j, raw19639step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19639step1 = (fun i j => raw19639step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19639step1 raw19639step0; decide +kernel
      have hl : raw19639step1Labels = raw19639step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19639step0 raw19639step0Labels permutation80 hz
    mixedMoment B raw19639step1 raw19639step1Labels = mixedMoment B raw19639step2 raw19639step2Labels := by
      have hz : ∀ j, raw19639step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19639step2 = (fun i j => raw19639step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19639step2 raw19639step1; decide +kernel
      have hl : raw19639step2Labels = raw19639step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19639step1 raw19639step1Labels permutation14 hz
    mixedMoment B raw19639step2 raw19639step2Labels = mixedMoment B raw19639step3 raw19639step3Labels := by
      have ha : raw19639step3 = (fun i j => raw19639step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19639step3 raw19639step2; decide +kernel
      have hl : raw19639step3Labels = raw19639step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19639step2 raw19639step2Labels permutation7 permutation2
    mixedMoment B raw19639step3 raw19639step3Labels = mixedMoment B raw19639step4 raw19639step4Labels := by
      have ha : raw19639step4 = -raw19639step3 := by apply Matrix.ext; change ∀ i j, raw19639step4 i j = -(raw19639step3 i j); unfold raw19639step4 raw19639step3; decide +kernel
      have hl : raw19639step4Labels = raw19639step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4187 node4187Labels := by rfl

theorem canonical19668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19668 raw19668Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw19668 raw19668Labels = mixedMoment B raw19668step0 raw19668step0Labels := by
      have hz : ∀ j, raw19668 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19668step0 = (fun i j => raw19668 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19668step0 raw19668; decide +kernel
      have hl : raw19668step0Labels = raw19668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19668 raw19668Labels permutation434 hz
    mixedMoment B raw19668step0 raw19668step0Labels = mixedMoment B raw19668step1 raw19668step1Labels := by
      have hz : ∀ j, raw19668step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19668step1 = (fun i j => raw19668step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19668step1 raw19668step0; decide +kernel
      have hl : raw19668step1Labels = raw19668step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19668step0 raw19668step0Labels permutation80 hz
    mixedMoment B raw19668step1 raw19668step1Labels = mixedMoment B raw19668step2 raw19668step2Labels := by
      have ha : raw19668step2 = (fun i j => raw19668step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19668step2 raw19668step1; decide +kernel
      have hl : raw19668step2Labels = raw19668step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19668step1 raw19668step1Labels permutation10 permutation5
    mixedMoment B raw19668step2 raw19668step2Labels = mixedMoment B raw19668step3 raw19668step3Labels := by
      have ha : raw19668step3 = -raw19668step2 := by apply Matrix.ext; change ∀ i j, raw19668step3 i j = -(raw19668step2 i j); unfold raw19668step3 raw19668step2; decide +kernel
      have hl : raw19668step3Labels = raw19668step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19668step3 raw19668step3Labels = mixedMoment B raw19668step4 raw19668step4Labels := by
      have ha : raw19668step4 = raw19668step3 := by apply Matrix.ext; unfold raw19668step4 raw19668step3; decide +kernel
      have hl : raw19668step3Labels = labelEmbedding1 ∘ raw19668step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19668step3 raw19668step3Labels raw19668step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1532 node1532Labels := by rfl

theorem canonical19669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19669 raw19669Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw19669 raw19669Labels = mixedMoment B raw19669step0 raw19669step0Labels := by
      have hz : ∀ j, raw19669 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19669step0 = (fun i j => raw19669 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19669step0 raw19669; decide +kernel
      have hl : raw19669step0Labels = raw19669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19669 raw19669Labels permutation434 hz
    mixedMoment B raw19669step0 raw19669step0Labels = mixedMoment B raw19669step1 raw19669step1Labels := by
      have ha : raw19669step1 = (fun i j => raw19669step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19669step1 raw19669step0; decide +kernel
      have hl : raw19669step1Labels = raw19669step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19669step0 raw19669step0Labels permutation137 permutation7
    mixedMoment B raw19669step1 raw19669step1Labels = mixedMoment B raw19669step2 raw19669step2Labels := by
      have ha : raw19669step2 = raw19669step1 := by apply Matrix.ext; unfold raw19669step2 raw19669step1; decide +kernel
      have hl : raw19669step1Labels = labelEmbedding1 ∘ raw19669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19669step1 raw19669step1Labels raw19669step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

theorem canonical19670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19670 raw19670Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw19670 raw19670Labels = mixedMoment B raw19670step0 raw19670step0Labels := by
      have hz : ∀ j, raw19670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19670step0 = (fun i j => raw19670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19670step0 raw19670; decide +kernel
      have hl : raw19670step0Labels = raw19670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19670 raw19670Labels permutation346 hz
    mixedMoment B raw19670step0 raw19670step0Labels = mixedMoment B raw19670step1 raw19670step1Labels := by
      have ha : raw19670step1 = (fun i j => raw19670step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19670step1 raw19670step0; decide +kernel
      have hl : raw19670step1Labels = raw19670step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19670step0 raw19670step0Labels permutation137 permutation7
    mixedMoment B raw19670step1 raw19670step1Labels = mixedMoment B raw19670step2 raw19670step2Labels := by
      have ha : raw19670step2 = raw19670step1 := by apply Matrix.ext; unfold raw19670step2 raw19670step1; decide +kernel
      have hl : raw19670step1Labels = labelEmbedding1 ∘ raw19670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19670step1 raw19670step1Labels raw19670step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

theorem canonical19671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19671 raw19671Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw19671 raw19671Labels = mixedMoment B raw19671step0 raw19671step0Labels := by
      have hz : ∀ j, raw19671 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19671step0 = (fun i j => raw19671 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19671step0 raw19671; decide +kernel
      have hl : raw19671step0Labels = raw19671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19671 raw19671Labels permutation434 hz
    mixedMoment B raw19671step0 raw19671step0Labels = mixedMoment B raw19671step1 raw19671step1Labels := by
      have hz : ∀ j, raw19671step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19671step1 = (fun i j => raw19671step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19671step1 raw19671step0; decide +kernel
      have hl : raw19671step1Labels = raw19671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19671step0 raw19671step0Labels permutation80 hz
    mixedMoment B raw19671step1 raw19671step1Labels = mixedMoment B raw19671step2 raw19671step2Labels := by
      have ha : raw19671step2 = (fun i j => raw19671step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19671step2 raw19671step1; decide +kernel
      have hl : raw19671step2Labels = raw19671step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19671step1 raw19671step1Labels permutation29 permutation7
    mixedMoment B raw19671step2 raw19671step2Labels = mixedMoment B raw19671step3 raw19671step3Labels := by
      have ha : raw19671step3 = raw19671step2 := by apply Matrix.ext; unfold raw19671step3 raw19671step2; decide +kernel
      have hl : raw19671step2Labels = labelEmbedding1 ∘ raw19671step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19671step2 raw19671step2Labels raw19671step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

theorem canonical19672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19672 raw19672Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw19672 raw19672Labels = mixedMoment B raw19672step0 raw19672step0Labels := by
      have hz : ∀ j, raw19672 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19672step0 = (fun i j => raw19672 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19672step0 raw19672; decide +kernel
      have hl : raw19672step0Labels = raw19672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19672 raw19672Labels permutation434 hz
    mixedMoment B raw19672step0 raw19672step0Labels = mixedMoment B raw19672step1 raw19672step1Labels := by
      have hz : ∀ j, raw19672step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19672step1 = (fun i j => raw19672step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19672step1 raw19672step0; decide +kernel
      have hl : raw19672step1Labels = raw19672step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19672step0 raw19672step0Labels permutation56 hz
    mixedMoment B raw19672step1 raw19672step1Labels = mixedMoment B raw19672step2 raw19672step2Labels := by
      have ha : raw19672step2 = (fun i j => raw19672step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19672step2 raw19672step1; decide +kernel
      have hl : raw19672step2Labels = raw19672step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19672step1 raw19672step1Labels permutation10 permutation5
    mixedMoment B raw19672step2 raw19672step2Labels = mixedMoment B raw19672step3 raw19672step3Labels := by
      have ha : raw19672step3 = -raw19672step2 := by apply Matrix.ext; change ∀ i j, raw19672step3 i j = -(raw19672step2 i j); unfold raw19672step3 raw19672step2; decide +kernel
      have hl : raw19672step3Labels = raw19672step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19672step3 raw19672step3Labels = mixedMoment B raw19672step4 raw19672step4Labels := by
      have ha : raw19672step4 = raw19672step3 := by apply Matrix.ext; unfold raw19672step4 raw19672step3; decide +kernel
      have hl : raw19672step3Labels = labelEmbedding1 ∘ raw19672step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19672step3 raw19672step3Labels raw19672step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1532 node1532Labels := by rfl

theorem canonical19673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19673 raw19673Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw19673 raw19673Labels = mixedMoment B raw19673step0 raw19673step0Labels := by
      have hz : ∀ j, raw19673 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19673step0 = (fun i j => raw19673 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19673step0 raw19673; decide +kernel
      have hl : raw19673step0Labels = raw19673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19673 raw19673Labels permutation434 hz
    mixedMoment B raw19673step0 raw19673step0Labels = mixedMoment B raw19673step1 raw19673step1Labels := by
      have ha : raw19673step1 = (fun i j => raw19673step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19673step1 raw19673step0; decide +kernel
      have hl : raw19673step1Labels = raw19673step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19673step0 raw19673step0Labels permutation143 permutation7
    mixedMoment B raw19673step1 raw19673step1Labels = mixedMoment B raw19673step2 raw19673step2Labels := by
      have ha : raw19673step2 = raw19673step1 := by apply Matrix.ext; unfold raw19673step2 raw19673step1; decide +kernel
      have hl : raw19673step1Labels = labelEmbedding1 ∘ raw19673step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19673step1 raw19673step1Labels raw19673step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

theorem canonical19674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19674 raw19674Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw19674 raw19674Labels = mixedMoment B raw19674step0 raw19674step0Labels := by
      have hz : ∀ j, raw19674 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19674step0 = (fun i j => raw19674 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19674step0 raw19674; decide +kernel
      have hl : raw19674step0Labels = raw19674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19674 raw19674Labels permutation265 hz
    mixedMoment B raw19674step0 raw19674step0Labels = mixedMoment B raw19674step1 raw19674step1Labels := by
      have ha : raw19674step1 = (fun i j => raw19674step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19674step1 raw19674step0; decide +kernel
      have hl : raw19674step1Labels = raw19674step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19674step0 raw19674step0Labels permutation137 permutation7
    mixedMoment B raw19674step1 raw19674step1Labels = mixedMoment B raw19674step2 raw19674step2Labels := by
      have ha : raw19674step2 = raw19674step1 := by apply Matrix.ext; unfold raw19674step2 raw19674step1; decide +kernel
      have hl : raw19674step1Labels = labelEmbedding1 ∘ raw19674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19674step1 raw19674step1Labels raw19674step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

theorem canonical19675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19675 raw19675Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw19675 raw19675Labels = mixedMoment B raw19675step0 raw19675step0Labels := by
      have hz : ∀ j, raw19675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19675step0 = (fun i j => raw19675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19675step0 raw19675; decide +kernel
      have hl : raw19675step0Labels = raw19675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19675 raw19675Labels permutation434 hz
    mixedMoment B raw19675step0 raw19675step0Labels = mixedMoment B raw19675step1 raw19675step1Labels := by
      have hz : ∀ j, raw19675step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19675step1 = (fun i j => raw19675step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19675step1 raw19675step0; decide +kernel
      have hl : raw19675step1Labels = raw19675step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19675step0 raw19675step0Labels permutation56 hz
    mixedMoment B raw19675step1 raw19675step1Labels = mixedMoment B raw19675step2 raw19675step2Labels := by
      have ha : raw19675step2 = (fun i j => raw19675step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19675step2 raw19675step1; decide +kernel
      have hl : raw19675step2Labels = raw19675step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19675step1 raw19675step1Labels permutation29 permutation7
    mixedMoment B raw19675step2 raw19675step2Labels = mixedMoment B raw19675step3 raw19675step3Labels := by
      have ha : raw19675step3 = raw19675step2 := by apply Matrix.ext; unfold raw19675step3 raw19675step2; decide +kernel
      have hl : raw19675step2Labels = labelEmbedding1 ∘ raw19675step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19675step2 raw19675step2Labels raw19675step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

theorem canonical19676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19676 raw19676Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw19676 raw19676Labels = mixedMoment B raw19676step0 raw19676step0Labels := by
      have hz : ∀ j, raw19676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19676step0 = (fun i j => raw19676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19676step0 raw19676; decide +kernel
      have hl : raw19676step0Labels = raw19676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19676 raw19676Labels permutation346 hz
    mixedMoment B raw19676step0 raw19676step0Labels = mixedMoment B raw19676step1 raw19676step1Labels := by
      have hz : ∀ j, raw19676step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19676step1 = (fun i j => raw19676step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19676step1 raw19676step0; decide +kernel
      have hl : raw19676step1Labels = raw19676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19676step0 raw19676step0Labels permutation56 hz
    mixedMoment B raw19676step1 raw19676step1Labels = mixedMoment B raw19676step2 raw19676step2Labels := by
      have ha : raw19676step2 = (fun i j => raw19676step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19676step2 raw19676step1; decide +kernel
      have hl : raw19676step2Labels = raw19676step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19676step1 raw19676step1Labels permutation10 permutation5
    mixedMoment B raw19676step2 raw19676step2Labels = mixedMoment B raw19676step3 raw19676step3Labels := by
      have ha : raw19676step3 = -raw19676step2 := by apply Matrix.ext; change ∀ i j, raw19676step3 i j = -(raw19676step2 i j); unfold raw19676step3 raw19676step2; decide +kernel
      have hl : raw19676step3Labels = raw19676step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19676step3 raw19676step3Labels = mixedMoment B raw19676step4 raw19676step4Labels := by
      have ha : raw19676step4 = raw19676step3 := by apply Matrix.ext; unfold raw19676step4 raw19676step3; decide +kernel
      have hl : raw19676step3Labels = labelEmbedding1 ∘ raw19676step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19676step3 raw19676step3Labels raw19676step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1532 node1532Labels := by rfl

theorem canonical19677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19677 raw19677Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw19677 raw19677Labels = mixedMoment B raw19677step0 raw19677step0Labels := by
      have hz : ∀ j, raw19677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19677step0 = (fun i j => raw19677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19677step0 raw19677; decide +kernel
      have hl : raw19677step0Labels = raw19677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19677 raw19677Labels permutation346 hz
    mixedMoment B raw19677step0 raw19677step0Labels = mixedMoment B raw19677step1 raw19677step1Labels := by
      have ha : raw19677step1 = (fun i j => raw19677step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19677step1 raw19677step0; decide +kernel
      have hl : raw19677step1Labels = raw19677step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19677step0 raw19677step0Labels permutation143 permutation7
    mixedMoment B raw19677step1 raw19677step1Labels = mixedMoment B raw19677step2 raw19677step2Labels := by
      have ha : raw19677step2 = raw19677step1 := by apply Matrix.ext; unfold raw19677step2 raw19677step1; decide +kernel
      have hl : raw19677step1Labels = labelEmbedding1 ∘ raw19677step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19677step1 raw19677step1Labels raw19677step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

theorem canonical19678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19678 raw19678Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw19678 raw19678Labels = mixedMoment B raw19678step0 raw19678step0Labels := by
      have hz : ∀ j, raw19678 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19678step0 = (fun i j => raw19678 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19678step0 raw19678; decide +kernel
      have hl : raw19678step0Labels = raw19678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19678 raw19678Labels permutation265 hz
    mixedMoment B raw19678step0 raw19678step0Labels = mixedMoment B raw19678step1 raw19678step1Labels := by
      have ha : raw19678step1 = (fun i j => raw19678step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19678step1 raw19678step0; decide +kernel
      have hl : raw19678step1Labels = raw19678step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19678step0 raw19678step0Labels permutation143 permutation7
    mixedMoment B raw19678step1 raw19678step1Labels = mixedMoment B raw19678step2 raw19678step2Labels := by
      have ha : raw19678step2 = raw19678step1 := by apply Matrix.ext; unfold raw19678step2 raw19678step1; decide +kernel
      have hl : raw19678step1Labels = labelEmbedding1 ∘ raw19678step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19678step1 raw19678step1Labels raw19678step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

theorem canonical19679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19679 raw19679Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw19679 raw19679Labels = mixedMoment B raw19679step0 raw19679step0Labels := by
      have hz : ∀ j, raw19679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19679step0 = (fun i j => raw19679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19679step0 raw19679; decide +kernel
      have hl : raw19679step0Labels = raw19679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19679 raw19679Labels permutation346 hz
    mixedMoment B raw19679step0 raw19679step0Labels = mixedMoment B raw19679step1 raw19679step1Labels := by
      have hz : ∀ j, raw19679step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19679step1 = (fun i j => raw19679step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19679step1 raw19679step0; decide +kernel
      have hl : raw19679step1Labels = raw19679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19679step0 raw19679step0Labels permutation56 hz
    mixedMoment B raw19679step1 raw19679step1Labels = mixedMoment B raw19679step2 raw19679step2Labels := by
      have ha : raw19679step2 = (fun i j => raw19679step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19679step2 raw19679step1; decide +kernel
      have hl : raw19679step2Labels = raw19679step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19679step1 raw19679step1Labels permutation29 permutation7
    mixedMoment B raw19679step2 raw19679step2Labels = mixedMoment B raw19679step3 raw19679step3Labels := by
      have ha : raw19679step3 = raw19679step2 := by apply Matrix.ext; unfold raw19679step3 raw19679step2; decide +kernel
      have hl : raw19679step2Labels = labelEmbedding1 ∘ raw19679step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19679step2 raw19679step2Labels raw19679step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

theorem canonical19680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19680 raw19680Labels = mixedMoment B node1540 node1540Labels := by
  calc
    mixedMoment B raw19680 raw19680Labels = mixedMoment B raw19680step0 raw19680step0Labels := by
      have hz : ∀ j, raw19680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19680step0 = (fun i j => raw19680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19680step0 raw19680; decide +kernel
      have hl : raw19680step0Labels = raw19680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19680 raw19680Labels permutation434 hz
    mixedMoment B raw19680step0 raw19680step0Labels = mixedMoment B raw19680step1 raw19680step1Labels := by
      have hz : ∀ j, raw19680step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19680step1 = (fun i j => raw19680step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19680step1 raw19680step0; decide +kernel
      have hl : raw19680step1Labels = raw19680step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19680step0 raw19680step0Labels permutation80 hz
    mixedMoment B raw19680step1 raw19680step1Labels = mixedMoment B raw19680step2 raw19680step2Labels := by
      have hz : ∀ j, raw19680step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19680step2 = (fun i j => raw19680step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19680step2 raw19680step1; decide +kernel
      have hl : raw19680step2Labels = raw19680step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19680step1 raw19680step1Labels permutation14 hz
    mixedMoment B raw19680step2 raw19680step2Labels = mixedMoment B raw19680step3 raw19680step3Labels := by
      have ha : raw19680step3 = (fun i j => raw19680step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19680step3 raw19680step2; decide +kernel
      have hl : raw19680step3Labels = raw19680step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19680step2 raw19680step2Labels permutation3 permutation5
    mixedMoment B raw19680step3 raw19680step3Labels = mixedMoment B raw19680step4 raw19680step4Labels := by
      have ha : raw19680step4 = -raw19680step3 := by apply Matrix.ext; change ∀ i j, raw19680step4 i j = -(raw19680step3 i j); unfold raw19680step4 raw19680step3; decide +kernel
      have hl : raw19680step4Labels = raw19680step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19680step4 raw19680step4Labels = mixedMoment B raw19680step5 raw19680step5Labels := by
      have ha : raw19680step5 = raw19680step4 := by apply Matrix.ext; unfold raw19680step5 raw19680step4; decide +kernel
      have hl : raw19680step4Labels = labelEmbedding1 ∘ raw19680step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19680step4 raw19680step4Labels raw19680step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1540 node1540Labels := by rfl

theorem canonical19681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19681 raw19681Labels = mixedMoment B node1722 node1722Labels := by
  calc
    mixedMoment B raw19681 raw19681Labels = mixedMoment B raw19681step0 raw19681step0Labels := by
      have hz : ∀ j, raw19681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19681step0 = (fun i j => raw19681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19681step0 raw19681; decide +kernel
      have hl : raw19681step0Labels = raw19681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19681 raw19681Labels permutation434 hz
    mixedMoment B raw19681step0 raw19681step0Labels = mixedMoment B raw19681step1 raw19681step1Labels := by
      have hz : ∀ j, raw19681step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19681step1 = (fun i j => raw19681step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19681step1 raw19681step0; decide +kernel
      have hl : raw19681step1Labels = raw19681step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19681step0 raw19681step0Labels permutation80 hz
    mixedMoment B raw19681step1 raw19681step1Labels = mixedMoment B raw19681step2 raw19681step2Labels := by
      have ha : raw19681step2 = (fun i j => raw19681step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19681step2 raw19681step1; decide +kernel
      have hl : raw19681step2Labels = raw19681step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19681step1 raw19681step1Labels permutation29 permutation7
    mixedMoment B raw19681step2 raw19681step2Labels = mixedMoment B raw19681step3 raw19681step3Labels := by
      have ha : raw19681step3 = raw19681step2 := by apply Matrix.ext; unfold raw19681step3 raw19681step2; decide +kernel
      have hl : raw19681step2Labels = labelEmbedding1 ∘ raw19681step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19681step2 raw19681step2Labels raw19681step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1722 node1722Labels := by rfl

theorem canonical19682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19682 raw19682Labels = mixedMoment B node1722 node1722Labels := by
  calc
    mixedMoment B raw19682 raw19682Labels = mixedMoment B raw19682step0 raw19682step0Labels := by
      have hz : ∀ j, raw19682 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19682step0 = (fun i j => raw19682 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19682step0 raw19682; decide +kernel
      have hl : raw19682step0Labels = raw19682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19682 raw19682Labels permutation434 hz
    mixedMoment B raw19682step0 raw19682step0Labels = mixedMoment B raw19682step1 raw19682step1Labels := by
      have hz : ∀ j, raw19682step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19682step1 = (fun i j => raw19682step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19682step1 raw19682step0; decide +kernel
      have hl : raw19682step1Labels = raw19682step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19682step0 raw19682step0Labels permutation56 hz
    mixedMoment B raw19682step1 raw19682step1Labels = mixedMoment B raw19682step2 raw19682step2Labels := by
      have ha : raw19682step2 = (fun i j => raw19682step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19682step2 raw19682step1; decide +kernel
      have hl : raw19682step2Labels = raw19682step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19682step1 raw19682step1Labels permutation29 permutation7
    mixedMoment B raw19682step2 raw19682step2Labels = mixedMoment B raw19682step3 raw19682step3Labels := by
      have ha : raw19682step3 = raw19682step2 := by apply Matrix.ext; unfold raw19682step3 raw19682step2; decide +kernel
      have hl : raw19682step2Labels = labelEmbedding1 ∘ raw19682step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19682step2 raw19682step2Labels raw19682step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1722 node1722Labels := by rfl

theorem canonical19683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19683 raw19683Labels = mixedMoment B node1722 node1722Labels := by
  calc
    mixedMoment B raw19683 raw19683Labels = mixedMoment B raw19683step0 raw19683step0Labels := by
      have hz : ∀ j, raw19683 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19683step0 = (fun i j => raw19683 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19683step0 raw19683; decide +kernel
      have hl : raw19683step0Labels = raw19683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19683 raw19683Labels permutation346 hz
    mixedMoment B raw19683step0 raw19683step0Labels = mixedMoment B raw19683step1 raw19683step1Labels := by
      have hz : ∀ j, raw19683step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19683step1 = (fun i j => raw19683step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19683step1 raw19683step0; decide +kernel
      have hl : raw19683step1Labels = raw19683step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19683step0 raw19683step0Labels permutation56 hz
    mixedMoment B raw19683step1 raw19683step1Labels = mixedMoment B raw19683step2 raw19683step2Labels := by
      have ha : raw19683step2 = (fun i j => raw19683step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19683step2 raw19683step1; decide +kernel
      have hl : raw19683step2Labels = raw19683step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19683step1 raw19683step1Labels permutation29 permutation7
    mixedMoment B raw19683step2 raw19683step2Labels = mixedMoment B raw19683step3 raw19683step3Labels := by
      have ha : raw19683step3 = raw19683step2 := by apply Matrix.ext; unfold raw19683step3 raw19683step2; decide +kernel
      have hl : raw19683step2Labels = labelEmbedding1 ∘ raw19683step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19683step2 raw19683step2Labels raw19683step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1722 node1722Labels := by rfl

theorem canonical19684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19684 raw19684Labels = mixedMoment B node1534 node1534Labels := by
  calc
    mixedMoment B raw19684 raw19684Labels = mixedMoment B raw19684step0 raw19684step0Labels := by
      have hz : ∀ j, raw19684 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19684step0 = (fun i j => raw19684 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19684step0 raw19684; decide +kernel
      have hl : raw19684step0Labels = raw19684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19684 raw19684Labels permutation434 hz
    mixedMoment B raw19684step0 raw19684step0Labels = mixedMoment B raw19684step1 raw19684step1Labels := by
      have hz : ∀ j, raw19684step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19684step1 = (fun i j => raw19684step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19684step1 raw19684step0; decide +kernel
      have hl : raw19684step1Labels = raw19684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19684step0 raw19684step0Labels permutation80 hz
    mixedMoment B raw19684step1 raw19684step1Labels = mixedMoment B raw19684step2 raw19684step2Labels := by
      have hz : ∀ j, raw19684step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19684step2 = (fun i j => raw19684step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19684step2 raw19684step1; decide +kernel
      have hl : raw19684step2Labels = raw19684step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19684step1 raw19684step1Labels permutation14 hz
    mixedMoment B raw19684step2 raw19684step2Labels = mixedMoment B raw19684step3 raw19684step3Labels := by
      have ha : raw19684step3 = (fun i j => raw19684step2 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19684step3 raw19684step2; decide +kernel
      have hl : raw19684step3Labels = raw19684step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19684step2 raw19684step2Labels permutation2 permutation5
    mixedMoment B raw19684step3 raw19684step3Labels = mixedMoment B raw19684step4 raw19684step4Labels := by
      have ha : raw19684step4 = -raw19684step3 := by apply Matrix.ext; change ∀ i j, raw19684step4 i j = -(raw19684step3 i j); unfold raw19684step4 raw19684step3; decide +kernel
      have hl : raw19684step4Labels = raw19684step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19684step4 raw19684step4Labels = mixedMoment B raw19684step5 raw19684step5Labels := by
      have ha : raw19684step5 = raw19684step4 := by apply Matrix.ext; unfold raw19684step5 raw19684step4; decide +kernel
      have hl : raw19684step4Labels = labelEmbedding1 ∘ raw19684step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19684step4 raw19684step4Labels raw19684step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1534 node1534Labels := by rfl

theorem canonical19685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19685 raw19685Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw19685 raw19685Labels = mixedMoment B raw19685step0 raw19685step0Labels := by
      have hz : ∀ j, raw19685 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19685step0 = (fun i j => raw19685 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19685step0 raw19685; decide +kernel
      have hl : raw19685step0Labels = raw19685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19685 raw19685Labels permutation434 hz
    mixedMoment B raw19685step0 raw19685step0Labels = mixedMoment B raw19685step1 raw19685step1Labels := by
      have hz : ∀ j, raw19685step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19685step1 = (fun i j => raw19685step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19685step1 raw19685step0; decide +kernel
      have hl : raw19685step1Labels = raw19685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19685step0 raw19685step0Labels permutation80 hz
    mixedMoment B raw19685step1 raw19685step1Labels = mixedMoment B raw19685step2 raw19685step2Labels := by
      have ha : raw19685step2 = (fun i j => raw19685step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19685step2 raw19685step1; decide +kernel
      have hl : raw19685step2Labels = raw19685step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19685step1 raw19685step1Labels permutation29 permutation7
    mixedMoment B raw19685step2 raw19685step2Labels = mixedMoment B raw19685step3 raw19685step3Labels := by
      have ha : raw19685step3 = raw19685step2 := by apply Matrix.ext; unfold raw19685step3 raw19685step2; decide +kernel
      have hl : raw19685step2Labels = labelEmbedding1 ∘ raw19685step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19685step2 raw19685step2Labels raw19685step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1516 node1516Labels := by rfl

theorem canonical19686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19686 raw19686Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw19686 raw19686Labels = mixedMoment B raw19686step0 raw19686step0Labels := by
      have hz : ∀ j, raw19686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19686step0 = (fun i j => raw19686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19686step0 raw19686; decide +kernel
      have hl : raw19686step0Labels = raw19686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19686 raw19686Labels permutation434 hz
    mixedMoment B raw19686step0 raw19686step0Labels = mixedMoment B raw19686step1 raw19686step1Labels := by
      have hz : ∀ j, raw19686step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19686step1 = (fun i j => raw19686step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19686step1 raw19686step0; decide +kernel
      have hl : raw19686step1Labels = raw19686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19686step0 raw19686step0Labels permutation56 hz
    mixedMoment B raw19686step1 raw19686step1Labels = mixedMoment B raw19686step2 raw19686step2Labels := by
      have ha : raw19686step2 = (fun i j => raw19686step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19686step2 raw19686step1; decide +kernel
      have hl : raw19686step2Labels = raw19686step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19686step1 raw19686step1Labels permutation29 permutation7
    mixedMoment B raw19686step2 raw19686step2Labels = mixedMoment B raw19686step3 raw19686step3Labels := by
      have ha : raw19686step3 = raw19686step2 := by apply Matrix.ext; unfold raw19686step3 raw19686step2; decide +kernel
      have hl : raw19686step2Labels = labelEmbedding1 ∘ raw19686step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19686step2 raw19686step2Labels raw19686step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1516 node1516Labels := by rfl

theorem canonical19687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19687 raw19687Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw19687 raw19687Labels = mixedMoment B raw19687step0 raw19687step0Labels := by
      have hz : ∀ j, raw19687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19687step0 = (fun i j => raw19687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19687step0 raw19687; decide +kernel
      have hl : raw19687step0Labels = raw19687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19687 raw19687Labels permutation346 hz
    mixedMoment B raw19687step0 raw19687step0Labels = mixedMoment B raw19687step1 raw19687step1Labels := by
      have hz : ∀ j, raw19687step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19687step1 = (fun i j => raw19687step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19687step1 raw19687step0; decide +kernel
      have hl : raw19687step1Labels = raw19687step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19687step0 raw19687step0Labels permutation56 hz
    mixedMoment B raw19687step1 raw19687step1Labels = mixedMoment B raw19687step2 raw19687step2Labels := by
      have ha : raw19687step2 = (fun i j => raw19687step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19687step2 raw19687step1; decide +kernel
      have hl : raw19687step2Labels = raw19687step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19687step1 raw19687step1Labels permutation29 permutation7
    mixedMoment B raw19687step2 raw19687step2Labels = mixedMoment B raw19687step3 raw19687step3Labels := by
      have ha : raw19687step3 = raw19687step2 := by apply Matrix.ext; unfold raw19687step3 raw19687step2; decide +kernel
      have hl : raw19687step2Labels = labelEmbedding1 ∘ raw19687step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19687step2 raw19687step2Labels raw19687step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1516 node1516Labels := by rfl

theorem canonical19688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19688 raw19688Labels = mixedMoment B node1537 node1537Labels := by
  calc
    mixedMoment B raw19688 raw19688Labels = mixedMoment B raw19688step0 raw19688step0Labels := by
      have hz : ∀ j, raw19688 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19688step0 = (fun i j => raw19688 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19688step0 raw19688; decide +kernel
      have hl : raw19688step0Labels = raw19688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19688 raw19688Labels permutation434 hz
    mixedMoment B raw19688step0 raw19688step0Labels = mixedMoment B raw19688step1 raw19688step1Labels := by
      have hz : ∀ j, raw19688step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19688step1 = (fun i j => raw19688step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19688step1 raw19688step0; decide +kernel
      have hl : raw19688step1Labels = raw19688step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19688step0 raw19688step0Labels permutation80 hz
    mixedMoment B raw19688step1 raw19688step1Labels = mixedMoment B raw19688step2 raw19688step2Labels := by
      have hz : ∀ j, raw19688step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19688step2 = (fun i j => raw19688step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19688step2 raw19688step1; decide +kernel
      have hl : raw19688step2Labels = raw19688step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19688step1 raw19688step1Labels permutation14 hz
    mixedMoment B raw19688step2 raw19688step2Labels = mixedMoment B raw19688step3 raw19688step3Labels := by
      have ha : raw19688step3 = (fun i j => raw19688step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19688step3 raw19688step2; decide +kernel
      have hl : raw19688step3Labels = raw19688step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19688step2 raw19688step2Labels permutation7 permutation7
    mixedMoment B raw19688step3 raw19688step3Labels = mixedMoment B raw19688step4 raw19688step4Labels := by
      have ha : raw19688step4 = raw19688step3 := by apply Matrix.ext; unfold raw19688step4 raw19688step3; decide +kernel
      have hl : raw19688step3Labels = labelEmbedding1 ∘ raw19688step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19688step3 raw19688step3Labels raw19688step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1537 node1537Labels := by rfl

theorem canonical19689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19689 raw19689Labels = mixedMoment B node628 node628Labels := by
  calc
    mixedMoment B raw19689 raw19689Labels = mixedMoment B raw19689step0 raw19689step0Labels := by
      have hz : ∀ j, raw19689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19689step0 = (fun i j => raw19689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19689step0 raw19689; decide +kernel
      have hl : raw19689step0Labels = raw19689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19689 raw19689Labels permutation434 hz
    mixedMoment B raw19689step0 raw19689step0Labels = mixedMoment B raw19689step1 raw19689step1Labels := by
      have hz : ∀ j, raw19689step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19689step1 = (fun i j => raw19689step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19689step1 raw19689step0; decide +kernel
      have hl : raw19689step1Labels = raw19689step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19689step0 raw19689step0Labels permutation80 hz
    mixedMoment B raw19689step1 raw19689step1Labels = mixedMoment B raw19689step2 raw19689step2Labels := by
      have ha : raw19689step2 = (fun i j => raw19689step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19689step2 raw19689step1; decide +kernel
      have hl : raw19689step2Labels = raw19689step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19689step1 raw19689step1Labels permutation10 permutation2
    _ = mixedMoment B node628 node628Labels := by rfl

theorem canonical19690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19690 raw19690Labels = mixedMoment B node628 node628Labels := by
  calc
    mixedMoment B raw19690 raw19690Labels = mixedMoment B raw19690step0 raw19690step0Labels := by
      have hz : ∀ j, raw19690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19690step0 = (fun i j => raw19690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19690step0 raw19690; decide +kernel
      have hl : raw19690step0Labels = raw19690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19690 raw19690Labels permutation434 hz
    mixedMoment B raw19690step0 raw19690step0Labels = mixedMoment B raw19690step1 raw19690step1Labels := by
      have hz : ∀ j, raw19690step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19690step1 = (fun i j => raw19690step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19690step1 raw19690step0; decide +kernel
      have hl : raw19690step1Labels = raw19690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19690step0 raw19690step0Labels permutation56 hz
    mixedMoment B raw19690step1 raw19690step1Labels = mixedMoment B raw19690step2 raw19690step2Labels := by
      have ha : raw19690step2 = (fun i j => raw19690step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19690step2 raw19690step1; decide +kernel
      have hl : raw19690step2Labels = raw19690step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19690step1 raw19690step1Labels permutation10 permutation2
    _ = mixedMoment B node628 node628Labels := by rfl

theorem canonical19691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19691 raw19691Labels = mixedMoment B node628 node628Labels := by
  calc
    mixedMoment B raw19691 raw19691Labels = mixedMoment B raw19691step0 raw19691step0Labels := by
      have hz : ∀ j, raw19691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19691step0 = (fun i j => raw19691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19691step0 raw19691; decide +kernel
      have hl : raw19691step0Labels = raw19691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19691 raw19691Labels permutation346 hz
    mixedMoment B raw19691step0 raw19691step0Labels = mixedMoment B raw19691step1 raw19691step1Labels := by
      have hz : ∀ j, raw19691step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19691step1 = (fun i j => raw19691step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19691step1 raw19691step0; decide +kernel
      have hl : raw19691step1Labels = raw19691step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19691step0 raw19691step0Labels permutation56 hz
    mixedMoment B raw19691step1 raw19691step1Labels = mixedMoment B raw19691step2 raw19691step2Labels := by
      have ha : raw19691step2 = (fun i j => raw19691step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19691step2 raw19691step1; decide +kernel
      have hl : raw19691step2Labels = raw19691step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19691step1 raw19691step1Labels permutation10 permutation2
    _ = mixedMoment B node628 node628Labels := by rfl

theorem canonical19692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19692 raw19692Labels = mixedMoment B node643 node643Labels := by
  calc
    mixedMoment B raw19692 raw19692Labels = mixedMoment B raw19692step0 raw19692step0Labels := by
      have hz : ∀ j, raw19692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19692step0 = (fun i j => raw19692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19692step0 raw19692; decide +kernel
      have hl : raw19692step0Labels = raw19692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19692 raw19692Labels permutation434 hz
    mixedMoment B raw19692step0 raw19692step0Labels = mixedMoment B raw19692step1 raw19692step1Labels := by
      have hz : ∀ j, raw19692step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19692step1 = (fun i j => raw19692step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19692step1 raw19692step0; decide +kernel
      have hl : raw19692step1Labels = raw19692step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19692step0 raw19692step0Labels permutation80 hz
    mixedMoment B raw19692step1 raw19692step1Labels = mixedMoment B raw19692step2 raw19692step2Labels := by
      have hz : ∀ j, raw19692step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19692step2 = (fun i j => raw19692step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19692step2 raw19692step1; decide +kernel
      have hl : raw19692step2Labels = raw19692step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19692step1 raw19692step1Labels permutation14 hz
    _ = mixedMoment B node643 node643Labels := by rfl

theorem canonical19693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19693 raw19693Labels = mixedMoment B node591 node591Labels := by
  calc
    mixedMoment B raw19693 raw19693Labels = mixedMoment B raw19693step0 raw19693step0Labels := by
      have hz : ∀ j, raw19693 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19693step0 = (fun i j => raw19693 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19693step0 raw19693; decide +kernel
      have hl : raw19693step0Labels = raw19693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19693 raw19693Labels permutation434 hz
    mixedMoment B raw19693step0 raw19693step0Labels = mixedMoment B raw19693step1 raw19693step1Labels := by
      have hz : ∀ j, raw19693step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19693step1 = (fun i j => raw19693step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19693step1 raw19693step0; decide +kernel
      have hl : raw19693step1Labels = raw19693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19693step0 raw19693step0Labels permutation80 hz
    mixedMoment B raw19693step1 raw19693step1Labels = mixedMoment B raw19693step2 raw19693step2Labels := by
      have hz : ∀ j, raw19693step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19693step2 = (fun i j => raw19693step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19693step2 raw19693step1; decide +kernel
      have hl : raw19693step2Labels = raw19693step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19693step1 raw19693step1Labels permutation14 hz
    mixedMoment B raw19693step2 raw19693step2Labels = mixedMoment B raw19693step3 raw19693step3Labels := by
      have ha : raw19693step3 = (fun i j => raw19693step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19693step3 raw19693step2; decide +kernel
      have hl : raw19693step3Labels = raw19693step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19693step2 raw19693step2Labels permutation7 permutation2
    mixedMoment B raw19693step3 raw19693step3Labels = mixedMoment B raw19693step4 raw19693step4Labels := by
      have ha : raw19693step4 = -raw19693step3 := by apply Matrix.ext; change ∀ i j, raw19693step4 i j = -(raw19693step3 i j); unfold raw19693step4 raw19693step3; decide +kernel
      have hl : raw19693step4Labels = raw19693step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node591 node591Labels := by rfl

theorem canonical19694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19694 raw19694Labels = mixedMoment B node908 node908Labels := by
  calc
    mixedMoment B raw19694 raw19694Labels = mixedMoment B raw19694step0 raw19694step0Labels := by
      have hz : ∀ j, raw19694 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19694step0 = (fun i j => raw19694 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19694step0 raw19694; decide +kernel
      have hl : raw19694step0Labels = raw19694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19694 raw19694Labels permutation434 hz
    mixedMoment B raw19694step0 raw19694step0Labels = mixedMoment B raw19694step1 raw19694step1Labels := by
      have ha : raw19694step1 = (fun i j => raw19694step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19694step1 raw19694step0; decide +kernel
      have hl : raw19694step1Labels = raw19694step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19694step0 raw19694step0Labels permutation139 permutation2
    mixedMoment B raw19694step1 raw19694step1Labels = mixedMoment B raw19694step2 raw19694step2Labels := by
      have ha : raw19694step2 = -raw19694step1 := by apply Matrix.ext; change ∀ i j, raw19694step2 i j = -(raw19694step1 i j); unfold raw19694step2 raw19694step1; decide +kernel
      have hl : raw19694step2Labels = raw19694step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node908 node908Labels := by rfl

theorem canonical19695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19695 raw19695Labels = mixedMoment B node908 node908Labels := by
  calc
    mixedMoment B raw19695 raw19695Labels = mixedMoment B raw19695step0 raw19695step0Labels := by
      have hz : ∀ j, raw19695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19695step0 = (fun i j => raw19695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19695step0 raw19695; decide +kernel
      have hl : raw19695step0Labels = raw19695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19695 raw19695Labels permutation346 hz
    mixedMoment B raw19695step0 raw19695step0Labels = mixedMoment B raw19695step1 raw19695step1Labels := by
      have ha : raw19695step1 = (fun i j => raw19695step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19695step1 raw19695step0; decide +kernel
      have hl : raw19695step1Labels = raw19695step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19695step0 raw19695step0Labels permutation139 permutation2
    mixedMoment B raw19695step1 raw19695step1Labels = mixedMoment B raw19695step2 raw19695step2Labels := by
      have ha : raw19695step2 = -raw19695step1 := by apply Matrix.ext; change ∀ i j, raw19695step2 i j = -(raw19695step1 i j); unfold raw19695step2 raw19695step1; decide +kernel
      have hl : raw19695step2Labels = raw19695step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node908 node908Labels := by rfl

theorem canonical19696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19696 raw19696Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw19696 raw19696Labels = mixedMoment B raw19696step0 raw19696step0Labels := by
      have hz : ∀ j, raw19696 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19696step0 = (fun i j => raw19696 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19696step0 raw19696; decide +kernel
      have hl : raw19696step0Labels = raw19696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19696 raw19696Labels permutation434 hz
    mixedMoment B raw19696step0 raw19696step0Labels = mixedMoment B raw19696step1 raw19696step1Labels := by
      have hz : ∀ j, raw19696step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19696step1 = (fun i j => raw19696step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19696step1 raw19696step0; decide +kernel
      have hl : raw19696step1Labels = raw19696step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19696step0 raw19696step0Labels permutation80 hz
    mixedMoment B raw19696step1 raw19696step1Labels = mixedMoment B raw19696step2 raw19696step2Labels := by
      have ha : raw19696step2 = (fun i j => raw19696step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19696step2 raw19696step1; decide +kernel
      have hl : raw19696step2Labels = raw19696step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19696step1 raw19696step1Labels permutation29 permutation2
    mixedMoment B raw19696step2 raw19696step2Labels = mixedMoment B raw19696step3 raw19696step3Labels := by
      have ha : raw19696step3 = -raw19696step2 := by apply Matrix.ext; change ∀ i j, raw19696step3 i j = -(raw19696step2 i j); unfold raw19696step3 raw19696step2; decide +kernel
      have hl : raw19696step3Labels = raw19696step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node934 node934Labels := by rfl

theorem canonical19697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19697 raw19697Labels = mixedMoment B node908 node908Labels := by
  calc
    mixedMoment B raw19697 raw19697Labels = mixedMoment B raw19697step0 raw19697step0Labels := by
      have hz : ∀ j, raw19697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19697step0 = (fun i j => raw19697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19697step0 raw19697; decide +kernel
      have hl : raw19697step0Labels = raw19697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19697 raw19697Labels permutation434 hz
    mixedMoment B raw19697step0 raw19697step0Labels = mixedMoment B raw19697step1 raw19697step1Labels := by
      have ha : raw19697step1 = (fun i j => raw19697step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19697step1 raw19697step0; decide +kernel
      have hl : raw19697step1Labels = raw19697step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19697step0 raw19697step0Labels permutation145 permutation2
    mixedMoment B raw19697step1 raw19697step1Labels = mixedMoment B raw19697step2 raw19697step2Labels := by
      have ha : raw19697step2 = -raw19697step1 := by apply Matrix.ext; change ∀ i j, raw19697step2 i j = -(raw19697step1 i j); unfold raw19697step2 raw19697step1; decide +kernel
      have hl : raw19697step2Labels = raw19697step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node908 node908Labels := by rfl

theorem canonical19698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19698 raw19698Labels = mixedMoment B node908 node908Labels := by
  calc
    mixedMoment B raw19698 raw19698Labels = mixedMoment B raw19698step0 raw19698step0Labels := by
      have hz : ∀ j, raw19698 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19698step0 = (fun i j => raw19698 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19698step0 raw19698; decide +kernel
      have hl : raw19698step0Labels = raw19698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19698 raw19698Labels permutation346 hz
    mixedMoment B raw19698step0 raw19698step0Labels = mixedMoment B raw19698step1 raw19698step1Labels := by
      have ha : raw19698step1 = (fun i j => raw19698step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19698step1 raw19698step0; decide +kernel
      have hl : raw19698step1Labels = raw19698step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19698step0 raw19698step0Labels permutation145 permutation2
    mixedMoment B raw19698step1 raw19698step1Labels = mixedMoment B raw19698step2 raw19698step2Labels := by
      have ha : raw19698step2 = -raw19698step1 := by apply Matrix.ext; change ∀ i j, raw19698step2 i j = -(raw19698step1 i j); unfold raw19698step2 raw19698step1; decide +kernel
      have hl : raw19698step2Labels = raw19698step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node908 node908Labels := by rfl

theorem canonical19699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19699 raw19699Labels = mixedMoment B node948 node948Labels := by
  calc
    mixedMoment B raw19699 raw19699Labels = mixedMoment B raw19699step0 raw19699step0Labels := by
      have hz : ∀ j, raw19699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19699step0 = (fun i j => raw19699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19699step0 raw19699; decide +kernel
      have hl : raw19699step0Labels = raw19699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19699 raw19699Labels permutation434 hz
    mixedMoment B raw19699step0 raw19699step0Labels = mixedMoment B raw19699step1 raw19699step1Labels := by
      have hz : ∀ j, raw19699step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19699step1 = (fun i j => raw19699step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19699step1 raw19699step0; decide +kernel
      have hl : raw19699step1Labels = raw19699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19699step0 raw19699step0Labels permutation80 hz
    mixedMoment B raw19699step1 raw19699step1Labels = mixedMoment B raw19699step2 raw19699step2Labels := by
      have ha : raw19699step2 = (fun i j => raw19699step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19699step2 raw19699step1; decide +kernel
      have hl : raw19699step2Labels = raw19699step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19699step1 raw19699step1Labels permutation31 permutation2
    mixedMoment B raw19699step2 raw19699step2Labels = mixedMoment B raw19699step3 raw19699step3Labels := by
      have ha : raw19699step3 = -raw19699step2 := by apply Matrix.ext; change ∀ i j, raw19699step3 i j = -(raw19699step2 i j); unfold raw19699step3 raw19699step2; decide +kernel
      have hl : raw19699step3Labels = raw19699step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node948 node948Labels := by rfl

theorem canonical19700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19700 raw19700Labels = mixedMoment B node584 node584Labels := by
  calc
    mixedMoment B raw19700 raw19700Labels = mixedMoment B raw19700step0 raw19700step0Labels := by
      have hz : ∀ j, raw19700 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19700step0 = (fun i j => raw19700 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19700step0 raw19700; decide +kernel
      have hl : raw19700step0Labels = raw19700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19700 raw19700Labels permutation434 hz
    mixedMoment B raw19700step0 raw19700step0Labels = mixedMoment B raw19700step1 raw19700step1Labels := by
      have hz : ∀ j, raw19700step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19700step1 = (fun i j => raw19700step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19700step1 raw19700step0; decide +kernel
      have hl : raw19700step1Labels = raw19700step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19700step0 raw19700step0Labels permutation80 hz
    mixedMoment B raw19700step1 raw19700step1Labels = mixedMoment B raw19700step2 raw19700step2Labels := by
      have ha : raw19700step2 = (fun i j => raw19700step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19700step2 raw19700step1; decide +kernel
      have hl : raw19700step2Labels = raw19700step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19700step1 raw19700step1Labels permutation31 permutation2
    mixedMoment B raw19700step2 raw19700step2Labels = mixedMoment B raw19700step3 raw19700step3Labels := by
      have ha : raw19700step3 = -raw19700step2 := by apply Matrix.ext; change ∀ i j, raw19700step3 i j = -(raw19700step2 i j); unfold raw19700step3 raw19700step2; decide +kernel
      have hl : raw19700step3Labels = raw19700step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node584 node584Labels := by rfl

theorem canonical19701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19701 raw19701Labels = mixedMoment B node948 node948Labels := by
  calc
    mixedMoment B raw19701 raw19701Labels = mixedMoment B raw19701step0 raw19701step0Labels := by
      have hz : ∀ j, raw19701 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19701step0 = (fun i j => raw19701 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19701step0 raw19701; decide +kernel
      have hl : raw19701step0Labels = raw19701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19701 raw19701Labels permutation434 hz
    mixedMoment B raw19701step0 raw19701step0Labels = mixedMoment B raw19701step1 raw19701step1Labels := by
      have hz : ∀ j, raw19701step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19701step1 = (fun i j => raw19701step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19701step1 raw19701step0; decide +kernel
      have hl : raw19701step1Labels = raw19701step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19701step0 raw19701step0Labels permutation56 hz
    mixedMoment B raw19701step1 raw19701step1Labels = mixedMoment B raw19701step2 raw19701step2Labels := by
      have ha : raw19701step2 = (fun i j => raw19701step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19701step2 raw19701step1; decide +kernel
      have hl : raw19701step2Labels = raw19701step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19701step1 raw19701step1Labels permutation31 permutation2
    mixedMoment B raw19701step2 raw19701step2Labels = mixedMoment B raw19701step3 raw19701step3Labels := by
      have ha : raw19701step3 = -raw19701step2 := by apply Matrix.ext; change ∀ i j, raw19701step3 i j = -(raw19701step2 i j); unfold raw19701step3 raw19701step2; decide +kernel
      have hl : raw19701step3Labels = raw19701step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node948 node948Labels := by rfl

theorem canonical19702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19702 raw19702Labels = mixedMoment B node948 node948Labels := by
  calc
    mixedMoment B raw19702 raw19702Labels = mixedMoment B raw19702step0 raw19702step0Labels := by
      have hz : ∀ j, raw19702 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19702step0 = (fun i j => raw19702 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19702step0 raw19702; decide +kernel
      have hl : raw19702step0Labels = raw19702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19702 raw19702Labels permutation346 hz
    mixedMoment B raw19702step0 raw19702step0Labels = mixedMoment B raw19702step1 raw19702step1Labels := by
      have hz : ∀ j, raw19702step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19702step1 = (fun i j => raw19702step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19702step1 raw19702step0; decide +kernel
      have hl : raw19702step1Labels = raw19702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19702step0 raw19702step0Labels permutation56 hz
    mixedMoment B raw19702step1 raw19702step1Labels = mixedMoment B raw19702step2 raw19702step2Labels := by
      have ha : raw19702step2 = (fun i j => raw19702step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19702step2 raw19702step1; decide +kernel
      have hl : raw19702step2Labels = raw19702step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19702step1 raw19702step1Labels permutation31 permutation2
    mixedMoment B raw19702step2 raw19702step2Labels = mixedMoment B raw19702step3 raw19702step3Labels := by
      have ha : raw19702step3 = -raw19702step2 := by apply Matrix.ext; change ∀ i j, raw19702step3 i j = -(raw19702step2 i j); unfold raw19702step3 raw19702step2; decide +kernel
      have hl : raw19702step3Labels = raw19702step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node948 node948Labels := by rfl

theorem canonical19703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19703 raw19703Labels = mixedMoment B node1089 node1089Labels := by
  calc
    mixedMoment B raw19703 raw19703Labels = mixedMoment B raw19703step0 raw19703step0Labels := by
      have hz : ∀ j, raw19703 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19703step0 = (fun i j => raw19703 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19703step0 raw19703; decide +kernel
      have hl : raw19703step0Labels = raw19703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19703 raw19703Labels permutation434 hz
    mixedMoment B raw19703step0 raw19703step0Labels = mixedMoment B raw19703step1 raw19703step1Labels := by
      have hz : ∀ j, raw19703step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19703step1 = (fun i j => raw19703step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19703step1 raw19703step0; decide +kernel
      have hl : raw19703step1Labels = raw19703step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19703step0 raw19703step0Labels permutation80 hz
    mixedMoment B raw19703step1 raw19703step1Labels = mixedMoment B raw19703step2 raw19703step2Labels := by
      have hz : ∀ j, raw19703step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19703step2 = (fun i j => raw19703step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19703step2 raw19703step1; decide +kernel
      have hl : raw19703step2Labels = raw19703step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19703step1 raw19703step1Labels permutation14 hz
    mixedMoment B raw19703step2 raw19703step2Labels = mixedMoment B raw19703step3 raw19703step3Labels := by
      have ha : raw19703step3 = (fun i j => raw19703step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19703step3 raw19703step2; decide +kernel
      have hl : raw19703step3Labels = raw19703step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19703step2 raw19703step2Labels permutation7 permutation2
    mixedMoment B raw19703step3 raw19703step3Labels = mixedMoment B raw19703step4 raw19703step4Labels := by
      have ha : raw19703step4 = -raw19703step3 := by apply Matrix.ext; change ∀ i j, raw19703step4 i j = -(raw19703step3 i j); unfold raw19703step4 raw19703step3; decide +kernel
      have hl : raw19703step4Labels = raw19703step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1089 node1089Labels := by rfl

theorem canonical19704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19704 raw19704Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw19704 raw19704Labels = mixedMoment B raw19704step0 raw19704step0Labels := by
      have hz : ∀ j, raw19704 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19704step0 = (fun i j => raw19704 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19704step0 raw19704; decide +kernel
      have hl : raw19704step0Labels = raw19704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19704 raw19704Labels permutation434 hz
    mixedMoment B raw19704step0 raw19704step0Labels = mixedMoment B raw19704step1 raw19704step1Labels := by
      have hz : ∀ j, raw19704step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19704step1 = (fun i j => raw19704step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19704step1 raw19704step0; decide +kernel
      have hl : raw19704step1Labels = raw19704step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19704step0 raw19704step0Labels permutation56 hz
    mixedMoment B raw19704step1 raw19704step1Labels = mixedMoment B raw19704step2 raw19704step2Labels := by
      have ha : raw19704step2 = (fun i j => raw19704step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19704step2 raw19704step1; decide +kernel
      have hl : raw19704step2Labels = raw19704step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19704step1 raw19704step1Labels permutation29 permutation2
    mixedMoment B raw19704step2 raw19704step2Labels = mixedMoment B raw19704step3 raw19704step3Labels := by
      have ha : raw19704step3 = -raw19704step2 := by apply Matrix.ext; change ∀ i j, raw19704step3 i j = -(raw19704step2 i j); unfold raw19704step3 raw19704step2; decide +kernel
      have hl : raw19704step3Labels = raw19704step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node934 node934Labels := by rfl

theorem canonical19705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19705 raw19705Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw19705 raw19705Labels = mixedMoment B raw19705step0 raw19705step0Labels := by
      have hz : ∀ j, raw19705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19705step0 = (fun i j => raw19705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19705step0 raw19705; decide +kernel
      have hl : raw19705step0Labels = raw19705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19705 raw19705Labels permutation346 hz
    mixedMoment B raw19705step0 raw19705step0Labels = mixedMoment B raw19705step1 raw19705step1Labels := by
      have hz : ∀ j, raw19705step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19705step1 = (fun i j => raw19705step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19705step1 raw19705step0; decide +kernel
      have hl : raw19705step1Labels = raw19705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19705step0 raw19705step0Labels permutation56 hz
    mixedMoment B raw19705step1 raw19705step1Labels = mixedMoment B raw19705step2 raw19705step2Labels := by
      have ha : raw19705step2 = (fun i j => raw19705step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19705step2 raw19705step1; decide +kernel
      have hl : raw19705step2Labels = raw19705step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19705step1 raw19705step1Labels permutation29 permutation2
    mixedMoment B raw19705step2 raw19705step2Labels = mixedMoment B raw19705step3 raw19705step3Labels := by
      have ha : raw19705step3 = -raw19705step2 := by apply Matrix.ext; change ∀ i j, raw19705step3 i j = -(raw19705step2 i j); unfold raw19705step3 raw19705step2; decide +kernel
      have hl : raw19705step3Labels = raw19705step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node934 node934Labels := by rfl

theorem canonical19706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19706 raw19706Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw19706 raw19706Labels = mixedMoment B raw19706step0 raw19706step0Labels := by
      have hz : ∀ j, raw19706 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19706step0 = (fun i j => raw19706 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19706step0 raw19706; decide +kernel
      have hl : raw19706step0Labels = raw19706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19706 raw19706Labels permutation434 hz
    mixedMoment B raw19706step0 raw19706step0Labels = mixedMoment B raw19706step1 raw19706step1Labels := by
      have hz : ∀ j, raw19706step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19706step1 = (fun i j => raw19706step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19706step1 raw19706step0; decide +kernel
      have hl : raw19706step1Labels = raw19706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19706step0 raw19706step0Labels permutation80 hz
    mixedMoment B raw19706step1 raw19706step1Labels = mixedMoment B raw19706step2 raw19706step2Labels := by
      have hz : ∀ j, raw19706step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19706step2 = (fun i j => raw19706step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19706step2 raw19706step1; decide +kernel
      have hl : raw19706step2Labels = raw19706step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19706step1 raw19706step1Labels permutation14 hz
    mixedMoment B raw19706step2 raw19706step2Labels = mixedMoment B raw19706step3 raw19706step3Labels := by
      have ha : raw19706step3 = (fun i j => raw19706step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19706step3 raw19706step2; decide +kernel
      have hl : raw19706step3Labels = raw19706step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19706step2 raw19706step2Labels permutation7 permutation2
    mixedMoment B raw19706step3 raw19706step3Labels = mixedMoment B raw19706step4 raw19706step4Labels := by
      have ha : raw19706step4 = -raw19706step3 := by apply Matrix.ext; change ∀ i j, raw19706step4 i j = -(raw19706step3 i j); unfold raw19706step4 raw19706step3; decide +kernel
      have hl : raw19706step4Labels = raw19706step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node615 node615Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19824 raw19824Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw19824 raw19824Labels = mixedMoment B raw19824step0 raw19824step0Labels := by
      have hz : ∀ j, raw19824 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19824step0 = (fun i j => raw19824 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19824step0 raw19824; decide +kernel
      have hl : raw19824step0Labels = raw19824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19824 raw19824Labels permutation434 hz
    mixedMoment B raw19824step0 raw19824step0Labels = mixedMoment B raw19824step1 raw19824step1Labels := by
      have hz : ∀ j, raw19824step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19824step1 = (fun i j => raw19824step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19824step1 raw19824step0; decide +kernel
      have hl : raw19824step1Labels = raw19824step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19824step0 raw19824step0Labels permutation80 hz
    mixedMoment B raw19824step1 raw19824step1Labels = mixedMoment B raw19824step2 raw19824step2Labels := by
      have hz : ∀ j, raw19824step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19824step2 = (fun i j => raw19824step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19824step2 raw19824step1; decide +kernel
      have hl : raw19824step2Labels = raw19824step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19824step1 raw19824step1Labels permutation14 hz
    mixedMoment B raw19824step2 raw19824step2Labels = mixedMoment B raw19824step3 raw19824step3Labels := by
      have ha : raw19824step3 = (fun i j => raw19824step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19824step3 raw19824step2; decide +kernel
      have hl : raw19824step3Labels = raw19824step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19824step2 raw19824step2Labels permutation7 permutation4
    _ = mixedMoment B node1752 node1752Labels := by rfl

theorem canonical19825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19825 raw19825Labels = mixedMoment B node1620 node1620Labels := by
  calc
    mixedMoment B raw19825 raw19825Labels = mixedMoment B raw19825step0 raw19825step0Labels := by
      have hz : ∀ j, raw19825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19825step0 = (fun i j => raw19825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19825step0 raw19825; decide +kernel
      have hl : raw19825step0Labels = raw19825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19825 raw19825Labels permutation434 hz
    mixedMoment B raw19825step0 raw19825step0Labels = mixedMoment B raw19825step1 raw19825step1Labels := by
      have hz : ∀ j, raw19825step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19825step1 = (fun i j => raw19825step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19825step1 raw19825step0; decide +kernel
      have hl : raw19825step1Labels = raw19825step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19825step0 raw19825step0Labels permutation80 hz
    mixedMoment B raw19825step1 raw19825step1Labels = mixedMoment B raw19825step2 raw19825step2Labels := by
      have ha : raw19825step2 = (fun i j => raw19825step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19825step2 raw19825step1; decide +kernel
      have hl : raw19825step2Labels = raw19825step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19825step1 raw19825step1Labels permutation29 permutation4
    _ = mixedMoment B node1620 node1620Labels := by rfl

theorem canonical19826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19826 raw19826Labels = mixedMoment B node1620 node1620Labels := by
  calc
    mixedMoment B raw19826 raw19826Labels = mixedMoment B raw19826step0 raw19826step0Labels := by
      have hz : ∀ j, raw19826 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19826step0 = (fun i j => raw19826 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19826step0 raw19826; decide +kernel
      have hl : raw19826step0Labels = raw19826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19826 raw19826Labels permutation434 hz
    mixedMoment B raw19826step0 raw19826step0Labels = mixedMoment B raw19826step1 raw19826step1Labels := by
      have hz : ∀ j, raw19826step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19826step1 = (fun i j => raw19826step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19826step1 raw19826step0; decide +kernel
      have hl : raw19826step1Labels = raw19826step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19826step0 raw19826step0Labels permutation56 hz
    mixedMoment B raw19826step1 raw19826step1Labels = mixedMoment B raw19826step2 raw19826step2Labels := by
      have ha : raw19826step2 = (fun i j => raw19826step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19826step2 raw19826step1; decide +kernel
      have hl : raw19826step2Labels = raw19826step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19826step1 raw19826step1Labels permutation29 permutation4
    _ = mixedMoment B node1620 node1620Labels := by rfl

theorem canonical19827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19827 raw19827Labels = mixedMoment B node1620 node1620Labels := by
  calc
    mixedMoment B raw19827 raw19827Labels = mixedMoment B raw19827step0 raw19827step0Labels := by
      have hz : ∀ j, raw19827 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19827step0 = (fun i j => raw19827 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19827step0 raw19827; decide +kernel
      have hl : raw19827step0Labels = raw19827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19827 raw19827Labels permutation346 hz
    mixedMoment B raw19827step0 raw19827step0Labels = mixedMoment B raw19827step1 raw19827step1Labels := by
      have hz : ∀ j, raw19827step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19827step1 = (fun i j => raw19827step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19827step1 raw19827step0; decide +kernel
      have hl : raw19827step1Labels = raw19827step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19827step0 raw19827step0Labels permutation56 hz
    mixedMoment B raw19827step1 raw19827step1Labels = mixedMoment B raw19827step2 raw19827step2Labels := by
      have ha : raw19827step2 = (fun i j => raw19827step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19827step2 raw19827step1; decide +kernel
      have hl : raw19827step2Labels = raw19827step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19827step1 raw19827step1Labels permutation29 permutation4
    _ = mixedMoment B node1620 node1620Labels := by rfl

theorem canonical19828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19828 raw19828Labels = mixedMoment B node1758 node1758Labels := by
  calc
    mixedMoment B raw19828 raw19828Labels = mixedMoment B raw19828step0 raw19828step0Labels := by
      have hz : ∀ j, raw19828 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19828step0 = (fun i j => raw19828 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19828step0 raw19828; decide +kernel
      have hl : raw19828step0Labels = raw19828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19828 raw19828Labels permutation520 hz
    mixedMoment B raw19828step0 raw19828step0Labels = mixedMoment B raw19828step1 raw19828step1Labels := by
      have hz : ∀ j, raw19828step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19828step1 = (fun i j => raw19828step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19828step1 raw19828step0; decide +kernel
      have hl : raw19828step1Labels = raw19828step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19828step0 raw19828step0Labels permutation104 hz
    mixedMoment B raw19828step1 raw19828step1Labels = mixedMoment B raw19828step2 raw19828step2Labels := by
      have hz : ∀ j, raw19828step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19828step2 = (fun i j => raw19828step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19828step2 raw19828step1; decide +kernel
      have hl : raw19828step2Labels = raw19828step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19828step1 raw19828step1Labels permutation20 hz
    mixedMoment B raw19828step2 raw19828step2Labels = mixedMoment B raw19828step3 raw19828step3Labels := by
      have hz : ∀ j, raw19828step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19828step3 = (fun i j => raw19828step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19828step3 raw19828step2; decide +kernel
      have hl : raw19828step3Labels = raw19828step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19828step2 raw19828step2Labels permutation4 hz
    mixedMoment B raw19828step3 raw19828step3Labels = mixedMoment B raw19828step4 raw19828step4Labels := by
      have ha : raw19828step4 = (fun i j => raw19828step3 (permutation1 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19828step4 raw19828step3; decide +kernel
      have hl : raw19828step4Labels = raw19828step3Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19828step3 raw19828step3Labels permutation1 permutation4
    _ = mixedMoment B node1758 node1758Labels := by rfl

theorem canonical19829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19829 raw19829Labels = mixedMoment B node855 node855Labels := by
  calc
    mixedMoment B raw19829 raw19829Labels = mixedMoment B raw19829step0 raw19829step0Labels := by
      have hz : ∀ j, raw19829 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19829step0 = (fun i j => raw19829 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19829step0 raw19829; decide +kernel
      have hl : raw19829step0Labels = raw19829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19829 raw19829Labels permutation434 hz
    mixedMoment B raw19829step0 raw19829step0Labels = mixedMoment B raw19829step1 raw19829step1Labels := by
      have hz : ∀ j, raw19829step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19829step1 = (fun i j => raw19829step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19829step1 raw19829step0; decide +kernel
      have hl : raw19829step1Labels = raw19829step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19829step0 raw19829step0Labels permutation80 hz
    mixedMoment B raw19829step1 raw19829step1Labels = mixedMoment B raw19829step2 raw19829step2Labels := by
      have hz : ∀ j, raw19829step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19829step2 = (fun i j => raw19829step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19829step2 raw19829step1; decide +kernel
      have hl : raw19829step2Labels = raw19829step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19829step1 raw19829step1Labels permutation14 hz
    mixedMoment B raw19829step2 raw19829step2Labels = mixedMoment B raw19829step3 raw19829step3Labels := by
      have ha : raw19829step3 = (fun i j => raw19829step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19829step3 raw19829step2; decide +kernel
      have hl : raw19829step3Labels = raw19829step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19829step2 raw19829step2Labels permutation7 permutation4
    _ = mixedMoment B node855 node855Labels := by rfl

theorem canonical19830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19830 raw19830Labels = mixedMoment B node832 node832Labels := by
  calc
    mixedMoment B raw19830 raw19830Labels = mixedMoment B raw19830step0 raw19830step0Labels := by
      have hz : ∀ j, raw19830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19830step0 = (fun i j => raw19830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19830step0 raw19830; decide +kernel
      have hl : raw19830step0Labels = raw19830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19830 raw19830Labels permutation434 hz
    mixedMoment B raw19830step0 raw19830step0Labels = mixedMoment B raw19830step1 raw19830step1Labels := by
      have hz : ∀ j, raw19830step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19830step1 = (fun i j => raw19830step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19830step1 raw19830step0; decide +kernel
      have hl : raw19830step1Labels = raw19830step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19830step0 raw19830step0Labels permutation80 hz
    mixedMoment B raw19830step1 raw19830step1Labels = mixedMoment B raw19830step2 raw19830step2Labels := by
      have hz : ∀ j, raw19830step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19830step2 = (fun i j => raw19830step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19830step2 raw19830step1; decide +kernel
      have hl : raw19830step2Labels = raw19830step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19830step1 raw19830step1Labels permutation14 hz
    mixedMoment B raw19830step2 raw19830step2Labels = mixedMoment B raw19830step3 raw19830step3Labels := by
      have ha : raw19830step3 = (fun i j => raw19830step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19830step3 raw19830step2; decide +kernel
      have hl : raw19830step3Labels = raw19830step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19830step2 raw19830step2Labels permutation7 permutation2
    mixedMoment B raw19830step3 raw19830step3Labels = mixedMoment B raw19830step4 raw19830step4Labels := by
      have ha : raw19830step4 = -raw19830step3 := by apply Matrix.ext; change ∀ i j, raw19830step4 i j = -(raw19830step3 i j); unfold raw19830step4 raw19830step3; decide +kernel
      have hl : raw19830step4Labels = raw19830step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node832 node832Labels := by rfl

theorem canonical19831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19831 raw19831Labels = mixedMoment B node826 node826Labels := by
  calc
    mixedMoment B raw19831 raw19831Labels = mixedMoment B raw19831step0 raw19831step0Labels := by
      have hz : ∀ j, raw19831 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19831step0 = (fun i j => raw19831 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19831step0 raw19831; decide +kernel
      have hl : raw19831step0Labels = raw19831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19831 raw19831Labels permutation434 hz
    mixedMoment B raw19831step0 raw19831step0Labels = mixedMoment B raw19831step1 raw19831step1Labels := by
      have hz : ∀ j, raw19831step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19831step1 = (fun i j => raw19831step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19831step1 raw19831step0; decide +kernel
      have hl : raw19831step1Labels = raw19831step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19831step0 raw19831step0Labels permutation80 hz
    mixedMoment B raw19831step1 raw19831step1Labels = mixedMoment B raw19831step2 raw19831step2Labels := by
      have ha : raw19831step2 = (fun i j => raw19831step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19831step2 raw19831step1; decide +kernel
      have hl : raw19831step2Labels = raw19831step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19831step1 raw19831step1Labels permutation31 permutation2
    mixedMoment B raw19831step2 raw19831step2Labels = mixedMoment B raw19831step3 raw19831step3Labels := by
      have ha : raw19831step3 = -raw19831step2 := by apply Matrix.ext; change ∀ i j, raw19831step3 i j = -(raw19831step2 i j); unfold raw19831step3 raw19831step2; decide +kernel
      have hl : raw19831step3Labels = raw19831step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node826 node826Labels := by rfl

theorem canonical19832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19832 raw19832Labels = mixedMoment B node826 node826Labels := by
  calc
    mixedMoment B raw19832 raw19832Labels = mixedMoment B raw19832step0 raw19832step0Labels := by
      have hz : ∀ j, raw19832 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19832step0 = (fun i j => raw19832 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19832step0 raw19832; decide +kernel
      have hl : raw19832step0Labels = raw19832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19832 raw19832Labels permutation434 hz
    mixedMoment B raw19832step0 raw19832step0Labels = mixedMoment B raw19832step1 raw19832step1Labels := by
      have hz : ∀ j, raw19832step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19832step1 = (fun i j => raw19832step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19832step1 raw19832step0; decide +kernel
      have hl : raw19832step1Labels = raw19832step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19832step0 raw19832step0Labels permutation56 hz
    mixedMoment B raw19832step1 raw19832step1Labels = mixedMoment B raw19832step2 raw19832step2Labels := by
      have ha : raw19832step2 = (fun i j => raw19832step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19832step2 raw19832step1; decide +kernel
      have hl : raw19832step2Labels = raw19832step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19832step1 raw19832step1Labels permutation31 permutation2
    mixedMoment B raw19832step2 raw19832step2Labels = mixedMoment B raw19832step3 raw19832step3Labels := by
      have ha : raw19832step3 = -raw19832step2 := by apply Matrix.ext; change ∀ i j, raw19832step3 i j = -(raw19832step2 i j); unfold raw19832step3 raw19832step2; decide +kernel
      have hl : raw19832step3Labels = raw19832step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node826 node826Labels := by rfl

theorem canonical19833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19833 raw19833Labels = mixedMoment B node826 node826Labels := by
  calc
    mixedMoment B raw19833 raw19833Labels = mixedMoment B raw19833step0 raw19833step0Labels := by
      have hz : ∀ j, raw19833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19833step0 = (fun i j => raw19833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19833step0 raw19833; decide +kernel
      have hl : raw19833step0Labels = raw19833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19833 raw19833Labels permutation346 hz
    mixedMoment B raw19833step0 raw19833step0Labels = mixedMoment B raw19833step1 raw19833step1Labels := by
      have hz : ∀ j, raw19833step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19833step1 = (fun i j => raw19833step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19833step1 raw19833step0; decide +kernel
      have hl : raw19833step1Labels = raw19833step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19833step0 raw19833step0Labels permutation56 hz
    mixedMoment B raw19833step1 raw19833step1Labels = mixedMoment B raw19833step2 raw19833step2Labels := by
      have ha : raw19833step2 = (fun i j => raw19833step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19833step2 raw19833step1; decide +kernel
      have hl : raw19833step2Labels = raw19833step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19833step1 raw19833step1Labels permutation31 permutation2
    mixedMoment B raw19833step2 raw19833step2Labels = mixedMoment B raw19833step3 raw19833step3Labels := by
      have ha : raw19833step3 = -raw19833step2 := by apply Matrix.ext; change ∀ i j, raw19833step3 i j = -(raw19833step2 i j); unfold raw19833step3 raw19833step2; decide +kernel
      have hl : raw19833step3Labels = raw19833step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node826 node826Labels := by rfl

theorem canonical19834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19834 raw19834Labels = mixedMoment B node859 node859Labels := by
  calc
    mixedMoment B raw19834 raw19834Labels = mixedMoment B raw19834step0 raw19834step0Labels := by
      have hz : ∀ j, raw19834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19834step0 = (fun i j => raw19834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19834step0 raw19834; decide +kernel
      have hl : raw19834step0Labels = raw19834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19834 raw19834Labels permutation434 hz
    mixedMoment B raw19834step0 raw19834step0Labels = mixedMoment B raw19834step1 raw19834step1Labels := by
      have hz : ∀ j, raw19834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19834step1 = (fun i j => raw19834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19834step1 raw19834step0; decide +kernel
      have hl : raw19834step1Labels = raw19834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19834step0 raw19834step0Labels permutation80 hz
    mixedMoment B raw19834step1 raw19834step1Labels = mixedMoment B raw19834step2 raw19834step2Labels := by
      have hz : ∀ j, raw19834step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19834step2 = (fun i j => raw19834step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19834step2 raw19834step1; decide +kernel
      have hl : raw19834step2Labels = raw19834step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19834step1 raw19834step1Labels permutation14 hz
    mixedMoment B raw19834step2 raw19834step2Labels = mixedMoment B raw19834step3 raw19834step3Labels := by
      have ha : raw19834step3 = (fun i j => raw19834step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19834step3 raw19834step2; decide +kernel
      have hl : raw19834step3Labels = raw19834step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19834step2 raw19834step2Labels permutation7 permutation2
    mixedMoment B raw19834step3 raw19834step3Labels = mixedMoment B raw19834step4 raw19834step4Labels := by
      have ha : raw19834step4 = -raw19834step3 := by apply Matrix.ext; change ∀ i j, raw19834step4 i j = -(raw19834step3 i j); unfold raw19834step4 raw19834step3; decide +kernel
      have hl : raw19834step4Labels = raw19834step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node859 node859Labels := by rfl

theorem canonical19835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19835 raw19835Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw19835 raw19835Labels = mixedMoment B raw19835step0 raw19835step0Labels := by
      have hz : ∀ j, raw19835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19835step0 = (fun i j => raw19835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19835step0 raw19835; decide +kernel
      have hl : raw19835step0Labels = raw19835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19835 raw19835Labels permutation434 hz
    mixedMoment B raw19835step0 raw19835step0Labels = mixedMoment B raw19835step1 raw19835step1Labels := by
      have hz : ∀ j, raw19835step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19835step1 = (fun i j => raw19835step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19835step1 raw19835step0; decide +kernel
      have hl : raw19835step1Labels = raw19835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19835step0 raw19835step0Labels permutation80 hz
    mixedMoment B raw19835step1 raw19835step1Labels = mixedMoment B raw19835step2 raw19835step2Labels := by
      have hz : ∀ j, raw19835step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19835step2 = (fun i j => raw19835step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19835step2 raw19835step1; decide +kernel
      have hl : raw19835step2Labels = raw19835step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19835step1 raw19835step1Labels permutation14 hz
    mixedMoment B raw19835step2 raw19835step2Labels = mixedMoment B raw19835step3 raw19835step3Labels := by
      have ha : raw19835step3 = (fun i j => raw19835step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19835step3 raw19835step2; decide +kernel
      have hl : raw19835step3Labels = raw19835step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19835step2 raw19835step2Labels permutation7 permutation2
    mixedMoment B raw19835step3 raw19835step3Labels = mixedMoment B raw19835step4 raw19835step4Labels := by
      have ha : raw19835step4 = -raw19835step3 := by apply Matrix.ext; change ∀ i j, raw19835step4 i j = -(raw19835step3 i j); unfold raw19835step4 raw19835step3; decide +kernel
      have hl : raw19835step4Labels = raw19835step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1741 node1741Labels := by rfl

theorem canonical19836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19836 raw19836Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw19836 raw19836Labels = mixedMoment B raw19836step0 raw19836step0Labels := by
      have hz : ∀ j, raw19836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19836step0 = (fun i j => raw19836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19836step0 raw19836; decide +kernel
      have hl : raw19836step0Labels = raw19836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19836 raw19836Labels permutation434 hz
    mixedMoment B raw19836step0 raw19836step0Labels = mixedMoment B raw19836step1 raw19836step1Labels := by
      have hz : ∀ j, raw19836step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19836step1 = (fun i j => raw19836step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19836step1 raw19836step0; decide +kernel
      have hl : raw19836step1Labels = raw19836step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19836step0 raw19836step0Labels permutation80 hz
    mixedMoment B raw19836step1 raw19836step1Labels = mixedMoment B raw19836step2 raw19836step2Labels := by
      have hz : ∀ j, raw19836step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19836step2 = (fun i j => raw19836step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19836step2 raw19836step1; decide +kernel
      have hl : raw19836step2Labels = raw19836step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19836step1 raw19836step1Labels permutation14 hz
    mixedMoment B raw19836step2 raw19836step2Labels = mixedMoment B raw19836step3 raw19836step3Labels := by
      have ha : raw19836step3 = (fun i j => raw19836step2 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19836step3 raw19836step2; decide +kernel
      have hl : raw19836step3Labels = raw19836step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19836step2 raw19836step2Labels permutation6 permutation0
    mixedMoment B raw19836step3 raw19836step3Labels = mixedMoment B raw19836step4 raw19836step4Labels := by
      have ha : raw19836step4 = -raw19836step3 := by apply Matrix.ext; change ∀ i j, raw19836step4 i j = -(raw19836step3 i j); unfold raw19836step4 raw19836step3; decide +kernel
      have hl : raw19836step4Labels = raw19836step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4071 node4071Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5106 raw5106Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw5106 raw5106Labels = mixedMoment B raw5106step0 raw5106step0Labels := by
      have hz : ∀ j, raw5106 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5106step0 = (fun i j => raw5106 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5106step0 raw5106; decide +kernel
      have hl : raw5106step0Labels = raw5106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5106 raw5106Labels permutation434 hz
    mixedMoment B raw5106step0 raw5106step0Labels = mixedMoment B raw5106step1 raw5106step1Labels := by
      have hz : ∀ j, raw5106step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5106step1 = (fun i j => raw5106step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5106step1 raw5106step0; decide +kernel
      have hl : raw5106step1Labels = raw5106step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5106step0 raw5106step0Labels permutation80 hz
    mixedMoment B raw5106step1 raw5106step1Labels = mixedMoment B raw5106step2 raw5106step2Labels := by
      have ha : raw5106step2 = (fun i j => raw5106step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5106step2 raw5106step1; decide +kernel
      have hl : raw5106step2Labels = raw5106step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5106step1 raw5106step1Labels permutation10 permutation2
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical5111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5111 raw5111Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw5111 raw5111Labels = mixedMoment B raw5111step0 raw5111step0Labels := by
      have hz : ∀ j, raw5111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5111step0 = (fun i j => raw5111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5111step0 raw5111; decide +kernel
      have hl : raw5111step0Labels = raw5111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5111 raw5111Labels permutation434 hz
    mixedMoment B raw5111step0 raw5111step0Labels = mixedMoment B raw5111step1 raw5111step1Labels := by
      have hz : ∀ j, raw5111step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5111step1 = (fun i j => raw5111step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5111step1 raw5111step0; decide +kernel
      have hl : raw5111step1Labels = raw5111step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5111step0 raw5111step0Labels permutation56 hz
    mixedMoment B raw5111step1 raw5111step1Labels = mixedMoment B raw5111step2 raw5111step2Labels := by
      have ha : raw5111step2 = (fun i j => raw5111step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5111step2 raw5111step1; decide +kernel
      have hl : raw5111step2Labels = raw5111step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5111step1 raw5111step1Labels permutation10 permutation2
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical5116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5116 raw5116Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw5116 raw5116Labels = mixedMoment B raw5116step0 raw5116step0Labels := by
      have hz : ∀ j, raw5116 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5116step0 = (fun i j => raw5116 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5116step0 raw5116; decide +kernel
      have hl : raw5116step0Labels = raw5116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5116 raw5116Labels permutation346 hz
    mixedMoment B raw5116step0 raw5116step0Labels = mixedMoment B raw5116step1 raw5116step1Labels := by
      have hz : ∀ j, raw5116step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5116step1 = (fun i j => raw5116step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5116step1 raw5116step0; decide +kernel
      have hl : raw5116step1Labels = raw5116step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5116step0 raw5116step0Labels permutation56 hz
    mixedMoment B raw5116step1 raw5116step1Labels = mixedMoment B raw5116step2 raw5116step2Labels := by
      have ha : raw5116step2 = (fun i j => raw5116step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5116step2 raw5116step1; decide +kernel
      have hl : raw5116step2Labels = raw5116step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5116step1 raw5116step1Labels permutation10 permutation2
    _ = mixedMoment B node4605 node4605Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5121 raw5121Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw5121 raw5121Labels = mixedMoment B raw5121step0 raw5121step0Labels := by
      have hz : ∀ j, raw5121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5121step0 = (fun i j => raw5121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5121step0 raw5121; decide +kernel
      have hl : raw5121step0Labels = raw5121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5121 raw5121Labels permutation434 hz
    mixedMoment B raw5121step0 raw5121step0Labels = mixedMoment B raw5121step1 raw5121step1Labels := by
      have hz : ∀ j, raw5121step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5121step1 = (fun i j => raw5121step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5121step1 raw5121step0; decide +kernel
      have hl : raw5121step1Labels = raw5121step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5121step0 raw5121step0Labels permutation80 hz
    mixedMoment B raw5121step1 raw5121step1Labels = mixedMoment B raw5121step2 raw5121step2Labels := by
      have hz : ∀ j, raw5121step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5121step2 = (fun i j => raw5121step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5121step2 raw5121step1; decide +kernel
      have hl : raw5121step2Labels = raw5121step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5121step1 raw5121step1Labels permutation14 hz
    _ = mixedMoment B node4621 node4621Labels := by rfl

theorem canonical5127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5127 raw5127Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw5127 raw5127Labels = mixedMoment B raw5127step0 raw5127step0Labels := by
      have hz : ∀ j, raw5127 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5127step0 = (fun i j => raw5127 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5127step0 raw5127; decide +kernel
      have hl : raw5127step0Labels = raw5127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5127 raw5127Labels permutation434 hz
    mixedMoment B raw5127step0 raw5127step0Labels = mixedMoment B raw5127step1 raw5127step1Labels := by
      have hz : ∀ j, raw5127step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5127step1 = (fun i j => raw5127step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5127step1 raw5127step0; decide +kernel
      have hl : raw5127step1Labels = raw5127step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5127step0 raw5127step0Labels permutation80 hz
    mixedMoment B raw5127step1 raw5127step1Labels = mixedMoment B raw5127step2 raw5127step2Labels := by
      have ha : raw5127step2 = (fun i j => raw5127step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5127step2 raw5127step1; decide +kernel
      have hl : raw5127step2Labels = raw5127step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5127step1 raw5127step1Labels permutation31 permutation2
    mixedMoment B raw5127step2 raw5127step2Labels = mixedMoment B raw5127step3 raw5127step3Labels := by
      have ha : raw5127step3 = -raw5127step2 := by apply Matrix.ext; change ∀ i j, raw5127step3 i j = -(raw5127step2 i j); unfold raw5127step3 raw5127step2; decide +kernel
      have hl : raw5127step3Labels = raw5127step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical5128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5128 raw5128Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw5128 raw5128Labels = mixedMoment B raw5128step0 raw5128step0Labels := by
      have hz : ∀ j, raw5128 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5128step0 = (fun i j => raw5128 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5128step0 raw5128; decide +kernel
      have hl : raw5128step0Labels = raw5128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5128 raw5128Labels permutation434 hz
    mixedMoment B raw5128step0 raw5128step0Labels = mixedMoment B raw5128step1 raw5128step1Labels := by
      have hz : ∀ j, raw5128step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5128step1 = (fun i j => raw5128step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5128step1 raw5128step0; decide +kernel
      have hl : raw5128step1Labels = raw5128step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5128step0 raw5128step0Labels permutation56 hz
    mixedMoment B raw5128step1 raw5128step1Labels = mixedMoment B raw5128step2 raw5128step2Labels := by
      have ha : raw5128step2 = (fun i j => raw5128step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5128step2 raw5128step1; decide +kernel
      have hl : raw5128step2Labels = raw5128step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5128step1 raw5128step1Labels permutation31 permutation2
    mixedMoment B raw5128step2 raw5128step2Labels = mixedMoment B raw5128step3 raw5128step3Labels := by
      have ha : raw5128step3 = -raw5128step2 := by apply Matrix.ext; change ∀ i j, raw5128step3 i j = -(raw5128step2 i j); unfold raw5128step3 raw5128step2; decide +kernel
      have hl : raw5128step3Labels = raw5128step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical5129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5129 raw5129Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw5129 raw5129Labels = mixedMoment B raw5129step0 raw5129step0Labels := by
      have hz : ∀ j, raw5129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5129step0 = (fun i j => raw5129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5129step0 raw5129; decide +kernel
      have hl : raw5129step0Labels = raw5129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5129 raw5129Labels permutation346 hz
    mixedMoment B raw5129step0 raw5129step0Labels = mixedMoment B raw5129step1 raw5129step1Labels := by
      have hz : ∀ j, raw5129step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5129step1 = (fun i j => raw5129step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5129step1 raw5129step0; decide +kernel
      have hl : raw5129step1Labels = raw5129step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5129step0 raw5129step0Labels permutation56 hz
    mixedMoment B raw5129step1 raw5129step1Labels = mixedMoment B raw5129step2 raw5129step2Labels := by
      have ha : raw5129step2 = (fun i j => raw5129step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5129step2 raw5129step1; decide +kernel
      have hl : raw5129step2Labels = raw5129step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5129step1 raw5129step1Labels permutation31 permutation2
    mixedMoment B raw5129step2 raw5129step2Labels = mixedMoment B raw5129step3 raw5129step3Labels := by
      have ha : raw5129step3 = -raw5129step2 := by apply Matrix.ext; change ∀ i j, raw5129step3 i j = -(raw5129step2 i j); unfold raw5129step3 raw5129step2; decide +kernel
      have hl : raw5129step3Labels = raw5129step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical5130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5130 raw5130Labels = mixedMoment B node4505 node4505Labels := by
  calc
    mixedMoment B raw5130 raw5130Labels = mixedMoment B raw5130step0 raw5130step0Labels := by
      have hz : ∀ j, raw5130 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5130step0 = (fun i j => raw5130 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5130step0 raw5130; decide +kernel
      have hl : raw5130step0Labels = raw5130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5130 raw5130Labels permutation434 hz
    mixedMoment B raw5130step0 raw5130step0Labels = mixedMoment B raw5130step1 raw5130step1Labels := by
      have hz : ∀ j, raw5130step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5130step1 = (fun i j => raw5130step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5130step1 raw5130step0; decide +kernel
      have hl : raw5130step1Labels = raw5130step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5130step0 raw5130step0Labels permutation80 hz
    mixedMoment B raw5130step1 raw5130step1Labels = mixedMoment B raw5130step2 raw5130step2Labels := by
      have hz : ∀ j, raw5130step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5130step2 = (fun i j => raw5130step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5130step2 raw5130step1; decide +kernel
      have hl : raw5130step2Labels = raw5130step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5130step1 raw5130step1Labels permutation14 hz
    mixedMoment B raw5130step2 raw5130step2Labels = mixedMoment B raw5130step3 raw5130step3Labels := by
      have ha : raw5130step3 = (fun i j => raw5130step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5130step3 raw5130step2; decide +kernel
      have hl : raw5130step3Labels = raw5130step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5130step2 raw5130step2Labels permutation7 permutation2
    mixedMoment B raw5130step3 raw5130step3Labels = mixedMoment B raw5130step4 raw5130step4Labels := by
      have ha : raw5130step4 = -raw5130step3 := by apply Matrix.ext; change ∀ i j, raw5130step4 i j = -(raw5130step3 i j); unfold raw5130step4 raw5130step3; decide +kernel
      have hl : raw5130step4Labels = raw5130step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4505 node4505Labels := by rfl

theorem canonical5136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5136 raw5136Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw5136 raw5136Labels = mixedMoment B raw5136step0 raw5136step0Labels := by
      have hz : ∀ j, raw5136 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5136step0 = (fun i j => raw5136 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5136step0 raw5136; decide +kernel
      have hl : raw5136step0Labels = raw5136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5136 raw5136Labels permutation434 hz
    mixedMoment B raw5136step0 raw5136step0Labels = mixedMoment B raw5136step1 raw5136step1Labels := by
      have hz : ∀ j, raw5136step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5136step1 = (fun i j => raw5136step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5136step1 raw5136step0; decide +kernel
      have hl : raw5136step1Labels = raw5136step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5136step0 raw5136step0Labels permutation80 hz
    mixedMoment B raw5136step1 raw5136step1Labels = mixedMoment B raw5136step2 raw5136step2Labels := by
      have ha : raw5136step2 = (fun i j => raw5136step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5136step2 raw5136step1; decide +kernel
      have hl : raw5136step2Labels = raw5136step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5136step1 raw5136step1Labels permutation29 permutation7
    mixedMoment B raw5136step2 raw5136step2Labels = mixedMoment B raw5136step3 raw5136step3Labels := by
      have ha : raw5136step3 = raw5136step2 := by apply Matrix.ext; unfold raw5136step3 raw5136step2; decide +kernel
      have hl : raw5136step2Labels = labelEmbedding1 ∘ raw5136step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5136step2 raw5136step2Labels raw5136step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical5141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5141 raw5141Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw5141 raw5141Labels = mixedMoment B raw5141step0 raw5141step0Labels := by
      have hz : ∀ j, raw5141 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5141step0 = (fun i j => raw5141 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5141step0 raw5141; decide +kernel
      have hl : raw5141step0Labels = raw5141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5141 raw5141Labels permutation434 hz
    mixedMoment B raw5141step0 raw5141step0Labels = mixedMoment B raw5141step1 raw5141step1Labels := by
      have hz : ∀ j, raw5141step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5141step1 = (fun i j => raw5141step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5141step1 raw5141step0; decide +kernel
      have hl : raw5141step1Labels = raw5141step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5141step0 raw5141step0Labels permutation56 hz
    mixedMoment B raw5141step1 raw5141step1Labels = mixedMoment B raw5141step2 raw5141step2Labels := by
      have ha : raw5141step2 = (fun i j => raw5141step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5141step2 raw5141step1; decide +kernel
      have hl : raw5141step2Labels = raw5141step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5141step1 raw5141step1Labels permutation29 permutation7
    mixedMoment B raw5141step2 raw5141step2Labels = mixedMoment B raw5141step3 raw5141step3Labels := by
      have ha : raw5141step3 = raw5141step2 := by apply Matrix.ext; unfold raw5141step3 raw5141step2; decide +kernel
      have hl : raw5141step2Labels = labelEmbedding1 ∘ raw5141step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5141step2 raw5141step2Labels raw5141step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical5146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5146 raw5146Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw5146 raw5146Labels = mixedMoment B raw5146step0 raw5146step0Labels := by
      have hz : ∀ j, raw5146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5146step0 = (fun i j => raw5146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5146step0 raw5146; decide +kernel
      have hl : raw5146step0Labels = raw5146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5146 raw5146Labels permutation346 hz
    mixedMoment B raw5146step0 raw5146step0Labels = mixedMoment B raw5146step1 raw5146step1Labels := by
      have hz : ∀ j, raw5146step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5146step1 = (fun i j => raw5146step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5146step1 raw5146step0; decide +kernel
      have hl : raw5146step1Labels = raw5146step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5146step0 raw5146step0Labels permutation56 hz
    mixedMoment B raw5146step1 raw5146step1Labels = mixedMoment B raw5146step2 raw5146step2Labels := by
      have ha : raw5146step2 = (fun i j => raw5146step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5146step2 raw5146step1; decide +kernel
      have hl : raw5146step2Labels = raw5146step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5146step1 raw5146step1Labels permutation29 permutation7
    mixedMoment B raw5146step2 raw5146step2Labels = mixedMoment B raw5146step3 raw5146step3Labels := by
      have ha : raw5146step3 = raw5146step2 := by apply Matrix.ext; unfold raw5146step3 raw5146step2; decide +kernel
      have hl : raw5146step2Labels = labelEmbedding1 ∘ raw5146step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5146step2 raw5146step2Labels raw5146step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical5151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5151 raw5151Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw5151 raw5151Labels = mixedMoment B raw5151step0 raw5151step0Labels := by
      have hz : ∀ j, raw5151 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5151step0 = (fun i j => raw5151 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5151step0 raw5151; decide +kernel
      have hl : raw5151step0Labels = raw5151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5151 raw5151Labels permutation434 hz
    mixedMoment B raw5151step0 raw5151step0Labels = mixedMoment B raw5151step1 raw5151step1Labels := by
      have hz : ∀ j, raw5151step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5151step1 = (fun i j => raw5151step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5151step1 raw5151step0; decide +kernel
      have hl : raw5151step1Labels = raw5151step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5151step0 raw5151step0Labels permutation80 hz
    mixedMoment B raw5151step1 raw5151step1Labels = mixedMoment B raw5151step2 raw5151step2Labels := by
      have hz : ∀ j, raw5151step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5151step2 = (fun i j => raw5151step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5151step2 raw5151step1; decide +kernel
      have hl : raw5151step2Labels = raw5151step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5151step1 raw5151step1Labels permutation14 hz
    mixedMoment B raw5151step2 raw5151step2Labels = mixedMoment B raw5151step3 raw5151step3Labels := by
      have ha : raw5151step3 = (fun i j => raw5151step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5151step3 raw5151step2; decide +kernel
      have hl : raw5151step3Labels = raw5151step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5151step2 raw5151step2Labels permutation7 permutation7
    mixedMoment B raw5151step3 raw5151step3Labels = mixedMoment B raw5151step4 raw5151step4Labels := by
      have ha : raw5151step4 = raw5151step3 := by apply Matrix.ext; unfold raw5151step4 raw5151step3; decide +kernel
      have hl : raw5151step3Labels = labelEmbedding1 ∘ raw5151step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5151step3 raw5151step3Labels raw5151step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2289 node2289Labels := by rfl

theorem canonical5157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5157 raw5157Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw5157 raw5157Labels = mixedMoment B raw5157step0 raw5157step0Labels := by
      have hz : ∀ j, raw5157 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5157step0 = (fun i j => raw5157 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5157step0 raw5157; decide +kernel
      have hl : raw5157step0Labels = raw5157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5157 raw5157Labels permutation434 hz
    mixedMoment B raw5157step0 raw5157step0Labels = mixedMoment B raw5157step1 raw5157step1Labels := by
      have hz : ∀ j, raw5157step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5157step1 = (fun i j => raw5157step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5157step1 raw5157step0; decide +kernel
      have hl : raw5157step1Labels = raw5157step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5157step0 raw5157step0Labels permutation80 hz
    mixedMoment B raw5157step1 raw5157step1Labels = mixedMoment B raw5157step2 raw5157step2Labels := by
      have ha : raw5157step2 = (fun i j => raw5157step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5157step2 raw5157step1; decide +kernel
      have hl : raw5157step2Labels = raw5157step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5157step1 raw5157step1Labels permutation29 permutation7
    mixedMoment B raw5157step2 raw5157step2Labels = mixedMoment B raw5157step3 raw5157step3Labels := by
      have ha : raw5157step3 = raw5157step2 := by apply Matrix.ext; unfold raw5157step3 raw5157step2; decide +kernel
      have hl : raw5157step2Labels = labelEmbedding1 ∘ raw5157step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5157step2 raw5157step2Labels raw5157step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical5158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5158 raw5158Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw5158 raw5158Labels = mixedMoment B raw5158step0 raw5158step0Labels := by
      have hz : ∀ j, raw5158 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5158step0 = (fun i j => raw5158 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5158step0 raw5158; decide +kernel
      have hl : raw5158step0Labels = raw5158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5158 raw5158Labels permutation434 hz
    mixedMoment B raw5158step0 raw5158step0Labels = mixedMoment B raw5158step1 raw5158step1Labels := by
      have hz : ∀ j, raw5158step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5158step1 = (fun i j => raw5158step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5158step1 raw5158step0; decide +kernel
      have hl : raw5158step1Labels = raw5158step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5158step0 raw5158step0Labels permutation56 hz
    mixedMoment B raw5158step1 raw5158step1Labels = mixedMoment B raw5158step2 raw5158step2Labels := by
      have ha : raw5158step2 = (fun i j => raw5158step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5158step2 raw5158step1; decide +kernel
      have hl : raw5158step2Labels = raw5158step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5158step1 raw5158step1Labels permutation29 permutation7
    mixedMoment B raw5158step2 raw5158step2Labels = mixedMoment B raw5158step3 raw5158step3Labels := by
      have ha : raw5158step3 = raw5158step2 := by apply Matrix.ext; unfold raw5158step3 raw5158step2; decide +kernel
      have hl : raw5158step2Labels = labelEmbedding1 ∘ raw5158step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5158step2 raw5158step2Labels raw5158step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical5159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5159 raw5159Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw5159 raw5159Labels = mixedMoment B raw5159step0 raw5159step0Labels := by
      have hz : ∀ j, raw5159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5159step0 = (fun i j => raw5159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5159step0 raw5159; decide +kernel
      have hl : raw5159step0Labels = raw5159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5159 raw5159Labels permutation346 hz
    mixedMoment B raw5159step0 raw5159step0Labels = mixedMoment B raw5159step1 raw5159step1Labels := by
      have hz : ∀ j, raw5159step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5159step1 = (fun i j => raw5159step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5159step1 raw5159step0; decide +kernel
      have hl : raw5159step1Labels = raw5159step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5159step0 raw5159step0Labels permutation56 hz
    mixedMoment B raw5159step1 raw5159step1Labels = mixedMoment B raw5159step2 raw5159step2Labels := by
      have ha : raw5159step2 = (fun i j => raw5159step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5159step2 raw5159step1; decide +kernel
      have hl : raw5159step2Labels = raw5159step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5159step1 raw5159step1Labels permutation29 permutation7
    mixedMoment B raw5159step2 raw5159step2Labels = mixedMoment B raw5159step3 raw5159step3Labels := by
      have ha : raw5159step3 = raw5159step2 := by apply Matrix.ext; unfold raw5159step3 raw5159step2; decide +kernel
      have hl : raw5159step2Labels = labelEmbedding1 ∘ raw5159step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5159step2 raw5159step2Labels raw5159step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical5160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5160 raw5160Labels = mixedMoment B node1754 node1754Labels := by
  calc
    mixedMoment B raw5160 raw5160Labels = mixedMoment B raw5160step0 raw5160step0Labels := by
      have hz : ∀ j, raw5160 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5160step0 = (fun i j => raw5160 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5160step0 raw5160; decide +kernel
      have hl : raw5160step0Labels = raw5160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5160 raw5160Labels permutation434 hz
    mixedMoment B raw5160step0 raw5160step0Labels = mixedMoment B raw5160step1 raw5160step1Labels := by
      have hz : ∀ j, raw5160step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5160step1 = (fun i j => raw5160step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5160step1 raw5160step0; decide +kernel
      have hl : raw5160step1Labels = raw5160step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5160step0 raw5160step0Labels permutation80 hz
    mixedMoment B raw5160step1 raw5160step1Labels = mixedMoment B raw5160step2 raw5160step2Labels := by
      have hz : ∀ j, raw5160step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5160step2 = (fun i j => raw5160step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5160step2 raw5160step1; decide +kernel
      have hl : raw5160step2Labels = raw5160step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5160step1 raw5160step1Labels permutation14 hz
    mixedMoment B raw5160step2 raw5160step2Labels = mixedMoment B raw5160step3 raw5160step3Labels := by
      have ha : raw5160step3 = (fun i j => raw5160step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5160step3 raw5160step2; decide +kernel
      have hl : raw5160step3Labels = raw5160step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5160step2 raw5160step2Labels permutation7 permutation7
    mixedMoment B raw5160step3 raw5160step3Labels = mixedMoment B raw5160step4 raw5160step4Labels := by
      have ha : raw5160step4 = raw5160step3 := by apply Matrix.ext; unfold raw5160step4 raw5160step3; decide +kernel
      have hl : raw5160step3Labels = labelEmbedding1 ∘ raw5160step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5160step3 raw5160step3Labels raw5160step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1754 node1754Labels := by rfl

theorem canonical5162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5162 raw5162Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw5162 raw5162Labels = mixedMoment B raw5162step0 raw5162step0Labels := by
      have hz : ∀ j, raw5162 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5162step0 = (fun i j => raw5162 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5162step0 raw5162; decide +kernel
      have hl : raw5162step0Labels = raw5162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5162 raw5162Labels permutation434 hz
    mixedMoment B raw5162step0 raw5162step0Labels = mixedMoment B raw5162step1 raw5162step1Labels := by
      have hz : ∀ j, raw5162step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5162step1 = (fun i j => raw5162step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5162step1 raw5162step0; decide +kernel
      have hl : raw5162step1Labels = raw5162step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5162step0 raw5162step0Labels permutation80 hz
    mixedMoment B raw5162step1 raw5162step1Labels = mixedMoment B raw5162step2 raw5162step2Labels := by
      have ha : raw5162step2 = (fun i j => raw5162step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5162step2 raw5162step1; decide +kernel
      have hl : raw5162step2Labels = raw5162step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5162step1 raw5162step1Labels permutation10 permutation2
    _ = mixedMoment B node1239 node1239Labels := by rfl

theorem canonical5165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5165 raw5165Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw5165 raw5165Labels = mixedMoment B raw5165step0 raw5165step0Labels := by
      have hz : ∀ j, raw5165 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5165step0 = (fun i j => raw5165 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5165step0 raw5165; decide +kernel
      have hl : raw5165step0Labels = raw5165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5165 raw5165Labels permutation434 hz
    mixedMoment B raw5165step0 raw5165step0Labels = mixedMoment B raw5165step1 raw5165step1Labels := by
      have hz : ∀ j, raw5165step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5165step1 = (fun i j => raw5165step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5165step1 raw5165step0; decide +kernel
      have hl : raw5165step1Labels = raw5165step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5165step0 raw5165step0Labels permutation80 hz
    mixedMoment B raw5165step1 raw5165step1Labels = mixedMoment B raw5165step2 raw5165step2Labels := by
      have hz : ∀ j, raw5165step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5165step2 = (fun i j => raw5165step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5165step2 raw5165step1; decide +kernel
      have hl : raw5165step2Labels = raw5165step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5165step1 raw5165step1Labels permutation14 hz
    _ = mixedMoment B node1297 node1297Labels := by rfl

theorem canonical5166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5166 raw5166Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw5166 raw5166Labels = mixedMoment B raw5166step0 raw5166step0Labels := by
      have hz : ∀ j, raw5166 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5166step0 = (fun i j => raw5166 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5166step0 raw5166; decide +kernel
      have hl : raw5166step0Labels = raw5166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5166 raw5166Labels permutation434 hz
    mixedMoment B raw5166step0 raw5166step0Labels = mixedMoment B raw5166step1 raw5166step1Labels := by
      have hz : ∀ j, raw5166step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5166step1 = (fun i j => raw5166step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5166step1 raw5166step0; decide +kernel
      have hl : raw5166step1Labels = raw5166step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5166step0 raw5166step0Labels permutation80 hz
    mixedMoment B raw5166step1 raw5166step1Labels = mixedMoment B raw5166step2 raw5166step2Labels := by
      have hz : ∀ j, raw5166step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5166step2 = (fun i j => raw5166step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5166step2 raw5166step1; decide +kernel
      have hl : raw5166step2Labels = raw5166step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5166step1 raw5166step1Labels permutation14 hz
    mixedMoment B raw5166step2 raw5166step2Labels = mixedMoment B raw5166step3 raw5166step3Labels := by
      have ha : raw5166step3 = (fun i j => raw5166step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5166step3 raw5166step2; decide +kernel
      have hl : raw5166step3Labels = raw5166step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5166step2 raw5166step2Labels permutation7 permutation2
    mixedMoment B raw5166step3 raw5166step3Labels = mixedMoment B raw5166step4 raw5166step4Labels := by
      have ha : raw5166step4 = -raw5166step3 := by apply Matrix.ext; change ∀ i j, raw5166step4 i j = -(raw5166step3 i j); unfold raw5166step4 raw5166step3; decide +kernel
      have hl : raw5166step4Labels = raw5166step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1051 node1051Labels := by rfl

theorem canonical5167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5167 raw5167Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5167 raw5167Labels = mixedMoment B raw5167step0 raw5167step0Labels := by
      have hz : ∀ j, raw5167 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5167step0 = (fun i j => raw5167 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5167step0 raw5167; decide +kernel
      have hl : raw5167step0Labels = raw5167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5167 raw5167Labels permutation434 hz
    mixedMoment B raw5167step0 raw5167step0Labels = mixedMoment B raw5167step1 raw5167step1Labels := by
      have hz : ∀ j, raw5167step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5167step1 = (fun i j => raw5167step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5167step1 raw5167step0; decide +kernel
      have hl : raw5167step1Labels = raw5167step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5167step0 raw5167step0Labels permutation80 hz
    mixedMoment B raw5167step1 raw5167step1Labels = mixedMoment B raw5167step2 raw5167step2Labels := by
      have hz : ∀ j, raw5167step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5167step2 = (fun i j => raw5167step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5167step2 raw5167step1; decide +kernel
      have hl : raw5167step2Labels = raw5167step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5167step1 raw5167step1Labels permutation14 hz
    mixedMoment B raw5167step2 raw5167step2Labels = mixedMoment B raw5167step3 raw5167step3Labels := by
      have ha : raw5167step3 = (fun i j => raw5167step2 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5167step3 raw5167step2; decide +kernel
      have hl : raw5167step3Labels = raw5167step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5167step2 raw5167step2Labels permutation7 permutation0
    mixedMoment B raw5167step3 raw5167step3Labels = mixedMoment B raw5167step4 raw5167step4Labels := by
      have ha : raw5167step4 = -raw5167step3 := by apply Matrix.ext; change ∀ i j, raw5167step4 i j = -(raw5167step3 i j); unfold raw5167step4 raw5167step3; decide +kernel
      have hl : raw5167step4Labels = raw5167step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical5176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5176 raw5176Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw5176 raw5176Labels = mixedMoment B raw5176step0 raw5176step0Labels := by
      have hz : ∀ j, raw5176 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5176step0 = (fun i j => raw5176 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5176step0 raw5176; decide +kernel
      have hl : raw5176step0Labels = raw5176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5176 raw5176Labels permutation434 hz
    mixedMoment B raw5176step0 raw5176step0Labels = mixedMoment B raw5176step1 raw5176step1Labels := by
      have hz : ∀ j, raw5176step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5176step1 = (fun i j => raw5176step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5176step1 raw5176step0; decide +kernel
      have hl : raw5176step1Labels = raw5176step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5176step0 raw5176step0Labels permutation80 hz
    mixedMoment B raw5176step1 raw5176step1Labels = mixedMoment B raw5176step2 raw5176step2Labels := by
      have ha : raw5176step2 = (fun i j => raw5176step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5176step2 raw5176step1; decide +kernel
      have hl : raw5176step2Labels = raw5176step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5176step1 raw5176step1Labels permutation31 permutation2
    mixedMoment B raw5176step2 raw5176step2Labels = mixedMoment B raw5176step3 raw5176step3Labels := by
      have ha : raw5176step3 = -raw5176step2 := by apply Matrix.ext; change ∀ i j, raw5176step3 i j = -(raw5176step2 i j); unfold raw5176step3 raw5176step2; decide +kernel
      have hl : raw5176step3Labels = raw5176step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1043 node1043Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw834 raw834Labels = mixedMoment B node4187 node4187Labels := by
  calc
    mixedMoment B raw834 raw834Labels = mixedMoment B raw834step0 raw834step0Labels := by
      have ha : raw834step0 = (fun i j => raw834 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw834step0 raw834; decide +kernel
      have hl : raw834step0Labels = raw834Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw834 raw834Labels permutation2 permutation4
    mixedMoment B raw834step0 raw834step0Labels = mixedMoment B raw834step1 raw834step1Labels := by
      have ha : raw834step1 = raw834step0 := by apply Matrix.ext; unfold raw834step1 raw834step0; decide +kernel
      have hl : raw834step0Labels = labelEmbedding7 ∘ raw834step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw834step0 raw834step0Labels raw834step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4187 node4187Labels := by rfl

theorem canonical835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw835 raw835Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw835 raw835Labels = mixedMoment B raw835step0 raw835step0Labels := by
      have ha : raw835step0 = (fun i j => raw835 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw835step0 raw835; decide +kernel
      have hl : raw835step0Labels = raw835Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw835 raw835Labels permutation2 permutation4
    _ = mixedMoment B node615 node615Labels := by rfl

theorem canonical836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw836 raw836Labels = mixedMoment B node1537 node1537Labels := by
  calc
    mixedMoment B raw836 raw836Labels = mixedMoment B raw836step0 raw836step0Labels := by
      have ha : raw836step0 = (fun i j => raw836 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw836step0 raw836; decide +kernel
      have hl : raw836step0Labels = raw836Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw836 raw836Labels permutation2 permutation6
    mixedMoment B raw836step0 raw836step0Labels = mixedMoment B raw836step1 raw836step1Labels := by
      have ha : raw836step1 = -raw836step0 := by apply Matrix.ext; change ∀ i j, raw836step1 i j = -(raw836step0 i j); unfold raw836step1 raw836step0; decide +kernel
      have hl : raw836step1Labels = raw836step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw836step1 raw836step1Labels = mixedMoment B raw836step2 raw836step2Labels := by
      have ha : raw836step2 = raw836step1 := by apply Matrix.ext; unfold raw836step2 raw836step1; decide +kernel
      have hl : raw836step1Labels = labelEmbedding1 ∘ raw836step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw836step1 raw836step1Labels raw836step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1537 node1537Labels := by rfl

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

theorem canonical10259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10259 raw10259Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw10259 raw10259Labels = mixedMoment B raw10259step0 raw10259step0Labels := by
      have hz : ∀ j, raw10259 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10259step0 = (fun i j => raw10259 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10259step0 raw10259; decide +kernel
      have hl : raw10259step0Labels = raw10259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10259 raw10259Labels permutation434 hz
    mixedMoment B raw10259step0 raw10259step0Labels = mixedMoment B raw10259step1 raw10259step1Labels := by
      have hz : ∀ j, raw10259step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10259step1 = (fun i j => raw10259step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10259step1 raw10259step0; decide +kernel
      have hl : raw10259step1Labels = raw10259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10259step0 raw10259step0Labels permutation80 hz
    mixedMoment B raw10259step1 raw10259step1Labels = mixedMoment B raw10259step2 raw10259step2Labels := by
      have hz : ∀ j, raw10259step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10259step2 = (fun i j => raw10259step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10259step2 raw10259step1; decide +kernel
      have hl : raw10259step2Labels = raw10259step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10259step1 raw10259step1Labels permutation14 hz
    mixedMoment B raw10259step2 raw10259step2Labels = mixedMoment B raw10259step3 raw10259step3Labels := by
      have ha : raw10259step3 = (fun i j => raw10259step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10259step3 raw10259step2; decide +kernel
      have hl : raw10259step3Labels = raw10259step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10259step2 raw10259step2Labels permutation7 permutation2
    mixedMoment B raw10259step3 raw10259step3Labels = mixedMoment B raw10259step4 raw10259step4Labels := by
      have ha : raw10259step4 = -raw10259step3 := by apply Matrix.ext; change ∀ i j, raw10259step4 i j = -(raw10259step3 i j); unfold raw10259step4 raw10259step3; decide +kernel
      have hl : raw10259step4Labels = raw10259step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4897 node4897Labels := by rfl

theorem canonical10311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10311 raw10311Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw10311 raw10311Labels = mixedMoment B raw10311step0 raw10311step0Labels := by
      have hz : ∀ j, raw10311 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10311step0 = (fun i j => raw10311 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10311step0 raw10311; decide +kernel
      have hl : raw10311step0Labels = raw10311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10311 raw10311Labels permutation434 hz
    mixedMoment B raw10311step0 raw10311step0Labels = mixedMoment B raw10311step1 raw10311step1Labels := by
      have hz : ∀ j, raw10311step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10311step1 = (fun i j => raw10311step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10311step1 raw10311step0; decide +kernel
      have hl : raw10311step1Labels = raw10311step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10311step0 raw10311step0Labels permutation80 hz
    mixedMoment B raw10311step1 raw10311step1Labels = mixedMoment B raw10311step2 raw10311step2Labels := by
      have hz : ∀ j, raw10311step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10311step2 = (fun i j => raw10311step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10311step2 raw10311step1; decide +kernel
      have hl : raw10311step2Labels = raw10311step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10311step1 raw10311step1Labels permutation14 hz
    mixedMoment B raw10311step2 raw10311step2Labels = mixedMoment B raw10311step3 raw10311step3Labels := by
      have ha : raw10311step3 = (fun i j => raw10311step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10311step3 raw10311step2; decide +kernel
      have hl : raw10311step3Labels = raw10311step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10311step2 raw10311step2Labels permutation7 permutation7
    mixedMoment B raw10311step3 raw10311step3Labels = mixedMoment B raw10311step4 raw10311step4Labels := by
      have ha : raw10311step4 = raw10311step3 := by apply Matrix.ext; unfold raw10311step4 raw10311step3; decide +kernel
      have hl : raw10311step3Labels = labelEmbedding1 ∘ raw10311step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10311step3 raw10311step3Labels raw10311step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2292 node2292Labels := by rfl

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

theorem canonical1152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1152 raw1152Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw1152 raw1152Labels = mixedMoment B raw1152step0 raw1152step0Labels := by
      have ha : raw1152step0 = (fun i j => raw1152 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1152step0 raw1152; decide +kernel
      have hl : raw1152step0Labels = raw1152Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1152 raw1152Labels permutation8 permutation4
    mixedMoment B raw1152step0 raw1152step0Labels = mixedMoment B raw1152step1 raw1152step1Labels := by
      have ha : raw1152step1 = raw1152step0 := by apply Matrix.ext; unfold raw1152step1 raw1152step0; decide +kernel
      have hl : raw1152step0Labels = labelEmbedding7 ∘ raw1152step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1152step0 raw1152step0Labels raw1152step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4356 node4356Labels := by rfl

theorem canonical1153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1153 raw1153Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw1153 raw1153Labels = mixedMoment B raw1153step0 raw1153step0Labels := by
      have ha : raw1153step0 = (fun i j => raw1153 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1153step0 raw1153; decide +kernel
      have hl : raw1153step0Labels = raw1153Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1153 raw1153Labels permutation8 permutation4
    _ = mixedMoment B node934 node934Labels := by rfl

theorem canonical1154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1154 raw1154Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw1154 raw1154Labels = mixedMoment B raw1154step0 raw1154step0Labels := by
      have ha : raw1154step0 = (fun i j => raw1154 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1154step0 raw1154; decide +kernel
      have hl : raw1154step0Labels = raw1154Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1154 raw1154Labels permutation8 permutation6
    mixedMoment B raw1154step0 raw1154step0Labels = mixedMoment B raw1154step1 raw1154step1Labels := by
      have ha : raw1154step1 = -raw1154step0 := by apply Matrix.ext; change ∀ i j, raw1154step1 i j = -(raw1154step0 i j); unfold raw1154step1 raw1154step0; decide +kernel
      have hl : raw1154step1Labels = raw1154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1154step1 raw1154step1Labels = mixedMoment B raw1154step2 raw1154step2Labels := by
      have ha : raw1154step2 = raw1154step1 := by apply Matrix.ext; unfold raw1154step2 raw1154step1; decide +kernel
      have hl : raw1154step1Labels = labelEmbedding1 ∘ raw1154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1154step1 raw1154step1Labels raw1154step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

theorem canonical1263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1263 raw1263Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw1263 raw1263Labels = mixedMoment B raw1263step0 raw1263step0Labels := by
      have ha : raw1263step0 = (fun i j => raw1263 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1263step0 raw1263; decide +kernel
      have hl : raw1263step0Labels = raw1263Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1263 raw1263Labels permutation8 permutation4
    mixedMoment B raw1263step0 raw1263step0Labels = mixedMoment B raw1263step1 raw1263step1Labels := by
      have ha : raw1263step1 = raw1263step0 := by apply Matrix.ext; unfold raw1263step1 raw1263step0; decide +kernel
      have hl : raw1263step0Labels = labelEmbedding7 ∘ raw1263step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1263step0 raw1263step0Labels raw1263step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical1264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1264 raw1264Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw1264 raw1264Labels = mixedMoment B raw1264step0 raw1264step0Labels := by
      have ha : raw1264step0 = (fun i j => raw1264 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1264step0 raw1264; decide +kernel
      have hl : raw1264step0Labels = raw1264Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1264 raw1264Labels permutation8 permutation4
    _ = mixedMoment B node1043 node1043Labels := by rfl

theorem canonical1265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1265 raw1265Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw1265 raw1265Labels = mixedMoment B raw1265step0 raw1265step0Labels := by
      have ha : raw1265step0 = (fun i j => raw1265 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1265step0 raw1265; decide +kernel
      have hl : raw1265step0Labels = raw1265Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1265 raw1265Labels permutation10 permutation6
    mixedMoment B raw1265step0 raw1265step0Labels = mixedMoment B raw1265step1 raw1265step1Labels := by
      have ha : raw1265step1 = -raw1265step0 := by apply Matrix.ext; change ∀ i j, raw1265step1 i j = -(raw1265step0 i j); unfold raw1265step1 raw1265step0; decide +kernel
      have hl : raw1265step1Labels = raw1265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1265step1 raw1265step1Labels = mixedMoment B raw1265step2 raw1265step2Labels := by
      have ha : raw1265step2 = raw1265step1 := by apply Matrix.ext; unfold raw1265step2 raw1265step1; decide +kernel
      have hl : raw1265step1Labels = labelEmbedding1 ∘ raw1265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1265step1 raw1265step1Labels raw1265step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical1278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1278 raw1278Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw1278 raw1278Labels = mixedMoment B raw1278step0 raw1278step0Labels := by
      have ha : raw1278step0 = (fun i j => raw1278 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1278step0 raw1278; decide +kernel
      have hl : raw1278step0Labels = raw1278Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1278 raw1278Labels permutation2 permutation4
    mixedMoment B raw1278step0 raw1278step0Labels = mixedMoment B raw1278step1 raw1278step1Labels := by
      have ha : raw1278step1 = raw1278step0 := by apply Matrix.ext; unfold raw1278step1 raw1278step0; decide +kernel
      have hl : raw1278step0Labels = labelEmbedding7 ∘ raw1278step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1278step0 raw1278step0Labels raw1278step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical1279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1279 raw1279Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw1279 raw1279Labels = mixedMoment B raw1279step0 raw1279step0Labels := by
      have ha : raw1279step0 = (fun i j => raw1279 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1279step0 raw1279; decide +kernel
      have hl : raw1279step0Labels = raw1279Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1279 raw1279Labels permutation2 permutation4
    _ = mixedMoment B node1051 node1051Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4187 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4187 node4187Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node615 node615Labels + mixedMoment B node1537 node1537Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw834 singletonSmall4187
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4187) = raw834Labels := by decide +kernel
  rw [hl, canonical834 B hB] at h
  have hc0 : mixedMoment B raw834 (Fin.cases (0 : Fin 2) singletonSmall4187) =
      mixedMoment B node615 node615Labels := by
    have ha : raw834 = raw835 := by apply Matrix.ext; unfold raw834 raw835; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4187 = raw835Labels := by decide +kernel
    rw [ha, hj, canonical835 B hB]
  have hc1 : mixedMoment B raw834 (Fin.cases (1 : Fin 2) singletonSmall4187) =
      mixedMoment B node1537 node1537Labels := by
    have ha : raw834 = raw836 := by apply Matrix.ext; unfold raw834 raw836; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4187 = raw836Labels := by decide +kernel
    rw [ha, hj, canonical836 B hB]
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

theorem singleton4356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4356 node4356Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node934 node934Labels + mixedMoment B node1692 node1692Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1152 singletonSmall4356
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4356) = raw1152Labels := by decide +kernel
  rw [hl, canonical1152 B hB] at h
  have hc0 : mixedMoment B raw1152 (Fin.cases (0 : Fin 2) singletonSmall4356) =
      mixedMoment B node934 node934Labels := by
    have ha : raw1152 = raw1153 := by apply Matrix.ext; unfold raw1152 raw1153; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4356 = raw1153Labels := by decide +kernel
    rw [ha, hj, canonical1153 B hB]
  have hc1 : mixedMoment B raw1152 (Fin.cases (1 : Fin 2) singletonSmall4356) =
      mixedMoment B node1692 node1692Labels := by
    have ha : raw1152 = raw1154 := by apply Matrix.ext; unfold raw1152 raw1154; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4356 = raw1154Labels := by decide +kernel
    rw [ha, hj, canonical1154 B hB]
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

theorem singleton4460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4460 node4460Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1043 node1043Labels + mixedMoment B node1725 node1725Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1263 singletonSmall4460
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4460) = raw1263Labels := by decide +kernel
  rw [hl, canonical1263 B hB] at h
  have hc0 : mixedMoment B raw1263 (Fin.cases (0 : Fin 2) singletonSmall4460) =
      mixedMoment B node1043 node1043Labels := by
    have ha : raw1263 = raw1264 := by apply Matrix.ext; unfold raw1263 raw1264; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4460 = raw1264Labels := by decide +kernel
    rw [ha, hj, canonical1264 B hB]
  have hc1 : mixedMoment B raw1263 (Fin.cases (1 : Fin 2) singletonSmall4460) =
      mixedMoment B node1725 node1725Labels := by
    have ha : raw1263 = raw1265 := by apply Matrix.ext; unfold raw1263 raw1265; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4460 = raw1265Labels := by decide +kernel
    rw [ha, hj, canonical1265 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4468 node4468Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1051 node1051Labels + mixedMoment B node1752 node1752Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1278 singletonSmall4468
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4468) = raw1278Labels := by decide +kernel
  rw [hl, canonical1278 B hB] at h
  have hc0 : mixedMoment B raw1278 (Fin.cases (0 : Fin 2) singletonSmall4468) =
      mixedMoment B node1051 node1051Labels := by
    have ha : raw1278 = raw1279 := by apply Matrix.ext; unfold raw1278 raw1279; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4468 = raw1279Labels := by decide +kernel
    rw [ha, hj, canonical1279 B hB]
  have hc1 : mixedMoment B raw1278 (Fin.cases (1 : Fin 2) singletonSmall4468) =
      mixedMoment B node1752 node1752Labels := by
    have ha : raw1278 = raw1280 := by apply Matrix.ext; unfold raw1278 raw1280; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4468 = raw1280Labels := by decide +kernel
    rw [ha, hj, canonical1280 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4605 node4605Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1239 node1239Labels + mixedMoment B node2226 node2226Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1428 singletonSmall4605
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4605) = raw1428Labels := by decide +kernel
  rw [hl, canonical1428 B hB] at h
  have hc0 : mixedMoment B raw1428 (Fin.cases (0 : Fin 2) singletonSmall4605) =
      mixedMoment B node1239 node1239Labels := by
    have ha : raw1428 = raw1429 := by apply Matrix.ext; unfold raw1428 raw1429; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4605 = raw1429Labels := by decide +kernel
    rw [ha, hj, canonical1429 B hB]
  have hc1 : mixedMoment B raw1428 (Fin.cases (1 : Fin 2) singletonSmall4605) =
      mixedMoment B node2226 node2226Labels := by
    have ha : raw1428 = raw1430 := by apply Matrix.ext; unfold raw1428 raw1430; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4605 = raw1430Labels := by decide +kernel
    rw [ha, hj, canonical1430 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4621 node4621Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1297 node1297Labels + mixedMoment B node2289 node2289Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1446 singletonSmall4621
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4621) = raw1446Labels := by decide +kernel
  rw [hl, canonical1446 B hB] at h
  have hc0 : mixedMoment B raw1446 (Fin.cases (0 : Fin 2) singletonSmall4621) =
      mixedMoment B node1297 node1297Labels := by
    have ha : raw1446 = raw1447 := by apply Matrix.ext; unfold raw1446 raw1447; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4621 = raw1447Labels := by decide +kernel
    rw [ha, hj, canonical1447 B hB]
  have hc1 : mixedMoment B raw1446 (Fin.cases (1 : Fin 2) singletonSmall4621) =
      mixedMoment B node2289 node2289Labels := by
    have ha : raw1446 = raw1448 := by apply Matrix.ext; unfold raw1446 raw1448; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4621 = raw1448Labels := by decide +kernel
    rw [ha, hj, canonical1448 B hB]
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

theorem sound643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node643 node643Labels = Sparse.eval nodeValue643 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 643) = mixedMoment B node643 node643Labels := rfl
  simpa [nodeValue643, Sparse.eval] using hc.symm

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

theorem sound826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node826 node826Labels = Sparse.eval nodeValue826 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 826) = mixedMoment B node826 node826Labels := rfl
  simpa [nodeValue826, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero855 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node855 node855Labels = 0 := by
  exact mixedMoment_order_one B hB node855 node855Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero859 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node859 node859Labels = 0 := by
  exact mixedMoment_order_one B hB node859 node859Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node832 node832Labels = Sparse.eval nodeValue832 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 832) = mixedMoment B node832 node832Labels := rfl
  simpa [nodeValue832, Sparse.eval] using hc.symm

theorem sound855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node855 node855Labels = Sparse.eval nodeValue855 (mixedVector B) := by
  simpa only [nodeValue855, Sparse.eval_nil] using zero855 B _hB _hF

theorem sound859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node859 node859Labels = Sparse.eval nodeValue859 (mixedVector B) := by
  simpa only [nodeValue859, Sparse.eval_nil] using zero859 B _hB _hF

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

theorem sound908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node908 node908Labels = Sparse.eval nodeValue908 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 908) = mixedMoment B node908 node908Labels := rfl
  simpa [nodeValue908, Sparse.eval] using hc.symm

theorem sound934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node934 node934Labels = Sparse.eval nodeValue934 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 934) = mixedMoment B node934 node934Labels := rfl
  simpa [nodeValue934, Sparse.eval] using hc.symm

theorem sound948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node948 node948Labels = Sparse.eval nodeValue948 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 948) = mixedMoment B node948 node948Labels := rfl
  simpa [nodeValue948, Sparse.eval] using hc.symm

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

theorem sound1043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1043 node1043Labels = Sparse.eval nodeValue1043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1043) = mixedMoment B node1043 node1043Labels := rfl
  simpa [nodeValue1043, Sparse.eval] using hc.symm

theorem sound1051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1051 node1051Labels = Sparse.eval nodeValue1051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1051) = mixedMoment B node1051 node1051Labels := rfl
  simpa [nodeValue1051, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1089 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1089 node1089Labels = 0 := by
  exact mixedMoment_order_one B hB node1089 node1089Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1089 node1089Labels = Sparse.eval nodeValue1089 (mixedVector B) := by
  simpa only [nodeValue1089, Sparse.eval_nil] using zero1089 B _hB _hF

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

theorem sound1239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1239 node1239Labels = Sparse.eval nodeValue1239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1239) = mixedMoment B node1239 node1239Labels := rfl
  simpa [nodeValue1239, Sparse.eval] using hc.symm

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

theorem sound1297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1297 node1297Labels = Sparse.eval nodeValue1297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1297) = mixedMoment B node1297 node1297Labels := rfl
  simpa [nodeValue1297, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1516 node1516Labels = Sparse.eval nodeValue1516 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1516) = mixedMoment B node1516 node1516Labels := rfl
  simpa [nodeValue1516, Sparse.eval] using hc.symm

theorem sound1532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1532 node1532Labels = Sparse.eval nodeValue1532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1532) = mixedMoment B node1532 node1532Labels := rfl
  simpa [nodeValue1532, Sparse.eval] using hc.symm

theorem sound1534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1534 node1534Labels = Sparse.eval nodeValue1534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1534) = mixedMoment B node1534 node1534Labels := rfl
  simpa [nodeValue1534, Sparse.eval] using hc.symm

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

theorem sound1537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1537 node1537Labels = Sparse.eval nodeValue1537 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1537) = mixedMoment B node1537 node1537Labels := rfl
  simpa [nodeValue1537, Sparse.eval] using hc.symm

theorem sound1540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1540 node1540Labels = Sparse.eval nodeValue1540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1540) = mixedMoment B node1540 node1540Labels := rfl
  simpa [nodeValue1540, Sparse.eval] using hc.symm

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

theorem sound1620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1620 node1620Labels = Sparse.eval nodeValue1620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1620) = mixedMoment B node1620 node1620Labels := rfl
  simpa [nodeValue1620, Sparse.eval] using hc.symm

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

theorem sound1672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1672 node1672Labels = Sparse.eval nodeValue1672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1672) = mixedMoment B node1672 node1672Labels := rfl
  simpa [nodeValue1672, Sparse.eval] using hc.symm

theorem sound1692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1692 node1692Labels = Sparse.eval nodeValue1692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1692) = mixedMoment B node1692 node1692Labels := rfl
  simpa [nodeValue1692, Sparse.eval] using hc.symm

theorem sound1722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1722 node1722Labels = Sparse.eval nodeValue1722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1722) = mixedMoment B node1722 node1722Labels := rfl
  simpa [nodeValue1722, Sparse.eval] using hc.symm

theorem sound1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1725 node1725Labels = Sparse.eval nodeValue1725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1725) = mixedMoment B node1725 node1725Labels := rfl
  simpa [nodeValue1725, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1754 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1754 node1754Labels = 0 := by
  exact mixedMoment_order_one B hB node1754 node1754Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1758 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1758 node1758Labels = 0 := by
  exact mixedMoment_order_one B hB node1758 node1758Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1741 node1741Labels = Sparse.eval nodeValue1741 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1741) = mixedMoment B node1741 node1741Labels := rfl
  simpa [nodeValue1741, Sparse.eval] using hc.symm

theorem sound1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1752 node1752Labels = Sparse.eval nodeValue1752 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1752) = mixedMoment B node1752 node1752Labels := rfl
  simpa [nodeValue1752, Sparse.eval] using hc.symm

theorem sound1754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1754 node1754Labels = Sparse.eval nodeValue1754 (mixedVector B) := by
  simpa only [nodeValue1754, Sparse.eval_nil] using zero1754 B _hB _hF

theorem sound1758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1758 node1758Labels = Sparse.eval nodeValue1758 (mixedVector B) := by
  simpa only [nodeValue1758, Sparse.eval_nil] using zero1758 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2226 node2226Labels = Sparse.eval nodeValue2226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2226) = mixedMoment B node2226 node2226Labels := rfl
  simpa [nodeValue2226, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = 0 := by
  exact mixedMoment_order_one B hB node2292 node2292Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2289 node2289Labels = Sparse.eval nodeValue2289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2289) = mixedMoment B node2289 node2289Labels := rfl
  simpa [nodeValue2289, Sparse.eval] using hc.symm

theorem sound2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = Sparse.eval nodeValue2292 (mixedVector B) := by
  simpa only [nodeValue2292, Sparse.eval_nil] using zero2292 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3313 node3313Labels = Sparse.eval nodeValue3313 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3313) = mixedMoment B node3313 node3313Labels := rfl
  simpa [nodeValue3313, Sparse.eval] using hc.symm

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

theorem sound4071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4071 node4071Labels = Sparse.eval nodeValue4071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4071) = mixedMoment B node4071 node4071Labels := rfl
  simpa [nodeValue4071, Sparse.eval] using hc.symm

theorem sound4072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4072 node4072Labels = Sparse.eval nodeValue4072 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4072) = mixedMoment B node4072 node4072Labels := rfl
  simpa [nodeValue4072, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

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

theorem sound584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node584 node584Labels = Sparse.eval nodeValue584 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 584) = mixedMoment B node584 node584Labels := rfl
  simpa [nodeValue584, Sparse.eval] using hc.symm

theorem sound591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node591 node591Labels = Sparse.eval nodeValue591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 591) = mixedMoment B node591 node591Labels := rfl
  simpa [nodeValue591, Sparse.eval] using hc.symm

theorem sound615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node615 node615Labels = Sparse.eval nodeValue615 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 615) = mixedMoment B node615 node615Labels := rfl
  simpa [nodeValue615, Sparse.eval] using hc.symm

theorem sound628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node628 node628Labels = Sparse.eval nodeValue628 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 628) = mixedMoment B node628 node628Labels := rfl
  simpa [nodeValue628, Sparse.eval] using hc.symm

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

theorem sound4156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4156 node4156Labels = Sparse.eval nodeValue4156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4156) = mixedMoment B node4156 node4156Labels := rfl
  simpa [nodeValue4156, Sparse.eval] using hc.symm

theorem sound4159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4159 node4159Labels = Sparse.eval nodeValue4159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4159) = mixedMoment B node4159 node4159Labels := rfl
  simpa [nodeValue4159, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4163 node4163Labels = Sparse.eval nodeValue4163 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4163) = mixedMoment B node4163 node4163Labels := rfl
  simpa [nodeValue4163, Sparse.eval] using hc.symm

theorem sound4187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4187 node4187Labels = Sparse.eval nodeValue4187 (mixedVector B) := by
  have h := singleton4187 B _hB
  rw [sound615 B _hB _hF, sound1537 B _hB _hF] at h
  norm_num [nodeValue4187, nodeValue615, nodeValue1537, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4189 node4189Labels = Sparse.eval nodeValue4189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4189) = mixedMoment B node4189 node4189Labels := rfl
  simpa [nodeValue4189, Sparse.eval] using hc.symm

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

theorem sound4330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4330 node4330Labels = Sparse.eval nodeValue4330 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4330) = mixedMoment B node4330 node4330Labels := rfl
  simpa [nodeValue4330, Sparse.eval] using hc.symm

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

theorem sound4356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4356 node4356Labels = Sparse.eval nodeValue4356 (mixedVector B) := by
  have h := singleton4356 B _hB
  rw [sound934 B _hB _hF, sound1692 B _hB _hF] at h
  norm_num [nodeValue4356, nodeValue934, nodeValue1692, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4370 node4370Labels = Sparse.eval nodeValue4370 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4370) = mixedMoment B node4370 node4370Labels := rfl
  simpa [nodeValue4370, Sparse.eval] using hc.symm

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

theorem sound4460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4460 node4460Labels = Sparse.eval nodeValue4460 (mixedVector B) := by
  have h := singleton4460 B _hB
  rw [sound1043 B _hB _hF, sound1725 B _hB _hF] at h
  norm_num [nodeValue4460, nodeValue1043, nodeValue1725, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4468 node4468Labels = Sparse.eval nodeValue4468 (mixedVector B) := by
  have h := singleton4468 B _hB
  rw [sound1051 B _hB _hF, sound1752 B _hB _hF] at h
  norm_num [nodeValue4468, nodeValue1051, nodeValue1752, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4505 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4505 node4505Labels = 0 := by
  exact mixedMoment_order_one B hB node4505 node4505Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4512 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4512 node4512Labels = 0 := by
  exact mixedMoment_order_one B hB node4512 node4512Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4505 node4505Labels = Sparse.eval nodeValue4505 (mixedVector B) := by
  simpa only [nodeValue4505, Sparse.eval_nil] using zero4505 B _hB _hF

theorem sound4512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4512 node4512Labels = Sparse.eval nodeValue4512 (mixedVector B) := by
  simpa only [nodeValue4512, Sparse.eval_nil] using zero4512 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4594 node4594Labels = Sparse.eval nodeValue4594 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4594) = mixedMoment B node4594 node4594Labels := rfl
  simpa [nodeValue4594, Sparse.eval] using hc.symm

theorem sound4605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4605 node4605Labels = Sparse.eval nodeValue4605 (mixedVector B) := by
  have h := singleton4605 B _hB
  rw [sound1239 B _hB _hF, sound2226 B _hB _hF] at h
  norm_num [nodeValue4605, nodeValue1239, nodeValue2226, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4621 node4621Labels = Sparse.eval nodeValue4621 (mixedVector B) := by
  have h := singleton4621 B _hB
  rw [sound1297 B _hB _hF, sound2289 B _hB _hF] at h
  norm_num [nodeValue4621, nodeValue1297, nodeValue2289, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4897 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = 0 := by
  exact mixedMoment_order_one B hB node4897 node4897Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = Sparse.eval nodeValue4897 (mixedVector B) := by
  simpa only [nodeValue4897, Sparse.eval_nil] using zero4897 B _hB _hF

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

theorem sourceEq1161 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1161 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1161 + difference 0 1) (sourceB1161 + difference 1 0) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 0 1) (sourceB1161 + difference 1 0) sourceC1161) = raw19555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19555; decide +kernel
    rw [ha]
    exact (canonical19555 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1161 + difference 0 2) (sourceB1161 + difference 2 0) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 0 2) (sourceB1161 + difference 2 0) sourceC1161) = raw19556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19556; decide +kernel
    rw [ha]
    exact (canonical19556 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1161 + difference 0 3) (sourceB1161 + difference 3 0) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 0 3) (sourceB1161 + difference 3 0) sourceC1161) = raw19557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19557; decide +kernel
    rw [ha]
    exact (canonical19557 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1161 + difference 0 4) (sourceB1161 + difference 4 0) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 0 4) (sourceB1161 + difference 4 0) sourceC1161) = raw19558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19558; decide +kernel
    rw [ha]
    exact (canonical19558 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1161 + difference 0 5) (sourceB1161 + difference 5 0) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4512) := by
    have ha : (tripleCharges (sourceA1161 + difference 0 5) (sourceB1161 + difference 5 0) sourceC1161) = raw19559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19559; decide +kernel
    rw [ha]
    exact (canonical19559 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1161 + difference 1 0) (sourceB1161 + difference 0 1) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 1 0) (sourceB1161 + difference 0 1) sourceC1161) = raw19560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19560; decide +kernel
    rw [ha]
    exact (canonical19560 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1161 + difference 1 2) (sourceB1161 + difference 2 1) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 1 2) (sourceB1161 + difference 2 1) sourceC1161) = raw19561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19561; decide +kernel
    rw [ha]
    exact (canonical19561 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1161 + difference 1 3) (sourceB1161 + difference 3 1) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 1 3) (sourceB1161 + difference 3 1) sourceC1161) = raw19562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19562; decide +kernel
    rw [ha]
    exact (canonical19562 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1161 + difference 1 4) (sourceB1161 + difference 4 1) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 1 4) (sourceB1161 + difference 4 1) sourceC1161) = raw19563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19563; decide +kernel
    rw [ha]
    exact (canonical19563 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1161 + difference 1 5) (sourceB1161 + difference 5 1) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 1 5) (sourceB1161 + difference 5 1) sourceC1161) = raw19564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19564; decide +kernel
    rw [ha]
    exact (canonical19564 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1161 + difference 2 0) (sourceB1161 + difference 0 2) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 2 0) (sourceB1161 + difference 0 2) sourceC1161) = raw19565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19565; decide +kernel
    rw [ha]
    exact (canonical19565 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1161 + difference 2 1) (sourceB1161 + difference 1 2) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 2 1) (sourceB1161 + difference 1 2) sourceC1161) = raw19566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19566; decide +kernel
    rw [ha]
    exact (canonical19566 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1161 + difference 2 3) (sourceB1161 + difference 3 2) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 2 3) (sourceB1161 + difference 3 2) sourceC1161) = raw19567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19567; decide +kernel
    rw [ha]
    exact (canonical19567 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1161 + difference 2 4) (sourceB1161 + difference 4 2) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 2 4) (sourceB1161 + difference 4 2) sourceC1161) = raw19568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19568; decide +kernel
    rw [ha]
    exact (canonical19568 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1161 + difference 2 5) (sourceB1161 + difference 5 2) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 2 5) (sourceB1161 + difference 5 2) sourceC1161) = raw19569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19569; decide +kernel
    rw [ha]
    exact (canonical19569 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1161 + difference 3 0) (sourceB1161 + difference 0 3) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 3 0) (sourceB1161 + difference 0 3) sourceC1161) = raw19570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19570; decide +kernel
    rw [ha]
    exact (canonical19570 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1161 + difference 3 1) (sourceB1161 + difference 1 3) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 3 1) (sourceB1161 + difference 1 3) sourceC1161) = raw19571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19571; decide +kernel
    rw [ha]
    exact (canonical19571 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1161 + difference 3 2) (sourceB1161 + difference 2 3) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 3 2) (sourceB1161 + difference 2 3) sourceC1161) = raw19572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19572; decide +kernel
    rw [ha]
    exact (canonical19572 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1161 + difference 3 4) (sourceB1161 + difference 4 3) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 3 4) (sourceB1161 + difference 4 3) sourceC1161) = raw19573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19573; decide +kernel
    rw [ha]
    exact (canonical19573 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1161 + difference 3 5) (sourceB1161 + difference 5 3) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 3 5) (sourceB1161 + difference 5 3) sourceC1161) = raw19574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19574; decide +kernel
    rw [ha]
    exact (canonical19574 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1161 + difference 4 0) (sourceB1161 + difference 0 4) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 4 0) (sourceB1161 + difference 0 4) sourceC1161) = raw19575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19575; decide +kernel
    rw [ha]
    exact (canonical19575 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1161 + difference 4 1) (sourceB1161 + difference 1 4) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 4 1) (sourceB1161 + difference 1 4) sourceC1161) = raw19576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19576; decide +kernel
    rw [ha]
    exact (canonical19576 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1161 + difference 4 2) (sourceB1161 + difference 2 4) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 4 2) (sourceB1161 + difference 2 4) sourceC1161) = raw19577 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19577; decide +kernel
    rw [ha]
    exact (canonical19577 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1161 + difference 4 3) (sourceB1161 + difference 3 4) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 4 3) (sourceB1161 + difference 3 4) sourceC1161) = raw19578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19578; decide +kernel
    rw [ha]
    exact (canonical19578 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1161 + difference 4 5) (sourceB1161 + difference 5 4) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 4 5) (sourceB1161 + difference 5 4) sourceC1161) = raw19579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19579; decide +kernel
    rw [ha]
    exact (canonical19579 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1161 + difference 5 0) (sourceB1161 + difference 0 5) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4512) := by
    have ha : (tripleCharges (sourceA1161 + difference 5 0) (sourceB1161 + difference 0 5) sourceC1161) = raw19580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19580; decide +kernel
    rw [ha]
    exact (canonical19580 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1161 + difference 5 1) (sourceB1161 + difference 1 5) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 5 1) (sourceB1161 + difference 1 5) sourceC1161) = raw19581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19581; decide +kernel
    rw [ha]
    exact (canonical19581 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1161 + difference 5 2) (sourceB1161 + difference 2 5) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 5 2) (sourceB1161 + difference 2 5) sourceC1161) = raw19582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19582; decide +kernel
    rw [ha]
    exact (canonical19582 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1161 + difference 5 3) (sourceB1161 + difference 3 5) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 5 3) (sourceB1161 + difference 3 5) sourceC1161) = raw19583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19583; decide +kernel
    rw [ha]
    exact (canonical19583 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1161 + difference 5 4) (sourceB1161 + difference 4 5) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 5 4) (sourceB1161 + difference 4 5) sourceC1161) = raw19584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19584; decide +kernel
    rw [ha]
    exact (canonical19584 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1161 sourceB1161 sourceC1161
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1161, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1163 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1163 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1163 + difference 0 0) (sourceB1163 + difference 0 0) sourceC1163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3313) := by
    have ha : (tripleCharges (sourceA1163 + difference 0 0) (sourceB1163 + difference 0 0) sourceC1163) = raw19481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1163 sourceB1163 sourceC1163 difference raw19481; decide +kernel
    rw [ha]
    exact (canonical19481 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1163 + difference 0 1) (sourceB1163 + difference 1 0) sourceC1163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1163 + difference 0 1) (sourceB1163 + difference 1 0) sourceC1163) = raw19477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1163 sourceB1163 sourceC1163 difference raw19477; decide +kernel
    rw [ha]
    exact (canonical19477 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1163 + difference 0 2) (sourceB1163 + difference 2 0) sourceC1163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1163 + difference 0 2) (sourceB1163 + difference 2 0) sourceC1163) = raw19615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1163 sourceB1163 sourceC1163 difference raw19615; decide +kernel
    rw [ha]
    exact (canonical19615 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1163 + difference 0 3) (sourceB1163 + difference 3 0) sourceC1163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1163 + difference 0 3) (sourceB1163 + difference 3 0) sourceC1163) = raw19616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1163 sourceB1163 sourceC1163 difference raw19616; decide +kernel
    rw [ha]
    exact (canonical19616 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1163 + difference 0 4) (sourceB1163 + difference 4 0) sourceC1163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1163 + difference 0 4) (sourceB1163 + difference 4 0) sourceC1163) = raw19617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1163 sourceB1163 sourceC1163 difference raw19617; decide +kernel
    rw [ha]
    exact (canonical19617 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1163 + difference 0 5) (sourceB1163 + difference 5 0) sourceC1163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1758) := by
    have ha : (tripleCharges (sourceA1163 + difference 0 5) (sourceB1163 + difference 5 0) sourceC1163) = raw19618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1163 sourceB1163 sourceC1163 difference raw19618; decide +kernel
    rw [ha]
    exact (canonical19618 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1163 + sourceB1163) sourceC1163) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1163 + sourceB1163) sourceC1163) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1163 sourceB1163 sourceC1163 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1163 sourceB1163 sourceC1163
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1163, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1164 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1164 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1164 + difference 0 1) (sourceB1164 + difference 1 0) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1164 + difference 0 1) (sourceB1164 + difference 1 0) sourceC1164) = raw5127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw5127; decide +kernel
    rw [ha]
    exact (canonical5127 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1164 + difference 0 2) (sourceB1164 + difference 2 0) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1164 + difference 0 2) (sourceB1164 + difference 2 0) sourceC1164) = raw5128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw5128; decide +kernel
    rw [ha]
    exact (canonical5128 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1164 + difference 0 3) (sourceB1164 + difference 3 0) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1164 + difference 0 3) (sourceB1164 + difference 3 0) sourceC1164) = raw5129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw5129; decide +kernel
    rw [ha]
    exact (canonical5129 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1164 + difference 0 4) (sourceB1164 + difference 4 0) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1164 + difference 0 4) (sourceB1164 + difference 4 0) sourceC1164) = raw5130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw5130; decide +kernel
    rw [ha]
    exact (canonical5130 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1164 + difference 0 5) (sourceB1164 + difference 5 0) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA1164 + difference 0 5) (sourceB1164 + difference 5 0) sourceC1164) = raw10259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw10259; decide +kernel
    rw [ha]
    exact (canonical10259 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1164 + difference 1 0) (sourceB1164 + difference 0 1) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4159) := by
    have ha : (tripleCharges (sourceA1164 + difference 1 0) (sourceB1164 + difference 0 1) sourceC1164) = raw19619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19619; decide +kernel
    rw [ha]
    exact (canonical19619 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1164 + difference 1 2) (sourceB1164 + difference 2 1) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1164 + difference 1 2) (sourceB1164 + difference 2 1) sourceC1164) = raw19620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19620; decide +kernel
    rw [ha]
    exact (canonical19620 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1164 + difference 1 3) (sourceB1164 + difference 3 1) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1164 + difference 1 3) (sourceB1164 + difference 3 1) sourceC1164) = raw19621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19621; decide +kernel
    rw [ha]
    exact (canonical19621 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1164 + difference 1 4) (sourceB1164 + difference 4 1) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1164 + difference 1 4) (sourceB1164 + difference 4 1) sourceC1164) = raw19622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19622; decide +kernel
    rw [ha]
    exact (canonical19622 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1164 + difference 1 5) (sourceB1164 + difference 5 1) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1164 + difference 1 5) (sourceB1164 + difference 5 1) sourceC1164) = raw5106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw5106; decide +kernel
    rw [ha]
    exact (canonical5106 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1164 + difference 2 0) (sourceB1164 + difference 0 2) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4159) := by
    have ha : (tripleCharges (sourceA1164 + difference 2 0) (sourceB1164 + difference 0 2) sourceC1164) = raw19623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19623; decide +kernel
    rw [ha]
    exact (canonical19623 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1164 + difference 2 1) (sourceB1164 + difference 1 2) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1164 + difference 2 1) (sourceB1164 + difference 1 2) sourceC1164) = raw19624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19624; decide +kernel
    rw [ha]
    exact (canonical19624 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1164 + difference 2 3) (sourceB1164 + difference 3 2) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1164 + difference 2 3) (sourceB1164 + difference 3 2) sourceC1164) = raw19625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19625; decide +kernel
    rw [ha]
    exact (canonical19625 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1164 + difference 2 4) (sourceB1164 + difference 4 2) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1164 + difference 2 4) (sourceB1164 + difference 4 2) sourceC1164) = raw19626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19626; decide +kernel
    rw [ha]
    exact (canonical19626 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1164 + difference 2 5) (sourceB1164 + difference 5 2) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1164 + difference 2 5) (sourceB1164 + difference 5 2) sourceC1164) = raw5111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw5111; decide +kernel
    rw [ha]
    exact (canonical5111 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1164 + difference 3 0) (sourceB1164 + difference 0 3) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4159) := by
    have ha : (tripleCharges (sourceA1164 + difference 3 0) (sourceB1164 + difference 0 3) sourceC1164) = raw19627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19627; decide +kernel
    rw [ha]
    exact (canonical19627 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1164 + difference 3 1) (sourceB1164 + difference 1 3) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1164 + difference 3 1) (sourceB1164 + difference 1 3) sourceC1164) = raw19628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19628; decide +kernel
    rw [ha]
    exact (canonical19628 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1164 + difference 3 2) (sourceB1164 + difference 2 3) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1164 + difference 3 2) (sourceB1164 + difference 2 3) sourceC1164) = raw19629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19629; decide +kernel
    rw [ha]
    exact (canonical19629 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1164 + difference 3 4) (sourceB1164 + difference 4 3) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1164 + difference 3 4) (sourceB1164 + difference 4 3) sourceC1164) = raw19630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19630; decide +kernel
    rw [ha]
    exact (canonical19630 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1164 + difference 3 5) (sourceB1164 + difference 5 3) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1164 + difference 3 5) (sourceB1164 + difference 5 3) sourceC1164) = raw5116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw5116; decide +kernel
    rw [ha]
    exact (canonical5116 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1164 + difference 4 0) (sourceB1164 + difference 0 4) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4189) := by
    have ha : (tripleCharges (sourceA1164 + difference 4 0) (sourceB1164 + difference 0 4) sourceC1164) = raw19631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19631; decide +kernel
    rw [ha]
    exact (canonical19631 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1164 + difference 4 1) (sourceB1164 + difference 1 4) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA1164 + difference 4 1) (sourceB1164 + difference 1 4) sourceC1164) = raw19632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19632; decide +kernel
    rw [ha]
    exact (canonical19632 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1164 + difference 4 2) (sourceB1164 + difference 2 4) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA1164 + difference 4 2) (sourceB1164 + difference 2 4) sourceC1164) = raw19633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19633; decide +kernel
    rw [ha]
    exact (canonical19633 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1164 + difference 4 3) (sourceB1164 + difference 3 4) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA1164 + difference 4 3) (sourceB1164 + difference 3 4) sourceC1164) = raw19634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19634; decide +kernel
    rw [ha]
    exact (canonical19634 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1164 + difference 4 5) (sourceB1164 + difference 5 4) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA1164 + difference 4 5) (sourceB1164 + difference 5 4) sourceC1164) = raw5121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw5121; decide +kernel
    rw [ha]
    exact (canonical5121 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1164 + difference 5 0) (sourceB1164 + difference 0 5) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4163) := by
    have ha : (tripleCharges (sourceA1164 + difference 5 0) (sourceB1164 + difference 0 5) sourceC1164) = raw19635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19635; decide +kernel
    rw [ha]
    exact (canonical19635 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1164 + difference 5 1) (sourceB1164 + difference 1 5) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4156) := by
    have ha : (tripleCharges (sourceA1164 + difference 5 1) (sourceB1164 + difference 1 5) sourceC1164) = raw19636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19636; decide +kernel
    rw [ha]
    exact (canonical19636 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1164 + difference 5 2) (sourceB1164 + difference 2 5) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4156) := by
    have ha : (tripleCharges (sourceA1164 + difference 5 2) (sourceB1164 + difference 2 5) sourceC1164) = raw19637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19637; decide +kernel
    rw [ha]
    exact (canonical19637 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1164 + difference 5 3) (sourceB1164 + difference 3 5) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4156) := by
    have ha : (tripleCharges (sourceA1164 + difference 5 3) (sourceB1164 + difference 3 5) sourceC1164) = raw19638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19638; decide +kernel
    rw [ha]
    exact (canonical19638 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1164 + difference 5 4) (sourceB1164 + difference 4 5) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4187) := by
    have ha : (tripleCharges (sourceA1164 + difference 5 4) (sourceB1164 + difference 4 5) sourceC1164) = raw19639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19639; decide +kernel
    rw [ha]
    exact (canonical19639 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1164 sourceB1164 sourceC1164
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1164, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1166 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1166 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1166 + difference 0 1) (sourceB1166 + difference 1 0) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1166 + difference 0 1) (sourceB1166 + difference 1 0) sourceC1166) = raw5157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw5157; decide +kernel
    rw [ha]
    exact (canonical5157 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1166 + difference 0 2) (sourceB1166 + difference 2 0) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1166 + difference 0 2) (sourceB1166 + difference 2 0) sourceC1166) = raw5158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw5158; decide +kernel
    rw [ha]
    exact (canonical5158 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1166 + difference 0 3) (sourceB1166 + difference 3 0) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1166 + difference 0 3) (sourceB1166 + difference 3 0) sourceC1166) = raw5159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw5159; decide +kernel
    rw [ha]
    exact (canonical5159 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1166 + difference 0 4) (sourceB1166 + difference 4 0) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA1166 + difference 0 4) (sourceB1166 + difference 4 0) sourceC1166) = raw5160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw5160; decide +kernel
    rw [ha]
    exact (canonical5160 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1166 + difference 0 5) (sourceB1166 + difference 5 0) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA1166 + difference 0 5) (sourceB1166 + difference 5 0) sourceC1166) = raw10311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw10311; decide +kernel
    rw [ha]
    exact (canonical10311 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1166 + difference 1 0) (sourceB1166 + difference 0 1) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1532) := by
    have ha : (tripleCharges (sourceA1166 + difference 1 0) (sourceB1166 + difference 0 1) sourceC1166) = raw19668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19668; decide +kernel
    rw [ha]
    exact (canonical19668 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1166 + difference 1 2) (sourceB1166 + difference 2 1) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1166 + difference 1 2) (sourceB1166 + difference 2 1) sourceC1166) = raw19669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19669; decide +kernel
    rw [ha]
    exact (canonical19669 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1166 + difference 1 3) (sourceB1166 + difference 3 1) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1166 + difference 1 3) (sourceB1166 + difference 3 1) sourceC1166) = raw19670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19670; decide +kernel
    rw [ha]
    exact (canonical19670 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1166 + difference 1 4) (sourceB1166 + difference 4 1) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA1166 + difference 1 4) (sourceB1166 + difference 4 1) sourceC1166) = raw19671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19671; decide +kernel
    rw [ha]
    exact (canonical19671 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1166 + difference 1 5) (sourceB1166 + difference 5 1) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1166 + difference 1 5) (sourceB1166 + difference 5 1) sourceC1166) = raw5136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw5136; decide +kernel
    rw [ha]
    exact (canonical5136 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1166 + difference 2 0) (sourceB1166 + difference 0 2) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1532) := by
    have ha : (tripleCharges (sourceA1166 + difference 2 0) (sourceB1166 + difference 0 2) sourceC1166) = raw19672 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19672; decide +kernel
    rw [ha]
    exact (canonical19672 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1166 + difference 2 1) (sourceB1166 + difference 1 2) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1166 + difference 2 1) (sourceB1166 + difference 1 2) sourceC1166) = raw19673 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19673; decide +kernel
    rw [ha]
    exact (canonical19673 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1166 + difference 2 3) (sourceB1166 + difference 3 2) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1166 + difference 2 3) (sourceB1166 + difference 3 2) sourceC1166) = raw19674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19674; decide +kernel
    rw [ha]
    exact (canonical19674 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1166 + difference 2 4) (sourceB1166 + difference 4 2) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA1166 + difference 2 4) (sourceB1166 + difference 4 2) sourceC1166) = raw19675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19675; decide +kernel
    rw [ha]
    exact (canonical19675 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1166 + difference 2 5) (sourceB1166 + difference 5 2) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1166 + difference 2 5) (sourceB1166 + difference 5 2) sourceC1166) = raw5141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw5141; decide +kernel
    rw [ha]
    exact (canonical5141 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1166 + difference 3 0) (sourceB1166 + difference 0 3) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1532) := by
    have ha : (tripleCharges (sourceA1166 + difference 3 0) (sourceB1166 + difference 0 3) sourceC1166) = raw19676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19676; decide +kernel
    rw [ha]
    exact (canonical19676 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1166 + difference 3 1) (sourceB1166 + difference 1 3) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1166 + difference 3 1) (sourceB1166 + difference 1 3) sourceC1166) = raw19677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19677; decide +kernel
    rw [ha]
    exact (canonical19677 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1166 + difference 3 2) (sourceB1166 + difference 2 3) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1166 + difference 3 2) (sourceB1166 + difference 2 3) sourceC1166) = raw19678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19678; decide +kernel
    rw [ha]
    exact (canonical19678 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1166 + difference 3 4) (sourceB1166 + difference 4 3) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA1166 + difference 3 4) (sourceB1166 + difference 4 3) sourceC1166) = raw19679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19679; decide +kernel
    rw [ha]
    exact (canonical19679 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1166 + difference 3 5) (sourceB1166 + difference 5 3) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1166 + difference 3 5) (sourceB1166 + difference 5 3) sourceC1166) = raw5146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw5146; decide +kernel
    rw [ha]
    exact (canonical5146 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1166 + difference 4 0) (sourceB1166 + difference 0 4) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1540) := by
    have ha : (tripleCharges (sourceA1166 + difference 4 0) (sourceB1166 + difference 0 4) sourceC1166) = raw19680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19680; decide +kernel
    rw [ha]
    exact (canonical19680 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1166 + difference 4 1) (sourceB1166 + difference 1 4) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA1166 + difference 4 1) (sourceB1166 + difference 1 4) sourceC1166) = raw19681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19681; decide +kernel
    rw [ha]
    exact (canonical19681 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1166 + difference 4 2) (sourceB1166 + difference 2 4) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA1166 + difference 4 2) (sourceB1166 + difference 2 4) sourceC1166) = raw19682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19682; decide +kernel
    rw [ha]
    exact (canonical19682 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1166 + difference 4 3) (sourceB1166 + difference 3 4) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA1166 + difference 4 3) (sourceB1166 + difference 3 4) sourceC1166) = raw19683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19683; decide +kernel
    rw [ha]
    exact (canonical19683 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1166 + difference 4 5) (sourceB1166 + difference 5 4) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA1166 + difference 4 5) (sourceB1166 + difference 5 4) sourceC1166) = raw5151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw5151; decide +kernel
    rw [ha]
    exact (canonical5151 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1166 + difference 5 0) (sourceB1166 + difference 0 5) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1534) := by
    have ha : (tripleCharges (sourceA1166 + difference 5 0) (sourceB1166 + difference 0 5) sourceC1166) = raw19684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19684; decide +kernel
    rw [ha]
    exact (canonical19684 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1166 + difference 5 1) (sourceB1166 + difference 1 5) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1516) := by
    have ha : (tripleCharges (sourceA1166 + difference 5 1) (sourceB1166 + difference 1 5) sourceC1166) = raw19685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19685; decide +kernel
    rw [ha]
    exact (canonical19685 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1166 + difference 5 2) (sourceB1166 + difference 2 5) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1516) := by
    have ha : (tripleCharges (sourceA1166 + difference 5 2) (sourceB1166 + difference 2 5) sourceC1166) = raw19686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19686; decide +kernel
    rw [ha]
    exact (canonical19686 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1166 + difference 5 3) (sourceB1166 + difference 3 5) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1516) := by
    have ha : (tripleCharges (sourceA1166 + difference 5 3) (sourceB1166 + difference 3 5) sourceC1166) = raw19687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19687; decide +kernel
    rw [ha]
    exact (canonical19687 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1166 + difference 5 4) (sourceB1166 + difference 4 5) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1537) := by
    have ha : (tripleCharges (sourceA1166 + difference 5 4) (sourceB1166 + difference 4 5) sourceC1166) = raw19688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19688; decide +kernel
    rw [ha]
    exact (canonical19688 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1166 sourceB1166 sourceC1166
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1166, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1167 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1167 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1167 + difference 0 0) (sourceB1167 + difference 0 0) sourceC1167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1167 + difference 0 0) (sourceB1167 + difference 0 0) sourceC1167) = raw5166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1167 sourceB1167 sourceC1167 difference raw5166; decide +kernel
    rw [ha]
    exact (canonical5166 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1167 + difference 1 0) (sourceB1167 + difference 0 1) sourceC1167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 628) := by
    have ha : (tripleCharges (sourceA1167 + difference 1 0) (sourceB1167 + difference 0 1) sourceC1167) = raw19689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1167 sourceB1167 sourceC1167 difference raw19689; decide +kernel
    rw [ha]
    exact (canonical19689 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1167 + difference 2 0) (sourceB1167 + difference 0 2) sourceC1167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 628) := by
    have ha : (tripleCharges (sourceA1167 + difference 2 0) (sourceB1167 + difference 0 2) sourceC1167) = raw19690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1167 sourceB1167 sourceC1167 difference raw19690; decide +kernel
    rw [ha]
    exact (canonical19690 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1167 + difference 3 0) (sourceB1167 + difference 0 3) sourceC1167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 628) := by
    have ha : (tripleCharges (sourceA1167 + difference 3 0) (sourceB1167 + difference 0 3) sourceC1167) = raw19691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1167 sourceB1167 sourceC1167 difference raw19691; decide +kernel
    rw [ha]
    exact (canonical19691 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1167 + difference 4 0) (sourceB1167 + difference 0 4) sourceC1167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 643) := by
    have ha : (tripleCharges (sourceA1167 + difference 4 0) (sourceB1167 + difference 0 4) sourceC1167) = raw19692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1167 sourceB1167 sourceC1167 difference raw19692; decide +kernel
    rw [ha]
    exact (canonical19692 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1167 + difference 5 0) (sourceB1167 + difference 0 5) sourceC1167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 591) := by
    have ha : (tripleCharges (sourceA1167 + difference 5 0) (sourceB1167 + difference 0 5) sourceC1167) = raw19693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1167 sourceB1167 sourceC1167 difference raw19693; decide +kernel
    rw [ha]
    exact (canonical19693 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1167 + sourceB1167) sourceC1167) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1167 + sourceB1167) sourceC1167) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA1167 sourceB1167 sourceC1167 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1167 sourceB1167 sourceC1167
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1167, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1168 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1168 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1168 + difference 1 0) (sourceB1168 + difference 0 1) sourceC1168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 628) := by
    have ha : (tripleCharges (sourceA1168 + difference 1 0) (sourceB1168 + difference 0 1) sourceC1168) = raw19689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1168 sourceB1168 sourceC1168 difference raw19689; decide +kernel
    rw [ha]
    exact (canonical19689 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1168 + difference 1 1) (sourceB1168 + difference 1 1) sourceC1168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1168 + difference 1 1) (sourceB1168 + difference 1 1) sourceC1168) = raw5166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1168 sourceB1168 sourceC1168 difference raw5166; decide +kernel
    rw [ha]
    exact (canonical5166 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1168 + difference 1 2) (sourceB1168 + difference 2 1) sourceC1168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 908) := by
    have ha : (tripleCharges (sourceA1168 + difference 1 2) (sourceB1168 + difference 2 1) sourceC1168) = raw19694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1168 sourceB1168 sourceC1168 difference raw19694; decide +kernel
    rw [ha]
    exact (canonical19694 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1168 + difference 1 3) (sourceB1168 + difference 3 1) sourceC1168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 908) := by
    have ha : (tripleCharges (sourceA1168 + difference 1 3) (sourceB1168 + difference 3 1) sourceC1168) = raw19695 := by
      apply Matrix.ext; unfold tripleCharges sourceA1168 sourceB1168 sourceC1168 difference raw19695; decide +kernel
    rw [ha]
    exact (canonical19695 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1168 + difference 1 4) (sourceB1168 + difference 4 1) sourceC1168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1168 + difference 1 4) (sourceB1168 + difference 4 1) sourceC1168) = raw19696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1168 sourceB1168 sourceC1168 difference raw19696; decide +kernel
    rw [ha]
    exact (canonical19696 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1168 + difference 1 5) (sourceB1168 + difference 5 1) sourceC1168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1168 + difference 1 5) (sourceB1168 + difference 5 1) sourceC1168) = raw5162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1168 sourceB1168 sourceC1168 difference raw5162; decide +kernel
    rw [ha]
    exact (canonical5162 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1168 + sourceB1168) sourceC1168) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1168 + sourceB1168) sourceC1168) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA1168 sourceB1168 sourceC1168 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1168 sourceB1168 sourceC1168
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1168, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1169 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1169 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1169 + difference 0 1) (sourceB1169 + difference 1 0) sourceC1169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1169 + difference 0 1) (sourceB1169 + difference 1 0) sourceC1169) = raw5176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1169 sourceB1169 sourceC1169 difference raw5176; decide +kernel
    rw [ha]
    exact (canonical5176 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1169 + difference 1 1) (sourceB1169 + difference 1 1) sourceC1169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1169 + difference 1 1) (sourceB1169 + difference 1 1) sourceC1169) = raw5166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1169 sourceB1169 sourceC1169 difference raw5166; decide +kernel
    rw [ha]
    exact (canonical5166 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1169 + difference 2 1) (sourceB1169 + difference 1 2) sourceC1169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 908) := by
    have ha : (tripleCharges (sourceA1169 + difference 2 1) (sourceB1169 + difference 1 2) sourceC1169) = raw19697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1169 sourceB1169 sourceC1169 difference raw19697; decide +kernel
    rw [ha]
    exact (canonical19697 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1169 + difference 3 1) (sourceB1169 + difference 1 3) sourceC1169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 908) := by
    have ha : (tripleCharges (sourceA1169 + difference 3 1) (sourceB1169 + difference 1 3) sourceC1169) = raw19698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1169 sourceB1169 sourceC1169 difference raw19698; decide +kernel
    rw [ha]
    exact (canonical19698 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1169 + difference 4 1) (sourceB1169 + difference 1 4) sourceC1169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 948) := by
    have ha : (tripleCharges (sourceA1169 + difference 4 1) (sourceB1169 + difference 1 4) sourceC1169) = raw19699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1169 sourceB1169 sourceC1169 difference raw19699; decide +kernel
    rw [ha]
    exact (canonical19699 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1169 + difference 5 1) (sourceB1169 + difference 1 5) sourceC1169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 584) := by
    have ha : (tripleCharges (sourceA1169 + difference 5 1) (sourceB1169 + difference 1 5) sourceC1169) = raw19700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1169 sourceB1169 sourceC1169 difference raw19700; decide +kernel
    rw [ha]
    exact (canonical19700 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1169 + sourceB1169) sourceC1169) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1169 + sourceB1169) sourceC1169) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA1169 sourceB1169 sourceC1169 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1169 sourceB1169 sourceC1169
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1169, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1170 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1170 + difference 4 0) (sourceB1170 + difference 0 4) sourceC1170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 643) := by
    have ha : (tripleCharges (sourceA1170 + difference 4 0) (sourceB1170 + difference 0 4) sourceC1170) = raw19692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1170 sourceB1170 sourceC1170 difference raw19692; decide +kernel
    rw [ha]
    exact (canonical19692 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1170 + difference 4 1) (sourceB1170 + difference 1 4) sourceC1170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 948) := by
    have ha : (tripleCharges (sourceA1170 + difference 4 1) (sourceB1170 + difference 1 4) sourceC1170) = raw19699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1170 sourceB1170 sourceC1170 difference raw19699; decide +kernel
    rw [ha]
    exact (canonical19699 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1170 + difference 4 2) (sourceB1170 + difference 2 4) sourceC1170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 948) := by
    have ha : (tripleCharges (sourceA1170 + difference 4 2) (sourceB1170 + difference 2 4) sourceC1170) = raw19701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1170 sourceB1170 sourceC1170 difference raw19701; decide +kernel
    rw [ha]
    exact (canonical19701 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1170 + difference 4 3) (sourceB1170 + difference 3 4) sourceC1170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 948) := by
    have ha : (tripleCharges (sourceA1170 + difference 4 3) (sourceB1170 + difference 3 4) sourceC1170) = raw19702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1170 sourceB1170 sourceC1170 difference raw19702; decide +kernel
    rw [ha]
    exact (canonical19702 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1170 + difference 4 4) (sourceB1170 + difference 4 4) sourceC1170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1170 + difference 4 4) (sourceB1170 + difference 4 4) sourceC1170) = raw5166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1170 sourceB1170 sourceC1170 difference raw5166; decide +kernel
    rw [ha]
    exact (canonical5166 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1170 + difference 4 5) (sourceB1170 + difference 5 4) sourceC1170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA1170 + difference 4 5) (sourceB1170 + difference 5 4) sourceC1170) = raw5165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1170 sourceB1170 sourceC1170 difference raw5165; decide +kernel
    rw [ha]
    exact (canonical5165 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1170 + sourceB1170) sourceC1170) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1170 + sourceB1170) sourceC1170) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA1170 sourceB1170 sourceC1170 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1170 sourceB1170 sourceC1170
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1170, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1171 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1171 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1171 + difference 0 4) (sourceB1171 + difference 4 0) sourceC1171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1089) := by
    have ha : (tripleCharges (sourceA1171 + difference 0 4) (sourceB1171 + difference 4 0) sourceC1171) = raw19703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1171 sourceB1171 sourceC1171 difference raw19703; decide +kernel
    rw [ha]
    exact (canonical19703 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1171 + difference 1 4) (sourceB1171 + difference 4 1) sourceC1171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1171 + difference 1 4) (sourceB1171 + difference 4 1) sourceC1171) = raw19696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1171 sourceB1171 sourceC1171 difference raw19696; decide +kernel
    rw [ha]
    exact (canonical19696 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1171 + difference 2 4) (sourceB1171 + difference 4 2) sourceC1171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1171 + difference 2 4) (sourceB1171 + difference 4 2) sourceC1171) = raw19704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1171 sourceB1171 sourceC1171 difference raw19704; decide +kernel
    rw [ha]
    exact (canonical19704 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1171 + difference 3 4) (sourceB1171 + difference 4 3) sourceC1171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1171 + difference 3 4) (sourceB1171 + difference 4 3) sourceC1171) = raw19705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1171 sourceB1171 sourceC1171 difference raw19705; decide +kernel
    rw [ha]
    exact (canonical19705 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1171 + difference 4 4) (sourceB1171 + difference 4 4) sourceC1171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1171 + difference 4 4) (sourceB1171 + difference 4 4) sourceC1171) = raw5166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1171 sourceB1171 sourceC1171 difference raw5166; decide +kernel
    rw [ha]
    exact (canonical5166 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1171 + difference 5 4) (sourceB1171 + difference 4 5) sourceC1171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 615) := by
    have ha : (tripleCharges (sourceA1171 + difference 5 4) (sourceB1171 + difference 4 5) sourceC1171) = raw19706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1171 sourceB1171 sourceC1171 difference raw19706; decide +kernel
    rw [ha]
    exact (canonical19706 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1171 + sourceB1171) sourceC1171) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1171 + sourceB1171) sourceC1171) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA1171 sourceB1171 sourceC1171 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1171 sourceB1171 sourceC1171
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1171, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1177 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1177 + difference 0 0) (sourceB1177 + difference 0 0) sourceC1177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1177 + difference 0 0) (sourceB1177 + difference 0 0) sourceC1177) = raw19824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1177 sourceB1177 sourceC1177 difference raw19824; decide +kernel
    rw [ha]
    exact (canonical19824 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1177 + difference 1 0) (sourceB1177 + difference 0 1) sourceC1177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1620) := by
    have ha : (tripleCharges (sourceA1177 + difference 1 0) (sourceB1177 + difference 0 1) sourceC1177) = raw19825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1177 sourceB1177 sourceC1177 difference raw19825; decide +kernel
    rw [ha]
    exact (canonical19825 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1177 + difference 2 0) (sourceB1177 + difference 0 2) sourceC1177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1620) := by
    have ha : (tripleCharges (sourceA1177 + difference 2 0) (sourceB1177 + difference 0 2) sourceC1177) = raw19826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1177 sourceB1177 sourceC1177 difference raw19826; decide +kernel
    rw [ha]
    exact (canonical19826 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1177 + difference 3 0) (sourceB1177 + difference 0 3) sourceC1177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1620) := by
    have ha : (tripleCharges (sourceA1177 + difference 3 0) (sourceB1177 + difference 0 3) sourceC1177) = raw19827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1177 sourceB1177 sourceC1177 difference raw19827; decide +kernel
    rw [ha]
    exact (canonical19827 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1177 + difference 4 0) (sourceB1177 + difference 0 4) sourceC1177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1758) := by
    have ha : (tripleCharges (sourceA1177 + difference 4 0) (sourceB1177 + difference 0 4) sourceC1177) = raw19828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1177 sourceB1177 sourceC1177 difference raw19828; decide +kernel
    rw [ha]
    exact (canonical19828 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1177 + difference 5 0) (sourceB1177 + difference 0 5) sourceC1177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 855) := by
    have ha : (tripleCharges (sourceA1177 + difference 5 0) (sourceB1177 + difference 0 5) sourceC1177) = raw19829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1177 sourceB1177 sourceC1177 difference raw19829; decide +kernel
    rw [ha]
    exact (canonical19829 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1177 + sourceB1177) sourceC1177) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1177 + sourceB1177) sourceC1177) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1177 sourceB1177 sourceC1177 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1177 sourceB1177 sourceC1177
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1177, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1178 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1178 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1178 + difference 0 0) (sourceB1178 + difference 0 0) sourceC1178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 832) := by
    have ha : (tripleCharges (sourceA1178 + difference 0 0) (sourceB1178 + difference 0 0) sourceC1178) = raw19830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1178 sourceB1178 sourceC1178 difference raw19830; decide +kernel
    rw [ha]
    exact (canonical19830 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1178 + difference 0 1) (sourceB1178 + difference 1 0) sourceC1178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 826) := by
    have ha : (tripleCharges (sourceA1178 + difference 0 1) (sourceB1178 + difference 1 0) sourceC1178) = raw19831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1178 sourceB1178 sourceC1178 difference raw19831; decide +kernel
    rw [ha]
    exact (canonical19831 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1178 + difference 0 2) (sourceB1178 + difference 2 0) sourceC1178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 826) := by
    have ha : (tripleCharges (sourceA1178 + difference 0 2) (sourceB1178 + difference 2 0) sourceC1178) = raw19832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1178 sourceB1178 sourceC1178 difference raw19832; decide +kernel
    rw [ha]
    exact (canonical19832 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1178 + difference 0 3) (sourceB1178 + difference 3 0) sourceC1178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 826) := by
    have ha : (tripleCharges (sourceA1178 + difference 0 3) (sourceB1178 + difference 3 0) sourceC1178) = raw19833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1178 sourceB1178 sourceC1178 difference raw19833; decide +kernel
    rw [ha]
    exact (canonical19833 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1178 + difference 0 4) (sourceB1178 + difference 4 0) sourceC1178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 859) := by
    have ha : (tripleCharges (sourceA1178 + difference 0 4) (sourceB1178 + difference 4 0) sourceC1178) = raw19834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1178 sourceB1178 sourceC1178 difference raw19834; decide +kernel
    rw [ha]
    exact (canonical19834 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1178 + difference 0 5) (sourceB1178 + difference 5 0) sourceC1178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1178 + difference 0 5) (sourceB1178 + difference 5 0) sourceC1178) = raw19835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1178 sourceB1178 sourceC1178 difference raw19835; decide +kernel
    rw [ha]
    exact (canonical19835 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1178 + sourceB1178) sourceC1178) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1178 + sourceB1178) sourceC1178) = raw19836 := by
      apply Matrix.ext; unfold doubleCharges sourceA1178 sourceB1178 sourceC1178 raw19836; decide +kernel
    rw [ha]
    exact (canonical19836 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1178 sourceB1178 sourceC1178
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1178, Integer.Sparse.eval]
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

theorem reindexCheck1009 : Integer.Sparse.reindex keyMap MixedData.row1009 = numericRow1009 := by decide +kernel

theorem numericCheck1009 (x : Master → ℝ) : Integer.Sparse.eval numericRow1009 x =
    (1 : ℝ) * reducedSource1009 x := by
  norm_num [numericRow1009, reducedSource1009, Integer.Sparse.eval, Sparse.eval, nodeValue4468, nodeValue4512, nodeValue4594] <;> ring

theorem reindexCheck1011 : Integer.Sparse.reindex keyMap MixedData.row1011 = numericRow1011 := by decide +kernel

theorem numericCheck1011 (x : Master → ℝ) : Integer.Sparse.eval numericRow1011 x =
    (1 : ℝ) * reducedSource1011 x := by
  norm_num [numericRow1011, reducedSource1011, Integer.Sparse.eval, Sparse.eval, nodeValue1752, nodeValue1758, nodeValue3313, nodeValue4072]

theorem reindexCheck1012 : Integer.Sparse.reindex keyMap MixedData.row1012 = numericRow1012 := by decide +kernel

theorem numericCheck1012 (x : Master → ℝ) : Integer.Sparse.eval numericRow1012 x =
    (4 : ℝ) * reducedSource1012 x := by
  norm_num [numericRow1012, reducedSource1012, Integer.Sparse.eval, Sparse.eval, nodeValue4156, nodeValue4159, nodeValue4163, nodeValue4187, nodeValue4189, nodeValue4330, nodeValue4356, nodeValue4370, nodeValue4460, nodeValue4505, nodeValue4605, nodeValue4621, nodeValue4897] <;> ring

theorem reindexCheck1014 : Integer.Sparse.reindex keyMap MixedData.row1014 = numericRow1014 := by decide +kernel

theorem numericCheck1014 (x : Master → ℝ) : Integer.Sparse.eval numericRow1014 x =
    (1 : ℝ) * reducedSource1014 x := by
  norm_num [numericRow1014, reducedSource1014, Integer.Sparse.eval, Sparse.eval, nodeValue1516, nodeValue1532, nodeValue1534, nodeValue1537, nodeValue1540, nodeValue1672, nodeValue1692, nodeValue1722, nodeValue1725, nodeValue1754, nodeValue2226, nodeValue2289, nodeValue2292]

theorem reindexCheck1015 : Integer.Sparse.reindex keyMap MixedData.row1015 = numericRow1015 := by decide +kernel

theorem numericCheck1015 (x : Master → ℝ) : Integer.Sparse.eval numericRow1015 x =
    (1 : ℝ) * reducedSource1015 x := by
  norm_num [numericRow1015, reducedSource1015, Integer.Sparse.eval, Sparse.eval, nodeValue591, nodeValue628, nodeValue643, nodeValue1051, nodeValue4084]

theorem reindexCheck1016 : Integer.Sparse.reindex keyMap MixedData.row1016 = numericRow1016 := by decide +kernel

theorem numericCheck1016 (x : Master → ℝ) : Integer.Sparse.eval numericRow1016 x =
    (1 : ℝ) * reducedSource1016 x := by
  norm_num [numericRow1016, reducedSource1016, Integer.Sparse.eval, Sparse.eval, nodeValue628, nodeValue908, nodeValue934, nodeValue1051, nodeValue1239, nodeValue4084]

theorem reindexCheck1017 : Integer.Sparse.reindex keyMap MixedData.row1017 = numericRow1017 := by decide +kernel

theorem numericCheck1017 (x : Master → ℝ) : Integer.Sparse.eval numericRow1017 x =
    (1 : ℝ) * reducedSource1017 x := by
  norm_num [numericRow1017, reducedSource1017, Integer.Sparse.eval, Sparse.eval, nodeValue584, nodeValue908, nodeValue948, nodeValue1043, nodeValue1051, nodeValue4084]

theorem reindexCheck1018 : Integer.Sparse.reindex keyMap MixedData.row1018 = numericRow1018 := by decide +kernel

theorem numericCheck1018 (x : Master → ℝ) : Integer.Sparse.eval numericRow1018 x =
    (1 : ℝ) * reducedSource1018 x := by
  norm_num [numericRow1018, reducedSource1018, Integer.Sparse.eval, Sparse.eval, nodeValue643, nodeValue948, nodeValue1051, nodeValue1297, nodeValue4084]

theorem reindexCheck1019 : Integer.Sparse.reindex keyMap MixedData.row1019 = numericRow1019 := by decide +kernel

theorem numericCheck1019 (x : Master → ℝ) : Integer.Sparse.eval numericRow1019 x =
    (1 : ℝ) * reducedSource1019 x := by
  norm_num [numericRow1019, reducedSource1019, Integer.Sparse.eval, Sparse.eval, nodeValue615, nodeValue934, nodeValue1051, nodeValue1089, nodeValue4084]

theorem reindexCheck1022 : Integer.Sparse.reindex keyMap MixedData.row1022 = numericRow1022 := by decide +kernel

theorem numericCheck1022 (x : Master → ℝ) : Integer.Sparse.eval numericRow1022 x =
    (1 : ℝ) * reducedSource1022 x := by
  norm_num [numericRow1022, reducedSource1022, Integer.Sparse.eval, Sparse.eval, nodeValue855, nodeValue1620, nodeValue1752, nodeValue1758, nodeValue4072]

theorem reindexCheck1023 : Integer.Sparse.reindex keyMap MixedData.row1023 = numericRow1023 := by decide +kernel

theorem numericCheck1023 (x : Master → ℝ) : Integer.Sparse.eval numericRow1023 x =
    (1 : ℝ) * reducedSource1023 x := by
  norm_num [numericRow1023, reducedSource1023, Integer.Sparse.eval, Sparse.eval, nodeValue826, nodeValue832, nodeValue859, nodeValue1741, nodeValue4071]

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

theorem reducedZero1009 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1009 (mixedVector B) = 0 := by
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4512 : mixedVector B (Sum.inr 4512) = Sparse.eval nodeValue4512 (mixedVector B) := by
    change mixedMoment B node4512 node4512Labels = _
    exact sound4512 B hB hF
  have h4594 : mixedVector B (Sum.inr 4594) = Sparse.eval nodeValue4594 (mixedVector B) := by
    change mixedMoment B node4594 node4594Labels = _
    exact sound4594 B hB hF
  simpa only [sourceForm1161, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4468, h4512, h4594, reducedSource1009] using sourceEq1161 B hB

theorem rowSound1009 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1009 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1009, numericCheck1009, reducedZero1009 B hB hF, mul_zero]

theorem reducedZero1011 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1011 (mixedVector B) = 0 := by
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h1758 : mixedVector B (Sum.inr 1758) = Sparse.eval nodeValue1758 (mixedVector B) := by
    change mixedMoment B node1758 node1758Labels = _
    exact sound1758 B hB hF
  have h3313 : mixedVector B (Sum.inr 3313) = Sparse.eval nodeValue3313 (mixedVector B) := by
    change mixedMoment B node3313 node3313Labels = _
    exact sound3313 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  simpa only [sourceForm1163, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1752, h1758, h3313, h4072, reducedSource1011] using sourceEq1163 B hB

theorem rowSound1011 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1011 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1011, numericCheck1011, reducedZero1011 B hB hF, mul_zero]

theorem reducedZero1012 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1012 (mixedVector B) = 0 := by
  have h4156 : mixedVector B (Sum.inr 4156) = Sparse.eval nodeValue4156 (mixedVector B) := by
    change mixedMoment B node4156 node4156Labels = _
    exact sound4156 B hB hF
  have h4159 : mixedVector B (Sum.inr 4159) = Sparse.eval nodeValue4159 (mixedVector B) := by
    change mixedMoment B node4159 node4159Labels = _
    exact sound4159 B hB hF
  have h4163 : mixedVector B (Sum.inr 4163) = Sparse.eval nodeValue4163 (mixedVector B) := by
    change mixedMoment B node4163 node4163Labels = _
    exact sound4163 B hB hF
  have h4187 : mixedVector B (Sum.inr 4187) = Sparse.eval nodeValue4187 (mixedVector B) := by
    change mixedMoment B node4187 node4187Labels = _
    exact sound4187 B hB hF
  have h4189 : mixedVector B (Sum.inr 4189) = Sparse.eval nodeValue4189 (mixedVector B) := by
    change mixedMoment B node4189 node4189Labels = _
    exact sound4189 B hB hF
  have h4330 : mixedVector B (Sum.inr 4330) = Sparse.eval nodeValue4330 (mixedVector B) := by
    change mixedMoment B node4330 node4330Labels = _
    exact sound4330 B hB hF
  have h4356 : mixedVector B (Sum.inr 4356) = Sparse.eval nodeValue4356 (mixedVector B) := by
    change mixedMoment B node4356 node4356Labels = _
    exact sound4356 B hB hF
  have h4370 : mixedVector B (Sum.inr 4370) = Sparse.eval nodeValue4370 (mixedVector B) := by
    change mixedMoment B node4370 node4370Labels = _
    exact sound4370 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4505 : mixedVector B (Sum.inr 4505) = Sparse.eval nodeValue4505 (mixedVector B) := by
    change mixedMoment B node4505 node4505Labels = _
    exact sound4505 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4621 : mixedVector B (Sum.inr 4621) = Sparse.eval nodeValue4621 (mixedVector B) := by
    change mixedMoment B node4621 node4621Labels = _
    exact sound4621 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  simpa only [sourceForm1164, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4156, h4159, h4163, h4187, h4189, h4330, h4356, h4370, h4460, h4505, h4605, h4621, h4897, reducedSource1012] using sourceEq1164 B hB

theorem rowSound1012 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1012 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1012, numericCheck1012, reducedZero1012 B hB hF, mul_zero]

theorem reducedZero1014 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1014 (mixedVector B) = 0 := by
  have h1516 : mixedVector B (Sum.inr 1516) = Sparse.eval nodeValue1516 (mixedVector B) := by
    change mixedMoment B node1516 node1516Labels = _
    exact sound1516 B hB hF
  have h1532 : mixedVector B (Sum.inr 1532) = Sparse.eval nodeValue1532 (mixedVector B) := by
    change mixedMoment B node1532 node1532Labels = _
    exact sound1532 B hB hF
  have h1534 : mixedVector B (Sum.inr 1534) = Sparse.eval nodeValue1534 (mixedVector B) := by
    change mixedMoment B node1534 node1534Labels = _
    exact sound1534 B hB hF
  have h1537 : mixedVector B (Sum.inr 1537) = Sparse.eval nodeValue1537 (mixedVector B) := by
    change mixedMoment B node1537 node1537Labels = _
    exact sound1537 B hB hF
  have h1540 : mixedVector B (Sum.inr 1540) = Sparse.eval nodeValue1540 (mixedVector B) := by
    change mixedMoment B node1540 node1540Labels = _
    exact sound1540 B hB hF
  have h1672 : mixedVector B (Sum.inr 1672) = Sparse.eval nodeValue1672 (mixedVector B) := by
    change mixedMoment B node1672 node1672Labels = _
    exact sound1672 B hB hF
  have h1692 : mixedVector B (Sum.inr 1692) = Sparse.eval nodeValue1692 (mixedVector B) := by
    change mixedMoment B node1692 node1692Labels = _
    exact sound1692 B hB hF
  have h1722 : mixedVector B (Sum.inr 1722) = Sparse.eval nodeValue1722 (mixedVector B) := by
    change mixedMoment B node1722 node1722Labels = _
    exact sound1722 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  simpa only [sourceForm1166, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1516, h1532, h1534, h1537, h1540, h1672, h1692, h1722, h1725, h1754, h2226, h2289, h2292, reducedSource1014] using sourceEq1166 B hB

theorem rowSound1014 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1014 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1014, numericCheck1014, reducedZero1014 B hB hF, mul_zero]

theorem reducedZero1015 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1015 (mixedVector B) = 0 := by
  have h591 : mixedVector B (Sum.inr 591) = Sparse.eval nodeValue591 (mixedVector B) := by
    change mixedMoment B node591 node591Labels = _
    exact sound591 B hB hF
  have h628 : mixedVector B (Sum.inr 628) = Sparse.eval nodeValue628 (mixedVector B) := by
    change mixedMoment B node628 node628Labels = _
    exact sound628 B hB hF
  have h643 : mixedVector B (Sum.inr 643) = Sparse.eval nodeValue643 (mixedVector B) := by
    change mixedMoment B node643 node643Labels = _
    exact sound643 B hB hF
  have h1051 : mixedVector B (Sum.inr 1051) = Sparse.eval nodeValue1051 (mixedVector B) := by
    change mixedMoment B node1051 node1051Labels = _
    exact sound1051 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1167, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h591, h628, h643, h1051, h4084, reducedSource1015] using sourceEq1167 B hB

theorem rowSound1015 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1015 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1015, numericCheck1015, reducedZero1015 B hB hF, mul_zero]

theorem reducedZero1016 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1016 (mixedVector B) = 0 := by
  have h628 : mixedVector B (Sum.inr 628) = Sparse.eval nodeValue628 (mixedVector B) := by
    change mixedMoment B node628 node628Labels = _
    exact sound628 B hB hF
  have h908 : mixedVector B (Sum.inr 908) = Sparse.eval nodeValue908 (mixedVector B) := by
    change mixedMoment B node908 node908Labels = _
    exact sound908 B hB hF
  have h934 : mixedVector B (Sum.inr 934) = Sparse.eval nodeValue934 (mixedVector B) := by
    change mixedMoment B node934 node934Labels = _
    exact sound934 B hB hF
  have h1051 : mixedVector B (Sum.inr 1051) = Sparse.eval nodeValue1051 (mixedVector B) := by
    change mixedMoment B node1051 node1051Labels = _
    exact sound1051 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1168, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h628, h908, h934, h1051, h1239, h4084, reducedSource1016] using sourceEq1168 B hB

theorem rowSound1016 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1016 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1016, numericCheck1016, reducedZero1016 B hB hF, mul_zero]

theorem reducedZero1017 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1017 (mixedVector B) = 0 := by
  have h584 : mixedVector B (Sum.inr 584) = Sparse.eval nodeValue584 (mixedVector B) := by
    change mixedMoment B node584 node584Labels = _
    exact sound584 B hB hF
  have h908 : mixedVector B (Sum.inr 908) = Sparse.eval nodeValue908 (mixedVector B) := by
    change mixedMoment B node908 node908Labels = _
    exact sound908 B hB hF
  have h948 : mixedVector B (Sum.inr 948) = Sparse.eval nodeValue948 (mixedVector B) := by
    change mixedMoment B node948 node948Labels = _
    exact sound948 B hB hF
  have h1043 : mixedVector B (Sum.inr 1043) = Sparse.eval nodeValue1043 (mixedVector B) := by
    change mixedMoment B node1043 node1043Labels = _
    exact sound1043 B hB hF
  have h1051 : mixedVector B (Sum.inr 1051) = Sparse.eval nodeValue1051 (mixedVector B) := by
    change mixedMoment B node1051 node1051Labels = _
    exact sound1051 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1169, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h584, h908, h948, h1043, h1051, h4084, reducedSource1017] using sourceEq1169 B hB

theorem rowSound1017 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1017 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1017, numericCheck1017, reducedZero1017 B hB hF, mul_zero]

theorem reducedZero1018 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1018 (mixedVector B) = 0 := by
  have h643 : mixedVector B (Sum.inr 643) = Sparse.eval nodeValue643 (mixedVector B) := by
    change mixedMoment B node643 node643Labels = _
    exact sound643 B hB hF
  have h948 : mixedVector B (Sum.inr 948) = Sparse.eval nodeValue948 (mixedVector B) := by
    change mixedMoment B node948 node948Labels = _
    exact sound948 B hB hF
  have h1051 : mixedVector B (Sum.inr 1051) = Sparse.eval nodeValue1051 (mixedVector B) := by
    change mixedMoment B node1051 node1051Labels = _
    exact sound1051 B hB hF
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1170, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h643, h948, h1051, h1297, h4084, reducedSource1018] using sourceEq1170 B hB

theorem rowSound1018 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1018 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1018, numericCheck1018, reducedZero1018 B hB hF, mul_zero]

theorem reducedZero1019 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1019 (mixedVector B) = 0 := by
  have h615 : mixedVector B (Sum.inr 615) = Sparse.eval nodeValue615 (mixedVector B) := by
    change mixedMoment B node615 node615Labels = _
    exact sound615 B hB hF
  have h934 : mixedVector B (Sum.inr 934) = Sparse.eval nodeValue934 (mixedVector B) := by
    change mixedMoment B node934 node934Labels = _
    exact sound934 B hB hF
  have h1051 : mixedVector B (Sum.inr 1051) = Sparse.eval nodeValue1051 (mixedVector B) := by
    change mixedMoment B node1051 node1051Labels = _
    exact sound1051 B hB hF
  have h1089 : mixedVector B (Sum.inr 1089) = Sparse.eval nodeValue1089 (mixedVector B) := by
    change mixedMoment B node1089 node1089Labels = _
    exact sound1089 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1171, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h615, h934, h1051, h1089, h4084, reducedSource1019] using sourceEq1171 B hB

theorem rowSound1019 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1019 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1019, numericCheck1019, reducedZero1019 B hB hF, mul_zero]

theorem reducedZero1022 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1022 (mixedVector B) = 0 := by
  have h855 : mixedVector B (Sum.inr 855) = Sparse.eval nodeValue855 (mixedVector B) := by
    change mixedMoment B node855 node855Labels = _
    exact sound855 B hB hF
  have h1620 : mixedVector B (Sum.inr 1620) = Sparse.eval nodeValue1620 (mixedVector B) := by
    change mixedMoment B node1620 node1620Labels = _
    exact sound1620 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h1758 : mixedVector B (Sum.inr 1758) = Sparse.eval nodeValue1758 (mixedVector B) := by
    change mixedMoment B node1758 node1758Labels = _
    exact sound1758 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  simpa only [sourceForm1177, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h855, h1620, h1752, h1758, h4072, reducedSource1022] using sourceEq1177 B hB

theorem rowSound1022 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1022 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1022, numericCheck1022, reducedZero1022 B hB hF, mul_zero]

theorem reducedZero1023 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1023 (mixedVector B) = 0 := by
  have h826 : mixedVector B (Sum.inr 826) = Sparse.eval nodeValue826 (mixedVector B) := by
    change mixedMoment B node826 node826Labels = _
    exact sound826 B hB hF
  have h832 : mixedVector B (Sum.inr 832) = Sparse.eval nodeValue832 (mixedVector B) := by
    change mixedMoment B node832 node832Labels = _
    exact sound832 B hB hF
  have h859 : mixedVector B (Sum.inr 859) = Sparse.eval nodeValue859 (mixedVector B) := by
    change mixedMoment B node859 node859Labels = _
    exact sound859 B hB hF
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1178, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h826, h832, h859, h1741, h4071, reducedSource1023] using sourceEq1178 B hB

theorem rowSound1023 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1023 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1023, numericCheck1023, reducedZero1023 B hB hF, mul_zero]

theorem sourceRowsAt1008 : MixedData.sourceRows (1008 : Fin 2425) =
    MixedData.row1008 := by decide +kernel

theorem sourceRowsAt1009 : MixedData.sourceRows (1009 : Fin 2425) =
    MixedData.row1009 := by decide +kernel

theorem sourceRowsAt1010 : MixedData.sourceRows (1010 : Fin 2425) =
    MixedData.row1010 := by decide +kernel

theorem sourceRowsAt1011 : MixedData.sourceRows (1011 : Fin 2425) =
    MixedData.row1011 := by decide +kernel

theorem sourceRowsAt1012 : MixedData.sourceRows (1012 : Fin 2425) =
    MixedData.row1012 := by decide +kernel

theorem sourceRowsAt1013 : MixedData.sourceRows (1013 : Fin 2425) =
    MixedData.row1013 := by decide +kernel

theorem sourceRowsAt1014 : MixedData.sourceRows (1014 : Fin 2425) =
    MixedData.row1014 := by decide +kernel

theorem sourceRowsAt1015 : MixedData.sourceRows (1015 : Fin 2425) =
    MixedData.row1015 := by decide +kernel

theorem sourceRowsAt1016 : MixedData.sourceRows (1016 : Fin 2425) =
    MixedData.row1016 := by decide +kernel

theorem sourceRowsAt1017 : MixedData.sourceRows (1017 : Fin 2425) =
    MixedData.row1017 := by decide +kernel

theorem sourceRowsAt1018 : MixedData.sourceRows (1018 : Fin 2425) =
    MixedData.row1018 := by decide +kernel

theorem sourceRowsAt1019 : MixedData.sourceRows (1019 : Fin 2425) =
    MixedData.row1019 := by decide +kernel

theorem sourceRowsAt1020 : MixedData.sourceRows (1020 : Fin 2425) =
    MixedData.row1020 := by decide +kernel

theorem sourceRowsAt1021 : MixedData.sourceRows (1021 : Fin 2425) =
    MixedData.row1021 := by decide +kernel

theorem sourceRowsAt1022 : MixedData.sourceRows (1022 : Fin 2425) =
    MixedData.row1022 := by decide +kernel

theorem sourceRowsAt1023 : MixedData.sourceRows (1023 : Fin 2425) =
    MixedData.row1023 := by decide +kernel

theorem chunkSound63_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 63) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1008 ∨ k.val = 1009 ∨ k.val = 1010 ∨ k.val = 1011 ∨ k.val = 1012 ∨ k.val = 1013 ∨ k.val = 1014 ∨ k.val = 1015 ∨ k.val = 1016 ∨ k.val = 1017 ∨ k.val = 1018 ∨ k.val = 1019 ∨ k.val = 1020 ∨ k.val = 1021 ∨ k.val = 1022 ∨ k.val = 1023 := by omega
  rcases heq with h1008 | h1009 | h1010 | h1011 | h1012 | h1013 | h1014 | h1015 | h1016 | h1017 | h1018 | h1019 | h1020 | h1021 | h1022 | h1023
  · have he : k = (1008 : Fin 2425) := Fin.ext h1008
    subst k
    rw [sourceRowsAt1008]
    exact rowSound1008_e B hB hF
  · have he : k = (1009 : Fin 2425) := Fin.ext h1009
    subst k
    rw [sourceRowsAt1009]
    exact rowSound1009 B hB hF
  · have he : k = (1010 : Fin 2425) := Fin.ext h1010
    subst k
    rw [sourceRowsAt1010]
    exact rowSound1010_e B hB hF
  · have he : k = (1011 : Fin 2425) := Fin.ext h1011
    subst k
    rw [sourceRowsAt1011]
    exact rowSound1011 B hB hF
  · have he : k = (1012 : Fin 2425) := Fin.ext h1012
    subst k
    rw [sourceRowsAt1012]
    exact rowSound1012 B hB hF
  · have he : k = (1013 : Fin 2425) := Fin.ext h1013
    subst k
    rw [sourceRowsAt1013]
    exact rowSound1013_e B hB hF
  · have he : k = (1014 : Fin 2425) := Fin.ext h1014
    subst k
    rw [sourceRowsAt1014]
    exact rowSound1014 B hB hF
  · have he : k = (1015 : Fin 2425) := Fin.ext h1015
    subst k
    rw [sourceRowsAt1015]
    exact rowSound1015 B hB hF
  · have he : k = (1016 : Fin 2425) := Fin.ext h1016
    subst k
    rw [sourceRowsAt1016]
    exact rowSound1016 B hB hF
  · have he : k = (1017 : Fin 2425) := Fin.ext h1017
    subst k
    rw [sourceRowsAt1017]
    exact rowSound1017 B hB hF
  · have he : k = (1018 : Fin 2425) := Fin.ext h1018
    subst k
    rw [sourceRowsAt1018]
    exact rowSound1018 B hB hF
  · have he : k = (1019 : Fin 2425) := Fin.ext h1019
    subst k
    rw [sourceRowsAt1019]
    exact rowSound1019 B hB hF
  · have he : k = (1020 : Fin 2425) := Fin.ext h1020
    subst k
    rw [sourceRowsAt1020]
    exact rowSound1020_e B hB hF
  · have he : k = (1021 : Fin 2425) := Fin.ext h1021
    subst k
    rw [sourceRowsAt1021]
    exact rowSound1021_e B hB hF
  · have he : k = (1022 : Fin 2425) := Fin.ext h1022
    subst k
    rw [sourceRowsAt1022]
    exact rowSound1022 B hB hF
  · have he : k = (1023 : Fin 2425) := Fin.ext h1023
    subst k
    rw [sourceRowsAt1023]
    exact rowSound1023 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound63_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound63_e_oai
