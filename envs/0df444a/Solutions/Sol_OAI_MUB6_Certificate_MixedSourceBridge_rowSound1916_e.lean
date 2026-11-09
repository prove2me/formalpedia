-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:16:41.007296+00:00
-- url     : https://prove2.me/submissions/fee275a4-32a0-4a72-bb04-375e020e3acd

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E106
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5172_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5174_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5416_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5418_e
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

theorem canonical246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw246 raw246Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw246 raw246Labels = mixedMoment B raw246step0 raw246step0Labels := by
      have ha : raw246step0 = (fun i j => raw246 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw246step0 raw246; decide +kernel
      have hl : raw246step0Labels = raw246Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw246 raw246Labels permutation8 permutation5
    mixedMoment B raw246step0 raw246step0Labels = mixedMoment B raw246step1 raw246step1Labels := by
      have ha : raw246step1 = raw246step0 := by apply Matrix.ext; unfold raw246step1 raw246step0; decide +kernel
      have hl : raw246step0Labels = labelEmbedding1 ∘ raw246step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw246step0 raw246step0Labels raw246step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2604 node2604Labels := by rfl

theorem canonical247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw247 raw247Labels = mixedMoment B node343 node343Labels := by
  calc
    mixedMoment B raw247 raw247Labels = mixedMoment B raw247step0 raw247step0Labels := by
      have ha : raw247step0 = (fun i j => raw247 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw247step0 raw247; decide +kernel
      have hl : raw247step0Labels = raw247Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw247 raw247Labels permutation8 permutation5
    _ = mixedMoment B node343 node343Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical13579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13579 raw13579Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw13579 raw13579Labels = mixedMoment B raw13579step0 raw13579step0Labels := by
      have ha : raw13579step0 = (fun i j => raw13579 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13579step0 raw13579; decide +kernel
      have hl : raw13579step0Labels = raw13579Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13579 raw13579Labels permutation170 permutation3
    mixedMoment B raw13579step0 raw13579step0Labels = mixedMoment B raw13579step1 raw13579step1Labels := by
      have ha : raw13579step1 = raw13579step0 := by apply Matrix.ext; unfold raw13579step1 raw13579step0; decide +kernel
      have hl : raw13579step0Labels = labelEmbedding6 ∘ raw13579step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13579step0 raw13579step0Labels raw13579step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5162 node5162Labels := by rfl

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

theorem canonical13591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13591 raw13591Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw13591 raw13591Labels = mixedMoment B raw13591step0 raw13591step0Labels := by
      have hz : ∀ j, raw13591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13591step0 = (fun i j => raw13591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13591step0 raw13591; decide +kernel
      have hl : raw13591step0Labels = raw13591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13591 raw13591Labels permutation346 hz
    mixedMoment B raw13591step0 raw13591step0Labels = mixedMoment B raw13591step1 raw13591step1Labels := by
      have ha : raw13591step1 = (fun i j => raw13591step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13591step1 raw13591step0; decide +kernel
      have hl : raw13591step1Labels = raw13591step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13591step0 raw13591step0Labels permutation32 permutation3
    mixedMoment B raw13591step1 raw13591step1Labels = mixedMoment B raw13591step2 raw13591step2Labels := by
      have ha : raw13591step2 = raw13591step1 := by apply Matrix.ext; unfold raw13591step2 raw13591step1; decide +kernel
      have hl : raw13591step1Labels = labelEmbedding6 ∘ raw13591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13591step1 raw13591step1Labels raw13591step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

theorem canonical13593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13593 raw13593Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw13593 raw13593Labels = mixedMoment B raw13593step0 raw13593step0Labels := by
      have ha : raw13593step0 = (fun i j => raw13593 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13593step0 raw13593; decide +kernel
      have hl : raw13593step0Labels = raw13593Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13593 raw13593Labels permutation176 permutation3
    mixedMoment B raw13593step0 raw13593step0Labels = mixedMoment B raw13593step1 raw13593step1Labels := by
      have ha : raw13593step1 = raw13593step0 := by apply Matrix.ext; unfold raw13593step1 raw13593step0; decide +kernel
      have hl : raw13593step0Labels = labelEmbedding6 ∘ raw13593step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13593step0 raw13593step0Labels raw13593step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5076 node5076Labels := by rfl

theorem canonical13594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13594 raw13594Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw13594 raw13594Labels = mixedMoment B raw13594step0 raw13594step0Labels := by
      have hz : ∀ j, raw13594 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13594step0 = (fun i j => raw13594 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13594step0 raw13594; decide +kernel
      have hl : raw13594step0Labels = raw13594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13594 raw13594Labels permutation520 hz
    mixedMoment B raw13594step0 raw13594step0Labels = mixedMoment B raw13594step1 raw13594step1Labels := by
      have hz : ∀ j, raw13594step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw13594step1 = (fun i j => raw13594step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw13594step1 raw13594step0; decide +kernel
      have hl : raw13594step1Labels = raw13594step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13594step0 raw13594step0Labels permutation80 hz
    mixedMoment B raw13594step1 raw13594step1Labels = mixedMoment B raw13594step2 raw13594step2Labels := by
      have ha : raw13594step2 = (fun i j => raw13594step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13594step2 raw13594step1; decide +kernel
      have hl : raw13594step2Labels = raw13594step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13594step1 raw13594step1Labels permutation8 permutation3
    mixedMoment B raw13594step2 raw13594step2Labels = mixedMoment B raw13594step3 raw13594step3Labels := by
      have ha : raw13594step3 = raw13594step2 := by apply Matrix.ext; unfold raw13594step3 raw13594step2; decide +kernel
      have hl : raw13594step2Labels = labelEmbedding6 ∘ raw13594step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13594step2 raw13594step2Labels raw13594step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

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

theorem canonical17691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17691 raw17691Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw17691 raw17691Labels = mixedMoment B raw17691step0 raw17691step0Labels := by
      have hz : ∀ j, raw17691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17691step0 = (fun i j => raw17691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17691step0 raw17691; decide +kernel
      have hl : raw17691step0Labels = raw17691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17691 raw17691Labels permutation346 hz
    mixedMoment B raw17691step0 raw17691step0Labels = mixedMoment B raw17691step1 raw17691step1Labels := by
      have ha : raw17691step1 = (fun i j => raw17691step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17691step1 raw17691step0; decide +kernel
      have hl : raw17691step1Labels = raw17691step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17691step0 raw17691step0Labels permutation144 permutation2
    mixedMoment B raw17691step1 raw17691step1Labels = mixedMoment B raw17691step2 raw17691step2Labels := by
      have ha : raw17691step2 = -raw17691step1 := by apply Matrix.ext; change ∀ i j, raw17691step2 i j = -(raw17691step1 i j); unfold raw17691step2 raw17691step1; decide +kernel
      have hl : raw17691step2Labels = raw17691step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5418 node5418Labels := by rfl

theorem canonical17692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17692 raw17692Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw17692 raw17692Labels = mixedMoment B raw17692step0 raw17692step0Labels := by
      have ha : raw17692step0 = (fun i j => raw17692 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17692step0 raw17692; decide +kernel
      have hl : raw17692step0Labels = raw17692Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17692 raw17692Labels permutation664 permutation2
    mixedMoment B raw17692step0 raw17692step0Labels = mixedMoment B raw17692step1 raw17692step1Labels := by
      have ha : raw17692step1 = -raw17692step0 := by apply Matrix.ext; change ∀ i j, raw17692step1 i j = -(raw17692step0 i j); unfold raw17692step1 raw17692step0; decide +kernel
      have hl : raw17692step1Labels = raw17692step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5416 node5416Labels := by rfl

theorem canonical17693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17693 raw17693Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw17693 raw17693Labels = mixedMoment B raw17693step0 raw17693step0Labels := by
      have hz : ∀ j, raw17693 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17693step0 = (fun i j => raw17693 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17693step0 raw17693; decide +kernel
      have hl : raw17693step0Labels = raw17693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17693 raw17693Labels permutation520 hz
    mixedMoment B raw17693step0 raw17693step0Labels = mixedMoment B raw17693step1 raw17693step1Labels := by
      have hz : ∀ j, raw17693step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17693step1 = (fun i j => raw17693step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17693step1 raw17693step0; decide +kernel
      have hl : raw17693step1Labels = raw17693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17693step0 raw17693step0Labels permutation80 hz
    mixedMoment B raw17693step1 raw17693step1Labels = mixedMoment B raw17693step2 raw17693step2Labels := by
      have ha : raw17693step2 = (fun i j => raw17693step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17693step2 raw17693step1; decide +kernel
      have hl : raw17693step2Labels = raw17693step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17693step1 raw17693step1Labels permutation31 permutation2
    mixedMoment B raw17693step2 raw17693step2Labels = mixedMoment B raw17693step3 raw17693step3Labels := by
      have ha : raw17693step3 = -raw17693step2 := by apply Matrix.ext; change ∀ i j, raw17693step3 i j = -(raw17693step2 i j); unfold raw17693step3 raw17693step2; decide +kernel
      have hl : raw17693step3Labels = raw17693step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5442 node5442Labels := by rfl

theorem canonical17694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17694 raw17694Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw17694 raw17694Labels = mixedMoment B raw17694step0 raw17694step0Labels := by
      have hz : ∀ j, raw17694 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17694step0 = (fun i j => raw17694 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17694step0 raw17694; decide +kernel
      have hl : raw17694step0Labels = raw17694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17694 raw17694Labels permutation434 hz
    mixedMoment B raw17694step0 raw17694step0Labels = mixedMoment B raw17694step1 raw17694step1Labels := by
      have hz : ∀ j, raw17694step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17694step1 = (fun i j => raw17694step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17694step1 raw17694step0; decide +kernel
      have hl : raw17694step1Labels = raw17694step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17694step0 raw17694step0Labels permutation80 hz
    mixedMoment B raw17694step1 raw17694step1Labels = mixedMoment B raw17694step2 raw17694step2Labels := by
      have ha : raw17694step2 = (fun i j => raw17694step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17694step2 raw17694step1; decide +kernel
      have hl : raw17694step2Labels = raw17694step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17694step1 raw17694step1Labels permutation9 permutation3
    mixedMoment B raw17694step2 raw17694step2Labels = mixedMoment B raw17694step3 raw17694step3Labels := by
      have ha : raw17694step3 = raw17694step2 := by apply Matrix.ext; unfold raw17694step3 raw17694step2; decide +kernel
      have hl : raw17694step2Labels = labelEmbedding6 ∘ raw17694step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17694step2 raw17694step2Labels raw17694step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

theorem canonical17698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17698 raw17698Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw17698 raw17698Labels = mixedMoment B raw17698step0 raw17698step0Labels := by
      have hz : ∀ j, raw17698 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17698step0 = (fun i j => raw17698 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17698step0 raw17698; decide +kernel
      have hl : raw17698step0Labels = raw17698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17698 raw17698Labels permutation434 hz
    mixedMoment B raw17698step0 raw17698step0Labels = mixedMoment B raw17698step1 raw17698step1Labels := by
      have hz : ∀ j, raw17698step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17698step1 = (fun i j => raw17698step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17698step1 raw17698step0; decide +kernel
      have hl : raw17698step1Labels = raw17698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17698step0 raw17698step0Labels permutation80 hz
    mixedMoment B raw17698step1 raw17698step1Labels = mixedMoment B raw17698step2 raw17698step2Labels := by
      have ha : raw17698step2 = (fun i j => raw17698step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17698step2 raw17698step1; decide +kernel
      have hl : raw17698step2Labels = raw17698step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17698step1 raw17698step1Labels permutation31 permutation2
    mixedMoment B raw17698step2 raw17698step2Labels = mixedMoment B raw17698step3 raw17698step3Labels := by
      have ha : raw17698step3 = -raw17698step2 := by apply Matrix.ext; change ∀ i j, raw17698step3 i j = -(raw17698step2 i j); unfold raw17698step3 raw17698step2; decide +kernel
      have hl : raw17698step3Labels = raw17698step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5174 node5174Labels := by rfl

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

theorem canonical1917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1917 raw1917Labels = mixedMoment B node4948 node4948Labels := by
  calc
    mixedMoment B raw1917 raw1917Labels = mixedMoment B raw1917step0 raw1917step0Labels := by
      have ha : raw1917step0 = (fun i j => raw1917 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1917step0 raw1917; decide +kernel
      have hl : raw1917step0Labels = raw1917Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1917 raw1917Labels permutation32 permutation4
    mixedMoment B raw1917step0 raw1917step0Labels = mixedMoment B raw1917step1 raw1917step1Labels := by
      have ha : raw1917step1 = raw1917step0 := by apply Matrix.ext; unfold raw1917step1 raw1917step0; decide +kernel
      have hl : raw1917step0Labels = labelEmbedding7 ∘ raw1917step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1917step0 raw1917step0Labels raw1917step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4948 node4948Labels := by rfl

theorem canonical1918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1918 raw1918Labels = mixedMoment B node2339 node2339Labels := by
  calc
    mixedMoment B raw1918 raw1918Labels = mixedMoment B raw1918step0 raw1918step0Labels := by
      have ha : raw1918step0 = (fun i j => raw1918 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1918step0 raw1918; decide +kernel
      have hl : raw1918step0Labels = raw1918Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1918 raw1918Labels permutation32 permutation4
    _ = mixedMoment B node2339 node2339Labels := by rfl

theorem canonical1919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1919 raw1919Labels = mixedMoment B node3420 node3420Labels := by
  calc
    mixedMoment B raw1919 raw1919Labels = mixedMoment B raw1919step0 raw1919step0Labels := by
      have ha : raw1919step0 = (fun i j => raw1919 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1919step0 raw1919; decide +kernel
      have hl : raw1919step0Labels = raw1919Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1919 raw1919Labels permutation32 permutation6
    mixedMoment B raw1919step0 raw1919step0Labels = mixedMoment B raw1919step1 raw1919step1Labels := by
      have ha : raw1919step1 = -raw1919step0 := by apply Matrix.ext; change ∀ i j, raw1919step1 i j = -(raw1919step0 i j); unfold raw1919step1 raw1919step0; decide +kernel
      have hl : raw1919step1Labels = raw1919step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1919step1 raw1919step1Labels = mixedMoment B raw1919step2 raw1919step2Labels := by
      have ha : raw1919step2 = raw1919step1 := by apply Matrix.ext; unfold raw1919step2 raw1919step1; decide +kernel
      have hl : raw1919step1Labels = labelEmbedding1 ∘ raw1919step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1919step1 raw1919step1Labels raw1919step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3420 node3420Labels := by rfl

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

theorem canonical1920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1920 raw1920Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw1920 raw1920Labels = mixedMoment B raw1920step0 raw1920step0Labels := by
      have ha : raw1920step0 = (fun i j => raw1920 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1920step0 raw1920; decide +kernel
      have hl : raw1920step0Labels = raw1920Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1920 raw1920Labels permutation32 permutation4
    mixedMoment B raw1920step0 raw1920step0Labels = mixedMoment B raw1920step1 raw1920step1Labels := by
      have ha : raw1920step1 = raw1920step0 := by apply Matrix.ext; unfold raw1920step1 raw1920step0; decide +kernel
      have hl : raw1920step0Labels = labelEmbedding7 ∘ raw1920step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1920step0 raw1920step0Labels raw1920step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

theorem canonical1921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1921 raw1921Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw1921 raw1921Labels = mixedMoment B raw1921step0 raw1921step0Labels := by
      have ha : raw1921step0 = (fun i j => raw1921 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1921step0 raw1921; decide +kernel
      have hl : raw1921step0Labels = raw1921Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1921 raw1921Labels permutation32 permutation4
    _ = mixedMoment B node2341 node2341Labels := by rfl

theorem canonical1922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1922 raw1922Labels = mixedMoment B node3417 node3417Labels := by
  calc
    mixedMoment B raw1922 raw1922Labels = mixedMoment B raw1922step0 raw1922step0Labels := by
      have ha : raw1922step0 = (fun i j => raw1922 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1922step0 raw1922; decide +kernel
      have hl : raw1922step0Labels = raw1922Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1922 raw1922Labels permutation34 permutation6
    mixedMoment B raw1922step0 raw1922step0Labels = mixedMoment B raw1922step1 raw1922step1Labels := by
      have ha : raw1922step1 = -raw1922step0 := by apply Matrix.ext; change ∀ i j, raw1922step1 i j = -(raw1922step0 i j); unfold raw1922step1 raw1922step0; decide +kernel
      have hl : raw1922step1Labels = raw1922step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1922step1 raw1922step1Labels = mixedMoment B raw1922step2 raw1922step2Labels := by
      have ha : raw1922step2 = raw1922step1 := by apply Matrix.ext; unfold raw1922step2 raw1922step1; decide +kernel
      have hl : raw1922step1Labels = labelEmbedding1 ∘ raw1922step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1922step1 raw1922step1Labels raw1922step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3417 node3417Labels := by rfl

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

theorem canonical2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2058 raw2058Labels = mixedMoment B node5037 node5037Labels := by
  calc
    mixedMoment B raw2058 raw2058Labels = mixedMoment B raw2058step0 raw2058step0Labels := by
      have ha : raw2058step0 = (fun i j => raw2058 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2058step0 raw2058; decide +kernel
      have hl : raw2058step0Labels = raw2058Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2058 raw2058Labels permutation152 permutation4
    mixedMoment B raw2058step0 raw2058step0Labels = mixedMoment B raw2058step1 raw2058step1Labels := by
      have ha : raw2058step1 = raw2058step0 := by apply Matrix.ext; unfold raw2058step1 raw2058step0; decide +kernel
      have hl : raw2058step0Labels = labelEmbedding7 ∘ raw2058step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2058step0 raw2058step0Labels raw2058step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5037 node5037Labels := by rfl

theorem canonical2059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2059 raw2059Labels = mixedMoment B node2429 node2429Labels := by
  calc
    mixedMoment B raw2059 raw2059Labels = mixedMoment B raw2059step0 raw2059step0Labels := by
      have ha : raw2059step0 = (fun i j => raw2059 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2059step0 raw2059; decide +kernel
      have hl : raw2059step0Labels = raw2059Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2059 raw2059Labels permutation152 permutation4
    _ = mixedMoment B node2429 node2429Labels := by rfl

theorem canonical2060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2060 raw2060Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw2060 raw2060Labels = mixedMoment B raw2060step0 raw2060step0Labels := by
      have ha : raw2060step0 = (fun i j => raw2060 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2060step0 raw2060; decide +kernel
      have hl : raw2060step0Labels = raw2060Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2060 raw2060Labels permutation152 permutation6
    mixedMoment B raw2060step0 raw2060step0Labels = mixedMoment B raw2060step1 raw2060step1Labels := by
      have ha : raw2060step1 = -raw2060step0 := by apply Matrix.ext; change ∀ i j, raw2060step1 i j = -(raw2060step0 i j); unfold raw2060step1 raw2060step0; decide +kernel
      have hl : raw2060step1Labels = raw2060step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2060step1 raw2060step1Labels = mixedMoment B raw2060step2 raw2060step2Labels := by
      have ha : raw2060step2 = raw2060step1 := by apply Matrix.ext; unfold raw2060step2 raw2060step1; decide +kernel
      have hl : raw2060step1Labels = labelEmbedding1 ∘ raw2060step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2060step1 raw2060step1Labels raw2060step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3455 node3455Labels := by rfl

theorem canonical2061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2061 raw2061Labels = mixedMoment B node5038 node5038Labels := by
  calc
    mixedMoment B raw2061 raw2061Labels = mixedMoment B raw2061step0 raw2061step0Labels := by
      have ha : raw2061step0 = (fun i j => raw2061 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2061step0 raw2061; decide +kernel
      have hl : raw2061step0Labels = raw2061Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2061 raw2061Labels permutation152 permutation4
    mixedMoment B raw2061step0 raw2061step0Labels = mixedMoment B raw2061step1 raw2061step1Labels := by
      have ha : raw2061step1 = raw2061step0 := by apply Matrix.ext; unfold raw2061step1 raw2061step0; decide +kernel
      have hl : raw2061step0Labels = labelEmbedding7 ∘ raw2061step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2061step0 raw2061step0Labels raw2061step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5038 node5038Labels := by rfl

theorem canonical2062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2062 raw2062Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw2062 raw2062Labels = mixedMoment B raw2062step0 raw2062step0Labels := by
      have ha : raw2062step0 = (fun i j => raw2062 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2062step0 raw2062; decide +kernel
      have hl : raw2062step0Labels = raw2062Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2062 raw2062Labels permutation152 permutation4
    _ = mixedMoment B node2431 node2431Labels := by rfl

theorem canonical2063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2063 raw2063Labels = mixedMoment B node3453 node3453Labels := by
  calc
    mixedMoment B raw2063 raw2063Labels = mixedMoment B raw2063step0 raw2063step0Labels := by
      have ha : raw2063step0 = (fun i j => raw2063 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2063step0 raw2063; decide +kernel
      have hl : raw2063step0Labels = raw2063Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2063 raw2063Labels permutation154 permutation6
    mixedMoment B raw2063step0 raw2063step0Labels = mixedMoment B raw2063step1 raw2063step1Labels := by
      have ha : raw2063step1 = -raw2063step0 := by apply Matrix.ext; change ∀ i j, raw2063step1 i j = -(raw2063step0 i j); unfold raw2063step1 raw2063step0; decide +kernel
      have hl : raw2063step1Labels = raw2063step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2063step1 raw2063step1Labels = mixedMoment B raw2063step2 raw2063step2Labels := by
      have ha : raw2063step2 = raw2063step1 := by apply Matrix.ext; unfold raw2063step2 raw2063step1; decide +kernel
      have hl : raw2063step1Labels = labelEmbedding1 ∘ raw2063step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2063step1 raw2063step1Labels raw2063step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3453 node3453Labels := by rfl

theorem canonical2100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2100 raw2100Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw2100 raw2100Labels = mixedMoment B raw2100step0 raw2100step0Labels := by
      have ha : raw2100step0 = (fun i j => raw2100 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2100step0 raw2100; decide +kernel
      have hl : raw2100step0Labels = raw2100Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2100 raw2100Labels permutation152 permutation4
    mixedMoment B raw2100step0 raw2100step0Labels = mixedMoment B raw2100step1 raw2100step1Labels := by
      have ha : raw2100step1 = raw2100step0 := by apply Matrix.ext; unfold raw2100step1 raw2100step0; decide +kernel
      have hl : raw2100step0Labels = labelEmbedding7 ∘ raw2100step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2100step0 raw2100step0Labels raw2100step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5076 node5076Labels := by rfl

theorem canonical2101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2101 raw2101Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw2101 raw2101Labels = mixedMoment B raw2101step0 raw2101step0Labels := by
      have ha : raw2101step0 = (fun i j => raw2101 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2101step0 raw2101; decide +kernel
      have hl : raw2101step0Labels = raw2101Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2101 raw2101Labels permutation152 permutation4
    _ = mixedMoment B node2483 node2483Labels := by rfl

theorem canonical2102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2102 raw2102Labels = mixedMoment B node3477 node3477Labels := by
  calc
    mixedMoment B raw2102 raw2102Labels = mixedMoment B raw2102step0 raw2102step0Labels := by
      have ha : raw2102step0 = (fun i j => raw2102 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2102step0 raw2102; decide +kernel
      have hl : raw2102step0Labels = raw2102Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2102 raw2102Labels permutation170 permutation6
    mixedMoment B raw2102step0 raw2102step0Labels = mixedMoment B raw2102step1 raw2102step1Labels := by
      have ha : raw2102step1 = -raw2102step0 := by apply Matrix.ext; change ∀ i j, raw2102step1 i j = -(raw2102step0 i j); unfold raw2102step1 raw2102step0; decide +kernel
      have hl : raw2102step1Labels = raw2102step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2102step1 raw2102step1Labels = mixedMoment B raw2102step2 raw2102step2Labels := by
      have ha : raw2102step2 = raw2102step1 := by apply Matrix.ext; unfold raw2102step2 raw2102step1; decide +kernel
      have hl : raw2102step1Labels = labelEmbedding1 ∘ raw2102step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2102step1 raw2102step1Labels raw2102step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3477 node3477Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21250 raw21250Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw21250 raw21250Labels = mixedMoment B raw21250step0 raw21250step0Labels := by
      have hz : ∀ j, raw21250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21250step0 = (fun i j => raw21250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21250step0 raw21250; decide +kernel
      have hl : raw21250step0Labels = raw21250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21250 raw21250Labels permutation346 hz
    mixedMoment B raw21250step0 raw21250step0Labels = mixedMoment B raw21250step1 raw21250step1Labels := by
      have ha : raw21250step1 = (fun i j => raw21250step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21250step1 raw21250step0; decide +kernel
      have hl : raw21250step1Labels = raw21250step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21250step0 raw21250step0Labels permutation32 permutation3
    mixedMoment B raw21250step1 raw21250step1Labels = mixedMoment B raw21250step2 raw21250step2Labels := by
      have ha : raw21250step2 = raw21250step1 := by apply Matrix.ext; unfold raw21250step2 raw21250step1; decide +kernel
      have hl : raw21250step1Labels = labelEmbedding6 ∘ raw21250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21250step1 raw21250step1Labels raw21250step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4352 node4352Labels := by rfl

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

theorem canonical2187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2187 raw2187Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw2187 raw2187Labels = mixedMoment B raw2187step0 raw2187step0Labels := by
      have ha : raw2187step0 = (fun i j => raw2187 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2187step0 raw2187; decide +kernel
      have hl : raw2187step0Labels = raw2187Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2187 raw2187Labels permutation152 permutation4
    mixedMoment B raw2187step0 raw2187step0Labels = mixedMoment B raw2187step1 raw2187step1Labels := by
      have ha : raw2187step1 = raw2187step0 := by apply Matrix.ext; unfold raw2187step1 raw2187step0; decide +kernel
      have hl : raw2187step0Labels = labelEmbedding7 ∘ raw2187step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2187step0 raw2187step0Labels raw2187step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5162 node5162Labels := by rfl

theorem canonical2188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2188 raw2188Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw2188 raw2188Labels = mixedMoment B raw2188step0 raw2188step0Labels := by
      have ha : raw2188step0 = (fun i j => raw2188 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2188step0 raw2188; decide +kernel
      have hl : raw2188step0Labels = raw2188Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2188 raw2188Labels permutation152 permutation4
    _ = mixedMoment B node2589 node2589Labels := by rfl

theorem canonical2189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2189 raw2189Labels = mixedMoment B node3563 node3563Labels := by
  calc
    mixedMoment B raw2189 raw2189Labels = mixedMoment B raw2189step0 raw2189step0Labels := by
      have ha : raw2189step0 = (fun i j => raw2189 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2189step0 raw2189; decide +kernel
      have hl : raw2189step0Labels = raw2189Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2189 raw2189Labels permutation176 permutation6
    mixedMoment B raw2189step0 raw2189step0Labels = mixedMoment B raw2189step1 raw2189step1Labels := by
      have ha : raw2189step1 = -raw2189step0 := by apply Matrix.ext; change ∀ i j, raw2189step1 i j = -(raw2189step0 i j); unfold raw2189step1 raw2189step0; decide +kernel
      have hl : raw2189step1Labels = raw2189step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2189step1 raw2189step1Labels = mixedMoment B raw2189step2 raw2189step2Labels := by
      have ha : raw2189step2 = raw2189step1 := by apply Matrix.ext; unfold raw2189step2 raw2189step1; decide +kernel
      have hl : raw2189step1Labels = labelEmbedding1 ∘ raw2189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2189step1 raw2189step1Labels raw2189step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3563 node3563Labels := by rfl

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

theorem canonical2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2214 raw2214Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw2214 raw2214Labels = mixedMoment B raw2214step0 raw2214step0Labels := by
      have ha : raw2214step0 = (fun i j => raw2214 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2214step0 raw2214; decide +kernel
      have hl : raw2214step0Labels = raw2214Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2214 raw2214Labels permutation8 permutation4
    mixedMoment B raw2214step0 raw2214step0Labels = mixedMoment B raw2214step1 raw2214step1Labels := by
      have ha : raw2214step1 = raw2214step0 := by apply Matrix.ext; unfold raw2214step1 raw2214step0; decide +kernel
      have hl : raw2214step0Labels = labelEmbedding7 ∘ raw2214step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2214step0 raw2214step0Labels raw2214step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

theorem canonical2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2215 raw2215Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw2215 raw2215Labels = mixedMoment B raw2215step0 raw2215step0Labels := by
      have ha : raw2215step0 = (fun i j => raw2215 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2215step0 raw2215; decide +kernel
      have hl : raw2215step0Labels = raw2215Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2215 raw2215Labels permutation8 permutation4
    _ = mixedMoment B node2604 node2604Labels := by rfl

theorem canonical2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2216 raw2216Labels = mixedMoment B node3614 node3614Labels := by
  calc
    mixedMoment B raw2216 raw2216Labels = mixedMoment B raw2216step0 raw2216step0Labels := by
      have ha : raw2216step0 = (fun i j => raw2216 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2216step0 raw2216; decide +kernel
      have hl : raw2216step0Labels = raw2216Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2216 raw2216Labels permutation8 permutation6
    mixedMoment B raw2216step0 raw2216step0Labels = mixedMoment B raw2216step1 raw2216step1Labels := by
      have ha : raw2216step1 = -raw2216step0 := by apply Matrix.ext; change ∀ i j, raw2216step1 i j = -(raw2216step0 i j); unfold raw2216step1 raw2216step0; decide +kernel
      have hl : raw2216step1Labels = raw2216step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2216step1 raw2216step1Labels = mixedMoment B raw2216step2 raw2216step2Labels := by
      have ha : raw2216step2 = raw2216step1 := by apply Matrix.ext; unfold raw2216step2 raw2216step1; decide +kernel
      have hl : raw2216step1Labels = labelEmbedding1 ∘ raw2216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2216step1 raw2216step1Labels raw2216step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3614 node3614Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2304 raw2304Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw2304 raw2304Labels = mixedMoment B raw2304step0 raw2304step0Labels := by
      have ha : raw2304step0 = (fun i j => raw2304 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2304step0 raw2304; decide +kernel
      have hl : raw2304step0Labels = raw2304Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2304 raw2304Labels permutation8 permutation4
    mixedMoment B raw2304step0 raw2304step0Labels = mixedMoment B raw2304step1 raw2304step1Labels := by
      have ha : raw2304step1 = raw2304step0 := by apply Matrix.ext; unfold raw2304step1 raw2304step0; decide +kernel
      have hl : raw2304step0Labels = labelEmbedding7 ∘ raw2304step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2304step0 raw2304step0Labels raw2304step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

theorem canonical2305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2305 raw2305Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw2305 raw2305Labels = mixedMoment B raw2305step0 raw2305step0Labels := by
      have ha : raw2305step0 = (fun i j => raw2305 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2305step0 raw2305; decide +kernel
      have hl : raw2305step0Labels = raw2305Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2305 raw2305Labels permutation8 permutation4
    _ = mixedMoment B node2768 node2768Labels := by rfl

theorem canonical2306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2306 raw2306Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw2306 raw2306Labels = mixedMoment B raw2306step0 raw2306step0Labels := by
      have ha : raw2306step0 = (fun i j => raw2306 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2306step0 raw2306; decide +kernel
      have hl : raw2306step0Labels = raw2306Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2306 raw2306Labels permutation12 permutation6
    mixedMoment B raw2306step0 raw2306step0Labels = mixedMoment B raw2306step1 raw2306step1Labels := by
      have ha : raw2306step1 = -raw2306step0 := by apply Matrix.ext; change ∀ i j, raw2306step1 i j = -(raw2306step0 i j); unfold raw2306step1 raw2306step0; decide +kernel
      have hl : raw2306step1Labels = raw2306step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2306step1 raw2306step1Labels = mixedMoment B raw2306step2 raw2306step2Labels := by
      have ha : raw2306step2 = raw2306step1 := by apply Matrix.ext; unfold raw2306step2 raw2306step1; decide +kernel
      have hl : raw2306step1Labels = labelEmbedding1 ∘ raw2306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2306step1 raw2306step1Labels raw2306step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3632 node3632Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical180
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23047 raw23047Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw23047 raw23047Labels = mixedMoment B raw23047step0 raw23047step0Labels := by
      have hz : ∀ j, raw23047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23047step0 = (fun i j => raw23047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23047step0 raw23047; decide +kernel
      have hl : raw23047step0Labels = raw23047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23047 raw23047Labels permutation346 hz
    mixedMoment B raw23047step0 raw23047step0Labels = mixedMoment B raw23047step1 raw23047step1Labels := by
      have ha : raw23047step1 = (fun i j => raw23047step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23047step1 raw23047step0; decide +kernel
      have hl : raw23047step1Labels = raw23047step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23047step0 raw23047step0Labels permutation33 permutation3
    mixedMoment B raw23047step1 raw23047step1Labels = mixedMoment B raw23047step2 raw23047step2Labels := by
      have ha : raw23047step2 = raw23047step1 := by apply Matrix.ext; unfold raw23047step2 raw23047step1; decide +kernel
      have hl : raw23047step1Labels = labelEmbedding6 ∘ raw23047step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23047step1 raw23047step1Labels raw23047step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4354 node4354Labels := by rfl

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

theorem canonical25074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25074 raw25074Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw25074 raw25074Labels = mixedMoment B raw25074step0 raw25074step0Labels := by
      have hz : ∀ j, raw25074 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25074step0 = (fun i j => raw25074 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25074step0 raw25074; decide +kernel
      have hl : raw25074step0Labels = raw25074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25074 raw25074Labels permutation346 hz
    mixedMoment B raw25074step0 raw25074step0Labels = mixedMoment B raw25074step1 raw25074step1Labels := by
      have ha : raw25074step1 = (fun i j => raw25074step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25074step1 raw25074step0; decide +kernel
      have hl : raw25074step1Labels = raw25074step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25074step0 raw25074step0Labels permutation35 permutation3
    mixedMoment B raw25074step1 raw25074step1Labels = mixedMoment B raw25074step2 raw25074step2Labels := by
      have ha : raw25074step2 = raw25074step1 := by apply Matrix.ext; unfold raw25074step2 raw25074step1; decide +kernel
      have hl : raw25074step1Labels = labelEmbedding6 ∘ raw25074step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25074step1 raw25074step1Labels raw25074step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4354 node4354Labels := by rfl

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

theorem canonical272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw272 raw272Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw272 raw272Labels = mixedMoment B raw272step0 raw272step0Labels := by
      have ha : raw272step0 = (fun i j => raw272 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw272step0 raw272; decide +kernel
      have hl : raw272step0Labels = raw272Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw272 raw272Labels permutation8 permutation5
    mixedMoment B raw272step0 raw272step0Labels = mixedMoment B raw272step1 raw272step1Labels := by
      have ha : raw272step1 = raw272step0 := by apply Matrix.ext; unfold raw272step1 raw272step0; decide +kernel
      have hl : raw272step0Labels = labelEmbedding1 ∘ raw272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw272step0 raw272step0Labels raw272step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2768 node2768Labels := by rfl

theorem canonical273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw273 raw273Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw273 raw273Labels = mixedMoment B raw273step0 raw273step0Labels := by
      have ha : raw273step0 = (fun i j => raw273 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw273step0 raw273; decide +kernel
      have hl : raw273step0Labels = raw273Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw273 raw273Labels permutation8 permutation5
    _ = mixedMoment B node405 node405Labels := by rfl

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

theorem canonical3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3054 raw3054Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw3054 raw3054Labels = mixedMoment B raw3054step0 raw3054step0Labels := by
      have hz : ∀ j, raw3054 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3054step0 = (fun i j => raw3054 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3054step0 raw3054; decide +kernel
      have hl : raw3054step0Labels = raw3054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3054 raw3054Labels permutation434 hz
    mixedMoment B raw3054step0 raw3054step0Labels = mixedMoment B raw3054step1 raw3054step1Labels := by
      have hz : ∀ j, raw3054step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3054step1 = (fun i j => raw3054step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3054step1 raw3054step0; decide +kernel
      have hl : raw3054step1Labels = raw3054step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3054step0 raw3054step0Labels permutation80 hz
    mixedMoment B raw3054step1 raw3054step1Labels = mixedMoment B raw3054step2 raw3054step2Labels := by
      have ha : raw3054step2 = (fun i j => raw3054step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3054step2 raw3054step1; decide +kernel
      have hl : raw3054step2Labels = raw3054step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3054step1 raw3054step1Labels permutation8 permutation3
    mixedMoment B raw3054step2 raw3054step2Labels = mixedMoment B raw3054step3 raw3054step3Labels := by
      have ha : raw3054step3 = raw3054step2 := by apply Matrix.ext; unfold raw3054step3 raw3054step2; decide +kernel
      have hl : raw3054step2Labels = labelEmbedding6 ∘ raw3054step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3054step2 raw3054step2Labels raw3054step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

theorem canonical3055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3055 raw3055Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw3055 raw3055Labels = mixedMoment B raw3055step0 raw3055step0Labels := by
      have hz : ∀ j, raw3055 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3055step0 = (fun i j => raw3055 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3055step0 raw3055; decide +kernel
      have hl : raw3055step0Labels = raw3055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3055 raw3055Labels permutation434 hz
    mixedMoment B raw3055step0 raw3055step0Labels = mixedMoment B raw3055step1 raw3055step1Labels := by
      have hz : ∀ j, raw3055step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3055step1 = (fun i j => raw3055step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3055step1 raw3055step0; decide +kernel
      have hl : raw3055step1Labels = raw3055step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3055step0 raw3055step0Labels permutation80 hz
    mixedMoment B raw3055step1 raw3055step1Labels = mixedMoment B raw3055step2 raw3055step2Labels := by
      have ha : raw3055step2 = (fun i j => raw3055step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3055step2 raw3055step1; decide +kernel
      have hl : raw3055step2Labels = raw3055step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3055step1 raw3055step1Labels permutation31 permutation2
    mixedMoment B raw3055step2 raw3055step2Labels = mixedMoment B raw3055step3 raw3055step3Labels := by
      have ha : raw3055step3 = -raw3055step2 := by apply Matrix.ext; change ∀ i j, raw3055step3 i j = -(raw3055step2 i j); unfold raw3055step3 raw3055step2; decide +kernel
      have hl : raw3055step3Labels = raw3055step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5442 node5442Labels := by rfl

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

theorem canonical32203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32203 raw32203Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw32203 raw32203Labels = mixedMoment B raw32203step0 raw32203step0Labels := by
      have hz : ∀ j, raw32203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32203step0 = (fun i j => raw32203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32203step0 raw32203; decide +kernel
      have hl : raw32203step0Labels = raw32203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32203 raw32203Labels permutation346 hz
    mixedMoment B raw32203step0 raw32203step0Labels = mixedMoment B raw32203step1 raw32203step1Labels := by
      have ha : raw32203step1 = (fun i j => raw32203step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32203step1 raw32203step0; decide +kernel
      have hl : raw32203step1Labels = raw32203step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32203step0 raw32203step0Labels permutation35 permutation3
    mixedMoment B raw32203step1 raw32203step1Labels = mixedMoment B raw32203step2 raw32203step2Labels := by
      have ha : raw32203step2 = raw32203step1 := by apply Matrix.ext; unfold raw32203step2 raw32203step1; decide +kernel
      have hl : raw32203step1Labels = labelEmbedding6 ∘ raw32203step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32203step1 raw32203step1Labels raw32203step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

theorem canonical32204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32204 raw32204Labels = mixedMoment B node5038 node5038Labels := by
  calc
    mixedMoment B raw32204 raw32204Labels = mixedMoment B raw32204step0 raw32204step0Labels := by
      have ha : raw32204step0 = (fun i j => raw32204 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32204step0 raw32204; decide +kernel
      have hl : raw32204step0Labels = raw32204Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32204 raw32204Labels permutation179 permutation3
    mixedMoment B raw32204step0 raw32204step0Labels = mixedMoment B raw32204step1 raw32204step1Labels := by
      have ha : raw32204step1 = raw32204step0 := by apply Matrix.ext; unfold raw32204step1 raw32204step0; decide +kernel
      have hl : raw32204step0Labels = labelEmbedding6 ∘ raw32204step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32204step0 raw32204step0Labels raw32204step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5038 node5038Labels := by rfl

theorem canonical32205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32205 raw32205Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw32205 raw32205Labels = mixedMoment B raw32205step0 raw32205step0Labels := by
      have hz : ∀ j, raw32205 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32205step0 = (fun i j => raw32205 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32205step0 raw32205; decide +kernel
      have hl : raw32205step0Labels = raw32205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32205 raw32205Labels permutation520 hz
    mixedMoment B raw32205step0 raw32205step0Labels = mixedMoment B raw32205step1 raw32205step1Labels := by
      have hz : ∀ j, raw32205step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32205step1 = (fun i j => raw32205step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32205step1 raw32205step0; decide +kernel
      have hl : raw32205step1Labels = raw32205step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32205step0 raw32205step0Labels permutation80 hz
    mixedMoment B raw32205step1 raw32205step1Labels = mixedMoment B raw32205step2 raw32205step2Labels := by
      have ha : raw32205step2 = (fun i j => raw32205step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32205step2 raw32205step1; decide +kernel
      have hl : raw32205step2Labels = raw32205step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32205step1 raw32205step1Labels permutation9 permutation3
    mixedMoment B raw32205step2 raw32205step2Labels = mixedMoment B raw32205step3 raw32205step3Labels := by
      have ha : raw32205step3 = raw32205step2 := by apply Matrix.ext; unfold raw32205step3 raw32205step2; decide +kernel
      have hl : raw32205step2Labels = labelEmbedding6 ∘ raw32205step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32205step2 raw32205step2Labels raw32205step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

theorem canonical32206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32206 raw32206Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw32206 raw32206Labels = mixedMoment B raw32206step0 raw32206step0Labels := by
      have hz : ∀ j, raw32206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32206step0 = (fun i j => raw32206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32206step0 raw32206; decide +kernel
      have hl : raw32206step0Labels = raw32206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32206 raw32206Labels permutation346 hz
    mixedMoment B raw32206step0 raw32206step0Labels = mixedMoment B raw32206step1 raw32206step1Labels := by
      have ha : raw32206step1 = (fun i j => raw32206step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32206step1 raw32206step0; decide +kernel
      have hl : raw32206step1Labels = raw32206step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32206step0 raw32206step0Labels permutation33 permutation3
    mixedMoment B raw32206step1 raw32206step1Labels = mixedMoment B raw32206step2 raw32206step2Labels := by
      have ha : raw32206step2 = raw32206step1 := by apply Matrix.ext; unfold raw32206step2 raw32206step1; decide +kernel
      have hl : raw32206step1Labels = labelEmbedding6 ∘ raw32206step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32206step1 raw32206step1Labels raw32206step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

theorem canonical32207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32207 raw32207Labels = mixedMoment B node5038 node5038Labels := by
  calc
    mixedMoment B raw32207 raw32207Labels = mixedMoment B raw32207step0 raw32207step0Labels := by
      have ha : raw32207step0 = (fun i j => raw32207 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32207step0 raw32207; decide +kernel
      have hl : raw32207step0Labels = raw32207Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32207 raw32207Labels permutation177 permutation3
    mixedMoment B raw32207step0 raw32207step0Labels = mixedMoment B raw32207step1 raw32207step1Labels := by
      have ha : raw32207step1 = raw32207step0 := by apply Matrix.ext; unfold raw32207step1 raw32207step0; decide +kernel
      have hl : raw32207step0Labels = labelEmbedding6 ∘ raw32207step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32207step0 raw32207step0Labels raw32207step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5038 node5038Labels := by rfl

theorem canonical32208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32208 raw32208Labels = mixedMoment B node4948 node4948Labels := by
  calc
    mixedMoment B raw32208 raw32208Labels = mixedMoment B raw32208step0 raw32208step0Labels := by
      have hz : ∀ j, raw32208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32208step0 = (fun i j => raw32208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32208step0 raw32208; decide +kernel
      have hl : raw32208step0Labels = raw32208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32208 raw32208Labels permutation346 hz
    mixedMoment B raw32208step0 raw32208step0Labels = mixedMoment B raw32208step1 raw32208step1Labels := by
      have ha : raw32208step1 = (fun i j => raw32208step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32208step1 raw32208step0; decide +kernel
      have hl : raw32208step1Labels = raw32208step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32208step0 raw32208step0Labels permutation32 permutation3
    mixedMoment B raw32208step1 raw32208step1Labels = mixedMoment B raw32208step2 raw32208step2Labels := by
      have ha : raw32208step2 = raw32208step1 := by apply Matrix.ext; unfold raw32208step2 raw32208step1; decide +kernel
      have hl : raw32208step1Labels = labelEmbedding6 ∘ raw32208step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32208step1 raw32208step1Labels raw32208step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4948 node4948Labels := by rfl

theorem canonical32209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32209 raw32209Labels = mixedMoment B node5037 node5037Labels := by
  calc
    mixedMoment B raw32209 raw32209Labels = mixedMoment B raw32209step0 raw32209step0Labels := by
      have ha : raw32209step0 = (fun i j => raw32209 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32209step0 raw32209; decide +kernel
      have hl : raw32209step0Labels = raw32209Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32209 raw32209Labels permutation176 permutation3
    mixedMoment B raw32209step0 raw32209step0Labels = mixedMoment B raw32209step1 raw32209step1Labels := by
      have ha : raw32209step1 = raw32209step0 := by apply Matrix.ext; unfold raw32209step1 raw32209step0; decide +kernel
      have hl : raw32209step0Labels = labelEmbedding6 ∘ raw32209step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32209step0 raw32209step0Labels raw32209step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5037 node5037Labels := by rfl

theorem canonical32210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32210 raw32210Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw32210 raw32210Labels = mixedMoment B raw32210step0 raw32210step0Labels := by
      have hz : ∀ j, raw32210 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32210step0 = (fun i j => raw32210 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32210step0 raw32210; decide +kernel
      have hl : raw32210step0Labels = raw32210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32210 raw32210Labels permutation520 hz
    mixedMoment B raw32210step0 raw32210step0Labels = mixedMoment B raw32210step1 raw32210step1Labels := by
      have hz : ∀ j, raw32210step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32210step1 = (fun i j => raw32210step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32210step1 raw32210step0; decide +kernel
      have hl : raw32210step1Labels = raw32210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32210step0 raw32210step0Labels permutation80 hz
    mixedMoment B raw32210step1 raw32210step1Labels = mixedMoment B raw32210step2 raw32210step2Labels := by
      have ha : raw32210step2 = (fun i j => raw32210step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32210step2 raw32210step1; decide +kernel
      have hl : raw32210step2Labels = raw32210step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32210step1 raw32210step1Labels permutation31 permutation2
    mixedMoment B raw32210step2 raw32210step2Labels = mixedMoment B raw32210step3 raw32210step3Labels := by
      have ha : raw32210step3 = -raw32210step2 := by apply Matrix.ext; change ∀ i j, raw32210step3 i j = -(raw32210step2 i j); unfold raw32210step3 raw32210step2; decide +kernel
      have hl : raw32210step3Labels = raw32210step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5174 node5174Labels := by rfl

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

theorem canonical1143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1143 raw1143Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw1143 raw1143Labels = mixedMoment B raw1143step0 raw1143step0Labels := by
      have ha : raw1143step0 = (fun i j => raw1143 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1143step0 raw1143; decide +kernel
      have hl : raw1143step0Labels = raw1143Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1143 raw1143Labels permutation32 permutation4
    mixedMoment B raw1143step0 raw1143step0Labels = mixedMoment B raw1143step1 raw1143step1Labels := by
      have ha : raw1143step1 = raw1143step0 := by apply Matrix.ext; unfold raw1143step1 raw1143step0; decide +kernel
      have hl : raw1143step0Labels = labelEmbedding7 ∘ raw1143step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1143step0 raw1143step0Labels raw1143step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4352 node4352Labels := by rfl

theorem canonical1144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1144 raw1144Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw1144 raw1144Labels = mixedMoment B raw1144step0 raw1144step0Labels := by
      have ha : raw1144step0 = (fun i j => raw1144 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1144step0 raw1144; decide +kernel
      have hl : raw1144step0Labels = raw1144Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1144 raw1144Labels permutation32 permutation4
    _ = mixedMoment B node930 node930Labels := by rfl

theorem canonical1145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1145 raw1145Labels = mixedMoment B node1690 node1690Labels := by
  calc
    mixedMoment B raw1145 raw1145Labels = mixedMoment B raw1145step0 raw1145step0Labels := by
      have ha : raw1145step0 = (fun i j => raw1145 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1145step0 raw1145; decide +kernel
      have hl : raw1145step0Labels = raw1145Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1145 raw1145Labels permutation32 permutation6
    mixedMoment B raw1145step0 raw1145step0Labels = mixedMoment B raw1145step1 raw1145step1Labels := by
      have ha : raw1145step1 = -raw1145step0 := by apply Matrix.ext; change ∀ i j, raw1145step1 i j = -(raw1145step0 i j); unfold raw1145step1 raw1145step0; decide +kernel
      have hl : raw1145step1Labels = raw1145step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1145step1 raw1145step1Labels = mixedMoment B raw1145step2 raw1145step2Labels := by
      have ha : raw1145step2 = raw1145step1 := by apply Matrix.ext; unfold raw1145step2 raw1145step1; decide +kernel
      have hl : raw1145step1Labels = labelEmbedding1 ∘ raw1145step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1145step1 raw1145step1Labels raw1145step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1690 node1690Labels := by rfl

theorem canonical1146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1146 raw1146Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw1146 raw1146Labels = mixedMoment B raw1146step0 raw1146step0Labels := by
      have ha : raw1146step0 = (fun i j => raw1146 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1146step0 raw1146; decide +kernel
      have hl : raw1146step0Labels = raw1146Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1146 raw1146Labels permutation32 permutation4
    mixedMoment B raw1146step0 raw1146step0Labels = mixedMoment B raw1146step1 raw1146step1Labels := by
      have ha : raw1146step1 = raw1146step0 := by apply Matrix.ext; unfold raw1146step1 raw1146step0; decide +kernel
      have hl : raw1146step0Labels = labelEmbedding7 ∘ raw1146step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1146step0 raw1146step0Labels raw1146step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4354 node4354Labels := by rfl

theorem canonical1147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1147 raw1147Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw1147 raw1147Labels = mixedMoment B raw1147step0 raw1147step0Labels := by
      have ha : raw1147step0 = (fun i j => raw1147 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1147step0 raw1147; decide +kernel
      have hl : raw1147step0Labels = raw1147Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1147 raw1147Labels permutation32 permutation4
    _ = mixedMoment B node932 node932Labels := by rfl

theorem canonical1148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1148 raw1148Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw1148 raw1148Labels = mixedMoment B raw1148step0 raw1148step0Labels := by
      have ha : raw1148step0 = (fun i j => raw1148 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1148step0 raw1148; decide +kernel
      have hl : raw1148step0Labels = raw1148Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1148 raw1148Labels permutation34 permutation6
    mixedMoment B raw1148step0 raw1148step0Labels = mixedMoment B raw1148step1 raw1148step1Labels := by
      have ha : raw1148step1 = -raw1148step0 := by apply Matrix.ext; change ∀ i j, raw1148step1 i j = -(raw1148step0 i j); unfold raw1148step1 raw1148step0; decide +kernel
      have hl : raw1148step1Labels = raw1148step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1148step1 raw1148step1Labels = mixedMoment B raw1148step2 raw1148step2Labels := by
      have ha : raw1148step2 = raw1148step1 := by apply Matrix.ext; unfold raw1148step2 raw1148step1; decide +kernel
      have hl : raw1148step1Labels = labelEmbedding1 ∘ raw1148step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1148step1 raw1148step1Labels raw1148step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1681 node1681Labels := by rfl

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

theorem canonical1266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1266 raw1266Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw1266 raw1266Labels = mixedMoment B raw1266step0 raw1266step0Labels := by
      have ha : raw1266step0 = (fun i j => raw1266 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1266step0 raw1266; decide +kernel
      have hl : raw1266step0Labels = raw1266Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1266 raw1266Labels permutation32 permutation4
    mixedMoment B raw1266step0 raw1266step0Labels = mixedMoment B raw1266step1 raw1266step1Labels := by
      have ha : raw1266step1 = raw1266step0 := by apply Matrix.ext; unfold raw1266step1 raw1266step0; decide +kernel
      have hl : raw1266step0Labels = labelEmbedding7 ∘ raw1266step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1266step0 raw1266step0Labels raw1266step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

theorem canonical1267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1267 raw1267Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw1267 raw1267Labels = mixedMoment B raw1267step0 raw1267step0Labels := by
      have ha : raw1267step0 = (fun i j => raw1267 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1267step0 raw1267; decide +kernel
      have hl : raw1267step0Labels = raw1267Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1267 raw1267Labels permutation32 permutation4
    _ = mixedMoment B node1044 node1044Labels := by rfl

theorem canonical1268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1268 raw1268Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw1268 raw1268Labels = mixedMoment B raw1268step0 raw1268step0Labels := by
      have ha : raw1268step0 = (fun i j => raw1268 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1268step0 raw1268; decide +kernel
      have hl : raw1268step0Labels = raw1268Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1268 raw1268Labels permutation50 permutation6
    mixedMoment B raw1268step0 raw1268step0Labels = mixedMoment B raw1268step1 raw1268step1Labels := by
      have ha : raw1268step1 = -raw1268step0 := by apply Matrix.ext; change ∀ i j, raw1268step1 i j = -(raw1268step0 i j); unfold raw1268step1 raw1268step0; decide +kernel
      have hl : raw1268step1Labels = raw1268step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1268step1 raw1268step1Labels = mixedMoment B raw1268step2 raw1268step2Labels := by
      have ha : raw1268step2 = raw1268step1 := by apply Matrix.ext; unfold raw1268step2 raw1268step1; decide +kernel
      have hl : raw1268step1Labels = labelEmbedding1 ∘ raw1268step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1268step1 raw1268step1Labels raw1268step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5169 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5169 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5169 = injectiveMoment H raw5169step0 := by
      have hz : ∀ j, raw5169 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5169step0 = (fun i j => raw5169 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169 permutation21 hz
    injectiveMoment H raw5169step0 = injectiveMoment H raw5169step1 := by
      have hz : ∀ j, raw5169step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5169step1 = (fun i j => raw5169step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169step0 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

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

theorem canonical671 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw671 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw671 = injectiveMoment H raw671step0 := by
      have heq : raw671step0 = -raw671 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw671).symm
    injectiveMoment H raw671step0 = injectiveMoment H raw671step1 := by
      have heq : raw671step1 = (fun i j => raw671step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw671step0 permutation9 permutation8
    _ = injectiveMoment H node169 := by rfl

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

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

theorem canonical924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw924 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw924 = injectiveMoment H raw924step0 := by
      have heq : raw924step0 = (fun i j => raw924 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw924 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
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

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
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

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

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

theorem sound57 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node57 = Sparse.eval value57 (momentVector H) := by
  have heq : pivotMatrix57 = (fun u v => node57 (pivotPermutation57 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node57 = injectiveMoment H pivotMatrix57 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix57 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix57 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node57 + (injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value57, value10, value4, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical782 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw782 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw782 = injectiveMoment H raw782step0 := by
      have heq : raw782step0 = -raw782 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw782).symm
    injectiveMoment H raw782step0 = injectiveMoment H raw782step1 := by
      have heq : raw782step1 = (fun i j => raw782step0 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw782step0 permutation13 permutation8
    _ = injectiveMoment H node185 := by rfl

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

theorem canonical1435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1435 = injectiveMoment H node31 := by
  rfl

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

theorem canonical2863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2863 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2863 = injectiveMoment H raw2863step0 := by
      have heq : raw2863step0 = (fun i j => raw2863 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2863 permutation4 permutation5
    _ = injectiveMoment H node56 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2823 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw2823 = injectiveMoment H raw2823step0 := by
      have heq : raw2823step0 = (fun i j => raw2823 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2823 permutation4 permutation5
    _ = injectiveMoment H node57 := by rfl

theorem canonical2845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2845 = injectiveMoment H node36 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5979 = injectiveMoment H node57 := by
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

theorem sound169 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node169 = Sparse.eval value169 (momentVector H) := by
  have heq : pivotMatrix169 = (fun u v => node169 (pivotPermutation169 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node169 = injectiveMoment H pivotMatrix169 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix169 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix169 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix169 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (0 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix169 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (1 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix169 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node169 + (injectiveMoment H (mergeFirst pivotMatrix169 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix169 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix169 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value169, value31, value36, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound185 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node185 = Sparse.eval value185 (momentVector H) := by
  have heq : pivotMatrix185 = (fun u v => node185 (pivotPermutation185 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node185 = injectiveMoment H pivotMatrix185 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix185 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix185 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (0 : Fin 3) = raw5979 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (1 : Fin 3) = raw2863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2863 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node185 + (injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value185, value36, value56, value57, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

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

theorem singlePair343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node343 node343Labels = Sparse.eval singlePairValue343 (familyPairVector B) := by
  have hp := single_label_three B hB node343
  have hl : node343Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node343 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node343 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 2) = PairSemantics.raw7685 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node343 PairSemantics.raw7685; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7685 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node343 PairSemantics.raw872; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value169 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 4) = PairSemantics.raw671 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node343 PairSemantics.raw671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical671 hH).trans (PairSemantics.sound169 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue343, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value25, PairSemantics.value169, Sparse.eval] at hp ⊢
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

theorem singlePair405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node405 node405Labels = Sparse.eval singlePairValue405 (familyPairVector B) := by
  have hp := single_label_three B hB node405
  have hl : node405Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node405 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 1) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node405 PairSemantics.raw5204; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 2) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node405 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node405 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value185 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 4) = PairSemantics.raw782 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node405 PairSemantics.raw782; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical782 hH).trans (PairSemantics.sound185 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue405, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value185, Sparse.eval] at hp ⊢
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

theorem singleton2604 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2604 node2604Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node343 node343Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw246 singletonSmall2604
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2604) = raw246Labels := by decide +kernel
  rw [hl, canonical246 B hB] at h
  have hc0 : mixedMoment B raw246 (Fin.cases (0 : Fin 1) singletonSmall2604) =
      mixedMoment B node343 node343Labels := by
    have ha : raw246 = raw247 := by apply Matrix.ext; unfold raw246 raw247; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2604 = raw247Labels := by decide +kernel
    rw [ha, hj, canonical247 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton2768 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2768 node2768Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node405 node405Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw272 singletonSmall2768
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2768) = raw272Labels := by decide +kernel
  rw [hl, canonical272 B hB] at h
  have hc0 : mixedMoment B raw272 (Fin.cases (0 : Fin 1) singletonSmall2768) =
      mixedMoment B node405 node405Labels := by
    have ha : raw272 = raw273 := by apply Matrix.ext; unfold raw272 raw273; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2768 = raw273Labels := by decide +kernel
    rw [ha, hj, canonical273 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4352 node4352Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node930 node930Labels + mixedMoment B node1690 node1690Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1143 singletonSmall4352
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4352) = raw1143Labels := by decide +kernel
  rw [hl, canonical1143 B hB] at h
  have hc0 : mixedMoment B raw1143 (Fin.cases (0 : Fin 2) singletonSmall4352) =
      mixedMoment B node930 node930Labels := by
    have ha : raw1143 = raw1144 := by apply Matrix.ext; unfold raw1143 raw1144; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4352 = raw1144Labels := by decide +kernel
    rw [ha, hj, canonical1144 B hB]
  have hc1 : mixedMoment B raw1143 (Fin.cases (1 : Fin 2) singletonSmall4352) =
      mixedMoment B node1690 node1690Labels := by
    have ha : raw1143 = raw1145 := by apply Matrix.ext; unfold raw1143 raw1145; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4352 = raw1145Labels := by decide +kernel
    rw [ha, hj, canonical1145 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4354 node4354Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node932 node932Labels + mixedMoment B node1681 node1681Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1146 singletonSmall4354
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4354) = raw1146Labels := by decide +kernel
  rw [hl, canonical1146 B hB] at h
  have hc0 : mixedMoment B raw1146 (Fin.cases (0 : Fin 2) singletonSmall4354) =
      mixedMoment B node932 node932Labels := by
    have ha : raw1146 = raw1147 := by apply Matrix.ext; unfold raw1146 raw1147; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4354 = raw1147Labels := by decide +kernel
    rw [ha, hj, canonical1147 B hB]
  have hc1 : mixedMoment B raw1146 (Fin.cases (1 : Fin 2) singletonSmall4354) =
      mixedMoment B node1681 node1681Labels := by
    have ha : raw1146 = raw1148 := by apply Matrix.ext; unfold raw1146 raw1148; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4354 = raw1148Labels := by decide +kernel
    rw [ha, hj, canonical1148 B hB]
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

theorem singleton4461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4461 node4461Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1044 node1044Labels + mixedMoment B node1737 node1737Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1266 singletonSmall4461
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4461) = raw1266Labels := by decide +kernel
  rw [hl, canonical1266 B hB] at h
  have hc0 : mixedMoment B raw1266 (Fin.cases (0 : Fin 2) singletonSmall4461) =
      mixedMoment B node1044 node1044Labels := by
    have ha : raw1266 = raw1267 := by apply Matrix.ext; unfold raw1266 raw1267; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4461 = raw1267Labels := by decide +kernel
    rw [ha, hj, canonical1267 B hB]
  have hc1 : mixedMoment B raw1266 (Fin.cases (1 : Fin 2) singletonSmall4461) =
      mixedMoment B node1737 node1737Labels := by
    have ha : raw1266 = raw1268 := by apply Matrix.ext; unfold raw1266 raw1268; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4461 = raw1268Labels := by decide +kernel
    rw [ha, hj, canonical1268 B hB]
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

theorem singleton4948 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4948 node4948Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2339 node2339Labels + mixedMoment B node3420 node3420Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1917 singletonSmall4948
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4948) = raw1917Labels := by decide +kernel
  rw [hl, canonical1917 B hB] at h
  have hc0 : mixedMoment B raw1917 (Fin.cases (0 : Fin 2) singletonSmall4948) =
      mixedMoment B node2339 node2339Labels := by
    have ha : raw1917 = raw1918 := by apply Matrix.ext; unfold raw1917 raw1918; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4948 = raw1918Labels := by decide +kernel
    rw [ha, hj, canonical1918 B hB]
  have hc1 : mixedMoment B raw1917 (Fin.cases (1 : Fin 2) singletonSmall4948) =
      mixedMoment B node3420 node3420Labels := by
    have ha : raw1917 = raw1919 := by apply Matrix.ext; unfold raw1917 raw1919; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4948 = raw1919Labels := by decide +kernel
    rw [ha, hj, canonical1919 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4949 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4949 node4949Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2341 node2341Labels + mixedMoment B node3417 node3417Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1920 singletonSmall4949
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4949) = raw1920Labels := by decide +kernel
  rw [hl, canonical1920 B hB] at h
  have hc0 : mixedMoment B raw1920 (Fin.cases (0 : Fin 2) singletonSmall4949) =
      mixedMoment B node2341 node2341Labels := by
    have ha : raw1920 = raw1921 := by apply Matrix.ext; unfold raw1920 raw1921; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4949 = raw1921Labels := by decide +kernel
    rw [ha, hj, canonical1921 B hB]
  have hc1 : mixedMoment B raw1920 (Fin.cases (1 : Fin 2) singletonSmall4949) =
      mixedMoment B node3417 node3417Labels := by
    have ha : raw1920 = raw1922 := by apply Matrix.ext; unfold raw1920 raw1922; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4949 = raw1922Labels := by decide +kernel
    rw [ha, hj, canonical1922 B hB]
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

theorem singleton5037 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5037 node5037Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2429 node2429Labels + mixedMoment B node3455 node3455Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2058 singletonSmall5037
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5037) = raw2058Labels := by decide +kernel
  rw [hl, canonical2058 B hB] at h
  have hc0 : mixedMoment B raw2058 (Fin.cases (0 : Fin 2) singletonSmall5037) =
      mixedMoment B node2429 node2429Labels := by
    have ha : raw2058 = raw2059 := by apply Matrix.ext; unfold raw2058 raw2059; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5037 = raw2059Labels := by decide +kernel
    rw [ha, hj, canonical2059 B hB]
  have hc1 : mixedMoment B raw2058 (Fin.cases (1 : Fin 2) singletonSmall5037) =
      mixedMoment B node3455 node3455Labels := by
    have ha : raw2058 = raw2060 := by apply Matrix.ext; unfold raw2058 raw2060; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5037 = raw2060Labels := by decide +kernel
    rw [ha, hj, canonical2060 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5038 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5038 node5038Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2431 node2431Labels + mixedMoment B node3453 node3453Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2061 singletonSmall5038
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5038) = raw2061Labels := by decide +kernel
  rw [hl, canonical2061 B hB] at h
  have hc0 : mixedMoment B raw2061 (Fin.cases (0 : Fin 2) singletonSmall5038) =
      mixedMoment B node2431 node2431Labels := by
    have ha : raw2061 = raw2062 := by apply Matrix.ext; unfold raw2061 raw2062; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5038 = raw2062Labels := by decide +kernel
    rw [ha, hj, canonical2062 B hB]
  have hc1 : mixedMoment B raw2061 (Fin.cases (1 : Fin 2) singletonSmall5038) =
      mixedMoment B node3453 node3453Labels := by
    have ha : raw2061 = raw2063 := by apply Matrix.ext; unfold raw2061 raw2063; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5038 = raw2063Labels := by decide +kernel
    rw [ha, hj, canonical2063 B hB]
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

theorem singleton5076 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5076 node5076Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2483 node2483Labels + mixedMoment B node3477 node3477Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2100 singletonSmall5076
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5076) = raw2100Labels := by decide +kernel
  rw [hl, canonical2100 B hB] at h
  have hc0 : mixedMoment B raw2100 (Fin.cases (0 : Fin 2) singletonSmall5076) =
      mixedMoment B node2483 node2483Labels := by
    have ha : raw2100 = raw2101 := by apply Matrix.ext; unfold raw2100 raw2101; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5076 = raw2101Labels := by decide +kernel
    rw [ha, hj, canonical2101 B hB]
  have hc1 : mixedMoment B raw2100 (Fin.cases (1 : Fin 2) singletonSmall5076) =
      mixedMoment B node3477 node3477Labels := by
    have ha : raw2100 = raw2102 := by apply Matrix.ext; unfold raw2100 raw2102; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5076 = raw2102Labels := by decide +kernel
    rw [ha, hj, canonical2102 B hB]
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

theorem singleton5162 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5162 node5162Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2589 node2589Labels + mixedMoment B node3563 node3563Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2187 singletonSmall5162
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5162) = raw2187Labels := by decide +kernel
  rw [hl, canonical2187 B hB] at h
  have hc0 : mixedMoment B raw2187 (Fin.cases (0 : Fin 2) singletonSmall5162) =
      mixedMoment B node2589 node2589Labels := by
    have ha : raw2187 = raw2188 := by apply Matrix.ext; unfold raw2187 raw2188; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5162 = raw2188Labels := by decide +kernel
    rw [ha, hj, canonical2188 B hB]
  have hc1 : mixedMoment B raw2187 (Fin.cases (1 : Fin 2) singletonSmall5162) =
      mixedMoment B node3563 node3563Labels := by
    have ha : raw2187 = raw2189 := by apply Matrix.ext; unfold raw2187 raw2189; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5162 = raw2189Labels := by decide +kernel
    rw [ha, hj, canonical2189 B hB]
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

theorem singleton5176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5176 node5176Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2604 node2604Labels + mixedMoment B node3614 node3614Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2214 singletonSmall5176
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5176) = raw2214Labels := by decide +kernel
  rw [hl, canonical2214 B hB] at h
  have hc0 : mixedMoment B raw2214 (Fin.cases (0 : Fin 2) singletonSmall5176) =
      mixedMoment B node2604 node2604Labels := by
    have ha : raw2214 = raw2215 := by apply Matrix.ext; unfold raw2214 raw2215; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5176 = raw2215Labels := by decide +kernel
    rw [ha, hj, canonical2215 B hB]
  have hc1 : mixedMoment B raw2214 (Fin.cases (1 : Fin 2) singletonSmall5176) =
      mixedMoment B node3614 node3614Labels := by
    have ha : raw2214 = raw2216 := by apply Matrix.ext; unfold raw2214 raw2216; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5176 = raw2216Labels := by decide +kernel
    rw [ha, hj, canonical2216 B hB]
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

theorem singleton5294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5294 node5294Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2768 node2768Labels + mixedMoment B node3632 node3632Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2304 singletonSmall5294
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5294) = raw2304Labels := by decide +kernel
  rw [hl, canonical2304 B hB] at h
  have hc0 : mixedMoment B raw2304 (Fin.cases (0 : Fin 2) singletonSmall5294) =
      mixedMoment B node2768 node2768Labels := by
    have ha : raw2304 = raw2305 := by apply Matrix.ext; unfold raw2304 raw2305; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5294 = raw2305Labels := by decide +kernel
    rw [ha, hj, canonical2305 B hB]
  have hc1 : mixedMoment B raw2304 (Fin.cases (1 : Fin 2) singletonSmall5294) =
      mixedMoment B node3632 node3632Labels := by
    have ha : raw2304 = raw2306 := by apply Matrix.ext; unfold raw2304 raw2306; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5294 = raw2306Labels := by decide +kernel
    rw [ha, hj, canonical2306 B hB]
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

theorem zero5442 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5442 node5442Labels = 0 := by
  exact mixedMoment_order_one B hB node5442 node5442Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node929 node929Labels = Sparse.eval nodeValue929 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 929) = mixedMoment B node929 node929Labels := rfl
  simpa [nodeValue929, Sparse.eval] using hc.symm

theorem sound930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node930 node930Labels = Sparse.eval nodeValue930 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 930) = mixedMoment B node930 node930Labels := rfl
  simpa [nodeValue930, Sparse.eval] using hc.symm

theorem sound932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node932 node932Labels = Sparse.eval nodeValue932 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 932) = mixedMoment B node932 node932Labels := rfl
  simpa [nodeValue932, Sparse.eval] using hc.symm

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

theorem sound1044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1044 node1044Labels = Sparse.eval nodeValue1044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1044) = mixedMoment B node1044 node1044Labels := rfl
  simpa [nodeValue1044, Sparse.eval] using hc.symm

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

theorem sound1681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1681 node1681Labels = Sparse.eval nodeValue1681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1681) = mixedMoment B node1681 node1681Labels := rfl
  simpa [nodeValue1681, Sparse.eval] using hc.symm

theorem sound1690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1690 node1690Labels = Sparse.eval nodeValue1690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1690) = mixedMoment B node1690 node1690Labels := rfl
  simpa [nodeValue1690, Sparse.eval] using hc.symm

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

theorem sound1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1737 node1737Labels = Sparse.eval nodeValue1737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1737) = mixedMoment B node1737 node1737Labels := rfl
  simpa [nodeValue1737, Sparse.eval] using hc.symm

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

theorem sound2338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2338 node2338Labels = Sparse.eval nodeValue2338 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2338) = mixedMoment B node2338 node2338Labels := rfl
  simpa [nodeValue2338, Sparse.eval] using hc.symm

theorem sound2339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2339 node2339Labels = Sparse.eval nodeValue2339 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2339) = mixedMoment B node2339 node2339Labels := rfl
  simpa [nodeValue2339, Sparse.eval] using hc.symm

theorem sound2341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2341 node2341Labels = Sparse.eval nodeValue2341 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2341) = mixedMoment B node2341 node2341Labels := rfl
  simpa [nodeValue2341, Sparse.eval] using hc.symm

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

theorem sound2429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2429 node2429Labels = Sparse.eval nodeValue2429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2429) = mixedMoment B node2429 node2429Labels := rfl
  simpa [nodeValue2429, Sparse.eval] using hc.symm

theorem sound2431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2431 node2431Labels = Sparse.eval nodeValue2431 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2431) = mixedMoment B node2431 node2431Labels := rfl
  simpa [nodeValue2431, Sparse.eval] using hc.symm

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

theorem sound2483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2483 node2483Labels = Sparse.eval nodeValue2483 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2483) = mixedMoment B node2483 node2483Labels := rfl
  simpa [nodeValue2483, Sparse.eval] using hc.symm

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

theorem sound343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node343 node343Labels = Sparse.eval nodeValue343 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue343 (familyPairVector B) := singlePair343 B _hB
    _ = _ := by norm_num [singlePairValue343, nodeValue343, Sparse.eval, mixedVector] <;> ring

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

theorem sound2589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2589 node2589Labels = Sparse.eval nodeValue2589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2589) = mixedMoment B node2589 node2589Labels := rfl
  simpa [nodeValue2589, Sparse.eval] using hc.symm

theorem sound2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2590 node2590Labels = Sparse.eval nodeValue2590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2590) = mixedMoment B node2590 node2590Labels := rfl
  simpa [nodeValue2590, Sparse.eval] using hc.symm

theorem sound2604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2604 node2604Labels = Sparse.eval nodeValue2604 (mixedVector B) := by
  have h := singleton2604 B _hB
  rw [sound343 B _hB _hF] at h
  norm_num [nodeValue2604, nodeValue343, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node405 node405Labels = Sparse.eval nodeValue405 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue405 (familyPairVector B) := singlePair405 B _hB
    _ = _ := by
      norm_num [singlePairValue405, nodeValue405, Sparse.eval, mixedVector]
      ring

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

theorem sound2768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2768 node2768Labels = Sparse.eval nodeValue2768 (mixedVector B) := by
  have h := singleton2768 B _hB
  rw [sound405 B _hB _hF] at h
  norm_num [nodeValue2768, nodeValue405, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3416 node3416Labels = Sparse.eval nodeValue3416 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3416) = mixedMoment B node3416 node3416Labels := rfl
  simpa [nodeValue3416, Sparse.eval] using hc.symm

theorem sound3417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3417 node3417Labels = Sparse.eval nodeValue3417 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3417) = mixedMoment B node3417 node3417Labels := rfl
  simpa [nodeValue3417, Sparse.eval] using hc.symm

theorem sound3420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3420 node3420Labels = Sparse.eval nodeValue3420 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3420) = mixedMoment B node3420 node3420Labels := rfl
  simpa [nodeValue3420, Sparse.eval] using hc.symm

theorem sound3453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3453 node3453Labels = Sparse.eval nodeValue3453 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3453) = mixedMoment B node3453 node3453Labels := rfl
  simpa [nodeValue3453, Sparse.eval] using hc.symm

theorem sound3455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3455 node3455Labels = Sparse.eval nodeValue3455 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3455) = mixedMoment B node3455 node3455Labels := rfl
  simpa [nodeValue3455, Sparse.eval] using hc.symm

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

theorem sound3477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3477 node3477Labels = Sparse.eval nodeValue3477 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3477) = mixedMoment B node3477 node3477Labels := rfl
  simpa [nodeValue3477, Sparse.eval] using hc.symm

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

theorem sound3563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3563 node3563Labels = Sparse.eval nodeValue3563 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3563) = mixedMoment B node3563 node3563Labels := rfl
  simpa [nodeValue3563, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3614 node3614Labels = Sparse.eval nodeValue3614 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3614) = mixedMoment B node3614 node3614Labels := rfl
  simpa [nodeValue3614, Sparse.eval] using hc.symm

theorem sound3632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3632 node3632Labels = Sparse.eval nodeValue3632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3632) = mixedMoment B node3632 node3632Labels := rfl
  simpa [nodeValue3632, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4352 node4352Labels = Sparse.eval nodeValue4352 (mixedVector B) := by
  have h := singleton4352 B _hB
  rw [sound930 B _hB _hF, sound1690 B _hB _hF] at h
  norm_num [nodeValue4352, nodeValue930, nodeValue1690, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4354 node4354Labels = Sparse.eval nodeValue4354 (mixedVector B) := by
  have h := singleton4354 B _hB
  rw [sound932 B _hB _hF, sound1681 B _hB _hF] at h
  norm_num [nodeValue4354, nodeValue932, nodeValue1681, Sparse.eval] at h ⊢
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

theorem sound4461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4461 node4461Labels = Sparse.eval nodeValue4461 (mixedVector B) := by
  have h := singleton4461 B _hB
  rw [sound1044 B _hB _hF, sound1737 B _hB _hF] at h
  norm_num [nodeValue4461, nodeValue1044, nodeValue1737, Sparse.eval] at h ⊢
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

theorem sound4947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4947 node4947Labels = Sparse.eval nodeValue4947 (mixedVector B) := by
  have h := singleton4947 B _hB
  rw [sound2338 B _hB _hF, sound3416 B _hB _hF] at h
  norm_num [nodeValue4947, nodeValue2338, nodeValue3416, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4948 node4948Labels = Sparse.eval nodeValue4948 (mixedVector B) := by
  have h := singleton4948 B _hB
  rw [sound2339 B _hB _hF, sound3420 B _hB _hF] at h
  norm_num [nodeValue4948, nodeValue2339, nodeValue3420, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4949 node4949Labels = Sparse.eval nodeValue4949 (mixedVector B) := by
  have h := singleton4949 B _hB
  rw [sound2341 B _hB _hF, sound3417 B _hB _hF] at h
  norm_num [nodeValue4949, nodeValue2341, nodeValue3417, Sparse.eval] at h ⊢
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

theorem sound5037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5037 node5037Labels = Sparse.eval nodeValue5037 (mixedVector B) := by
  have h := singleton5037 B _hB
  rw [sound2429 B _hB _hF, sound3455 B _hB _hF] at h
  norm_num [nodeValue5037, nodeValue2429, nodeValue3455, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5038 node5038Labels = Sparse.eval nodeValue5038 (mixedVector B) := by
  have h := singleton5038 B _hB
  rw [sound2431 B _hB _hF, sound3453 B _hB _hF] at h
  norm_num [nodeValue5038, nodeValue2431, nodeValue3453, Sparse.eval] at h ⊢
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

theorem sound5076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5076 node5076Labels = Sparse.eval nodeValue5076 (mixedVector B) := by
  have h := singleton5076 B _hB
  rw [sound2483 B _hB _hF, sound3477 B _hB _hF] at h
  norm_num [nodeValue5076, nodeValue2483, nodeValue3477, Sparse.eval] at h ⊢
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

theorem sound5162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5162 node5162Labels = Sparse.eval nodeValue5162 (mixedVector B) := by
  have h := singleton5162 B _hB
  rw [sound2589 B _hB _hF, sound3563 B _hB _hF] at h
  norm_num [nodeValue5162, nodeValue2589, nodeValue3563, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5163 node5163Labels = Sparse.eval nodeValue5163 (mixedVector B) := by
  have h := singleton5163 B _hB
  rw [sound2590 B _hB _hF, sound3564 B _hB _hF] at h
  norm_num [nodeValue5163, nodeValue2590, nodeValue3564, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5176 node5176Labels = Sparse.eval nodeValue5176 (mixedVector B) := by
  have h := singleton5176 B _hB
  rw [sound2604 B _hB _hF, sound3614 B _hB _hF] at h
  norm_num [nodeValue5176, nodeValue2604, nodeValue3614, Sparse.eval] at h ⊢
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

theorem sound5294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5294 node5294Labels = Sparse.eval nodeValue5294 (mixedVector B) := by
  have h := singleton5294 B _hB
  rw [sound2768 B _hB _hF, sound3632 B _hB _hF] at h
  norm_num [nodeValue5294, nodeValue2768, nodeValue3632, Sparse.eval] at h ⊢
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

theorem sound5442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5442 node5442Labels = Sparse.eval nodeValue5442 (mixedVector B) := by
  simpa only [nodeValue5442, Sparse.eval_nil] using zero5442 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources73
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2352 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2352 + difference 0 1) (sourceB2352 + difference 1 0) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2352 + difference 0 1) (sourceB2352 + difference 1 0) sourceC2352) = raw17691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw17691; decide +kernel
    rw [ha]
    exact (canonical17691 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2352 + difference 0 2) (sourceB2352 + difference 2 0) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2352 + difference 0 2) (sourceB2352 + difference 2 0) sourceC2352) = raw17692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw17692; decide +kernel
    rw [ha]
    exact (canonical17692 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2352 + difference 0 3) (sourceB2352 + difference 3 0) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA2352 + difference 0 3) (sourceB2352 + difference 3 0) sourceC2352) = raw3055 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw3055; decide +kernel
    rw [ha]
    exact (canonical3055 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2352 + difference 0 4) (sourceB2352 + difference 4 0) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA2352 + difference 0 4) (sourceB2352 + difference 4 0) sourceC2352) = raw17693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw17693; decide +kernel
    rw [ha]
    exact (canonical17693 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2352 + difference 0 5) (sourceB2352 + difference 5 0) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2352 + difference 0 5) (sourceB2352 + difference 5 0) sourceC2352) = raw3045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw3045; decide +kernel
    rw [ha]
    exact (canonical3045 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2352 + difference 1 0) (sourceB2352 + difference 0 1) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA2352 + difference 1 0) (sourceB2352 + difference 0 1) sourceC2352) = raw13591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw13591; decide +kernel
    rw [ha]
    exact (canonical13591 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2352 + difference 1 2) (sourceB2352 + difference 2 1) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA2352 + difference 1 2) (sourceB2352 + difference 2 1) sourceC2352) = raw13593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw13593; decide +kernel
    rw [ha]
    exact (canonical13593 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2352 + difference 1 3) (sourceB2352 + difference 3 1) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA2352 + difference 1 3) (sourceB2352 + difference 3 1) sourceC2352) = raw3054 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw3054; decide +kernel
    rw [ha]
    exact (canonical3054 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2352 + difference 1 4) (sourceB2352 + difference 4 1) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA2352 + difference 1 4) (sourceB2352 + difference 4 1) sourceC2352) = raw13594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw13594; decide +kernel
    rw [ha]
    exact (canonical13594 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2352 + difference 1 5) (sourceB2352 + difference 5 1) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA2352 + difference 1 5) (sourceB2352 + difference 5 1) sourceC2352) = raw3044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw3044; decide +kernel
    rw [ha]
    exact (canonical3044 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2352 + difference 2 0) (sourceB2352 + difference 0 2) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4351) := by
    have ha : (tripleCharges (sourceA2352 + difference 2 0) (sourceB2352 + difference 0 2) sourceC2352) = raw25071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw25071; decide +kernel
    rw [ha]
    exact (canonical25071 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2352 + difference 2 1) (sourceB2352 + difference 1 2) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4947) := by
    have ha : (tripleCharges (sourceA2352 + difference 2 1) (sourceB2352 + difference 1 2) sourceC2352) = raw32201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32201; decide +kernel
    rw [ha]
    exact (canonical32201 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2352 + difference 2 3) (sourceB2352 + difference 3 2) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2352 + difference 2 3) (sourceB2352 + difference 3 2) sourceC2352) = raw17687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw17687; decide +kernel
    rw [ha]
    exact (canonical17687 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2352 + difference 2 4) (sourceB2352 + difference 4 2) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2352 + difference 2 4) (sourceB2352 + difference 4 2) sourceC2352) = raw32202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32202; decide +kernel
    rw [ha]
    exact (canonical32202 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2352 + difference 2 5) (sourceB2352 + difference 5 2) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA2352 + difference 2 5) (sourceB2352 + difference 5 2) sourceC2352) = raw13579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw13579; decide +kernel
    rw [ha]
    exact (canonical13579 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2352 + difference 3 0) (sourceB2352 + difference 0 3) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA2352 + difference 3 0) (sourceB2352 + difference 0 3) sourceC2352) = raw25074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw25074; decide +kernel
    rw [ha]
    exact (canonical25074 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2352 + difference 3 1) (sourceB2352 + difference 1 3) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2352 + difference 3 1) (sourceB2352 + difference 1 3) sourceC2352) = raw32203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32203; decide +kernel
    rw [ha]
    exact (canonical32203 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2352 + difference 3 2) (sourceB2352 + difference 2 3) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5038) := by
    have ha : (tripleCharges (sourceA2352 + difference 3 2) (sourceB2352 + difference 2 3) sourceC2352) = raw32204 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32204; decide +kernel
    rw [ha]
    exact (canonical32204 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2352 + difference 3 4) (sourceB2352 + difference 4 3) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2352 + difference 3 4) (sourceB2352 + difference 4 3) sourceC2352) = raw32205 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32205; decide +kernel
    rw [ha]
    exact (canonical32205 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2352 + difference 3 5) (sourceB2352 + difference 5 3) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2352 + difference 3 5) (sourceB2352 + difference 5 3) sourceC2352) = raw13583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw13583; decide +kernel
    rw [ha]
    exact (canonical13583 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2352 + difference 4 0) (sourceB2352 + difference 0 4) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA2352 + difference 4 0) (sourceB2352 + difference 0 4) sourceC2352) = raw23047 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw23047; decide +kernel
    rw [ha]
    exact (canonical23047 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2352 + difference 4 1) (sourceB2352 + difference 1 4) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2352 + difference 4 1) (sourceB2352 + difference 1 4) sourceC2352) = raw32206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32206; decide +kernel
    rw [ha]
    exact (canonical32206 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2352 + difference 4 2) (sourceB2352 + difference 2 4) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5038) := by
    have ha : (tripleCharges (sourceA2352 + difference 4 2) (sourceB2352 + difference 2 4) sourceC2352) = raw32207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32207; decide +kernel
    rw [ha]
    exact (canonical32207 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2352 + difference 4 3) (sourceB2352 + difference 3 4) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2352 + difference 4 3) (sourceB2352 + difference 3 4) sourceC2352) = raw17694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw17694; decide +kernel
    rw [ha]
    exact (canonical17694 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2352 + difference 4 5) (sourceB2352 + difference 5 4) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2352 + difference 4 5) (sourceB2352 + difference 5 4) sourceC2352) = raw13588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw13588; decide +kernel
    rw [ha]
    exact (canonical13588 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2352 + difference 5 0) (sourceB2352 + difference 0 5) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA2352 + difference 5 0) (sourceB2352 + difference 0 5) sourceC2352) = raw21250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw21250; decide +kernel
    rw [ha]
    exact (canonical21250 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2352 + difference 5 1) (sourceB2352 + difference 1 5) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4948) := by
    have ha : (tripleCharges (sourceA2352 + difference 5 1) (sourceB2352 + difference 1 5) sourceC2352) = raw32208 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32208; decide +kernel
    rw [ha]
    exact (canonical32208 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2352 + difference 5 2) (sourceB2352 + difference 2 5) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5037) := by
    have ha : (tripleCharges (sourceA2352 + difference 5 2) (sourceB2352 + difference 2 5) sourceC2352) = raw32209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32209; decide +kernel
    rw [ha]
    exact (canonical32209 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2352 + difference 5 3) (sourceB2352 + difference 3 5) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA2352 + difference 5 3) (sourceB2352 + difference 3 5) sourceC2352) = raw17698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw17698; decide +kernel
    rw [ha]
    exact (canonical17698 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2352 + difference 5 4) (sourceB2352 + difference 4 5) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA2352 + difference 5 4) (sourceB2352 + difference 4 5) sourceC2352) = raw32210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32210; decide +kernel
    rw [ha]
    exact (canonical32210 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2352 sourceB2352 sourceC2352
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2352, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1916 : Integer.Sparse.reindex keyMap MixedData.row1916 = numericRow1916 := by decide +kernel

theorem numericCheck1916 (x : Master → ℝ) : Integer.Sparse.eval numericRow1916 x =
    (5760 : ℝ) * reducedSource1916 x := by
  norm_num [numericRow1916, reducedSource1916, Integer.Sparse.eval, Sparse.eval, nodeValue4351, nodeValue4352, nodeValue4354, nodeValue4461, nodeValue4947, nodeValue4948, nodeValue4949, nodeValue5037, nodeValue5038, nodeValue5076, nodeValue5162, nodeValue5163, nodeValue5172, nodeValue5174, nodeValue5176, nodeValue5290, nodeValue5294, nodeValue5416, nodeValue5418, nodeValue5442, nodeValue5485]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1916 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1916 (mixedVector B) = 0 := by
  have h4351 : mixedVector B (Sum.inr 4351) = Sparse.eval nodeValue4351 (mixedVector B) := by
    change mixedMoment B node4351 node4351Labels = _
    exact sound4351 B hB hF
  have h4352 : mixedVector B (Sum.inr 4352) = Sparse.eval nodeValue4352 (mixedVector B) := by
    change mixedMoment B node4352 node4352Labels = _
    exact sound4352 B hB hF
  have h4354 : mixedVector B (Sum.inr 4354) = Sparse.eval nodeValue4354 (mixedVector B) := by
    change mixedMoment B node4354 node4354Labels = _
    exact sound4354 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4947 : mixedVector B (Sum.inr 4947) = Sparse.eval nodeValue4947 (mixedVector B) := by
    change mixedMoment B node4947 node4947Labels = _
    exact sound4947 B hB hF
  have h4948 : mixedVector B (Sum.inr 4948) = Sparse.eval nodeValue4948 (mixedVector B) := by
    change mixedMoment B node4948 node4948Labels = _
    exact sound4948 B hB hF
  have h4949 : mixedVector B (Sum.inr 4949) = Sparse.eval nodeValue4949 (mixedVector B) := by
    change mixedMoment B node4949 node4949Labels = _
    exact sound4949 B hB hF
  have h5037 : mixedVector B (Sum.inr 5037) = Sparse.eval nodeValue5037 (mixedVector B) := by
    change mixedMoment B node5037 node5037Labels = _
    exact sound5037 B hB hF
  have h5038 : mixedVector B (Sum.inr 5038) = Sparse.eval nodeValue5038 (mixedVector B) := by
    change mixedMoment B node5038 node5038Labels = _
    exact sound5038 B hB hF
  have h5076 : mixedVector B (Sum.inr 5076) = Sparse.eval nodeValue5076 (mixedVector B) := by
    change mixedMoment B node5076 node5076Labels = _
    exact sound5076 B hB hF
  have h5162 : mixedVector B (Sum.inr 5162) = Sparse.eval nodeValue5162 (mixedVector B) := by
    change mixedMoment B node5162 node5162Labels = _
    exact sound5162 B hB hF
  have h5163 : mixedVector B (Sum.inr 5163) = Sparse.eval nodeValue5163 (mixedVector B) := by
    change mixedMoment B node5163 node5163Labels = _
    exact sound5163 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172_e B hB hF
  have h5174 : mixedVector B (Sum.inr 5174) = Sparse.eval nodeValue5174 (mixedVector B) := by
    change mixedMoment B node5174 node5174Labels = _
    exact sound5174_e B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5416 : mixedVector B (Sum.inr 5416) = Sparse.eval nodeValue5416 (mixedVector B) := by
    change mixedMoment B node5416 node5416Labels = _
    exact sound5416_e B hB hF
  have h5418 : mixedVector B (Sum.inr 5418) = Sparse.eval nodeValue5418 (mixedVector B) := by
    change mixedMoment B node5418 node5418Labels = _
    exact sound5418_e B hB hF
  have h5442 : mixedVector B (Sum.inr 5442) = Sparse.eval nodeValue5442 (mixedVector B) := by
    change mixedMoment B node5442 node5442Labels = _
    exact sound5442 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485_e B hB hF
  simpa only [sourceForm2352, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4351, h4352, h4354, h4461, h4947, h4948, h4949, h5037, h5038, h5076, h5162, h5163, h5172, h5174, h5176, h5290, h5294, h5416, h5418, h5442, h5485, reducedSource1916] using sourceEq2352 B hB

theorem rowSound1916_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1916 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1916, numericCheck1916, reducedZero1916 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e_oai
