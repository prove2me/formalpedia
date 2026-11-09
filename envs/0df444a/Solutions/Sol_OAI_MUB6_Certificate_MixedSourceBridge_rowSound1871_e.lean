-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:37:57.827603+00:00
-- url     : https://prove2.me/submissions/6d00b7f0-8986-4244-a771-a929322b6a71

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5418_e
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1485 raw1485Labels = mixedMoment B node4635 node4635Labels := by
  calc
    mixedMoment B raw1485 raw1485Labels = mixedMoment B raw1485step0 raw1485step0Labels := by
      have ha : raw1485step0 = (fun i j => raw1485 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1485step0 raw1485; decide +kernel
      have hl : raw1485step0Labels = raw1485Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1485 raw1485Labels permutation152 permutation4
    mixedMoment B raw1485step0 raw1485step0Labels = mixedMoment B raw1485step1 raw1485step1Labels := by
      have ha : raw1485step1 = raw1485step0 := by apply Matrix.ext; unfold raw1485step1 raw1485step0; decide +kernel
      have hl : raw1485step0Labels = labelEmbedding7 ∘ raw1485step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1485step0 raw1485step0Labels raw1485step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4635 node4635Labels := by rfl

theorem canonical1486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1486 raw1486Labels = mixedMoment B node1764 node1764Labels := by
  calc
    mixedMoment B raw1486 raw1486Labels = mixedMoment B raw1486step0 raw1486step0Labels := by
      have ha : raw1486step0 = (fun i j => raw1486 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1486step0 raw1486; decide +kernel
      have hl : raw1486step0Labels = raw1486Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1486 raw1486Labels permutation152 permutation4
    _ = mixedMoment B node1764 node1764Labels := by rfl

theorem canonical1487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1487 raw1487Labels = mixedMoment B node1848 node1848Labels := by
  calc
    mixedMoment B raw1487 raw1487Labels = mixedMoment B raw1487step0 raw1487step0Labels := by
      have ha : raw1487step0 = (fun i j => raw1487 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1487step0 raw1487; decide +kernel
      have hl : raw1487step0Labels = raw1487Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1487 raw1487Labels permutation152 permutation6
    mixedMoment B raw1487step0 raw1487step0Labels = mixedMoment B raw1487step1 raw1487step1Labels := by
      have ha : raw1487step1 = -raw1487step0 := by apply Matrix.ext; change ∀ i j, raw1487step1 i j = -(raw1487step0 i j); unfold raw1487step1 raw1487step0; decide +kernel
      have hl : raw1487step1Labels = raw1487step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1487step1 raw1487step1Labels = mixedMoment B raw1487step2 raw1487step2Labels := by
      have ha : raw1487step2 = raw1487step1 := by apply Matrix.ext; unfold raw1487step2 raw1487step1; decide +kernel
      have hl : raw1487step1Labels = labelEmbedding1 ∘ raw1487step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1487step1 raw1487step1Labels raw1487step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1848 node1848Labels := by rfl

theorem canonical1491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1491 raw1491Labels = mixedMoment B node4637 node4637Labels := by
  calc
    mixedMoment B raw1491 raw1491Labels = mixedMoment B raw1491step0 raw1491step0Labels := by
      have ha : raw1491step0 = (fun i j => raw1491 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1491step0 raw1491; decide +kernel
      have hl : raw1491step0Labels = raw1491Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1491 raw1491Labels permutation32 permutation4
    mixedMoment B raw1491step0 raw1491step0Labels = mixedMoment B raw1491step1 raw1491step1Labels := by
      have ha : raw1491step1 = raw1491step0 := by apply Matrix.ext; unfold raw1491step1 raw1491step0; decide +kernel
      have hl : raw1491step0Labels = labelEmbedding7 ∘ raw1491step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1491step0 raw1491step0Labels raw1491step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4637 node4637Labels := by rfl

theorem canonical1492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1492 raw1492Labels = mixedMoment B node1766 node1766Labels := by
  calc
    mixedMoment B raw1492 raw1492Labels = mixedMoment B raw1492step0 raw1492step0Labels := by
      have ha : raw1492step0 = (fun i j => raw1492 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1492step0 raw1492; decide +kernel
      have hl : raw1492step0Labels = raw1492Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1492 raw1492Labels permutation32 permutation4
    _ = mixedMoment B node1766 node1766Labels := by rfl

theorem canonical1493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1493 raw1493Labels = mixedMoment B node1850 node1850Labels := by
  calc
    mixedMoment B raw1493 raw1493Labels = mixedMoment B raw1493step0 raw1493step0Labels := by
      have ha : raw1493step0 = (fun i j => raw1493 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1493step0 raw1493; decide +kernel
      have hl : raw1493step0Labels = raw1493Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1493 raw1493Labels permutation32 permutation6
    mixedMoment B raw1493step0 raw1493step0Labels = mixedMoment B raw1493step1 raw1493step1Labels := by
      have ha : raw1493step1 = -raw1493step0 := by apply Matrix.ext; change ∀ i j, raw1493step1 i j = -(raw1493step0 i j); unfold raw1493step1 raw1493step0; decide +kernel
      have hl : raw1493step1Labels = raw1493step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1493step1 raw1493step1Labels = mixedMoment B raw1493step2 raw1493step2Labels := by
      have ha : raw1493step2 = raw1493step1 := by apply Matrix.ext; unfold raw1493step2 raw1493step1; decide +kernel
      have hl : raw1493step1Labels = labelEmbedding1 ∘ raw1493step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1493step1 raw1493step1Labels raw1493step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1850 node1850Labels := by rfl

theorem canonical1524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1524 raw1524Labels = mixedMoment B node4654 node4654Labels := by
  calc
    mixedMoment B raw1524 raw1524Labels = mixedMoment B raw1524step0 raw1524step0Labels := by
      have ha : raw1524step0 = (fun i j => raw1524 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1524step0 raw1524; decide +kernel
      have hl : raw1524step0Labels = raw1524Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1524 raw1524Labels permutation32 permutation4
    mixedMoment B raw1524step0 raw1524step0Labels = mixedMoment B raw1524step1 raw1524step1Labels := by
      have ha : raw1524step1 = raw1524step0 := by apply Matrix.ext; unfold raw1524step1 raw1524step0; decide +kernel
      have hl : raw1524step0Labels = labelEmbedding7 ∘ raw1524step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1524step0 raw1524step0Labels raw1524step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4654 node4654Labels := by rfl

theorem canonical1525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1525 raw1525Labels = mixedMoment B node1782 node1782Labels := by
  calc
    mixedMoment B raw1525 raw1525Labels = mixedMoment B raw1525step0 raw1525step0Labels := by
      have ha : raw1525step0 = (fun i j => raw1525 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1525step0 raw1525; decide +kernel
      have hl : raw1525step0Labels = raw1525Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1525 raw1525Labels permutation32 permutation4
    _ = mixedMoment B node1782 node1782Labels := by rfl

theorem canonical1526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1526 raw1526Labels = mixedMoment B node1855 node1855Labels := by
  calc
    mixedMoment B raw1526 raw1526Labels = mixedMoment B raw1526step0 raw1526step0Labels := by
      have ha : raw1526step0 = (fun i j => raw1526 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1526step0 raw1526; decide +kernel
      have hl : raw1526step0Labels = raw1526Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1526 raw1526Labels permutation35 permutation6
    mixedMoment B raw1526step0 raw1526step0Labels = mixedMoment B raw1526step1 raw1526step1Labels := by
      have ha : raw1526step1 = -raw1526step0 := by apply Matrix.ext; change ∀ i j, raw1526step1 i j = -(raw1526step0 i j); unfold raw1526step1 raw1526step0; decide +kernel
      have hl : raw1526step1Labels = raw1526step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1526step1 raw1526step1Labels = mixedMoment B raw1526step2 raw1526step2Labels := by
      have ha : raw1526step2 = raw1526step1 := by apply Matrix.ext; unfold raw1526step2 raw1526step1; decide +kernel
      have hl : raw1526step1Labels = labelEmbedding1 ∘ raw1526step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1526step1 raw1526step1Labels raw1526step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1855 node1855Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14326 raw14326Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw14326 raw14326Labels = mixedMoment B raw14326step0 raw14326step0Labels := by
      have ha : raw14326step0 = (fun i j => raw14326 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14326step0 raw14326; decide +kernel
      have hl : raw14326step0Labels = raw14326Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14326 raw14326Labels permutation156 permutation3
    mixedMoment B raw14326step0 raw14326step0Labels = mixedMoment B raw14326step1 raw14326step1Labels := by
      have ha : raw14326step1 = raw14326step0 := by apply Matrix.ext; unfold raw14326step1 raw14326step0; decide +kernel
      have hl : raw14326step0Labels = labelEmbedding6 ∘ raw14326step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14326step0 raw14326step0Labels raw14326step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical14329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14329 raw14329Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw14329 raw14329Labels = mixedMoment B raw14329step0 raw14329step0Labels := by
      have hz : ∀ j, raw14329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14329step0 = (fun i j => raw14329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14329step0 raw14329; decide +kernel
      have hl : raw14329step0Labels = raw14329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14329 raw14329Labels permutation434 hz
    mixedMoment B raw14329step0 raw14329step0Labels = mixedMoment B raw14329step1 raw14329step1Labels := by
      have ha : raw14329step1 = (fun i j => raw14329step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14329step1 raw14329step0; decide +kernel
      have hl : raw14329step1Labels = raw14329step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14329step0 raw14329step0Labels permutation32 permutation3
    mixedMoment B raw14329step1 raw14329step1Labels = mixedMoment B raw14329step2 raw14329step2Labels := by
      have ha : raw14329step2 = raw14329step1 := by apply Matrix.ext; unfold raw14329step2 raw14329step1; decide +kernel
      have hl : raw14329step1Labels = labelEmbedding6 ∘ raw14329step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14329step1 raw14329step1Labels raw14329step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical1590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1590 raw1590Labels = mixedMoment B node4706 node4706Labels := by
  calc
    mixedMoment B raw1590 raw1590Labels = mixedMoment B raw1590step0 raw1590step0Labels := by
      have ha : raw1590step0 = (fun i j => raw1590 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1590step0 raw1590; decide +kernel
      have hl : raw1590step0Labels = raw1590Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1590 raw1590Labels permutation152 permutation4
    mixedMoment B raw1590step0 raw1590step0Labels = mixedMoment B raw1590step1 raw1590step1Labels := by
      have ha : raw1590step1 = raw1590step0 := by apply Matrix.ext; unfold raw1590step1 raw1590step0; decide +kernel
      have hl : raw1590step0Labels = labelEmbedding7 ∘ raw1590step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1590step0 raw1590step0Labels raw1590step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4706 node4706Labels := by rfl

theorem canonical1591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1591 raw1591Labels = mixedMoment B node1860 node1860Labels := by
  calc
    mixedMoment B raw1591 raw1591Labels = mixedMoment B raw1591step0 raw1591step0Labels := by
      have ha : raw1591step0 = (fun i j => raw1591 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1591step0 raw1591; decide +kernel
      have hl : raw1591step0Labels = raw1591Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1591 raw1591Labels permutation152 permutation4
    _ = mixedMoment B node1860 node1860Labels := by rfl

theorem canonical1592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1592 raw1592Labels = mixedMoment B node1888 node1888Labels := by
  calc
    mixedMoment B raw1592 raw1592Labels = mixedMoment B raw1592step0 raw1592step0Labels := by
      have ha : raw1592step0 = (fun i j => raw1592 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1592step0 raw1592; decide +kernel
      have hl : raw1592step0Labels = raw1592Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1592 raw1592Labels permutation152 permutation6
    mixedMoment B raw1592step0 raw1592step0Labels = mixedMoment B raw1592step1 raw1592step1Labels := by
      have ha : raw1592step1 = -raw1592step0 := by apply Matrix.ext; change ∀ i j, raw1592step1 i j = -(raw1592step0 i j); unfold raw1592step1 raw1592step0; decide +kernel
      have hl : raw1592step1Labels = raw1592step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1592step1 raw1592step1Labels = mixedMoment B raw1592step2 raw1592step2Labels := by
      have ha : raw1592step2 = raw1592step1 := by apply Matrix.ext; unfold raw1592step2 raw1592step1; decide +kernel
      have hl : raw1592step1Labels = labelEmbedding1 ∘ raw1592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1592step1 raw1592step1Labels raw1592step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1888 node1888Labels := by rfl

theorem canonical1611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1611 raw1611Labels = mixedMoment B node4717 node4717Labels := by
  calc
    mixedMoment B raw1611 raw1611Labels = mixedMoment B raw1611step0 raw1611step0Labels := by
      have ha : raw1611step0 = (fun i j => raw1611 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1611step0 raw1611; decide +kernel
      have hl : raw1611step0Labels = raw1611Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1611 raw1611Labels permutation152 permutation4
    mixedMoment B raw1611step0 raw1611step0Labels = mixedMoment B raw1611step1 raw1611step1Labels := by
      have ha : raw1611step1 = raw1611step0 := by apply Matrix.ext; unfold raw1611step1 raw1611step0; decide +kernel
      have hl : raw1611step0Labels = labelEmbedding7 ∘ raw1611step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1611step0 raw1611step0Labels raw1611step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4717 node4717Labels := by rfl

theorem canonical1612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1612 raw1612Labels = mixedMoment B node1871 node1871Labels := by
  calc
    mixedMoment B raw1612 raw1612Labels = mixedMoment B raw1612step0 raw1612step0Labels := by
      have ha : raw1612step0 = (fun i j => raw1612 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1612step0 raw1612; decide +kernel
      have hl : raw1612step0Labels = raw1612Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1612 raw1612Labels permutation152 permutation4
    _ = mixedMoment B node1871 node1871Labels := by rfl

theorem canonical1613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1613 raw1613Labels = mixedMoment B node1892 node1892Labels := by
  calc
    mixedMoment B raw1613 raw1613Labels = mixedMoment B raw1613step0 raw1613step0Labels := by
      have ha : raw1613step0 = (fun i j => raw1613 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1613step0 raw1613; decide +kernel
      have hl : raw1613step0Labels = raw1613Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1613 raw1613Labels permutation155 permutation6
    mixedMoment B raw1613step0 raw1613step0Labels = mixedMoment B raw1613step1 raw1613step1Labels := by
      have ha : raw1613step1 = -raw1613step0 := by apply Matrix.ext; change ∀ i j, raw1613step1 i j = -(raw1613step0 i j); unfold raw1613step1 raw1613step0; decide +kernel
      have hl : raw1613step1Labels = raw1613step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1613step1 raw1613step1Labels = mixedMoment B raw1613step2 raw1613step2Labels := by
      have ha : raw1613step2 = raw1613step1 := by apply Matrix.ext; unfold raw1613step2 raw1613step1; decide +kernel
      have hl : raw1613step1Labels = labelEmbedding1 ∘ raw1613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1613step1 raw1613step1Labels raw1613step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1892 node1892Labels := by rfl

theorem canonical1650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1650 raw1650Labels = mixedMoment B node4732 node4732Labels := by
  calc
    mixedMoment B raw1650 raw1650Labels = mixedMoment B raw1650step0 raw1650step0Labels := by
      have ha : raw1650step0 = (fun i j => raw1650 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1650step0 raw1650; decide +kernel
      have hl : raw1650step0Labels = raw1650Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1650 raw1650Labels permutation152 permutation4
    mixedMoment B raw1650step0 raw1650step0Labels = mixedMoment B raw1650step1 raw1650step1Labels := by
      have ha : raw1650step1 = raw1650step0 := by apply Matrix.ext; unfold raw1650step1 raw1650step0; decide +kernel
      have hl : raw1650step0Labels = labelEmbedding7 ∘ raw1650step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1650step0 raw1650step0Labels raw1650step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4732 node4732Labels := by rfl

theorem canonical1651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1651 raw1651Labels = mixedMoment B node1901 node1901Labels := by
  calc
    mixedMoment B raw1651 raw1651Labels = mixedMoment B raw1651step0 raw1651step0Labels := by
      have ha : raw1651step0 = (fun i j => raw1651 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1651step0 raw1651; decide +kernel
      have hl : raw1651step0Labels = raw1651Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1651 raw1651Labels permutation152 permutation4
    _ = mixedMoment B node1901 node1901Labels := by rfl

theorem canonical1652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1652 raw1652Labels = mixedMoment B node1941 node1941Labels := by
  calc
    mixedMoment B raw1652 raw1652Labels = mixedMoment B raw1652step0 raw1652step0Labels := by
      have ha : raw1652step0 = (fun i j => raw1652 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1652step0 raw1652; decide +kernel
      have hl : raw1652step0Labels = raw1652Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1652 raw1652Labels permutation152 permutation6
    mixedMoment B raw1652step0 raw1652step0Labels = mixedMoment B raw1652step1 raw1652step1Labels := by
      have ha : raw1652step1 = -raw1652step0 := by apply Matrix.ext; change ∀ i j, raw1652step1 i j = -(raw1652step0 i j); unfold raw1652step1 raw1652step0; decide +kernel
      have hl : raw1652step1Labels = raw1652step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1652step1 raw1652step1Labels = mixedMoment B raw1652step2 raw1652step2Labels := by
      have ha : raw1652step2 = raw1652step1 := by apply Matrix.ext; unfold raw1652step2 raw1652step1; decide +kernel
      have hl : raw1652step1Labels = labelEmbedding1 ∘ raw1652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1652step1 raw1652step1Labels raw1652step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1941 node1941Labels := by rfl

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

theorem canonical1701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1701 raw1701Labels = mixedMoment B node4767 node4767Labels := by
  calc
    mixedMoment B raw1701 raw1701Labels = mixedMoment B raw1701step0 raw1701step0Labels := by
      have ha : raw1701step0 = (fun i j => raw1701 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1701step0 raw1701; decide +kernel
      have hl : raw1701step0Labels = raw1701Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1701 raw1701Labels permutation152 permutation4
    mixedMoment B raw1701step0 raw1701step0Labels = mixedMoment B raw1701step1 raw1701step1Labels := by
      have ha : raw1701step1 = raw1701step0 := by apply Matrix.ext; unfold raw1701step1 raw1701step0; decide +kernel
      have hl : raw1701step0Labels = labelEmbedding7 ∘ raw1701step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1701step0 raw1701step0Labels raw1701step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4767 node4767Labels := by rfl

theorem canonical1702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1702 raw1702Labels = mixedMoment B node1967 node1967Labels := by
  calc
    mixedMoment B raw1702 raw1702Labels = mixedMoment B raw1702step0 raw1702step0Labels := by
      have ha : raw1702step0 = (fun i j => raw1702 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1702step0 raw1702; decide +kernel
      have hl : raw1702step0Labels = raw1702Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1702 raw1702Labels permutation152 permutation4
    _ = mixedMoment B node1967 node1967Labels := by rfl

theorem canonical1703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1703 raw1703Labels = mixedMoment B node2183 node2183Labels := by
  calc
    mixedMoment B raw1703 raw1703Labels = mixedMoment B raw1703step0 raw1703step0Labels := by
      have ha : raw1703step0 = (fun i j => raw1703 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1703step0 raw1703; decide +kernel
      have hl : raw1703step0Labels = raw1703Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1703 raw1703Labels permutation152 permutation6
    mixedMoment B raw1703step0 raw1703step0Labels = mixedMoment B raw1703step1 raw1703step1Labels := by
      have ha : raw1703step1 = -raw1703step0 := by apply Matrix.ext; change ∀ i j, raw1703step1 i j = -(raw1703step0 i j); unfold raw1703step1 raw1703step0; decide +kernel
      have hl : raw1703step1Labels = raw1703step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1703step1 raw1703step1Labels = mixedMoment B raw1703step2 raw1703step2Labels := by
      have ha : raw1703step2 = raw1703step1 := by apply Matrix.ext; unfold raw1703step2 raw1703step1; decide +kernel
      have hl : raw1703step1Labels = labelEmbedding1 ∘ raw1703step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1703step1 raw1703step1Labels raw1703step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2183 node2183Labels := by rfl

theorem canonical1704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1704 raw1704Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw1704 raw1704Labels = mixedMoment B raw1704step0 raw1704step0Labels := by
      have ha : raw1704step0 = (fun i j => raw1704 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1704step0 raw1704; decide +kernel
      have hl : raw1704step0Labels = raw1704Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1704 raw1704Labels permutation32 permutation4
    mixedMoment B raw1704step0 raw1704step0Labels = mixedMoment B raw1704step1 raw1704step1Labels := by
      have ha : raw1704step1 = raw1704step0 := by apply Matrix.ext; unfold raw1704step1 raw1704step0; decide +kernel
      have hl : raw1704step0Labels = labelEmbedding7 ∘ raw1704step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1704step0 raw1704step0Labels raw1704step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4769 node4769Labels := by rfl

theorem canonical1705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1705 raw1705Labels = mixedMoment B node1969 node1969Labels := by
  calc
    mixedMoment B raw1705 raw1705Labels = mixedMoment B raw1705step0 raw1705step0Labels := by
      have ha : raw1705step0 = (fun i j => raw1705 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1705step0 raw1705; decide +kernel
      have hl : raw1705step0Labels = raw1705Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1705 raw1705Labels permutation32 permutation4
    _ = mixedMoment B node1969 node1969Labels := by rfl

theorem canonical1706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1706 raw1706Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw1706 raw1706Labels = mixedMoment B raw1706step0 raw1706step0Labels := by
      have ha : raw1706step0 = (fun i j => raw1706 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1706step0 raw1706; decide +kernel
      have hl : raw1706step0Labels = raw1706Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1706 raw1706Labels permutation32 permutation6
    mixedMoment B raw1706step0 raw1706step0Labels = mixedMoment B raw1706step1 raw1706step1Labels := by
      have ha : raw1706step1 = -raw1706step0 := by apply Matrix.ext; change ∀ i j, raw1706step1 i j = -(raw1706step0 i j); unfold raw1706step1 raw1706step0; decide +kernel
      have hl : raw1706step1Labels = raw1706step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1706step1 raw1706step1Labels = mixedMoment B raw1706step2 raw1706step2Labels := by
      have ha : raw1706step2 = raw1706step1 := by apply Matrix.ext; unfold raw1706step2 raw1706step1; decide +kernel
      have hl : raw1706step1Labels = labelEmbedding1 ∘ raw1706step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1706step1 raw1706step1Labels raw1706step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

theorem canonical1734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1734 raw1734Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw1734 raw1734Labels = mixedMoment B raw1734step0 raw1734step0Labels := by
      have ha : raw1734step0 = (fun i j => raw1734 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1734step0 raw1734; decide +kernel
      have hl : raw1734step0Labels = raw1734Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1734 raw1734Labels permutation152 permutation4
    mixedMoment B raw1734step0 raw1734step0Labels = mixedMoment B raw1734step1 raw1734step1Labels := by
      have ha : raw1734step1 = raw1734step0 := by apply Matrix.ext; unfold raw1734step1 raw1734step0; decide +kernel
      have hl : raw1734step0Labels = labelEmbedding7 ∘ raw1734step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1734step0 raw1734step0Labels raw1734step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical1735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1735 raw1735Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw1735 raw1735Labels = mixedMoment B raw1735step0 raw1735step0Labels := by
      have ha : raw1735step0 = (fun i j => raw1735 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1735step0 raw1735; decide +kernel
      have hl : raw1735step0Labels = raw1735Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1735 raw1735Labels permutation152 permutation4
    _ = mixedMoment B node2020 node2020Labels := by rfl

theorem canonical1736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1736 raw1736Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw1736 raw1736Labels = mixedMoment B raw1736step0 raw1736step0Labels := by
      have ha : raw1736step0 = (fun i j => raw1736 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1736step0 raw1736; decide +kernel
      have hl : raw1736step0Labels = raw1736Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1736 raw1736Labels permutation158 permutation6
    mixedMoment B raw1736step0 raw1736step0Labels = mixedMoment B raw1736step1 raw1736step1Labels := by
      have ha : raw1736step1 = -raw1736step0 := by apply Matrix.ext; change ∀ i j, raw1736step1 i j = -(raw1736step0 i j); unfold raw1736step1 raw1736step0; decide +kernel
      have hl : raw1736step1Labels = raw1736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1736step1 raw1736step1Labels = mixedMoment B raw1736step2 raw1736step2Labels := by
      have ha : raw1736step2 = raw1736step1 := by apply Matrix.ext; unfold raw1736step2 raw1736step1; decide +kernel
      have hl : raw1736step1Labels = labelEmbedding1 ∘ raw1736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1736step1 raw1736step1Labels raw1736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1737 raw1737Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw1737 raw1737Labels = mixedMoment B raw1737step0 raw1737step0Labels := by
      have ha : raw1737step0 = (fun i j => raw1737 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1737step0 raw1737; decide +kernel
      have hl : raw1737step0Labels = raw1737Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1737 raw1737Labels permutation32 permutation4
    mixedMoment B raw1737step0 raw1737step0Labels = mixedMoment B raw1737step1 raw1737step1Labels := by
      have ha : raw1737step1 = raw1737step0 := by apply Matrix.ext; unfold raw1737step1 raw1737step0; decide +kernel
      have hl : raw1737step0Labels = labelEmbedding7 ∘ raw1737step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1737step0 raw1737step0Labels raw1737step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical1738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1738 raw1738Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw1738 raw1738Labels = mixedMoment B raw1738step0 raw1738step0Labels := by
      have ha : raw1738step0 = (fun i j => raw1738 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1738step0 raw1738; decide +kernel
      have hl : raw1738step0Labels = raw1738Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1738 raw1738Labels permutation32 permutation4
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1739 raw1739Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw1739 raw1739Labels = mixedMoment B raw1739step0 raw1739step0Labels := by
      have ha : raw1739step0 = (fun i j => raw1739 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1739step0 raw1739; decide +kernel
      have hl : raw1739step0Labels = raw1739Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1739 raw1739Labels permutation34 permutation6
    mixedMoment B raw1739step0 raw1739step0Labels = mixedMoment B raw1739step1 raw1739step1Labels := by
      have ha : raw1739step1 = -raw1739step0 := by apply Matrix.ext; change ∀ i j, raw1739step1 i j = -(raw1739step0 i j); unfold raw1739step1 raw1739step0; decide +kernel
      have hl : raw1739step1Labels = raw1739step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1739step1 raw1739step1Labels = mixedMoment B raw1739step2 raw1739step2Labels := by
      have ha : raw1739step2 = raw1739step1 := by apply Matrix.ext; unfold raw1739step2 raw1739step1; decide +kernel
      have hl : raw1739step1Labels = labelEmbedding1 ∘ raw1739step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1739step1 raw1739step1Labels raw1739step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical1749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1749 raw1749Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw1749 raw1749Labels = mixedMoment B raw1749step0 raw1749step0Labels := by
      have ha : raw1749step0 = (fun i j => raw1749 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1749step0 raw1749; decide +kernel
      have hl : raw1749step0Labels = raw1749Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1749 raw1749Labels permutation32 permutation4
    mixedMoment B raw1749step0 raw1749step0Labels = mixedMoment B raw1749step1 raw1749step1Labels := by
      have ha : raw1749step1 = raw1749step0 := by apply Matrix.ext; unfold raw1749step1 raw1749step0; decide +kernel
      have hl : raw1749step0Labels = labelEmbedding7 ∘ raw1749step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1749step0 raw1749step0Labels raw1749step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1750 raw1750Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw1750 raw1750Labels = mixedMoment B raw1750step0 raw1750step0Labels := by
      have ha : raw1750step0 = (fun i j => raw1750 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1750step0 raw1750; decide +kernel
      have hl : raw1750step0Labels = raw1750Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1750 raw1750Labels permutation32 permutation4
    _ = mixedMoment B node2029 node2029Labels := by rfl

theorem canonical1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1751 raw1751Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw1751 raw1751Labels = mixedMoment B raw1751step0 raw1751step0Labels := by
      have ha : raw1751step0 = (fun i j => raw1751 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1751step0 raw1751; decide +kernel
      have hl : raw1751step0Labels = raw1751Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1751 raw1751Labels permutation32 permutation6
    mixedMoment B raw1751step0 raw1751step0Labels = mixedMoment B raw1751step1 raw1751step1Labels := by
      have ha : raw1751step1 = -raw1751step0 := by apply Matrix.ext; change ∀ i j, raw1751step1 i j = -(raw1751step0 i j); unfold raw1751step1 raw1751step0; decide +kernel
      have hl : raw1751step1Labels = raw1751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1751step1 raw1751step1Labels = mixedMoment B raw1751step2 raw1751step2Labels := by
      have ha : raw1751step2 = raw1751step1 := by apply Matrix.ext; unfold raw1751step2 raw1751step1; decide +kernel
      have hl : raw1751step1Labels = labelEmbedding1 ∘ raw1751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1751step1 raw1751step1Labels raw1751step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

theorem canonical1767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1767 raw1767Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw1767 raw1767Labels = mixedMoment B raw1767step0 raw1767step0Labels := by
      have ha : raw1767step0 = (fun i j => raw1767 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1767step0 raw1767; decide +kernel
      have hl : raw1767step0Labels = raw1767Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1767 raw1767Labels permutation32 permutation4
    mixedMoment B raw1767step0 raw1767step0Labels = mixedMoment B raw1767step1 raw1767step1Labels := by
      have ha : raw1767step1 = raw1767step0 := by apply Matrix.ext; unfold raw1767step1 raw1767step0; decide +kernel
      have hl : raw1767step0Labels = labelEmbedding7 ∘ raw1767step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1767step0 raw1767step0Labels raw1767step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical1768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1768 raw1768Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw1768 raw1768Labels = mixedMoment B raw1768step0 raw1768step0Labels := by
      have ha : raw1768step0 = (fun i j => raw1768 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1768step0 raw1768; decide +kernel
      have hl : raw1768step0Labels = raw1768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1768 raw1768Labels permutation32 permutation4
    _ = mixedMoment B node2054 node2054Labels := by rfl

theorem canonical1769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1769 raw1769Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw1769 raw1769Labels = mixedMoment B raw1769step0 raw1769step0Labels := by
      have ha : raw1769step0 = (fun i j => raw1769 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1769step0 raw1769; decide +kernel
      have hl : raw1769step0Labels = raw1769Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1769 raw1769Labels permutation33 permutation6
    mixedMoment B raw1769step0 raw1769step0Labels = mixedMoment B raw1769step1 raw1769step1Labels := by
      have ha : raw1769step1 = -raw1769step0 := by apply Matrix.ext; change ∀ i j, raw1769step1 i j = -(raw1769step0 i j); unfold raw1769step1 raw1769step0; decide +kernel
      have hl : raw1769step1Labels = raw1769step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1769step1 raw1769step1Labels = mixedMoment B raw1769step2 raw1769step2Labels := by
      have ha : raw1769step2 = raw1769step1 := by apply Matrix.ext; unfold raw1769step2 raw1769step1; decide +kernel
      have hl : raw1769step1Labels = labelEmbedding1 ∘ raw1769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1769step1 raw1769step1Labels raw1769step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

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

theorem canonical1815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1815 raw1815Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw1815 raw1815Labels = mixedMoment B raw1815step0 raw1815step0Labels := by
      have ha : raw1815step0 = (fun i j => raw1815 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1815step0 raw1815; decide +kernel
      have hl : raw1815step0Labels = raw1815Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1815 raw1815Labels permutation32 permutation4
    mixedMoment B raw1815step0 raw1815step0Labels = mixedMoment B raw1815step1 raw1815step1Labels := by
      have ha : raw1815step1 = raw1815step0 := by apply Matrix.ext; unfold raw1815step1 raw1815step0; decide +kernel
      have hl : raw1815step0Labels = labelEmbedding7 ∘ raw1815step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1815step0 raw1815step0Labels raw1815step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical1816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1816 raw1816Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw1816 raw1816Labels = mixedMoment B raw1816step0 raw1816step0Labels := by
      have ha : raw1816step0 = (fun i j => raw1816 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1816step0 raw1816; decide +kernel
      have hl : raw1816step0Labels = raw1816Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1816 raw1816Labels permutation32 permutation4
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical1817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1817 raw1817Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw1817 raw1817Labels = mixedMoment B raw1817step0 raw1817step0Labels := by
      have ha : raw1817step0 = (fun i j => raw1817 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1817step0 raw1817; decide +kernel
      have hl : raw1817step0Labels = raw1817Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1817 raw1817Labels permutation44 permutation6
    mixedMoment B raw1817step0 raw1817step0Labels = mixedMoment B raw1817step1 raw1817step1Labels := by
      have ha : raw1817step1 = -raw1817step0 := by apply Matrix.ext; change ∀ i j, raw1817step1 i j = -(raw1817step0 i j); unfold raw1817step1 raw1817step0; decide +kernel
      have hl : raw1817step1Labels = raw1817step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1817step1 raw1817step1Labels = mixedMoment B raw1817step2 raw1817step2Labels := by
      have ha : raw1817step2 = raw1817step1 := by apply Matrix.ext; unfold raw1817step2 raw1817step1; decide +kernel
      have hl : raw1817step1Labels = labelEmbedding1 ∘ raw1817step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1817step1 raw1817step1Labels raw1817step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

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

theorem canonical2403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2403 raw2403Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw2403 raw2403Labels = mixedMoment B raw2403step0 raw2403step0Labels := by
      have ha : raw2403step0 = (fun i j => raw2403 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2403step0 raw2403; decide +kernel
      have hl : raw2403step0Labels = raw2403Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2403 raw2403Labels permutation32 permutation4
    mixedMoment B raw2403step0 raw2403step0Labels = mixedMoment B raw2403step1 raw2403step1Labels := by
      have ha : raw2403step1 = raw2403step0 := by apply Matrix.ext; unfold raw2403step1 raw2403step0; decide +kernel
      have hl : raw2403step0Labels = labelEmbedding7 ∘ raw2403step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2403step0 raw2403step0Labels raw2403step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

theorem canonical2404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2404 raw2404Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw2404 raw2404Labels = mixedMoment B raw2404step0 raw2404step0Labels := by
      have ha : raw2404step0 = (fun i j => raw2404 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2404step0 raw2404; decide +kernel
      have hl : raw2404step0Labels = raw2404Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2404 raw2404Labels permutation32 permutation4
    _ = mixedMoment B node3694 node3694Labels := by rfl

theorem canonical2405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2405 raw2405Labels = mixedMoment B node3773 node3773Labels := by
  calc
    mixedMoment B raw2405 raw2405Labels = mixedMoment B raw2405step0 raw2405step0Labels := by
      have ha : raw2405step0 = (fun i j => raw2405 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2405step0 raw2405; decide +kernel
      have hl : raw2405step0Labels = raw2405Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2405 raw2405Labels permutation32 permutation6
    mixedMoment B raw2405step0 raw2405step0Labels = mixedMoment B raw2405step1 raw2405step1Labels := by
      have ha : raw2405step1 = -raw2405step0 := by apply Matrix.ext; change ∀ i j, raw2405step1 i j = -(raw2405step0 i j); unfold raw2405step1 raw2405step0; decide +kernel
      have hl : raw2405step1Labels = raw2405step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2405step1 raw2405step1Labels = mixedMoment B raw2405step2 raw2405step2Labels := by
      have ha : raw2405step2 = raw2405step1 := by apply Matrix.ext; unfold raw2405step2 raw2405step1; decide +kernel
      have hl : raw2405step1Labels = labelEmbedding1 ∘ raw2405step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2405step1 raw2405step1Labels raw2405step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3773 node3773Labels := by rfl

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

theorem canonical2460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2460 raw2460Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw2460 raw2460Labels = mixedMoment B raw2460step0 raw2460step0Labels := by
      have ha : raw2460step0 = (fun i j => raw2460 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2460step0 raw2460; decide +kernel
      have hl : raw2460step0Labels = raw2460Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2460 raw2460Labels permutation152 permutation4
    mixedMoment B raw2460step0 raw2460step0Labels = mixedMoment B raw2460step1 raw2460step1Labels := by
      have ha : raw2460step1 = raw2460step0 := by apply Matrix.ext; unfold raw2460step1 raw2460step0; decide +kernel
      have hl : raw2460step0Labels = labelEmbedding7 ∘ raw2460step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2460step0 raw2460step0Labels raw2460step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

theorem canonical2461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2461 raw2461Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw2461 raw2461Labels = mixedMoment B raw2461step0 raw2461step0Labels := by
      have ha : raw2461step0 = (fun i j => raw2461 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2461step0 raw2461; decide +kernel
      have hl : raw2461step0Labels = raw2461Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2461 raw2461Labels permutation152 permutation4
    _ = mixedMoment B node3779 node3779Labels := by rfl

theorem canonical2462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2462 raw2462Labels = mixedMoment B node3797 node3797Labels := by
  calc
    mixedMoment B raw2462 raw2462Labels = mixedMoment B raw2462step0 raw2462step0Labels := by
      have ha : raw2462step0 = (fun i j => raw2462 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2462step0 raw2462; decide +kernel
      have hl : raw2462step0Labels = raw2462Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2462 raw2462Labels permutation152 permutation6
    mixedMoment B raw2462step0 raw2462step0Labels = mixedMoment B raw2462step1 raw2462step1Labels := by
      have ha : raw2462step1 = -raw2462step0 := by apply Matrix.ext; change ∀ i j, raw2462step1 i j = -(raw2462step0 i j); unfold raw2462step1 raw2462step0; decide +kernel
      have hl : raw2462step1Labels = raw2462step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2462step1 raw2462step1Labels = mixedMoment B raw2462step2 raw2462step2Labels := by
      have ha : raw2462step2 = raw2462step1 := by apply Matrix.ext; unfold raw2462step2 raw2462step1; decide +kernel
      have hl : raw2462step1Labels = labelEmbedding1 ∘ raw2462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2462step1 raw2462step1Labels raw2462step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3797 node3797Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical246
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31562 raw31562Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw31562 raw31562Labels = mixedMoment B raw31562step0 raw31562step0Labels := by
      have hz : ∀ j, raw31562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31562step0 = (fun i j => raw31562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31562step0 raw31562; decide +kernel
      have hl : raw31562step0Labels = raw31562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31562 raw31562Labels permutation434 hz
    mixedMoment B raw31562step0 raw31562step0Labels = mixedMoment B raw31562step1 raw31562step1Labels := by
      have ha : raw31562step1 = (fun i j => raw31562step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31562step1 raw31562step0; decide +kernel
      have hl : raw31562step1Labels = raw31562step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31562step0 raw31562step0Labels permutation32 permutation3
    mixedMoment B raw31562step1 raw31562step1Labels = mixedMoment B raw31562step2 raw31562step2Labels := by
      have ha : raw31562step2 = raw31562step1 := by apply Matrix.ext; unfold raw31562step2 raw31562step1; decide +kernel
      have hl : raw31562step1Labels = labelEmbedding6 ∘ raw31562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31562step1 raw31562step1Labels raw31562step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

theorem canonical31563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31563 raw31563Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw31563 raw31563Labels = mixedMoment B raw31563step0 raw31563step0Labels := by
      have hz : ∀ j, raw31563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31563step0 = (fun i j => raw31563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31563step0 raw31563; decide +kernel
      have hl : raw31563step0Labels = raw31563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31563 raw31563Labels permutation434 hz
    mixedMoment B raw31563step0 raw31563step0Labels = mixedMoment B raw31563step1 raw31563step1Labels := by
      have ha : raw31563step1 = (fun i j => raw31563step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31563step1 raw31563step0; decide +kernel
      have hl : raw31563step1Labels = raw31563step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31563step0 raw31563step0Labels permutation32 permutation3
    mixedMoment B raw31563step1 raw31563step1Labels = mixedMoment B raw31563step2 raw31563step2Labels := by
      have ha : raw31563step2 = raw31563step1 := by apply Matrix.ext; unfold raw31563step2 raw31563step1; decide +kernel
      have hl : raw31563step1Labels = labelEmbedding6 ∘ raw31563step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31563step1 raw31563step1Labels raw31563step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5418 node5418Labels := by rfl

theorem canonical31564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31564 raw31564Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw31564 raw31564Labels = mixedMoment B raw31564step0 raw31564step0Labels := by
      have ha : raw31564step0 = (fun i j => raw31564 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31564step0 raw31564; decide +kernel
      have hl : raw31564step0Labels = raw31564Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31564 raw31564Labels permutation200 permutation3
    mixedMoment B raw31564step0 raw31564step0Labels = mixedMoment B raw31564step1 raw31564step1Labels := by
      have ha : raw31564step1 = raw31564step0 := by apply Matrix.ext; unfold raw31564step1 raw31564step0; decide +kernel
      have hl : raw31564step0Labels = labelEmbedding6 ∘ raw31564step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31564step0 raw31564step0Labels raw31564step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

theorem canonical31565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31565 raw31565Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw31565 raw31565Labels = mixedMoment B raw31565step0 raw31565step0Labels := by
      have hz : ∀ j, raw31565 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31565step0 = (fun i j => raw31565 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31565step0 raw31565; decide +kernel
      have hl : raw31565step0Labels = raw31565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31565 raw31565Labels permutation434 hz
    mixedMoment B raw31565step0 raw31565step0Labels = mixedMoment B raw31565step1 raw31565step1Labels := by
      have ha : raw31565step1 = (fun i j => raw31565step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31565step1 raw31565step0; decide +kernel
      have hl : raw31565step1Labels = raw31565step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31565step0 raw31565step0Labels permutation33 permutation3
    mixedMoment B raw31565step1 raw31565step1Labels = mixedMoment B raw31565step2 raw31565step2Labels := by
      have ha : raw31565step2 = raw31565step1 := by apply Matrix.ext; unfold raw31565step2 raw31565step1; decide +kernel
      have hl : raw31565step1Labels = labelEmbedding6 ∘ raw31565step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31565step1 raw31565step1Labels raw31565step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical31566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31566 raw31566Labels = mixedMoment B node4224 node4224Labels := by
  calc
    mixedMoment B raw31566 raw31566Labels = mixedMoment B raw31566step0 raw31566step0Labels := by
      have hz : ∀ j, raw31566 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31566step0 = (fun i j => raw31566 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31566step0 raw31566; decide +kernel
      have hl : raw31566step0Labels = raw31566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31566 raw31566Labels permutation434 hz
    mixedMoment B raw31566step0 raw31566step0Labels = mixedMoment B raw31566step1 raw31566step1Labels := by
      have ha : raw31566step1 = (fun i j => raw31566step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31566step1 raw31566step0; decide +kernel
      have hl : raw31566step1Labels = raw31566step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31566step0 raw31566step0Labels permutation32 permutation3
    mixedMoment B raw31566step1 raw31566step1Labels = mixedMoment B raw31566step2 raw31566step2Labels := by
      have ha : raw31566step2 = raw31566step1 := by apply Matrix.ext; unfold raw31566step2 raw31566step1; decide +kernel
      have hl : raw31566step1Labels = labelEmbedding6 ∘ raw31566step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31566step1 raw31566step1Labels raw31566step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4224 node4224Labels := by rfl

theorem canonical31567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31567 raw31567Labels = mixedMoment B node4654 node4654Labels := by
  calc
    mixedMoment B raw31567 raw31567Labels = mixedMoment B raw31567step0 raw31567step0Labels := by
      have hz : ∀ j, raw31567 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31567step0 = (fun i j => raw31567 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31567step0 raw31567; decide +kernel
      have hl : raw31567step0Labels = raw31567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31567 raw31567Labels permutation434 hz
    mixedMoment B raw31567step0 raw31567step0Labels = mixedMoment B raw31567step1 raw31567step1Labels := by
      have ha : raw31567step1 = (fun i j => raw31567step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31567step1 raw31567step0; decide +kernel
      have hl : raw31567step1Labels = raw31567step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31567step0 raw31567step0Labels permutation32 permutation3
    mixedMoment B raw31567step1 raw31567step1Labels = mixedMoment B raw31567step2 raw31567step2Labels := by
      have ha : raw31567step2 = raw31567step1 := by apply Matrix.ext; unfold raw31567step2 raw31567step1; decide +kernel
      have hl : raw31567step1Labels = labelEmbedding6 ∘ raw31567step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31567step1 raw31567step1Labels raw31567step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4654 node4654Labels := by rfl

theorem canonical31568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31568 raw31568Labels = mixedMoment B node4717 node4717Labels := by
  calc
    mixedMoment B raw31568 raw31568Labels = mixedMoment B raw31568step0 raw31568step0Labels := by
      have ha : raw31568step0 = (fun i j => raw31568 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31568step0 raw31568; decide +kernel
      have hl : raw31568step0Labels = raw31568Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31568 raw31568Labels permutation200 permutation3
    mixedMoment B raw31568step0 raw31568step0Labels = mixedMoment B raw31568step1 raw31568step1Labels := by
      have ha : raw31568step1 = raw31568step0 := by apply Matrix.ext; unfold raw31568step1 raw31568step0; decide +kernel
      have hl : raw31568step0Labels = labelEmbedding6 ∘ raw31568step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31568step0 raw31568step0Labels raw31568step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4717 node4717Labels := by rfl

theorem canonical31569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31569 raw31569Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw31569 raw31569Labels = mixedMoment B raw31569step0 raw31569step0Labels := by
      have hz : ∀ j, raw31569 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31569step0 = (fun i j => raw31569 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31569step0 raw31569; decide +kernel
      have hl : raw31569step0Labels = raw31569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31569 raw31569Labels permutation434 hz
    mixedMoment B raw31569step0 raw31569step0Labels = mixedMoment B raw31569step1 raw31569step1Labels := by
      have ha : raw31569step1 = (fun i j => raw31569step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31569step1 raw31569step0; decide +kernel
      have hl : raw31569step1Labels = raw31569step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31569step0 raw31569step0Labels permutation36 permutation3
    mixedMoment B raw31569step1 raw31569step1Labels = mixedMoment B raw31569step2 raw31569step2Labels := by
      have ha : raw31569step2 = raw31569step1 := by apply Matrix.ext; unfold raw31569step2 raw31569step1; decide +kernel
      have hl : raw31569step1Labels = labelEmbedding6 ∘ raw31569step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31569step1 raw31569step1Labels raw31569step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical31570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31570 raw31570Labels = mixedMoment B node4201 node4201Labels := by
  calc
    mixedMoment B raw31570 raw31570Labels = mixedMoment B raw31570step0 raw31570step0Labels := by
      have ha : raw31570step0 = (fun i j => raw31570 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31570step0 raw31570; decide +kernel
      have hl : raw31570step0Labels = raw31570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31570 raw31570Labels permutation152 permutation3
    mixedMoment B raw31570step0 raw31570step0Labels = mixedMoment B raw31570step1 raw31570step1Labels := by
      have ha : raw31570step1 = raw31570step0 := by apply Matrix.ext; unfold raw31570step1 raw31570step0; decide +kernel
      have hl : raw31570step0Labels = labelEmbedding6 ∘ raw31570step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31570step0 raw31570step0Labels raw31570step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4201 node4201Labels := by rfl

theorem canonical31571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31571 raw31571Labels = mixedMoment B node4635 node4635Labels := by
  calc
    mixedMoment B raw31571 raw31571Labels = mixedMoment B raw31571step0 raw31571step0Labels := by
      have ha : raw31571step0 = (fun i j => raw31571 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31571step0 raw31571; decide +kernel
      have hl : raw31571step0Labels = raw31571Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31571 raw31571Labels permutation152 permutation3
    mixedMoment B raw31571step0 raw31571step0Labels = mixedMoment B raw31571step1 raw31571step1Labels := by
      have ha : raw31571step1 = raw31571step0 := by apply Matrix.ext; unfold raw31571step1 raw31571step0; decide +kernel
      have hl : raw31571step0Labels = labelEmbedding6 ∘ raw31571step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31571step0 raw31571step0Labels raw31571step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4635 node4635Labels := by rfl

theorem canonical31572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31572 raw31572Labels = mixedMoment B node4767 node4767Labels := by
  calc
    mixedMoment B raw31572 raw31572Labels = mixedMoment B raw31572step0 raw31572step0Labels := by
      have ha : raw31572step0 = (fun i j => raw31572 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31572step0 raw31572; decide +kernel
      have hl : raw31572step0Labels = raw31572Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31572 raw31572Labels permutation152 permutation3
    mixedMoment B raw31572step0 raw31572step0Labels = mixedMoment B raw31572step1 raw31572step1Labels := by
      have ha : raw31572step1 = raw31572step0 := by apply Matrix.ext; unfold raw31572step1 raw31572step0; decide +kernel
      have hl : raw31572step0Labels = labelEmbedding6 ∘ raw31572step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31572step0 raw31572step0Labels raw31572step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4767 node4767Labels := by rfl

theorem canonical31573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31573 raw31573Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw31573 raw31573Labels = mixedMoment B raw31573step0 raw31573step0Labels := by
      have hz : ∀ j, raw31573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31573step0 = (fun i j => raw31573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31573step0 raw31573; decide +kernel
      have hl : raw31573step0Labels = raw31573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31573 raw31573Labels permutation434 hz
    mixedMoment B raw31573step0 raw31573step0Labels = mixedMoment B raw31573step1 raw31573step1Labels := by
      have ha : raw31573step1 = (fun i j => raw31573step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31573step1 raw31573step0; decide +kernel
      have hl : raw31573step1Labels = raw31573step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31573step0 raw31573step0Labels permutation33 permutation3
    mixedMoment B raw31573step1 raw31573step1Labels = mixedMoment B raw31573step2 raw31573step2Labels := by
      have ha : raw31573step2 = raw31573step1 := by apply Matrix.ext; unfold raw31573step2 raw31573step1; decide +kernel
      have hl : raw31573step1Labels = labelEmbedding6 ∘ raw31573step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31573step1 raw31573step1Labels raw31573step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4204 node4204Labels := by rfl

theorem canonical31574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31574 raw31574Labels = mixedMoment B node4637 node4637Labels := by
  calc
    mixedMoment B raw31574 raw31574Labels = mixedMoment B raw31574step0 raw31574step0Labels := by
      have hz : ∀ j, raw31574 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31574step0 = (fun i j => raw31574 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31574step0 raw31574; decide +kernel
      have hl : raw31574step0Labels = raw31574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31574 raw31574Labels permutation434 hz
    mixedMoment B raw31574step0 raw31574step0Labels = mixedMoment B raw31574step1 raw31574step1Labels := by
      have ha : raw31574step1 = (fun i j => raw31574step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31574step1 raw31574step0; decide +kernel
      have hl : raw31574step1Labels = raw31574step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31574step0 raw31574step0Labels permutation33 permutation3
    mixedMoment B raw31574step1 raw31574step1Labels = mixedMoment B raw31574step2 raw31574step2Labels := by
      have ha : raw31574step2 = raw31574step1 := by apply Matrix.ext; unfold raw31574step2 raw31574step1; decide +kernel
      have hl : raw31574step1Labels = labelEmbedding6 ∘ raw31574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31574step1 raw31574step1Labels raw31574step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4637 node4637Labels := by rfl

theorem canonical31575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31575 raw31575Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw31575 raw31575Labels = mixedMoment B raw31575step0 raw31575step0Labels := by
      have hz : ∀ j, raw31575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31575step0 = (fun i j => raw31575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31575step0 raw31575; decide +kernel
      have hl : raw31575step0Labels = raw31575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31575 raw31575Labels permutation434 hz
    mixedMoment B raw31575step0 raw31575step0Labels = mixedMoment B raw31575step1 raw31575step1Labels := by
      have ha : raw31575step1 = (fun i j => raw31575step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31575step1 raw31575step0; decide +kernel
      have hl : raw31575step1Labels = raw31575step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31575step0 raw31575step0Labels permutation33 permutation3
    mixedMoment B raw31575step1 raw31575step1Labels = mixedMoment B raw31575step2 raw31575step2Labels := by
      have ha : raw31575step2 = raw31575step1 := by apply Matrix.ext; unfold raw31575step2 raw31575step1; decide +kernel
      have hl : raw31575step1Labels = labelEmbedding6 ∘ raw31575step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31575step1 raw31575step1Labels raw31575step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4769 node4769Labels := by rfl

theorem canonical31576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31576 raw31576Labels = mixedMoment B node4706 node4706Labels := by
  calc
    mixedMoment B raw31576 raw31576Labels = mixedMoment B raw31576step0 raw31576step0Labels := by
      have ha : raw31576step0 = (fun i j => raw31576 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31576step0 raw31576; decide +kernel
      have hl : raw31576step0Labels = raw31576Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31576 raw31576Labels permutation201 permutation3
    mixedMoment B raw31576step0 raw31576step0Labels = mixedMoment B raw31576step1 raw31576step1Labels := by
      have ha : raw31576step1 = raw31576step0 := by apply Matrix.ext; unfold raw31576step1 raw31576step0; decide +kernel
      have hl : raw31576step0Labels = labelEmbedding6 ∘ raw31576step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31576step0 raw31576step0Labels raw31576step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4706 node4706Labels := by rfl

theorem canonical31577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31577 raw31577Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw31577 raw31577Labels = mixedMoment B raw31577step0 raw31577step0Labels := by
      have hz : ∀ j, raw31577 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31577step0 = (fun i j => raw31577 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31577step0 raw31577; decide +kernel
      have hl : raw31577step0Labels = raw31577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31577 raw31577Labels permutation434 hz
    mixedMoment B raw31577step0 raw31577step0Labels = mixedMoment B raw31577step1 raw31577step1Labels := by
      have ha : raw31577step1 = (fun i j => raw31577step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31577step1 raw31577step0; decide +kernel
      have hl : raw31577step1Labels = raw31577step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31577step0 raw31577step0Labels permutation33 permutation3
    mixedMoment B raw31577step1 raw31577step1Labels = mixedMoment B raw31577step2 raw31577step2Labels := by
      have ha : raw31577step2 = raw31577step1 := by apply Matrix.ext; unfold raw31577step2 raw31577step1; decide +kernel
      have hl : raw31577step1Labels = labelEmbedding6 ∘ raw31577step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31577step1 raw31577step1Labels raw31577step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical31578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31578 raw31578Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw31578 raw31578Labels = mixedMoment B raw31578step0 raw31578step0Labels := by
      have hz : ∀ j, raw31578 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31578step0 = (fun i j => raw31578 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31578step0 raw31578; decide +kernel
      have hl : raw31578step0Labels = raw31578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31578 raw31578Labels permutation434 hz
    mixedMoment B raw31578step0 raw31578step0Labels = mixedMoment B raw31578step1 raw31578step1Labels := by
      have ha : raw31578step1 = (fun i j => raw31578step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31578step1 raw31578step0; decide +kernel
      have hl : raw31578step1Labels = raw31578step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31578step0 raw31578step0Labels permutation32 permutation3
    mixedMoment B raw31578step1 raw31578step1Labels = mixedMoment B raw31578step2 raw31578step2Labels := by
      have ha : raw31578step2 = raw31578step1 := by apply Matrix.ext; unfold raw31578step2 raw31578step1; decide +kernel
      have hl : raw31578step1Labels = labelEmbedding6 ∘ raw31578step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31578step1 raw31578step1Labels raw31578step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4204 node4204Labels := by rfl

theorem canonical31579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31579 raw31579Labels = mixedMoment B node4637 node4637Labels := by
  calc
    mixedMoment B raw31579 raw31579Labels = mixedMoment B raw31579step0 raw31579step0Labels := by
      have hz : ∀ j, raw31579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31579step0 = (fun i j => raw31579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31579step0 raw31579; decide +kernel
      have hl : raw31579step0Labels = raw31579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31579 raw31579Labels permutation434 hz
    mixedMoment B raw31579step0 raw31579step0Labels = mixedMoment B raw31579step1 raw31579step1Labels := by
      have ha : raw31579step1 = (fun i j => raw31579step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31579step1 raw31579step0; decide +kernel
      have hl : raw31579step1Labels = raw31579step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31579step0 raw31579step0Labels permutation32 permutation3
    mixedMoment B raw31579step1 raw31579step1Labels = mixedMoment B raw31579step2 raw31579step2Labels := by
      have ha : raw31579step2 = raw31579step1 := by apply Matrix.ext; unfold raw31579step2 raw31579step1; decide +kernel
      have hl : raw31579step1Labels = labelEmbedding6 ∘ raw31579step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31579step1 raw31579step1Labels raw31579step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4637 node4637Labels := by rfl

theorem canonical31580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31580 raw31580Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw31580 raw31580Labels = mixedMoment B raw31580step0 raw31580step0Labels := by
      have hz : ∀ j, raw31580 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31580step0 = (fun i j => raw31580 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31580step0 raw31580; decide +kernel
      have hl : raw31580step0Labels = raw31580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31580 raw31580Labels permutation434 hz
    mixedMoment B raw31580step0 raw31580step0Labels = mixedMoment B raw31580step1 raw31580step1Labels := by
      have ha : raw31580step1 = (fun i j => raw31580step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31580step1 raw31580step0; decide +kernel
      have hl : raw31580step1Labels = raw31580step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31580step0 raw31580step0Labels permutation32 permutation3
    mixedMoment B raw31580step1 raw31580step1Labels = mixedMoment B raw31580step2 raw31580step2Labels := by
      have ha : raw31580step2 = raw31580step1 := by apply Matrix.ext; unfold raw31580step2 raw31580step1; decide +kernel
      have hl : raw31580step1Labels = labelEmbedding6 ∘ raw31580step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31580step1 raw31580step1Labels raw31580step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4769 node4769Labels := by rfl

theorem canonical31581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31581 raw31581Labels = mixedMoment B node4706 node4706Labels := by
  calc
    mixedMoment B raw31581 raw31581Labels = mixedMoment B raw31581step0 raw31581step0Labels := by
      have ha : raw31581step0 = (fun i j => raw31581 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31581step0 raw31581; decide +kernel
      have hl : raw31581step0Labels = raw31581Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31581 raw31581Labels permutation200 permutation3
    mixedMoment B raw31581step0 raw31581step0Labels = mixedMoment B raw31581step1 raw31581step1Labels := by
      have ha : raw31581step1 = raw31581step0 := by apply Matrix.ext; unfold raw31581step1 raw31581step0; decide +kernel
      have hl : raw31581step0Labels = labelEmbedding6 ∘ raw31581step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31581step0 raw31581step0Labels raw31581step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4706 node4706Labels := by rfl

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

theorem canonical867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw867 raw867Labels = mixedMoment B node4201 node4201Labels := by
  calc
    mixedMoment B raw867 raw867Labels = mixedMoment B raw867step0 raw867step0Labels := by
      have ha : raw867step0 = (fun i j => raw867 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw867step0 raw867; decide +kernel
      have hl : raw867step0Labels = raw867Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw867 raw867Labels permutation152 permutation4
    mixedMoment B raw867step0 raw867step0Labels = mixedMoment B raw867step1 raw867step1Labels := by
      have ha : raw867step1 = raw867step0 := by apply Matrix.ext; unfold raw867step1 raw867step0; decide +kernel
      have hl : raw867step0Labels = labelEmbedding7 ∘ raw867step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw867step0 raw867step0Labels raw867step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4201 node4201Labels := by rfl

theorem canonical868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw868 raw868Labels = mixedMoment B node704 node704Labels := by
  calc
    mixedMoment B raw868 raw868Labels = mixedMoment B raw868step0 raw868step0Labels := by
      have ha : raw868step0 = (fun i j => raw868 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw868step0 raw868; decide +kernel
      have hl : raw868step0Labels = raw868Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw868 raw868Labels permutation152 permutation4
    _ = mixedMoment B node704 node704Labels := by rfl

theorem canonical869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw869 raw869Labels = mixedMoment B node761 node761Labels := by
  calc
    mixedMoment B raw869 raw869Labels = mixedMoment B raw869step0 raw869step0Labels := by
      have ha : raw869step0 = (fun i j => raw869 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw869step0 raw869; decide +kernel
      have hl : raw869step0Labels = raw869Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw869 raw869Labels permutation152 permutation6
    mixedMoment B raw869step0 raw869step0Labels = mixedMoment B raw869step1 raw869step1Labels := by
      have ha : raw869step1 = -raw869step0 := by apply Matrix.ext; change ∀ i j, raw869step1 i j = -(raw869step0 i j); unfold raw869step1 raw869step0; decide +kernel
      have hl : raw869step1Labels = raw869step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw869step1 raw869step1Labels = mixedMoment B raw869step2 raw869step2Labels := by
      have ha : raw869step2 = raw869step1 := by apply Matrix.ext; unfold raw869step2 raw869step1; decide +kernel
      have hl : raw869step1Labels = labelEmbedding1 ∘ raw869step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw869step1 raw869step1Labels raw869step2Labels labelEmbedding1 hl
    _ = mixedMoment B node761 node761Labels := by rfl

theorem canonical876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw876 raw876Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw876 raw876Labels = mixedMoment B raw876step0 raw876step0Labels := by
      have ha : raw876step0 = (fun i j => raw876 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw876step0 raw876; decide +kernel
      have hl : raw876step0Labels = raw876Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw876 raw876Labels permutation32 permutation4
    mixedMoment B raw876step0 raw876step0Labels = mixedMoment B raw876step1 raw876step1Labels := by
      have ha : raw876step1 = raw876step0 := by apply Matrix.ext; unfold raw876step1 raw876step0; decide +kernel
      have hl : raw876step0Labels = labelEmbedding7 ∘ raw876step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw876step0 raw876step0Labels raw876step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4204 node4204Labels := by rfl

theorem canonical877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw877 raw877Labels = mixedMoment B node707 node707Labels := by
  calc
    mixedMoment B raw877 raw877Labels = mixedMoment B raw877step0 raw877step0Labels := by
      have ha : raw877step0 = (fun i j => raw877 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw877step0 raw877; decide +kernel
      have hl : raw877step0Labels = raw877Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw877 raw877Labels permutation32 permutation4
    _ = mixedMoment B node707 node707Labels := by rfl

theorem canonical878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw878 raw878Labels = mixedMoment B node763 node763Labels := by
  calc
    mixedMoment B raw878 raw878Labels = mixedMoment B raw878step0 raw878step0Labels := by
      have ha : raw878step0 = (fun i j => raw878 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw878step0 raw878; decide +kernel
      have hl : raw878step0Labels = raw878Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw878 raw878Labels permutation32 permutation6
    mixedMoment B raw878step0 raw878step0Labels = mixedMoment B raw878step1 raw878step1Labels := by
      have ha : raw878step1 = -raw878step0 := by apply Matrix.ext; change ∀ i j, raw878step1 i j = -(raw878step0 i j); unfold raw878step1 raw878step0; decide +kernel
      have hl : raw878step1Labels = raw878step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw878step1 raw878step1Labels = mixedMoment B raw878step2 raw878step2Labels := by
      have ha : raw878step2 = raw878step1 := by apply Matrix.ext; unfold raw878step2 raw878step1; decide +kernel
      have hl : raw878step1Labels = labelEmbedding1 ∘ raw878step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw878step1 raw878step1Labels raw878step2Labels labelEmbedding1 hl
    _ = mixedMoment B node763 node763Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw912 raw912Labels = mixedMoment B node4224 node4224Labels := by
  calc
    mixedMoment B raw912 raw912Labels = mixedMoment B raw912step0 raw912step0Labels := by
      have ha : raw912step0 = (fun i j => raw912 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw912step0 raw912; decide +kernel
      have hl : raw912step0Labels = raw912Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw912 raw912Labels permutation32 permutation4
    mixedMoment B raw912step0 raw912step0Labels = mixedMoment B raw912step1 raw912step1Labels := by
      have ha : raw912step1 = raw912step0 := by apply Matrix.ext; unfold raw912step1 raw912step0; decide +kernel
      have hl : raw912step0Labels = labelEmbedding7 ∘ raw912step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw912step0 raw912step0Labels raw912step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4224 node4224Labels := by rfl

theorem canonical913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw913 raw913Labels = mixedMoment B node725 node725Labels := by
  calc
    mixedMoment B raw913 raw913Labels = mixedMoment B raw913step0 raw913step0Labels := by
      have ha : raw913step0 = (fun i j => raw913 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw913step0 raw913; decide +kernel
      have hl : raw913step0Labels = raw913Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw913 raw913Labels permutation32 permutation4
    _ = mixedMoment B node725 node725Labels := by rfl

theorem canonical914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw914 raw914Labels = mixedMoment B node771 node771Labels := by
  calc
    mixedMoment B raw914 raw914Labels = mixedMoment B raw914step0 raw914step0Labels := by
      have ha : raw914step0 = (fun i j => raw914 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw914step0 raw914; decide +kernel
      have hl : raw914step0Labels = raw914Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw914 raw914Labels permutation35 permutation6
    mixedMoment B raw914step0 raw914step0Labels = mixedMoment B raw914step1 raw914step1Labels := by
      have ha : raw914step1 = -raw914step0 := by apply Matrix.ext; change ∀ i j, raw914step1 i j = -(raw914step0 i j); unfold raw914step1 raw914step0; decide +kernel
      have hl : raw914step1Labels = raw914step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw914step1 raw914step1Labels = mixedMoment B raw914step2 raw914step2Labels := by
      have ha : raw914step2 = raw914step1 := by apply Matrix.ext; unfold raw914step2 raw914step1; decide +kernel
      have hl : raw914step1Labels = labelEmbedding1 ∘ raw914step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw914step1 raw914step1Labels raw914step2Labels labelEmbedding1 hl
    _ = mixedMoment B node771 node771Labels := by rfl

theorem canonical984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw984 raw984Labels = mixedMoment B node4256 node4256Labels := by
  calc
    mixedMoment B raw984 raw984Labels = mixedMoment B raw984step0 raw984step0Labels := by
      have ha : raw984step0 = (fun i j => raw984 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw984step0 raw984; decide +kernel
      have hl : raw984step0Labels = raw984Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw984 raw984Labels permutation32 permutation4
    mixedMoment B raw984step0 raw984step0Labels = mixedMoment B raw984step1 raw984step1Labels := by
      have ha : raw984step1 = raw984step0 := by apply Matrix.ext; unfold raw984step1 raw984step0; decide +kernel
      have hl : raw984step0Labels = labelEmbedding7 ∘ raw984step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw984step0 raw984step0Labels raw984step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4256 node4256Labels := by rfl

theorem canonical985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw985 raw985Labels = mixedMoment B node790 node790Labels := by
  calc
    mixedMoment B raw985 raw985Labels = mixedMoment B raw985step0 raw985step0Labels := by
      have ha : raw985step0 = (fun i j => raw985 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw985step0 raw985; decide +kernel
      have hl : raw985step0Labels = raw985Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw985 raw985Labels permutation32 permutation4
    _ = mixedMoment B node790 node790Labels := by rfl

theorem canonical986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw986 raw986Labels = mixedMoment B node848 node848Labels := by
  calc
    mixedMoment B raw986 raw986Labels = mixedMoment B raw986step0 raw986step0Labels := by
      have ha : raw986step0 = (fun i j => raw986 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw986step0 raw986; decide +kernel
      have hl : raw986step0Labels = raw986Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw986 raw986Labels permutation32 permutation6
    mixedMoment B raw986step0 raw986step0Labels = mixedMoment B raw986step1 raw986step1Labels := by
      have ha : raw986step1 = -raw986step0 := by apply Matrix.ext; change ∀ i j, raw986step1 i j = -(raw986step0 i j); unfold raw986step1 raw986step0; decide +kernel
      have hl : raw986step1Labels = raw986step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw986step1 raw986step1Labels = mixedMoment B raw986step2 raw986step2Labels := by
      have ha : raw986step2 = raw986step1 := by apply Matrix.ext; unfold raw986step2 raw986step1; decide +kernel
      have hl : raw986step1Labels = labelEmbedding1 ∘ raw986step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw986step1 raw986step1Labels raw986step2Labels labelEmbedding1 hl
    _ = mixedMoment B node848 node848Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11315 raw11315Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw11315 raw11315Labels = mixedMoment B raw11315step0 raw11315step0Labels := by
      have hz : ∀ j, raw11315 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11315step0 = (fun i j => raw11315 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11315step0 raw11315; decide +kernel
      have hl : raw11315step0Labels = raw11315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11315 raw11315Labels permutation434 hz
    mixedMoment B raw11315step0 raw11315step0Labels = mixedMoment B raw11315step1 raw11315step1Labels := by
      have ha : raw11315step1 = (fun i j => raw11315step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11315step1 raw11315step0; decide +kernel
      have hl : raw11315step1Labels = raw11315step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11315step0 raw11315step0Labels permutation32 permutation3
    mixedMoment B raw11315step1 raw11315step1Labels = mixedMoment B raw11315step2 raw11315step2Labels := by
      have ha : raw11315step2 = raw11315step1 := by apply Matrix.ext; unfold raw11315step2 raw11315step1; decide +kernel
      have hl : raw11315step1Labels = labelEmbedding6 ∘ raw11315step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11315step1 raw11315step1Labels raw11315step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical11326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11326 raw11326Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11326 raw11326Labels = mixedMoment B raw11326step0 raw11326step0Labels := by
      have hz : ∀ j, raw11326 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11326step0 = (fun i j => raw11326 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11326step0 raw11326; decide +kernel
      have hl : raw11326step0Labels = raw11326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11326 raw11326Labels permutation434 hz
    mixedMoment B raw11326step0 raw11326step0Labels = mixedMoment B raw11326step1 raw11326step1Labels := by
      have ha : raw11326step1 = (fun i j => raw11326step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11326step1 raw11326step0; decide +kernel
      have hl : raw11326step1Labels = raw11326step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11326step0 raw11326step0Labels permutation34 permutation3
    mixedMoment B raw11326step1 raw11326step1Labels = mixedMoment B raw11326step2 raw11326step2Labels := by
      have ha : raw11326step2 = raw11326step1 := by apply Matrix.ext; unfold raw11326step2 raw11326step1; decide +kernel
      have hl : raw11326step1Labels = labelEmbedding6 ∘ raw11326step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11326step1 raw11326step1Labels raw11326step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical11331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11331 raw11331Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw11331 raw11331Labels = mixedMoment B raw11331step0 raw11331step0Labels := by
      have ha : raw11331step0 = (fun i j => raw11331 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11331step0 raw11331; decide +kernel
      have hl : raw11331step0Labels = raw11331Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11331 raw11331Labels permutation154 permutation3
    mixedMoment B raw11331step0 raw11331step0Labels = mixedMoment B raw11331step1 raw11331step1Labels := by
      have ha : raw11331step1 = raw11331step0 := by apply Matrix.ext; unfold raw11331step1 raw11331step0; decide +kernel
      have hl : raw11331step0Labels = labelEmbedding6 ∘ raw11331step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11331step0 raw11331step0Labels raw11331step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical11335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11335 raw11335Labels = mixedMoment B node4256 node4256Labels := by
  calc
    mixedMoment B raw11335 raw11335Labels = mixedMoment B raw11335step0 raw11335step0Labels := by
      have hz : ∀ j, raw11335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11335step0 = (fun i j => raw11335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11335step0 raw11335; decide +kernel
      have hl : raw11335step0Labels = raw11335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11335 raw11335Labels permutation434 hz
    mixedMoment B raw11335step0 raw11335step0Labels = mixedMoment B raw11335step1 raw11335step1Labels := by
      have ha : raw11335step1 = (fun i j => raw11335step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11335step1 raw11335step0; decide +kernel
      have hl : raw11335step1Labels = raw11335step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11335step0 raw11335step0Labels permutation32 permutation3
    mixedMoment B raw11335step1 raw11335step1Labels = mixedMoment B raw11335step2 raw11335step2Labels := by
      have ha : raw11335step2 = raw11335step1 := by apply Matrix.ext; unfold raw11335step2 raw11335step1; decide +kernel
      have hl : raw11335step1Labels = labelEmbedding6 ∘ raw11335step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11335step1 raw11335step1Labels raw11335step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4256 node4256Labels := by rfl

theorem canonical11337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11337 raw11337Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw11337 raw11337Labels = mixedMoment B raw11337step0 raw11337step0Labels := by
      have hz : ∀ j, raw11337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11337step0 = (fun i j => raw11337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11337step0 raw11337; decide +kernel
      have hl : raw11337step0Labels = raw11337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11337 raw11337Labels permutation434 hz
    mixedMoment B raw11337step0 raw11337step0Labels = mixedMoment B raw11337step1 raw11337step1Labels := by
      have ha : raw11337step1 = (fun i j => raw11337step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11337step1 raw11337step0; decide +kernel
      have hl : raw11337step1Labels = raw11337step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11337step0 raw11337step0Labels permutation38 permutation3
    mixedMoment B raw11337step1 raw11337step1Labels = mixedMoment B raw11337step2 raw11337step2Labels := by
      have ha : raw11337step2 = raw11337step1 := by apply Matrix.ext; unfold raw11337step2 raw11337step1; decide +kernel
      have hl : raw11337step1Labels = labelEmbedding6 ∘ raw11337step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11337step1 raw11337step1Labels raw11337step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical11338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11338 raw11338Labels = mixedMoment B node4732 node4732Labels := by
  calc
    mixedMoment B raw11338 raw11338Labels = mixedMoment B raw11338step0 raw11338step0Labels := by
      have ha : raw11338step0 = (fun i j => raw11338 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11338step0 raw11338; decide +kernel
      have hl : raw11338step0Labels = raw11338Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11338 raw11338Labels permutation200 permutation3
    mixedMoment B raw11338step0 raw11338step0Labels = mixedMoment B raw11338step1 raw11338step1Labels := by
      have ha : raw11338step1 = raw11338step0 := by apply Matrix.ext; unfold raw11338step1 raw11338step0; decide +kernel
      have hl : raw11338step0Labels = labelEmbedding6 ∘ raw11338step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11338step0 raw11338step0Labels raw11338step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4732 node4732Labels := by rfl

theorem canonical11339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11339 raw11339Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11339 raw11339Labels = mixedMoment B raw11339step0 raw11339step0Labels := by
      have hz : ∀ j, raw11339 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11339step0 = (fun i j => raw11339 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11339step0 raw11339; decide +kernel
      have hl : raw11339step0Labels = raw11339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11339 raw11339Labels permutation434 hz
    mixedMoment B raw11339step0 raw11339step0Labels = mixedMoment B raw11339step1 raw11339step1Labels := by
      have ha : raw11339step1 = (fun i j => raw11339step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11339step1 raw11339step0; decide +kernel
      have hl : raw11339step1Labels = raw11339step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11339step0 raw11339step0Labels permutation33 permutation3
    mixedMoment B raw11339step1 raw11339step1Labels = mixedMoment B raw11339step2 raw11339step2Labels := by
      have ha : raw11339step2 = raw11339step1 := by apply Matrix.ext; unfold raw11339step2 raw11339step1; decide +kernel
      have hl : raw11339step1Labels = labelEmbedding6 ∘ raw11339step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11339step1 raw11339step1Labels raw11339step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical11341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11341 raw11341Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw11341 raw11341Labels = mixedMoment B raw11341step0 raw11341step0Labels := by
      have hz : ∀ j, raw11341 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11341step0 = (fun i j => raw11341 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11341step0 raw11341; decide +kernel
      have hl : raw11341step0Labels = raw11341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11341 raw11341Labels permutation434 hz
    mixedMoment B raw11341step0 raw11341step0Labels = mixedMoment B raw11341step1 raw11341step1Labels := by
      have ha : raw11341step1 = (fun i j => raw11341step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11341step1 raw11341step0; decide +kernel
      have hl : raw11341step1Labels = raw11341step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11341step0 raw11341step0Labels permutation32 permutation3
    mixedMoment B raw11341step1 raw11341step1Labels = mixedMoment B raw11341step2 raw11341step2Labels := by
      have ha : raw11341step2 = raw11341step1 := by apply Matrix.ext; unfold raw11341step2 raw11341step1; decide +kernel
      have hl : raw11341step1Labels = labelEmbedding6 ∘ raw11341step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11341step1 raw11341step1Labels raw11341step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

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

theorem singleton4201 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4201 node4201Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node704 node704Labels + mixedMoment B node761 node761Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw867 singletonSmall4201
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4201) = raw867Labels := by decide +kernel
  rw [hl, canonical867 B hB] at h
  have hc0 : mixedMoment B raw867 (Fin.cases (0 : Fin 2) singletonSmall4201) =
      mixedMoment B node704 node704Labels := by
    have ha : raw867 = raw868 := by apply Matrix.ext; unfold raw867 raw868; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4201 = raw868Labels := by decide +kernel
    rw [ha, hj, canonical868 B hB]
  have hc1 : mixedMoment B raw867 (Fin.cases (1 : Fin 2) singletonSmall4201) =
      mixedMoment B node761 node761Labels := by
    have ha : raw867 = raw869 := by apply Matrix.ext; unfold raw867 raw869; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4201 = raw869Labels := by decide +kernel
    rw [ha, hj, canonical869 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4204 node4204Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node707 node707Labels + mixedMoment B node763 node763Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw876 singletonSmall4204
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4204) = raw876Labels := by decide +kernel
  rw [hl, canonical876 B hB] at h
  have hc0 : mixedMoment B raw876 (Fin.cases (0 : Fin 2) singletonSmall4204) =
      mixedMoment B node707 node707Labels := by
    have ha : raw876 = raw877 := by apply Matrix.ext; unfold raw876 raw877; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4204 = raw877Labels := by decide +kernel
    rw [ha, hj, canonical877 B hB]
  have hc1 : mixedMoment B raw876 (Fin.cases (1 : Fin 2) singletonSmall4204) =
      mixedMoment B node763 node763Labels := by
    have ha : raw876 = raw878 := by apply Matrix.ext; unfold raw876 raw878; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4204 = raw878Labels := by decide +kernel
    rw [ha, hj, canonical878 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4224 node4224Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node725 node725Labels + mixedMoment B node771 node771Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw912 singletonSmall4224
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4224) = raw912Labels := by decide +kernel
  rw [hl, canonical912 B hB] at h
  have hc0 : mixedMoment B raw912 (Fin.cases (0 : Fin 2) singletonSmall4224) =
      mixedMoment B node725 node725Labels := by
    have ha : raw912 = raw913 := by apply Matrix.ext; unfold raw912 raw913; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4224 = raw913Labels := by decide +kernel
    rw [ha, hj, canonical913 B hB]
  have hc1 : mixedMoment B raw912 (Fin.cases (1 : Fin 2) singletonSmall4224) =
      mixedMoment B node771 node771Labels := by
    have ha : raw912 = raw914 := by apply Matrix.ext; unfold raw912 raw914; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4224 = raw914Labels := by decide +kernel
    rw [ha, hj, canonical914 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4256 node4256Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node790 node790Labels + mixedMoment B node848 node848Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw984 singletonSmall4256
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4256) = raw984Labels := by decide +kernel
  rw [hl, canonical984 B hB] at h
  have hc0 : mixedMoment B raw984 (Fin.cases (0 : Fin 2) singletonSmall4256) =
      mixedMoment B node790 node790Labels := by
    have ha : raw984 = raw985 := by apply Matrix.ext; unfold raw984 raw985; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4256 = raw985Labels := by decide +kernel
    rw [ha, hj, canonical985 B hB]
  have hc1 : mixedMoment B raw984 (Fin.cases (1 : Fin 2) singletonSmall4256) =
      mixedMoment B node848 node848Labels := by
    have ha : raw984 = raw986 := by apply Matrix.ext; unfold raw984 raw986; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4256 = raw986Labels := by decide +kernel
    rw [ha, hj, canonical986 B hB]
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

theorem singleton4635 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4635 node4635Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1764 node1764Labels + mixedMoment B node1848 node1848Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1485 singletonSmall4635
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4635) = raw1485Labels := by decide +kernel
  rw [hl, canonical1485 B hB] at h
  have hc0 : mixedMoment B raw1485 (Fin.cases (0 : Fin 2) singletonSmall4635) =
      mixedMoment B node1764 node1764Labels := by
    have ha : raw1485 = raw1486 := by apply Matrix.ext; unfold raw1485 raw1486; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4635 = raw1486Labels := by decide +kernel
    rw [ha, hj, canonical1486 B hB]
  have hc1 : mixedMoment B raw1485 (Fin.cases (1 : Fin 2) singletonSmall4635) =
      mixedMoment B node1848 node1848Labels := by
    have ha : raw1485 = raw1487 := by apply Matrix.ext; unfold raw1485 raw1487; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4635 = raw1487Labels := by decide +kernel
    rw [ha, hj, canonical1487 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4637 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4637 node4637Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1766 node1766Labels + mixedMoment B node1850 node1850Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1491 singletonSmall4637
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4637) = raw1491Labels := by decide +kernel
  rw [hl, canonical1491 B hB] at h
  have hc0 : mixedMoment B raw1491 (Fin.cases (0 : Fin 2) singletonSmall4637) =
      mixedMoment B node1766 node1766Labels := by
    have ha : raw1491 = raw1492 := by apply Matrix.ext; unfold raw1491 raw1492; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4637 = raw1492Labels := by decide +kernel
    rw [ha, hj, canonical1492 B hB]
  have hc1 : mixedMoment B raw1491 (Fin.cases (1 : Fin 2) singletonSmall4637) =
      mixedMoment B node1850 node1850Labels := by
    have ha : raw1491 = raw1493 := by apply Matrix.ext; unfold raw1491 raw1493; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4637 = raw1493Labels := by decide +kernel
    rw [ha, hj, canonical1493 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4654 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4654 node4654Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1782 node1782Labels + mixedMoment B node1855 node1855Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1524 singletonSmall4654
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4654) = raw1524Labels := by decide +kernel
  rw [hl, canonical1524 B hB] at h
  have hc0 : mixedMoment B raw1524 (Fin.cases (0 : Fin 2) singletonSmall4654) =
      mixedMoment B node1782 node1782Labels := by
    have ha : raw1524 = raw1525 := by apply Matrix.ext; unfold raw1524 raw1525; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4654 = raw1525Labels := by decide +kernel
    rw [ha, hj, canonical1525 B hB]
  have hc1 : mixedMoment B raw1524 (Fin.cases (1 : Fin 2) singletonSmall4654) =
      mixedMoment B node1855 node1855Labels := by
    have ha : raw1524 = raw1526 := by apply Matrix.ext; unfold raw1524 raw1526; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4654 = raw1526Labels := by decide +kernel
    rw [ha, hj, canonical1526 B hB]
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

theorem singleton4706 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4706 node4706Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1860 node1860Labels + mixedMoment B node1888 node1888Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1590 singletonSmall4706
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4706) = raw1590Labels := by decide +kernel
  rw [hl, canonical1590 B hB] at h
  have hc0 : mixedMoment B raw1590 (Fin.cases (0 : Fin 2) singletonSmall4706) =
      mixedMoment B node1860 node1860Labels := by
    have ha : raw1590 = raw1591 := by apply Matrix.ext; unfold raw1590 raw1591; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4706 = raw1591Labels := by decide +kernel
    rw [ha, hj, canonical1591 B hB]
  have hc1 : mixedMoment B raw1590 (Fin.cases (1 : Fin 2) singletonSmall4706) =
      mixedMoment B node1888 node1888Labels := by
    have ha : raw1590 = raw1592 := by apply Matrix.ext; unfold raw1590 raw1592; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4706 = raw1592Labels := by decide +kernel
    rw [ha, hj, canonical1592 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4717 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4717 node4717Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1871 node1871Labels + mixedMoment B node1892 node1892Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1611 singletonSmall4717
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4717) = raw1611Labels := by decide +kernel
  rw [hl, canonical1611 B hB] at h
  have hc0 : mixedMoment B raw1611 (Fin.cases (0 : Fin 2) singletonSmall4717) =
      mixedMoment B node1871 node1871Labels := by
    have ha : raw1611 = raw1612 := by apply Matrix.ext; unfold raw1611 raw1612; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4717 = raw1612Labels := by decide +kernel
    rw [ha, hj, canonical1612 B hB]
  have hc1 : mixedMoment B raw1611 (Fin.cases (1 : Fin 2) singletonSmall4717) =
      mixedMoment B node1892 node1892Labels := by
    have ha : raw1611 = raw1613 := by apply Matrix.ext; unfold raw1611 raw1613; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4717 = raw1613Labels := by decide +kernel
    rw [ha, hj, canonical1613 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4732 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4732 node4732Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1901 node1901Labels + mixedMoment B node1941 node1941Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1650 singletonSmall4732
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4732) = raw1650Labels := by decide +kernel
  rw [hl, canonical1650 B hB] at h
  have hc0 : mixedMoment B raw1650 (Fin.cases (0 : Fin 2) singletonSmall4732) =
      mixedMoment B node1901 node1901Labels := by
    have ha : raw1650 = raw1651 := by apply Matrix.ext; unfold raw1650 raw1651; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4732 = raw1651Labels := by decide +kernel
    rw [ha, hj, canonical1651 B hB]
  have hc1 : mixedMoment B raw1650 (Fin.cases (1 : Fin 2) singletonSmall4732) =
      mixedMoment B node1941 node1941Labels := by
    have ha : raw1650 = raw1652 := by apply Matrix.ext; unfold raw1650 raw1652; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4732 = raw1652Labels := by decide +kernel
    rw [ha, hj, canonical1652 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4767 node4767Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1967 node1967Labels + mixedMoment B node2183 node2183Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1701 singletonSmall4767
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4767) = raw1701Labels := by decide +kernel
  rw [hl, canonical1701 B hB] at h
  have hc0 : mixedMoment B raw1701 (Fin.cases (0 : Fin 2) singletonSmall4767) =
      mixedMoment B node1967 node1967Labels := by
    have ha : raw1701 = raw1702 := by apply Matrix.ext; unfold raw1701 raw1702; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4767 = raw1702Labels := by decide +kernel
    rw [ha, hj, canonical1702 B hB]
  have hc1 : mixedMoment B raw1701 (Fin.cases (1 : Fin 2) singletonSmall4767) =
      mixedMoment B node2183 node2183Labels := by
    have ha : raw1701 = raw1703 := by apply Matrix.ext; unfold raw1701 raw1703; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4767 = raw1703Labels := by decide +kernel
    rw [ha, hj, canonical1703 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4769 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4769 node4769Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1969 node1969Labels + mixedMoment B node2185 node2185Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1704 singletonSmall4769
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4769) = raw1704Labels := by decide +kernel
  rw [hl, canonical1704 B hB] at h
  have hc0 : mixedMoment B raw1704 (Fin.cases (0 : Fin 2) singletonSmall4769) =
      mixedMoment B node1969 node1969Labels := by
    have ha : raw1704 = raw1705 := by apply Matrix.ext; unfold raw1704 raw1705; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4769 = raw1705Labels := by decide +kernel
    rw [ha, hj, canonical1705 B hB]
  have hc1 : mixedMoment B raw1704 (Fin.cases (1 : Fin 2) singletonSmall4769) =
      mixedMoment B node2185 node2185Labels := by
    have ha : raw1704 = raw1706 := by apply Matrix.ext; unfold raw1704 raw1706; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4769 = raw1706Labels := by decide +kernel
    rw [ha, hj, canonical1706 B hB]
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

theorem singleton4802 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4802 node4802Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2020 node2020Labels + mixedMoment B node2202 node2202Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1734 singletonSmall4802
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4802) = raw1734Labels := by decide +kernel
  rw [hl, canonical1734 B hB] at h
  have hc0 : mixedMoment B raw1734 (Fin.cases (0 : Fin 2) singletonSmall4802) =
      mixedMoment B node2020 node2020Labels := by
    have ha : raw1734 = raw1735 := by apply Matrix.ext; unfold raw1734 raw1735; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4802 = raw1735Labels := by decide +kernel
    rw [ha, hj, canonical1735 B hB]
  have hc1 : mixedMoment B raw1734 (Fin.cases (1 : Fin 2) singletonSmall4802) =
      mixedMoment B node2202 node2202Labels := by
    have ha : raw1734 = raw1736 := by apply Matrix.ext; unfold raw1734 raw1736; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4802 = raw1736Labels := by decide +kernel
    rw [ha, hj, canonical1736 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4804 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4804 node4804Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2022 node2022Labels + mixedMoment B node2203 node2203Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1737 singletonSmall4804
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4804) = raw1737Labels := by decide +kernel
  rw [hl, canonical1737 B hB] at h
  have hc0 : mixedMoment B raw1737 (Fin.cases (0 : Fin 2) singletonSmall4804) =
      mixedMoment B node2022 node2022Labels := by
    have ha : raw1737 = raw1738 := by apply Matrix.ext; unfold raw1737 raw1738; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4804 = raw1738Labels := by decide +kernel
    rw [ha, hj, canonical1738 B hB]
  have hc1 : mixedMoment B raw1737 (Fin.cases (1 : Fin 2) singletonSmall4804) =
      mixedMoment B node2203 node2203Labels := by
    have ha : raw1737 = raw1739 := by apply Matrix.ext; unfold raw1737 raw1739; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4804 = raw1739Labels := by decide +kernel
    rw [ha, hj, canonical1739 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4811 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4811 node4811Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2029 node2029Labels + mixedMoment B node2225 node2225Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1749 singletonSmall4811
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4811) = raw1749Labels := by decide +kernel
  rw [hl, canonical1749 B hB] at h
  have hc0 : mixedMoment B raw1749 (Fin.cases (0 : Fin 2) singletonSmall4811) =
      mixedMoment B node2029 node2029Labels := by
    have ha : raw1749 = raw1750 := by apply Matrix.ext; unfold raw1749 raw1750; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4811 = raw1750Labels := by decide +kernel
    rw [ha, hj, canonical1750 B hB]
  have hc1 : mixedMoment B raw1749 (Fin.cases (1 : Fin 2) singletonSmall4811) =
      mixedMoment B node2225 node2225Labels := by
    have ha : raw1749 = raw1751 := by apply Matrix.ext; unfold raw1749 raw1751; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4811 = raw1751Labels := by decide +kernel
    rw [ha, hj, canonical1751 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4835 node4835Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2054 node2054Labels + mixedMoment B node2206 node2206Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1767 singletonSmall4835
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4835) = raw1767Labels := by decide +kernel
  rw [hl, canonical1767 B hB] at h
  have hc0 : mixedMoment B raw1767 (Fin.cases (0 : Fin 2) singletonSmall4835) =
      mixedMoment B node2054 node2054Labels := by
    have ha : raw1767 = raw1768 := by apply Matrix.ext; unfold raw1767 raw1768; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4835 = raw1768Labels := by decide +kernel
    rw [ha, hj, canonical1768 B hB]
  have hc1 : mixedMoment B raw1767 (Fin.cases (1 : Fin 2) singletonSmall4835) =
      mixedMoment B node2206 node2206Labels := by
    have ha : raw1767 = raw1769 := by apply Matrix.ext; unfold raw1767 raw1769; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4835 = raw1769Labels := by decide +kernel
    rw [ha, hj, canonical1769 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4888 node4888Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2244 node2244Labels + mixedMoment B node2262 node2262Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1815 singletonSmall4888
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4888) = raw1815Labels := by decide +kernel
  rw [hl, canonical1815 B hB] at h
  have hc0 : mixedMoment B raw1815 (Fin.cases (0 : Fin 2) singletonSmall4888) =
      mixedMoment B node2244 node2244Labels := by
    have ha : raw1815 = raw1816 := by apply Matrix.ext; unfold raw1815 raw1816; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4888 = raw1816Labels := by decide +kernel
    rw [ha, hj, canonical1816 B hB]
  have hc1 : mixedMoment B raw1815 (Fin.cases (1 : Fin 2) singletonSmall4888) =
      mixedMoment B node2262 node2262Labels := by
    have ha : raw1815 = raw1817 := by apply Matrix.ext; unfold raw1815 raw1817; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4888 = raw1817Labels := by decide +kernel
    rw [ha, hj, canonical1817 B hB]
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

theorem singleton5356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5356 node5356Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3694 node3694Labels + mixedMoment B node3773 node3773Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2403 singletonSmall5356
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5356) = raw2403Labels := by decide +kernel
  rw [hl, canonical2403 B hB] at h
  have hc0 : mixedMoment B raw2403 (Fin.cases (0 : Fin 2) singletonSmall5356) =
      mixedMoment B node3694 node3694Labels := by
    have ha : raw2403 = raw2404 := by apply Matrix.ext; unfold raw2403 raw2404; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5356 = raw2404Labels := by decide +kernel
    rw [ha, hj, canonical2404 B hB]
  have hc1 : mixedMoment B raw2403 (Fin.cases (1 : Fin 2) singletonSmall5356) =
      mixedMoment B node3773 node3773Labels := by
    have ha : raw2403 = raw2405 := by apply Matrix.ext; unfold raw2403 raw2405; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5356 = raw2405Labels := by decide +kernel
    rw [ha, hj, canonical2405 B hB]
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

theorem singleton5393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5393 node5393Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3779 node3779Labels + mixedMoment B node3797 node3797Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2460 singletonSmall5393
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5393) = raw2460Labels := by decide +kernel
  rw [hl, canonical2460 B hB] at h
  have hc0 : mixedMoment B raw2460 (Fin.cases (0 : Fin 2) singletonSmall5393) =
      mixedMoment B node3779 node3779Labels := by
    have ha : raw2460 = raw2461 := by apply Matrix.ext; unfold raw2460 raw2461; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5393 = raw2461Labels := by decide +kernel
    rw [ha, hj, canonical2461 B hB]
  have hc1 : mixedMoment B raw2460 (Fin.cases (1 : Fin 2) singletonSmall5393) =
      mixedMoment B node3797 node3797Labels := by
    have ha : raw2460 = raw2462 := by apply Matrix.ext; unfold raw2460 raw2462; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5393 = raw2462Labels := by decide +kernel
    rw [ha, hj, canonical2462 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node704 node704Labels = Sparse.eval nodeValue704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 704) = mixedMoment B node704 node704Labels := rfl
  simpa [nodeValue704, Sparse.eval] using hc.symm

theorem sound707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node707 node707Labels = Sparse.eval nodeValue707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 707) = mixedMoment B node707 node707Labels := rfl
  simpa [nodeValue707, Sparse.eval] using hc.symm

theorem sound725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node725 node725Labels = Sparse.eval nodeValue725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 725) = mixedMoment B node725 node725Labels := rfl
  simpa [nodeValue725, Sparse.eval] using hc.symm

theorem sound761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node761 node761Labels = Sparse.eval nodeValue761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 761) = mixedMoment B node761 node761Labels := rfl
  simpa [nodeValue761, Sparse.eval] using hc.symm

theorem sound763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node763 node763Labels = Sparse.eval nodeValue763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 763) = mixedMoment B node763 node763Labels := rfl
  simpa [nodeValue763, Sparse.eval] using hc.symm

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

theorem sound771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node771 node771Labels = Sparse.eval nodeValue771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 771) = mixedMoment B node771 node771Labels := rfl
  simpa [nodeValue771, Sparse.eval] using hc.symm

theorem sound790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node790 node790Labels = Sparse.eval nodeValue790 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 790) = mixedMoment B node790 node790Labels := rfl
  simpa [nodeValue790, Sparse.eval] using hc.symm

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

theorem sound848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node848 node848Labels = Sparse.eval nodeValue848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 848) = mixedMoment B node848 node848Labels := rfl
  simpa [nodeValue848, Sparse.eval] using hc.symm

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

theorem sound1764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1764 node1764Labels = Sparse.eval nodeValue1764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1764) = mixedMoment B node1764 node1764Labels := rfl
  simpa [nodeValue1764, Sparse.eval] using hc.symm

theorem sound1766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1766 node1766Labels = Sparse.eval nodeValue1766 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1766) = mixedMoment B node1766 node1766Labels := rfl
  simpa [nodeValue1766, Sparse.eval] using hc.symm

theorem sound1782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1782 node1782Labels = Sparse.eval nodeValue1782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1782) = mixedMoment B node1782 node1782Labels := rfl
  simpa [nodeValue1782, Sparse.eval] using hc.symm

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

theorem sound1848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1848 node1848Labels = Sparse.eval nodeValue1848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1848) = mixedMoment B node1848 node1848Labels := rfl
  simpa [nodeValue1848, Sparse.eval] using hc.symm

theorem sound1850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1850 node1850Labels = Sparse.eval nodeValue1850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1850) = mixedMoment B node1850 node1850Labels := rfl
  simpa [nodeValue1850, Sparse.eval] using hc.symm

theorem sound1855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1855 node1855Labels = Sparse.eval nodeValue1855 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1855) = mixedMoment B node1855 node1855Labels := rfl
  simpa [nodeValue1855, Sparse.eval] using hc.symm

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

theorem sound1860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1860 node1860Labels = Sparse.eval nodeValue1860 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1860) = mixedMoment B node1860 node1860Labels := rfl
  simpa [nodeValue1860, Sparse.eval] using hc.symm

theorem sound1871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1871 node1871Labels = Sparse.eval nodeValue1871 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1871) = mixedMoment B node1871 node1871Labels := rfl
  simpa [nodeValue1871, Sparse.eval] using hc.symm

theorem sound1888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1888 node1888Labels = Sparse.eval nodeValue1888 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1888) = mixedMoment B node1888 node1888Labels := rfl
  simpa [nodeValue1888, Sparse.eval] using hc.symm

theorem sound1892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1892 node1892Labels = Sparse.eval nodeValue1892 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1892) = mixedMoment B node1892 node1892Labels := rfl
  simpa [nodeValue1892, Sparse.eval] using hc.symm

theorem sound1901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1901 node1901Labels = Sparse.eval nodeValue1901 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1901) = mixedMoment B node1901 node1901Labels := rfl
  simpa [nodeValue1901, Sparse.eval] using hc.symm

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

theorem sound1941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1941 node1941Labels = Sparse.eval nodeValue1941 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1941) = mixedMoment B node1941 node1941Labels := rfl
  simpa [nodeValue1941, Sparse.eval] using hc.symm

theorem sound1967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1967 node1967Labels = Sparse.eval nodeValue1967 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1967) = mixedMoment B node1967 node1967Labels := rfl
  simpa [nodeValue1967, Sparse.eval] using hc.symm

theorem sound1969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1969 node1969Labels = Sparse.eval nodeValue1969 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1969) = mixedMoment B node1969 node1969Labels := rfl
  simpa [nodeValue1969, Sparse.eval] using hc.symm

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

theorem sound2020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2020 node2020Labels = Sparse.eval nodeValue2020 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2020) = mixedMoment B node2020 node2020Labels := rfl
  simpa [nodeValue2020, Sparse.eval] using hc.symm

theorem sound2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2022 node2022Labels = Sparse.eval nodeValue2022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2022) = mixedMoment B node2022 node2022Labels := rfl
  simpa [nodeValue2022, Sparse.eval] using hc.symm

theorem sound2029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2029 node2029Labels = Sparse.eval nodeValue2029 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2029) = mixedMoment B node2029 node2029Labels := rfl
  simpa [nodeValue2029, Sparse.eval] using hc.symm

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

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

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

theorem sound2183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2183 node2183Labels = Sparse.eval nodeValue2183 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2183) = mixedMoment B node2183 node2183Labels := rfl
  simpa [nodeValue2183, Sparse.eval] using hc.symm

theorem sound2185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2185 node2185Labels = Sparse.eval nodeValue2185 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2185) = mixedMoment B node2185 node2185Labels := rfl
  simpa [nodeValue2185, Sparse.eval] using hc.symm

theorem sound2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2202 node2202Labels = Sparse.eval nodeValue2202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2202) = mixedMoment B node2202 node2202Labels := rfl
  simpa [nodeValue2202, Sparse.eval] using hc.symm

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

theorem sound2225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2225 node2225Labels = Sparse.eval nodeValue2225 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2225) = mixedMoment B node2225 node2225Labels := rfl
  simpa [nodeValue2225, Sparse.eval] using hc.symm

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

theorem sound2244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2244 node2244Labels = Sparse.eval nodeValue2244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2244) = mixedMoment B node2244 node2244Labels := rfl
  simpa [nodeValue2244, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

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

theorem sound3694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3694 node3694Labels = Sparse.eval nodeValue3694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3694) = mixedMoment B node3694 node3694Labels := rfl
  simpa [nodeValue3694, Sparse.eval] using hc.symm

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

theorem sound3773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3773 node3773Labels = Sparse.eval nodeValue3773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3773) = mixedMoment B node3773 node3773Labels := rfl
  simpa [nodeValue3773, Sparse.eval] using hc.symm

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

theorem sound3779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3779 node3779Labels = Sparse.eval nodeValue3779 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3779) = mixedMoment B node3779 node3779Labels := rfl
  simpa [nodeValue3779, Sparse.eval] using hc.symm

theorem sound3797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3797 node3797Labels = Sparse.eval nodeValue3797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3797) = mixedMoment B node3797 node3797Labels := rfl
  simpa [nodeValue3797, Sparse.eval] using hc.symm

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

theorem sound4201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4201 node4201Labels = Sparse.eval nodeValue4201 (mixedVector B) := by
  have h := singleton4201 B _hB
  rw [sound704 B _hB _hF, sound761 B _hB _hF] at h
  norm_num [nodeValue4201, nodeValue704, nodeValue761, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4204 node4204Labels = Sparse.eval nodeValue4204 (mixedVector B) := by
  have h := singleton4204 B _hB
  rw [sound707 B _hB _hF, sound763 B _hB _hF] at h
  norm_num [nodeValue4204, nodeValue707, nodeValue763, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4224 node4224Labels = Sparse.eval nodeValue4224 (mixedVector B) := by
  have h := singleton4224 B _hB
  rw [sound725 B _hB _hF, sound771 B _hB _hF] at h
  norm_num [nodeValue4224, nodeValue725, nodeValue771, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4256 node4256Labels = Sparse.eval nodeValue4256 (mixedVector B) := by
  have h := singleton4256 B _hB
  rw [sound790 B _hB _hF, sound848 B _hB _hF] at h
  norm_num [nodeValue4256, nodeValue790, nodeValue848, Sparse.eval] at h ⊢
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

theorem sound4635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4635 node4635Labels = Sparse.eval nodeValue4635 (mixedVector B) := by
  have h := singleton4635 B _hB
  rw [sound1764 B _hB _hF, sound1848 B _hB _hF] at h
  norm_num [nodeValue4635, nodeValue1764, nodeValue1848, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4637 node4637Labels = Sparse.eval nodeValue4637 (mixedVector B) := by
  have h := singleton4637 B _hB
  rw [sound1766 B _hB _hF, sound1850 B _hB _hF] at h
  norm_num [nodeValue4637, nodeValue1766, nodeValue1850, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4654 node4654Labels = Sparse.eval nodeValue4654 (mixedVector B) := by
  have h := singleton4654 B _hB
  rw [sound1782 B _hB _hF, sound1855 B _hB _hF] at h
  norm_num [nodeValue4654, nodeValue1782, nodeValue1855, Sparse.eval] at h ⊢
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

theorem sound4706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4706 node4706Labels = Sparse.eval nodeValue4706 (mixedVector B) := by
  have h := singleton4706 B _hB
  rw [sound1860 B _hB _hF, sound1888 B _hB _hF] at h
  norm_num [nodeValue4706, nodeValue1860, nodeValue1888, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4717 node4717Labels = Sparse.eval nodeValue4717 (mixedVector B) := by
  have h := singleton4717 B _hB
  rw [sound1871 B _hB _hF, sound1892 B _hB _hF] at h
  norm_num [nodeValue4717, nodeValue1871, nodeValue1892, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4732 node4732Labels = Sparse.eval nodeValue4732 (mixedVector B) := by
  have h := singleton4732 B _hB
  rw [sound1901 B _hB _hF, sound1941 B _hB _hF] at h
  norm_num [nodeValue4732, nodeValue1901, nodeValue1941, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4767 node4767Labels = Sparse.eval nodeValue4767 (mixedVector B) := by
  have h := singleton4767 B _hB
  rw [sound1967 B _hB _hF, sound2183 B _hB _hF] at h
  norm_num [nodeValue4767, nodeValue1967, nodeValue2183, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4769 node4769Labels = Sparse.eval nodeValue4769 (mixedVector B) := by
  have h := singleton4769 B _hB
  rw [sound1969 B _hB _hF, sound2185 B _hB _hF] at h
  norm_num [nodeValue4769, nodeValue1969, nodeValue2185, Sparse.eval] at h ⊢
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

theorem sound4802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4802 node4802Labels = Sparse.eval nodeValue4802 (mixedVector B) := by
  have h := singleton4802 B _hB
  rw [sound2020 B _hB _hF, sound2202 B _hB _hF] at h
  norm_num [nodeValue4802, nodeValue2020, nodeValue2202, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4804 node4804Labels = Sparse.eval nodeValue4804 (mixedVector B) := by
  have h := singleton4804 B _hB
  rw [sound2022 B _hB _hF, sound2203 B _hB _hF] at h
  norm_num [nodeValue4804, nodeValue2022, nodeValue2203, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4811 node4811Labels = Sparse.eval nodeValue4811 (mixedVector B) := by
  have h := singleton4811 B _hB
  rw [sound2029 B _hB _hF, sound2225 B _hB _hF] at h
  norm_num [nodeValue4811, nodeValue2029, nodeValue2225, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4835 node4835Labels = Sparse.eval nodeValue4835 (mixedVector B) := by
  have h := singleton4835 B _hB
  rw [sound2054 B _hB _hF, sound2206 B _hB _hF] at h
  norm_num [nodeValue4835, nodeValue2054, nodeValue2206, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4888 node4888Labels = Sparse.eval nodeValue4888 (mixedVector B) := by
  have h := singleton4888 B _hB
  rw [sound2244 B _hB _hF, sound2262 B _hB _hF] at h
  norm_num [nodeValue4888, nodeValue2244, nodeValue2262, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5356 node5356Labels = Sparse.eval nodeValue5356 (mixedVector B) := by
  have h := singleton5356 B _hB
  rw [sound3694 B _hB _hF, sound3773 B _hB _hF] at h
  norm_num [nodeValue5356, nodeValue3694, nodeValue3773, Sparse.eval] at h ⊢
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

theorem sound5393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5393 node5393Labels = Sparse.eval nodeValue5393 (mixedVector B) := by
  have h := singleton5393 B _hB
  rw [sound3779 B _hB _hF, sound3797 B _hB _hF] at h
  norm_num [nodeValue5393, nodeValue3779, nodeValue3797, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources71
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2289 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2289 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2289 + difference 0 1) (sourceB2289 + difference 1 0) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2289 + difference 0 1) (sourceB2289 + difference 1 0) sourceC2289) = raw31562 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31562; decide +kernel
    rw [ha]
    exact (canonical31562 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2289 + difference 0 2) (sourceB2289 + difference 2 0) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2289 + difference 0 2) (sourceB2289 + difference 2 0) sourceC2289) = raw31563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31563; decide +kernel
    rw [ha]
    exact (canonical31563 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2289 + difference 0 3) (sourceB2289 + difference 3 0) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2289 + difference 0 3) (sourceB2289 + difference 3 0) sourceC2289) = raw31564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31564; decide +kernel
    rw [ha]
    exact (canonical31564 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2289 + difference 0 4) (sourceB2289 + difference 4 0) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2289 + difference 0 4) (sourceB2289 + difference 4 0) sourceC2289) = raw11315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw11315; decide +kernel
    rw [ha]
    exact (canonical11315 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2289 + difference 0 5) (sourceB2289 + difference 5 0) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2289 + difference 0 5) (sourceB2289 + difference 5 0) sourceC2289) = raw31565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31565; decide +kernel
    rw [ha]
    exact (canonical31565 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2289 + difference 1 0) (sourceB2289 + difference 0 1) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4256) := by
    have ha : (tripleCharges (sourceA2289 + difference 1 0) (sourceB2289 + difference 0 1) sourceC2289) = raw11335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw11335; decide +kernel
    rw [ha]
    exact (canonical11335 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2289 + difference 1 2) (sourceB2289 + difference 2 1) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2289 + difference 1 2) (sourceB2289 + difference 2 1) sourceC2289) = raw11337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw11337; decide +kernel
    rw [ha]
    exact (canonical11337 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2289 + difference 1 3) (sourceB2289 + difference 3 1) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4732) := by
    have ha : (tripleCharges (sourceA2289 + difference 1 3) (sourceB2289 + difference 3 1) sourceC2289) = raw11338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw11338; decide +kernel
    rw [ha]
    exact (canonical11338 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2289 + difference 1 4) (sourceB2289 + difference 4 1) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA2289 + difference 1 4) (sourceB2289 + difference 4 1) sourceC2289) = raw14329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw14329; decide +kernel
    rw [ha]
    exact (canonical14329 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2289 + difference 1 5) (sourceB2289 + difference 5 1) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA2289 + difference 1 5) (sourceB2289 + difference 5 1) sourceC2289) = raw11339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw11339; decide +kernel
    rw [ha]
    exact (canonical11339 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2289 + difference 2 0) (sourceB2289 + difference 0 2) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4224) := by
    have ha : (tripleCharges (sourceA2289 + difference 2 0) (sourceB2289 + difference 0 2) sourceC2289) = raw31566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31566; decide +kernel
    rw [ha]
    exact (canonical31566 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2289 + difference 2 1) (sourceB2289 + difference 1 2) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4654) := by
    have ha : (tripleCharges (sourceA2289 + difference 2 1) (sourceB2289 + difference 1 2) sourceC2289) = raw31567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31567; decide +kernel
    rw [ha]
    exact (canonical31567 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2289 + difference 2 3) (sourceB2289 + difference 3 2) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4717) := by
    have ha : (tripleCharges (sourceA2289 + difference 2 3) (sourceB2289 + difference 3 2) sourceC2289) = raw31568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31568; decide +kernel
    rw [ha]
    exact (canonical31568 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2289 + difference 2 4) (sourceB2289 + difference 4 2) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2289 + difference 2 4) (sourceB2289 + difference 4 2) sourceC2289) = raw11326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw11326; decide +kernel
    rw [ha]
    exact (canonical11326 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2289 + difference 2 5) (sourceB2289 + difference 5 2) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2289 + difference 2 5) (sourceB2289 + difference 5 2) sourceC2289) = raw31569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31569; decide +kernel
    rw [ha]
    exact (canonical31569 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2289 + difference 3 0) (sourceB2289 + difference 0 3) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4201) := by
    have ha : (tripleCharges (sourceA2289 + difference 3 0) (sourceB2289 + difference 0 3) sourceC2289) = raw31570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31570; decide +kernel
    rw [ha]
    exact (canonical31570 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2289 + difference 3 1) (sourceB2289 + difference 1 3) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4635) := by
    have ha : (tripleCharges (sourceA2289 + difference 3 1) (sourceB2289 + difference 1 3) sourceC2289) = raw31571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31571; decide +kernel
    rw [ha]
    exact (canonical31571 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2289 + difference 3 2) (sourceB2289 + difference 2 3) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4767) := by
    have ha : (tripleCharges (sourceA2289 + difference 3 2) (sourceB2289 + difference 2 3) sourceC2289) = raw31572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31572; decide +kernel
    rw [ha]
    exact (canonical31572 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2289 + difference 3 4) (sourceB2289 + difference 4 3) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2289 + difference 3 4) (sourceB2289 + difference 4 3) sourceC2289) = raw11331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw11331; decide +kernel
    rw [ha]
    exact (canonical11331 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2289 + difference 3 5) (sourceB2289 + difference 5 3) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2289 + difference 3 5) (sourceB2289 + difference 5 3) sourceC2289) = raw14326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw14326; decide +kernel
    rw [ha]
    exact (canonical14326 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2289 + difference 4 0) (sourceB2289 + difference 0 4) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4204) := by
    have ha : (tripleCharges (sourceA2289 + difference 4 0) (sourceB2289 + difference 0 4) sourceC2289) = raw31573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31573; decide +kernel
    rw [ha]
    exact (canonical31573 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2289 + difference 4 1) (sourceB2289 + difference 1 4) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4637) := by
    have ha : (tripleCharges (sourceA2289 + difference 4 1) (sourceB2289 + difference 1 4) sourceC2289) = raw31574 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31574; decide +kernel
    rw [ha]
    exact (canonical31574 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2289 + difference 4 2) (sourceB2289 + difference 2 4) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2289 + difference 4 2) (sourceB2289 + difference 2 4) sourceC2289) = raw31575 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31575; decide +kernel
    rw [ha]
    exact (canonical31575 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2289 + difference 4 3) (sourceB2289 + difference 3 4) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4706) := by
    have ha : (tripleCharges (sourceA2289 + difference 4 3) (sourceB2289 + difference 3 4) sourceC2289) = raw31576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31576; decide +kernel
    rw [ha]
    exact (canonical31576 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2289 + difference 4 5) (sourceB2289 + difference 5 4) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2289 + difference 4 5) (sourceB2289 + difference 5 4) sourceC2289) = raw31577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31577; decide +kernel
    rw [ha]
    exact (canonical31577 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2289 + difference 5 0) (sourceB2289 + difference 0 5) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4204) := by
    have ha : (tripleCharges (sourceA2289 + difference 5 0) (sourceB2289 + difference 0 5) sourceC2289) = raw31578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31578; decide +kernel
    rw [ha]
    exact (canonical31578 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2289 + difference 5 1) (sourceB2289 + difference 1 5) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4637) := by
    have ha : (tripleCharges (sourceA2289 + difference 5 1) (sourceB2289 + difference 1 5) sourceC2289) = raw31579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31579; decide +kernel
    rw [ha]
    exact (canonical31579 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2289 + difference 5 2) (sourceB2289 + difference 2 5) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2289 + difference 5 2) (sourceB2289 + difference 2 5) sourceC2289) = raw31580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31580; decide +kernel
    rw [ha]
    exact (canonical31580 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2289 + difference 5 3) (sourceB2289 + difference 3 5) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4706) := by
    have ha : (tripleCharges (sourceA2289 + difference 5 3) (sourceB2289 + difference 3 5) sourceC2289) = raw31581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31581; decide +kernel
    rw [ha]
    exact (canonical31581 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2289 + difference 5 4) (sourceB2289 + difference 4 5) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2289 + difference 5 4) (sourceB2289 + difference 4 5) sourceC2289) = raw11341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw11341; decide +kernel
    rw [ha]
    exact (canonical11341 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2289 sourceB2289 sourceC2289
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2289, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1871 : Integer.Sparse.reindex keyMap MixedData.row1871 = numericRow1871 := by decide +kernel

theorem numericCheck1871 (x : Master → ℝ) : Integer.Sparse.eval numericRow1871 x =
    (25920 : ℝ) * reducedSource1871 x := by
  norm_num [numericRow1871, reducedSource1871, Integer.Sparse.eval, Sparse.eval, nodeValue4201, nodeValue4204, nodeValue4224, nodeValue4256, nodeValue4635, nodeValue4637, nodeValue4654, nodeValue4706, nodeValue4717, nodeValue4732, nodeValue4767, nodeValue4769, nodeValue4802, nodeValue4804, nodeValue4811, nodeValue4835, nodeValue4888, nodeValue5356, nodeValue5393, nodeValue5418, nodeValue5434]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1871 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1871 (mixedVector B) = 0 := by
  have h4201 : mixedVector B (Sum.inr 4201) = Sparse.eval nodeValue4201 (mixedVector B) := by
    change mixedMoment B node4201 node4201Labels = _
    exact sound4201 B hB hF
  have h4204 : mixedVector B (Sum.inr 4204) = Sparse.eval nodeValue4204 (mixedVector B) := by
    change mixedMoment B node4204 node4204Labels = _
    exact sound4204 B hB hF
  have h4224 : mixedVector B (Sum.inr 4224) = Sparse.eval nodeValue4224 (mixedVector B) := by
    change mixedMoment B node4224 node4224Labels = _
    exact sound4224 B hB hF
  have h4256 : mixedVector B (Sum.inr 4256) = Sparse.eval nodeValue4256 (mixedVector B) := by
    change mixedMoment B node4256 node4256Labels = _
    exact sound4256 B hB hF
  have h4635 : mixedVector B (Sum.inr 4635) = Sparse.eval nodeValue4635 (mixedVector B) := by
    change mixedMoment B node4635 node4635Labels = _
    exact sound4635 B hB hF
  have h4637 : mixedVector B (Sum.inr 4637) = Sparse.eval nodeValue4637 (mixedVector B) := by
    change mixedMoment B node4637 node4637Labels = _
    exact sound4637 B hB hF
  have h4654 : mixedVector B (Sum.inr 4654) = Sparse.eval nodeValue4654 (mixedVector B) := by
    change mixedMoment B node4654 node4654Labels = _
    exact sound4654 B hB hF
  have h4706 : mixedVector B (Sum.inr 4706) = Sparse.eval nodeValue4706 (mixedVector B) := by
    change mixedMoment B node4706 node4706Labels = _
    exact sound4706 B hB hF
  have h4717 : mixedVector B (Sum.inr 4717) = Sparse.eval nodeValue4717 (mixedVector B) := by
    change mixedMoment B node4717 node4717Labels = _
    exact sound4717 B hB hF
  have h4732 : mixedVector B (Sum.inr 4732) = Sparse.eval nodeValue4732 (mixedVector B) := by
    change mixedMoment B node4732 node4732Labels = _
    exact sound4732 B hB hF
  have h4767 : mixedVector B (Sum.inr 4767) = Sparse.eval nodeValue4767 (mixedVector B) := by
    change mixedMoment B node4767 node4767Labels = _
    exact sound4767 B hB hF
  have h4769 : mixedVector B (Sum.inr 4769) = Sparse.eval nodeValue4769 (mixedVector B) := by
    change mixedMoment B node4769 node4769Labels = _
    exact sound4769 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h5356 : mixedVector B (Sum.inr 5356) = Sparse.eval nodeValue5356 (mixedVector B) := by
    change mixedMoment B node5356 node5356Labels = _
    exact sound5356 B hB hF
  have h5393 : mixedVector B (Sum.inr 5393) = Sparse.eval nodeValue5393 (mixedVector B) := by
    change mixedMoment B node5393 node5393Labels = _
    exact sound5393 B hB hF
  have h5418 : mixedVector B (Sum.inr 5418) = Sparse.eval nodeValue5418 (mixedVector B) := by
    change mixedMoment B node5418 node5418Labels = _
    exact sound5418_e B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  simpa only [sourceForm2289, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4201, h4204, h4224, h4256, h4635, h4637, h4654, h4706, h4717, h4732, h4767, h4769, h4802, h4804, h4811, h4835, h4888, h5356, h5393, h5418, h5434, reducedSource1871] using sourceEq2289 B hB

theorem rowSound1871_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1871 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1871, numericCheck1871, reducedZero1871 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e_oai
