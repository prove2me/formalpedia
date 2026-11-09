-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T02:33:12.819478+00:00
-- url     : https://prove2.me/submissions/a2727df2-ca95-416e-b4d6-6f44e9847819

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3882_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3980_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound4026_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15603 raw15603Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw15603 raw15603Labels = mixedMoment B raw15603step0 raw15603step0Labels := by
      have ha : raw15603step0 = (fun i j => raw15603 (permutation572 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15603step0 raw15603; decide +kernel
      have hl : raw15603step0Labels = raw15603Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15603 raw15603Labels permutation572 permutation7
    mixedMoment B raw15603step0 raw15603step0Labels = mixedMoment B raw15603step1 raw15603step1Labels := by
      have ha : raw15603step1 = raw15603step0 := by apply Matrix.ext; unfold raw15603step1 raw15603step0; decide +kernel
      have hl : raw15603step0Labels = labelEmbedding1 ∘ raw15603step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15603step0 raw15603step0Labels raw15603step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3956 node3956Labels := by rfl

theorem canonical15604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15604 raw15604Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw15604 raw15604Labels = mixedMoment B raw15604step0 raw15604step0Labels := by
      have ha : raw15604step0 = (fun i j => raw15604 (permutation573 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15604step0 raw15604; decide +kernel
      have hl : raw15604step0Labels = raw15604Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15604 raw15604Labels permutation573 permutation7
    mixedMoment B raw15604step0 raw15604step0Labels = mixedMoment B raw15604step1 raw15604step1Labels := by
      have ha : raw15604step1 = raw15604step0 := by apply Matrix.ext; unfold raw15604step1 raw15604step0; decide +kernel
      have hl : raw15604step0Labels = labelEmbedding1 ∘ raw15604step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15604step0 raw15604step0Labels raw15604step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

theorem canonical15605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15605 raw15605Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw15605 raw15605Labels = mixedMoment B raw15605step0 raw15605step0Labels := by
      have ha : raw15605step0 = (fun i j => raw15605 (permutation571 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15605step0 raw15605; decide +kernel
      have hl : raw15605step0Labels = raw15605Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15605 raw15605Labels permutation571 permutation7
    mixedMoment B raw15605step0 raw15605step0Labels = mixedMoment B raw15605step1 raw15605step1Labels := by
      have ha : raw15605step1 = raw15605step0 := by apply Matrix.ext; unfold raw15605step1 raw15605step0; decide +kernel
      have hl : raw15605step0Labels = labelEmbedding1 ∘ raw15605step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15605step0 raw15605step0Labels raw15605step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

theorem canonical15606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15606 raw15606Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw15606 raw15606Labels = mixedMoment B raw15606step0 raw15606step0Labels := by
      have ha : raw15606step0 = (fun i j => raw15606 (permutation572 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15606step0 raw15606; decide +kernel
      have hl : raw15606step0Labels = raw15606Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15606 raw15606Labels permutation572 permutation7
    mixedMoment B raw15606step0 raw15606step0Labels = mixedMoment B raw15606step1 raw15606step1Labels := by
      have ha : raw15606step1 = raw15606step0 := by apply Matrix.ext; unfold raw15606step1 raw15606step0; decide +kernel
      have hl : raw15606step0Labels = labelEmbedding1 ∘ raw15606step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15606step0 raw15606step0Labels raw15606step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

theorem canonical15607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15607 raw15607Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw15607 raw15607Labels = mixedMoment B raw15607step0 raw15607step0Labels := by
      have ha : raw15607step0 = (fun i j => raw15607 (permutation572 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15607step0 raw15607; decide +kernel
      have hl : raw15607step0Labels = raw15607Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15607 raw15607Labels permutation572 permutation7
    mixedMoment B raw15607step0 raw15607step0Labels = mixedMoment B raw15607step1 raw15607step1Labels := by
      have ha : raw15607step1 = raw15607step0 := by apply Matrix.ext; unfold raw15607step1 raw15607step0; decide +kernel
      have hl : raw15607step0Labels = labelEmbedding1 ∘ raw15607step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15607step0 raw15607step0Labels raw15607step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3980 node3980Labels := by rfl

theorem canonical15608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15608 raw15608Labels = mixedMoment B node2104 node2104Labels := by
  calc
    mixedMoment B raw15608 raw15608Labels = mixedMoment B raw15608step0 raw15608step0Labels := by
      have ha : raw15608step0 = (fun i j => raw15608 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15608step0 raw15608; decide +kernel
      have hl : raw15608step0Labels = raw15608Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15608 raw15608Labels permutation224 permutation5
    mixedMoment B raw15608step0 raw15608step0Labels = mixedMoment B raw15608step1 raw15608step1Labels := by
      have ha : raw15608step1 = -raw15608step0 := by apply Matrix.ext; change ∀ i j, raw15608step1 i j = -(raw15608step0 i j); unfold raw15608step1 raw15608step0; decide +kernel
      have hl : raw15608step1Labels = raw15608step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15608step1 raw15608step1Labels = mixedMoment B raw15608step2 raw15608step2Labels := by
      have ha : raw15608step2 = raw15608step1 := by apply Matrix.ext; unfold raw15608step2 raw15608step1; decide +kernel
      have hl : raw15608step1Labels = labelEmbedding1 ∘ raw15608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15608step1 raw15608step1Labels raw15608step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2104 node2104Labels := by rfl

theorem canonical15609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15609 raw15609Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw15609 raw15609Labels = mixedMoment B raw15609step0 raw15609step0Labels := by
      have ha : raw15609step0 = (fun i j => raw15609 (permutation230 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15609step0 raw15609; decide +kernel
      have hl : raw15609step0Labels = raw15609Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15609 raw15609Labels permutation230 permutation5
    mixedMoment B raw15609step0 raw15609step0Labels = mixedMoment B raw15609step1 raw15609step1Labels := by
      have ha : raw15609step1 = -raw15609step0 := by apply Matrix.ext; change ∀ i j, raw15609step1 i j = -(raw15609step0 i j); unfold raw15609step1 raw15609step0; decide +kernel
      have hl : raw15609step1Labels = raw15609step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15609step1 raw15609step1Labels = mixedMoment B raw15609step2 raw15609step2Labels := by
      have ha : raw15609step2 = raw15609step1 := by apply Matrix.ext; unfold raw15609step2 raw15609step1; decide +kernel
      have hl : raw15609step1Labels = labelEmbedding1 ∘ raw15609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15609step1 raw15609step1Labels raw15609step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

theorem canonical15610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15610 raw15610Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw15610 raw15610Labels = mixedMoment B raw15610step0 raw15610step0Labels := by
      have ha : raw15610step0 = (fun i j => raw15610 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15610step0 raw15610; decide +kernel
      have hl : raw15610step0Labels = raw15610Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15610 raw15610Labels permutation234 permutation5
    mixedMoment B raw15610step0 raw15610step0Labels = mixedMoment B raw15610step1 raw15610step1Labels := by
      have ha : raw15610step1 = -raw15610step0 := by apply Matrix.ext; change ∀ i j, raw15610step1 i j = -(raw15610step0 i j); unfold raw15610step1 raw15610step0; decide +kernel
      have hl : raw15610step1Labels = raw15610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15610step1 raw15610step1Labels = mixedMoment B raw15610step2 raw15610step2Labels := by
      have ha : raw15610step2 = raw15610step1 := by apply Matrix.ext; unfold raw15610step2 raw15610step1; decide +kernel
      have hl : raw15610step1Labels = labelEmbedding1 ∘ raw15610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15610step1 raw15610step1Labels raw15610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

theorem canonical15611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15611 raw15611Labels = mixedMoment B node3734 node3734Labels := by
  calc
    mixedMoment B raw15611 raw15611Labels = mixedMoment B raw15611step0 raw15611step0Labels := by
      have ha : raw15611step0 = (fun i j => raw15611 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15611step0 raw15611; decide +kernel
      have hl : raw15611step0Labels = raw15611Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15611 raw15611Labels permutation224 permutation5
    mixedMoment B raw15611step0 raw15611step0Labels = mixedMoment B raw15611step1 raw15611step1Labels := by
      have ha : raw15611step1 = -raw15611step0 := by apply Matrix.ext; change ∀ i j, raw15611step1 i j = -(raw15611step0 i j); unfold raw15611step1 raw15611step0; decide +kernel
      have hl : raw15611step1Labels = raw15611step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15611step1 raw15611step1Labels = mixedMoment B raw15611step2 raw15611step2Labels := by
      have ha : raw15611step2 = raw15611step1 := by apply Matrix.ext; unfold raw15611step2 raw15611step1; decide +kernel
      have hl : raw15611step1Labels = labelEmbedding1 ∘ raw15611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15611step1 raw15611step1Labels raw15611step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3734 node3734Labels := by rfl

theorem canonical15612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15612 raw15612Labels = mixedMoment B node3882 node3882Labels := by
  calc
    mixedMoment B raw15612 raw15612Labels = mixedMoment B raw15612step0 raw15612step0Labels := by
      have ha : raw15612step0 = (fun i j => raw15612 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15612step0 raw15612; decide +kernel
      have hl : raw15612step0Labels = raw15612Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15612 raw15612Labels permutation240 permutation5
    mixedMoment B raw15612step0 raw15612step0Labels = mixedMoment B raw15612step1 raw15612step1Labels := by
      have ha : raw15612step1 = -raw15612step0 := by apply Matrix.ext; change ∀ i j, raw15612step1 i j = -(raw15612step0 i j); unfold raw15612step1 raw15612step0; decide +kernel
      have hl : raw15612step1Labels = raw15612step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15612step1 raw15612step1Labels = mixedMoment B raw15612step2 raw15612step2Labels := by
      have ha : raw15612step2 = raw15612step1 := by apply Matrix.ext; unfold raw15612step2 raw15612step1; decide +kernel
      have hl : raw15612step1Labels = labelEmbedding1 ∘ raw15612step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15612step1 raw15612step1Labels raw15612step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3882 node3882Labels := by rfl

theorem canonical15613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15613 raw15613Labels = mixedMoment B node2076 node2076Labels := by
  calc
    mixedMoment B raw15613 raw15613Labels = mixedMoment B raw15613step0 raw15613step0Labels := by
      have ha : raw15613step0 = (fun i j => raw15613 (permutation227 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15613step0 raw15613; decide +kernel
      have hl : raw15613step0Labels = raw15613Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15613 raw15613Labels permutation227 permutation5
    mixedMoment B raw15613step0 raw15613step0Labels = mixedMoment B raw15613step1 raw15613step1Labels := by
      have ha : raw15613step1 = -raw15613step0 := by apply Matrix.ext; change ∀ i j, raw15613step1 i j = -(raw15613step0 i j); unfold raw15613step1 raw15613step0; decide +kernel
      have hl : raw15613step1Labels = raw15613step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15613step1 raw15613step1Labels = mixedMoment B raw15613step2 raw15613step2Labels := by
      have ha : raw15613step2 = raw15613step1 := by apply Matrix.ext; unfold raw15613step2 raw15613step1; decide +kernel
      have hl : raw15613step1Labels = labelEmbedding1 ∘ raw15613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15613step1 raw15613step1Labels raw15613step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2076 node2076Labels := by rfl

theorem canonical15614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15614 raw15614Labels = mixedMoment B node3750 node3750Labels := by
  calc
    mixedMoment B raw15614 raw15614Labels = mixedMoment B raw15614step0 raw15614step0Labels := by
      have ha : raw15614step0 = (fun i j => raw15614 (permutation167 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15614step0 raw15614; decide +kernel
      have hl : raw15614step0Labels = raw15614Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15614 raw15614Labels permutation167 permutation5
    mixedMoment B raw15614step0 raw15614step0Labels = mixedMoment B raw15614step1 raw15614step1Labels := by
      have ha : raw15614step1 = -raw15614step0 := by apply Matrix.ext; change ∀ i j, raw15614step1 i j = -(raw15614step0 i j); unfold raw15614step1 raw15614step0; decide +kernel
      have hl : raw15614step1Labels = raw15614step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15614step1 raw15614step1Labels = mixedMoment B raw15614step2 raw15614step2Labels := by
      have ha : raw15614step2 = raw15614step1 := by apply Matrix.ext; unfold raw15614step2 raw15614step1; decide +kernel
      have hl : raw15614step1Labels = labelEmbedding1 ∘ raw15614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15614step1 raw15614step1Labels raw15614step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3750 node3750Labels := by rfl

theorem canonical15615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15615 raw15615Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw15615 raw15615Labels = mixedMoment B raw15615step0 raw15615step0Labels := by
      have ha : raw15615step0 = (fun i j => raw15615 (permutation227 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15615step0 raw15615; decide +kernel
      have hl : raw15615step0Labels = raw15615Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15615 raw15615Labels permutation227 permutation5
    mixedMoment B raw15615step0 raw15615step0Labels = mixedMoment B raw15615step1 raw15615step1Labels := by
      have ha : raw15615step1 = -raw15615step0 := by apply Matrix.ext; change ∀ i j, raw15615step1 i j = -(raw15615step0 i j); unfold raw15615step1 raw15615step0; decide +kernel
      have hl : raw15615step1Labels = raw15615step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15615step1 raw15615step1Labels = mixedMoment B raw15615step2 raw15615step2Labels := by
      have ha : raw15615step2 = raw15615step1 := by apply Matrix.ext; unfold raw15615step2 raw15615step1; decide +kernel
      have hl : raw15615step1Labels = labelEmbedding1 ∘ raw15615step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15615step1 raw15615step1Labels raw15615step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3869 node3869Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15616 raw15616Labels = mixedMoment B node3720 node3720Labels := by
  calc
    mixedMoment B raw15616 raw15616Labels = mixedMoment B raw15616step0 raw15616step0Labels := by
      have ha : raw15616step0 = (fun i j => raw15616 (permutation227 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15616step0 raw15616; decide +kernel
      have hl : raw15616step0Labels = raw15616Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15616 raw15616Labels permutation227 permutation5
    mixedMoment B raw15616step0 raw15616step0Labels = mixedMoment B raw15616step1 raw15616step1Labels := by
      have ha : raw15616step1 = -raw15616step0 := by apply Matrix.ext; change ∀ i j, raw15616step1 i j = -(raw15616step0 i j); unfold raw15616step1 raw15616step0; decide +kernel
      have hl : raw15616step1Labels = raw15616step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15616step1 raw15616step1Labels = mixedMoment B raw15616step2 raw15616step2Labels := by
      have ha : raw15616step2 = raw15616step1 := by apply Matrix.ext; unfold raw15616step2 raw15616step1; decide +kernel
      have hl : raw15616step1Labels = labelEmbedding1 ∘ raw15616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15616step1 raw15616step1Labels raw15616step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3720 node3720Labels := by rfl

theorem canonical15617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15617 raw15617Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw15617 raw15617Labels = mixedMoment B raw15617step0 raw15617step0Labels := by
      have ha : raw15617step0 = (fun i j => raw15617 (permutation229 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15617step0 raw15617; decide +kernel
      have hl : raw15617step0Labels = raw15617Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15617 raw15617Labels permutation229 permutation5
    mixedMoment B raw15617step0 raw15617step0Labels = mixedMoment B raw15617step1 raw15617step1Labels := by
      have ha : raw15617step1 = -raw15617step0 := by apply Matrix.ext; change ∀ i j, raw15617step1 i j = -(raw15617step0 i j); unfold raw15617step1 raw15617step0; decide +kernel
      have hl : raw15617step1Labels = raw15617step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15617step1 raw15617step1Labels = mixedMoment B raw15617step2 raw15617step2Labels := by
      have ha : raw15617step2 = raw15617step1 := by apply Matrix.ext; unfold raw15617step2 raw15617step1; decide +kernel
      have hl : raw15617step1Labels = labelEmbedding1 ∘ raw15617step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15617step1 raw15617step1Labels raw15617step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

theorem canonical15618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15618 raw15618Labels = mixedMoment B node2076 node2076Labels := by
  calc
    mixedMoment B raw15618 raw15618Labels = mixedMoment B raw15618step0 raw15618step0Labels := by
      have ha : raw15618step0 = (fun i j => raw15618 (permutation225 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15618step0 raw15618; decide +kernel
      have hl : raw15618step0Labels = raw15618Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15618 raw15618Labels permutation225 permutation5
    mixedMoment B raw15618step0 raw15618step0Labels = mixedMoment B raw15618step1 raw15618step1Labels := by
      have ha : raw15618step1 = -raw15618step0 := by apply Matrix.ext; change ∀ i j, raw15618step1 i j = -(raw15618step0 i j); unfold raw15618step1 raw15618step0; decide +kernel
      have hl : raw15618step1Labels = raw15618step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15618step1 raw15618step1Labels = mixedMoment B raw15618step2 raw15618step2Labels := by
      have ha : raw15618step2 = raw15618step1 := by apply Matrix.ext; unfold raw15618step2 raw15618step1; decide +kernel
      have hl : raw15618step1Labels = labelEmbedding1 ∘ raw15618step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15618step1 raw15618step1Labels raw15618step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2076 node2076Labels := by rfl

theorem canonical15619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15619 raw15619Labels = mixedMoment B node3750 node3750Labels := by
  calc
    mixedMoment B raw15619 raw15619Labels = mixedMoment B raw15619step0 raw15619step0Labels := by
      have ha : raw15619step0 = (fun i j => raw15619 (permutation165 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15619step0 raw15619; decide +kernel
      have hl : raw15619step0Labels = raw15619Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15619 raw15619Labels permutation165 permutation5
    mixedMoment B raw15619step0 raw15619step0Labels = mixedMoment B raw15619step1 raw15619step1Labels := by
      have ha : raw15619step1 = -raw15619step0 := by apply Matrix.ext; change ∀ i j, raw15619step1 i j = -(raw15619step0 i j); unfold raw15619step1 raw15619step0; decide +kernel
      have hl : raw15619step1Labels = raw15619step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15619step1 raw15619step1Labels = mixedMoment B raw15619step2 raw15619step2Labels := by
      have ha : raw15619step2 = raw15619step1 := by apply Matrix.ext; unfold raw15619step2 raw15619step1; decide +kernel
      have hl : raw15619step1Labels = labelEmbedding1 ∘ raw15619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15619step1 raw15619step1Labels raw15619step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3750 node3750Labels := by rfl

theorem canonical15620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15620 raw15620Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw15620 raw15620Labels = mixedMoment B raw15620step0 raw15620step0Labels := by
      have ha : raw15620step0 = (fun i j => raw15620 (permutation225 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15620step0 raw15620; decide +kernel
      have hl : raw15620step0Labels = raw15620Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15620 raw15620Labels permutation225 permutation5
    mixedMoment B raw15620step0 raw15620step0Labels = mixedMoment B raw15620step1 raw15620step1Labels := by
      have ha : raw15620step1 = -raw15620step0 := by apply Matrix.ext; change ∀ i j, raw15620step1 i j = -(raw15620step0 i j); unfold raw15620step1 raw15620step0; decide +kernel
      have hl : raw15620step1Labels = raw15620step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15620step1 raw15620step1Labels = mixedMoment B raw15620step2 raw15620step2Labels := by
      have ha : raw15620step2 = raw15620step1 := by apply Matrix.ext; unfold raw15620step2 raw15620step1; decide +kernel
      have hl : raw15620step1Labels = labelEmbedding1 ∘ raw15620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15620step1 raw15620step1Labels raw15620step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3869 node3869Labels := by rfl

theorem canonical15621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15621 raw15621Labels = mixedMoment B node3720 node3720Labels := by
  calc
    mixedMoment B raw15621 raw15621Labels = mixedMoment B raw15621step0 raw15621step0Labels := by
      have ha : raw15621step0 = (fun i j => raw15621 (permutation225 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15621step0 raw15621; decide +kernel
      have hl : raw15621step0Labels = raw15621Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15621 raw15621Labels permutation225 permutation5
    mixedMoment B raw15621step0 raw15621step0Labels = mixedMoment B raw15621step1 raw15621step1Labels := by
      have ha : raw15621step1 = -raw15621step0 := by apply Matrix.ext; change ∀ i j, raw15621step1 i j = -(raw15621step0 i j); unfold raw15621step1 raw15621step0; decide +kernel
      have hl : raw15621step1Labels = raw15621step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15621step1 raw15621step1Labels = mixedMoment B raw15621step2 raw15621step2Labels := by
      have ha : raw15621step2 = raw15621step1 := by apply Matrix.ext; unfold raw15621step2 raw15621step1; decide +kernel
      have hl : raw15621step1Labels = labelEmbedding1 ∘ raw15621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15621step1 raw15621step1Labels raw15621step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3720 node3720Labels := by rfl

theorem canonical15622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15622 raw15622Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw15622 raw15622Labels = mixedMoment B raw15622step0 raw15622step0Labels := by
      have ha : raw15622step0 = (fun i j => raw15622 (permutation228 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15622step0 raw15622; decide +kernel
      have hl : raw15622step0Labels = raw15622Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15622 raw15622Labels permutation228 permutation5
    mixedMoment B raw15622step0 raw15622step0Labels = mixedMoment B raw15622step1 raw15622step1Labels := by
      have ha : raw15622step1 = -raw15622step0 := by apply Matrix.ext; change ∀ i j, raw15622step1 i j = -(raw15622step0 i j); unfold raw15622step1 raw15622step0; decide +kernel
      have hl : raw15622step1Labels = raw15622step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15622step1 raw15622step1Labels = mixedMoment B raw15622step2 raw15622step2Labels := by
      have ha : raw15622step2 = raw15622step1 := by apply Matrix.ext; unfold raw15622step2 raw15622step1; decide +kernel
      have hl : raw15622step1Labels = labelEmbedding1 ∘ raw15622step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15622step1 raw15622step1Labels raw15622step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

theorem canonical15623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15623 raw15623Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw15623 raw15623Labels = mixedMoment B raw15623step0 raw15623step0Labels := by
      have ha : raw15623step0 = (fun i j => raw15623 (permutation164 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15623step0 raw15623; decide +kernel
      have hl : raw15623step0Labels = raw15623Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15623 raw15623Labels permutation164 permutation5
    mixedMoment B raw15623step0 raw15623step0Labels = mixedMoment B raw15623step1 raw15623step1Labels := by
      have ha : raw15623step1 = -raw15623step0 := by apply Matrix.ext; change ∀ i j, raw15623step1 i j = -(raw15623step0 i j); unfold raw15623step1 raw15623step0; decide +kernel
      have hl : raw15623step1Labels = raw15623step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15623step1 raw15623step1Labels = mixedMoment B raw15623step2 raw15623step2Labels := by
      have ha : raw15623step2 = raw15623step1 := by apply Matrix.ext; unfold raw15623step2 raw15623step1; decide +kernel
      have hl : raw15623step1Labels = labelEmbedding1 ∘ raw15623step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15623step1 raw15623step1Labels raw15623step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

theorem canonical15624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15624 raw15624Labels = mixedMoment B node3768 node3768Labels := by
  calc
    mixedMoment B raw15624 raw15624Labels = mixedMoment B raw15624step0 raw15624step0Labels := by
      have ha : raw15624step0 = (fun i j => raw15624 (permutation164 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15624step0 raw15624; decide +kernel
      have hl : raw15624step0Labels = raw15624Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15624 raw15624Labels permutation164 permutation5
    mixedMoment B raw15624step0 raw15624step0Labels = mixedMoment B raw15624step1 raw15624step1Labels := by
      have ha : raw15624step1 = -raw15624step0 := by apply Matrix.ext; change ∀ i j, raw15624step1 i j = -(raw15624step0 i j); unfold raw15624step1 raw15624step0; decide +kernel
      have hl : raw15624step1Labels = raw15624step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15624step1 raw15624step1Labels = mixedMoment B raw15624step2 raw15624step2Labels := by
      have ha : raw15624step2 = raw15624step1 := by apply Matrix.ext; unfold raw15624step2 raw15624step1; decide +kernel
      have hl : raw15624step1Labels = labelEmbedding1 ∘ raw15624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15624step1 raw15624step1Labels raw15624step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3768 node3768Labels := by rfl

theorem canonical15625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15625 raw15625Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw15625 raw15625Labels = mixedMoment B raw15625step0 raw15625step0Labels := by
      have ha : raw15625step0 = (fun i j => raw15625 (permutation573 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15625step0 raw15625; decide +kernel
      have hl : raw15625step0Labels = raw15625Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15625 raw15625Labels permutation573 permutation7
    mixedMoment B raw15625step0 raw15625step0Labels = mixedMoment B raw15625step1 raw15625step1Labels := by
      have ha : raw15625step1 = raw15625step0 := by apply Matrix.ext; unfold raw15625step1 raw15625step0; decide +kernel
      have hl : raw15625step0Labels = labelEmbedding1 ∘ raw15625step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15625step0 raw15625step0Labels raw15625step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

theorem canonical15626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15626 raw15626Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw15626 raw15626Labels = mixedMoment B raw15626step0 raw15626step0Labels := by
      have ha : raw15626step0 = (fun i j => raw15626 (permutation571 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15626step0 raw15626; decide +kernel
      have hl : raw15626step0Labels = raw15626Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15626 raw15626Labels permutation571 permutation7
    mixedMoment B raw15626step0 raw15626step0Labels = mixedMoment B raw15626step1 raw15626step1Labels := by
      have ha : raw15626step1 = raw15626step0 := by apply Matrix.ext; unfold raw15626step1 raw15626step0; decide +kernel
      have hl : raw15626step0Labels = labelEmbedding1 ∘ raw15626step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15626step0 raw15626step0Labels raw15626step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

theorem canonical15627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15627 raw15627Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw15627 raw15627Labels = mixedMoment B raw15627step0 raw15627step0Labels := by
      have ha : raw15627step0 = (fun i j => raw15627 (permutation572 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15627step0 raw15627; decide +kernel
      have hl : raw15627step0Labels = raw15627Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15627 raw15627Labels permutation572 permutation7
    mixedMoment B raw15627step0 raw15627step0Labels = mixedMoment B raw15627step1 raw15627step1Labels := by
      have ha : raw15627step1 = raw15627step0 := by apply Matrix.ext; unfold raw15627step1 raw15627step0; decide +kernel
      have hl : raw15627step0Labels = labelEmbedding1 ∘ raw15627step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15627step0 raw15627step0Labels raw15627step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

theorem canonical15628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15628 raw15628Labels = mixedMoment B node2074 node2074Labels := by
  calc
    mixedMoment B raw15628 raw15628Labels = mixedMoment B raw15628step0 raw15628step0Labels := by
      have ha : raw15628step0 = (fun i j => raw15628 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15628step0 raw15628; decide +kernel
      have hl : raw15628step0Labels = raw15628Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15628 raw15628Labels permutation224 permutation5
    mixedMoment B raw15628step0 raw15628step0Labels = mixedMoment B raw15628step1 raw15628step1Labels := by
      have ha : raw15628step1 = -raw15628step0 := by apply Matrix.ext; change ∀ i j, raw15628step1 i j = -(raw15628step0 i j); unfold raw15628step1 raw15628step0; decide +kernel
      have hl : raw15628step1Labels = raw15628step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15628step1 raw15628step1Labels = mixedMoment B raw15628step2 raw15628step2Labels := by
      have ha : raw15628step2 = raw15628step1 := by apply Matrix.ext; unfold raw15628step2 raw15628step1; decide +kernel
      have hl : raw15628step1Labels = labelEmbedding1 ∘ raw15628step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15628step1 raw15628step1Labels raw15628step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2074 node2074Labels := by rfl

theorem canonical15629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15629 raw15629Labels = mixedMoment B node3491 node3491Labels := by
  calc
    mixedMoment B raw15629 raw15629Labels = mixedMoment B raw15629step0 raw15629step0Labels := by
      have ha : raw15629step0 = (fun i j => raw15629 (permutation640 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15629step0 raw15629; decide +kernel
      have hl : raw15629step0Labels = raw15629Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15629 raw15629Labels permutation640 permutation5
    mixedMoment B raw15629step0 raw15629step0Labels = mixedMoment B raw15629step1 raw15629step1Labels := by
      have ha : raw15629step1 = raw15629step0 := by apply Matrix.ext; unfold raw15629step1 raw15629step0; decide +kernel
      have hl : raw15629step0Labels = labelEmbedding1 ∘ raw15629step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15629step0 raw15629step0Labels raw15629step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3491 node3491Labels := by rfl

theorem canonical15630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15630 raw15630Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw15630 raw15630Labels = mixedMoment B raw15630step0 raw15630step0Labels := by
      have ha : raw15630step0 = (fun i j => raw15630 (permutation653 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15630step0 raw15630; decide +kernel
      have hl : raw15630step0Labels = raw15630Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15630 raw15630Labels permutation653 permutation5
    mixedMoment B raw15630step0 raw15630step0Labels = mixedMoment B raw15630step1 raw15630step1Labels := by
      have ha : raw15630step1 = raw15630step0 := by apply Matrix.ext; unfold raw15630step1 raw15630step0; decide +kernel
      have hl : raw15630step0Labels = labelEmbedding1 ∘ raw15630step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15630step0 raw15630step0Labels raw15630step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

theorem canonical15631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15631 raw15631Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw15631 raw15631Labels = mixedMoment B raw15631step0 raw15631step0Labels := by
      have ha : raw15631step0 = (fun i j => raw15631 (permutation632 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15631step0 raw15631; decide +kernel
      have hl : raw15631step0Labels = raw15631Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15631 raw15631Labels permutation632 permutation5
    mixedMoment B raw15631step0 raw15631step0Labels = mixedMoment B raw15631step1 raw15631step1Labels := by
      have ha : raw15631step1 = raw15631step0 := by apply Matrix.ext; unfold raw15631step1 raw15631step0; decide +kernel
      have hl : raw15631step0Labels = labelEmbedding1 ∘ raw15631step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15631step0 raw15631step0Labels raw15631step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

theorem canonical15632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15632 raw15632Labels = mixedMoment B node3488 node3488Labels := by
  calc
    mixedMoment B raw15632 raw15632Labels = mixedMoment B raw15632step0 raw15632step0Labels := by
      have ha : raw15632step0 = (fun i j => raw15632 (permutation638 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15632step0 raw15632; decide +kernel
      have hl : raw15632step0Labels = raw15632Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15632 raw15632Labels permutation638 permutation5
    mixedMoment B raw15632step0 raw15632step0Labels = mixedMoment B raw15632step1 raw15632step1Labels := by
      have ha : raw15632step1 = raw15632step0 := by apply Matrix.ext; unfold raw15632step1 raw15632step0; decide +kernel
      have hl : raw15632step0Labels = labelEmbedding1 ∘ raw15632step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15632step0 raw15632step0Labels raw15632step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3488 node3488Labels := by rfl

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

theorem canonical488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw488 raw488Labels = mixedMoment B node3734 node3734Labels := by
  calc
    mixedMoment B raw488 raw488Labels = mixedMoment B raw488step0 raw488step0Labels := by
      have ha : raw488step0 = (fun i j => raw488 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw488step0 raw488; decide +kernel
      have hl : raw488step0Labels = raw488Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw488 raw488Labels permutation152 permutation5
    mixedMoment B raw488step0 raw488step0Labels = mixedMoment B raw488step1 raw488step1Labels := by
      have ha : raw488step1 = raw488step0 := by apply Matrix.ext; unfold raw488step1 raw488step0; decide +kernel
      have hl : raw488step0Labels = labelEmbedding1 ∘ raw488step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw488step0 raw488step0Labels raw488step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3734 node3734Labels := by rfl

theorem canonical489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw489 raw489Labels = mixedMoment B node445 node445Labels := by
  calc
    mixedMoment B raw489 raw489Labels = mixedMoment B raw489step0 raw489step0Labels := by
      have ha : raw489step0 = (fun i j => raw489 (permutation283 i) (permutation4 j)) := by apply Matrix.ext; unfold raw489step0 raw489; decide +kernel
      have hl : raw489step0Labels = raw489Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw489 raw489Labels permutation283 permutation4
    _ = mixedMoment B node445 node445Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3886 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3886 = injectiveMoment H node2118 := by
  calc
    injectiveMoment H raw3886 = injectiveMoment H raw3886step0 := by
      have heq : raw3886step0 = -raw3886 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3886).symm
    injectiveMoment H raw3886step0 = injectiveMoment H raw3886step1 := by
      have heq : raw3886step1 = (fun i j => raw3886step0 (permutation205 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3886step0 permutation205 permutation6
    _ = injectiveMoment H node2118 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5109 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5109 = injectiveMoment H node716 := by
  rfl

theorem canonical5110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5110 = injectiveMoment H node231 := by
  rfl

theorem canonical5111 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5111 = injectiveMoment H node231 := by
  calc
    injectiveMoment H raw5111 = injectiveMoment H raw5111step0 := by
      have heq : raw5111step0 = (fun i j => raw5111 (permutation34 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5111 permutation34 permutation1
    _ = injectiveMoment H node231 := by rfl

theorem canonical5112 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5112 = injectiveMoment H node25 := by
  calc
    injectiveMoment H raw5112 = injectiveMoment H raw5112step0 := by
      have heq : raw5112step0 = (fun i j => raw5112 (permutation31 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5112 permutation31 permutation2
    _ = injectiveMoment H node25 := by rfl

theorem canonical5115 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5115 = injectiveMoment H node231 := by
  calc
    injectiveMoment H raw5115 = injectiveMoment H raw5115step0 := by
      have heq : raw5115step0 = (fun i j => raw5115 (permutation36 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5115 permutation36 permutation1
    _ = injectiveMoment H node231 := by rfl

theorem canonical5116 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5116 = injectiveMoment H node45 := by
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

theorem canonical5139 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5139 = injectiveMoment H node232 := by
  rfl

theorem canonical5141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5141 = injectiveMoment H node46 := by
  rfl

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

theorem canonical5156 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5156 = injectiveMoment H node232 := by
  clear _hH
  calc
    injectiveMoment H raw5156 = injectiveMoment H raw5156step0 := by
      have hz : ∀ j, raw5156 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw5156step0 = (fun i j => raw5156 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5156 permutation202 hz
    _ = injectiveMoment H node232 := by rfl

theorem canonical5177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5177 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5177 = injectiveMoment H raw5177step0 := by
      have hz : ∀ j, raw5177 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5177step0 = (fun i j => raw5177 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5177 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7982 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7982 = injectiveMoment H raw7982step0 := by
      have hz : ∀ j, raw7982 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7982step0 = (fun i j => raw7982 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982 permutation308 hz
    injectiveMoment H raw7982step0 = injectiveMoment H raw7982step1 := by
      have hz : ∀ j, raw7982step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7982step1 = (fun i j => raw7982step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step0 permutation128 hz
    injectiveMoment H raw7982step1 = injectiveMoment H raw7982step2 := by
      have hz : ∀ j, raw7982step1 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7982step2 = (fun i j => raw7982step1 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step1 permutation27 hz
    injectiveMoment H raw7982step2 = injectiveMoment H raw7982step3 := by
      have hz : ∀ j, raw7982step2 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7982step3 = (fun i j => raw7982step2 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step2 permutation7 hz
    injectiveMoment H raw7982step3 = injectiveMoment H raw7982step4 := by
      have hz : ∀ j, raw7982step3 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7982step4 = (fun i j => raw7982step3 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step3 permutation2 hz
    injectiveMoment H raw7982step4 = injectiveMoment H raw7982step5 := by
      have hz : ∀ j, raw7982step4 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7982step5 = (fun i j => raw7982step4 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step4 permutation0 hz
    injectiveMoment H raw7982step5 = injectiveMoment H raw7982step6 := by
      have hz : ∀ i, raw7982step5 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7982step6 = (fun i j => raw7982step5 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7982step5 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

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

theorem canonical8989 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8989 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8989 = injectiveMoment H raw8989step0 := by
      have hz : ∀ j, raw8989 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw8989step0 = (fun i j => raw8989 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8989 permutation308 hz
    injectiveMoment H raw8989step0 = injectiveMoment H raw8989step1 := by
      have hz : ∀ j, raw8989step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8989step1 = (fun i j => raw8989step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8989step0 permutation128 hz
    injectiveMoment H raw8989step1 = injectiveMoment H raw8989step2 := by
      have hz : ∀ j, raw8989step1 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw8989step2 = (fun i j => raw8989step1 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8989step1 permutation27 hz
    injectiveMoment H raw8989step2 = injectiveMoment H raw8989step3 := by
      have hz : ∀ j, raw8989step2 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8989step3 = (fun i j => raw8989step2 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8989step2 permutation3 hz
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

theorem canonical8216 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8216 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8216 = injectiveMoment H raw8216step0 := by
      have hz : ∀ j, raw8216 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw8216step0 = (fun i j => raw8216 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8216 permutation7 hz
    injectiveMoment H raw8216step0 = injectiveMoment H raw8216step1 := by
      have hz : ∀ i, raw8216step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8216step1 = (fun i j => raw8216step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8216step0 permutation3 hz
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

theorem canonical914 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw914 = injectiveMoment H node26 := by
  rfl

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

theorem sound26 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node26 = Sparse.eval value26 (momentVector H) := by
  have heq : pivotMatrix26 = (fun u v => node26 (pivotPermutation26 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node26 = injectiveMoment H pivotMatrix26 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix26 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix26 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix26 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix26 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (1 : Fin 3) = raw924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical924 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix26 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (2 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node26 + (injectiveMoment H (mergeFirst pivotMatrix26 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix26 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix26 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value26, value10, value11, Sparse.eval] at hc ⊢
  linarith

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

theorem sound45 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node45 = Sparse.eval value45 (momentVector H) := by
  have hc : momentVector H 27 = injectiveMoment H node45 := rfl
  simp [value45, Sparse.eval, hc]

theorem sound46 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node46 = Sparse.eval value46 (momentVector H) := by
  have heq : pivotMatrix46 = (fun u v => node46 (pivotPermutation46 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node46 = injectiveMoment H pivotMatrix46 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix46 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix46 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (1 : Fin 3) = raw5183 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5183 hH).trans (sound4 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (2 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node46 + (injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value46, value10, value11, value4, Sparse.eval] at hc ⊢
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

theorem canonical4034 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4034 = injectiveMoment H node197 := by
  rfl

theorem canonical4037 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4037 = injectiveMoment H node198 := by
  rfl

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

theorem canonical4134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4134 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4134 = injectiveMoment H raw4134step0 := by
      have heq : raw4134step0 = (fun i j => raw4134 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4134 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4023 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4023 = injectiveMoment H node641 := by
  rfl

theorem canonical4024 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4024 = injectiveMoment H node642 := by
  rfl

theorem canonical4029 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4029 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw4029 = injectiveMoment H raw4029step0 := by
      have heq : raw4029step0 = -raw4029 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4029).symm
    injectiveMoment H raw4029step0 = injectiveMoment H raw4029step1 := by
      have heq : raw4029step1 = (fun i j => raw4029step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4029step0 permutation32 permutation3
    _ = injectiveMoment H node169 := by rfl

theorem canonical4031 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4031 = injectiveMoment H node642 := by
  calc
    injectiveMoment H raw4031 = injectiveMoment H raw4031step0 := by
      have heq : raw4031step0 = (fun i j => raw4031 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4031 permutation35 permutation3
    _ = injectiveMoment H node642 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4067 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4067 = injectiveMoment H node655 := by
  rfl

theorem canonical4074 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4074 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw4074 = injectiveMoment H raw4074step0 := by
      have heq : raw4074step0 = (fun i j => raw4074 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4074 permutation16 permutation5
    _ = injectiveMoment H node291 := by rfl

theorem canonical4079 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4079 = injectiveMoment H node203 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4096 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4096 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4096 = injectiveMoment H raw4096step0 := by
      have hz : ∀ j, raw4096 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw4096step0 = (fun i j => raw4096 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4096 permutation15 hz
    injectiveMoment H raw4096step0 = injectiveMoment H raw4096step1 := by
      have heq : raw4096step1 = (fun i j => raw4096step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4096step0 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

theorem canonical4110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4110 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4110 = injectiveMoment H raw4110step0 := by
      have hz : ∀ j, raw4110 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw4110step0 = (fun i j => raw4110 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4110 permutation21 hz
    injectiveMoment H raw4110step0 = injectiveMoment H raw4110step1 := by
      have heq : raw4110step1 = (fun i j => raw4110step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4110step0 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

theorem canonical4117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4117 = injectiveMoment H node207 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4912 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4912 = injectiveMoment H node704 := by
  rfl

theorem canonical4915 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4915 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw4915 = injectiveMoment H raw4915step0 := by
      have heq : raw4915step0 = -raw4915 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4915).symm
    injectiveMoment H raw4915step0 = injectiveMoment H raw4915step1 := by
      have heq : raw4915step1 = (fun i j => raw4915step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4915step0 permutation32 permutation3
    _ = injectiveMoment H node203 := by rfl

theorem canonical4918 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4918 = injectiveMoment H node224 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4943 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4943 = injectiveMoment H node227 := by
  rfl

theorem canonical4950 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4950 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw4950 = injectiveMoment H raw4950step0 := by
      have heq : raw4950step0 = raw4950.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4950).symm
    injectiveMoment H raw4950step0 = injectiveMoment H raw4950step1 := by
      have hz : ∀ i, raw4950step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw4950step1 = (fun i j => raw4950step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4950step0 permutation5 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical4956 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4956 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4956 = injectiveMoment H raw4956step0 := by
      have heq : raw4956step0 = -raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4956).symm
    injectiveMoment H raw4956step0 = injectiveMoment H raw4956step1 := by
      have heq : raw4956step1 = (fun i j => raw4956step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4956step0 permutation4 permutation8
    _ = injectiveMoment H node62 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5384 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5384 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw5384 = injectiveMoment H raw5384step0 := by
      have heq : raw5384step0 = (fun i j => raw5384 (permutation11 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5384 permutation11 permutation4
    _ = injectiveMoment H node203 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2803 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2803 = injectiveMoment H node176 := by
  rfl

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

theorem sound176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node176 = Sparse.eval value176 (momentVector H) := by
  have heq : pivotMatrix176 = (fun u v => node176 (pivotPermutation176 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node176 = injectiveMoment H pivotMatrix176 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix176 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix176 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (0 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (1 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (2 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node176 + (injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value176, value36, value57, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical238
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7634 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7634 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7634 = injectiveMoment H raw7634step0 := by
      have heq : raw7634step0 = (fun i j => raw7634 (permutation57 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7634 permutation57 permutation1
    _ = injectiveMoment H node232 := by rfl

theorem canonical7636 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7636 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7636 = injectiveMoment H raw7636step0 := by
      have heq : raw7636step0 = (fun i j => raw7636 (permutation15 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7636 permutation15 permutation1
    _ = injectiveMoment H node46 := by rfl

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

theorem sound197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node197 = Sparse.eval value197 (momentVector H) := by
  have hc : momentVector H 23 = injectiveMoment H node197 := rfl
  simp [value197, Sparse.eval, hc]

theorem sound198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node198 = Sparse.eval value198 (momentVector H) := by
  have hc : momentVector H 54 = injectiveMoment H node198 := rfl
  simp [value198, Sparse.eval, hc]

theorem sound203 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node203 = Sparse.eval value203 (momentVector H) := by
  have heq : pivotMatrix203 = (fun u v => node203 (pivotPermutation203 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node203 = injectiveMoment H pivotMatrix203 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix203 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix203 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (0 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (1 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (2 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node203 + (injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value203, value36, value41, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound207 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node207 = Sparse.eval value207 (momentVector H) := by
  have heq : pivotMatrix207 = (fun u v => node207 (pivotPermutation207 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node207 = injectiveMoment H pivotMatrix207 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix207 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix207 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix207 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (0 : Fin 3) = raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4956 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix207 (1 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (1 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix207 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (2 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node207 + (injectiveMoment H (mergeFirst pivotMatrix207 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix207 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix207 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value207, value41, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound224 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node224 = Sparse.eval value224 (momentVector H) := by
  have hc : momentVector H 25 = injectiveMoment H node224 := rfl
  simp [value224, Sparse.eval, hc]

theorem sound227 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node227 = Sparse.eval value227 (momentVector H) := by
  have heq : pivotMatrix227 = (fun u v => node227 (pivotPermutation227 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node227 = injectiveMoment H pivotMatrix227 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix227 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix227 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix227 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (0 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix227 (1 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (1 : Fin 3) = raw4950 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4950 hH).trans (sound11 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix227 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (2 : Fin 3) = raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4956 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node227 + (injectiveMoment H (mergeFirst pivotMatrix227 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix227 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix227 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value227, value11, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound231 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node231 = Sparse.eval value231 (momentVector H) := by
  have heq : pivotMatrix231 = (fun u v => node231 (pivotPermutation231 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node231 = injectiveMoment H pivotMatrix231 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix231 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix231 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix231 (0 : Fin 4)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : mergeFirst pivotMatrix231 (0 : Fin 4) = raw7636 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7636 hH).trans (sound46 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix231 (1 : Fin 4)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : mergeFirst pivotMatrix231 (1 : Fin 4) = raw5141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5141 hH).trans (sound46 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix231 (2 : Fin 4)) =
      Sparse.eval value45 (momentVector H) := by
    have heq : mergeFirst pivotMatrix231 (2 : Fin 4) = raw5116 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5116 hH).trans (sound45 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix231 (3 : Fin 4)) =
      Sparse.eval value25 (momentVector H) := by
    have heq : mergeFirst pivotMatrix231 (3 : Fin 4) = raw5112 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5112 hH).trans (sound25 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node231 + (injectiveMoment H (mergeFirst pivotMatrix231 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix231 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix231 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix231 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value231, value25, value45, value46, Sparse.eval] at hc ⊢
  linarith

theorem sound232 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node232 = Sparse.eval value232 (momentVector H) := by
  have heq : pivotMatrix232 = (fun u v => node232 (pivotPermutation232 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node232 = injectiveMoment H pivotMatrix232 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix232 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix232 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix232 (0 : Fin 4)) =
      Sparse.eval value26 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (0 : Fin 4) = raw914 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical914 hH).trans (sound26 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix232 (1 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (1 : Fin 4) = raw5177 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5177 hH).trans (sound11 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix232 (2 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (2 : Fin 4) = raw5197 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5197 hH).trans (sound11 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix232 (3 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (3 : Fin 4) = raw5204 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5204 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node232 + (injectiveMoment H (mergeFirst pivotMatrix232 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value232, value11, value26, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical255
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8167 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw8167 = injectiveMoment H raw8167step0 := by
      have heq : raw8167step0 = (fun i j => raw8167 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8167 permutation5 permutation4
    _ = injectiveMoment H node62 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound4
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound291 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node291 = Sparse.eval value291 (momentVector H) := by
  have heq : pivotMatrix291 = (fun u v => node291 (pivotPermutation291 u) v) := by apply Matrix.ext; unfold pivotMatrix291 node291 pivotPermutation291; decide +kernel
  have hmoment : injectiveMoment H node291 = injectiveMoment H pivotMatrix291 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix291 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix291 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix291 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix291 (0 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix291 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix291 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix291 (1 : Fin 3) = raw8167 := by apply Matrix.ext; unfold mergeFirst pivotMatrix291 raw8167; decide +kernel
    rw [heq]
    exact (canonical8167 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix291 (2 : Fin 3)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix291 (2 : Fin 3) = raw8216 := by apply Matrix.ext; unfold mergeFirst pivotMatrix291 raw8216; decide +kernel
    rw [heq]
    exact (canonical8216 hH).trans (sound4 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node291 + (injectiveMoment H (mergeFirst pivotMatrix291 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix291 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix291 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value291, value4, value57, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound10
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound641 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node641 = Sparse.eval value641 (momentVector H) := by
  have heq : pivotMatrix641 = (fun u v => node641 (pivotPermutation641 u) v) := by apply Matrix.ext; unfold pivotMatrix641 node641 pivotPermutation641; decide +kernel
  have hmoment : injectiveMoment H node641 = injectiveMoment H pivotMatrix641 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix641 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix641 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix641 (0 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix641 (0 : Fin 4) = raw4915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix641 raw4915; decide +kernel
    rw [heq]
    exact (canonical4915 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix641 (1 : Fin 4)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix641 (1 : Fin 4) = raw4074 := by apply Matrix.ext; unfold mergeFirst pivotMatrix641 raw4074; decide +kernel
    rw [heq]
    exact (canonical4074 hH).trans (sound291 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix641 (2 : Fin 4)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix641 (2 : Fin 4) = raw4034 := by apply Matrix.ext; unfold mergeFirst pivotMatrix641 raw4034; decide +kernel
    rw [heq]
    exact (canonical4034 hH).trans (sound197 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix641 (3 : Fin 4)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix641 (3 : Fin 4) = raw4029 := by apply Matrix.ext; unfold mergeFirst pivotMatrix641 raw4029; decide +kernel
    rw [heq]
    exact (canonical4029 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node641 + (injectiveMoment H (mergeFirst pivotMatrix641 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix641 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix641 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix641 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value641, value169, value197, value203, value291, Sparse.eval] at hc ⊢
  linarith

theorem sound642 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node642 = Sparse.eval value642 (momentVector H) := by
  have heq : pivotMatrix642 = (fun u v => node642 (pivotPermutation642 u) v) := by apply Matrix.ext; unfold pivotMatrix642 node642 pivotPermutation642; decide +kernel
  have hmoment : injectiveMoment H node642 = injectiveMoment H pivotMatrix642 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix642 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix642 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix642 (0 : Fin 4)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix642 (0 : Fin 4) = raw4918 := by apply Matrix.ext; unfold mergeFirst pivotMatrix642 raw4918; decide +kernel
    rw [heq]
    exact (canonical4918 hH).trans (sound224 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix642 (1 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix642 (1 : Fin 4) = raw4079 := by apply Matrix.ext; unfold mergeFirst pivotMatrix642 raw4079; decide +kernel
    rw [heq]
    exact (canonical4079 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix642 (2 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix642 (2 : Fin 4) = raw4037 := by apply Matrix.ext; unfold mergeFirst pivotMatrix642 raw4037; decide +kernel
    rw [heq]
    exact (canonical4037 hH).trans (sound198 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix642 (3 : Fin 4)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix642 (3 : Fin 4) = raw4034 := by apply Matrix.ext; unfold mergeFirst pivotMatrix642 raw4034; decide +kernel
    rw [heq]
    exact (canonical4034 hH).trans (sound197 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node642 + (injectiveMoment H (mergeFirst pivotMatrix642 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix642 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix642 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix642 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value642, value197, value198, value203, value224, Sparse.eval] at hc ⊢
  linarith

theorem sound655 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node655 = Sparse.eval value655 (momentVector H) := by
  have heq : pivotMatrix655 = (fun u v => node655 (pivotPermutation655 u) v) := by apply Matrix.ext; unfold pivotMatrix655 node655 pivotPermutation655; decide +kernel
  have hmoment : injectiveMoment H node655 = injectiveMoment H pivotMatrix655 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix655 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix655 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix655 (0 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix655 (0 : Fin 4) = raw2803 := by apply Matrix.ext; unfold mergeFirst pivotMatrix655 raw2803; decide +kernel
    rw [heq]
    exact (canonical2803 hH).trans (sound176 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix655 (1 : Fin 4)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix655 (1 : Fin 4) = raw4096 := by apply Matrix.ext; unfold mergeFirst pivotMatrix655 raw4096; decide +kernel
    rw [heq]
    exact (canonical4096 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix655 (2 : Fin 4)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix655 (2 : Fin 4) = raw4110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix655 raw4110; decide +kernel
    rw [heq]
    exact (canonical4110 hH).trans (sound62 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix655 (3 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix655 (3 : Fin 4) = raw4117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix655 raw4117; decide +kernel
    rw [heq]
    exact (canonical4117 hH).trans (sound207 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node655 + (injectiveMoment H (mergeFirst pivotMatrix655 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix655 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix655 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix655 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value655, value176, value207, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound11
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound704 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node704 = Sparse.eval value704 (momentVector H) := by
  have heq : pivotMatrix704 = (fun u v => node704 (pivotPermutation704 u) v) := by apply Matrix.ext; unfold pivotMatrix704 node704 pivotPermutation704; decide +kernel
  have hmoment : injectiveMoment H node704 = injectiveMoment H pivotMatrix704 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix704 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix704 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix704 (0 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix704 (0 : Fin 4) = raw5384 := by apply Matrix.ext; unfold mergeFirst pivotMatrix704 raw5384; decide +kernel
    rw [heq]
    exact (canonical5384 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix704 (1 : Fin 4)) =
      Sparse.eval value227 (momentVector H) := by
    have heq : mergeFirst pivotMatrix704 (1 : Fin 4) = raw4943 := by apply Matrix.ext; unfold mergeFirst pivotMatrix704 raw4943; decide +kernel
    rw [heq]
    exact (canonical4943 hH).trans (sound227 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix704 (2 : Fin 4)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix704 (2 : Fin 4) = raw4918 := by apply Matrix.ext; unfold mergeFirst pivotMatrix704 raw4918; decide +kernel
    rw [heq]
    exact (canonical4918 hH).trans (sound224 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix704 (3 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix704 (3 : Fin 4) = raw4915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix704 raw4915; decide +kernel
    rw [heq]
    exact (canonical4915 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node704 + (injectiveMoment H (mergeFirst pivotMatrix704 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix704 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix704 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix704 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value704, value203, value224, value227, Sparse.eval] at hc ⊢
  linarith

theorem sound716 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node716 = Sparse.eval value716 (momentVector H) := by
  have heq : pivotMatrix716 = (fun u v => node716 (pivotPermutation716 u) v) := by apply Matrix.ext; unfold pivotMatrix716 node716 pivotPermutation716; decide +kernel
  have hmoment : injectiveMoment H node716 = injectiveMoment H pivotMatrix716 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix716 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix716 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix716 (0 : Fin 5)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : mergeFirst pivotMatrix716 (0 : Fin 5) = raw7634 := by apply Matrix.ext; unfold mergeFirst pivotMatrix716 raw7634; decide +kernel
    rw [heq]
    exact (canonical7634 hH).trans (sound232 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix716 (1 : Fin 5)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : mergeFirst pivotMatrix716 (1 : Fin 5) = raw5139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix716 raw5139; decide +kernel
    rw [heq]
    exact (canonical5139 hH).trans (sound232 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix716 (2 : Fin 5)) =
      Sparse.eval value231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix716 (2 : Fin 5) = raw5115 := by apply Matrix.ext; unfold mergeFirst pivotMatrix716 raw5115; decide +kernel
    rw [heq]
    exact (canonical5115 hH).trans (sound231 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix716 (3 : Fin 5)) =
      Sparse.eval value231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix716 (3 : Fin 5) = raw5111 := by apply Matrix.ext; unfold mergeFirst pivotMatrix716 raw5111; decide +kernel
    rw [heq]
    exact (canonical5111 hH).trans (sound231 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix716 (4 : Fin 5)) =
      Sparse.eval value231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix716 (4 : Fin 5) = raw5110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix716 raw5110; decide +kernel
    rw [heq]
    exact (canonical5110 hH).trans (sound231 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node716 + (injectiveMoment H (mergeFirst pivotMatrix716 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix716 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix716 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix716 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix716 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value716, value231, value232, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound33
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2118 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2118 = Sparse.eval value2118 (momentVector H) := by
  have heq : pivotMatrix2118 = (fun u v => node2118 (pivotPermutation2118 u) v) := by apply Matrix.ext; unfold pivotMatrix2118 node2118 pivotPermutation2118; decide +kernel
  have hmoment : injectiveMoment H node2118 = injectiveMoment H pivotMatrix2118 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2118 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2118 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2118 (0 : Fin 5)) =
      Sparse.eval value704 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2118 (0 : Fin 5) = raw4912 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2118 raw4912; decide +kernel
    rw [heq]
    exact (canonical4912 hH).trans (sound704 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2118 (1 : Fin 5)) =
      Sparse.eval value655 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2118 (1 : Fin 5) = raw4067 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2118 raw4067; decide +kernel
    rw [heq]
    exact (canonical4067 hH).trans (sound655 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2118 (2 : Fin 5)) =
      Sparse.eval value642 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2118 (2 : Fin 5) = raw4031 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2118 raw4031; decide +kernel
    rw [heq]
    exact (canonical4031 hH).trans (sound642 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2118 (3 : Fin 5)) =
      Sparse.eval value642 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2118 (3 : Fin 5) = raw4024 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2118 raw4024; decide +kernel
    rw [heq]
    exact (canonical4024 hH).trans (sound642 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2118 (4 : Fin 5)) =
      Sparse.eval value641 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2118 (4 : Fin 5) = raw4023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2118 raw4023; decide +kernel
    rw [heq]
    exact (canonical4023 hH).trans (sound641 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2118 + (injectiveMoment H (mergeFirst pivotMatrix2118 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2118 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2118 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2118 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2118 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2118, value641, value642, value655, value704, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair445 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node445 node445Labels = Sparse.eval singlePairValue445 (familyPairVector B) := by
  have hp := single_label_three B hB node445
  have hl : node445Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node445 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node445 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node445 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node445 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node445 (EqualityPatterns.family3.label 1) = PairSemantics.raw5156 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node445 PairSemantics.raw5156; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5156 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node445 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node445 (EqualityPatterns.family3.label 2) = PairSemantics.raw8989 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node445 PairSemantics.raw8989; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8989 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node445 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value716 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node445 (EqualityPatterns.family3.label 3) = PairSemantics.raw5109 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node445 PairSemantics.raw5109; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5109 hH).trans (PairSemantics.sound716 hH)
  have hm4 : familyPairMoment B (groupedColumns node445 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node445 (EqualityPatterns.family3.label 4) = PairSemantics.raw3886 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node445 PairSemantics.raw3886; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3886 hH).trans (PairSemantics.sound2118 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue445, PairSemantics.value0, PairSemantics.value4, PairSemantics.value232, PairSemantics.value716, PairSemantics.value2118, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3734 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3734 node3734Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node445 node445Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw488 singletonSmall3734
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3734) = raw488Labels := by decide +kernel
  rw [hl, canonical488 B hB] at h
  have hc0 : mixedMoment B raw488 (Fin.cases (0 : Fin 1) singletonSmall3734) =
      mixedMoment B node445 node445Labels := by
    have ha : raw488 = raw489 := by apply Matrix.ext; unfold raw488 raw489; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3734 = raw489Labels := by decide +kernel
    rw [ha, hj, canonical489 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem sound2074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2074 node2074Labels = Sparse.eval nodeValue2074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2074) = mixedMoment B node2074 node2074Labels := rfl
  simpa [nodeValue2074, Sparse.eval] using hc.symm

theorem sound2076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2076 node2076Labels = Sparse.eval nodeValue2076 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2076) = mixedMoment B node2076 node2076Labels := rfl
  simpa [nodeValue2076, Sparse.eval] using hc.symm

theorem sound2104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2104 node2104Labels = Sparse.eval nodeValue2104 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2104) = mixedMoment B node2104 node2104Labels := rfl
  simpa [nodeValue2104, Sparse.eval] using hc.symm

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

theorem sound2213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2213 node2213Labels = Sparse.eval nodeValue2213 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2213) = mixedMoment B node2213 node2213Labels := rfl
  simpa [nodeValue2213, Sparse.eval] using hc.symm

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

theorem sound3488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3488 node3488Labels = Sparse.eval nodeValue3488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3488) = mixedMoment B node3488 node3488Labels := rfl
  simpa [nodeValue3488, Sparse.eval] using hc.symm

theorem sound3491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3491 node3491Labels = Sparse.eval nodeValue3491 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3491) = mixedMoment B node3491 node3491Labels := rfl
  simpa [nodeValue3491, Sparse.eval] using hc.symm

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

theorem sound3524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3524 node3524Labels = Sparse.eval nodeValue3524 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3524) = mixedMoment B node3524 node3524Labels := rfl
  simpa [nodeValue3524, Sparse.eval] using hc.symm

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

theorem sound445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node445 node445Labels = Sparse.eval nodeValue445 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue445 (familyPairVector B) := singlePair445 B _hB
    _ = _ := by
      norm_num [singlePairValue445, nodeValue445, Sparse.eval, mixedVector]
      ring

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

theorem sound3720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3720 node3720Labels = Sparse.eval nodeValue3720 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3720) = mixedMoment B node3720 node3720Labels := rfl
  simpa [nodeValue3720, Sparse.eval] using hc.symm

theorem sound3734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3734 node3734Labels = Sparse.eval nodeValue3734 (mixedVector B) := by
  have h := singleton3734 B _hB
  rw [sound445 B _hB _hF] at h
  norm_num [nodeValue3734, nodeValue445, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3750 node3750Labels = Sparse.eval nodeValue3750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3750) = mixedMoment B node3750 node3750Labels := rfl
  simpa [nodeValue3750, Sparse.eval] using hc.symm

theorem sound3768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3768 node3768Labels = Sparse.eval nodeValue3768 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3768) = mixedMoment B node3768 node3768Labels := rfl
  simpa [nodeValue3768, Sparse.eval] using hc.symm

theorem sound3769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3769 node3769Labels = Sparse.eval nodeValue3769 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3769) = mixedMoment B node3769 node3769Labels := rfl
  simpa [nodeValue3769, Sparse.eval] using hc.symm

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

theorem sound3812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3812 node3812Labels = Sparse.eval nodeValue3812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3812) = mixedMoment B node3812 node3812Labels := rfl
  simpa [nodeValue3812, Sparse.eval] using hc.symm

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

theorem sound3869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3869 node3869Labels = Sparse.eval nodeValue3869 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3869) = mixedMoment B node3869 node3869Labels := rfl
  simpa [nodeValue3869, Sparse.eval] using hc.symm

theorem sound3871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3871 node3871Labels = Sparse.eval nodeValue3871 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3871) = mixedMoment B node3871 node3871Labels := rfl
  simpa [nodeValue3871, Sparse.eval] using hc.symm

theorem sound3874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3874 node3874Labels = Sparse.eval nodeValue3874 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3874) = mixedMoment B node3874 node3874Labels := rfl
  simpa [nodeValue3874, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3956 node3956Labels = 0 := by
  exact mixedMoment_alpha B hF node3956 node3956Labels 1 permutation203
    (by decide +kernel)

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

theorem sound3956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3956 node3956Labels = Sparse.eval nodeValue3956 (mixedVector B) := by
  simpa only [nodeValue3956, Sparse.eval_nil] using zero3956 B _hB _hF

theorem sound3957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3957 node3957Labels = Sparse.eval nodeValue3957 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3957) = mixedMoment B node3957 node3957Labels := rfl
  simpa [nodeValue3957, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources29
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq943 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm943 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA943 + difference 0 1) (sourceB943 + difference 1 0) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA943 + difference 0 1) (sourceB943 + difference 1 0) sourceC943) = raw15603 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15603; decide +kernel
    rw [ha]
    exact (canonical15603 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA943 + difference 0 2) (sourceB943 + difference 2 0) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA943 + difference 0 2) (sourceB943 + difference 2 0) sourceC943) = raw15604 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15604; decide +kernel
    rw [ha]
    exact (canonical15604 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA943 + difference 0 3) (sourceB943 + difference 3 0) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA943 + difference 0 3) (sourceB943 + difference 3 0) sourceC943) = raw15605 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15605; decide +kernel
    rw [ha]
    exact (canonical15605 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA943 + difference 0 4) (sourceB943 + difference 4 0) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4026) := by
    have ha : (tripleCharges (sourceA943 + difference 0 4) (sourceB943 + difference 4 0) sourceC943) = raw15606 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15606; decide +kernel
    rw [ha]
    exact (canonical15606 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA943 + difference 0 5) (sourceB943 + difference 5 0) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA943 + difference 0 5) (sourceB943 + difference 5 0) sourceC943) = raw15607 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15607; decide +kernel
    rw [ha]
    exact (canonical15607 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA943 + difference 1 0) (sourceB943 + difference 0 1) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2104) := by
    have ha : (tripleCharges (sourceA943 + difference 1 0) (sourceB943 + difference 0 1) sourceC943) = raw15608 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15608; decide +kernel
    rw [ha]
    exact (canonical15608 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA943 + difference 1 2) (sourceB943 + difference 2 1) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA943 + difference 1 2) (sourceB943 + difference 2 1) sourceC943) = raw15609 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15609; decide +kernel
    rw [ha]
    exact (canonical15609 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA943 + difference 1 3) (sourceB943 + difference 3 1) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA943 + difference 1 3) (sourceB943 + difference 3 1) sourceC943) = raw15610 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15610; decide +kernel
    rw [ha]
    exact (canonical15610 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA943 + difference 1 4) (sourceB943 + difference 4 1) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3734) := by
    have ha : (tripleCharges (sourceA943 + difference 1 4) (sourceB943 + difference 4 1) sourceC943) = raw15611 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15611; decide +kernel
    rw [ha]
    exact (canonical15611 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA943 + difference 1 5) (sourceB943 + difference 5 1) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3882) := by
    have ha : (tripleCharges (sourceA943 + difference 1 5) (sourceB943 + difference 5 1) sourceC943) = raw15612 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15612; decide +kernel
    rw [ha]
    exact (canonical15612 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA943 + difference 2 0) (sourceB943 + difference 0 2) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2076) := by
    have ha : (tripleCharges (sourceA943 + difference 2 0) (sourceB943 + difference 0 2) sourceC943) = raw15613 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15613; decide +kernel
    rw [ha]
    exact (canonical15613 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA943 + difference 2 1) (sourceB943 + difference 1 2) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3750) := by
    have ha : (tripleCharges (sourceA943 + difference 2 1) (sourceB943 + difference 1 2) sourceC943) = raw15614 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15614; decide +kernel
    rw [ha]
    exact (canonical15614 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA943 + difference 2 3) (sourceB943 + difference 3 2) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA943 + difference 2 3) (sourceB943 + difference 3 2) sourceC943) = raw15615 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15615; decide +kernel
    rw [ha]
    exact (canonical15615 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA943 + difference 2 4) (sourceB943 + difference 4 2) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3720) := by
    have ha : (tripleCharges (sourceA943 + difference 2 4) (sourceB943 + difference 4 2) sourceC943) = raw15616 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15616; decide +kernel
    rw [ha]
    exact (canonical15616 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA943 + difference 2 5) (sourceB943 + difference 5 2) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA943 + difference 2 5) (sourceB943 + difference 5 2) sourceC943) = raw15617 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15617; decide +kernel
    rw [ha]
    exact (canonical15617 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA943 + difference 3 0) (sourceB943 + difference 0 3) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2076) := by
    have ha : (tripleCharges (sourceA943 + difference 3 0) (sourceB943 + difference 0 3) sourceC943) = raw15618 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15618; decide +kernel
    rw [ha]
    exact (canonical15618 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA943 + difference 3 1) (sourceB943 + difference 1 3) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3750) := by
    have ha : (tripleCharges (sourceA943 + difference 3 1) (sourceB943 + difference 1 3) sourceC943) = raw15619 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15619; decide +kernel
    rw [ha]
    exact (canonical15619 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA943 + difference 3 2) (sourceB943 + difference 2 3) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA943 + difference 3 2) (sourceB943 + difference 2 3) sourceC943) = raw15620 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15620; decide +kernel
    rw [ha]
    exact (canonical15620 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA943 + difference 3 4) (sourceB943 + difference 4 3) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3720) := by
    have ha : (tripleCharges (sourceA943 + difference 3 4) (sourceB943 + difference 4 3) sourceC943) = raw15621 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15621; decide +kernel
    rw [ha]
    exact (canonical15621 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA943 + difference 3 5) (sourceB943 + difference 5 3) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA943 + difference 3 5) (sourceB943 + difference 5 3) sourceC943) = raw15622 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15622; decide +kernel
    rw [ha]
    exact (canonical15622 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA943 + difference 4 0) (sourceB943 + difference 0 4) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA943 + difference 4 0) (sourceB943 + difference 0 4) sourceC943) = raw15623 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15623; decide +kernel
    rw [ha]
    exact (canonical15623 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA943 + difference 4 1) (sourceB943 + difference 1 4) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3768) := by
    have ha : (tripleCharges (sourceA943 + difference 4 1) (sourceB943 + difference 1 4) sourceC943) = raw15624 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15624; decide +kernel
    rw [ha]
    exact (canonical15624 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA943 + difference 4 2) (sourceB943 + difference 2 4) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3769) := by
    have ha : (tripleCharges (sourceA943 + difference 4 2) (sourceB943 + difference 2 4) sourceC943) = raw15625 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15625; decide +kernel
    rw [ha]
    exact (canonical15625 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA943 + difference 4 3) (sourceB943 + difference 3 4) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3769) := by
    have ha : (tripleCharges (sourceA943 + difference 4 3) (sourceB943 + difference 3 4) sourceC943) = raw15626 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15626; decide +kernel
    rw [ha]
    exact (canonical15626 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA943 + difference 4 5) (sourceB943 + difference 5 4) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA943 + difference 4 5) (sourceB943 + difference 5 4) sourceC943) = raw15627 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15627; decide +kernel
    rw [ha]
    exact (canonical15627 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA943 + difference 5 0) (sourceB943 + difference 0 5) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2074) := by
    have ha : (tripleCharges (sourceA943 + difference 5 0) (sourceB943 + difference 0 5) sourceC943) = raw15628 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15628; decide +kernel
    rw [ha]
    exact (canonical15628 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA943 + difference 5 1) (sourceB943 + difference 1 5) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3491) := by
    have ha : (tripleCharges (sourceA943 + difference 5 1) (sourceB943 + difference 1 5) sourceC943) = raw15629 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15629; decide +kernel
    rw [ha]
    exact (canonical15629 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA943 + difference 5 2) (sourceB943 + difference 2 5) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA943 + difference 5 2) (sourceB943 + difference 2 5) sourceC943) = raw15630 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15630; decide +kernel
    rw [ha]
    exact (canonical15630 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA943 + difference 5 3) (sourceB943 + difference 3 5) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA943 + difference 5 3) (sourceB943 + difference 3 5) sourceC943) = raw15631 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15631; decide +kernel
    rw [ha]
    exact (canonical15631 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA943 + difference 5 4) (sourceB943 + difference 4 5) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3488) := by
    have ha : (tripleCharges (sourceA943 + difference 5 4) (sourceB943 + difference 4 5) sourceC943) = raw15632 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15632; decide +kernel
    rw [ha]
    exact (canonical15632 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA943 sourceB943 sourceC943
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm943, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck823 : Integer.Sparse.reindex keyMap MixedData.row823 = numericRow823 := by decide +kernel

theorem numericCheck823 (x : Master → ℝ) : Integer.Sparse.eval numericRow823 x =
    (4320 : ℝ) * reducedSource823 x := by
  norm_num [numericRow823, reducedSource823, Integer.Sparse.eval, Sparse.eval, nodeValue2074, nodeValue2076, nodeValue2104, nodeValue2213, nodeValue3488, nodeValue3491, nodeValue3524, nodeValue3720, nodeValue3734, nodeValue3750, nodeValue3768, nodeValue3769, nodeValue3812, nodeValue3869, nodeValue3871, nodeValue3874, nodeValue3882, nodeValue3956, nodeValue3957, nodeValue3980, nodeValue4026]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero823 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource823 (mixedVector B) = 0 := by
  have h2074 : mixedVector B (Sum.inr 2074) = Sparse.eval nodeValue2074 (mixedVector B) := by
    change mixedMoment B node2074 node2074Labels = _
    exact sound2074 B hB hF
  have h2076 : mixedVector B (Sum.inr 2076) = Sparse.eval nodeValue2076 (mixedVector B) := by
    change mixedMoment B node2076 node2076Labels = _
    exact sound2076 B hB hF
  have h2104 : mixedVector B (Sum.inr 2104) = Sparse.eval nodeValue2104 (mixedVector B) := by
    change mixedMoment B node2104 node2104Labels = _
    exact sound2104 B hB hF
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h3488 : mixedVector B (Sum.inr 3488) = Sparse.eval nodeValue3488 (mixedVector B) := by
    change mixedMoment B node3488 node3488Labels = _
    exact sound3488 B hB hF
  have h3491 : mixedVector B (Sum.inr 3491) = Sparse.eval nodeValue3491 (mixedVector B) := by
    change mixedMoment B node3491 node3491Labels = _
    exact sound3491 B hB hF
  have h3524 : mixedVector B (Sum.inr 3524) = Sparse.eval nodeValue3524 (mixedVector B) := by
    change mixedMoment B node3524 node3524Labels = _
    exact sound3524 B hB hF
  have h3720 : mixedVector B (Sum.inr 3720) = Sparse.eval nodeValue3720 (mixedVector B) := by
    change mixedMoment B node3720 node3720Labels = _
    exact sound3720 B hB hF
  have h3734 : mixedVector B (Sum.inr 3734) = Sparse.eval nodeValue3734 (mixedVector B) := by
    change mixedMoment B node3734 node3734Labels = _
    exact sound3734 B hB hF
  have h3750 : mixedVector B (Sum.inr 3750) = Sparse.eval nodeValue3750 (mixedVector B) := by
    change mixedMoment B node3750 node3750Labels = _
    exact sound3750 B hB hF
  have h3768 : mixedVector B (Sum.inr 3768) = Sparse.eval nodeValue3768 (mixedVector B) := by
    change mixedMoment B node3768 node3768Labels = _
    exact sound3768 B hB hF
  have h3769 : mixedVector B (Sum.inr 3769) = Sparse.eval nodeValue3769 (mixedVector B) := by
    change mixedMoment B node3769 node3769Labels = _
    exact sound3769 B hB hF
  have h3812 : mixedVector B (Sum.inr 3812) = Sparse.eval nodeValue3812 (mixedVector B) := by
    change mixedMoment B node3812 node3812Labels = _
    exact sound3812 B hB hF
  have h3869 : mixedVector B (Sum.inr 3869) = Sparse.eval nodeValue3869 (mixedVector B) := by
    change mixedMoment B node3869 node3869Labels = _
    exact sound3869 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h3882 : mixedVector B (Sum.inr 3882) = Sparse.eval nodeValue3882 (mixedVector B) := by
    change mixedMoment B node3882 node3882Labels = _
    exact sound3882_e B hB hF
  have h3956 : mixedVector B (Sum.inr 3956) = Sparse.eval nodeValue3956 (mixedVector B) := by
    change mixedMoment B node3956 node3956Labels = _
    exact sound3956 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  have h3980 : mixedVector B (Sum.inr 3980) = Sparse.eval nodeValue3980 (mixedVector B) := by
    change mixedMoment B node3980 node3980Labels = _
    exact sound3980_e B hB hF
  have h4026 : mixedVector B (Sum.inr 4026) = Sparse.eval nodeValue4026 (mixedVector B) := by
    change mixedMoment B node4026 node4026Labels = _
    exact sound4026_e B hB hF
  simpa only [sourceForm943, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2074, h2076, h2104, h2213, h3488, h3491, h3524, h3720, h3734, h3750, h3768, h3769, h3812, h3869, h3871, h3874, h3882, h3956, h3957, h3980, h4026, reducedSource823] using sourceEq943 B hB

theorem rowSound823_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row823 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck823, numericCheck823, reducedZero823 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e_oai
