-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound42_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:15:47.377209+00:00
-- url     : https://prove2.me/submissions/456d1ef7-611d-42f0-8f09-81857e340ae7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3100_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3223_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5292_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound675_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound682_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound683_e

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

theorem canonical12855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12855 raw12855Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw12855 raw12855Labels = mixedMoment B raw12855step0 raw12855step0Labels := by
      have hz : ∀ j, raw12855 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12855step0 = (fun i j => raw12855 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12855step0 raw12855; decide +kernel
      have hl : raw12855step0Labels = raw12855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12855 raw12855Labels permutation265 hz
    mixedMoment B raw12855step0 raw12855step0Labels = mixedMoment B raw12855step1 raw12855step1Labels := by
      have ha : raw12855step1 = (fun i j => raw12855step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12855step1 raw12855step0; decide +kernel
      have hl : raw12855step1Labels = raw12855step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12855step0 raw12855step0Labels permutation37 permutation2
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical12856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12856 raw12856Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw12856 raw12856Labels = mixedMoment B raw12856step0 raw12856step0Labels := by
      have ha : raw12856step0 = (fun i j => raw12856 (permutation428 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12856step0 raw12856; decide +kernel
      have hl : raw12856step0Labels = raw12856Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12856 raw12856Labels permutation428 permutation4
    _ = mixedMoment B node3848 node3848Labels := by rfl

theorem canonical12857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12857 raw12857Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw12857 raw12857Labels = mixedMoment B raw12857step0 raw12857step0Labels := by
      have hz : ∀ j, raw12857 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12857step0 = (fun i j => raw12857 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12857step0 raw12857; decide +kernel
      have hl : raw12857step0Labels = raw12857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12857 raw12857Labels permutation265 hz
    mixedMoment B raw12857step0 raw12857step0Labels = mixedMoment B raw12857step1 raw12857step1Labels := by
      have ha : raw12857step1 = (fun i j => raw12857step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12857step1 raw12857step0; decide +kernel
      have hl : raw12857step1Labels = raw12857step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12857step0 raw12857step0Labels permutation37 permutation2
    _ = mixedMoment B node3961 node3961Labels := by rfl

theorem canonical12858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12858 raw12858Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw12858 raw12858Labels = mixedMoment B raw12858step0 raw12858step0Labels := by
      have hz : ∀ j, raw12858 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12858step0 = (fun i j => raw12858 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12858step0 raw12858; decide +kernel
      have hl : raw12858step0Labels = raw12858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12858 raw12858Labels permutation265 hz
    mixedMoment B raw12858step0 raw12858step0Labels = mixedMoment B raw12858step1 raw12858step1Labels := by
      have ha : raw12858step1 = (fun i j => raw12858step0 (permutation78 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12858step1 raw12858step0; decide +kernel
      have hl : raw12858step1Labels = raw12858step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12858step0 raw12858step0Labels permutation78 permutation4
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical12861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12861 raw12861Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw12861 raw12861Labels = mixedMoment B raw12861step0 raw12861step0Labels := by
      have hz : ∀ j, raw12861 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12861step0 = (fun i j => raw12861 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12861step0 raw12861; decide +kernel
      have hl : raw12861step0Labels = raw12861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12861 raw12861Labels permutation590 hz
    mixedMoment B raw12861step0 raw12861step0Labels = mixedMoment B raw12861step1 raw12861step1Labels := by
      have hz : ∀ j, raw12861step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12861step1 = (fun i j => raw12861step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12861step1 raw12861step0; decide +kernel
      have hl : raw12861step1Labels = raw12861step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12861step0 raw12861step0Labels permutation56 hz
    mixedMoment B raw12861step1 raw12861step1Labels = mixedMoment B raw12861step2 raw12861step2Labels := by
      have ha : raw12861step2 = (fun i j => raw12861step1 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw12861step2 raw12861step1; decide +kernel
      have hl : raw12861step2Labels = raw12861step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12861step1 raw12861step1Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical12867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12867 raw12867Labels = mixedMoment B node2878 node2878Labels := by
  calc
    mixedMoment B raw12867 raw12867Labels = mixedMoment B raw12867step0 raw12867step0Labels := by
      have ha : raw12867step0 = (fun i j => raw12867 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12867step0 raw12867; decide +kernel
      have hl : raw12867step0Labels = raw12867Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12867 raw12867Labels permutation181 permutation2
    _ = mixedMoment B node2878 node2878Labels := by rfl

theorem canonical12868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12868 raw12868Labels = mixedMoment B node3043 node3043Labels := by
  calc
    mixedMoment B raw12868 raw12868Labels = mixedMoment B raw12868step0 raw12868step0Labels := by
      have ha : raw12868step0 = (fun i j => raw12868 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12868step0 raw12868; decide +kernel
      have hl : raw12868step0Labels = raw12868Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12868 raw12868Labels permutation183 permutation2
    _ = mixedMoment B node3043 node3043Labels := by rfl

theorem canonical12871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12871 raw12871Labels = mixedMoment B node2571 node2571Labels := by
  calc
    mixedMoment B raw12871 raw12871Labels = mixedMoment B raw12871step0 raw12871step0Labels := by
      have ha : raw12871step0 = (fun i j => raw12871 (permutation431 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12871step0 raw12871; decide +kernel
      have hl : raw12871step0Labels = raw12871Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12871 raw12871Labels permutation431 permutation4
    _ = mixedMoment B node2571 node2571Labels := by rfl

theorem canonical12872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12872 raw12872Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw12872 raw12872Labels = mixedMoment B raw12872step0 raw12872step0Labels := by
      have ha : raw12872step0 = (fun i j => raw12872 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12872step0 raw12872; decide +kernel
      have hl : raw12872step0Labels = raw12872Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12872 raw12872Labels permutation157 permutation2
    _ = mixedMoment B node2974 node2974Labels := by rfl

theorem canonical12873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12873 raw12873Labels = mixedMoment B node2975 node2975Labels := by
  calc
    mixedMoment B raw12873 raw12873Labels = mixedMoment B raw12873step0 raw12873step0Labels := by
      have ha : raw12873step0 = (fun i j => raw12873 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12873step0 raw12873; decide +kernel
      have hl : raw12873step0Labels = raw12873Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12873 raw12873Labels permutation156 permutation2
    _ = mixedMoment B node2975 node2975Labels := by rfl

theorem canonical12874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12874 raw12874Labels = mixedMoment B node2977 node2977Labels := by
  calc
    mixedMoment B raw12874 raw12874Labels = mixedMoment B raw12874step0 raw12874step0Labels := by
      have ha : raw12874step0 = (fun i j => raw12874 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12874step0 raw12874; decide +kernel
      have hl : raw12874step0Labels = raw12874Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12874 raw12874Labels permutation154 permutation2
    _ = mixedMoment B node2977 node2977Labels := by rfl

theorem canonical12875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12875 raw12875Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw12875 raw12875Labels = mixedMoment B raw12875step0 raw12875step0Labels := by
      have hz : ∀ j, raw12875 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12875step0 = (fun i j => raw12875 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12875step0 raw12875; decide +kernel
      have hl : raw12875step0Labels = raw12875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12875 raw12875Labels permutation265 hz
    mixedMoment B raw12875step0 raw12875step0Labels = mixedMoment B raw12875step1 raw12875step1Labels := by
      have ha : raw12875step1 = (fun i j => raw12875step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12875step1 raw12875step0; decide +kernel
      have hl : raw12875step1Labels = raw12875step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12875step0 raw12875step0Labels permutation37 permutation2
    _ = mixedMoment B node2881 node2881Labels := by rfl

theorem canonical12876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12876 raw12876Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw12876 raw12876Labels = mixedMoment B raw12876step0 raw12876step0Labels := by
      have hz : ∀ j, raw12876 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12876step0 = (fun i j => raw12876 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12876step0 raw12876; decide +kernel
      have hl : raw12876step0Labels = raw12876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12876 raw12876Labels permutation265 hz
    mixedMoment B raw12876step0 raw12876step0Labels = mixedMoment B raw12876step1 raw12876step1Labels := by
      have ha : raw12876step1 = (fun i j => raw12876step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12876step1 raw12876step0; decide +kernel
      have hl : raw12876step1Labels = raw12876step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12876step0 raw12876step0Labels permutation36 permutation2
    _ = mixedMoment B node2882 node2882Labels := by rfl

theorem canonical12877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12877 raw12877Labels = mixedMoment B node2885 node2885Labels := by
  calc
    mixedMoment B raw12877 raw12877Labels = mixedMoment B raw12877step0 raw12877step0Labels := by
      have hz : ∀ j, raw12877 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12877step0 = (fun i j => raw12877 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12877step0 raw12877; decide +kernel
      have hl : raw12877step0Labels = raw12877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12877 raw12877Labels permutation265 hz
    mixedMoment B raw12877step0 raw12877step0Labels = mixedMoment B raw12877step1 raw12877step1Labels := by
      have ha : raw12877step1 = (fun i j => raw12877step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12877step1 raw12877step0; decide +kernel
      have hl : raw12877step1Labels = raw12877step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12877step0 raw12877step0Labels permutation34 permutation2
    _ = mixedMoment B node2885 node2885Labels := by rfl

theorem canonical12878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12878 raw12878Labels = mixedMoment B node2575 node2575Labels := by
  calc
    mixedMoment B raw12878 raw12878Labels = mixedMoment B raw12878step0 raw12878step0Labels := by
      have hz : ∀ j, raw12878 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12878step0 = (fun i j => raw12878 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12878step0 raw12878; decide +kernel
      have hl : raw12878step0Labels = raw12878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12878 raw12878Labels permutation265 hz
    mixedMoment B raw12878step0 raw12878step0Labels = mixedMoment B raw12878step1 raw12878step1Labels := by
      have ha : raw12878step1 = (fun i j => raw12878step0 (permutation78 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12878step1 raw12878step0; decide +kernel
      have hl : raw12878step1Labels = raw12878step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12878step0 raw12878step0Labels permutation78 permutation4
    _ = mixedMoment B node2575 node2575Labels := by rfl

theorem canonical12879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12879 raw12879Labels = mixedMoment B node3044 node3044Labels := by
  calc
    mixedMoment B raw12879 raw12879Labels = mixedMoment B raw12879step0 raw12879step0Labels := by
      have hz : ∀ j, raw12879 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12879step0 = (fun i j => raw12879 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12879step0 raw12879; decide +kernel
      have hl : raw12879step0Labels = raw12879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12879 raw12879Labels permutation265 hz
    mixedMoment B raw12879step0 raw12879step0Labels = mixedMoment B raw12879step1 raw12879step1Labels := by
      have ha : raw12879step1 = (fun i j => raw12879step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12879step1 raw12879step0; decide +kernel
      have hl : raw12879step1Labels = raw12879step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12879step0 raw12879step0Labels permutation33 permutation2
    _ = mixedMoment B node3044 node3044Labels := by rfl

theorem canonical12880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12880 raw12880Labels = mixedMoment B node3045 node3045Labels := by
  calc
    mixedMoment B raw12880 raw12880Labels = mixedMoment B raw12880step0 raw12880step0Labels := by
      have hz : ∀ j, raw12880 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12880step0 = (fun i j => raw12880 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12880step0 raw12880; decide +kernel
      have hl : raw12880step0Labels = raw12880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12880 raw12880Labels permutation265 hz
    _ = mixedMoment B node3045 node3045Labels := by rfl

theorem canonical12883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12883 raw12883Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw12883 raw12883Labels = mixedMoment B raw12883step0 raw12883step0Labels := by
      have hz : ∀ j, raw12883 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12883step0 = (fun i j => raw12883 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12883step0 raw12883; decide +kernel
      have hl : raw12883step0Labels = raw12883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12883 raw12883Labels permutation265 hz
    mixedMoment B raw12883step0 raw12883step0Labels = mixedMoment B raw12883step1 raw12883step1Labels := by
      have ha : raw12883step1 = (fun i j => raw12883step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12883step1 raw12883step0; decide +kernel
      have hl : raw12883step1Labels = raw12883step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12883step0 raw12883step0Labels permutation35 permutation7
    mixedMoment B raw12883step1 raw12883step1Labels = mixedMoment B raw12883step2 raw12883step2Labels := by
      have ha : raw12883step2 = raw12883step1 := by apply Matrix.ext; unfold raw12883step2 raw12883step1; decide +kernel
      have hl : raw12883step1Labels = labelEmbedding10 ∘ raw12883step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12883step1 raw12883step1Labels raw12883step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

theorem canonical12887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12887 raw12887Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw12887 raw12887Labels = mixedMoment B raw12887step0 raw12887step0Labels := by
      have ha : raw12887step0 = (fun i j => raw12887 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12887step0 raw12887; decide +kernel
      have hl : raw12887step0Labels = raw12887Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12887 raw12887Labels permutation152 permutation6
    mixedMoment B raw12887step0 raw12887step0Labels = mixedMoment B raw12887step1 raw12887step1Labels := by
      have ha : raw12887step1 = raw12887step0 := by apply Matrix.ext; unfold raw12887step1 raw12887step0; decide +kernel
      have hl : raw12887step0Labels = labelEmbedding9 ∘ raw12887step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12887step0 raw12887step0Labels raw12887step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

theorem canonical12891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12891 raw12891Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw12891 raw12891Labels = mixedMoment B raw12891step0 raw12891step0Labels := by
      have hz : ∀ j, raw12891 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12891step0 = (fun i j => raw12891 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12891step0 raw12891; decide +kernel
      have hl : raw12891step0Labels = raw12891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12891 raw12891Labels permutation265 hz
    mixedMoment B raw12891step0 raw12891step0Labels = mixedMoment B raw12891step1 raw12891step1Labels := by
      have ha : raw12891step1 = (fun i j => raw12891step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12891step1 raw12891step0; decide +kernel
      have hl : raw12891step1Labels = raw12891step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12891step0 raw12891step0Labels permutation59 permutation3
    mixedMoment B raw12891step1 raw12891step1Labels = mixedMoment B raw12891step2 raw12891step2Labels := by
      have ha : raw12891step2 = -raw12891step1 := by apply Matrix.ext; change ∀ i j, raw12891step2 i j = -(raw12891step1 i j); unfold raw12891step2 raw12891step1; decide +kernel
      have hl : raw12891step2Labels = raw12891step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12891step2 raw12891step2Labels = mixedMoment B raw12891step3 raw12891step3Labels := by
      have ha : raw12891step3 = raw12891step2 := by apply Matrix.ext; unfold raw12891step3 raw12891step2; decide +kernel
      have hl : raw12891step2Labels = labelEmbedding6 ∘ raw12891step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12891step2 raw12891step2Labels raw12891step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

theorem canonical12894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12894 raw12894Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw12894 raw12894Labels = mixedMoment B raw12894step0 raw12894step0Labels := by
      have hz : ∀ j, raw12894 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12894step0 = (fun i j => raw12894 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12894step0 raw12894; decide +kernel
      have hl : raw12894step0Labels = raw12894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12894 raw12894Labels permutation265 hz
    mixedMoment B raw12894step0 raw12894step0Labels = mixedMoment B raw12894step1 raw12894step1Labels := by
      have ha : raw12894step1 = (fun i j => raw12894step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12894step1 raw12894step0; decide +kernel
      have hl : raw12894step1Labels = raw12894step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12894step0 raw12894step0Labels permutation33 permutation6
    mixedMoment B raw12894step1 raw12894step1Labels = mixedMoment B raw12894step2 raw12894step2Labels := by
      have ha : raw12894step2 = raw12894step1 := by apply Matrix.ext; unfold raw12894step2 raw12894step1; decide +kernel
      have hl : raw12894step1Labels = labelEmbedding9 ∘ raw12894step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12894step1 raw12894step1Labels raw12894step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical12911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12911 raw12911Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw12911 raw12911Labels = mixedMoment B raw12911step0 raw12911step0Labels := by
      have hz : ∀ j, raw12911 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12911step0 = (fun i j => raw12911 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12911step0 raw12911; decide +kernel
      have hl : raw12911step0Labels = raw12911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12911 raw12911Labels permutation265 hz
    mixedMoment B raw12911step0 raw12911step0Labels = mixedMoment B raw12911step1 raw12911step1Labels := by
      have ha : raw12911step1 = (fun i j => raw12911step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12911step1 raw12911step0; decide +kernel
      have hl : raw12911step1Labels = raw12911step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12911step0 raw12911step0Labels permutation35 permutation7
    mixedMoment B raw12911step1 raw12911step1Labels = mixedMoment B raw12911step2 raw12911step2Labels := by
      have ha : raw12911step2 = raw12911step1 := by apply Matrix.ext; unfold raw12911step2 raw12911step1; decide +kernel
      have hl : raw12911step1Labels = labelEmbedding1 ∘ raw12911step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12911step1 raw12911step1Labels raw12911step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2684 node2684Labels := by rfl

theorem canonical12915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12915 raw12915Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw12915 raw12915Labels = mixedMoment B raw12915step0 raw12915step0Labels := by
      have ha : raw12915step0 = (fun i j => raw12915 (permutation179 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12915step0 raw12915; decide +kernel
      have hl : raw12915step0Labels = raw12915Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12915 raw12915Labels permutation179 permutation7
    mixedMoment B raw12915step0 raw12915step0Labels = mixedMoment B raw12915step1 raw12915step1Labels := by
      have ha : raw12915step1 = raw12915step0 := by apply Matrix.ext; unfold raw12915step1 raw12915step0; decide +kernel
      have hl : raw12915step0Labels = labelEmbedding1 ∘ raw12915step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12915step0 raw12915step0Labels raw12915step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

theorem canonical12919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12919 raw12919Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw12919 raw12919Labels = mixedMoment B raw12919step0 raw12919step0Labels := by
      have hz : ∀ j, raw12919 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12919step0 = (fun i j => raw12919 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12919step0 raw12919; decide +kernel
      have hl : raw12919step0Labels = raw12919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12919 raw12919Labels permutation265 hz
    mixedMoment B raw12919step0 raw12919step0Labels = mixedMoment B raw12919step1 raw12919step1Labels := by
      have ha : raw12919step1 = (fun i j => raw12919step0 (permutation73 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12919step1 raw12919step0; decide +kernel
      have hl : raw12919step1Labels = raw12919step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12919step0 raw12919step0Labels permutation73 permutation5
    mixedMoment B raw12919step1 raw12919step1Labels = mixedMoment B raw12919step2 raw12919step2Labels := by
      have ha : raw12919step2 = raw12919step1 := by apply Matrix.ext; unfold raw12919step2 raw12919step1; decide +kernel
      have hl : raw12919step1Labels = labelEmbedding1 ∘ raw12919step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12919step1 raw12919step1Labels raw12919step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2246 node2246Labels := by rfl

theorem canonical12922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12922 raw12922Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw12922 raw12922Labels = mixedMoment B raw12922step0 raw12922step0Labels := by
      have hz : ∀ j, raw12922 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12922step0 = (fun i j => raw12922 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12922step0 raw12922; decide +kernel
      have hl : raw12922step0Labels = raw12922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12922 raw12922Labels permutation265 hz
    mixedMoment B raw12922step0 raw12922step0Labels = mixedMoment B raw12922step1 raw12922step1Labels := by
      have ha : raw12922step1 = (fun i j => raw12922step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12922step1 raw12922step0; decide +kernel
      have hl : raw12922step1Labels = raw12922step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12922step0 raw12922step0Labels permutation35 permutation7
    mixedMoment B raw12922step1 raw12922step1Labels = mixedMoment B raw12922step2 raw12922step2Labels := by
      have ha : raw12922step2 = raw12922step1 := by apply Matrix.ext; unfold raw12922step2 raw12922step1; decide +kernel
      have hl : raw12922step1Labels = labelEmbedding1 ∘ raw12922step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12922step1 raw12922step1Labels raw12922step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical12923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12923 raw12923Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw12923 raw12923Labels = mixedMoment B raw12923step0 raw12923step0Labels := by
      have hz : ∀ j, raw12923 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12923step0 = (fun i j => raw12923 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12923step0 raw12923; decide +kernel
      have hl : raw12923step0Labels = raw12923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12923 raw12923Labels permutation265 hz
    mixedMoment B raw12923step0 raw12923step0Labels = mixedMoment B raw12923step1 raw12923step1Labels := by
      have ha : raw12923step1 = (fun i j => raw12923step0 (permutation97 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12923step1 raw12923step0; decide +kernel
      have hl : raw12923step1Labels = raw12923step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12923step0 raw12923step0Labels permutation97 permutation2
    _ = mixedMoment B node2930 node2930Labels := by rfl

theorem canonical12924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12924 raw12924Labels = mixedMoment B node3380 node3380Labels := by
  calc
    mixedMoment B raw12924 raw12924Labels = mixedMoment B raw12924step0 raw12924step0Labels := by
      have hz : ∀ j, raw12924 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12924step0 = (fun i j => raw12924 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12924step0 raw12924; decide +kernel
      have hl : raw12924step0Labels = raw12924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12924 raw12924Labels permutation265 hz
    mixedMoment B raw12924step0 raw12924step0Labels = mixedMoment B raw12924step1 raw12924step1Labels := by
      have ha : raw12924step1 = (fun i j => raw12924step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12924step1 raw12924step0; decide +kernel
      have hl : raw12924step1Labels = raw12924step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12924step0 raw12924step0Labels permutation36 permutation2
    mixedMoment B raw12924step1 raw12924step1Labels = mixedMoment B raw12924step2 raw12924step2Labels := by
      have ha : raw12924step2 = -raw12924step1 := by apply Matrix.ext; change ∀ i j, raw12924step2 i j = -(raw12924step1 i j); unfold raw12924step2 raw12924step1; decide +kernel
      have hl : raw12924step2Labels = raw12924step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3380 node3380Labels := by rfl

theorem canonical12925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12925 raw12925Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw12925 raw12925Labels = mixedMoment B raw12925step0 raw12925step0Labels := by
      have hz : ∀ j, raw12925 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12925step0 = (fun i j => raw12925 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12925step0 raw12925; decide +kernel
      have hl : raw12925step0Labels = raw12925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12925 raw12925Labels permutation265 hz
    mixedMoment B raw12925step0 raw12925step0Labels = mixedMoment B raw12925step1 raw12925step1Labels := by
      have ha : raw12925step1 = (fun i j => raw12925step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12925step1 raw12925step0; decide +kernel
      have hl : raw12925step1Labels = raw12925step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12925step0 raw12925step0Labels permutation35 permutation2
    mixedMoment B raw12925step1 raw12925step1Labels = mixedMoment B raw12925step2 raw12925step2Labels := by
      have ha : raw12925step2 = -raw12925step1 := by apply Matrix.ext; change ∀ i j, raw12925step2 i j = -(raw12925step1 i j); unfold raw12925step2 raw12925step1; decide +kernel
      have hl : raw12925step2Labels = raw12925step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3394 node3394Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12928 raw12928Labels = mixedMoment B node3551 node3551Labels := by
  calc
    mixedMoment B raw12928 raw12928Labels = mixedMoment B raw12928step0 raw12928step0Labels := by
      have ha : raw12928step0 = (fun i j => raw12928 (permutation213 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12928step0 raw12928; decide +kernel
      have hl : raw12928step0Labels = raw12928Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12928 raw12928Labels permutation213 permutation4
    mixedMoment B raw12928step0 raw12928step0Labels = mixedMoment B raw12928step1 raw12928step1Labels := by
      have ha : raw12928step1 = -raw12928step0 := by apply Matrix.ext; change ∀ i j, raw12928step1 i j = -(raw12928step0 i j); unfold raw12928step1 raw12928step0; decide +kernel
      have hl : raw12928step1Labels = raw12928step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3551 node3551Labels := by rfl

theorem canonical12929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12929 raw12929Labels = mixedMoment B node3567 node3567Labels := by
  calc
    mixedMoment B raw12929 raw12929Labels = mixedMoment B raw12929step0 raw12929step0Labels := by
      have ha : raw12929step0 = (fun i j => raw12929 (permutation216 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12929step0 raw12929; decide +kernel
      have hl : raw12929step0Labels = raw12929Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12929 raw12929Labels permutation216 permutation4
    mixedMoment B raw12929step0 raw12929step0Labels = mixedMoment B raw12929step1 raw12929step1Labels := by
      have ha : raw12929step1 = -raw12929step0 := by apply Matrix.ext; change ∀ i j, raw12929step1 i j = -(raw12929step0 i j); unfold raw12929step1 raw12929step0; decide +kernel
      have hl : raw12929step1Labels = raw12929step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3567 node3567Labels := by rfl

theorem canonical12930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12930 raw12930Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw12930 raw12930Labels = mixedMoment B raw12930step0 raw12930step0Labels := by
      have hz : ∀ j, raw12930 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12930step0 = (fun i j => raw12930 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12930step0 raw12930; decide +kernel
      have hl : raw12930step0Labels = raw12930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12930 raw12930Labels permutation265 hz
    mixedMoment B raw12930step0 raw12930step0Labels = mixedMoment B raw12930step1 raw12930step1Labels := by
      have ha : raw12930step1 = (fun i j => raw12930step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12930step1 raw12930step0; decide +kernel
      have hl : raw12930step1Labels = raw12930step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12930step0 raw12930step0Labels permutation41 permutation4
    mixedMoment B raw12930step1 raw12930step1Labels = mixedMoment B raw12930step2 raw12930step2Labels := by
      have ha : raw12930step2 = -raw12930step1 := by apply Matrix.ext; change ∀ i j, raw12930step2 i j = -(raw12930step1 i j); unfold raw12930step2 raw12930step1; decide +kernel
      have hl : raw12930step2Labels = raw12930step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2092 node2092Labels := by rfl

theorem canonical12931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12931 raw12931Labels = mixedMoment B node2929 node2929Labels := by
  calc
    mixedMoment B raw12931 raw12931Labels = mixedMoment B raw12931step0 raw12931step0Labels := by
      have hz : ∀ j, raw12931 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12931step0 = (fun i j => raw12931 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12931step0 raw12931; decide +kernel
      have hl : raw12931step0Labels = raw12931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12931 raw12931Labels permutation265 hz
    mixedMoment B raw12931step0 raw12931step0Labels = mixedMoment B raw12931step1 raw12931step1Labels := by
      have ha : raw12931step1 = (fun i j => raw12931step0 (permutation96 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12931step1 raw12931step0; decide +kernel
      have hl : raw12931step1Labels = raw12931step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12931step0 raw12931step0Labels permutation96 permutation2
    _ = mixedMoment B node2929 node2929Labels := by rfl

theorem canonical12932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12932 raw12932Labels = mixedMoment B node3152 node3152Labels := by
  calc
    mixedMoment B raw12932 raw12932Labels = mixedMoment B raw12932step0 raw12932step0Labels := by
      have hz : ∀ j, raw12932 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12932step0 = (fun i j => raw12932 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12932step0 raw12932; decide +kernel
      have hl : raw12932step0Labels = raw12932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12932 raw12932Labels permutation265 hz
    mixedMoment B raw12932step0 raw12932step0Labels = mixedMoment B raw12932step1 raw12932step1Labels := by
      have ha : raw12932step1 = (fun i j => raw12932step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12932step1 raw12932step0; decide +kernel
      have hl : raw12932step1Labels = raw12932step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12932step0 raw12932step0Labels permutation60 permutation2
    mixedMoment B raw12932step1 raw12932step1Labels = mixedMoment B raw12932step2 raw12932step2Labels := by
      have ha : raw12932step2 = -raw12932step1 := by apply Matrix.ext; change ∀ i j, raw12932step2 i j = -(raw12932step1 i j); unfold raw12932step2 raw12932step1; decide +kernel
      have hl : raw12932step2Labels = raw12932step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3152 node3152Labels := by rfl

theorem canonical12933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12933 raw12933Labels = mixedMoment B node3158 node3158Labels := by
  calc
    mixedMoment B raw12933 raw12933Labels = mixedMoment B raw12933step0 raw12933step0Labels := by
      have hz : ∀ j, raw12933 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12933step0 = (fun i j => raw12933 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12933step0 raw12933; decide +kernel
      have hl : raw12933step0Labels = raw12933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12933 raw12933Labels permutation265 hz
    mixedMoment B raw12933step0 raw12933step0Labels = mixedMoment B raw12933step1 raw12933step1Labels := by
      have ha : raw12933step1 = (fun i j => raw12933step0 (permutation59 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12933step1 raw12933step0; decide +kernel
      have hl : raw12933step1Labels = raw12933step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12933step0 raw12933step0Labels permutation59 permutation2
    mixedMoment B raw12933step1 raw12933step1Labels = mixedMoment B raw12933step2 raw12933step2Labels := by
      have ha : raw12933step2 = -raw12933step1 := by apply Matrix.ext; change ∀ i j, raw12933step2 i j = -(raw12933step1 i j); unfold raw12933step2 raw12933step1; decide +kernel
      have hl : raw12933step2Labels = raw12933step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3158 node3158Labels := by rfl

theorem canonical12934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12934 raw12934Labels = mixedMoment B node3079 node3079Labels := by
  calc
    mixedMoment B raw12934 raw12934Labels = mixedMoment B raw12934step0 raw12934step0Labels := by
      have hz : ∀ j, raw12934 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12934step0 = (fun i j => raw12934 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12934step0 raw12934; decide +kernel
      have hl : raw12934step0Labels = raw12934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12934 raw12934Labels permutation265 hz
    mixedMoment B raw12934step0 raw12934step0Labels = mixedMoment B raw12934step1 raw12934step1Labels := by
      have ha : raw12934step1 = (fun i j => raw12934step0 (permutation96 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12934step1 raw12934step0; decide +kernel
      have hl : raw12934step1Labels = raw12934step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12934step0 raw12934step0Labels permutation96 permutation2
    _ = mixedMoment B node3079 node3079Labels := by rfl

theorem canonical12935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12935 raw12935Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw12935 raw12935Labels = mixedMoment B raw12935step0 raw12935step0Labels := by
      have hz : ∀ j, raw12935 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12935step0 = (fun i j => raw12935 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12935step0 raw12935; decide +kernel
      have hl : raw12935step0Labels = raw12935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12935 raw12935Labels permutation265 hz
    mixedMoment B raw12935step0 raw12935step0Labels = mixedMoment B raw12935step1 raw12935step1Labels := by
      have ha : raw12935step1 = (fun i j => raw12935step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12935step1 raw12935step0; decide +kernel
      have hl : raw12935step1Labels = raw12935step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12935step0 raw12935step0Labels permutation41 permutation4
    mixedMoment B raw12935step1 raw12935step1Labels = mixedMoment B raw12935step2 raw12935step2Labels := by
      have ha : raw12935step2 = -raw12935step1 := by apply Matrix.ext; change ∀ i j, raw12935step2 i j = -(raw12935step1 i j); unfold raw12935step2 raw12935step1; decide +kernel
      have hl : raw12935step2Labels = raw12935step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2110 node2110Labels := by rfl

theorem canonical12936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12936 raw12936Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw12936 raw12936Labels = mixedMoment B raw12936step0 raw12936step0Labels := by
      have hz : ∀ j, raw12936 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12936step0 = (fun i j => raw12936 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12936step0 raw12936; decide +kernel
      have hl : raw12936step0Labels = raw12936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12936 raw12936Labels permutation265 hz
    mixedMoment B raw12936step0 raw12936step0Labels = mixedMoment B raw12936step1 raw12936step1Labels := by
      have ha : raw12936step1 = (fun i j => raw12936step0 (permutation43 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12936step1 raw12936step0; decide +kernel
      have hl : raw12936step1Labels = raw12936step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12936step0 raw12936step0Labels permutation43 permutation4
    mixedMoment B raw12936step1 raw12936step1Labels = mixedMoment B raw12936step2 raw12936step2Labels := by
      have ha : raw12936step2 = -raw12936step1 := by apply Matrix.ext; change ∀ i j, raw12936step2 i j = -(raw12936step1 i j); unfold raw12936step2 raw12936step1; decide +kernel
      have hl : raw12936step2Labels = raw12936step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical12937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12937 raw12937Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw12937 raw12937Labels = mixedMoment B raw12937step0 raw12937step0Labels := by
      have hz : ∀ j, raw12937 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12937step0 = (fun i j => raw12937 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12937step0 raw12937; decide +kernel
      have hl : raw12937step0Labels = raw12937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12937 raw12937Labels permutation265 hz
    mixedMoment B raw12937step0 raw12937step0Labels = mixedMoment B raw12937step1 raw12937step1Labels := by
      have ha : raw12937step1 = (fun i j => raw12937step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12937step1 raw12937step0; decide +kernel
      have hl : raw12937step1Labels = raw12937step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12937step0 raw12937step0Labels permutation47 permutation4
    mixedMoment B raw12937step1 raw12937step1Labels = mixedMoment B raw12937step2 raw12937step2Labels := by
      have ha : raw12937step2 = -raw12937step1 := by apply Matrix.ext; change ∀ i j, raw12937step2 i j = -(raw12937step1 i j); unfold raw12937step2 raw12937step1; decide +kernel
      have hl : raw12937step2Labels = raw12937step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3573 node3573Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13058 raw13058Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw13058 raw13058Labels = mixedMoment B raw13058step0 raw13058step0Labels := by
      have hz : ∀ j, raw13058 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13058step0 = (fun i j => raw13058 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13058step0 raw13058; decide +kernel
      have hl : raw13058step0Labels = raw13058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13058 raw13058Labels permutation265 hz
    _ = mixedMoment B node3053 node3053Labels := by rfl

theorem canonical13059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13059 raw13059Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw13059 raw13059Labels = mixedMoment B raw13059step0 raw13059step0Labels := by
      have ha : raw13059step0 = (fun i j => raw13059 (permutation393 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13059step0 raw13059; decide +kernel
      have hl : raw13059step0Labels = raw13059Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13059 raw13059Labels permutation393 permutation4
    _ = mixedMoment B node3909 node3909Labels := by rfl

theorem canonical13060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13060 raw13060Labels = mixedMoment B node3962 node3962Labels := by
  calc
    mixedMoment B raw13060 raw13060Labels = mixedMoment B raw13060step0 raw13060step0Labels := by
      have hz : ∀ j, raw13060 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13060step0 = (fun i j => raw13060 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13060step0 raw13060; decide +kernel
      have hl : raw13060step0Labels = raw13060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13060 raw13060Labels permutation265 hz
    _ = mixedMoment B node3962 node3962Labels := by rfl

theorem canonical13061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13061 raw13061Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw13061 raw13061Labels = mixedMoment B raw13061step0 raw13061step0Labels := by
      have hz : ∀ j, raw13061 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13061step0 = (fun i j => raw13061 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13061step0 raw13061; decide +kernel
      have hl : raw13061step0Labels = raw13061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13061 raw13061Labels permutation265 hz
    mixedMoment B raw13061step0 raw13061step0Labels = mixedMoment B raw13061step1 raw13061step1Labels := by
      have ha : raw13061step1 = (fun i j => raw13061step0 (permutation72 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13061step1 raw13061step0; decide +kernel
      have hl : raw13061step1Labels = raw13061step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13061step0 raw13061step0Labels permutation72 permutation4
    _ = mixedMoment B node3910 node3910Labels := by rfl

theorem canonical13062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13062 raw13062Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw13062 raw13062Labels = mixedMoment B raw13062step0 raw13062step0Labels := by
      have hz : ∀ j, raw13062 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13062step0 = (fun i j => raw13062 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13062step0 raw13062; decide +kernel
      have hl : raw13062step0Labels = raw13062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13062 raw13062Labels permutation265 hz
    mixedMoment B raw13062step0 raw13062step0Labels = mixedMoment B raw13062step1 raw13062step1Labels := by
      have ha : raw13062step1 = (fun i j => raw13062step0 (permutation66 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13062step1 raw13062step0; decide +kernel
      have hl : raw13062step1Labels = raw13062step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13062step0 raw13062step0Labels permutation66 permutation4
    _ = mixedMoment B node3910 node3910Labels := by rfl

theorem canonical13063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13063 raw13063Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw13063 raw13063Labels = mixedMoment B raw13063step0 raw13063step0Labels := by
      have hz : ∀ j, raw13063 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13063step0 = (fun i j => raw13063 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13063step0 raw13063; decide +kernel
      have hl : raw13063step0Labels = raw13063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13063 raw13063Labels permutation265 hz
    mixedMoment B raw13063step0 raw13063step0Labels = mixedMoment B raw13063step1 raw13063step1Labels := by
      have ha : raw13063step1 = (fun i j => raw13063step0 (permutation64 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13063step1 raw13063step0; decide +kernel
      have hl : raw13063step1Labels = raw13063step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13063step0 raw13063step0Labels permutation64 permutation4
    _ = mixedMoment B node3910 node3910Labels := by rfl

theorem canonical13064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13064 raw13064Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw13064 raw13064Labels = mixedMoment B raw13064step0 raw13064step0Labels := by
      have hz : ∀ j, raw13064 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13064step0 = (fun i j => raw13064 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13064step0 raw13064; decide +kernel
      have hl : raw13064step0Labels = raw13064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13064 raw13064Labels permutation265 hz
    mixedMoment B raw13064step0 raw13064step0Labels = mixedMoment B raw13064step1 raw13064step1Labels := by
      have ha : raw13064step1 = (fun i j => raw13064step0 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw13064step1 raw13064step0; decide +kernel
      have hl : raw13064step1Labels = raw13064step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13064step0 raw13064step0Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical13065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13065 raw13065Labels = mixedMoment B node2746 node2746Labels := by
  calc
    mixedMoment B raw13065 raw13065Labels = mixedMoment B raw13065step0 raw13065step0Labels := by
      have ha : raw13065step0 = (fun i j => raw13065 (permutation394 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13065step0 raw13065; decide +kernel
      have hl : raw13065step0Labels = raw13065Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13065 raw13065Labels permutation394 permutation4
    _ = mixedMoment B node2746 node2746Labels := by rfl

theorem canonical13066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13066 raw13066Labels = mixedMoment B node2976 node2976Labels := by
  calc
    mixedMoment B raw13066 raw13066Labels = mixedMoment B raw13066step0 raw13066step0Labels := by
      have ha : raw13066step0 = (fun i j => raw13066 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13066step0 raw13066; decide +kernel
      have hl : raw13066step0Labels = raw13066Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13066 raw13066Labels permutation155 permutation2
    _ = mixedMoment B node2976 node2976Labels := by rfl

theorem canonical13067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13067 raw13067Labels = mixedMoment B node2976 node2976Labels := by
  calc
    mixedMoment B raw13067 raw13067Labels = mixedMoment B raw13067step0 raw13067step0Labels := by
      have ha : raw13067step0 = (fun i j => raw13067 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13067step0 raw13067; decide +kernel
      have hl : raw13067step0Labels = raw13067Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13067 raw13067Labels permutation153 permutation2
    _ = mixedMoment B node2976 node2976Labels := by rfl

theorem canonical13068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13068 raw13068Labels = mixedMoment B node2976 node2976Labels := by
  calc
    _ = mixedMoment B node2976 node2976Labels := by rfl

theorem canonical13069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13069 raw13069Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw13069 raw13069Labels = mixedMoment B raw13069step0 raw13069step0Labels := by
      have hz : ∀ j, raw13069 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13069step0 = (fun i j => raw13069 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13069step0 raw13069; decide +kernel
      have hl : raw13069step0Labels = raw13069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13069 raw13069Labels permutation265 hz
    mixedMoment B raw13069step0 raw13069step0Labels = mixedMoment B raw13069step1 raw13069step1Labels := by
      have ha : raw13069step1 = (fun i j => raw13069step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13069step1 raw13069step0; decide +kernel
      have hl : raw13069step1Labels = raw13069step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13069step0 raw13069step0Labels permutation33 permutation7
    mixedMoment B raw13069step1 raw13069step1Labels = mixedMoment B raw13069step2 raw13069step2Labels := by
      have ha : raw13069step2 = raw13069step1 := by apply Matrix.ext; unfold raw13069step2 raw13069step1; decide +kernel
      have hl : raw13069step1Labels = labelEmbedding10 ∘ raw13069step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13069step1 raw13069step1Labels raw13069step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

theorem canonical13070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13070 raw13070Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw13070 raw13070Labels = mixedMoment B raw13070step0 raw13070step0Labels := by
      have hz : ∀ j, raw13070 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13070step0 = (fun i j => raw13070 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13070step0 raw13070; decide +kernel
      have hl : raw13070step0Labels = raw13070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13070 raw13070Labels permutation265 hz
    mixedMoment B raw13070step0 raw13070step0Labels = mixedMoment B raw13070step1 raw13070step1Labels := by
      have ha : raw13070step1 = (fun i j => raw13070step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13070step1 raw13070step0; decide +kernel
      have hl : raw13070step1Labels = raw13070step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13070step0 raw13070step0Labels permutation32 permutation7
    mixedMoment B raw13070step1 raw13070step1Labels = mixedMoment B raw13070step2 raw13070step2Labels := by
      have ha : raw13070step2 = raw13070step1 := by apply Matrix.ext; unfold raw13070step2 raw13070step1; decide +kernel
      have hl : raw13070step1Labels = labelEmbedding10 ∘ raw13070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13070step1 raw13070step1Labels raw13070step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

theorem canonical13071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13071 raw13071Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw13071 raw13071Labels = mixedMoment B raw13071step0 raw13071step0Labels := by
      have ha : raw13071step0 = (fun i j => raw13071 (permutation216 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13071step0 raw13071; decide +kernel
      have hl : raw13071step0Labels = raw13071Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13071 raw13071Labels permutation216 permutation4
    mixedMoment B raw13071step0 raw13071step0Labels = mixedMoment B raw13071step1 raw13071step1Labels := by
      have ha : raw13071step1 = -raw13071step0 := by apply Matrix.ext; change ∀ i j, raw13071step1 i j = -(raw13071step0 i j); unfold raw13071step1 raw13071step0; decide +kernel
      have hl : raw13071step1Labels = raw13071step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13071step1 raw13071step1Labels = mixedMoment B raw13071step2 raw13071step2Labels := by
      have ha : raw13071step2 = raw13071step1 := by apply Matrix.ext; unfold raw13071step2 raw13071step1; decide +kernel
      have hl : raw13071step1Labels = labelEmbedding7 ∘ raw13071step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13071step1 raw13071step1Labels raw13071step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

theorem canonical13072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13072 raw13072Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw13072 raw13072Labels = mixedMoment B raw13072step0 raw13072step0Labels := by
      have ha : raw13072step0 = (fun i j => raw13072 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13072step0 raw13072; decide +kernel
      have hl : raw13072step0Labels = raw13072Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13072 raw13072Labels permutation154 permutation6
    mixedMoment B raw13072step0 raw13072step0Labels = mixedMoment B raw13072step1 raw13072step1Labels := by
      have ha : raw13072step1 = raw13072step0 := by apply Matrix.ext; unfold raw13072step1 raw13072step0; decide +kernel
      have hl : raw13072step0Labels = labelEmbedding9 ∘ raw13072step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13072step0 raw13072step0Labels raw13072step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

theorem canonical13073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13073 raw13073Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw13073 raw13073Labels = mixedMoment B raw13073step0 raw13073step0Labels := by
      have ha : raw13073step0 = (fun i j => raw13073 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13073step0 raw13073; decide +kernel
      have hl : raw13073step0Labels = raw13073Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13073 raw13073Labels permutation156 permutation6
    mixedMoment B raw13073step0 raw13073step0Labels = mixedMoment B raw13073step1 raw13073step1Labels := by
      have ha : raw13073step1 = raw13073step0 := by apply Matrix.ext; unfold raw13073step1 raw13073step0; decide +kernel
      have hl : raw13073step0Labels = labelEmbedding9 ∘ raw13073step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13073step0 raw13073step0Labels raw13073step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

theorem canonical13074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13074 raw13074Labels = mixedMoment B node4886 node4886Labels := by
  calc
    mixedMoment B raw13074 raw13074Labels = mixedMoment B raw13074step0 raw13074step0Labels := by
      have hz : ∀ j, raw13074 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13074step0 = (fun i j => raw13074 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13074step0 raw13074; decide +kernel
      have hl : raw13074step0Labels = raw13074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13074 raw13074Labels permutation265 hz
    mixedMoment B raw13074step0 raw13074step0Labels = mixedMoment B raw13074step1 raw13074step1Labels := by
      have ha : raw13074step1 = (fun i j => raw13074step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13074step1 raw13074step0; decide +kernel
      have hl : raw13074step1Labels = raw13074step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13074step0 raw13074step0Labels permutation41 permutation4
    mixedMoment B raw13074step1 raw13074step1Labels = mixedMoment B raw13074step2 raw13074step2Labels := by
      have ha : raw13074step2 = -raw13074step1 := by apply Matrix.ext; change ∀ i j, raw13074step2 i j = -(raw13074step1 i j); unfold raw13074step2 raw13074step1; decide +kernel
      have hl : raw13074step2Labels = raw13074step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13074step2 raw13074step2Labels = mixedMoment B raw13074step3 raw13074step3Labels := by
      have ha : raw13074step3 = raw13074step2 := by apply Matrix.ext; unfold raw13074step3 raw13074step2; decide +kernel
      have hl : raw13074step2Labels = labelEmbedding7 ∘ raw13074step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13074step2 raw13074step2Labels raw13074step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4886 node4886Labels := by rfl

theorem canonical13075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13075 raw13075Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw13075 raw13075Labels = mixedMoment B raw13075step0 raw13075step0Labels := by
      have hz : ∀ j, raw13075 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13075step0 = (fun i j => raw13075 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13075step0 raw13075; decide +kernel
      have hl : raw13075step0Labels = raw13075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13075 raw13075Labels permutation265 hz
    mixedMoment B raw13075step0 raw13075step0Labels = mixedMoment B raw13075step1 raw13075step1Labels := by
      have ha : raw13075step1 = (fun i j => raw13075step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13075step1 raw13075step0; decide +kernel
      have hl : raw13075step1Labels = raw13075step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13075step0 raw13075step0Labels permutation57 permutation3
    mixedMoment B raw13075step1 raw13075step1Labels = mixedMoment B raw13075step2 raw13075step2Labels := by
      have ha : raw13075step2 = -raw13075step1 := by apply Matrix.ext; change ∀ i j, raw13075step2 i j = -(raw13075step1 i j); unfold raw13075step2 raw13075step1; decide +kernel
      have hl : raw13075step2Labels = raw13075step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13075step2 raw13075step2Labels = mixedMoment B raw13075step3 raw13075step3Labels := by
      have ha : raw13075step3 = raw13075step2 := by apply Matrix.ext; unfold raw13075step3 raw13075step2; decide +kernel
      have hl : raw13075step2Labels = labelEmbedding6 ∘ raw13075step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13075step2 raw13075step2Labels raw13075step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

theorem canonical13076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13076 raw13076Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw13076 raw13076Labels = mixedMoment B raw13076step0 raw13076step0Labels := by
      have hz : ∀ j, raw13076 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13076step0 = (fun i j => raw13076 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13076step0 raw13076; decide +kernel
      have hl : raw13076step0Labels = raw13076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13076 raw13076Labels permutation265 hz
    mixedMoment B raw13076step0 raw13076step0Labels = mixedMoment B raw13076step1 raw13076step1Labels := by
      have ha : raw13076step1 = (fun i j => raw13076step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13076step1 raw13076step0; decide +kernel
      have hl : raw13076step1Labels = raw13076step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13076step0 raw13076step0Labels permutation56 permutation3
    mixedMoment B raw13076step1 raw13076step1Labels = mixedMoment B raw13076step2 raw13076step2Labels := by
      have ha : raw13076step2 = -raw13076step1 := by apply Matrix.ext; change ∀ i j, raw13076step2 i j = -(raw13076step1 i j); unfold raw13076step2 raw13076step1; decide +kernel
      have hl : raw13076step2Labels = raw13076step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13076step2 raw13076step2Labels = mixedMoment B raw13076step3 raw13076step3Labels := by
      have ha : raw13076step3 = raw13076step2 := by apply Matrix.ext; unfold raw13076step3 raw13076step2; decide +kernel
      have hl : raw13076step2Labels = labelEmbedding6 ∘ raw13076step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13076step2 raw13076step2Labels raw13076step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

theorem canonical13077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13077 raw13077Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw13077 raw13077Labels = mixedMoment B raw13077step0 raw13077step0Labels := by
      have hz : ∀ j, raw13077 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13077step0 = (fun i j => raw13077 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13077step0 raw13077; decide +kernel
      have hl : raw13077step0Labels = raw13077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13077 raw13077Labels permutation265 hz
    mixedMoment B raw13077step0 raw13077step0Labels = mixedMoment B raw13077step1 raw13077step1Labels := by
      have ha : raw13077step1 = (fun i j => raw13077step0 (permutation49 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13077step1 raw13077step0; decide +kernel
      have hl : raw13077step1Labels = raw13077step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13077step0 raw13077step0Labels permutation49 permutation4
    mixedMoment B raw13077step1 raw13077step1Labels = mixedMoment B raw13077step2 raw13077step2Labels := by
      have ha : raw13077step2 = -raw13077step1 := by apply Matrix.ext; change ∀ i j, raw13077step2 i j = -(raw13077step1 i j); unfold raw13077step2 raw13077step1; decide +kernel
      have hl : raw13077step2Labels = raw13077step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13077step2 raw13077step2Labels = mixedMoment B raw13077step3 raw13077step3Labels := by
      have ha : raw13077step3 = raw13077step2 := by apply Matrix.ext; unfold raw13077step3 raw13077step2; decide +kernel
      have hl : raw13077step2Labels = labelEmbedding7 ∘ raw13077step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13077step2 raw13077step2Labels raw13077step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical13078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13078 raw13078Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw13078 raw13078Labels = mixedMoment B raw13078step0 raw13078step0Labels := by
      have hz : ∀ j, raw13078 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13078step0 = (fun i j => raw13078 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13078step0 raw13078; decide +kernel
      have hl : raw13078step0Labels = raw13078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13078 raw13078Labels permutation265 hz
    mixedMoment B raw13078step0 raw13078step0Labels = mixedMoment B raw13078step1 raw13078step1Labels := by
      have ha : raw13078step1 = (fun i j => raw13078step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13078step1 raw13078step0; decide +kernel
      have hl : raw13078step1Labels = raw13078step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13078step0 raw13078step0Labels permutation35 permutation6
    mixedMoment B raw13078step1 raw13078step1Labels = mixedMoment B raw13078step2 raw13078step2Labels := by
      have ha : raw13078step2 = raw13078step1 := by apply Matrix.ext; unfold raw13078step2 raw13078step1; decide +kernel
      have hl : raw13078step1Labels = labelEmbedding9 ∘ raw13078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13078step1 raw13078step1Labels raw13078step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical13079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13079 raw13079Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw13079 raw13079Labels = mixedMoment B raw13079step0 raw13079step0Labels := by
      have hz : ∀ j, raw13079 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13079step0 = (fun i j => raw13079 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13079step0 raw13079; decide +kernel
      have hl : raw13079step0Labels = raw13079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13079 raw13079Labels permutation265 hz
    mixedMoment B raw13079step0 raw13079step0Labels = mixedMoment B raw13079step1 raw13079step1Labels := by
      have ha : raw13079step1 = (fun i j => raw13079step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13079step1 raw13079step0; decide +kernel
      have hl : raw13079step1Labels = raw13079step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13079step0 raw13079step0Labels permutation37 permutation6
    mixedMoment B raw13079step1 raw13079step1Labels = mixedMoment B raw13079step2 raw13079step2Labels := by
      have ha : raw13079step2 = raw13079step1 := by apply Matrix.ext; unfold raw13079step2 raw13079step1; decide +kernel
      have hl : raw13079step1Labels = labelEmbedding9 ∘ raw13079step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13079step1 raw13079step1Labels raw13079step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical13080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13080 raw13080Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw13080 raw13080Labels = mixedMoment B raw13080step0 raw13080step0Labels := by
      have hz : ∀ j, raw13080 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13080step0 = (fun i j => raw13080 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13080step0 raw13080; decide +kernel
      have hl : raw13080step0Labels = raw13080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13080 raw13080Labels permutation265 hz
    mixedMoment B raw13080step0 raw13080step0Labels = mixedMoment B raw13080step1 raw13080step1Labels := by
      have ha : raw13080step1 = (fun i j => raw13080step0 (permutation43 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13080step1 raw13080step0; decide +kernel
      have hl : raw13080step1Labels = raw13080step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13080step0 raw13080step0Labels permutation43 permutation4
    mixedMoment B raw13080step1 raw13080step1Labels = mixedMoment B raw13080step2 raw13080step2Labels := by
      have ha : raw13080step2 = -raw13080step1 := by apply Matrix.ext; change ∀ i j, raw13080step2 i j = -(raw13080step1 i j); unfold raw13080step2 raw13080step1; decide +kernel
      have hl : raw13080step2Labels = raw13080step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13080step2 raw13080step2Labels = mixedMoment B raw13080step3 raw13080step3Labels := by
      have ha : raw13080step3 = raw13080step2 := by apply Matrix.ext; unfold raw13080step3 raw13080step2; decide +kernel
      have hl : raw13080step2Labels = labelEmbedding7 ∘ raw13080step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13080step2 raw13080step2Labels raw13080step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical13081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13081 raw13081Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw13081 raw13081Labels = mixedMoment B raw13081step0 raw13081step0Labels := by
      have hz : ∀ j, raw13081 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13081step0 = (fun i j => raw13081 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13081step0 raw13081; decide +kernel
      have hl : raw13081step0Labels = raw13081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13081 raw13081Labels permutation265 hz
    mixedMoment B raw13081step0 raw13081step0Labels = mixedMoment B raw13081step1 raw13081step1Labels := by
      have ha : raw13081step1 = (fun i j => raw13081step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13081step1 raw13081step0; decide +kernel
      have hl : raw13081step1Labels = raw13081step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13081step0 raw13081step0Labels permutation36 permutation6
    mixedMoment B raw13081step1 raw13081step1Labels = mixedMoment B raw13081step2 raw13081step2Labels := by
      have ha : raw13081step2 = raw13081step1 := by apply Matrix.ext; unfold raw13081step2 raw13081step1; decide +kernel
      have hl : raw13081step1Labels = labelEmbedding9 ∘ raw13081step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13081step1 raw13081step1Labels raw13081step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical13082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13082 raw13082Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw13082 raw13082Labels = mixedMoment B raw13082step0 raw13082step0Labels := by
      have hz : ∀ j, raw13082 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13082step0 = (fun i j => raw13082 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13082step0 raw13082; decide +kernel
      have hl : raw13082step0Labels = raw13082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13082 raw13082Labels permutation265 hz
    mixedMoment B raw13082step0 raw13082step0Labels = mixedMoment B raw13082step1 raw13082step1Labels := by
      have ha : raw13082step1 = (fun i j => raw13082step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13082step1 raw13082step0; decide +kernel
      have hl : raw13082step1Labels = raw13082step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13082step0 raw13082step0Labels permutation32 permutation7
    mixedMoment B raw13082step1 raw13082step1Labels = mixedMoment B raw13082step2 raw13082step2Labels := by
      have ha : raw13082step2 = raw13082step1 := by apply Matrix.ext; unfold raw13082step2 raw13082step1; decide +kernel
      have hl : raw13082step1Labels = labelEmbedding1 ∘ raw13082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13082step1 raw13082step1Labels raw13082step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2741 node2741Labels := by rfl

theorem canonical13083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13083 raw13083Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw13083 raw13083Labels = mixedMoment B raw13083step0 raw13083step0Labels := by
      have hz : ∀ j, raw13083 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13083step0 = (fun i j => raw13083 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13083step0 raw13083; decide +kernel
      have hl : raw13083step0Labels = raw13083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13083 raw13083Labels permutation265 hz
    mixedMoment B raw13083step0 raw13083step0Labels = mixedMoment B raw13083step1 raw13083step1Labels := by
      have ha : raw13083step1 = (fun i j => raw13083step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13083step1 raw13083step0; decide +kernel
      have hl : raw13083step1Labels = raw13083step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13083step0 raw13083step0Labels permutation33 permutation7
    mixedMoment B raw13083step1 raw13083step1Labels = mixedMoment B raw13083step2 raw13083step2Labels := by
      have ha : raw13083step2 = raw13083step1 := by apply Matrix.ext; unfold raw13083step2 raw13083step1; decide +kernel
      have hl : raw13083step1Labels = labelEmbedding1 ∘ raw13083step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13083step1 raw13083step1Labels raw13083step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2684 node2684Labels := by rfl

theorem canonical13084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13084 raw13084Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw13084 raw13084Labels = mixedMoment B raw13084step0 raw13084step0Labels := by
      have hz : ∀ j, raw13084 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13084step0 = (fun i j => raw13084 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13084step0 raw13084; decide +kernel
      have hl : raw13084step0Labels = raw13084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13084 raw13084Labels permutation265 hz
    mixedMoment B raw13084step0 raw13084step0Labels = mixedMoment B raw13084step1 raw13084step1Labels := by
      have ha : raw13084step1 = (fun i j => raw13084step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13084step1 raw13084step0; decide +kernel
      have hl : raw13084step1Labels = raw13084step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13084step0 raw13084step0Labels permutation32 permutation7
    mixedMoment B raw13084step1 raw13084step1Labels = mixedMoment B raw13084step2 raw13084step2Labels := by
      have ha : raw13084step2 = raw13084step1 := by apply Matrix.ext; unfold raw13084step2 raw13084step1; decide +kernel
      have hl : raw13084step1Labels = labelEmbedding1 ∘ raw13084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13084step1 raw13084step1Labels raw13084step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2684 node2684Labels := by rfl

theorem canonical13085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13085 raw13085Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw13085 raw13085Labels = mixedMoment B raw13085step0 raw13085step0Labels := by
      have ha : raw13085step0 = (fun i j => raw13085 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13085step0 raw13085; decide +kernel
      have hl : raw13085step0Labels = raw13085Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13085 raw13085Labels permutation176 permutation7
    mixedMoment B raw13085step0 raw13085step0Labels = mixedMoment B raw13085step1 raw13085step1Labels := by
      have ha : raw13085step1 = raw13085step0 := by apply Matrix.ext; unfold raw13085step1 raw13085step0; decide +kernel
      have hl : raw13085step0Labels = labelEmbedding1 ∘ raw13085step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13085step0 raw13085step0Labels raw13085step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3221 node3221Labels := by rfl

theorem canonical13086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13086 raw13086Labels = mixedMoment B node3076 node3076Labels := by
  calc
    mixedMoment B raw13086 raw13086Labels = mixedMoment B raw13086step0 raw13086step0Labels := by
      have ha : raw13086step0 = (fun i j => raw13086 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13086step0 raw13086; decide +kernel
      have hl : raw13086step0Labels = raw13086Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13086 raw13086Labels permutation152 permutation7
    mixedMoment B raw13086step0 raw13086step0Labels = mixedMoment B raw13086step1 raw13086step1Labels := by
      have ha : raw13086step1 = raw13086step0 := by apply Matrix.ext; unfold raw13086step1 raw13086step0; decide +kernel
      have hl : raw13086step0Labels = labelEmbedding1 ∘ raw13086step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13086step0 raw13086step0Labels raw13086step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3076 node3076Labels := by rfl

theorem canonical13087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13087 raw13087Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw13087 raw13087Labels = mixedMoment B raw13087step0 raw13087step0Labels := by
      have ha : raw13087step0 = (fun i j => raw13087 (permutation177 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13087step0 raw13087; decide +kernel
      have hl : raw13087step0Labels = raw13087Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13087 raw13087Labels permutation177 permutation7
    mixedMoment B raw13087step0 raw13087step0Labels = mixedMoment B raw13087step1 raw13087step1Labels := by
      have ha : raw13087step1 = raw13087step0 := by apply Matrix.ext; unfold raw13087step1 raw13087step0; decide +kernel
      have hl : raw13087step0Labels = labelEmbedding1 ∘ raw13087step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13087step0 raw13087step0Labels raw13087step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

theorem canonical13088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13088 raw13088Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw13088 raw13088Labels = mixedMoment B raw13088step0 raw13088step0Labels := by
      have ha : raw13088step0 = (fun i j => raw13088 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13088step0 raw13088; decide +kernel
      have hl : raw13088step0Labels = raw13088Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13088 raw13088Labels permutation176 permutation7
    mixedMoment B raw13088step0 raw13088step0Labels = mixedMoment B raw13088step1 raw13088step1Labels := by
      have ha : raw13088step1 = raw13088step0 := by apply Matrix.ext; unfold raw13088step1 raw13088step0; decide +kernel
      have hl : raw13088step0Labels = labelEmbedding1 ∘ raw13088step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13088step0 raw13088step0Labels raw13088step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

theorem canonical13089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13089 raw13089Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw13089 raw13089Labels = mixedMoment B raw13089step0 raw13089step0Labels := by
      have hz : ∀ j, raw13089 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13089step0 = (fun i j => raw13089 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13089step0 raw13089; decide +kernel
      have hl : raw13089step0Labels = raw13089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13089 raw13089Labels permutation265 hz
    mixedMoment B raw13089step0 raw13089step0Labels = mixedMoment B raw13089step1 raw13089step1Labels := by
      have ha : raw13089step1 = (fun i j => raw13089step0 (permutation65 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13089step1 raw13089step0; decide +kernel
      have hl : raw13089step1Labels = raw13089step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13089step0 raw13089step0Labels permutation65 permutation5
    mixedMoment B raw13089step1 raw13089step1Labels = mixedMoment B raw13089step2 raw13089step2Labels := by
      have ha : raw13089step2 = raw13089step1 := by apply Matrix.ext; unfold raw13089step2 raw13089step1; decide +kernel
      have hl : raw13089step1Labels = labelEmbedding1 ∘ raw13089step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13089step1 raw13089step1Labels raw13089step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2235 node2235Labels := by rfl

theorem canonical13090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13090 raw13090Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw13090 raw13090Labels = mixedMoment B raw13090step0 raw13090step0Labels := by
      have hz : ∀ j, raw13090 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13090step0 = (fun i j => raw13090 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13090step0 raw13090; decide +kernel
      have hl : raw13090step0Labels = raw13090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13090 raw13090Labels permutation265 hz
    mixedMoment B raw13090step0 raw13090step0Labels = mixedMoment B raw13090step1 raw13090step1Labels := by
      have ha : raw13090step1 = (fun i j => raw13090step0 (permutation67 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13090step1 raw13090step0; decide +kernel
      have hl : raw13090step1Labels = raw13090step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13090step0 raw13090step0Labels permutation67 permutation5
    mixedMoment B raw13090step1 raw13090step1Labels = mixedMoment B raw13090step2 raw13090step2Labels := by
      have ha : raw13090step2 = raw13090step1 := by apply Matrix.ext; unfold raw13090step2 raw13090step1; decide +kernel
      have hl : raw13090step1Labels = labelEmbedding1 ∘ raw13090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13090step1 raw13090step1Labels raw13090step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2246 node2246Labels := by rfl

theorem canonical13091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13091 raw13091Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw13091 raw13091Labels = mixedMoment B raw13091step0 raw13091step0Labels := by
      have hz : ∀ j, raw13091 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13091step0 = (fun i j => raw13091 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13091step0 raw13091; decide +kernel
      have hl : raw13091step0Labels = raw13091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13091 raw13091Labels permutation265 hz
    mixedMoment B raw13091step0 raw13091step0Labels = mixedMoment B raw13091step1 raw13091step1Labels := by
      have ha : raw13091step1 = (fun i j => raw13091step0 (permutation65 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13091step1 raw13091step0; decide +kernel
      have hl : raw13091step1Labels = raw13091step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13091step0 raw13091step0Labels permutation65 permutation5
    mixedMoment B raw13091step1 raw13091step1Labels = mixedMoment B raw13091step2 raw13091step2Labels := by
      have ha : raw13091step2 = raw13091step1 := by apply Matrix.ext; unfold raw13091step2 raw13091step1; decide +kernel
      have hl : raw13091step1Labels = labelEmbedding1 ∘ raw13091step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13091step1 raw13091step1Labels raw13091step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2246 node2246Labels := by rfl

theorem canonical13092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13092 raw13092Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw13092 raw13092Labels = mixedMoment B raw13092step0 raw13092step0Labels := by
      have hz : ∀ j, raw13092 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13092step0 = (fun i j => raw13092 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13092step0 raw13092; decide +kernel
      have hl : raw13092step0Labels = raw13092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13092 raw13092Labels permutation265 hz
    mixedMoment B raw13092step0 raw13092step0Labels = mixedMoment B raw13092step1 raw13092step1Labels := by
      have ha : raw13092step1 = (fun i j => raw13092step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13092step1 raw13092step0; decide +kernel
      have hl : raw13092step1Labels = raw13092step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13092step0 raw13092step0Labels permutation32 permutation7
    mixedMoment B raw13092step1 raw13092step1Labels = mixedMoment B raw13092step2 raw13092step2Labels := by
      have ha : raw13092step2 = raw13092step1 := by apply Matrix.ext; unfold raw13092step2 raw13092step1; decide +kernel
      have hl : raw13092step1Labels = labelEmbedding1 ∘ raw13092step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13092step1 raw13092step1Labels raw13092step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

theorem canonical13093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13093 raw13093Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13093 raw13093Labels = mixedMoment B raw13093step0 raw13093step0Labels := by
      have hz : ∀ j, raw13093 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13093step0 = (fun i j => raw13093 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13093step0 raw13093; decide +kernel
      have hl : raw13093step0Labels = raw13093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13093 raw13093Labels permutation265 hz
    mixedMoment B raw13093step0 raw13093step0Labels = mixedMoment B raw13093step1 raw13093step1Labels := by
      have ha : raw13093step1 = (fun i j => raw13093step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13093step1 raw13093step0; decide +kernel
      have hl : raw13093step1Labels = raw13093step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13093step0 raw13093step0Labels permutation32 permutation7
    mixedMoment B raw13093step1 raw13093step1Labels = mixedMoment B raw13093step2 raw13093step2Labels := by
      have ha : raw13093step2 = raw13093step1 := by apply Matrix.ext; unfold raw13093step2 raw13093step1; decide +kernel
      have hl : raw13093step1Labels = labelEmbedding1 ∘ raw13093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13093step1 raw13093step1Labels raw13093step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3100 node3100Labels := by rfl

theorem canonical13094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13094 raw13094Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw13094 raw13094Labels = mixedMoment B raw13094step0 raw13094step0Labels := by
      have hz : ∀ j, raw13094 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13094step0 = (fun i j => raw13094 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13094step0 raw13094; decide +kernel
      have hl : raw13094step0Labels = raw13094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13094 raw13094Labels permutation265 hz
    mixedMoment B raw13094step0 raw13094step0Labels = mixedMoment B raw13094step1 raw13094step1Labels := by
      have ha : raw13094step1 = (fun i j => raw13094step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13094step1 raw13094step0; decide +kernel
      have hl : raw13094step1Labels = raw13094step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13094step0 raw13094step0Labels permutation33 permutation7
    mixedMoment B raw13094step1 raw13094step1Labels = mixedMoment B raw13094step2 raw13094step2Labels := by
      have ha : raw13094step2 = raw13094step1 := by apply Matrix.ext; unfold raw13094step2 raw13094step1; decide +kernel
      have hl : raw13094step1Labels = labelEmbedding1 ∘ raw13094step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13094step1 raw13094step1Labels raw13094step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical13095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13095 raw13095Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw13095 raw13095Labels = mixedMoment B raw13095step0 raw13095step0Labels := by
      have hz : ∀ j, raw13095 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13095step0 = (fun i j => raw13095 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13095step0 raw13095; decide +kernel
      have hl : raw13095step0Labels = raw13095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13095 raw13095Labels permutation265 hz
    mixedMoment B raw13095step0 raw13095step0Labels = mixedMoment B raw13095step1 raw13095step1Labels := by
      have ha : raw13095step1 = (fun i j => raw13095step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13095step1 raw13095step0; decide +kernel
      have hl : raw13095step1Labels = raw13095step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13095step0 raw13095step0Labels permutation32 permutation7
    mixedMoment B raw13095step1 raw13095step1Labels = mixedMoment B raw13095step2 raw13095step2Labels := by
      have ha : raw13095step2 = raw13095step1 := by apply Matrix.ext; unfold raw13095step2 raw13095step1; decide +kernel
      have hl : raw13095step1Labels = labelEmbedding1 ∘ raw13095step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13095step1 raw13095step1Labels raw13095step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical13096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13096 raw13096Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw13096 raw13096Labels = mixedMoment B raw13096step0 raw13096step0Labels := by
      have hz : ∀ j, raw13096 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13096step0 = (fun i j => raw13096 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13096step0 raw13096; decide +kernel
      have hl : raw13096step0Labels = raw13096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13096 raw13096Labels permutation265 hz
    mixedMoment B raw13096step0 raw13096step0Labels = mixedMoment B raw13096step1 raw13096step1Labels := by
      have ha : raw13096step1 = (fun i j => raw13096step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13096step1 raw13096step0; decide +kernel
      have hl : raw13096step1Labels = raw13096step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13096step0 raw13096step0Labels permutation34 permutation7
    mixedMoment B raw13096step1 raw13096step1Labels = mixedMoment B raw13096step2 raw13096step2Labels := by
      have ha : raw13096step2 = raw13096step1 := by apply Matrix.ext; unfold raw13096step2 raw13096step1; decide +kernel
      have hl : raw13096step1Labels = labelEmbedding1 ∘ raw13096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13096step1 raw13096step1Labels raw13096step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

theorem canonical13097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13097 raw13097Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13097 raw13097Labels = mixedMoment B raw13097step0 raw13097step0Labels := by
      have hz : ∀ j, raw13097 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13097step0 = (fun i j => raw13097 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13097step0 raw13097; decide +kernel
      have hl : raw13097step0Labels = raw13097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13097 raw13097Labels permutation265 hz
    mixedMoment B raw13097step0 raw13097step0Labels = mixedMoment B raw13097step1 raw13097step1Labels := by
      have ha : raw13097step1 = (fun i j => raw13097step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13097step1 raw13097step0; decide +kernel
      have hl : raw13097step1Labels = raw13097step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13097step0 raw13097step0Labels permutation34 permutation7
    mixedMoment B raw13097step1 raw13097step1Labels = mixedMoment B raw13097step2 raw13097step2Labels := by
      have ha : raw13097step2 = raw13097step1 := by apply Matrix.ext; unfold raw13097step2 raw13097step1; decide +kernel
      have hl : raw13097step1Labels = labelEmbedding1 ∘ raw13097step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13097step1 raw13097step1Labels raw13097step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3100 node3100Labels := by rfl

theorem canonical13098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13098 raw13098Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw13098 raw13098Labels = mixedMoment B raw13098step0 raw13098step0Labels := by
      have hz : ∀ j, raw13098 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13098step0 = (fun i j => raw13098 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13098step0 raw13098; decide +kernel
      have hl : raw13098step0Labels = raw13098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13098 raw13098Labels permutation265 hz
    mixedMoment B raw13098step0 raw13098step0Labels = mixedMoment B raw13098step1 raw13098step1Labels := by
      have ha : raw13098step1 = (fun i j => raw13098step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13098step1 raw13098step0; decide +kernel
      have hl : raw13098step1Labels = raw13098step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13098step0 raw13098step0Labels permutation34 permutation7
    mixedMoment B raw13098step1 raw13098step1Labels = mixedMoment B raw13098step2 raw13098step2Labels := by
      have ha : raw13098step2 = raw13098step1 := by apply Matrix.ext; unfold raw13098step2 raw13098step1; decide +kernel
      have hl : raw13098step1Labels = labelEmbedding1 ∘ raw13098step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13098step1 raw13098step1Labels raw13098step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

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

theorem canonical1818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1818 raw1818Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw1818 raw1818Labels = mixedMoment B raw1818step0 raw1818step0Labels := by
      have ha : raw1818step0 = (fun i j => raw1818 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1818step0 raw1818; decide +kernel
      have hl : raw1818step0Labels = raw1818Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1818 raw1818Labels permutation32 permutation4
    mixedMoment B raw1818step0 raw1818step0Labels = mixedMoment B raw1818step1 raw1818step1Labels := by
      have ha : raw1818step1 = raw1818step0 := by apply Matrix.ext; unfold raw1818step1 raw1818step0; decide +kernel
      have hl : raw1818step0Labels = labelEmbedding7 ∘ raw1818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1818step0 raw1818step0Labels raw1818step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical1819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1819 raw1819Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw1819 raw1819Labels = mixedMoment B raw1819step0 raw1819step0Labels := by
      have ha : raw1819step0 = (fun i j => raw1819 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1819step0 raw1819; decide +kernel
      have hl : raw1819step0Labels = raw1819Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1819 raw1819Labels permutation32 permutation4
    _ = mixedMoment B node2245 node2245Labels := by rfl

theorem canonical1820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1820 raw1820Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw1820 raw1820Labels = mixedMoment B raw1820step0 raw1820step0Labels := by
      have ha : raw1820step0 = (fun i j => raw1820 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1820step0 raw1820; decide +kernel
      have hl : raw1820step0Labels = raw1820Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1820 raw1820Labels permutation50 permutation6
    mixedMoment B raw1820step0 raw1820step0Labels = mixedMoment B raw1820step1 raw1820step1Labels := by
      have ha : raw1820step1 = -raw1820step0 := by apply Matrix.ext; change ∀ i j, raw1820step1 i j = -(raw1820step0 i j); unfold raw1820step1 raw1820step0; decide +kernel
      have hl : raw1820step1Labels = raw1820step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1820step1 raw1820step1Labels = mixedMoment B raw1820step2 raw1820step2Labels := by
      have ha : raw1820step2 = raw1820step1 := by apply Matrix.ext; unfold raw1820step2 raw1820step1; decide +kernel
      have hl : raw1820step1Labels = labelEmbedding1 ∘ raw1820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1820step1 raw1820step1Labels raw1820step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

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

theorem canonical2253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2253 raw2253Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw2253 raw2253Labels = mixedMoment B raw2253step0 raw2253step0Labels := by
      have ha : raw2253step0 = (fun i j => raw2253 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2253step0 raw2253; decide +kernel
      have hl : raw2253step0Labels = raw2253Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2253 raw2253Labels permutation32 permutation4
    mixedMoment B raw2253step0 raw2253step0Labels = mixedMoment B raw2253step1 raw2253step1Labels := by
      have ha : raw2253step1 = raw2253step0 := by apply Matrix.ext; unfold raw2253step1 raw2253step0; decide +kernel
      have hl : raw2253step0Labels = labelEmbedding7 ∘ raw2253step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2253step0 raw2253step0Labels raw2253step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

theorem canonical2254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2254 raw2254Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw2254 raw2254Labels = mixedMoment B raw2254step0 raw2254step0Labels := by
      have ha : raw2254step0 = (fun i j => raw2254 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2254step0 raw2254; decide +kernel
      have hl : raw2254step0Labels = raw2254Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2254 raw2254Labels permutation32 permutation4
    _ = mixedMoment B node2684 node2684Labels := by rfl

theorem canonical2255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2255 raw2255Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw2255 raw2255Labels = mixedMoment B raw2255step0 raw2255step0Labels := by
      have ha : raw2255step0 = (fun i j => raw2255 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2255step0 raw2255; decide +kernel
      have hl : raw2255step0Labels = raw2255Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2255 raw2255Labels permutation32 permutation6
    mixedMoment B raw2255step0 raw2255step0Labels = mixedMoment B raw2255step1 raw2255step1Labels := by
      have ha : raw2255step1 = -raw2255step0 := by apply Matrix.ext; change ∀ i j, raw2255step1 i j = -(raw2255step0 i j); unfold raw2255step1 raw2255step0; decide +kernel
      have hl : raw2255step1Labels = raw2255step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2255step1 raw2255step1Labels = mixedMoment B raw2255step2 raw2255step2Labels := by
      have ha : raw2255step2 = raw2255step1 := by apply Matrix.ext; unfold raw2255step2 raw2255step1; decide +kernel
      have hl : raw2255step1Labels = labelEmbedding1 ∘ raw2255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2255step1 raw2255step1Labels raw2255step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3394 node3394Labels := by rfl

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

theorem canonical11669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11669 raw11669Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw11669 raw11669Labels = mixedMoment B raw11669step0 raw11669step0Labels := by
      have hz : ∀ j, raw11669 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11669step0 = (fun i j => raw11669 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11669step0 raw11669; decide +kernel
      have hl : raw11669step0Labels = raw11669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11669 raw11669Labels permutation265 hz
    mixedMoment B raw11669step0 raw11669step0Labels = mixedMoment B raw11669step1 raw11669step1Labels := by
      have ha : raw11669step1 = (fun i j => raw11669step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11669step1 raw11669step0; decide +kernel
      have hl : raw11669step1Labels = raw11669step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11669step0 raw11669step0Labels permutation32 permutation6
    mixedMoment B raw11669step1 raw11669step1Labels = mixedMoment B raw11669step2 raw11669step2Labels := by
      have ha : raw11669step2 = raw11669step1 := by apply Matrix.ext; unfold raw11669step2 raw11669step1; decide +kernel
      have hl : raw11669step1Labels = labelEmbedding9 ∘ raw11669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11669step1 raw11669step1Labels raw11669step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical11674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11674 raw11674Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw11674 raw11674Labels = mixedMoment B raw11674step0 raw11674step0Labels := by
      have ha : raw11674step0 = (fun i j => raw11674 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11674step0 raw11674; decide +kernel
      have hl : raw11674step0Labels = raw11674Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11674 raw11674Labels permutation152 permutation6
    mixedMoment B raw11674step0 raw11674step0Labels = mixedMoment B raw11674step1 raw11674step1Labels := by
      have ha : raw11674step1 = raw11674step0 := by apply Matrix.ext; unfold raw11674step1 raw11674step0; decide +kernel
      have hl : raw11674step0Labels = labelEmbedding9 ∘ raw11674step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11674step0 raw11674step0Labels raw11674step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical11729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11729 raw11729Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw11729 raw11729Labels = mixedMoment B raw11729step0 raw11729step0Labels := by
      have hz : ∀ j, raw11729 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11729step0 = (fun i j => raw11729 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11729step0 raw11729; decide +kernel
      have hl : raw11729step0Labels = raw11729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11729 raw11729Labels permutation265 hz
    mixedMoment B raw11729step0 raw11729step0Labels = mixedMoment B raw11729step1 raw11729step1Labels := by
      have ha : raw11729step1 = (fun i j => raw11729step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11729step1 raw11729step0; decide +kernel
      have hl : raw11729step1Labels = raw11729step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11729step0 raw11729step0Labels permutation36 permutation7
    mixedMoment B raw11729step1 raw11729step1Labels = mixedMoment B raw11729step2 raw11729step2Labels := by
      have ha : raw11729step2 = raw11729step1 := by apply Matrix.ext; unfold raw11729step2 raw11729step1; decide +kernel
      have hl : raw11729step1Labels = labelEmbedding1 ∘ raw11729step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11729step1 raw11729step1Labels raw11729step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3100 node3100Labels := by rfl

theorem canonical11734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11734 raw11734Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw11734 raw11734Labels = mixedMoment B raw11734step0 raw11734step0Labels := by
      have ha : raw11734step0 = (fun i j => raw11734 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11734step0 raw11734; decide +kernel
      have hl : raw11734step0Labels = raw11734Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11734 raw11734Labels permutation180 permutation7
    mixedMoment B raw11734step0 raw11734step0Labels = mixedMoment B raw11734step1 raw11734step1Labels := by
      have ha : raw11734step1 = raw11734step0 := by apply Matrix.ext; unfold raw11734step1 raw11734step0; decide +kernel
      have hl : raw11734step0Labels = labelEmbedding1 ∘ raw11734step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11734step0 raw11734step0Labels raw11734step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12001 raw12001Labels = mixedMoment B node5227 node5227Labels := by
  calc
    mixedMoment B raw12001 raw12001Labels = mixedMoment B raw12001step0 raw12001step0Labels := by
      have ha : raw12001step0 = (fun i j => raw12001 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12001step0 raw12001; decide +kernel
      have hl : raw12001step0Labels = raw12001Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12001 raw12001Labels permutation176 permutation7
    mixedMoment B raw12001step0 raw12001step0Labels = mixedMoment B raw12001step1 raw12001step1Labels := by
      have ha : raw12001step1 = raw12001step0 := by apply Matrix.ext; unfold raw12001step1 raw12001step0; decide +kernel
      have hl : raw12001step0Labels = labelEmbedding10 ∘ raw12001step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12001step0 raw12001step0Labels raw12001step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5227 node5227Labels := by rfl

theorem canonical12002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12002 raw12002Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw12002 raw12002Labels = mixedMoment B raw12002step0 raw12002step0Labels := by
      have hz : ∀ j, raw12002 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12002step0 = (fun i j => raw12002 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12002step0 raw12002; decide +kernel
      have hl : raw12002step0Labels = raw12002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12002 raw12002Labels permutation265 hz
    mixedMoment B raw12002step0 raw12002step0Labels = mixedMoment B raw12002step1 raw12002step1Labels := by
      have ha : raw12002step1 = (fun i j => raw12002step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12002step1 raw12002step0; decide +kernel
      have hl : raw12002step1Labels = raw12002step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12002step0 raw12002step0Labels permutation41 permutation4
    mixedMoment B raw12002step1 raw12002step1Labels = mixedMoment B raw12002step2 raw12002step2Labels := by
      have ha : raw12002step2 = -raw12002step1 := by apply Matrix.ext; change ∀ i j, raw12002step2 i j = -(raw12002step1 i j); unfold raw12002step2 raw12002step1; decide +kernel
      have hl : raw12002step2Labels = raw12002step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12002step2 raw12002step2Labels = mixedMoment B raw12002step3 raw12002step3Labels := by
      have ha : raw12002step3 = raw12002step2 := by apply Matrix.ext; unfold raw12002step3 raw12002step2; decide +kernel
      have hl : raw12002step2Labels = labelEmbedding7 ∘ raw12002step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12002step2 raw12002step2Labels raw12002step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical12003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12003 raw12003Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw12003 raw12003Labels = mixedMoment B raw12003step0 raw12003step0Labels := by
      have hz : ∀ j, raw12003 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12003step0 = (fun i j => raw12003 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12003step0 raw12003; decide +kernel
      have hl : raw12003step0Labels = raw12003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12003 raw12003Labels permutation265 hz
    mixedMoment B raw12003step0 raw12003step0Labels = mixedMoment B raw12003step1 raw12003step1Labels := by
      have ha : raw12003step1 = (fun i j => raw12003step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12003step1 raw12003step0; decide +kernel
      have hl : raw12003step1Labels = raw12003step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12003step0 raw12003step0Labels permutation32 permutation6
    mixedMoment B raw12003step1 raw12003step1Labels = mixedMoment B raw12003step2 raw12003step2Labels := by
      have ha : raw12003step2 = raw12003step1 := by apply Matrix.ext; unfold raw12003step2 raw12003step1; decide +kernel
      have hl : raw12003step1Labels = labelEmbedding9 ∘ raw12003step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12003step1 raw12003step1Labels raw12003step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical12004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12004 raw12004Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw12004 raw12004Labels = mixedMoment B raw12004step0 raw12004step0Labels := by
      have hz : ∀ j, raw12004 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12004step0 = (fun i j => raw12004 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12004step0 raw12004; decide +kernel
      have hl : raw12004step0Labels = raw12004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12004 raw12004Labels permutation265 hz
    mixedMoment B raw12004step0 raw12004step0Labels = mixedMoment B raw12004step1 raw12004step1Labels := by
      have ha : raw12004step1 = (fun i j => raw12004step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12004step1 raw12004step0; decide +kernel
      have hl : raw12004step1Labels = raw12004step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12004step0 raw12004step0Labels permutation34 permutation6
    mixedMoment B raw12004step1 raw12004step1Labels = mixedMoment B raw12004step2 raw12004step2Labels := by
      have ha : raw12004step2 = raw12004step1 := by apply Matrix.ext; unfold raw12004step2 raw12004step1; decide +kernel
      have hl : raw12004step1Labels = labelEmbedding9 ∘ raw12004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12004step1 raw12004step1Labels raw12004step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical12010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12010 raw12010Labels = mixedMoment B node4878 node4878Labels := by
  calc
    mixedMoment B raw12010 raw12010Labels = mixedMoment B raw12010step0 raw12010step0Labels := by
      have ha : raw12010step0 = (fun i j => raw12010 (permutation355 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12010step0 raw12010; decide +kernel
      have hl : raw12010step0Labels = raw12010Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12010 raw12010Labels permutation355 permutation3
    mixedMoment B raw12010step0 raw12010step0Labels = mixedMoment B raw12010step1 raw12010step1Labels := by
      have ha : raw12010step1 = -raw12010step0 := by apply Matrix.ext; change ∀ i j, raw12010step1 i j = -(raw12010step0 i j); unfold raw12010step1 raw12010step0; decide +kernel
      have hl : raw12010step1Labels = raw12010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12010step1 raw12010step1Labels = mixedMoment B raw12010step2 raw12010step2Labels := by
      have ha : raw12010step2 = raw12010step1 := by apply Matrix.ext; unfold raw12010step2 raw12010step1; decide +kernel
      have hl : raw12010step1Labels = labelEmbedding6 ∘ raw12010step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12010step1 raw12010step1Labels raw12010step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4878 node4878Labels := by rfl

theorem canonical12014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12014 raw12014Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw12014 raw12014Labels = mixedMoment B raw12014step0 raw12014step0Labels := by
      have ha : raw12014step0 = (fun i j => raw12014 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12014step0 raw12014; decide +kernel
      have hl : raw12014step0Labels = raw12014Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12014 raw12014Labels permutation155 permutation6
    mixedMoment B raw12014step0 raw12014step0Labels = mixedMoment B raw12014step1 raw12014step1Labels := by
      have ha : raw12014step1 = raw12014step0 := by apply Matrix.ext; unfold raw12014step1 raw12014step0; decide +kernel
      have hl : raw12014step0Labels = labelEmbedding9 ∘ raw12014step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12014step0 raw12014step0Labels raw12014step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical12018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12018 raw12018Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw12018 raw12018Labels = mixedMoment B raw12018step0 raw12018step0Labels := by
      have ha : raw12018step0 = (fun i j => raw12018 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12018step0 raw12018; decide +kernel
      have hl : raw12018step0Labels = raw12018Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12018 raw12018Labels permutation153 permutation6
    mixedMoment B raw12018step0 raw12018step0Labels = mixedMoment B raw12018step1 raw12018step1Labels := by
      have ha : raw12018step1 = raw12018step0 := by apply Matrix.ext; unfold raw12018step1 raw12018step0; decide +kernel
      have hl : raw12018step0Labels = labelEmbedding9 ∘ raw12018step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12018step0 raw12018step0Labels raw12018step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12045 raw12045Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw12045 raw12045Labels = mixedMoment B raw12045step0 raw12045step0Labels := by
      have ha : raw12045step0 = (fun i j => raw12045 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12045step0 raw12045; decide +kernel
      have hl : raw12045step0Labels = raw12045Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12045 raw12045Labels permutation176 permutation7
    mixedMoment B raw12045step0 raw12045step0Labels = mixedMoment B raw12045step1 raw12045step1Labels := by
      have ha : raw12045step1 = raw12045step0 := by apply Matrix.ext; unfold raw12045step1 raw12045step0; decide +kernel
      have hl : raw12045step0Labels = labelEmbedding1 ∘ raw12045step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12045step0 raw12045step0Labels raw12045step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2671 node2671Labels := by rfl

theorem canonical12046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12046 raw12046Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw12046 raw12046Labels = mixedMoment B raw12046step0 raw12046step0Labels := by
      have hz : ∀ j, raw12046 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12046step0 = (fun i j => raw12046 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12046step0 raw12046; decide +kernel
      have hl : raw12046step0Labels = raw12046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12046 raw12046Labels permutation265 hz
    mixedMoment B raw12046step0 raw12046step0Labels = mixedMoment B raw12046step1 raw12046step1Labels := by
      have ha : raw12046step1 = (fun i j => raw12046step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12046step1 raw12046step0; decide +kernel
      have hl : raw12046step1Labels = raw12046step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12046step0 raw12046step0Labels permutation36 permutation7
    mixedMoment B raw12046step1 raw12046step1Labels = mixedMoment B raw12046step2 raw12046step2Labels := by
      have ha : raw12046step2 = raw12046step1 := by apply Matrix.ext; unfold raw12046step2 raw12046step1; decide +kernel
      have hl : raw12046step1Labels = labelEmbedding1 ∘ raw12046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12046step1 raw12046step1Labels raw12046step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

theorem canonical12047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12047 raw12047Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw12047 raw12047Labels = mixedMoment B raw12047step0 raw12047step0Labels := by
      have hz : ∀ j, raw12047 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12047step0 = (fun i j => raw12047 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12047step0 raw12047; decide +kernel
      have hl : raw12047step0Labels = raw12047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12047 raw12047Labels permutation265 hz
    mixedMoment B raw12047step0 raw12047step0Labels = mixedMoment B raw12047step1 raw12047step1Labels := by
      have ha : raw12047step1 = (fun i j => raw12047step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12047step1 raw12047step0; decide +kernel
      have hl : raw12047step1Labels = raw12047step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12047step0 raw12047step0Labels permutation37 permutation7
    mixedMoment B raw12047step1 raw12047step1Labels = mixedMoment B raw12047step2 raw12047step2Labels := by
      have ha : raw12047step2 = raw12047step1 := by apply Matrix.ext; unfold raw12047step2 raw12047step1; decide +kernel
      have hl : raw12047step1Labels = labelEmbedding1 ∘ raw12047step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12047step1 raw12047step1Labels raw12047step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical12048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12048 raw12048Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw12048 raw12048Labels = mixedMoment B raw12048step0 raw12048step0Labels := by
      have hz : ∀ j, raw12048 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12048step0 = (fun i j => raw12048 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12048step0 raw12048; decide +kernel
      have hl : raw12048step0Labels = raw12048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12048 raw12048Labels permutation265 hz
    mixedMoment B raw12048step0 raw12048step0Labels = mixedMoment B raw12048step1 raw12048step1Labels := by
      have ha : raw12048step1 = (fun i j => raw12048step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12048step1 raw12048step0; decide +kernel
      have hl : raw12048step1Labels = raw12048step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12048step0 raw12048step0Labels permutation36 permutation7
    mixedMoment B raw12048step1 raw12048step1Labels = mixedMoment B raw12048step2 raw12048step2Labels := by
      have ha : raw12048step2 = raw12048step1 := by apply Matrix.ext; unfold raw12048step2 raw12048step1; decide +kernel
      have hl : raw12048step1Labels = labelEmbedding1 ∘ raw12048step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12048step1 raw12048step1Labels raw12048step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical12054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12054 raw12054Labels = mixedMoment B node2234 node2234Labels := by
  calc
    mixedMoment B raw12054 raw12054Labels = mixedMoment B raw12054step0 raw12054step0Labels := by
      have ha : raw12054step0 = (fun i j => raw12054 (permutation394 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12054step0 raw12054; decide +kernel
      have hl : raw12054step0Labels = raw12054Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12054 raw12054Labels permutation394 permutation5
    mixedMoment B raw12054step0 raw12054step0Labels = mixedMoment B raw12054step1 raw12054step1Labels := by
      have ha : raw12054step1 = raw12054step0 := by apply Matrix.ext; unfold raw12054step1 raw12054step0; decide +kernel
      have hl : raw12054step0Labels = labelEmbedding1 ∘ raw12054step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12054step0 raw12054step0Labels raw12054step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2234 node2234Labels := by rfl

theorem canonical12058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12058 raw12058Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw12058 raw12058Labels = mixedMoment B raw12058step0 raw12058step0Labels := by
      have ha : raw12058step0 = (fun i j => raw12058 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12058step0 raw12058; decide +kernel
      have hl : raw12058step0Labels = raw12058Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12058 raw12058Labels permutation176 permutation7
    mixedMoment B raw12058step0 raw12058step0Labels = mixedMoment B raw12058step1 raw12058step1Labels := by
      have ha : raw12058step1 = raw12058step0 := by apply Matrix.ext; unfold raw12058step1 raw12058step0; decide +kernel
      have hl : raw12058step0Labels = labelEmbedding1 ∘ raw12058step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12058step0 raw12058step0Labels raw12058step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical12062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12062 raw12062Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw12062 raw12062Labels = mixedMoment B raw12062step0 raw12062step0Labels := by
      have ha : raw12062step0 = (fun i j => raw12062 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12062step0 raw12062; decide +kernel
      have hl : raw12062step0Labels = raw12062Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12062 raw12062Labels permutation178 permutation7
    mixedMoment B raw12062step0 raw12062step0Labels = mixedMoment B raw12062step1 raw12062step1Labels := by
      have ha : raw12062step1 = raw12062step0 := by apply Matrix.ext; unfold raw12062step1 raw12062step0; decide +kernel
      have hl : raw12062step0Labels = labelEmbedding1 ∘ raw12062step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12062step0 raw12062step0Labels raw12062step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical12065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12065 raw12065Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw12065 raw12065Labels = mixedMoment B raw12065step0 raw12065step0Labels := by
      have ha : raw12065step0 = (fun i j => raw12065 (permutation195 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12065step0 raw12065; decide +kernel
      have hl : raw12065step0Labels = raw12065Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12065 raw12065Labels permutation195 permutation2
    mixedMoment B raw12065step0 raw12065step0Labels = mixedMoment B raw12065step1 raw12065step1Labels := by
      have ha : raw12065step1 = -raw12065step0 := by apply Matrix.ext; change ∀ i j, raw12065step1 i j = -(raw12065step0 i j); unfold raw12065step1 raw12065step0; decide +kernel
      have hl : raw12065step1Labels = raw12065step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3376 node3376Labels := by rfl

theorem canonical12072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12072 raw12072Labels = mixedMoment B node3149 node3149Labels := by
  calc
    mixedMoment B raw12072 raw12072Labels = mixedMoment B raw12072step0 raw12072step0Labels := by
      have ha : raw12072step0 = (fun i j => raw12072 (permutation362 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12072step0 raw12072; decide +kernel
      have hl : raw12072step0Labels = raw12072Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12072 raw12072Labels permutation362 permutation2
    mixedMoment B raw12072step0 raw12072step0Labels = mixedMoment B raw12072step1 raw12072step1Labels := by
      have ha : raw12072step1 = -raw12072step0 := by apply Matrix.ext; change ∀ i j, raw12072step1 i j = -(raw12072step0 i j); unfold raw12072step1 raw12072step0; decide +kernel
      have hl : raw12072step1Labels = raw12072step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3149 node3149Labels := by rfl

theorem canonical12078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12078 raw12078Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw12078 raw12078Labels = mixedMoment B raw12078step0 raw12078step0Labels := by
      have hz : ∀ j, raw12078 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12078step0 = (fun i j => raw12078 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12078step0 raw12078; decide +kernel
      have hl : raw12078step0Labels = raw12078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12078 raw12078Labels permutation265 hz
    mixedMoment B raw12078step0 raw12078step0Labels = mixedMoment B raw12078step1 raw12078step1Labels := by
      have ha : raw12078step1 = (fun i j => raw12078step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12078step1 raw12078step0; decide +kernel
      have hl : raw12078step1Labels = raw12078step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12078step0 raw12078step0Labels permutation41 permutation4
    mixedMoment B raw12078step1 raw12078step1Labels = mixedMoment B raw12078step2 raw12078step2Labels := by
      have ha : raw12078step2 = -raw12078step1 := by apply Matrix.ext; change ∀ i j, raw12078step2 i j = -(raw12078step1 i j); unfold raw12078step2 raw12078step1; decide +kernel
      have hl : raw12078step2Labels = raw12078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical12079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12079 raw12079Labels = mixedMoment B node3505 node3505Labels := by
  calc
    mixedMoment B raw12079 raw12079Labels = mixedMoment B raw12079step0 raw12079step0Labels := by
      have ha : raw12079step0 = (fun i j => raw12079 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12079step0 raw12079; decide +kernel
      have hl : raw12079step0Labels = raw12079Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12079 raw12079Labels permutation161 permutation4
    mixedMoment B raw12079step0 raw12079step0Labels = mixedMoment B raw12079step1 raw12079step1Labels := by
      have ha : raw12079step1 = -raw12079step0 := by apply Matrix.ext; change ∀ i j, raw12079step1 i j = -(raw12079step0 i j); unfold raw12079step1 raw12079step0; decide +kernel
      have hl : raw12079step1Labels = raw12079step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3505 node3505Labels := by rfl

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

theorem canonical12522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12522 raw12522Labels = mixedMoment B node2956 node2956Labels := by
  calc
    mixedMoment B raw12522 raw12522Labels = mixedMoment B raw12522step0 raw12522step0Labels := by
      have hz : ∀ j, raw12522 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12522step0 = (fun i j => raw12522 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12522step0 raw12522; decide +kernel
      have hl : raw12522step0Labels = raw12522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12522 raw12522Labels permutation265 hz
    mixedMoment B raw12522step0 raw12522step0Labels = mixedMoment B raw12522step1 raw12522step1Labels := by
      have ha : raw12522step1 = (fun i j => raw12522step0 (permutation96 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12522step1 raw12522step0; decide +kernel
      have hl : raw12522step1Labels = raw12522step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12522step0 raw12522step0Labels permutation96 permutation2
    _ = mixedMoment B node2956 node2956Labels := by rfl

theorem canonical12523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12523 raw12523Labels = mixedMoment B node3552 node3552Labels := by
  calc
    mixedMoment B raw12523 raw12523Labels = mixedMoment B raw12523step0 raw12523step0Labels := by
      have hz : ∀ j, raw12523 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12523step0 = (fun i j => raw12523 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12523step0 raw12523; decide +kernel
      have hl : raw12523step0Labels = raw12523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12523 raw12523Labels permutation265 hz
    mixedMoment B raw12523step0 raw12523step0Labels = mixedMoment B raw12523step1 raw12523step1Labels := by
      have ha : raw12523step1 = (fun i j => raw12523step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12523step1 raw12523step0; decide +kernel
      have hl : raw12523step1Labels = raw12523step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12523step0 raw12523step0Labels permutation40 permutation4
    mixedMoment B raw12523step1 raw12523step1Labels = mixedMoment B raw12523step2 raw12523step2Labels := by
      have ha : raw12523step2 = -raw12523step1 := by apply Matrix.ext; change ∀ i j, raw12523step2 i j = -(raw12523step1 i j); unfold raw12523step2 raw12523step1; decide +kernel
      have hl : raw12523step2Labels = raw12523step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3552 node3552Labels := by rfl

theorem canonical12528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12528 raw12528Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw12528 raw12528Labels = mixedMoment B raw12528step0 raw12528step0Labels := by
      have hz : ∀ j, raw12528 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12528step0 = (fun i j => raw12528 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12528step0 raw12528; decide +kernel
      have hl : raw12528step0Labels = raw12528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12528 raw12528Labels permutation265 hz
    mixedMoment B raw12528step0 raw12528step0Labels = mixedMoment B raw12528step1 raw12528step1Labels := by
      have ha : raw12528step1 = (fun i j => raw12528step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12528step1 raw12528step0; decide +kernel
      have hl : raw12528step1Labels = raw12528step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12528step0 raw12528step0Labels permutation38 permutation4
    mixedMoment B raw12528step1 raw12528step1Labels = mixedMoment B raw12528step2 raw12528step2Labels := by
      have ha : raw12528step2 = -raw12528step1 := by apply Matrix.ext; change ∀ i j, raw12528step2 i j = -(raw12528step1 i j); unfold raw12528step2 raw12528step1; decide +kernel
      have hl : raw12528step2Labels = raw12528step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3581 node3581Labels := by rfl

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

theorem canonical12652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12652 raw12652Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw12652 raw12652Labels = mixedMoment B raw12652step0 raw12652step0Labels := by
      have hz : ∀ j, raw12652 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12652step0 = (fun i j => raw12652 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12652step0 raw12652; decide +kernel
      have hl : raw12652step0Labels = raw12652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12652 raw12652Labels permutation265 hz
    mixedMoment B raw12652step0 raw12652step0Labels = mixedMoment B raw12652step1 raw12652step1Labels := by
      have ha : raw12652step1 = (fun i j => raw12652step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12652step1 raw12652step0; decide +kernel
      have hl : raw12652step1Labels = raw12652step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12652step0 raw12652step0Labels permutation32 permutation7
    mixedMoment B raw12652step1 raw12652step1Labels = mixedMoment B raw12652step2 raw12652step2Labels := by
      have ha : raw12652step2 = raw12652step1 := by apply Matrix.ext; unfold raw12652step2 raw12652step1; decide +kernel
      have hl : raw12652step1Labels = labelEmbedding10 ∘ raw12652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12652step1 raw12652step1Labels raw12652step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

theorem canonical12655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12655 raw12655Labels = mixedMoment B node5283 node5283Labels := by
  calc
    mixedMoment B raw12655 raw12655Labels = mixedMoment B raw12655step0 raw12655step0Labels := by
      have ha : raw12655step0 = (fun i j => raw12655 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12655step0 raw12655; decide +kernel
      have hl : raw12655step0Labels = raw12655Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12655 raw12655Labels permutation152 permutation6
    mixedMoment B raw12655step0 raw12655step0Labels = mixedMoment B raw12655step1 raw12655step1Labels := by
      have ha : raw12655step1 = raw12655step0 := by apply Matrix.ext; unfold raw12655step1 raw12655step0; decide +kernel
      have hl : raw12655step0Labels = labelEmbedding9 ∘ raw12655step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12655step0 raw12655step0Labels raw12655step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5283 node5283Labels := by rfl

theorem canonical12658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12658 raw12658Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12658 raw12658Labels = mixedMoment B raw12658step0 raw12658step0Labels := by
      have hz : ∀ j, raw12658 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12658step0 = (fun i j => raw12658 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12658step0 raw12658; decide +kernel
      have hl : raw12658step0Labels = raw12658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12658 raw12658Labels permutation265 hz
    mixedMoment B raw12658step0 raw12658step0Labels = mixedMoment B raw12658step1 raw12658step1Labels := by
      have ha : raw12658step1 = (fun i j => raw12658step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12658step1 raw12658step0; decide +kernel
      have hl : raw12658step1Labels = raw12658step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12658step0 raw12658step0Labels permutation35 permutation6
    mixedMoment B raw12658step1 raw12658step1Labels = mixedMoment B raw12658step2 raw12658step2Labels := by
      have ha : raw12658step2 = raw12658step1 := by apply Matrix.ext; unfold raw12658step2 raw12658step1; decide +kernel
      have hl : raw12658step1Labels = labelEmbedding9 ∘ raw12658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12658step1 raw12658step1Labels raw12658step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical12660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12660 raw12660Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12660 raw12660Labels = mixedMoment B raw12660step0 raw12660step0Labels := by
      have hz : ∀ j, raw12660 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12660step0 = (fun i j => raw12660 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12660step0 raw12660; decide +kernel
      have hl : raw12660step0Labels = raw12660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12660 raw12660Labels permutation265 hz
    mixedMoment B raw12660step0 raw12660step0Labels = mixedMoment B raw12660step1 raw12660step1Labels := by
      have ha : raw12660step1 = (fun i j => raw12660step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12660step1 raw12660step0; decide +kernel
      have hl : raw12660step1Labels = raw12660step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12660step0 raw12660step0Labels permutation33 permutation6
    mixedMoment B raw12660step1 raw12660step1Labels = mixedMoment B raw12660step2 raw12660step2Labels := by
      have ha : raw12660step2 = raw12660step1 := by apply Matrix.ext; unfold raw12660step2 raw12660step1; decide +kernel
      have hl : raw12660step1Labels = labelEmbedding9 ∘ raw12660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12660step1 raw12660step1Labels raw12660step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4889 node4889Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2245 node2245Labels + mixedMoment B node2277 node2277Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1818 singletonSmall4889
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4889) = raw1818Labels := by decide +kernel
  rw [hl, canonical1818 B hB] at h
  have hc0 : mixedMoment B raw1818 (Fin.cases (0 : Fin 2) singletonSmall4889) =
      mixedMoment B node2245 node2245Labels := by
    have ha : raw1818 = raw1819 := by apply Matrix.ext; unfold raw1818 raw1819; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4889 = raw1819Labels := by decide +kernel
    rw [ha, hj, canonical1819 B hB]
  have hc1 : mixedMoment B raw1818 (Fin.cases (1 : Fin 2) singletonSmall4889) =
      mixedMoment B node2277 node2277Labels := by
    have ha : raw1818 = raw1820 := by apply Matrix.ext; unfold raw1818 raw1820; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4889 = raw1820Labels := by decide +kernel
    rw [ha, hj, canonical1820 B hB]
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

theorem singleton5237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5237 node5237Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2684 node2684Labels + mixedMoment B node3394 node3394Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2253 singletonSmall5237
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5237) = raw2253Labels := by decide +kernel
  rw [hl, canonical2253 B hB] at h
  have hc0 : mixedMoment B raw2253 (Fin.cases (0 : Fin 2) singletonSmall5237) =
      mixedMoment B node2684 node2684Labels := by
    have ha : raw2253 = raw2254 := by apply Matrix.ext; unfold raw2253 raw2254; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5237 = raw2254Labels := by decide +kernel
    rw [ha, hj, canonical2254 B hB]
  have hc1 : mixedMoment B raw2253 (Fin.cases (1 : Fin 2) singletonSmall5237) =
      mixedMoment B node3394 node3394Labels := by
    have ha : raw2253 = raw2255 := by apply Matrix.ext; unfold raw2253 raw2255; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5237 = raw2255Labels := by decide +kernel
    rw [ha, hj, canonical2255 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
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

theorem sound2089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2089 node2089Labels = Sparse.eval nodeValue2089 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2089) = mixedMoment B node2089 node2089Labels := rfl
  simpa [nodeValue2089, Sparse.eval] using hc.symm

theorem sound2092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2092 node2092Labels = Sparse.eval nodeValue2092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2092) = mixedMoment B node2092 node2092Labels := rfl
  simpa [nodeValue2092, Sparse.eval] using hc.symm

theorem sound2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2110 node2110Labels = Sparse.eval nodeValue2110 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2110) = mixedMoment B node2110 node2110Labels := rfl
  simpa [nodeValue2110, Sparse.eval] using hc.symm

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

theorem sound2234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2234 node2234Labels = Sparse.eval nodeValue2234 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2234) = mixedMoment B node2234 node2234Labels := rfl
  simpa [nodeValue2234, Sparse.eval] using hc.symm

theorem sound2235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2235 node2235Labels = Sparse.eval nodeValue2235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2235) = mixedMoment B node2235 node2235Labels := rfl
  simpa [nodeValue2235, Sparse.eval] using hc.symm

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

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2246 node2246Labels = Sparse.eval nodeValue2246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2246) = mixedMoment B node2246 node2246Labels := rfl
  simpa [nodeValue2246, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

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

theorem sound2571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2571 node2571Labels = Sparse.eval nodeValue2571 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2571) = mixedMoment B node2571 node2571Labels := rfl
  simpa [nodeValue2571, Sparse.eval] using hc.symm

theorem sound2575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2575 node2575Labels = Sparse.eval nodeValue2575 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2575) = mixedMoment B node2575 node2575Labels := rfl
  simpa [nodeValue2575, Sparse.eval] using hc.symm

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

theorem sound2684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2684 node2684Labels = Sparse.eval nodeValue2684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2684) = mixedMoment B node2684 node2684Labels := rfl
  simpa [nodeValue2684, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2741 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2741 node2741Labels = 0 := by
  exact mixedMoment_order_one B hB node2741 node2741Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2741 node2741Labels = Sparse.eval nodeValue2741 (mixedVector B) := by
  simpa only [nodeValue2741, Sparse.eval_nil] using zero2741 B _hB _hF

theorem sound2746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2746 node2746Labels = Sparse.eval nodeValue2746 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2746) = mixedMoment B node2746 node2746Labels := rfl
  simpa [nodeValue2746, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2878 node2878Labels = Sparse.eval nodeValue2878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2878) = mixedMoment B node2878 node2878Labels := rfl
  simpa [nodeValue2878, Sparse.eval] using hc.symm

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

theorem sound2881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2881 node2881Labels = Sparse.eval nodeValue2881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2881) = mixedMoment B node2881 node2881Labels := rfl
  simpa [nodeValue2881, Sparse.eval] using hc.symm

theorem sound2882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2882 node2882Labels = Sparse.eval nodeValue2882 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2882) = mixedMoment B node2882 node2882Labels := rfl
  simpa [nodeValue2882, Sparse.eval] using hc.symm

theorem sound2885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2885 node2885Labels = Sparse.eval nodeValue2885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2885) = mixedMoment B node2885 node2885Labels := rfl
  simpa [nodeValue2885, Sparse.eval] using hc.symm

theorem sound2926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2926 node2926Labels = Sparse.eval nodeValue2926 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2926) = mixedMoment B node2926 node2926Labels := rfl
  simpa [nodeValue2926, Sparse.eval] using hc.symm

theorem sound2929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2929 node2929Labels = Sparse.eval nodeValue2929 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2929) = mixedMoment B node2929 node2929Labels := rfl
  simpa [nodeValue2929, Sparse.eval] using hc.symm

theorem sound2930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2930 node2930Labels = Sparse.eval nodeValue2930 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2930) = mixedMoment B node2930 node2930Labels := rfl
  simpa [nodeValue2930, Sparse.eval] using hc.symm

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

theorem sound2956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2956 node2956Labels = Sparse.eval nodeValue2956 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2956) = mixedMoment B node2956 node2956Labels := rfl
  simpa [nodeValue2956, Sparse.eval] using hc.symm

theorem sound2974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2974 node2974Labels = Sparse.eval nodeValue2974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2974) = mixedMoment B node2974 node2974Labels := rfl
  simpa [nodeValue2974, Sparse.eval] using hc.symm

theorem sound2975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2975 node2975Labels = Sparse.eval nodeValue2975 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2975) = mixedMoment B node2975 node2975Labels := rfl
  simpa [nodeValue2975, Sparse.eval] using hc.symm

theorem sound2976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2976 node2976Labels = Sparse.eval nodeValue2976 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2976) = mixedMoment B node2976 node2976Labels := rfl
  simpa [nodeValue2976, Sparse.eval] using hc.symm

theorem sound2977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2977 node2977Labels = Sparse.eval nodeValue2977 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2977) = mixedMoment B node2977 node2977Labels := rfl
  simpa [nodeValue2977, Sparse.eval] using hc.symm

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

theorem sound3023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3023 node3023Labels = Sparse.eval nodeValue3023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3023) = mixedMoment B node3023 node3023Labels := rfl
  simpa [nodeValue3023, Sparse.eval] using hc.symm

theorem sound3037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3037 node3037Labels = Sparse.eval nodeValue3037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3037) = mixedMoment B node3037 node3037Labels := rfl
  simpa [nodeValue3037, Sparse.eval] using hc.symm

theorem sound3043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3043 node3043Labels = Sparse.eval nodeValue3043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3043) = mixedMoment B node3043 node3043Labels := rfl
  simpa [nodeValue3043, Sparse.eval] using hc.symm

theorem sound3044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3044 node3044Labels = Sparse.eval nodeValue3044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3044) = mixedMoment B node3044 node3044Labels := rfl
  simpa [nodeValue3044, Sparse.eval] using hc.symm

theorem sound3045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3045 node3045Labels = Sparse.eval nodeValue3045 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3045) = mixedMoment B node3045 node3045Labels := rfl
  simpa [nodeValue3045, Sparse.eval] using hc.symm

theorem sound3051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3051 node3051Labels = Sparse.eval nodeValue3051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3051) = mixedMoment B node3051 node3051Labels := rfl
  simpa [nodeValue3051, Sparse.eval] using hc.symm

theorem sound3053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3053 node3053Labels = Sparse.eval nodeValue3053 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3053) = mixedMoment B node3053 node3053Labels := rfl
  simpa [nodeValue3053, Sparse.eval] using hc.symm

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

theorem zero3076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3076 node3076Labels = 0 := by
  exact mixedMoment_alpha B hF node3076 node3076Labels 2 permutation152
    (by decide +kernel)

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

theorem sound3076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3076 node3076Labels = Sparse.eval nodeValue3076 (mixedVector B) := by
  simpa only [nodeValue3076, Sparse.eval_nil] using zero3076 B _hB _hF

theorem sound3079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3079 node3079Labels = Sparse.eval nodeValue3079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3079) = mixedMoment B node3079 node3079Labels := rfl
  simpa [nodeValue3079, Sparse.eval] using hc.symm

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

theorem sound3149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3149 node3149Labels = Sparse.eval nodeValue3149 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3149) = mixedMoment B node3149 node3149Labels := rfl
  simpa [nodeValue3149, Sparse.eval] using hc.symm

theorem sound3152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3152 node3152Labels = Sparse.eval nodeValue3152 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3152) = mixedMoment B node3152 node3152Labels := rfl
  simpa [nodeValue3152, Sparse.eval] using hc.symm

theorem sound3158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3158 node3158Labels = Sparse.eval nodeValue3158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3158) = mixedMoment B node3158 node3158Labels := rfl
  simpa [nodeValue3158, Sparse.eval] using hc.symm

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

theorem sound3221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3221 node3221Labels = Sparse.eval nodeValue3221 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3221) = mixedMoment B node3221 node3221Labels := rfl
  simpa [nodeValue3221, Sparse.eval] using hc.symm

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

theorem sound3376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3376 node3376Labels = Sparse.eval nodeValue3376 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3376) = mixedMoment B node3376 node3376Labels := rfl
  simpa [nodeValue3376, Sparse.eval] using hc.symm

theorem sound3380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3380 node3380Labels = Sparse.eval nodeValue3380 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3380) = mixedMoment B node3380 node3380Labels := rfl
  simpa [nodeValue3380, Sparse.eval] using hc.symm

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

theorem sound3394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3394 node3394Labels = Sparse.eval nodeValue3394 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3394) = mixedMoment B node3394 node3394Labels := rfl
  simpa [nodeValue3394, Sparse.eval] using hc.symm

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

theorem sound3505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3505 node3505Labels = Sparse.eval nodeValue3505 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3505) = mixedMoment B node3505 node3505Labels := rfl
  simpa [nodeValue3505, Sparse.eval] using hc.symm

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

theorem sound3551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3551 node3551Labels = Sparse.eval nodeValue3551 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3551) = mixedMoment B node3551 node3551Labels := rfl
  simpa [nodeValue3551, Sparse.eval] using hc.symm

theorem sound3552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3552 node3552Labels = Sparse.eval nodeValue3552 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3552) = mixedMoment B node3552 node3552Labels := rfl
  simpa [nodeValue3552, Sparse.eval] using hc.symm

theorem sound3567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3567 node3567Labels = Sparse.eval nodeValue3567 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3567) = mixedMoment B node3567 node3567Labels := rfl
  simpa [nodeValue3567, Sparse.eval] using hc.symm

theorem sound3571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3571 node3571Labels = Sparse.eval nodeValue3571 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3571) = mixedMoment B node3571 node3571Labels := rfl
  simpa [nodeValue3571, Sparse.eval] using hc.symm

theorem sound3573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3573 node3573Labels = Sparse.eval nodeValue3573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3573) = mixedMoment B node3573 node3573Labels := rfl
  simpa [nodeValue3573, Sparse.eval] using hc.symm

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

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

theorem sound3848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3848 node3848Labels = Sparse.eval nodeValue3848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3848) = mixedMoment B node3848 node3848Labels := rfl
  simpa [nodeValue3848, Sparse.eval] using hc.symm

theorem sound3850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3850 node3850Labels = Sparse.eval nodeValue3850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3850) = mixedMoment B node3850 node3850Labels := rfl
  simpa [nodeValue3850, Sparse.eval] using hc.symm

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

theorem zero3962 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3962 node3962Labels = 0 := by
  exact mixedMoment_order_one B hB node3962 node3962Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3961 node3961Labels = Sparse.eval nodeValue3961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3961) = mixedMoment B node3961 node3961Labels := rfl
  simpa [nodeValue3961, Sparse.eval] using hc.symm

theorem sound3962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3962 node3962Labels = Sparse.eval nodeValue3962 (mixedVector B) := by
  simpa only [nodeValue3962, Sparse.eval_nil] using zero3962 B _hB _hF

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

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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

theorem sound4878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4878 node4878Labels = Sparse.eval nodeValue4878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4878) = mixedMoment B node4878 node4878Labels := rfl
  simpa [nodeValue4878, Sparse.eval] using hc.symm

theorem sound4879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4879 node4879Labels = Sparse.eval nodeValue4879 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4879) = mixedMoment B node4879 node4879Labels := rfl
  simpa [nodeValue4879, Sparse.eval] using hc.symm

theorem sound4885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4885 node4885Labels = Sparse.eval nodeValue4885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4885) = mixedMoment B node4885 node4885Labels := rfl
  simpa [nodeValue4885, Sparse.eval] using hc.symm

theorem sound4886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4886 node4886Labels = Sparse.eval nodeValue4886 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4886) = mixedMoment B node4886 node4886Labels := rfl
  simpa [nodeValue4886, Sparse.eval] using hc.symm

theorem sound4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4889 node4889Labels = Sparse.eval nodeValue4889 (mixedVector B) := by
  have h := singleton4889 B _hB
  rw [sound2245 B _hB _hF, sound2277 B _hB _hF] at h
  norm_num [nodeValue4889, nodeValue2245, nodeValue2277, Sparse.eval] at h ⊢
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

theorem sound5237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5237 node5237Labels = Sparse.eval nodeValue5237 (mixedVector B) := by
  have h := singleton5237 B _hB
  rw [sound2684 B _hB _hF, sound3394 B _hB _hF] at h
  norm_num [nodeValue5237, nodeValue2684, nodeValue3394, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5273 node5273Labels = 0 := by
  exact mixedMoment_order_one B hB node5273 node5273Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5283 node5283Labels = 0 := by
  exact mixedMoment_alpha B hF node5283 node5283Labels 1 permutation152
    (by decide +kernel)

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

theorem sound5265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5265 node5265Labels = Sparse.eval nodeValue5265 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5265) = mixedMoment B node5265 node5265Labels := rfl
  simpa [nodeValue5265, Sparse.eval] using hc.symm

theorem sound5273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5273 node5273Labels = Sparse.eval nodeValue5273 (mixedVector B) := by
  simpa only [nodeValue5273, Sparse.eval_nil] using zero5273 B _hB _hF

theorem sound5283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5283 node5283Labels = Sparse.eval nodeValue5283 (mixedVector B) := by
  simpa only [nodeValue5283, Sparse.eval_nil] using zero5283 B _hB _hF

theorem sound5286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5286 node5286Labels = Sparse.eval nodeValue5286 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5286) = mixedMoment B node5286 node5286Labels := rfl
  simpa [nodeValue5286, Sparse.eval] using hc.symm

theorem sound5299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5299 node5299Labels = Sparse.eval nodeValue5299 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5299) = mixedMoment B node5299 node5299Labels := rfl
  simpa [nodeValue5299, Sparse.eval] using hc.symm

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

theorem sourceEq774 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm774 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA774 + difference 0 1) (sourceB774 + difference 1 0) sourceC774) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA774 + difference 0 1) (sourceB774 + difference 1 0) sourceC774) = raw12856 := by
      apply Matrix.ext; unfold tripleCharges sourceA774 sourceB774 sourceC774 difference raw12856; decide +kernel
    rw [ha]
    exact (canonical12856 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA774 + difference 1 1) (sourceB774 + difference 1 1) sourceC774) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA774 + difference 1 1) (sourceB774 + difference 1 1) sourceC774) = raw12855 := by
      apply Matrix.ext; unfold tripleCharges sourceA774 sourceB774 sourceC774 difference raw12855; decide +kernel
    rw [ha]
    exact (canonical12855 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA774 + difference 2 1) (sourceB774 + difference 1 2) sourceC774) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2571) := by
    have ha : (tripleCharges (sourceA774 + difference 2 1) (sourceB774 + difference 1 2) sourceC774) = raw12871 := by
      apply Matrix.ext; unfold tripleCharges sourceA774 sourceB774 sourceC774 difference raw12871; decide +kernel
    rw [ha]
    exact (canonical12871 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA774 + difference 3 1) (sourceB774 + difference 1 3) sourceC774) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA774 + difference 3 1) (sourceB774 + difference 1 3) sourceC774) = raw12872 := by
      apply Matrix.ext; unfold tripleCharges sourceA774 sourceB774 sourceC774 difference raw12872; decide +kernel
    rw [ha]
    exact (canonical12872 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA774 + difference 4 1) (sourceB774 + difference 1 4) sourceC774) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2975) := by
    have ha : (tripleCharges (sourceA774 + difference 4 1) (sourceB774 + difference 1 4) sourceC774) = raw12873 := by
      apply Matrix.ext; unfold tripleCharges sourceA774 sourceB774 sourceC774 difference raw12873; decide +kernel
    rw [ha]
    exact (canonical12873 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA774 + difference 5 1) (sourceB774 + difference 1 5) sourceC774) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2977) := by
    have ha : (tripleCharges (sourceA774 + difference 5 1) (sourceB774 + difference 1 5) sourceC774) = raw12874 := by
      apply Matrix.ext; unfold tripleCharges sourceA774 sourceB774 sourceC774 difference raw12874; decide +kernel
    rw [ha]
    exact (canonical12874 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA774 + sourceB774) sourceC774) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA774 + sourceB774) sourceC774) = raw12861 := by
      apply Matrix.ext; unfold doubleCharges sourceA774 sourceB774 sourceC774 raw12861; decide +kernel
    rw [ha]
    exact (canonical12861 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA774 sourceB774 sourceC774
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm774, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq775 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm775 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA775 + difference 0 2) (sourceB775 + difference 2 0) sourceC775) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA775 + difference 0 2) (sourceB775 + difference 2 0) sourceC775) = raw12857 := by
      apply Matrix.ext; unfold tripleCharges sourceA775 sourceB775 sourceC775 difference raw12857; decide +kernel
    rw [ha]
    exact (canonical12857 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA775 + difference 1 2) (sourceB775 + difference 2 1) sourceC775) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2878) := by
    have ha : (tripleCharges (sourceA775 + difference 1 2) (sourceB775 + difference 2 1) sourceC775) = raw12867 := by
      apply Matrix.ext; unfold tripleCharges sourceA775 sourceB775 sourceC775 difference raw12867; decide +kernel
    rw [ha]
    exact (canonical12867 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA775 + difference 2 2) (sourceB775 + difference 2 2) sourceC775) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA775 + difference 2 2) (sourceB775 + difference 2 2) sourceC775) = raw12855 := by
      apply Matrix.ext; unfold tripleCharges sourceA775 sourceB775 sourceC775 difference raw12855; decide +kernel
    rw [ha]
    exact (canonical12855 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA775 + difference 3 2) (sourceB775 + difference 2 3) sourceC775) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA775 + difference 3 2) (sourceB775 + difference 2 3) sourceC775) = raw12875 := by
      apply Matrix.ext; unfold tripleCharges sourceA775 sourceB775 sourceC775 difference raw12875; decide +kernel
    rw [ha]
    exact (canonical12875 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA775 + difference 4 2) (sourceB775 + difference 2 4) sourceC775) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA775 + difference 4 2) (sourceB775 + difference 2 4) sourceC775) = raw12876 := by
      apply Matrix.ext; unfold tripleCharges sourceA775 sourceB775 sourceC775 difference raw12876; decide +kernel
    rw [ha]
    exact (canonical12876 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA775 + difference 5 2) (sourceB775 + difference 2 5) sourceC775) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2885) := by
    have ha : (tripleCharges (sourceA775 + difference 5 2) (sourceB775 + difference 2 5) sourceC775) = raw12877 := by
      apply Matrix.ext; unfold tripleCharges sourceA775 sourceB775 sourceC775 difference raw12877; decide +kernel
    rw [ha]
    exact (canonical12877 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA775 + sourceB775) sourceC775) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA775 + sourceB775) sourceC775) = raw12861 := by
      apply Matrix.ext; unfold doubleCharges sourceA775 sourceB775 sourceC775 raw12861; decide +kernel
    rw [ha]
    exact (canonical12861 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA775 sourceB775 sourceC775
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm775, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq776 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm776 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA776 + difference 0 3) (sourceB776 + difference 3 0) sourceC776) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA776 + difference 0 3) (sourceB776 + difference 3 0) sourceC776) = raw12858 := by
      apply Matrix.ext; unfold tripleCharges sourceA776 sourceB776 sourceC776 difference raw12858; decide +kernel
    rw [ha]
    exact (canonical12858 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA776 + difference 1 3) (sourceB776 + difference 3 1) sourceC776) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3043) := by
    have ha : (tripleCharges (sourceA776 + difference 1 3) (sourceB776 + difference 3 1) sourceC776) = raw12868 := by
      apply Matrix.ext; unfold tripleCharges sourceA776 sourceB776 sourceC776 difference raw12868; decide +kernel
    rw [ha]
    exact (canonical12868 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA776 + difference 2 3) (sourceB776 + difference 3 2) sourceC776) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2575) := by
    have ha : (tripleCharges (sourceA776 + difference 2 3) (sourceB776 + difference 3 2) sourceC776) = raw12878 := by
      apply Matrix.ext; unfold tripleCharges sourceA776 sourceB776 sourceC776 difference raw12878; decide +kernel
    rw [ha]
    exact (canonical12878 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA776 + difference 3 3) (sourceB776 + difference 3 3) sourceC776) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA776 + difference 3 3) (sourceB776 + difference 3 3) sourceC776) = raw12855 := by
      apply Matrix.ext; unfold tripleCharges sourceA776 sourceB776 sourceC776 difference raw12855; decide +kernel
    rw [ha]
    exact (canonical12855 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA776 + difference 4 3) (sourceB776 + difference 3 4) sourceC776) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3044) := by
    have ha : (tripleCharges (sourceA776 + difference 4 3) (sourceB776 + difference 3 4) sourceC776) = raw12879 := by
      apply Matrix.ext; unfold tripleCharges sourceA776 sourceB776 sourceC776 difference raw12879; decide +kernel
    rw [ha]
    exact (canonical12879 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA776 + difference 5 3) (sourceB776 + difference 3 5) sourceC776) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3045) := by
    have ha : (tripleCharges (sourceA776 + difference 5 3) (sourceB776 + difference 3 5) sourceC776) = raw12880 := by
      apply Matrix.ext; unfold tripleCharges sourceA776 sourceB776 sourceC776 difference raw12880; decide +kernel
    rw [ha]
    exact (canonical12880 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA776 + sourceB776) sourceC776) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA776 + sourceB776) sourceC776) = raw12861 := by
      apply Matrix.ext; unfold doubleCharges sourceA776 sourceB776 sourceC776 raw12861; decide +kernel
    rw [ha]
    exact (canonical12861 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA776 sourceB776 sourceC776
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm776, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq780 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm780 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA780 + difference 0 0) (sourceB780 + difference 0 0) sourceC780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA780 + difference 0 0) (sourceB780 + difference 0 0) sourceC780) = raw12078 := by
      apply Matrix.ext; unfold tripleCharges sourceA780 sourceB780 sourceC780 difference raw12078; decide +kernel
    rw [ha]
    exact (canonical12078 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA780 + difference 0 1) (sourceB780 + difference 1 0) sourceC780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA780 + difference 0 1) (sourceB780 + difference 1 0) sourceC780) = raw12065 := by
      apply Matrix.ext; unfold tripleCharges sourceA780 sourceB780 sourceC780 difference raw12065; decide +kernel
    rw [ha]
    exact (canonical12065 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA780 + difference 0 2) (sourceB780 + difference 2 0) sourceC780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA780 + difference 0 2) (sourceB780 + difference 2 0) sourceC780) = raw12515 := by
      apply Matrix.ext; unfold tripleCharges sourceA780 sourceB780 sourceC780 difference raw12515; decide +kernel
    rw [ha]
    exact (canonical12515 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA780 + difference 0 3) (sourceB780 + difference 3 0) sourceC780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA780 + difference 0 3) (sourceB780 + difference 3 0) sourceC780) = raw12923 := by
      apply Matrix.ext; unfold tripleCharges sourceA780 sourceB780 sourceC780 difference raw12923; decide +kernel
    rw [ha]
    exact (canonical12923 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA780 + difference 0 4) (sourceB780 + difference 4 0) sourceC780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3380) := by
    have ha : (tripleCharges (sourceA780 + difference 0 4) (sourceB780 + difference 4 0) sourceC780) = raw12924 := by
      apply Matrix.ext; unfold tripleCharges sourceA780 sourceB780 sourceC780 difference raw12924; decide +kernel
    rw [ha]
    exact (canonical12924 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA780 + difference 0 5) (sourceB780 + difference 5 0) sourceC780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3394) := by
    have ha : (tripleCharges (sourceA780 + difference 0 5) (sourceB780 + difference 5 0) sourceC780) = raw12925 := by
      apply Matrix.ext; unfold tripleCharges sourceA780 sourceB780 sourceC780 difference raw12925; decide +kernel
    rw [ha]
    exact (canonical12925 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA780 + sourceB780) sourceC780) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA780 + sourceB780) sourceC780) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA780 sourceB780 sourceC780 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA780 sourceB780 sourceC780
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm780, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq781 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm781 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA781 + difference 1 0) (sourceB781 + difference 0 1) sourceC781) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA781 + difference 1 0) (sourceB781 + difference 0 1) sourceC781) = raw12926 := by
      apply Matrix.ext; unfold tripleCharges sourceA781 sourceB781 sourceC781 difference raw12926; decide +kernel
    rw [ha]
    exact (canonical12926 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA781 + difference 1 1) (sourceB781 + difference 1 1) sourceC781) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA781 + difference 1 1) (sourceB781 + difference 1 1) sourceC781) = raw12078 := by
      apply Matrix.ext; unfold tripleCharges sourceA781 sourceB781 sourceC781 difference raw12078; decide +kernel
    rw [ha]
    exact (canonical12078 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA781 + difference 1 2) (sourceB781 + difference 2 1) sourceC781) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA781 + difference 1 2) (sourceB781 + difference 2 1) sourceC781) = raw12520 := by
      apply Matrix.ext; unfold tripleCharges sourceA781 sourceB781 sourceC781 difference raw12520; decide +kernel
    rw [ha]
    exact (canonical12520 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA781 + difference 1 3) (sourceB781 + difference 3 1) sourceC781) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2926) := by
    have ha : (tripleCharges (sourceA781 + difference 1 3) (sourceB781 + difference 3 1) sourceC781) = raw12927 := by
      apply Matrix.ext; unfold tripleCharges sourceA781 sourceB781 sourceC781 difference raw12927; decide +kernel
    rw [ha]
    exact (canonical12927 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA781 + difference 1 4) (sourceB781 + difference 4 1) sourceC781) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3551) := by
    have ha : (tripleCharges (sourceA781 + difference 1 4) (sourceB781 + difference 4 1) sourceC781) = raw12928 := by
      apply Matrix.ext; unfold tripleCharges sourceA781 sourceB781 sourceC781 difference raw12928; decide +kernel
    rw [ha]
    exact (canonical12928 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA781 + difference 1 5) (sourceB781 + difference 5 1) sourceC781) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3567) := by
    have ha : (tripleCharges (sourceA781 + difference 1 5) (sourceB781 + difference 5 1) sourceC781) = raw12929 := by
      apply Matrix.ext; unfold tripleCharges sourceA781 sourceB781 sourceC781 difference raw12929; decide +kernel
    rw [ha]
    exact (canonical12929 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA781 + sourceB781) sourceC781) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA781 + sourceB781) sourceC781) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA781 sourceB781 sourceC781 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA781 sourceB781 sourceC781
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm781, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq782 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm782 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA782 + difference 2 0) (sourceB782 + difference 0 2) sourceC782) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA782 + difference 2 0) (sourceB782 + difference 0 2) sourceC782) = raw12930 := by
      apply Matrix.ext; unfold tripleCharges sourceA782 sourceB782 sourceC782 difference raw12930; decide +kernel
    rw [ha]
    exact (canonical12930 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA782 + difference 2 1) (sourceB782 + difference 1 2) sourceC782) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3149) := by
    have ha : (tripleCharges (sourceA782 + difference 2 1) (sourceB782 + difference 1 2) sourceC782) = raw12072 := by
      apply Matrix.ext; unfold tripleCharges sourceA782 sourceB782 sourceC782 difference raw12072; decide +kernel
    rw [ha]
    exact (canonical12072 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA782 + difference 2 2) (sourceB782 + difference 2 2) sourceC782) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA782 + difference 2 2) (sourceB782 + difference 2 2) sourceC782) = raw12078 := by
      apply Matrix.ext; unfold tripleCharges sourceA782 sourceB782 sourceC782 difference raw12078; decide +kernel
    rw [ha]
    exact (canonical12078 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA782 + difference 2 3) (sourceB782 + difference 3 2) sourceC782) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2929) := by
    have ha : (tripleCharges (sourceA782 + difference 2 3) (sourceB782 + difference 3 2) sourceC782) = raw12931 := by
      apply Matrix.ext; unfold tripleCharges sourceA782 sourceB782 sourceC782 difference raw12931; decide +kernel
    rw [ha]
    exact (canonical12931 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA782 + difference 2 4) (sourceB782 + difference 4 2) sourceC782) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3152) := by
    have ha : (tripleCharges (sourceA782 + difference 2 4) (sourceB782 + difference 4 2) sourceC782) = raw12932 := by
      apply Matrix.ext; unfold tripleCharges sourceA782 sourceB782 sourceC782 difference raw12932; decide +kernel
    rw [ha]
    exact (canonical12932 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA782 + difference 2 5) (sourceB782 + difference 5 2) sourceC782) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA782 + difference 2 5) (sourceB782 + difference 5 2) sourceC782) = raw12933 := by
      apply Matrix.ext; unfold tripleCharges sourceA782 sourceB782 sourceC782 difference raw12933; decide +kernel
    rw [ha]
    exact (canonical12933 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA782 + sourceB782) sourceC782) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA782 + sourceB782) sourceC782) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA782 sourceB782 sourceC782 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA782 sourceB782 sourceC782
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm782, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq783 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm783 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA783 + difference 0 3) (sourceB783 + difference 3 0) sourceC783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA783 + difference 0 3) (sourceB783 + difference 3 0) sourceC783) = raw12923 := by
      apply Matrix.ext; unfold tripleCharges sourceA783 sourceB783 sourceC783 difference raw12923; decide +kernel
    rw [ha]
    exact (canonical12923 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA783 + difference 1 3) (sourceB783 + difference 3 1) sourceC783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2926) := by
    have ha : (tripleCharges (sourceA783 + difference 1 3) (sourceB783 + difference 3 1) sourceC783) = raw12927 := by
      apply Matrix.ext; unfold tripleCharges sourceA783 sourceB783 sourceC783 difference raw12927; decide +kernel
    rw [ha]
    exact (canonical12927 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA783 + difference 2 3) (sourceB783 + difference 3 2) sourceC783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2929) := by
    have ha : (tripleCharges (sourceA783 + difference 2 3) (sourceB783 + difference 3 2) sourceC783) = raw12931 := by
      apply Matrix.ext; unfold tripleCharges sourceA783 sourceB783 sourceC783 difference raw12931; decide +kernel
    rw [ha]
    exact (canonical12931 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA783 + difference 3 3) (sourceB783 + difference 3 3) sourceC783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA783 + difference 3 3) (sourceB783 + difference 3 3) sourceC783) = raw12078 := by
      apply Matrix.ext; unfold tripleCharges sourceA783 sourceB783 sourceC783 difference raw12078; decide +kernel
    rw [ha]
    exact (canonical12078 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA783 + difference 4 3) (sourceB783 + difference 3 4) sourceC783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3079) := by
    have ha : (tripleCharges (sourceA783 + difference 4 3) (sourceB783 + difference 3 4) sourceC783) = raw12934 := by
      apply Matrix.ext; unfold tripleCharges sourceA783 sourceB783 sourceC783 difference raw12934; decide +kernel
    rw [ha]
    exact (canonical12934 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA783 + difference 5 3) (sourceB783 + difference 3 5) sourceC783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2956) := by
    have ha : (tripleCharges (sourceA783 + difference 5 3) (sourceB783 + difference 3 5) sourceC783) = raw12522 := by
      apply Matrix.ext; unfold tripleCharges sourceA783 sourceB783 sourceC783 difference raw12522; decide +kernel
    rw [ha]
    exact (canonical12522 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA783 + sourceB783) sourceC783) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA783 + sourceB783) sourceC783) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA783 sourceB783 sourceC783 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA783 sourceB783 sourceC783
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm783, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq784 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm784 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA784 + difference 4 0) (sourceB784 + difference 0 4) sourceC784) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA784 + difference 4 0) (sourceB784 + difference 0 4) sourceC784) = raw12935 := by
      apply Matrix.ext; unfold tripleCharges sourceA784 sourceB784 sourceC784 difference raw12935; decide +kernel
    rw [ha]
    exact (canonical12935 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA784 + difference 4 1) (sourceB784 + difference 1 4) sourceC784) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3505) := by
    have ha : (tripleCharges (sourceA784 + difference 4 1) (sourceB784 + difference 1 4) sourceC784) = raw12079 := by
      apply Matrix.ext; unfold tripleCharges sourceA784 sourceB784 sourceC784 difference raw12079; decide +kernel
    rw [ha]
    exact (canonical12079 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA784 + difference 4 2) (sourceB784 + difference 2 4) sourceC784) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA784 + difference 4 2) (sourceB784 + difference 2 4) sourceC784) = raw12528 := by
      apply Matrix.ext; unfold tripleCharges sourceA784 sourceB784 sourceC784 difference raw12528; decide +kernel
    rw [ha]
    exact (canonical12528 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA784 + difference 4 3) (sourceB784 + difference 3 4) sourceC784) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3079) := by
    have ha : (tripleCharges (sourceA784 + difference 4 3) (sourceB784 + difference 3 4) sourceC784) = raw12934 := by
      apply Matrix.ext; unfold tripleCharges sourceA784 sourceB784 sourceC784 difference raw12934; decide +kernel
    rw [ha]
    exact (canonical12934 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA784 + difference 4 4) (sourceB784 + difference 4 4) sourceC784) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA784 + difference 4 4) (sourceB784 + difference 4 4) sourceC784) = raw12078 := by
      apply Matrix.ext; unfold tripleCharges sourceA784 sourceB784 sourceC784 difference raw12078; decide +kernel
    rw [ha]
    exact (canonical12078 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA784 + difference 4 5) (sourceB784 + difference 5 4) sourceC784) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA784 + difference 4 5) (sourceB784 + difference 5 4) sourceC784) = raw12936 := by
      apply Matrix.ext; unfold tripleCharges sourceA784 sourceB784 sourceC784 difference raw12936; decide +kernel
    rw [ha]
    exact (canonical12936 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA784 + sourceB784) sourceC784) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA784 + sourceB784) sourceC784) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA784 sourceB784 sourceC784 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA784 sourceB784 sourceC784
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm784, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq785 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm785 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA785 + difference 0 4) (sourceB785 + difference 4 0) sourceC785) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3380) := by
    have ha : (tripleCharges (sourceA785 + difference 0 4) (sourceB785 + difference 4 0) sourceC785) = raw12924 := by
      apply Matrix.ext; unfold tripleCharges sourceA785 sourceB785 sourceC785 difference raw12924; decide +kernel
    rw [ha]
    exact (canonical12924 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA785 + difference 1 4) (sourceB785 + difference 4 1) sourceC785) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3551) := by
    have ha : (tripleCharges (sourceA785 + difference 1 4) (sourceB785 + difference 4 1) sourceC785) = raw12928 := by
      apply Matrix.ext; unfold tripleCharges sourceA785 sourceB785 sourceC785 difference raw12928; decide +kernel
    rw [ha]
    exact (canonical12928 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA785 + difference 2 4) (sourceB785 + difference 4 2) sourceC785) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3152) := by
    have ha : (tripleCharges (sourceA785 + difference 2 4) (sourceB785 + difference 4 2) sourceC785) = raw12932 := by
      apply Matrix.ext; unfold tripleCharges sourceA785 sourceB785 sourceC785 difference raw12932; decide +kernel
    rw [ha]
    exact (canonical12932 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA785 + difference 3 4) (sourceB785 + difference 4 3) sourceC785) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA785 + difference 3 4) (sourceB785 + difference 4 3) sourceC785) = raw12937 := by
      apply Matrix.ext; unfold tripleCharges sourceA785 sourceB785 sourceC785 difference raw12937; decide +kernel
    rw [ha]
    exact (canonical12937 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA785 + difference 4 4) (sourceB785 + difference 4 4) sourceC785) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA785 + difference 4 4) (sourceB785 + difference 4 4) sourceC785) = raw12078 := by
      apply Matrix.ext; unfold tripleCharges sourceA785 sourceB785 sourceC785 difference raw12078; decide +kernel
    rw [ha]
    exact (canonical12078 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA785 + difference 5 4) (sourceB785 + difference 4 5) sourceC785) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3552) := by
    have ha : (tripleCharges (sourceA785 + difference 5 4) (sourceB785 + difference 4 5) sourceC785) = raw12523 := by
      apply Matrix.ext; unfold tripleCharges sourceA785 sourceB785 sourceC785 difference raw12523; decide +kernel
    rw [ha]
    exact (canonical12523 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA785 + sourceB785) sourceC785) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA785 + sourceB785) sourceC785) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA785 sourceB785 sourceC785 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA785 sourceB785 sourceC785
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm785, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq790 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm790 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA790 + difference 0 0) (sourceB790 + difference 0 0) sourceC790) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA790 + difference 0 0) (sourceB790 + difference 0 0) sourceC790) = raw13058 := by
      apply Matrix.ext; unfold tripleCharges sourceA790 sourceB790 sourceC790 difference raw13058; decide +kernel
    rw [ha]
    exact (canonical13058 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA790 + difference 0 1) (sourceB790 + difference 1 0) sourceC790) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3909) := by
    have ha : (tripleCharges (sourceA790 + difference 0 1) (sourceB790 + difference 1 0) sourceC790) = raw13059 := by
      apply Matrix.ext; unfold tripleCharges sourceA790 sourceB790 sourceC790 difference raw13059; decide +kernel
    rw [ha]
    exact (canonical13059 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA790 + difference 0 2) (sourceB790 + difference 2 0) sourceC790) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3962) := by
    have ha : (tripleCharges (sourceA790 + difference 0 2) (sourceB790 + difference 2 0) sourceC790) = raw13060 := by
      apply Matrix.ext; unfold tripleCharges sourceA790 sourceB790 sourceC790 difference raw13060; decide +kernel
    rw [ha]
    exact (canonical13060 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA790 + difference 0 3) (sourceB790 + difference 3 0) sourceC790) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA790 + difference 0 3) (sourceB790 + difference 3 0) sourceC790) = raw13061 := by
      apply Matrix.ext; unfold tripleCharges sourceA790 sourceB790 sourceC790 difference raw13061; decide +kernel
    rw [ha]
    exact (canonical13061 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA790 + difference 0 4) (sourceB790 + difference 4 0) sourceC790) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA790 + difference 0 4) (sourceB790 + difference 4 0) sourceC790) = raw13062 := by
      apply Matrix.ext; unfold tripleCharges sourceA790 sourceB790 sourceC790 difference raw13062; decide +kernel
    rw [ha]
    exact (canonical13062 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA790 + difference 0 5) (sourceB790 + difference 5 0) sourceC790) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA790 + difference 0 5) (sourceB790 + difference 5 0) sourceC790) = raw13063 := by
      apply Matrix.ext; unfold tripleCharges sourceA790 sourceB790 sourceC790 difference raw13063; decide +kernel
    rw [ha]
    exact (canonical13063 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA790 + sourceB790) sourceC790) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA790 + sourceB790) sourceC790) = raw13064 := by
      apply Matrix.ext; unfold doubleCharges sourceA790 sourceB790 sourceC790 raw13064; decide +kernel
    rw [ha]
    exact (canonical13064 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA790 sourceB790 sourceC790
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm790, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq791 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm791 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA791 + difference 0 1) (sourceB791 + difference 1 0) sourceC791) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3909) := by
    have ha : (tripleCharges (sourceA791 + difference 0 1) (sourceB791 + difference 1 0) sourceC791) = raw13059 := by
      apply Matrix.ext; unfold tripleCharges sourceA791 sourceB791 sourceC791 difference raw13059; decide +kernel
    rw [ha]
    exact (canonical13059 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA791 + difference 1 1) (sourceB791 + difference 1 1) sourceC791) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA791 + difference 1 1) (sourceB791 + difference 1 1) sourceC791) = raw13058 := by
      apply Matrix.ext; unfold tripleCharges sourceA791 sourceB791 sourceC791 difference raw13058; decide +kernel
    rw [ha]
    exact (canonical13058 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA791 + difference 2 1) (sourceB791 + difference 1 2) sourceC791) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2746) := by
    have ha : (tripleCharges (sourceA791 + difference 2 1) (sourceB791 + difference 1 2) sourceC791) = raw13065 := by
      apply Matrix.ext; unfold tripleCharges sourceA791 sourceB791 sourceC791 difference raw13065; decide +kernel
    rw [ha]
    exact (canonical13065 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA791 + difference 3 1) (sourceB791 + difference 1 3) sourceC791) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA791 + difference 3 1) (sourceB791 + difference 1 3) sourceC791) = raw13066 := by
      apply Matrix.ext; unfold tripleCharges sourceA791 sourceB791 sourceC791 difference raw13066; decide +kernel
    rw [ha]
    exact (canonical13066 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA791 + difference 4 1) (sourceB791 + difference 1 4) sourceC791) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA791 + difference 4 1) (sourceB791 + difference 1 4) sourceC791) = raw13067 := by
      apply Matrix.ext; unfold tripleCharges sourceA791 sourceB791 sourceC791 difference raw13067; decide +kernel
    rw [ha]
    exact (canonical13067 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA791 + difference 5 1) (sourceB791 + difference 1 5) sourceC791) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA791 + difference 5 1) (sourceB791 + difference 1 5) sourceC791) = raw13068 := by
      apply Matrix.ext; unfold tripleCharges sourceA791 sourceB791 sourceC791 difference raw13068; decide +kernel
    rw [ha]
    exact (canonical13068 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA791 + sourceB791) sourceC791) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA791 + sourceB791) sourceC791) = raw13064 := by
      apply Matrix.ext; unfold doubleCharges sourceA791 sourceB791 sourceC791 raw13064; decide +kernel
    rw [ha]
    exact (canonical13064 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA791 sourceB791 sourceC791
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm791, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq792 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm792 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA792 + difference 0 1) (sourceB792 + difference 1 0) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5227) := by
    have ha : (tripleCharges (sourceA792 + difference 0 1) (sourceB792 + difference 1 0) sourceC792) = raw12001 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12001; decide +kernel
    rw [ha]
    exact (canonical12001 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA792 + difference 0 2) (sourceB792 + difference 2 0) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA792 + difference 0 2) (sourceB792 + difference 2 0) sourceC792) = raw12652 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12652; decide +kernel
    rw [ha]
    exact (canonical12652 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA792 + difference 0 3) (sourceB792 + difference 3 0) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA792 + difference 0 3) (sourceB792 + difference 3 0) sourceC792) = raw12883 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12883; decide +kernel
    rw [ha]
    exact (canonical12883 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA792 + difference 0 4) (sourceB792 + difference 4 0) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA792 + difference 0 4) (sourceB792 + difference 4 0) sourceC792) = raw13069 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13069; decide +kernel
    rw [ha]
    exact (canonical13069 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA792 + difference 0 5) (sourceB792 + difference 5 0) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA792 + difference 0 5) (sourceB792 + difference 5 0) sourceC792) = raw13070 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13070; decide +kernel
    rw [ha]
    exact (canonical13070 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA792 + difference 1 0) (sourceB792 + difference 0 1) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA792 + difference 1 0) (sourceB792 + difference 0 1) sourceC792) = raw13071 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13071; decide +kernel
    rw [ha]
    exact (canonical13071 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA792 + difference 1 2) (sourceB792 + difference 2 1) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5283) := by
    have ha : (tripleCharges (sourceA792 + difference 1 2) (sourceB792 + difference 2 1) sourceC792) = raw12655 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12655; decide +kernel
    rw [ha]
    exact (canonical12655 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA792 + difference 1 3) (sourceB792 + difference 3 1) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA792 + difference 1 3) (sourceB792 + difference 3 1) sourceC792) = raw12887 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12887; decide +kernel
    rw [ha]
    exact (canonical12887 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA792 + difference 1 4) (sourceB792 + difference 4 1) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA792 + difference 1 4) (sourceB792 + difference 4 1) sourceC792) = raw13072 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13072; decide +kernel
    rw [ha]
    exact (canonical13072 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA792 + difference 1 5) (sourceB792 + difference 5 1) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA792 + difference 1 5) (sourceB792 + difference 5 1) sourceC792) = raw13073 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13073; decide +kernel
    rw [ha]
    exact (canonical13073 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA792 + difference 2 0) (sourceB792 + difference 0 2) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4886) := by
    have ha : (tripleCharges (sourceA792 + difference 2 0) (sourceB792 + difference 0 2) sourceC792) = raw13074 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13074; decide +kernel
    rw [ha]
    exact (canonical13074 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA792 + difference 2 1) (sourceB792 + difference 1 2) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4878) := by
    have ha : (tripleCharges (sourceA792 + difference 2 1) (sourceB792 + difference 1 2) sourceC792) = raw12010 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12010; decide +kernel
    rw [ha]
    exact (canonical12010 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA792 + difference 2 3) (sourceB792 + difference 3 2) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA792 + difference 2 3) (sourceB792 + difference 3 2) sourceC792) = raw12891 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12891; decide +kernel
    rw [ha]
    exact (canonical12891 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA792 + difference 2 4) (sourceB792 + difference 4 2) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA792 + difference 2 4) (sourceB792 + difference 4 2) sourceC792) = raw13075 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13075; decide +kernel
    rw [ha]
    exact (canonical13075 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA792 + difference 2 5) (sourceB792 + difference 5 2) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA792 + difference 2 5) (sourceB792 + difference 5 2) sourceC792) = raw13076 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13076; decide +kernel
    rw [ha]
    exact (canonical13076 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA792 + difference 3 0) (sourceB792 + difference 0 3) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA792 + difference 3 0) (sourceB792 + difference 0 3) sourceC792) = raw13077 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13077; decide +kernel
    rw [ha]
    exact (canonical13077 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA792 + difference 3 1) (sourceB792 + difference 1 3) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA792 + difference 3 1) (sourceB792 + difference 1 3) sourceC792) = raw12014 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12014; decide +kernel
    rw [ha]
    exact (canonical12014 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA792 + difference 3 2) (sourceB792 + difference 2 3) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA792 + difference 3 2) (sourceB792 + difference 2 3) sourceC792) = raw12658 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12658; decide +kernel
    rw [ha]
    exact (canonical12658 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA792 + difference 3 4) (sourceB792 + difference 4 3) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA792 + difference 3 4) (sourceB792 + difference 4 3) sourceC792) = raw13078 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13078; decide +kernel
    rw [ha]
    exact (canonical13078 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA792 + difference 3 5) (sourceB792 + difference 5 3) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA792 + difference 3 5) (sourceB792 + difference 5 3) sourceC792) = raw13079 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13079; decide +kernel
    rw [ha]
    exact (canonical13079 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA792 + difference 4 0) (sourceB792 + difference 0 4) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA792 + difference 4 0) (sourceB792 + difference 0 4) sourceC792) = raw13080 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13080; decide +kernel
    rw [ha]
    exact (canonical13080 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA792 + difference 4 1) (sourceB792 + difference 1 4) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA792 + difference 4 1) (sourceB792 + difference 1 4) sourceC792) = raw12018 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12018; decide +kernel
    rw [ha]
    exact (canonical12018 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA792 + difference 4 2) (sourceB792 + difference 2 4) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA792 + difference 4 2) (sourceB792 + difference 2 4) sourceC792) = raw12660 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12660; decide +kernel
    rw [ha]
    exact (canonical12660 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA792 + difference 4 3) (sourceB792 + difference 3 4) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA792 + difference 4 3) (sourceB792 + difference 3 4) sourceC792) = raw12894 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12894; decide +kernel
    rw [ha]
    exact (canonical12894 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA792 + difference 4 5) (sourceB792 + difference 5 4) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA792 + difference 4 5) (sourceB792 + difference 5 4) sourceC792) = raw13081 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13081; decide +kernel
    rw [ha]
    exact (canonical13081 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA792 + difference 5 0) (sourceB792 + difference 0 5) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA792 + difference 5 0) (sourceB792 + difference 0 5) sourceC792) = raw12002 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12002; decide +kernel
    rw [ha]
    exact (canonical12002 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA792 + difference 5 1) (sourceB792 + difference 1 5) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA792 + difference 5 1) (sourceB792 + difference 1 5) sourceC792) = raw11674 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw11674; decide +kernel
    rw [ha]
    exact (canonical11674 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA792 + difference 5 2) (sourceB792 + difference 2 5) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA792 + difference 5 2) (sourceB792 + difference 2 5) sourceC792) = raw11669 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw11669; decide +kernel
    rw [ha]
    exact (canonical11669 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA792 + difference 5 3) (sourceB792 + difference 3 5) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA792 + difference 5 3) (sourceB792 + difference 3 5) sourceC792) = raw12003 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12003; decide +kernel
    rw [ha]
    exact (canonical12003 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA792 + difference 5 4) (sourceB792 + difference 4 5) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA792 + difference 5 4) (sourceB792 + difference 4 5) sourceC792) = raw12004 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12004; decide +kernel
    rw [ha]
    exact (canonical12004 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA792 sourceB792 sourceC792
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm792, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq793 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm793 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA793 + difference 0 1) (sourceB793 + difference 1 0) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA793 + difference 0 1) (sourceB793 + difference 1 0) sourceC793) = raw12045 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12045; decide +kernel
    rw [ha]
    exact (canonical12045 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA793 + difference 0 2) (sourceB793 + difference 2 0) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA793 + difference 0 2) (sourceB793 + difference 2 0) sourceC793) = raw13082 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13082; decide +kernel
    rw [ha]
    exact (canonical13082 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA793 + difference 0 3) (sourceB793 + difference 3 0) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA793 + difference 0 3) (sourceB793 + difference 3 0) sourceC793) = raw12911 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12911; decide +kernel
    rw [ha]
    exact (canonical12911 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA793 + difference 0 4) (sourceB793 + difference 4 0) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA793 + difference 0 4) (sourceB793 + difference 4 0) sourceC793) = raw13083 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13083; decide +kernel
    rw [ha]
    exact (canonical13083 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA793 + difference 0 5) (sourceB793 + difference 5 0) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA793 + difference 0 5) (sourceB793 + difference 5 0) sourceC793) = raw13084 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13084; decide +kernel
    rw [ha]
    exact (canonical13084 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA793 + difference 1 0) (sourceB793 + difference 0 1) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA793 + difference 1 0) (sourceB793 + difference 0 1) sourceC793) = raw13085 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13085; decide +kernel
    rw [ha]
    exact (canonical13085 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA793 + difference 1 2) (sourceB793 + difference 2 1) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3076) := by
    have ha : (tripleCharges (sourceA793 + difference 1 2) (sourceB793 + difference 2 1) sourceC793) = raw13086 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13086; decide +kernel
    rw [ha]
    exact (canonical13086 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA793 + difference 1 3) (sourceB793 + difference 3 1) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA793 + difference 1 3) (sourceB793 + difference 3 1) sourceC793) = raw12915 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12915; decide +kernel
    rw [ha]
    exact (canonical12915 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA793 + difference 1 4) (sourceB793 + difference 4 1) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA793 + difference 1 4) (sourceB793 + difference 4 1) sourceC793) = raw13087 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13087; decide +kernel
    rw [ha]
    exact (canonical13087 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA793 + difference 1 5) (sourceB793 + difference 5 1) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA793 + difference 1 5) (sourceB793 + difference 5 1) sourceC793) = raw13088 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13088; decide +kernel
    rw [ha]
    exact (canonical13088 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA793 + difference 2 0) (sourceB793 + difference 0 2) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA793 + difference 2 0) (sourceB793 + difference 0 2) sourceC793) = raw13089 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13089; decide +kernel
    rw [ha]
    exact (canonical13089 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA793 + difference 2 1) (sourceB793 + difference 1 2) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA793 + difference 2 1) (sourceB793 + difference 1 2) sourceC793) = raw12054 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12054; decide +kernel
    rw [ha]
    exact (canonical12054 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA793 + difference 2 3) (sourceB793 + difference 3 2) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA793 + difference 2 3) (sourceB793 + difference 3 2) sourceC793) = raw12919 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12919; decide +kernel
    rw [ha]
    exact (canonical12919 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA793 + difference 2 4) (sourceB793 + difference 4 2) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA793 + difference 2 4) (sourceB793 + difference 4 2) sourceC793) = raw13090 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13090; decide +kernel
    rw [ha]
    exact (canonical13090 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA793 + difference 2 5) (sourceB793 + difference 5 2) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA793 + difference 2 5) (sourceB793 + difference 5 2) sourceC793) = raw13091 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13091; decide +kernel
    rw [ha]
    exact (canonical13091 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA793 + difference 3 0) (sourceB793 + difference 0 3) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA793 + difference 3 0) (sourceB793 + difference 0 3) sourceC793) = raw13092 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13092; decide +kernel
    rw [ha]
    exact (canonical13092 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA793 + difference 3 1) (sourceB793 + difference 1 3) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA793 + difference 3 1) (sourceB793 + difference 1 3) sourceC793) = raw12058 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12058; decide +kernel
    rw [ha]
    exact (canonical12058 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA793 + difference 3 2) (sourceB793 + difference 2 3) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA793 + difference 3 2) (sourceB793 + difference 2 3) sourceC793) = raw13093 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13093; decide +kernel
    rw [ha]
    exact (canonical13093 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA793 + difference 3 4) (sourceB793 + difference 4 3) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA793 + difference 3 4) (sourceB793 + difference 4 3) sourceC793) = raw13094 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13094; decide +kernel
    rw [ha]
    exact (canonical13094 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA793 + difference 3 5) (sourceB793 + difference 5 3) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA793 + difference 3 5) (sourceB793 + difference 5 3) sourceC793) = raw13095 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13095; decide +kernel
    rw [ha]
    exact (canonical13095 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA793 + difference 4 0) (sourceB793 + difference 0 4) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA793 + difference 4 0) (sourceB793 + difference 0 4) sourceC793) = raw13096 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13096; decide +kernel
    rw [ha]
    exact (canonical13096 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA793 + difference 4 1) (sourceB793 + difference 1 4) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA793 + difference 4 1) (sourceB793 + difference 1 4) sourceC793) = raw12062 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12062; decide +kernel
    rw [ha]
    exact (canonical12062 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA793 + difference 4 2) (sourceB793 + difference 2 4) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA793 + difference 4 2) (sourceB793 + difference 2 4) sourceC793) = raw13097 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13097; decide +kernel
    rw [ha]
    exact (canonical13097 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA793 + difference 4 3) (sourceB793 + difference 3 4) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA793 + difference 4 3) (sourceB793 + difference 3 4) sourceC793) = raw12922 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12922; decide +kernel
    rw [ha]
    exact (canonical12922 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA793 + difference 4 5) (sourceB793 + difference 5 4) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA793 + difference 4 5) (sourceB793 + difference 5 4) sourceC793) = raw13098 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13098; decide +kernel
    rw [ha]
    exact (canonical13098 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA793 + difference 5 0) (sourceB793 + difference 0 5) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA793 + difference 5 0) (sourceB793 + difference 0 5) sourceC793) = raw12046 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12046; decide +kernel
    rw [ha]
    exact (canonical12046 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA793 + difference 5 1) (sourceB793 + difference 1 5) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA793 + difference 5 1) (sourceB793 + difference 1 5) sourceC793) = raw11734 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw11734; decide +kernel
    rw [ha]
    exact (canonical11734 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA793 + difference 5 2) (sourceB793 + difference 2 5) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA793 + difference 5 2) (sourceB793 + difference 2 5) sourceC793) = raw11729 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw11729; decide +kernel
    rw [ha]
    exact (canonical11729 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA793 + difference 5 3) (sourceB793 + difference 3 5) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA793 + difference 5 3) (sourceB793 + difference 3 5) sourceC793) = raw12047 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12047; decide +kernel
    rw [ha]
    exact (canonical12047 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA793 + difference 5 4) (sourceB793 + difference 4 5) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA793 + difference 5 4) (sourceB793 + difference 4 5) sourceC793) = raw12048 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12048; decide +kernel
    rw [ha]
    exact (canonical12048 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA793 sourceB793 sourceC793
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm793, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck672 : Integer.Sparse.reindex keyMap MixedData.row672 = numericRow672 := by decide +kernel

theorem numericCheck672 (x : Master → ℝ) : Integer.Sparse.eval numericRow672 x =
    (1 : ℝ) * reducedSource672 x := by
  norm_num [numericRow672, reducedSource672, Integer.Sparse.eval, Sparse.eval, nodeValue2571, nodeValue2974, nodeValue2975, nodeValue2977, nodeValue3051, nodeValue3848, nodeValue4092]

theorem reindexCheck673 : Integer.Sparse.reindex keyMap MixedData.row673 = numericRow673 := by decide +kernel

theorem numericCheck673 (x : Master → ℝ) : Integer.Sparse.eval numericRow673 x =
    (1 : ℝ) * reducedSource673 x := by
  norm_num [numericRow673, reducedSource673, Integer.Sparse.eval, Sparse.eval, nodeValue2878, nodeValue2881, nodeValue2882, nodeValue2885, nodeValue3051, nodeValue3961, nodeValue4092]

theorem reindexCheck674 : Integer.Sparse.reindex keyMap MixedData.row674 = numericRow674 := by decide +kernel

theorem numericCheck674 (x : Master → ℝ) : Integer.Sparse.eval numericRow674 x =
    (1 : ℝ) * reducedSource674 x := by
  norm_num [numericRow674, reducedSource674, Integer.Sparse.eval, Sparse.eval, nodeValue2575, nodeValue3043, nodeValue3044, nodeValue3045, nodeValue3051, nodeValue3850, nodeValue4092]

theorem reindexCheck676 : Integer.Sparse.reindex keyMap MixedData.row676 = numericRow676 := by decide +kernel

theorem numericCheck676 (x : Master → ℝ) : Integer.Sparse.eval numericRow676 x =
    (1 : ℝ) * reducedSource676 x := by
  norm_num [numericRow676, reducedSource676, Integer.Sparse.eval, Sparse.eval, nodeValue2930, nodeValue3376, nodeValue3380, nodeValue3394, nodeValue3534, nodeValue3573, nodeValue4083]

theorem reindexCheck677 : Integer.Sparse.reindex keyMap MixedData.row677 = numericRow677 := by decide +kernel

theorem numericCheck677 (x : Master → ℝ) : Integer.Sparse.eval numericRow677 x =
    (1 : ℝ) * reducedSource677 x := by
  norm_num [numericRow677, reducedSource677, Integer.Sparse.eval, Sparse.eval, nodeValue2089, nodeValue2926, nodeValue3551, nodeValue3567, nodeValue3571, nodeValue3573, nodeValue4083]

theorem reindexCheck678 : Integer.Sparse.reindex keyMap MixedData.row678 = numericRow678 := by decide +kernel

theorem numericCheck678 (x : Master → ℝ) : Integer.Sparse.eval numericRow678 x =
    (1 : ℝ) * reducedSource678 x := by
  norm_num [numericRow678, reducedSource678, Integer.Sparse.eval, Sparse.eval, nodeValue2092, nodeValue2929, nodeValue3149, nodeValue3152, nodeValue3158, nodeValue3573, nodeValue4083]

theorem reindexCheck679 : Integer.Sparse.reindex keyMap MixedData.row679 = numericRow679 := by decide +kernel

theorem numericCheck679 (x : Master → ℝ) : Integer.Sparse.eval numericRow679 x =
    (1 : ℝ) * reducedSource679 x := by
  norm_num [numericRow679, reducedSource679, Integer.Sparse.eval, Sparse.eval, nodeValue2926, nodeValue2929, nodeValue2930, nodeValue2956, nodeValue3079, nodeValue3573, nodeValue4083]

theorem reindexCheck680 : Integer.Sparse.reindex keyMap MixedData.row680 = numericRow680 := by decide +kernel

theorem numericCheck680 (x : Master → ℝ) : Integer.Sparse.eval numericRow680 x =
    (1 : ℝ) * reducedSource680 x := by
  norm_num [numericRow680, reducedSource680, Integer.Sparse.eval, Sparse.eval, nodeValue2110, nodeValue3079, nodeValue3505, nodeValue3573, nodeValue3581, nodeValue4083]

theorem reindexCheck681 : Integer.Sparse.reindex keyMap MixedData.row681 = numericRow681 := by decide +kernel

theorem numericCheck681 (x : Master → ℝ) : Integer.Sparse.eval numericRow681 x =
    (1 : ℝ) * reducedSource681 x := by
  norm_num [numericRow681, reducedSource681, Integer.Sparse.eval, Sparse.eval, nodeValue3152, nodeValue3380, nodeValue3551, nodeValue3552, nodeValue3573, nodeValue4083]

theorem reindexCheck684 : Integer.Sparse.reindex keyMap MixedData.row684 = numericRow684 := by decide +kernel

theorem numericCheck684 (x : Master → ℝ) : Integer.Sparse.eval numericRow684 x =
    (1 : ℝ) * reducedSource684 x := by
  norm_num [numericRow684, reducedSource684, Integer.Sparse.eval, Sparse.eval, nodeValue3053, nodeValue3909, nodeValue3910, nodeValue3962, nodeValue4091]

theorem reindexCheck685 : Integer.Sparse.reindex keyMap MixedData.row685 = numericRow685 := by decide +kernel

theorem numericCheck685 (x : Master → ℝ) : Integer.Sparse.eval numericRow685 x =
    (1 : ℝ) * reducedSource685 x := by
  norm_num [numericRow685, reducedSource685, Integer.Sparse.eval, Sparse.eval, nodeValue2746, nodeValue2976, nodeValue3053, nodeValue3909, nodeValue4091]

theorem reindexCheck686 : Integer.Sparse.reindex keyMap MixedData.row686 = numericRow686 := by decide +kernel

theorem numericCheck686 (x : Master → ℝ) : Integer.Sparse.eval numericRow686 x =
    (5760 : ℝ) * reducedSource686 x := by
  norm_num [numericRow686, reducedSource686, Integer.Sparse.eval, Sparse.eval, nodeValue4878, nodeValue4879, nodeValue4885, nodeValue4886, nodeValue4889, nodeValue5227, nodeValue5237, nodeValue5265, nodeValue5273, nodeValue5283, nodeValue5286, nodeValue5292, nodeValue5299]
  ring

theorem reindexCheck687 : Integer.Sparse.reindex keyMap MixedData.row687 = numericRow687 := by decide +kernel

theorem numericCheck687 (x : Master → ℝ) : Integer.Sparse.eval numericRow687 x =
    (1440 : ℝ) * reducedSource687 x := by
  norm_num [numericRow687, reducedSource687, Integer.Sparse.eval, Sparse.eval, nodeValue2234, nodeValue2235, nodeValue2246, nodeValue2671, nodeValue2684, nodeValue2741, nodeValue3023, nodeValue3037, nodeValue3051, nodeValue3076, nodeValue3100, nodeValue3221, nodeValue3223]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero672 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource672 (mixedVector B) = 0 := by
  have h2571 : mixedVector B (Sum.inr 2571) = Sparse.eval nodeValue2571 (mixedVector B) := by
    change mixedMoment B node2571 node2571Labels = _
    exact sound2571 B hB hF
  have h2974 : mixedVector B (Sum.inr 2974) = Sparse.eval nodeValue2974 (mixedVector B) := by
    change mixedMoment B node2974 node2974Labels = _
    exact sound2974 B hB hF
  have h2975 : mixedVector B (Sum.inr 2975) = Sparse.eval nodeValue2975 (mixedVector B) := by
    change mixedMoment B node2975 node2975Labels = _
    exact sound2975 B hB hF
  have h2977 : mixedVector B (Sum.inr 2977) = Sparse.eval nodeValue2977 (mixedVector B) := by
    change mixedMoment B node2977 node2977Labels = _
    exact sound2977 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm774, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2571, h2974, h2975, h2977, h3051, h3848, h4092, reducedSource672] using sourceEq774 B hB

theorem rowSound672 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row672 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck672, numericCheck672, reducedZero672 B hB hF, mul_zero]

theorem reducedZero673 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource673 (mixedVector B) = 0 := by
  have h2878 : mixedVector B (Sum.inr 2878) = Sparse.eval nodeValue2878 (mixedVector B) := by
    change mixedMoment B node2878 node2878Labels = _
    exact sound2878 B hB hF
  have h2881 : mixedVector B (Sum.inr 2881) = Sparse.eval nodeValue2881 (mixedVector B) := by
    change mixedMoment B node2881 node2881Labels = _
    exact sound2881 B hB hF
  have h2882 : mixedVector B (Sum.inr 2882) = Sparse.eval nodeValue2882 (mixedVector B) := by
    change mixedMoment B node2882 node2882Labels = _
    exact sound2882 B hB hF
  have h2885 : mixedVector B (Sum.inr 2885) = Sparse.eval nodeValue2885 (mixedVector B) := by
    change mixedMoment B node2885 node2885Labels = _
    exact sound2885 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm775, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2878, h2881, h2882, h2885, h3051, h3961, h4092, reducedSource673] using sourceEq775 B hB

theorem rowSound673 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row673 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck673, numericCheck673, reducedZero673 B hB hF, mul_zero]

theorem reducedZero674 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource674 (mixedVector B) = 0 := by
  have h2575 : mixedVector B (Sum.inr 2575) = Sparse.eval nodeValue2575 (mixedVector B) := by
    change mixedMoment B node2575 node2575Labels = _
    exact sound2575 B hB hF
  have h3043 : mixedVector B (Sum.inr 3043) = Sparse.eval nodeValue3043 (mixedVector B) := by
    change mixedMoment B node3043 node3043Labels = _
    exact sound3043 B hB hF
  have h3044 : mixedVector B (Sum.inr 3044) = Sparse.eval nodeValue3044 (mixedVector B) := by
    change mixedMoment B node3044 node3044Labels = _
    exact sound3044 B hB hF
  have h3045 : mixedVector B (Sum.inr 3045) = Sparse.eval nodeValue3045 (mixedVector B) := by
    change mixedMoment B node3045 node3045Labels = _
    exact sound3045 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm776, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2575, h3043, h3044, h3045, h3051, h3850, h4092, reducedSource674] using sourceEq776 B hB

theorem rowSound674 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row674 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck674, numericCheck674, reducedZero674 B hB hF, mul_zero]

theorem reducedZero676 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource676 (mixedVector B) = 0 := by
  have h2930 : mixedVector B (Sum.inr 2930) = Sparse.eval nodeValue2930 (mixedVector B) := by
    change mixedMoment B node2930 node2930Labels = _
    exact sound2930 B hB hF
  have h3376 : mixedVector B (Sum.inr 3376) = Sparse.eval nodeValue3376 (mixedVector B) := by
    change mixedMoment B node3376 node3376Labels = _
    exact sound3376 B hB hF
  have h3380 : mixedVector B (Sum.inr 3380) = Sparse.eval nodeValue3380 (mixedVector B) := by
    change mixedMoment B node3380 node3380Labels = _
    exact sound3380 B hB hF
  have h3394 : mixedVector B (Sum.inr 3394) = Sparse.eval nodeValue3394 (mixedVector B) := by
    change mixedMoment B node3394 node3394Labels = _
    exact sound3394 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm780, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2930, h3376, h3380, h3394, h3534, h3573, h4083, reducedSource676] using sourceEq780 B hB

theorem rowSound676 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row676 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck676, numericCheck676, reducedZero676 B hB hF, mul_zero]

theorem reducedZero677 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource677 (mixedVector B) = 0 := by
  have h2089 : mixedVector B (Sum.inr 2089) = Sparse.eval nodeValue2089 (mixedVector B) := by
    change mixedMoment B node2089 node2089Labels = _
    exact sound2089 B hB hF
  have h2926 : mixedVector B (Sum.inr 2926) = Sparse.eval nodeValue2926 (mixedVector B) := by
    change mixedMoment B node2926 node2926Labels = _
    exact sound2926 B hB hF
  have h3551 : mixedVector B (Sum.inr 3551) = Sparse.eval nodeValue3551 (mixedVector B) := by
    change mixedMoment B node3551 node3551Labels = _
    exact sound3551 B hB hF
  have h3567 : mixedVector B (Sum.inr 3567) = Sparse.eval nodeValue3567 (mixedVector B) := by
    change mixedMoment B node3567 node3567Labels = _
    exact sound3567 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm781, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2089, h2926, h3551, h3567, h3571, h3573, h4083, reducedSource677] using sourceEq781 B hB

theorem rowSound677 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row677 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck677, numericCheck677, reducedZero677 B hB hF, mul_zero]

theorem reducedZero678 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource678 (mixedVector B) = 0 := by
  have h2092 : mixedVector B (Sum.inr 2092) = Sparse.eval nodeValue2092 (mixedVector B) := by
    change mixedMoment B node2092 node2092Labels = _
    exact sound2092 B hB hF
  have h2929 : mixedVector B (Sum.inr 2929) = Sparse.eval nodeValue2929 (mixedVector B) := by
    change mixedMoment B node2929 node2929Labels = _
    exact sound2929 B hB hF
  have h3149 : mixedVector B (Sum.inr 3149) = Sparse.eval nodeValue3149 (mixedVector B) := by
    change mixedMoment B node3149 node3149Labels = _
    exact sound3149 B hB hF
  have h3152 : mixedVector B (Sum.inr 3152) = Sparse.eval nodeValue3152 (mixedVector B) := by
    change mixedMoment B node3152 node3152Labels = _
    exact sound3152 B hB hF
  have h3158 : mixedVector B (Sum.inr 3158) = Sparse.eval nodeValue3158 (mixedVector B) := by
    change mixedMoment B node3158 node3158Labels = _
    exact sound3158 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm782, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2092, h2929, h3149, h3152, h3158, h3573, h4083, reducedSource678] using sourceEq782 B hB

theorem rowSound678 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row678 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck678, numericCheck678, reducedZero678 B hB hF, mul_zero]

theorem reducedZero679 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource679 (mixedVector B) = 0 := by
  have h2926 : mixedVector B (Sum.inr 2926) = Sparse.eval nodeValue2926 (mixedVector B) := by
    change mixedMoment B node2926 node2926Labels = _
    exact sound2926 B hB hF
  have h2929 : mixedVector B (Sum.inr 2929) = Sparse.eval nodeValue2929 (mixedVector B) := by
    change mixedMoment B node2929 node2929Labels = _
    exact sound2929 B hB hF
  have h2930 : mixedVector B (Sum.inr 2930) = Sparse.eval nodeValue2930 (mixedVector B) := by
    change mixedMoment B node2930 node2930Labels = _
    exact sound2930 B hB hF
  have h2956 : mixedVector B (Sum.inr 2956) = Sparse.eval nodeValue2956 (mixedVector B) := by
    change mixedMoment B node2956 node2956Labels = _
    exact sound2956 B hB hF
  have h3079 : mixedVector B (Sum.inr 3079) = Sparse.eval nodeValue3079 (mixedVector B) := by
    change mixedMoment B node3079 node3079Labels = _
    exact sound3079 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm783, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2926, h2929, h2930, h2956, h3079, h3573, h4083, reducedSource679] using sourceEq783 B hB

theorem rowSound679 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row679 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck679, numericCheck679, reducedZero679 B hB hF, mul_zero]

theorem reducedZero680 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource680 (mixedVector B) = 0 := by
  have h2110 : mixedVector B (Sum.inr 2110) = Sparse.eval nodeValue2110 (mixedVector B) := by
    change mixedMoment B node2110 node2110Labels = _
    exact sound2110 B hB hF
  have h3079 : mixedVector B (Sum.inr 3079) = Sparse.eval nodeValue3079 (mixedVector B) := by
    change mixedMoment B node3079 node3079Labels = _
    exact sound3079 B hB hF
  have h3505 : mixedVector B (Sum.inr 3505) = Sparse.eval nodeValue3505 (mixedVector B) := by
    change mixedMoment B node3505 node3505Labels = _
    exact sound3505 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3581 : mixedVector B (Sum.inr 3581) = Sparse.eval nodeValue3581 (mixedVector B) := by
    change mixedMoment B node3581 node3581Labels = _
    exact sound3581 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm784, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2110, h3079, h3505, h3573, h3581, h4083, reducedSource680] using sourceEq784 B hB

theorem rowSound680 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row680 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck680, numericCheck680, reducedZero680 B hB hF, mul_zero]

theorem reducedZero681 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource681 (mixedVector B) = 0 := by
  have h3152 : mixedVector B (Sum.inr 3152) = Sparse.eval nodeValue3152 (mixedVector B) := by
    change mixedMoment B node3152 node3152Labels = _
    exact sound3152 B hB hF
  have h3380 : mixedVector B (Sum.inr 3380) = Sparse.eval nodeValue3380 (mixedVector B) := by
    change mixedMoment B node3380 node3380Labels = _
    exact sound3380 B hB hF
  have h3551 : mixedVector B (Sum.inr 3551) = Sparse.eval nodeValue3551 (mixedVector B) := by
    change mixedMoment B node3551 node3551Labels = _
    exact sound3551 B hB hF
  have h3552 : mixedVector B (Sum.inr 3552) = Sparse.eval nodeValue3552 (mixedVector B) := by
    change mixedMoment B node3552 node3552Labels = _
    exact sound3552 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm785, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3152, h3380, h3551, h3552, h3573, h4083, reducedSource681] using sourceEq785 B hB

theorem rowSound681 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row681 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck681, numericCheck681, reducedZero681 B hB hF, mul_zero]

theorem reducedZero684 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource684 (mixedVector B) = 0 := by
  have h3053 : mixedVector B (Sum.inr 3053) = Sparse.eval nodeValue3053 (mixedVector B) := by
    change mixedMoment B node3053 node3053Labels = _
    exact sound3053 B hB hF
  have h3909 : mixedVector B (Sum.inr 3909) = Sparse.eval nodeValue3909 (mixedVector B) := by
    change mixedMoment B node3909 node3909Labels = _
    exact sound3909 B hB hF
  have h3910 : mixedVector B (Sum.inr 3910) = Sparse.eval nodeValue3910 (mixedVector B) := by
    change mixedMoment B node3910 node3910Labels = _
    exact sound3910 B hB hF
  have h3962 : mixedVector B (Sum.inr 3962) = Sparse.eval nodeValue3962 (mixedVector B) := by
    change mixedMoment B node3962 node3962Labels = _
    exact sound3962 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm790, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3053, h3909, h3910, h3962, h4091, reducedSource684] using sourceEq790 B hB

theorem rowSound684 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row684 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck684, numericCheck684, reducedZero684 B hB hF, mul_zero]

theorem reducedZero685 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource685 (mixedVector B) = 0 := by
  have h2746 : mixedVector B (Sum.inr 2746) = Sparse.eval nodeValue2746 (mixedVector B) := by
    change mixedMoment B node2746 node2746Labels = _
    exact sound2746 B hB hF
  have h2976 : mixedVector B (Sum.inr 2976) = Sparse.eval nodeValue2976 (mixedVector B) := by
    change mixedMoment B node2976 node2976Labels = _
    exact sound2976 B hB hF
  have h3053 : mixedVector B (Sum.inr 3053) = Sparse.eval nodeValue3053 (mixedVector B) := by
    change mixedMoment B node3053 node3053Labels = _
    exact sound3053 B hB hF
  have h3909 : mixedVector B (Sum.inr 3909) = Sparse.eval nodeValue3909 (mixedVector B) := by
    change mixedMoment B node3909 node3909Labels = _
    exact sound3909 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm791, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2746, h2976, h3053, h3909, h4091, reducedSource685] using sourceEq791 B hB

theorem rowSound685 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row685 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck685, numericCheck685, reducedZero685 B hB hF, mul_zero]

theorem reducedZero686 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource686 (mixedVector B) = 0 := by
  have h4878 : mixedVector B (Sum.inr 4878) = Sparse.eval nodeValue4878 (mixedVector B) := by
    change mixedMoment B node4878 node4878Labels = _
    exact sound4878 B hB hF
  have h4879 : mixedVector B (Sum.inr 4879) = Sparse.eval nodeValue4879 (mixedVector B) := by
    change mixedMoment B node4879 node4879Labels = _
    exact sound4879 B hB hF
  have h4885 : mixedVector B (Sum.inr 4885) = Sparse.eval nodeValue4885 (mixedVector B) := by
    change mixedMoment B node4885 node4885Labels = _
    exact sound4885 B hB hF
  have h4886 : mixedVector B (Sum.inr 4886) = Sparse.eval nodeValue4886 (mixedVector B) := by
    change mixedMoment B node4886 node4886Labels = _
    exact sound4886 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h5227 : mixedVector B (Sum.inr 5227) = Sparse.eval nodeValue5227 (mixedVector B) := by
    change mixedMoment B node5227 node5227Labels = _
    exact sound5227 B hB hF
  have h5237 : mixedVector B (Sum.inr 5237) = Sparse.eval nodeValue5237 (mixedVector B) := by
    change mixedMoment B node5237 node5237Labels = _
    exact sound5237 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5273 : mixedVector B (Sum.inr 5273) = Sparse.eval nodeValue5273 (mixedVector B) := by
    change mixedMoment B node5273 node5273Labels = _
    exact sound5273 B hB hF
  have h5283 : mixedVector B (Sum.inr 5283) = Sparse.eval nodeValue5283 (mixedVector B) := by
    change mixedMoment B node5283 node5283Labels = _
    exact sound5283 B hB hF
  have h5286 : mixedVector B (Sum.inr 5286) = Sparse.eval nodeValue5286 (mixedVector B) := by
    change mixedMoment B node5286 node5286Labels = _
    exact sound5286 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  have h5299 : mixedVector B (Sum.inr 5299) = Sparse.eval nodeValue5299 (mixedVector B) := by
    change mixedMoment B node5299 node5299Labels = _
    exact sound5299 B hB hF
  simpa only [sourceForm792, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4878, h4879, h4885, h4886, h4889, h5227, h5237, h5265, h5273, h5283, h5286, h5292, h5299, reducedSource686] using sourceEq792 B hB

theorem rowSound686 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row686 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck686, numericCheck686, reducedZero686 B hB hF, mul_zero]

theorem reducedZero687 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource687 (mixedVector B) = 0 := by
  have h2234 : mixedVector B (Sum.inr 2234) = Sparse.eval nodeValue2234 (mixedVector B) := by
    change mixedMoment B node2234 node2234Labels = _
    exact sound2234 B hB hF
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h2246 : mixedVector B (Sum.inr 2246) = Sparse.eval nodeValue2246 (mixedVector B) := by
    change mixedMoment B node2246 node2246Labels = _
    exact sound2246 B hB hF
  have h2671 : mixedVector B (Sum.inr 2671) = Sparse.eval nodeValue2671 (mixedVector B) := by
    change mixedMoment B node2671 node2671Labels = _
    exact sound2671 B hB hF
  have h2684 : mixedVector B (Sum.inr 2684) = Sparse.eval nodeValue2684 (mixedVector B) := by
    change mixedMoment B node2684 node2684Labels = _
    exact sound2684 B hB hF
  have h2741 : mixedVector B (Sum.inr 2741) = Sparse.eval nodeValue2741 (mixedVector B) := by
    change mixedMoment B node2741 node2741Labels = _
    exact sound2741 B hB hF
  have h3023 : mixedVector B (Sum.inr 3023) = Sparse.eval nodeValue3023 (mixedVector B) := by
    change mixedMoment B node3023 node3023Labels = _
    exact sound3023 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3076 : mixedVector B (Sum.inr 3076) = Sparse.eval nodeValue3076 (mixedVector B) := by
    change mixedMoment B node3076 node3076Labels = _
    exact sound3076 B hB hF
  have h3100 : mixedVector B (Sum.inr 3100) = Sparse.eval nodeValue3100 (mixedVector B) := by
    change mixedMoment B node3100 node3100Labels = _
    exact sound3100_e B hB hF
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h3223 : mixedVector B (Sum.inr 3223) = Sparse.eval nodeValue3223 (mixedVector B) := by
    change mixedMoment B node3223 node3223Labels = _
    exact sound3223_e B hB hF
  simpa only [sourceForm793, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2234, h2235, h2246, h2671, h2684, h2741, h3023, h3037, h3051, h3076, h3100, h3221, h3223, reducedSource687] using sourceEq793 B hB

theorem rowSound687 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row687 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck687, numericCheck687, reducedZero687 B hB hF, mul_zero]

theorem sourceRowsAt672 : MixedData.sourceRows (672 : Fin 2425) =
    MixedData.row672 := by decide +kernel

theorem sourceRowsAt673 : MixedData.sourceRows (673 : Fin 2425) =
    MixedData.row673 := by decide +kernel

theorem sourceRowsAt674 : MixedData.sourceRows (674 : Fin 2425) =
    MixedData.row674 := by decide +kernel

theorem sourceRowsAt675 : MixedData.sourceRows (675 : Fin 2425) =
    MixedData.row675 := by decide +kernel

theorem sourceRowsAt676 : MixedData.sourceRows (676 : Fin 2425) =
    MixedData.row676 := by decide +kernel

theorem sourceRowsAt677 : MixedData.sourceRows (677 : Fin 2425) =
    MixedData.row677 := by decide +kernel

theorem sourceRowsAt678 : MixedData.sourceRows (678 : Fin 2425) =
    MixedData.row678 := by decide +kernel

theorem sourceRowsAt679 : MixedData.sourceRows (679 : Fin 2425) =
    MixedData.row679 := by decide +kernel

theorem sourceRowsAt680 : MixedData.sourceRows (680 : Fin 2425) =
    MixedData.row680 := by decide +kernel

theorem sourceRowsAt681 : MixedData.sourceRows (681 : Fin 2425) =
    MixedData.row681 := by decide +kernel

theorem sourceRowsAt682 : MixedData.sourceRows (682 : Fin 2425) =
    MixedData.row682 := by decide +kernel

theorem sourceRowsAt683 : MixedData.sourceRows (683 : Fin 2425) =
    MixedData.row683 := by decide +kernel

theorem sourceRowsAt684 : MixedData.sourceRows (684 : Fin 2425) =
    MixedData.row684 := by decide +kernel

theorem sourceRowsAt685 : MixedData.sourceRows (685 : Fin 2425) =
    MixedData.row685 := by decide +kernel

theorem sourceRowsAt686 : MixedData.sourceRows (686 : Fin 2425) =
    MixedData.row686 := by decide +kernel

theorem sourceRowsAt687 : MixedData.sourceRows (687 : Fin 2425) =
    MixedData.row687 := by decide +kernel

theorem chunkSound42_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 42) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 672 ∨ k.val = 673 ∨ k.val = 674 ∨ k.val = 675 ∨ k.val = 676 ∨ k.val = 677 ∨ k.val = 678 ∨ k.val = 679 ∨ k.val = 680 ∨ k.val = 681 ∨ k.val = 682 ∨ k.val = 683 ∨ k.val = 684 ∨ k.val = 685 ∨ k.val = 686 ∨ k.val = 687 := by omega
  rcases heq with h672 | h673 | h674 | h675 | h676 | h677 | h678 | h679 | h680 | h681 | h682 | h683 | h684 | h685 | h686 | h687
  · have he : k = (672 : Fin 2425) := Fin.ext h672
    subst k
    rw [sourceRowsAt672]
    exact rowSound672 B hB hF
  · have he : k = (673 : Fin 2425) := Fin.ext h673
    subst k
    rw [sourceRowsAt673]
    exact rowSound673 B hB hF
  · have he : k = (674 : Fin 2425) := Fin.ext h674
    subst k
    rw [sourceRowsAt674]
    exact rowSound674 B hB hF
  · have he : k = (675 : Fin 2425) := Fin.ext h675
    subst k
    rw [sourceRowsAt675]
    exact rowSound675_e B hB hF
  · have he : k = (676 : Fin 2425) := Fin.ext h676
    subst k
    rw [sourceRowsAt676]
    exact rowSound676 B hB hF
  · have he : k = (677 : Fin 2425) := Fin.ext h677
    subst k
    rw [sourceRowsAt677]
    exact rowSound677 B hB hF
  · have he : k = (678 : Fin 2425) := Fin.ext h678
    subst k
    rw [sourceRowsAt678]
    exact rowSound678 B hB hF
  · have he : k = (679 : Fin 2425) := Fin.ext h679
    subst k
    rw [sourceRowsAt679]
    exact rowSound679 B hB hF
  · have he : k = (680 : Fin 2425) := Fin.ext h680
    subst k
    rw [sourceRowsAt680]
    exact rowSound680 B hB hF
  · have he : k = (681 : Fin 2425) := Fin.ext h681
    subst k
    rw [sourceRowsAt681]
    exact rowSound681 B hB hF
  · have he : k = (682 : Fin 2425) := Fin.ext h682
    subst k
    rw [sourceRowsAt682]
    exact rowSound682_e B hB hF
  · have he : k = (683 : Fin 2425) := Fin.ext h683
    subst k
    rw [sourceRowsAt683]
    exact rowSound683_e B hB hF
  · have he : k = (684 : Fin 2425) := Fin.ext h684
    subst k
    rw [sourceRowsAt684]
    exact rowSound684 B hB hF
  · have he : k = (685 : Fin 2425) := Fin.ext h685
    subst k
    rw [sourceRowsAt685]
    exact rowSound685 B hB hF
  · have he : k = (686 : Fin 2425) := Fin.ext h686
    subst k
    rw [sourceRowsAt686]
    exact rowSound686 B hB hF
  · have he : k = (687 : Fin 2425) := Fin.ext h687
    subst k
    rw [sourceRowsAt687]
    exact rowSound687 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound42_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound42_e_oai
